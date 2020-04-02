library(pracma)
library(ggplot2)
library(tidyr)
library(reshape2)
library(tidyverse)
library(matrixcalc)
library(truncnorm)
library(mvtnorm)
library(caret)
library(ggplot2)
library(reshape2)
library(pROC)
library(gstat)
library(tidyverse)
library(vegan)
library(TSA)
library(kernlab)
library(gridExtra)

conv2 <- function(X, A){
  ## This mimics the conv2 function in Matlab
  ## https://github.com/cran/WaveletCo/blob/master/R/conv2.R
  
  X.pad <- matrix(0, ncol = NCOL(X) + NCOL(A)-1, nrow = NROW(X)+NROW(A)-1);
  X.pad[1:NROW(X), 1:NCOL(X)] <- X
  A.pad <- matrix(0, ncol = NCOL(X) + NCOL(A)-1, nrow = NROW(X)+NROW(A)-1);
  A.pad[1:NROW(A), 1:NCOL(A)] <- A
  
  X.fft <- fft(X.pad);
  A.fft <- fft(A.pad);
  M <- fft(X.fft * A.fft, inverse = TRUE)/length(X.fft)
  
  N.row <- (floor(NROW(A)/2) + (1:NROW(X)))
  N.col <- (floor(NCOL(A)/2) + (1:NCOL(X)))
  
  XC <- M[N.row, N.col]
  return((XC))
}


bispecd <- function(y,  nfft=128, wind=5, nsamp=0, overlap=50){
  ## Translation of bispecd Matlab function
  
  #BISPECD Bispectrum estimation using the direct (fft-based) approach.
  #	[Bspec,waxis] = bispecd (y,  nfft, wind, segsamp, overlap)
  #	y    - data vector or time-series
  #	nfft - fft length [default = power of two > segsamp]
  #	wind - window specification for frequency-domain smoothing
  #	       if 'wind' is a scalar, it specifies the length of the side
  #	          of the square for the Rao-Gabr optimal window  [default=5]
  #	       if 'wind' is a vector, a 2D window will be calculated via
  #	          w2(i,j) = wind(i) * wind(j) * wind(i+j)
  #	       if 'wind' is a matrix, it specifies the 2-D filter directly
  #	segsamp - samples per segment [default: such that we have 8 segments]
  #	        - if y is a matrix, segsamp is set to the number of rows
  #	overlap - percentage overlap [default = 50]
  #	        - if y is a matrix, overlap is set to 0.
  #
  #	Bspec   - estimated bispectrum: an nfft x nfft array, with origin
  #	          at the center, and axes pointing down and to the right.
  #	waxis   - vector of frequencies associated with the rows and columns
  #	          of Bspec;  sampling frequency is assumed to be 1.
  

  ly = length(y)
  nrecs = 1
  
  overlap = min(99,max(overlap,0))
  
  if (nsamp <= 0)  nsamp = floor(ly/ (8 - 7 * overlap/100))
  
  overlap  = floor(nsamp * overlap / 100)             # added 2/14
  nadvance = nsamp - overlap
  nrecs    = floor( (ly*nrecs - overlap) / nadvance)
  
  
  # ------------------- create the 2-D window -------------------------
  m = 1
  n = 1
  window = wind
  if (max(m,n) == 1){     # scalar: wind is size of Rao-Gabr window
    winsize = wind
    if (winsize < 0) winsize = 5        # the window length L
    winsize = winsize - (winsize %% 2) + 1  # make it odd
    if (winsize > 1){
      mwind   = floor(nfft/winsize)            # the scale parameter M
      lby2    = (winsize - 1)/2
      theta  = -lby2:lby2
      opwind = rep(1, winsize) %*% t(theta^2)       # w(m,n)=m^2  # *****
      opwind = opwind + t(opwind) + theta %*% t(theta)   # m^2 + n^2 + mn
      opwind = 1 - (2*mwind/nfft)^2 * opwind       
      hex    = rep(1,winsize) %*% t(theta)             # m
      hex    = abs(hex) + abs(t(hex)) + abs(hex+t(hex))
      hex    = (hex < winsize)
      opwind = opwind * hex
      opwind = opwind * (4 * mwind^2) / (7 * pi^2) 
    } else opwind = 1
  }
  
  
  
  # ---------------- accumulate triple products ----------------------
  
  Bspec    = matrix(0,nrow=nfft,ncol=nfft)
  
  #mask = hankel(1:nfft,c(nfft,1:(nfft-1)))   # the hankel mask (faster)
  mask = hankel.matrix(nfft, 1:nfft)
  locseg = 1:nsamp
  for (krec in 1:nrecs){
    xseg   = y[locseg]
    Xf     = fft((xseg-mean(xseg)))[1:nfft]/nsamp
    CXf    = Conj(Xf)
    Bspec  = Bspec + ((Xf %*% t(Xf)) * matrix(CXf[mask], nrow=nfft, ncol=nfft)) 
    locseg = locseg + nadvance
  }
  
  Bspec = mrbsizeR::fftshift(Bspec)/(nrecs)
  
  
  
  # ----------------- frequency-domain smoothing ------------------------
  
  if (winsize > 1){
    lby2 = (winsize-1)/2
    Bspec = conv2(Bspec,opwind)#,'full')
  }
  
  if (nfft%%2 == 0){
    waxis = ((-nfft/2):(nfft/2-1))/nfft
  } else {
    waxis = ((-(nfft-1)/2):((nfft-1)/2))/nfft
  }
  return(list(bspec=Bspec, waxis=waxis))
}   




ssvs <- function(dat, iter,  predX=NULL, topN=NULL){
  ## This function performs SSVS for a probit regression model
  ## input dat is a data frame containing the response Y and design matrix X
  ## input iter is the number of iterations for MCMC
  ## input predX is the design matrix for data points to be predicted on
  ## input topN is used to return the top topN EOF's at every iteration
  
  ## returns Zout, the latent variable at every iteration
  ## returns betaOut, the regression coefficient values at every iteration
  ## returns gammaOut, the indicator of which variables are "selected" at every iteration
  ## returns predOut, the class predictions for non-training data at every iteration
  ## returns topOut, the indexes for the top topN variables at every iteration
  
  ## Initialize Outputs
  topOut <- NULL
  if(!is.null(topN)) topOut <- matrix(0, nrow=iter, ncol=topN) # Indexes of top N variables every iteration
  predOut <- NULL
  if(!is.null(predX)) predOut <- matrix(0, nrow=iter, ncol=nrow(predX))
  Zout <- matrix(0, nrow=iter, ncol=nrow(dat))
  betaOut <- matrix(0, nrow=iter, ncol=ncol(dat$X))
  gammaOut <- matrix(0, nrow=iter, ncol=ncol(dat$X))
  
  ## Starting point for MCMC
  gamma <- rep(1,ncol(dat$X))
  beta <- rep(0,ncol(dat$X))
  Z <- dat$Y - 0.5
  d <- (gamma*(cTune-1)) + 1
  D <- diag(d*tauTune)
  
  ## Keep outside of loop
  J1 <- which(dat$Y == 1)
  J0 <- which(dat$Y == 0)
  XJ1 <- dat$X[J1,]
  XJ0 <- dat$X[J0,]
  xtx <- t(dat$X) %*% dat$X
  XT <- t(dat$X)
  colX <- ncol(dat$X)
  
  ## Probit MCMC
  for(i in 1:iter){
    Z[J1] <- Zout[i,J1] <- rtruncnorm(1, a=0, mean=XJ1%*%beta)
    Z[J0] <- Zout[i,J0] <- rtruncnorm(1, b=0, mean=XJ0%*%beta)
    sigma <- solve(xtx + solve(D %*% D))
    mu <- sigma %*% XT %*% Z
    beta <- betaOut[i,] <- as.vector(rmvnorm(1, mean=mu, sigma=sigma))
    a <- piTune * dnorm(beta, sd=cTune*tauTune)
    b <- piTune * dnorm(beta, sd=tauTune)
    gamma <- gammaOut[i,] <- rbinom(colX,1,(a/(a+b)))
    d <- (gamma*(cTune-1)) + 1
    D <- diag(d*tauTune)
    if(!is.null(predX)) predOut[i,] <- pnorm(predX %*% beta) 
    if(!is.null(topN)) topOut[i,] <- which(abs(beta[-1]) %in% sort(abs(beta[-1]), decreasing=T)[1:topN])
  }
  return(out=list(Zout=Zout,betaOut=betaOut,gammaOut=gammaOut, pred=predOut, topOut=topOut))
}


EOF <- function(z) {
  nz <- dim(z)
  neigen <- min(nz) 
  Z <- scale(z, center = T, scale =F)
  
  if (nz[1] < nz[2]) { 			# USING von STORCH's trick
    
    S <- Z %*% t(Z) / (nz[2]-1)
    eigS <- eigen(S)		
    e <- t(Z) %*% eigS$vectors[,1:(neigen-1)] # lose one degree of freedom
    for (ii in 1:(neigen-1)) {
      e[,ii] <- e[,ii]/sqrt(sum(e[,ii]^2))
    }
  } else {				# TRADITIONAL METHOD
    
    S <- t(Z) %*% Z / (nz[1]-1)
    eigS <- eigen(S)		
    e <- eigS$vectors[,1:(neigen-1)]
  }
  return(list(e = e, v = eigS$values[1:(neigen-1)]))
}





## Prep data
google <- read_csv('trendsClean.csv')
dataMat <- as.matrix(google[,-c(1:2)])
tStep <- ncol(dataMat)

Validation <- Calibration <- SSVS_Cal <- data.frame(Drop_Rate=seq(0.02, 0.1, by=0.02), Acc=NA, AUC=NA)


Y <- as.numeric(google$Type == 'Actor')
compBspec <- array(NA, dim=c(tStep,tStep,nrow(dataMat)))
for(i in 1:nrow(dataMat)){
  compBspec[,,i] <- bispecd(as.numeric(dataMat[i,]), tStep, 3, tStep)$bspec ### Compute Bispectrum
  print(i)
}
compBspec <- log(abs(compBspec))
compBspec <- aperm(compBspec, dim=c(3,1,2))
compBspecNorm <- apply(compBspec, c(2,3), scale)


Xdat <- array(NA, dim=c(200,52,52,1))
Xdat[,,,1] <- compBspecNorm



tauTune <- 0.1 ## For SSVS
cTune <- 10
piTune <- 0.5

func1 <- function(x){
  periodogram(x,plot=FALSE)$spec
}
compSpec <- t(apply(dataMat,1,func1))
eofSpec <- EOF(compSpec)
EQXspec <- compSpec %*% eofSpec$e[,1:20]
EQXspec <- cbind(1,scale(EQXspec))
eqdatSpec <- data.frame(Y=Y, X=I(EQXspec))


library(keras)
use_session_with_seed(100)
for(d in 1:nrow(Validation)){
  reps <- 50
  K <- 20
  Out <- rep(NA,reps)
  truthV <- c()
  predsV <- c()
  truthC <- c()
  predsC <- c()
  predsCssvs <- c()
  for(i in 1:reps){
    Ind <- sample(200, K)
    
    ## Fit BCNN first
    drop1 <- layer_dropout(rate=Validation$Drop_Rate[d])
    inputs <- layer_input(shape=c(52, 52, 1)) 
    outputs <- inputs %>%
      layer_conv_2d(filters = 32, kernel_size = c(3, 3),  activation = "relu",
                    input_shape = c(52, 52, 1)) %>%
      layer_max_pooling_2d(pool_size = c(3, 3)) %>%
      layer_batch_normalization() %>%
      drop1(training=T) %>%
      layer_conv_2d(filters = 32, kernel_size = c(5, 5),  activation = "relu") %>%
      layer_max_pooling_2d(pool_size = c(4, 4)) %>%
      layer_batch_normalization() %>%
      layer_flatten() %>%
      layer_dense(units=8, activation = 'relu') %>%
      drop1(training=T) %>%
      layer_dense(units=1, activation = 'sigmoid')
    
    model <- keras_model(inputs, outputs)
    
    model %>% compile(
      optimizer_adam(lr=0.001),
      loss = "binary_crossentropy",
      metrics = c("accuracy")
    )
    model %>% fit(
      Xdat[-Ind,,,,drop=F], Y[-Ind],
      epochs = 10, batch_size=8
    )
    
    postPred <- matrix(NA, nrow=K, ncol=100)
    for(j in 1:100){
      postPred[,j] <- as.numeric(predict(model, Xdat[Ind,,,,drop=F]))
    }
    predsMod <- apply(postPred,1,mean)
    ansV <- Y[Ind[1:10]]
    ansC <- Y[Ind[-c(1:10)]]
    truthV <- c(truthV, ansV)
    truthC <- c(truthC, ansC)
    predsV <- c(predsV, predsMod[1:10])
    predsC <- c(predsC, predsMod[-c(1:10)])
    
    
    ## Fit SSVS
    train <- eqdatSpec[-Ind,]
    ssvsMod <- ssvs(eqdatSpec[-Ind,], 2000, predX=eqdatSpec[Ind,]$X,0)
    predsCssvs <- c(predsCssvs, apply(ssvsMod$pred[-c(1:1000), ], 2, mean)[-c(1:10)])
    
    print(paste(i, d))
    print(paste0("Val: ",mean((predsV > 0.5) == truthV), 
                 " Cal: ",mean((predsC > 0.5) == truthC), 
                 " SSVS: ", mean((predsCssvs > 0.5) == truthC) ))
  }
  Validation$Acc[d] <- mean((predsV > 0.5) == truthV)
  Validation$AUC[d] <- plot.roc(truthV, predsV)$auc
  Calibration$Acc[d] <- mean((predsC > 0.5) == truthC)
  Calibration$AUC[d] <- plot.roc(truthC, predsC)$auc
  SSVS_Cal$Acc[d] <- mean((predsCssvs > 0.5) == truthC)
  SSVS_Cal$AUC[d] <- plot.roc(truthC, predsCssvs)$auc
}









