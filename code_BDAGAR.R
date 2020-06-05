
#Please change to your own directory
#setwd("/Users/Leiwen/Box Sync/Research/Submission/code_data")

library(maps)
#Import California map with counties
ca.county = map("county","california", fill=TRUE, plot=FALSE)


library(lattice)
library(mvtnorm)
library(matrixStats)
library(fields)
library(boot)
library(mapproj)
library(blockmatrix)
library(ggmcmc)
library(Matrix)
library(mcmc)
library(magic)
library(msos)
library(AICcmodavg)
library(coda)
library(mvtnorm)
library(invgamma)
library(MASS)
library(rjags)
library(R2jags)
library(readr)
library(spdep)
library(maptools)
library(classInt)
library(RColorBrewer)
library(tidyr)
library(LaplacesDemon)

######### Functions ############
Dinv_new <- function(Rho, n, cn, ns, udnei,q){
  Tau <- list()
  B <- list()
  invD <- list()
  for(i in 1:q){
    Tau[[i]] <- diag(n)
    B[[i]] <- matrix(0, n, n)
    for(j in 3:n){
      Tau[[i]][j,j] <- (1 + (ns[j-1] - 1) * Rho[i]^2) / (1 - Rho[i]^2)
      for(k in (udnei[(cn[j-1] + 1):(cn[j-1] + ns[j-1])])){
        B[[i]][j,k] <- Rho[i] / (1 + (ns[j-1] - 1) * Rho[i]^2)
      }
    }
    invD[[i]] <- t(diag(n) - B[[i]]) %*% Tau[[i]] %*% (diag(n) - B[[i]])
  }
  return(invD)
}
cor_fun = function(x){
  A21_est = diag(x[["eta0_21"]], n) + x[["eta1_21"]] * Minc
  
  invD_est = Dinv_new(c(x[["rho1"]],x[["rho2"]]), n, cn, ns, udnei,q=2)
  G_est = as.matrix(bdiag(1/x[["tausq1"]]*solve(invD_est[[1]]), 1/x[["tausq2"]]*solve(invD_est[[2]])))
  A_est = as.matrix(blockmatrix(names = c("0","A21","0","0"), 
                                A21=A21_est, dim=c(2,2)))
  L_est = solve(diag(2*n)-A_est)
  V_est = L_est%*%G_est%*%t(L_est)
  
  cor12 = diag(V_est[1:58, (1+58):(58+58)])/sqrt(diag(V_est[1:58, 1:58])*diag(V_est[(1+58):(58+58), (1+58):(58+58)]))
  return(cor12)
}

cor_fun1 = function(x){
  A21_est = diag(x[["eta0_21"]], n) + x[["eta1_21"]] * Minc
  
  invD_est = Dinv_new(c(x[["rho1"]],x[["rho2"]]), n, cn, ns, udnei,q=2)
  G_est = as.matrix(bdiag(1/x[["tausq1"]]*solve(invD_est[[1]]), 1/x[["tausq2"]]*solve(invD_est[[2]])))
  A_est = as.matrix(blockmatrix(names = c("0","A21","0","0"), 
                                A21=A21_est, dim=c(2,2)))
  L_est = solve(diag(2*n)-A_est)
  V_est = L_est%*%G_est%*%t(L_est)
  
  cor1 = diag(diag(V_est[1:58, 1:58])^(-0.5))%*%V_est[1:58, 1:58]%*%diag(diag(V_est[1:58, 1:58])^(-0.5))
  mean_cor1 = mean(cor1[which(Minc==1)])
  return(mean_cor1)
}

cor_fun2 = function(x){
  A21_est = diag(x[["eta0_21"]], n) + x[["eta1_21"]] * Minc
  
  invD_est = Dinv_new(c(x[["rho1"]],x[["rho2"]]), n, cn, ns, udnei,q=2)
  G_est = as.matrix(bdiag(1/x[["tausq1"]]*solve(invD_est[[1]]), 1/x[["tausq2"]]*solve(invD_est[[2]])))
  A_est = as.matrix(blockmatrix(names = c("0","A21","0","0"), 
                                A21=A21_est, dim=c(2,2)))
  L_est = solve(diag(2*n)-A_est)
  V_est = L_est%*%G_est%*%t(L_est)
  
  cor2 = diag(diag(V_est[(1:58)+58, (1:58)+58])^(-0.5))%*%V_est[(1:58)+58, (1:58)+58]%*%diag(diag(V_est[(1:58)+58, (1:58)+58])^(-0.5))
  mean_cor2 = mean(cor2[which(Minc==1)])
  return(mean_cor2)
}

mysummary = function(invector) {
  c(mean(invector), median(invector), sd(invector), quantile(invector, .025), quantile(invector,.975))
}



inclattice=function(m){
  n=m^2
  Minc=matrix(0,n,n)
  for(i in 1:(m-1))	for(j in 1:(m-1)) Minc[(i-1)*m+j,(i-1)*m+j+1]=Minc[(i-1)*m+j,i*m+j]=1
  for(i in 1:(m-1)) Minc[(i-1)*m+m,i*m+m]=1
  for(j in 1:(m-1)) Minc[(m-1)*m+j,(m-1)*m+j+1]=1
  Minc+t(Minc)
}

# Import dataset extracted from SEER
crude_rate_5y <- read_csv("crude_rate.csv")
covariates <- read_csv("county_attributes.csv")
race <- read_csv("race.csv")
sex <- read_csv("sex.csv")
insurance <- read_csv("insurance.csv")
# Import dataset for adult cigarette smoking rates
smoking <- read_csv("smoking.csv")
smoking$smoking <- as.numeric(substr(smoking$`Cigarette Smoking Rate `, 1,4))

crude_rate_CA = crude_rate_5y[substr(crude_rate_5y$State_county,1,2) == "CA",]
crude_rate_lung = crude_rate_CA[crude_rate_CA$Site_recode_ICD_O_3_WHO_2008=="Lung and Bronchus",]
crude_rate_lung = crude_rate_lung[order(extract_numeric(crude_rate_lung$State_county)),]

crude_rate_esophagus = crude_rate_CA[crude_rate_CA$Site_recode_ICD_O_3_WHO_2008=="Esophagus",]
crude_rate_esophagus = crude_rate_esophagus[order(extract_numeric(crude_rate_esophagus$State_county)),]

# Combine cancer data with the map for each county
county.ID <- sapply(strsplit(ca.county$names, ","), function(x) x[2])
ca.poly = map2SpatialPolygons(ca.county, IDs=county.ID)
ca.poly$rate_lung = crude_rate_lung$Crude_Rate
ca.poly$rate_esophagus = crude_rate_esophagus$Crude_Rate
ca.poly$smoking = smoking$smoking
# Merge covariates with incidence rate for each canser
county_attribute = covariates[substr(covariates$State_county,1,2) == "CA",]
county_attribute$state = extract_numeric(county_attribute$State_county)
county_attribute1 = data.frame(county_attribute[order(county_attribute$state),])
county_attribute1$V_Persons_age_18_ACS_2012_2016 = as.numeric(county_attribute1$V_Persons_age_18_ACS_2012_2016)/100
county_attribute1$V_Persons_age_65_ACS_2012_2016 = as.numeric(county_attribute1$V_Persons_age_65_ACS_2012_2016)/100
county_attribute1$VHighschooleducationACS2012201 = as.numeric(county_attribute1$VHighschooleducationACS2012201)/100
county_attribute1$VFamiliesbelowpovertyACS201220 = as.numeric(county_attribute1$VFamiliesbelowpovertyACS201220)/100
county_attribute1$V_Unemployed_ACS_2012_2016 = as.numeric(county_attribute1$V_Unemployed_ACS_2012_2016)/100

race1 = race[substr(race$State_county,1,2) == "CA"&race$Race_recode_White_Black_Other=="Black",]
sex1 = sex[substr(sex$State_county,1,2) == "CA"&sex$Sex=="Male",]
insurance1 = insurance[substr(insurance$State_county,1,2) == "CA"&insurance$Insurance_Recode_2007=="Uninsured",]


crude_rate_lung1 = cbind(crude_rate_lung, smoking$smoking, county_attribute1[,2:6], race1$Row_Percent, sex1$Row_Percent,insurance1$Row_Percent)
colnames(crude_rate_lung1) = c("county", "site", "rate", "count", "population", "smoking", "young","old", "highschool", "poverty", "unemployed", "black", "male", "uninsured")

crude_rate_esophagus1 = cbind(crude_rate_esophagus, smoking$smoking, county_attribute1[,2:6], race1$Row_Percent, sex1$Row_Percent,insurance1$Row_Percent)
colnames(crude_rate_esophagus1) = c("county", "site", "rate", "count", "population", "smoking", "young","old", "highschool", "poverty", "unemployed", "black", "male", "uninsured")

# Create adjacency matrix
ca.neighbors = poly2nb(ca.poly)
n=length(ca.neighbors)

Adj=sapply(ca.neighbors,function(x,n) {v=rep(0,n);v[x]=1;v},n)
colnames(Adj)=county.ID
ca.coord = coordinates(ca.poly)
ca.latrange=round(quantile(ca.coord[,2],c(0.25,0.75)))
ca.albersproj=mapproject(ca.coord[,1],ca.coord[,2],projection = "albers",param=ca.latrange)

perm=order(ca.albersproj$x-ca.albersproj$y)
colnames(Adj)[perm]

Adj_new=Adj[perm,perm]

n=nrow(Adj_new)
ni=rowSums(Adj_new)
maxn=max(ni)
neimat=matrix(0,n,maxn)
neighbors=lapply(1:n,function(x) which(Adj_new[x,]==1))
dneighbors=sapply(2:n,function(i) intersect(neighbors[[i]],1:(i-1)))
dni=sapply(dneighbors,length)
original_perm = 1:58
index2=c(1,which(dni==0)+1)

final_perm=c(original_perm[perm][index2],
             original_perm[perm][-index2])

Minc = Adj[final_perm,final_perm]
n=nrow(Minc)
ni=rowSums(Minc)
maxn=max(ni)
neimat=matrix(0,n,maxn)
neighbors=lapply(1:n,function(x) which(Minc[x,]==1))
dneighbors=sapply(2:n,function(i) intersect(neighbors[[i]],1:(i-1)))
dni=sapply(dneighbors,length)
nmax=max(dni)
cni=cumsum(dni)
dneimat=sapply(dneighbors, function(nei,nmax,n) c(nei,rep(n+1,nmax+1-length(nei))),nmax,n)
udnei=unlist(dneighbors)
ni_wo = sapply(neighbors,length)
cni_wo = cumsum(ni_wo)
udnei_wo = unlist(neighbors)
cn = c(0, cni)
ns = dni

# Create response vector and covariate matrix in regression for each cancer
Y1 = crude_rate_lung1$rate[final_perm]
Y2 = crude_rate_esophagus1$rate[final_perm]

X1 = as.matrix(cbind(1,crude_rate_lung1[,6:14]))[final_perm,]
X2 = as.matrix(cbind(1,crude_rate_esophagus1[,6:14]))[final_perm,]

#Model1 : lung, esophagus
Y.o1 = c(Y1,Y2)
X.o1 = as.matrix(bdiag(X1, X2))

#Model2 : esophagus, lung
Y.o2 = c(Y2,Y1)
X.o2 = as.matrix(bdiag(X2, X1))

region = seq(1:n)
cn = c(0, cni)
ns = dni
index = list()
for(i in 1:(n-2)){
  index[[i]] = region[-(udnei[(cn[i+1] + 1):(cn[i+1] + ns[i+1])])]
}
index1 = unlist(index)

# GMCAR model
sink("GMCAR.txt")
cat("
    model
    {
    Q1[1:k, 1:k] <- tau1*(D - rho1*Minc)
    Q2[1:k, 1:k] <- tau2*(D - rho2*Minc)
    
    W1[1:k] ~ dmnorm(rep(0, k), Q1)
    W2[1:k] ~ dmnorm(rep(0, k), Q2)
    
    
    A21 <- eta021 * I + eta121 * Minc
    
    W[1:k] <- W1
    W[(k+1):(2*k)] <- A21 %*% W1 + W2
    
    for (i in 1:k)
    {
    mu[i] <- X[i,] %*% beta + W[i]
    Y[i] ~ dnorm(mu[i], taue1)
    }
    for (i in (k+1):(2*k))
    {
    mu[i] <- X[i,] %*% beta + W[i]
    Y[i] ~ dnorm(mu[i], taue2)
    }
    
    rho1 ~ dunif(0, 0.999)
    rho2 ~ dunif(0, 0.999)
    tau1 ~ dgamma(2, 0.1)
    tau2 ~ dgamma(2, 0.1)
    eta021 ~ dnorm(0, 0.01)
    eta121 ~ dnorm(0, 0.01)
    
    taue1 ~ dgamma(2, 1)
    taue2 ~ dgamma(2, 1)
    vare1 <- 1/taue1
    vare2 <- 1/taue2
    
    beta[1:20] ~ dmnorm(rep(0,20), (0.001*I1))
    }
    ", fill = TRUE)
sink()

model.data <- list(k = n, I = diag(n), I1 = diag(20), Minc = Minc, D = diag(rowSums(Minc)), X = X.o1, Y = Y.o1)
model.data2 <- list(k = n, I = diag(n), I1 = diag(20), Minc = Minc, D = diag(rowSums(Minc)), X = X.o2, Y = Y.o2)

model.inits <- rep(list(list(rho1 = 0.1, rho2 = 0.1, tau1 = 1, tau2 = 1, eta021 = 1, 
                             eta121 = 1, taue1 = 1, taue2 = 1,
                             beta = rep(0, 20), W1 = rep(0.1, n), 
                             W2 = rep(0.1, n))),1)
model.param <- c("beta", "rho1", "rho2", "tau1", "tau2", "eta021", "eta121",
                 "vare1", "vare2", "W")
set.seed(123)
#Model1 result: esophagus | lung
est.MCAR <- jags(model.data, model.inits, model.param, "GMCAR.txt",
                 n.chains = 1, n.iter = 30000,n.burnin = 15000, n.thin = 1)
set.seed(123)
#Model2 result: lung | esophagus 
est.MCAR2 <- jags(model.data2, model.inits, model.param, "GMCAR.txt",
                  n.chains = 1, n.iter = 30000,n.burnin = 15000, n.thin = 1)


W_mcmc.c1 = est.MCAR$BUGSoutput$sims.array[,1,1:116]
W_mcmc.c2 = est.MCAR2$BUGSoutput$sims.array[,1,1:116]

########## WAIC ############

#Model 1
W1_mcmc = W_mcmc.c1[,1:58]
W2_mcmc = W_mcmc.c1[,59:116]

sample.mcmc1 = est.MCAR$BUGSoutput$sims.array[,1,c(117:136,144:145)]

PL_single <- matrix(0, nrow = 2*n, ncol = 15000)
for(i in 1:15000){
  theta <- sample.mcmc1[i,]
  
  beta1 <- theta[1:10]
  beta2 <- theta[11:20]
  sigmasq1 <- theta[21]
  sigmasq2 <- theta[22]
  
  PL_single[1:58,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq1), n)) - unlist(rep(1/(2*sigmasq1),n))*(Y1-X1%*%as.vector(beta1) - W1_mcmc[i,])^2
  PL_single[59:116,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq2), n)) - unlist(rep(1/(2*sigmasq2),n))*(Y2-X2%*%as.vector(beta2) - W2_mcmc[i,])^2
}

waic_car1 = WAIC(PL_single)

#Model 2
W1_mcmc = W_mcmc.c2[,1:58]
W2_mcmc = W_mcmc.c2[,59:116]

sample.mcmc2 = est.MCAR2$BUGSoutput$sims.array[,1,c(117:136,144:145)]

PL_single <- matrix(0, nrow = 2*n, ncol = 15000)
for(i in 1:15000){
  theta <- sample.mcmc2[i,]
  
  beta1 <- theta[1:10]
  beta2 <- theta[11:20]
  sigmasq1 <- theta[21]
  sigmasq2 <- theta[22]
  
  PL_single[1:58,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq1), n)) - unlist(rep(1/(2*sigmasq1),n))*(Y2-X2%*%as.vector(beta1) - W1_mcmc[i,])^2
  PL_single[59:116,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq2), n)) - unlist(rep(1/(2*sigmasq2),n))*(Y1-X1%*%as.vector(beta2) - W2_mcmc[i,])^2
}

waic_car2 = WAIC(PL_single)

#BDARAR model

sink("BDAGAR.txt")
cat("
    model
    {
    for(i in 1:2){
    Tau1[i, i] <- 1
    Tau2[i, i] <- 1
    
    
    for(j in 1:k){
    B1[i,j] <- 0
    B2[i,j] <- 0
    }
    }
    
    for(l in 1:(k-1)){
    for(h in (l+1):k){
    Tau1[l,h] <- 0
    Tau2[l,h] <- 0
    }
    }
    
    Tau1[2,1] <- 0
    Tau2[2,1] <- 0
    
    for (i in 3:k)
    {
    Tau1[i,i] <- (1 + (ns[i-1] - 1) * rho1^2) / (1 - rho1^2)
    Tau2[i,i] <- (1 + (ns[i-1] - 1) * rho2^2) / (1 - rho2^2)
    for(h in 1:(i-1)){
    Tau1[i,h] <- 0
    Tau2[i,h] <- 0
    }
    b1[i] <- rho1 / (1 + (ns[i-1] - 1) * rho1^2)
    b2[i] <- rho2 / (1 + (ns[i-1] - 1) * rho2^2)
    for(j in (udnei[(cn[i-1] + 1):(cn[i-1] + ns[i-1])])){
    B1[i,j] <- b1[i]
    B2[i,j] <- b2[i]
    }
    for(j in index1[((k)*(i-3)-cn[i-1]+1) : ((k)*(i-3)-cn[i-1] + (k - ns[i-1]))]){
    B1[i,j] <- 0
    B2[i,j] <- 0
    }
    }
    
    Q1 <- t(I - B1) %*% Tau1 %*% (I - B1)
    Q2 <- t(I - B2) %*% Tau2 %*% (I - B2)
    
    W1[1:k] ~ dmnorm(rep(0, k), tau1*Q1)
    W2[1:k] ~ dmnorm(rep(0, k), tau2*Q2)
    
    A21 <- eta021 * I + eta121 * Minc
    
    W[1:k] <- W1
    W[(k+1):(2*k)] <- A21 %*% W1 + W2
    
    for (i in 1:k)
    {
    mu[i] <- X[i,] %*% beta + W[i]
    Y[i] ~ dnorm(mu[i], taue1)
    }
    
    for (i in (k+1):(2*k))
    {
    mu[i] <- X[i,] %*% beta + W[i]
    Y[i] ~ dnorm(mu[i], taue2)
    }
    
    rho1 ~ dunif(0, 0.999)
    rho2 ~ dunif(0, 0.999)
    tau1 ~ dgamma(2, 0.1)
    tau2 ~ dgamma(2, 0.1)
    eta021 ~ dnorm(0, 0.01)
    eta121 ~ dnorm(0, 0.01)
    
    taue1 ~ dgamma(2, 1)
    taue2 ~ dgamma(2, 1)
    vare1 <- 1/taue1
    vare2 <- 1/taue2
    
    beta[1:20] ~ dmnorm(rep(0,20), (0.001*I1))
    }
    ", fill = TRUE)
sink()

model.data1 <- list(k = n, index1 = index1, I = diag(n), I1 = diag(20), Minc = Minc, ns = dni, cn = c(0, cni), udnei = udnei, X = X.o1, Y = Y.o1)
model.data2 <- list(k = n, index1 = index1, I = diag(n), I1 = diag(20), Minc = Minc, ns = dni, cn = c(0, cni), udnei = udnei, X = X.o2, Y = Y.o2)
model.inits <- rep(list(list(rho1 = 0.1, rho2 = 0.1,  tau1 = 1, tau2 = 1, eta021 = 1, 
                             eta121 = 1, taue1 = 1, taue2 = 1,
                             beta = rep(0, 20), W1 = rep(0.1, n), 
                             W2 = rep(0.1, n))),1)
model.param <- c("beta", "rho1", "rho2", "tau1", "tau2", "eta021", "eta121",
                 "vare1", "vare2", "W")
set.seed(123)
#Model1 result: esophagus | lung
estimate1 <- jags(model.data1, model.inits, model.param, "BDAGAR.txt",
                  n.chains = 1, n.iter = 30000,n.burnin = 15000, n.thin = 1)
set.seed(123)
#Model2 result: lung | esophagus 
estimate2 <- jags(model.data2, model.inits, model.param, "BDAGAR.txt",
                  n.chains = 1, n.iter = 30000,n.burnin = 15000, n.thin = 1)

estimate1$BUGSoutput$summary[-c(1:116),]
estimate2$BUGSoutput$summary[-c(1:116),]

estimate2 = readRDS("estimate2_dagar.rds")
estimate1 = readRDS("estimate1_dagar.rds")


W_mcmc.m1 = estimate1$BUGSoutput$sims.array[,1,1:116]
W_mcmc.m2 = estimate2$BUGSoutput$sims.array[,1,1:116]

########## WAIC ############

#Model 1
W1_mcmc = W_mcmc.m1[,1:58]
W2_mcmc = W_mcmc.m1[,59:116]

sample.mcmc1 = estimate1$BUGSoutput$sims.array[,1,c(117:136,144:145)]

PL_single <- matrix(0, nrow = 2*n, ncol = 15000)
for(i in 1:15000){
  #print(i)
  theta <- sample.mcmc1[i,]
  
  beta1 <- theta[1:10]
  beta2 <- theta[11:20]
  sigmasq1 <- theta[21]
  sigmasq2 <- theta[22]
  
  PL_single[1:58,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq1), n)) - unlist(rep(1/(2*sigmasq1),n))*(Y1-X1%*%as.vector(beta1) - W1_mcmc[i,])^2
  PL_single[59:116,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq2), n)) - unlist(rep(1/(2*sigmasq2),n))*(Y2-X2%*%as.vector(beta2) - W2_mcmc[i,])^2
}

waic_dagar1 = WAIC(PL_single)

#Model 2
W1_mcmc = W_mcmc.m2[,1:58]
W2_mcmc = W_mcmc.m2[,59:116]

sample.mcmc2 = estimate2$BUGSoutput$sims.array[,1,c(117:136,144:145)]

PL_single <- matrix(0, nrow = 2*n, ncol = 15000)
for(i in 1:15000){
  #print(i)
  theta <- sample.mcmc2[i,]
  
  beta1 <- theta[1:10]
  beta2 <- theta[11:20]
  sigmasq1 <- theta[21]
  sigmasq2 <- theta[22]
  
  PL_single[1:58,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq1), n)) - unlist(rep(1/(2*sigmasq1),n))*(Y2-X2%*%as.vector(beta1) - W1_mcmc[i,])^2
  PL_single[59:116,i] <- unlist(rep(-1/2*log(2*pi) - 1/2*log(sigmasq2), n)) - unlist(rep(1/(2*sigmasq2),n))*(Y1-X1%*%as.vector(beta2) - W2_mcmc[i,])^2
}

waic_dagar2 = WAIC(PL_single)


# Table 1 consists of values from waic_car1, waic_car2, waic_dagar1 and waic_dagar2.
# BDAGAR Model 2 has smallest WAIC, and estimates for coefficients are shown in Table 2.

# Figure 3: Posterior distribution of eat_021 and eta_121 for two models using BDAGAR
png("eta_posterior_new.png", units="mm", height = 155, width = 207, res=300)
par(mfrow=c(2,2))
hist(estimate1$BUGSoutput$sims.array[,1,138],xlab = "eta_0, esophagus | lung",ylab = "", main="")
hist(estimate1$BUGSoutput$sims.array[,1,139],xlab = "eta_1, esophagus | lung",ylab = "", main="")
hist(estimate2$BUGSoutput$sims.array[,1,138],xlab = "eta_0, lung | esophagus",ylab = "", main="")
hist(estimate2$BUGSoutput$sims.array[,1,139],xlab = "eta_1, lung | esophagus",ylab = "", main="")
dev.off()
mysummary(estimate1$BUGSoutput$sims.array[,1,138])
mysummary(estimate1$BUGSoutput$sims.array[,1,139])

## We only use BDAGAR Model2 for analysis below

############## correlations in the same region ######################
jags_result = estimate2$BUGSoutput$sims.array[,1,c(117:136,138:145)]
colnames(jags_result) = c("beta1", "beta2","beta3","beta4","beta5", "beta6", "beta7","beta8","beta9","beta10","beta11","beta12",
                          "beta13", "beta14","beta15","beta16","beta17", "beta18","beta19", "beta20","eta0_21", "eta1_21", "rho1", "rho2", 
                          "tausq1", "tausq2", "sigmasq1","sigmasq2")

estimate_result <- round(t(apply(jags_result, 2, mysummary)),2)


# Table 2 for parameter estimates
table_est = paste(estimate_result[,1], " (", estimate_result[,4], ", ",
                  estimate_result[,5], ")", sep="")

table1 <- data.frame(matrix(table_est[1:20], ncol = 2, byrow=F))
table2 <- data.frame(matrix(table_est[23:28], ncol = 2, byrow=T))

table <- rbind(table1, table2)
colnames(table) <- c("Esophagus", "Lung")
write.csv(table, "table_est.csv")


cor_jags = apply(jags_result,1,cor_fun)
sptial_cor1 = apply(jags_result, 1, cor_fun1)
mean(sptial_cor1)

sptial_cor2 = apply(jags_result, 1, cor_fun2)
mean(sptial_cor2)
quantile(sptial_cor2, c(0.025, 0.975))

cor_jags_est = apply(cor_jags,1,mysummary)

cor_jags_est12 = cor_jags_est[,1:58]
ca.poly$rate12 = cor_jags_est12[1,][order(final_perm)]
ca.poly$sig12 = 0
ca.poly$sig12[which(cor_jags_est12[4,][order(final_perm)] > 0| cor_jags_est12[5,][order(final_perm)]<0)] = 1
brks_fit12 = quantile(ca.poly$rate12)
color.pallete1 = brewer.pal(4,"Blues")
class.rate12 = classIntervals(var=ca.poly$rate12, n=4, style="fixed", 
                              fixedBreaks=brks_fit12, dataPrecision=4)
color.code.rate12 = findColours(class.rate12, color.pallete1)
ca.coords = coordinates(ca.poly)
leg.txt = c("0.970 - 0.979", "0.979 - 0.982", "0.982 - 0.985", "0.985 - 0.996") 

## Figure 4: Correlation between two diseases in each region
#pdf("cor_bivariate.pdf", height = 3.5, width = 5.5)
png("cor_bivariate_new.png", units="mm", height = 155, width = 207, res=300)
plot(ca.poly, col = color.code.rate12)
legend("bottomleft", title="Correlation", legend=leg.txt, xpd = TRUE, cex=0.5, bty="n", horiz = FALSE, 
       fill = color.pallete1)
dev.off()


############### Predictions ###################
beta_mcmc = sample.mcmc2[,1:20]

y.est = matrix(0,15000,2*n)
for(iter in 1:15000){
  y.est[iter,] = as.vector(X.o2 %*% as.vector(beta_mcmc[iter,]) + W_mcmc.m2[iter,])
}
y.mean = apply(y.est,2,mean)
ca.poly$rate_lung_est = y.mean[59:116][order(final_perm)]
ca.poly$rate_esophagus_est = y.mean[1:58][order(final_perm)]

brks_fit_lung = c(28, 41, 54, 70, 115)
brks_fit_esophagus = c(0, 3.6, 4.7, 6.7, 16)
color.pallete = brewer.pal(4,"OrRd")
class.rate_lung = classIntervals(var=ca.poly$rate_lung_est, n=4, style="fixed", 
                                 fixedBreaks=brks_fit_lung, dataPrecision=4)
class.rate_esophagus = classIntervals(var=ca.poly$rate_esophagus_est, n=4, style="fixed", 
                                      fixedBreaks=brks_fit_esophagus, dataPrecision=4)
color.code.rate_lung = findColours(class.rate_lung, color.pallete)
color.code.rate_esophagus = findColours(class.rate_esophagus, color.pallete)

# Figure 5 Plots for posterior mean

png("posterior_cancer_new.png", units="mm", height = 155, width = 240, res=300)
par(mfrow=c(2,2), oma = c(0,0,4,0) + 0.1, mar = c(0,0,1,0) + 0.1)

plot(ca.poly, col = color.code.rate_lung)
leg.txt1 = c("28-41", "41-54", "54-70","70-115")
legend("bottomleft", title="Lung cancer", legend=leg.txt1, cex=1.25, bty="n", horiz = FALSE, 
       fill = color.pallete)

plot(ca.poly, col = color.code.rate_esophagus)
leg.txt2 = c("0-3.6", "3.6-4.7", "4.7-6.7", "6.7-16")
legend("bottomleft", title="Esophageal cancer", legend=leg.txt2, cex=1.25, bty="n", horiz = FALSE, 
       fill = color.pallete)
dev.off()



brks_fit_lung = c(28, 41, 54, 70, 115)
brks_fit_esophagus = c(0, 3.6, 4.7, 6.7, 16)
ca.poly$rate_lung = crude_rate_lung$Crude_Rate
ca.poly$rate_esophagus = crude_rate_esophagus$Crude_Rate
class.rate_lung = classIntervals(var=ca.poly$rate_lung, n=4, style="fixed", 
                                 fixedBreaks=brks_fit_lung, dataPrecision=4)
class.rate_esophagus = classIntervals(var=ca.poly$rate_esophagus, n=4, style="fixed", 
                                      fixedBreaks=brks_fit_esophagus, dataPrecision=4)
color.pallete = brewer.pal(4,"OrRd")
color.code.rate_lung = findColours(class.rate_lung, color.pallete)
color.code.rate_esophagus = findColours(class.rate_esophagus, color.pallete)

###### Figure 1: Plot for raw incidence data ############
#pdf("incidence_bivariate.pdf", height = 7, width = 10)
png("incidence_bivariate_new.png", units="mm", height = 155, width = 240, res=300)
par(mfrow=c(2,2), oma = c(0,0,4,0) + 0.1, mar = c(0,0,1,0) + 0.1)

plot(ca.poly, col = color.code.rate_lung)
leg.txt1 = c("28-41", "41-54", "54-70","70-115")
legend("bottomleft", title="Lung cancer", legend=leg.txt1, cex=1.25, bty="n", horiz = FALSE, 
       fill = color.pallete)

plot(ca.poly, col = color.code.rate_esophagus)
leg.txt2 = c("0-3.6", "3.6-4.7", "4.7-6.7", "6.7-16")
legend("bottomleft", title="Esophageal cancer",legend=leg.txt2, cex=1.25, bty="n", horiz = FALSE, 
       fill = color.pallete)

dev.off()

###### Figure 2: Plot for smoking rates ############
brks_smoking = quantile(smoking$smoking)

class.rate_smoking = classIntervals(var=ca.poly$smoking, n=4, style="fixed", 
                                 fixedBreaks=brks_smoking, dataPrecision=4)

color.pallete = brewer.pal(4,"OrRd")
color.code.rate_smoking = findColours(class.rate_smoking, color.pallete)


png("somking_rate.png", units="mm", height = 155, width = 207, res=300)

plot(ca.poly, col = color.code.rate_smoking)
leg.txt1 = c("6.7-11.5", "11.5-13.9", "13.9-16.3","16.3-25.5")
legend("bottomleft", title="Smoking rate (%)", legend=leg.txt1, cex=1.25, bty="n", horiz = FALSE, 
       fill = color.pallete)

dev.off()

