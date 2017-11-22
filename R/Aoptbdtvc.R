library(MASS)
library(lpSolve)
block.design=function(N)
{
  design=NULL
  v=nrow(N)
  b=ncol(N)
  kvec=t(N)%*%matrix(1,v,1)
  k=max(kvec)	
  for (i in 1:b)
  {
    trts=which(N[,i]>0)    
    design=rbind(design,rep(trts,N[trts,i]))    
  }
  return(design)
}

g=function(v,b,k,x,z,alpha,rho=0)
{
  A=k*(v-1)*(b*(k-x)-z)-(1-rho)*(v*(b*(k-x)-z)-b*k*k-b*x*x-2*x*z-z+2*k*(b*x+z))
  B=b*(1-rho)*(k*(b*x+z)-(b*x*x+2*x*z+z))+rho*(b*x+z)*(b*k-b*x-z)
  value=v*k*(((1-alpha+alpha*v)*(v-1)^2)/A+(1-alpha)*b/B) 
  return(value)
}

getts=function(v,b,k,alpha,rho)
{
  kby2=floor(k/2)
  ming=999999999
  ts=NULL
  for (x in 0:(kby2-1))
  {
      for(z in 0:b)
      {
          if (!(x==0 & z==0))
          {
              temp=g(v,b,k,x,z,alpha,rho)
              if (temp<ming) 
              {
                  ming=temp
                  ts=c(x,z)                  
              } else {
						            if (temp==ming) ts=rbind(ts,c(x,z))             
                      }
          }
      }          
  }
  return(ts)
}

getrow=function(v,b,k,r,r0,lambda,lambda0,N1,T,rownum,relaxed)
{
  kvec_obt=colSums(N1)
  w=matrix(0,1,b)
  for (j in 1:b)
  {
    if (kvec_obt[j]==0) w[,j]=1
    else w[,j]=1/kvec_obt[j]
  }		
  obj=w 
  constr1=matrix(1,1,b)		
  constr2=matrix(0,b,b)
  for (j in 1:b)	constr2[j,j]=1	
  constr3=N1 	
  constr4=T
  if (relaxed>0)  constr=rbind(constr1,constr2,constr4) else constr=rbind(constr1,constr2,constr3,constr4)
  dir1=rep("=", times=(1))	
  dir2=rep("<=",times=(b))	
  dim(dir2)=c(b,1)	
  dir3=rep("=",times=(nrow(N1)))  
  dim(dir3)=c(nrow(N1),1)	
  dir4=rep("<",times=(nrow(constr4)))
  dim(dir4)=c(nrow(constr4),1)					
  if (relaxed>0) dir=rbind(dir1,dir2,dir4) else dir=rbind(dir1,dir2,dir3,dir4)
  rhs1=r
  rhs2=k-kvec_obt
  dim(rhs2)=c(b,1)
  rhs3=matrix(0,nrow(N1),1)
  for (j in 1:nrow(N1))
  {
    if (sum(N1[j,])>0) 
    {
      if (j==1) rhs3[j,]=lambda0 else rhs3[j,]=lambda      
    } else rhs3[j,]=0
  }		
  rhs4=matrix(r-0.5,nrow(constr4),1)	
  if (relaxed>0) rhs=rbind(rhs1,rhs2,rhs4) else rhs=rbind(rhs1,rhs2,rhs3,rhs4)
  sol=lp (direction = "max", obj, constr, dir, rhs,transpose.constraints = TRUE, all.bin=TRUE, use.rw=TRUE)
  if (sol[[28]]==0) 
  {	
    row=sol[[12]]
    dim(row)=c(1,b)
    if (rownum>nrow(N1)) N1=rbind(N1,row) else N1[rownum,]=row		
  }
  return(N1)	
}

alternate.sol=function(v,b,k,r,r0,lambda,lambda0,N1,T,relaxed)
{
  row_detected=0	
  result=0
  k0=1   
  while (k0<=min(4,nrow(N1)) & row_detected==0)
  {
    row_indices=combn(2:nrow(N1),k0)
    nr=ncol(row_indices)
    j=1
    while(j<=nr & row_detected==0)
    {
      rows=row_indices[,j]
      T_temp=rbind(T,N1[rows,])			
      N1_temp=N1
      N1_temp[rows,]=matrix(0,1,b)
      cnt=0
      for (m in 1:k0)
      {
        rownum=rows[m]				
        N1_temp=getrow(v,b,k,r,r0,lambda,lambda0,N1_temp,T_temp,rownum,relaxed)
        if (sum(N1_temp[rownum,])>0) cnt=cnt+1
      }
      if (cnt==k0) 
      {
        row_detected=1
        result=list(rows,N1_temp)
      }
      j=j+1	
    }
    k0=k0+1				
  }
  return(result)
}
btibts=function(v,b,k,t,s,alpha,rho=0,ntrial,pbar)
{
  r0=s+b*t
  r=(b*k-r0)/v
  lambda0=(s*(t+1)*(k-t-1)+(b-s)*t*(k-t))/v
  lambda=(r*(k-1)-lambda0)/(v-1)
  q2=s*(k-t-1)/v
  q3=(q2*(k-t-2)+(r-q2)*(k-t-1))/(v-1)
  if (r-floor(r)==0 & q2-floor(q2)==0 & q3-floor(q3)==0 & lambda-floor(lambda)==0 & lambda0-floor(lambda0)==0)
  {
      trial=0
      success=0				
      while(trial<ntrial & success==0)
      {
        trial=trial+1
        if (pbar==TRUE) 
        {
          if (Sys.info()[[1]]=="Windows") pb = winProgressBar(title = "progress bar", min = 0, max = v, width = 400) else pb=txtProgressBar(min = 0, max = v, style=3)
        }
        N1=matrix(0,1,b)
        cols=sample(b,b-s)
        N1[1,cols]=t
        if (s>0)
        {
          remblocks=setdiff(1:b,cols)
          N1[1,remblocks]=t+1
        }
        T=matrix(0,1,b)
        i=2	
        relaxed=0
        breaker=0
        while (i<=(v+1) & breaker==0)
        {
            N1=getrow(v,b,k,r,r0,lambda,lambda0,N1,T,i,relaxed)
            if (nrow(N1)<i) 
            {
              if(nrow(N1)>=2)
              {
                temp=alternate.sol(v,b,k,r,r0,lambda,lambda0,N1,T,relaxed)
                rows=temp[[1]]
                if (all(rows>0)) 
                {
                  T=rbind(T,N1[rows,])
                  N1=temp[[2]]												
                } else breaker=1
                if (nrow(T)>5*v) breaker=1
              } else breaker=1
            } 					
            Sys.sleep(0.1)
            if (pbar==TRUE) 
            {
              if (Sys.info()[[1]]=="Windows") setWinProgressBar(pb, i,title=paste(round((i-1)*100/v, 0),"% done,","row=",i, ",trial=",trial)) else  setTxtProgressBar(pb, i)
            }
            i=nrow(N1)+1	
        }
        if (nrow(N1)==(v+1)) 
        {
            success=1
            NNP=N1%*%t(N1)
            rvec=rowSums(N1)
            R=diag(rvec,nrow=(v+1))
            diag(NNP)=rvec
            design=block.design(N1)
		        C=R-NNP/k
		        P=matrix(0,v*(v+1)/2,v+1)
		        temp=0
		        for(ii in 1:v)
		        {
			        for(jj in (ii+1):(v+1))
			        {
				        temp=temp+1
				        P[temp,ii]=1
				        P[temp,jj]=-1
			        }
		        }
		      Pc=P[1:v,]
		      Pt=P[(v+1):(v*(v+1)/2),]
		      if(length(Pt)==(v+1)) dim(Pt)=c(1,(v+1))
		      Cinv=ginv(C)
		      den=(1-alpha)*sum(diag(Pc%*%Cinv%*%t(Pc)))+alpha*sum(diag(Pt%*%Cinv%*%t(Pt)))
		      nume=g(v,b,k,t,s,alpha,rho)
		      Aeff=nume/den
          if (s>0) type="S" else type="R"
          parameter=c(v,b,k,t,s,alpha, rho,round(Aeff,3),type)
		  names(parameter)=c("v","b","k","t","s","alpha","rho","A-eff","type")
          txtparm=paste(as.character(v),as.character( b), as.character( k),as.character( t),as.character( s), as.character( alpha), as.character( rho))
          result=list(parameters=noquote(parameter),design=design,N=N1,NNP=NNP)
        } else {
                    result="Design not found"	
                    parameter=c(v,b,k,t,s, alpha, rho)
                }
        	if (pbar==TRUE) close(pb)
      }
  } else {
            result="BTIB design does not exist for these parameters"
            parameter=c(v,b,k,t,s,alpha, rho)              
          }
  return(result)  
}

wtaoptbtib=function(v,b,k,alpha,rho=0,ntrial=5,pbar=FALSE)
{
	if(k%%2!=0)
	{
			if (alpha/(1-alpha) <=((2*v*k-2*v-k+1)^2-(k-1)^2*(v-1)^2+(rho*rho*(2*v-k-1)^2+2*rho*(2*v-k-1)*(2*v*k-2*v-k+1)))/v*((k-1)*(v-1))^2) c1=1 else c1=0
			
	} else {
				if (alpha/(1-alpha) <=(2*v*k-2*v-k)^2-k^2*(v-1)^2+(rho*rho*(2*v-k)^2+2*rho*(2*v-k)*(2*v*k-2*v-k))/v*(k*(v-1))^2) c1=1 else c1=0
			}	
	if (c1==1)
	{
		ts=getts(v,b,k,alpha,rho)
		dim(ts)=c(length(ts)/2,2)
		if(nrow(ts)>1) 
		{
			output=vector("list",nrow(ts)) 
			for (i in 1:nrow(ts))
			{
				t=ts[i,1]
				s=ts[i,2]
				output[[i]]=btibts(v,b,k,t,s,alpha,rho,ntrial,pbar)		
			}  
		} else {
					t=ts[1,1]
					s=ts[1,2]
					output=btibts(v,b,k,t,s,alpha,rho,ntrial,pbar)	
				}
	} else {
				#output="Conditions of Lemma 5 are not satisfied"		
	      output="Certain conditions are not satisfied"			
			}
	return(output)
}

getr0=function(v,b,k)
{  
  minH1=99999999
  M=9999999
  for (r0 in 1:(b*k-v))
  {
    r=(b*k-r0)/v
    if (r-floor(r)==0)
    {
      rr0=floor(r)
      alphar0=floor(r0/b)
      Rr0=(r0-b*alphar0)*(alphar0+1)^2+(b-r0+b*alphar0)*alphar0^2
      m1r0=(k*r0-Rr0)/(v*k)
      Ar0=(b*k-r0)*(k-1)/k
      B1r0=((b*k-r0-v*rr0)*((rr0+1)*(k-1))^2+(v-b*k+r0+v*rr0)*(rr0*(k-1))^2)/k^2
      Abarr0=b*k*(k-1)-r0*(2*k-1)+Rr0
      lambdar0=floor(Abarr0/(v*(v-1)))
      B2r0=((Abarr0-v*(v-1)*lambdar0)*(lambdar0+1)^2+(v*(v-1)-Abarr0+v*(v-1)*lambdar0)*lambdar0^2)/k^2
      Br0=B1r0+B2r0
      temp=Br0-m1r0^2-((Ar0-m1r0)^2)/(v-1)
      if (abs(temp)<1e-8) temp=0
      Pr0=sqrt(temp)
      m2r0=(Ar0-m1r0-sqrt((v-1)/(v-2))*Pr0)/(v-1)
      m3r0=(Ar0-m1r0+sqrt((v-1)*(v-2))*Pr0)/(v-1)
      temp2=Br0-(Ar0^2)/v
      if (abs(temp2)<1e-8) temp2=0
      Phatr0=sqrt(temp2)
      m12r0=(Ar0-sqrt(v/(v-1))*Phatr0)/(v-1)
      m13r0=(Ar0+sqrt(v*(v-1))*Phatr0)/(v-1)
      if (m1r0 <= m2r0) H1r0=1/m1r0+(v-2)/m2r0+1/m3r0 else H1r0=(v-1)/m12r0+1/m13r0
      if (H1r0<minH1) 
      {
          minH1=H1r0
          r0star=r0
      }
      m1hatr0=min((r0*k-Rr0)/(v*k),(Ar0-2/k)/v)
      m4r0=(Ar0-2/k-m1r0)/(v-1)
      H2r0=1/m1hatr0+(v-1)/m4r0
      Mr0=min(H1r0,H2r0)
      if (Mr0<M) M=Mr0      
    }
  }
  out=list(r0star=r0star,M=M)
  return(out)
}

aoptgdtd=function(m,n,b,k,ntrial=5,pbar=FALSE)
{
  v=m*n
  out=getr0(v,b,k)
  r0=out$r0star
  r=(b*k-r0)/v
  rr0=floor(r)  
  alphar0=floor(r0/b)
  Rr0=(r0-b*alphar0)*(alphar0+1)^2+(b-r0+b*alphar0)*alphar0^2
  lambda0=(r0*k-Rr0)/v  
  lambda1=(r*(k-1)-lambda0-(m-1)*n)/(v-1)
  if (r-floor(r)==0 & lambda1-floor(lambda1)==0 & lambda0-floor(lambda0)==0)
  {
      trial=0
      success=0				
      while(trial<ntrial & success==0)
      {
        trial=trial+1   
        if (pbar==TRUE) 
        {
          if (Sys.info()[[1]]=="Windows") pb = winProgressBar(title = "progress bar", min = 0, max = v, width = 400) else pb=txtProgressBar(min = 0, max = v, style=3)
        }
        N1=matrix(0,1,b)        
        if (r0>b) 
        {
          n2=(r0+b*(alphar0+1))/(2*alphar0+1)
          if (n2>=0 & n2<=b) s=b-n2 else s=0
          t=alphar0
          cols=sample(b,b-s)
          N1[1,cols]=t
          if (s>0)
          {
            remblocks=setdiff(1:b,cols)
            N1[1,remblocks]=t+1
          }
        } else {
                cols=sample(b,r0)
                N1[1,cols]=1
              }        
        T=matrix(0,1,b)
        i=2	
        relaxed=0
        breaker=0
        while (i<=(v+1) & breaker==0)
        {
            N1=getrow2(m,n,b,k,r,r0,lambda1,lambda0,N1,T,i,relaxed)
            if (nrow(N1)<i) 
            {
              temp=alternate.sol2(m,n,b,k,r,r0,lambda1,lambda0,N1,T,relaxed)
              rows=temp[[1]]
              if (all(rows>0)) 
              {
                T=rbind(T,N1[rows,])
                N1=temp[[2]]												
              } else breaker=1
              if (nrow(T)>5*v) breaker=1
            } 					
            Sys.sleep(0.1)
            if (pbar==TRUE) 
            {
              if (Sys.info()[[1]]=="Windows") setWinProgressBar(pb, i,title=paste(round((i-1)*100/v, 0),"% done,","row=",i, ",trial=",trial)) else  setTxtProgressBar(pb, i)
            }
            i=nrow(N1)+1	
        }
        if (nrow(N1)==(v+1)) 
        {
            success=1
            if (is.matrix(N1))
            {  
              NNP=N1%*%t(N1)
              rvec=rowSums(N1)
              R=diag(rvec,nrow=(v+1))
              diag(NNP)=rvec
              design=block.design(N1)
              C=R-NNP/k
              C11=C[-1,-1]
              e=eigen(C11)
              ev=e$values
              sumev=sum(1/ev)
              Aeff=out$M/sumev    
              parameters=c(m,n,b,k,r,r0,lambda1,lambda0)
              names(parameters)=c("m","n","b","k","r","r0","lambda1","lambda0")
              result=list(parameters=parameters,design=design,N=N1,NNP=NNP,Aeff=Aeff)              
            }            
        } 
        if (pbar==TRUE) close(pb)
      }
      if (success==0) 
      {
        design="Design not found"	
        result=list(m=m,n=n,b=b,k=k,r=r,r0=r0,lambda1=lambda1,lambda0=lambda0,design=design)
        parameter=c(m,n,b,k,r,r0,lambda1,lambda0)         
      }	
  } else {
              result="A-optimal Design does not exist for these parameters"
              parameter=c(m,n,b,k,r,r0,lambda1,lambda0)               
         }
  return(result)
}

check.group=function(m,n,x,y)
{
  
  i1=ceiling(x/n) 
  i2=ceiling(y/n)
  if (i1!=i2) group="different" else group="same"
  return(group)
}

getrow2=function(m,n,b,k,r,r0,lambda1,lambda0,N1,T,rownum,relaxed)
{
  kvec_obt=colSums(N1)
  w=matrix(0,1,b)
  for (j in 1:b)
  {
    if (kvec_obt[j]==0) w[,j]=1
    else w[,j]=1/kvec_obt[j]
  }		
  obj=w	
  constr1=matrix(1,1,b)		
  constr2=matrix(0,b,b)
  for (j in 1:b)	constr2[j,j]=1	
  constr3=N1 	
  constr4=T
  if (relaxed>0)  constr=rbind(constr1,constr2,constr4) else constr=rbind(constr1,constr2,constr3,constr4)
  dir1=rep("=", times=(1))	
  dir2=rep("<=",times=(b))	
  dim(dir2)=c(b,1)	
  dir3=rep("=",times=(nrow(N1)))  
  dim(dir3)=c(nrow(N1),1)	
  dir4=rep("<",times=(nrow(constr4)))
  dim(dir4)=c(nrow(constr4),1)					
  if (relaxed>0) dir=rbind(dir1,dir2,dir4) else dir=rbind(dir1,dir2,dir3,dir4)
  rhs1=r
  rhs2=k-kvec_obt
  dim(rhs2)=c(b,1)
  rhs3=matrix(0,nrow(N1),1)
  for (j in 1:nrow(N1))
  {
    if (sum(N1[j,])>0) 
    {
      if (j==1) rhs3[j,]=lambda0 else {
                                      if (check.group(m,n,(j-1),(rownum-1))=="same") rhs3[j,]=lambda1 else rhs3[j,]=lambda1+1
                                    }
    } else rhs3[j,]=0
  }		
  rhs4=matrix(r-0.5,nrow(constr4),1)	
  if (relaxed>0) rhs=rbind(rhs1,rhs2,rhs4) else rhs=rbind(rhs1,rhs2,rhs3,rhs4)
  sol=lp (direction = "max", obj, constr, dir, rhs,transpose.constraints = TRUE, all.bin=TRUE, use.rw=TRUE)
  if (sol[[28]]==0) 
  {	
    row=sol[[12]]
    dim(row)=c(1,b)
    if (rownum>nrow(N1)) N1=rbind(N1,row) else N1[rownum,]=row		
  }
  return(N1)	
}

alternate.sol2=function(m,n,b,k,r,r0,lambda1,lambda0,N1,T,relaxed)
{
  row_detected=0	
  result=0
  k0=1   
  while (k0<=min(4,nrow(N1)-1) & row_detected==0)
  {
    row_indices=combn(nrow(N1),k0)
    nr=ncol(row_indices)
    j=1
    while(j<=nr & row_detected==0)
    {
      rows=row_indices[,j]
      T_temp=rbind(T,N1[rows,])			
      N1_temp=N1
      N1_temp[rows,]=matrix(0,1,b)
      cnt=0
      for (m in 1:k0)
      {
        rownum=rows[m]				
        N1_temp=getrow2(m,n,b,k,r,r0,lambda1,lambda0,N1_temp,T_temp,rownum,relaxed)
        if (sum(N1_temp[rownum,])>0) cnt=cnt+1
      }
      if (cnt==k0) 
      {
        row_detected=1
        result=list(rows,N1_temp)
      }
      j=j+1	
    }
    k0=k0+1				
  }
  return(result)
}

gbbpb=function(v1,v2,b,k,x,z)
{
	C=b*x+z
	A=(k*C-v2*(b*x*x+2*x*z+z))/(v1*k)
	B=(b*k*v1*(k-1)-v2*(v1*(k-1)+k)*C+v2*v2*(b*x*x+2*x*z+z))/(v1*k)
	a=v2*(v1-1)^2
	d=v1*(v2-1)
	value=1/A+a/B+d/C
  return(value)
}

getwq=function(v1,v2,b,k)
{
  kbyv2=floor(k/v2)
  ming=999999999
  wq=NULL
  for (x in 0:(kbyv2-1))
  {
      for(z in 0:b)
      {
          if (!(x==0 & z==0))
          {
              temp=gbbpb(v1,v2,b,k,x,z)
              if (temp<ming) 
              {
                  ming=temp                  
                  wq=c(x,z)                  
              } else if (temp==ming)
                    {
                      wq=rbind(wq,c(x,z))             
                    }            
          }
      }          
  }  
  return(wq)
}

bbpbwq=function(v1,v2,b,k,w,q,ntrial,pbar)
{
  r0=q+b*w
  r=(b*k-v2*r0)/v1
  lambda2=r0
  lambda12=(q*(w+1)*(k-v2*(w+1))+(b-q)*w*(k-v2*w))/v1
  lambda1=(r*(k-1)-v2*lambda12)/(v1-1)
  if (r-floor(r)==0 & r0-floor(r0)==0 & lambda1-floor(lambda1)==0 & lambda12-floor(lambda12)==0)
  {
    trial=0
    success=0				
    while(trial<ntrial & success==0)
    {
      trial=trial+1
      if (pbar==TRUE) 
      {
        if (Sys.info()[[1]]=="Windows") pb = winProgressBar(title = "progress bar", min = 0, max = v1+v2, width = 400) else pb=txtProgressBar(min = 0, max = v1+v2, style=3)
      }
      N1=matrix(0,v2,b)
      if (b>q) 
      {
        cols=sample(b,b-q)
        N1[1:v2,cols]=w
        if (q>0)
        {
          remblocks=setdiff(1:b,cols)
          N1[1:v2,remblocks]=w+1
        }
      } else N1[1:v2,1:b]=w+1
      T=matrix(0,1,b)
      i=v2+1	
      relaxed=0
      breaker=0
      while (i<=(v1+v2) & breaker==0)
      {
        N1=getrow3(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1,T,i,relaxed)
        if (nrow(N1)<i) 
        {
          temp=alternate.sol3(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1,T,relaxed)
          rows=temp[[1]]
          if (all(rows>0)) 
          {
            T=rbind(T,N1[rows,])
            N1=temp[[2]]												
          } else breaker=1
          if (nrow(T)>5*(v1+v2)) breaker=1
        } 					
        Sys.sleep(0.1)
        if (pbar==TRUE) 
        {
          if (Sys.info()[[1]]=="Windows") setWinProgressBar(pb, i,title=paste(round((i-1)*100/(v1+v2), 0),"% done,","row=",i, ",trial=",trial)) else  setTxtProgressBar(pb, i)
        }
        i=nrow(N1)+1	
      }
      if (nrow(N1)==(v1+v2)) 
      {
        success=1
        NNP=N1%*%t(N1)
        rvec=rowSums(N1)
        R=diag(rvec,nrow=(v1+v2))
        diag(NNP)=rvec
        adtt=r-NNP[v2+1,v2+1]/k	
        adttdash=-lambda1/k
        dss=r0-NNP[1,1]/k
        dssdash=-lambda2/k
        bts=-lambda12/k
        f1bar=adtt
        f2bar=adttdash
        f3bar=dssdash
        f4bar=dss
        f5bar=dssdash
        design=block.design(N1)
        Aeff=gbbpb(v1,v2,b,k,w,q)/(v2*(v1-1)/(f1bar-f2bar)+v1*(v2-1)/(f4bar-f5bar)+v2/(f1bar+(v1-1)*f2bar))
        if (q>0) type="S" else type="R"
        parameters=c(v1,v2,b,k,w,q,type)
        names(parameters)=c("v1","v2","b","k","w","q","type")
        result=list(parameters=parameters,design=design,N=N1,NNP=NNP,Aeff=Aeff,type=type)	            		
      } else {
        result="Design not found"	
        parameter=c(v1,v2,b,k,w,q)                    		 
      }
      if (pbar==TRUE) close(pb)
    }
  } else {
    result="BBPB design does not exist for these parameters"
    parameter=c(v1,v2,b,k,w,q)        	    
  }
  return(result)
}

getrow3=function(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1,T,rownum,relaxed)
{
  kvec_obt=colSums(N1)
  w=matrix(0,1,b)
  for (j in 1:b)
  {
    if (kvec_obt[j]==0) w[,j]=1
    else w[,j]=1/kvec_obt[j]
  }		
  obj=w	
  constr1=matrix(1,1,b)		
  constr2=matrix(0,b,b)
  for (j in 1:b) constr2[j,j]=1	
  constr3=N1 	
  constr4=T
  if (relaxed>0) constr=rbind(constr1,constr2,constr4) else constr=rbind(constr1,constr2,constr3,constr4)
  dir1=rep("=", times=(1))	
  dir2=rep("<=",times=(b))	
  dim(dir2)=c(b,1)	
  dir3=rep("=",times=(nrow(N1)))  
  dim(dir3)=c(nrow(N1),1)	
  dir4=rep("<",times=(nrow(constr4)))
  dim(dir4)=c(nrow(constr4),1)					
  if (relaxed>0) dir=rbind(dir1,dir2,dir4) else dir=rbind(dir1,dir2,dir3,dir4)
  rhs1=r
  rhs2=k-kvec_obt
  dim(rhs2)=c(b,1)
  rhs3=matrix(0,nrow(N1),1)
  for (j in 1:nrow(N1))
  {
    if (sum(N1[j,])>0) 
    {
      if (j<=v2) rhs3[j,]=lambda12 else rhs3[j,]=lambda1      
    } else rhs3[j,]=0
  }		
  rhs4=matrix(r-0.5,nrow(constr4),1)	
  if (relaxed>0) rhs=rbind(rhs1,rhs2,rhs4) else rhs=rbind(rhs1,rhs2,rhs3,rhs4)
  sol=lp (direction = "max", obj, constr, dir, rhs,transpose.constraints = TRUE, all.bin=TRUE, use.rw=TRUE)
  if (sol[[28]]==0) 
  {	
    row=sol[[12]]
    dim(row)=c(1,b)
    if (rownum>nrow(N1)) N1=rbind(N1,row) else N1[rownum,]=row    		
  }
  return(N1)	
}

alternate.sol3=function(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1,T,relaxed)
{
  row_detected=0	
  result=0
  k0=1   
  while (k0<=min(4,nrow(N1)-v2) & row_detected==0)
  {
    row_indices=combn((v2+1):nrow(N1),k0)
    nr=ncol(row_indices)
    j=1
    while(j<=nr & row_detected==0)
    {
      rows=row_indices[,j]
      T_temp=rbind(T,N1[rows,])			
      N1_temp=N1
      N1_temp[rows,]=matrix(0,1,b)
      cnt=0
      for (m in 1:k0)
      {
        rownum=rows[m]				
        N1_temp=getrow3(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1_temp,T_temp,rownum,relaxed)
        if (sum(N1_temp[rownum,])>0) cnt=cnt+1
      }
      if (cnt==k0) 
      {
        row_detected=1
        result=list(rows,N1_temp)
      }
      j=j+1	
    }
    k0=k0+1				
  }
  return(result)
}

aoptbbpb=function(v1,v2,b,k,ntrial=5,pbar=FALSE)
{
  
  wq=getwq(v1,v2,b,k)
  dim(wq)=c(length(wq)/2,2)
  for (i in 1:nrow(wq))
  {
    w=wq[i,1]
    q=wq[i,2]
    result=bbpbwq(v1,v2,b,k,w,q,ntrial,pbar)
    return(result)
  }  
}



