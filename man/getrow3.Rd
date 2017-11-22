\name{getrow3}
\alias{getrow3}
\title{Get a particular row of incidence matrix}
\description{This function returns a particular row of incidence matrix with specified properties.}
\usage{getrow3(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1,T,rownum,relaxed)}
\arguments{
	\item{v1}{number of test treatments}
	\item{v2}{number of controls}
	\item{b}{number of blocks}
	\item{k}{block size}
	\item{r}{number of replications of the test treatments}
	\item{r0}{number of replications of the control}
	\item{lambda1}{number of concurrences of two test treatments}
	\item{lambda0}{number of concurrences of a test treatment with the control}
	\item{N1}{Incidence matrix obtained till the previous row}
	\item{T}{Tabu list of deleted rows}
	\item{rownum}{the row number being obtained}
	\item{relaxed}{are the constraints being relaxed? TRUE or FALSE}
	}
\value{return the desired row of the incidence matrix}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{internal}