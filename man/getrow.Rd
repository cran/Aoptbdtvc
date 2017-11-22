\name{getrow}
\alias{getrow}
\title{Get a particular row of incidence matrix}
\description{This function returns a particular row of incidence matrix with specified properties.}
\usage{getrow(v,b,k,r,r0,lambda,lambda0,N1,T,rownum,relaxed)}
\arguments{
	\item{v}{number of test treatments}
	\item{b}{number of blocks}
	\item{k}{block size}
	\item{r}{number of replications of the test treatments}
	\item{r0}{number of replications of the control}
	\item{lambda}{number of concurrences of two test treatments}
	\item{lambda0}{number of concurrences of a test treatment with the control}
	\item{N1}{Incidence matrix obtained till the previous row}
	\item{T}{Tabu list of deleted rows}
	\item{rownum}{the row number being obtained}
	\item{relaxed}{are the constraints being relaxed? TRUE or FALSE}
	}
\value{return the desired row of the incidence matrix}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{internal}