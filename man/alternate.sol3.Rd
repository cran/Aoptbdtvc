\name{alternate.sol3}
\alias{alternate.sol3}
\title{Get an altnernate solution for particular row of incidence matrix}
\description{This function returns an alternate solution for a particular row of incidence matrix with specified properties.}
\usage{alternate.sol3(v1,v2,b,k,r,r0,lambda1,lambda2,lambda12,N1,T,relaxed)}
\arguments{
	\item{v1}{number of test treatments}
	\item{v2}{number of controls}
	\item{b}{number of blocks}
	\item{k}{block size}
	\item{r}{number of replications of the test treatments}
	\item{r0}{number of replications of the control}
	\item{lambda1}{number of concurrences of two test treatments}
	\item{lambda2}{number of concurrences between two control treatments}
	\item{lambda12}{number of concurrences between a test and a control treatment}
	\item{N1}{Incidence matrix obtained till the previous row}
	\item{T}{Tabu list of deleted rows}
	\item{relaxed}{are the constraints being relaxed?}
	}
\value{return the desired row of the incidence matrix}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{internal}