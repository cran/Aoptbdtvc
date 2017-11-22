\name{alternate.sol2}
\alias{alternate.sol2}
\title{Get an altnernate solution for particular row of incidence matrix}
\description{This function returns an alternate solution for a particular row of incidence matrix with specified properties.}
\usage{alternate.sol2(m,n,b,k,r,r0,lambda1,lambda0,N1,T,relaxed)}
\arguments{
	\item{m}{number of rows}
	\item{n}{number of columns}
	\item{b}{number of blocks}
	\item{k}{block size}
	\item{r}{number of replications of the test treatments}
	\item{r0}{number of replications of the control}
	\item{lambda1}{number of concurrences of two test treatments}
	\item{lambda0}{number of concurrences of a test treatment with the control}
	\item{N1}{Incidence matrix obtained till the previous row}
	\item{T}{Tabu list of deleted rows}
	\item{relaxed}{are the constraints being relaxed?}
	}
\value{return the desired row of the incidence matrix}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{internal}