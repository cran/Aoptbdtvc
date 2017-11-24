\name{btibts}
\alias{btibts}
\title{BTIB design with given parameters}
\description{This function returns incidence matrix of a BTIB design with given parameters.}
\usage{btibts(v,b,k,t,s,alpha,rho=0,ntrial)}
\arguments{
	\item{v}{number of test treatments}
	\item{b}{number of blocks}
	\item{k}{block size}
	\item{t}{paramter t}
	\item{s}{parameter s}
	\item{alpha}{weight of the test versus test contrasts}
	\item{rho}{rho=0}
	\item{ntrial}{number of trials}
	}
\value{return the incidence matrix of a BTIB design}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{internal}