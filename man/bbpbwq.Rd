\name{bbpbwq}
\alias{bbpbwq}
\title{BBPB design with given parameters}
\description{This function returns incidence matrix of a BBPB design with given parameters.}
\usage{bbpbwq(v1,v2,b,k,w,q,ntrial)}
\arguments{
	\item{v1}{number of test treatments}
	\item{v2}{number of controls}
	\item{b}{number of blocks}
	\item{k}{block size}
	\item{w}{parameter w}
	\item{q}{parameter q}	
	\item{ntrial}{number of trials}
	}
\value{return the incidence matrix of BBPB design}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{internal}