\name{aoptbbpb}
\alias{aoptbbpb}
\title{A-optimal balanced bipartite block designs}
\description{This function generates A-optimal balanced bipartite block (BBPB) designs for tests vs controls comparisons 
with specified parameters}
\usage{aoptbbpb(v1,v2,b,k,ntrial,pbar)}
\arguments{	
	\item{v1}{number of test treatments}
	\item{v2}{number of controls}
	\item{b}{number of blocks}
	\item{k}{block size}	
	\item{ntrial}{number of trials, default is 5}
	\item{pbar}{logical value indicating whether progress bar will be displayed. Default
 is FALSE.}
	}
\value{It either returns a message that "Design not found" or "BBPB Design does not exist for these parameters" or a design. If a design is found, it returns a list with following components
	\item{parameters}{parameters of the design}	
	\item{design}{generated A-optmal BBPB design}
	\item{N}{incidence matrix of the generated A-optmal BBPB design}
	\item{NNP}{concurrence matrix of the generated design}
	\item{Aeff}{A-efficiency of the design}
	\item{type}{R- type or S- type design}
}
\examples{
##construct an A-optimal BBPB design with 5 test treatments and 3 control treatments in 
##12 blocks each of size 5
aoptbbpb(v1=5,v2=3,b=12,k=5)
##construct an A-optimal BBPB design with 6 test treatments and 3 control treatments in 
##6 blocks each of size 8
aoptbbpb(v1=6,v2=3,b=6,k=8)
##Design does not exist
#not run
aoptbbpb(3,2,9,3)
aoptbbpb(6,3,9,4)
#Design not found
\dontrun{aoptbbpb(3,3,12,4)}
}
\references{
Jaggi, S., Gupta, V. and Parsad, R. (1996). A-efficient block designs for comparing two disjoint sets of treatments, Communications in Statistics-Theory and Methods 25(5), 967–983.

Mandal, B. N., Parsad, R. and Dash, S. (2017). A-optimal block designs for comparing test treatments with control treatment(s) - an algorithmic approach, upcoming project report, ICAR-Indian Agricultural Statistics Research Institute, New Delhi, India.
}
\note{The function is useful to construct A-optimal BBPB designs for v1+v2 <= 30 and up to block size 10. May not be very useful beyond v1+v2 > 30. For k<=3, designs with larger v1+v2 may be obtained.}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\keyword{balanced bipartite block designs}
\keyword{A-optimal}