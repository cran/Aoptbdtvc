\name{wtaoptbtib}
\alias{wtaoptbtib}
\title{Weighted A-optimal balanced treatment incomplete block designs}
\description{This function generates weighted A-optimal balanced treatment incomplete block design for test vs control comparisons with specified parameters}
\usage{wtaoptbtib(v,b,k,alpha,rho=0,ntrial=5)}
\arguments{	
	\item{v}{number of test treatments}
	\item{b}{number of blocks}
	\item{k}{block size}		
	\item{alpha}{Weight for test versus test comparisons. Should be between 0 to 1}
	\item{rho}{rho=0}
	\item{ntrial}{number of trials, default is 5}	
	}
\value{It either returns a message that "Design not found" or "BTIB design does not exist for these parameters" or "Certain conditions are not satisfied" or a design. If a design is found, it returns a list with following components
	\item{parameters}{parameters of the design}	
	\item{design}{generated weighted A-optmal BTIB design}
	\item{N}{incidence matrix of the generated weighted A-optmal BTIB design}
	\item{NNP}{concurrence matrix of the generated design}
}
\examples{
##construct a weighted A-optimal BTIB design with 4 test treatments in 6 blocks each of size 4 
##with weights to test vs test treatments comparisons as 0.6
wtaoptbtib(v=4,b=6,k=4,alpha=0.6,rho=0)
##construct an A-optimal BTIB design with 9 test treatments in 12 blocks each of size 4 
##with weights to test vs test treatments comparisons as 0
wtaoptbtib(v=9,b=12,k=4,alpha=0,rho=0)
##design not found
\dontrun{wtaoptbtib(v=3,b=6,k=5,alpha=0.2,rho=0)}
##BTIB design does not exist for these parameters
#Not run
wtaoptbtib(3,4,3,0.2,0)
}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\references{
Gupta, V., Ramana, D. and Parsad, R. (1999). Weighted A-efficiency of block designs for making treatment-control and treatment-treatment comparisons, Journal of statistical planning and inference 77(2), 301–319.

Mandal, B. N., Parsad, R. and Dash, S. (2017). A-optimal block designs for comparing test treatments with control treatment(s) - an algorithmic approach, upcoming project report, ICAR-Indian Agricultural Statistics Research Institute, New Delhi, India.
}
\note{The function is useful to construct weighted A-optimal BTIB designs upto 30  test treatments and up to block size 10. May not be very useful beyond 30 test treatments. For k<=3, designs with larger number of test treatments may be obtained.}
\keyword{balanced treatment incomplete block design}
\keyword{weighted A-optimal}