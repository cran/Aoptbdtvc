\name{aoptgdtd}
\alias{aoptgdtd}
\title{A-optimal group divisible treatment designs}
\description{This function generates A-optimal group divisible treatment (GDT) designs for test vs control comparisons 
with specified parameters}
\usage{aoptgdtd(m,n,b,k,ntrial,pbar)}
\arguments{	
	\item{m}{number of rows such that m*n = number of test treatments}
	\item{n}{number of columns such that m*n = number of test treatments}
	\item{b}{number of blocks}
	\item{k}{block size}	
	\item{ntrial}{number of trials, default is 5}
	\item{pbar}{Logical value indicating whether progress bar will be displayed. Default
 is FALSE.}
	}
\value{It either returns a message that "Design not found" or "A-optimal Design does not exist for these parameters" or a design. If a design is found, it returns a list with following components
	\item{parameters}{parameters of the design}	
	\item{design}{generated A-optmal GDT design}
	\item{N}{incidence matrix of the generated A-optmal GDT design}
	\item{NNP}{concurrence matrix of the generated design}
}
\examples{
## construct an A-optimal GDT design with 12 (= 4 x 3) test treatments 
##in 12 blocks each of size 6
aoptgdtd(m=4,n=3,b=12,k=6)
## construct an A-optimal GDT design with 8 (= 4 x 2) test treatments 
##in 8 blocks each of size 4
aoptgdtd(m=4,n=2,b=8,k=4)
##design does not exist
aoptgdtd(4,2,8,2)
##Design not found
\dontrun{aoptgdtd(3,3,15,3)}
}
\author{Baidya Nath Mandal <mandal.stat@gmail.com>}
\references{
Jacroux, M. (1989). The A-optimality of block designs for comparing test treatments with a control, Journal of the American Statistical Association 84(405), 310–317.

Mandal, B. N., Parsad, R. and Dash, S. (2017). A-optimal block designs for comparing test treatments with control treatment(s) - an algorithmic approach, upcoming project report, ICAR-Indian Agricultural Statistics Research Institute, New Delhi, India.
}
\note{The function is useful to construct A-optimal GDT designs for number of test treatments <= 30 and up to block size 10. May not be very useful for m*n > 30. For k<=3, designs with larger number of test treatment may be obtained.}
\keyword{group divisible treatment design}
\keyword{A-optimal}