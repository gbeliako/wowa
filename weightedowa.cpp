/*
	Three different implementations of the Weighted OWA function.
	
	This library implements Torra's algorithm based on RIM quantifier interpolation, 
	Beliakov's prunned n-ary tree algorithm PnTA and the Implicit WOWA.
	
	
	The main functions are:
	weightedf  (PnTA method)
	weightedOWAQuantifierBuild followed by weightedOWAQuantifier (Torra)
	ImplicitWOWA (implicit)
	
	The user needs to supply the OWA weighting vector w, the inputs weightings p and the vector of inputs x
	all of dimension n.
	
	
	The details of these methods can be found in:
	
	G. Beliakov, H. Bustince, and T. Calvo. A Practical Guide to Averaging Functions.
	Springer, Berlin, Heidelberg, 2016.

	G. Beliakov. A method of introducing weights into OWA operators and other
	symmetric functions. In V. Kreinovich, editor, Uncertainty Modeling. Dedicated
	to B. Kovalerchuk, pages 37–52. Springer, Cham, 2017.
	
	G. Beliakov. Comparing apples and oranges: The weighted OWA function, submitted, 2017.

	V. Torra. The weighted OWA operator. Int. J. Intelligent Systems, 12:153–166, 1997.
	
	
	This program is distributed under LGPL-3 Licence without any charge. 
	
	
	Compile this file with g++ weightedowa.cpp or another C++ compiled. The code at the end
	illustrates the use of the library and main() can be commented out to use the code 
	in other programs.
	
	The library depends on the monotone spline library by Gleb Beliakov, included here as a .h file

	Please cite our work:
	

	G. Beliakov. A method of introducing weights into OWA operators and other
	symmetric functions. In V. Kreinovich, editor, Uncertainty Modeling. Dedicated
	to B. Kovalerchuk, pages 37–52. Springer, Cham, 2017.
	
	J.J. Dujmovic and G. Beliakov. Idempotent weighted aggregation based on binary
	aggregation trees. Int. J. Intelligent Systems, in press, DOI:10.1002/int.21828, 2017.


	Copyright Gleb Beliakov, 2017
	gleb@deakin.edu.au
*/



#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <iomanip>
#include <math.h>
#include <time.h>
#include <algorithm>
#include <numeric>
using namespace std;

#include "monspline.h"

template <class ForwardIterator, class T>
  void iota (ForwardIterator first, ForwardIterator last, T val)
{
  while (first!=last) {
    *first = val;
    ++first;
    ++val;
  }
}

template <typename Container>
struct compare_indirect_index
  {
  const Container& container;
  compare_indirect_index( const Container& container ): container( container ) { }
  bool operator () ( size_t lindex, size_t rindex ) const
    {
    return container[ lindex ] > container[ rindex ];
    }
  };

 
  
double OWA(int n, double x[],double w[])
 { /* no sorting is needed when used in the tree */
    double z=0;
    for(int i=0;i<n;i++) z+=x[i]*w[i];
    return z;
 }
 
double OWA(int n, double x[],double w[], int index[])
 { /* no sorting is needed when used in the tree */
    double z=0;
    for(int i=0;i<n;i++) z+=x[index[i]]*w[i];
    return z;
 }
 double node(int n, double x[], long int N[], long int C, int & k,
             double w[], double(*F)(int, double [],double[]), int indices[], double* z)
 {
   /* recursive function in the n-ary tree processing
   Parameters: x - input vector, N vector of multiplicities of  x
   m current level of recursion counted from L (root node)  to 0
   k - input-output parameter, the index of x[k] being processed   */	
   if(N[k]==0) k++;
   if(N[k]>= C) {  /* we use idempotency here to prune the tree */
       N[k] -= C;
       if(N[k]<=0) return x[indices[k++]]; else return x[indices[k]];
   }
    C /= n;
   /* tree not pruned, process the children nodes */
   //if (C == 0) k++;
   for(int i=0;i<n;i++) z[i]=node(n,x,N,C,k,w,F,indices,z+n);
   return F(n,z,w);
}


double weightedf(double x[], double p[], double w[], int n,
         double(*F)(int, double[],double[]), int L)
/*
 Function F is the symmetric base aggregator.
 p[] = array of weights of inputs x[],
 w[] = array of weights for OWA, n = the dimension of x, p, w.
 the weights must add to one and be non-negative.
 L = number of binary tree levels. Run time = O[(n-1)L]  */
{
   double r=1.0/n;	
   long int t=0, C=1;
   int k=0;
   for(int i=0;i<L;i++) C*=n;  /* C=n^L */


  int indices[n];
  iota( indices, indices+n, 0 );  // found in <numeric>
  sort( indices, indices+n, compare_indirect_index <typeof(x)> ( x ) );

//   sortpairs(x, x+n, p);
   long int N[n]; /* multiplicities of x based on the weights */

   for(int i=0;i<n-1;i++)  {
  	   N[i]=p[indices[i]]*C+r;   t+=N[i]; 
   }	
   N[n-1]=C-t;

   double *z=new double[(L+1)*n];
   double y= node(n,x,N,C,k,w,F,indices,z);
   delete[] z;
   return y;
}

void weightedOWAQuantifierBuild( double p[], double w[], int n, double temp[], int& T)
/*
 Builds the RIM quantifier of the Weighted OWA, should be called before weightedOWAQuantifier.
input:
 p[] = array of weights of the inputs,
 w[] = array of weights for OWA, n = the dimension of  p, w.
 the weights must add to one and be non-negative.
output: 
 temp[] = working memory, keeps the spline knots and coefficients for later use in weightedOWAQuantifier
 should be at least 12(n+1) in length and the memory should be allocated by the calling program
 T  = the number of knots in the monotone spline
 */
{
	double *h,*alpha, *beta,*gamma,*ttemp; // temp variables
	h=&temp[0];
	alpha=&temp[2*n+2];
	beta=&temp[4*(n+1)];
	gamma=&temp[6*(n+1)];
	ttemp=&temp[8*(n+1)];
	
	double *x=new double[n+1];
	double *y=new double[n+1];
	x[0]=0; y[0]=0;
	for(int i=1;i<=n;i++) {
			x[i]=double(i)/n;
			y[i]=y[i-1]+w[i-1];
		}
	
	T= BuildMonotonSpline(x,y,n+1,h,alpha,beta,gamma,ttemp);
	
	delete[] x;
	delete[] y;
}

double weightedOWAQuantifier(double x[], double p[], double w[], int n, double temp[], int T)
/*
 Calculates the value of the WOWA, with quantifier function obtained in weightedOWAQuantifierBuild

input: 
 x[] = inputs
 p[] = array of weights of inputs x[],
 w[] = array of weights for OWA, n = the dimension of x, p, w.
 the weights must add to one and be non-negative.
 temp[] = working memory, keeps the spline knots and coefficients computed in weightedOWAQuantifierBuild
 T  = the number of knots in the monotone spline, as computed in  weightedOWAQuantifierBuild
 */
{

  int indices[n];
  double weights[n];
  	double *h,*alpha, *beta,*gamma; // temp variables
	h=&temp[0];
	alpha=&temp[2*n+2];
	beta=&temp[4*(n+1)];
	gamma=&temp[6*(n+1)];
  
  iota( indices, indices+n, 0 );  // found in <numeric>
  sort( indices, indices+n, compare_indirect_index <typeof(x)> ( x ) );

// build the required values for the coefficients
	double t2=0;
	

	for(int i=0;i<n;i++) {
			t2 += p[indices[i]];
			weights[i]=MonotoneSplineValue(t2,h,alpha,beta,gamma,T);
	}

    for(int i=n-1;i>0;i--) {
		weights[i]=weights[i]-weights[i-1];
	}

  
   t2=0;
    return OWA(n,x,weights, indices);
}

#define MEPS 10e-12
double ImplicitWOWA(double x[], double p[], double w[], int n )
/*
	Calculates implicit Weighted OWA function
	input: 
 x[] = inputs
 p[] = array of weights of inputs x[],
 w[] = array of weights for OWA, n = the dimension of x, p, w.
 the weights need not add to one but should be  non-negative.
 n = the dimension of x,w,p
	
*/
{
  int indices[n];
  iota( indices, indices+n, 0 );  // found in <numeric>
  sort( indices, indices+n, compare_indirect_index <typeof(p)> ( p ) );

 	double den=OWA(n,p,w,indices);
	if(den<=MEPS) den=MEPS;
	
	double *px=new double[n];
	for(int i=0;i<n;i++) px[i]=p[i]*x[i];
	
  iota( indices, indices+n, 0 );  // found in <numeric>
  sort( indices, indices+n, compare_indirect_index <typeof(px)> ( px) );
	
	double numer=OWA(n,px,w,indices);
	delete[] px;
	return numer/den;
}

int main() {
/*
	This program illustrates the use of the three WOWA methods. 
	The main function can be commented out in order to use this library in other programs.

*/

// preparing some test inputs

int n=4, L=10; // dimension and the number of levels of the n-ary tree
double x[4]={0.3,0.4,0.8,0.2};   // inputs
double w[4]={0.4,0.35,0.2,0.05}; // OWA weights
double p[4]={0.3,0.25,0.3,0.15}; // inputs weights

/* calling the functions */
// calling the PnTA algorithm 
  double y=weightedf(x,p,w,n,&OWA,L);
  printf("WOWA %f \n",y);

// calling the standard WAM (note that x is not sorted, and OWA does not sort it)
   y=OWA(n,x,p);	
   printf("WAM %f \n",y);
   
// we can sort the values of x and get proper OWA   
  int indices[n];
  iota( indices, indices+n, 0 );  // found in <numeric>
  sort( indices, indices+n, compare_indirect_index <typeof(x)> ( x ) );   
   y=OWA(n,x,w, indices);	
   printf("OWA %f \n",y);
   
   
// preparing the data for RIM quantifier based WOWA 
  int T;
  double ttemp[4*12];
  weightedOWAQuantifierBuild(p,w,n,ttemp, T);
  
// calling the RIM quantifier based WOWA by Torra 
  y=weightedOWAQuantifier(x,p,w,n,ttemp,T);
  printf("Torra %f \n",y);

  // calling the implicit WOWA
	y=ImplicitWOWA(x,p,w,n);
    printf("implicit %f \n",y);
	
  
    return 0;
}