/*
 * ExistsUntil.cpp
 *
 *  Created on: May 20, 2014
 *      Author: nicola
 */

#include "ExistsUntil.h"

namespace ctl_sat {

ExistsUntil::ExistsUntil(Formula * f1, Formula * f2){

	this->f1 = f1 ;
	this->f2 = f2 ;

	type=EXISTS_UNTIL;

	string_format = string("E(").append(this->f1->toString()).append("U").append(this->f2->toString()).append(")");

};

ExistsUntil::~ExistsUntil() {}

Formula * ExistsUntil::removeDoubleNegations(){

	return new ExistsUntil(
				getLeftSubFormula()->removeDoubleNegations(),
				getRightSubFormula()->removeDoubleNegations()
			);

}

vector<Formula*> * ExistsUntil::positiveClosure(){

	vector<Formula*> * closure1 = getLeftSubFormula()->positiveClosure();
	vector<Formula*> * closure2 = getRightSubFormula()->positiveClosure();

	closure1->insert(closure1->end(), closure2->begin(), closure2->end());
	closure1->push_back(this);

	return closure1;

}


} /* namespace ctl_sat */
