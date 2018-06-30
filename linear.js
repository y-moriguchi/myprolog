/**
 * myprolog
 *
 * Copyright (c) 2018 Yuichiro MORIGUCHI
 *
 * This software is released under the MIT License.
 * http://opensource.org/licenses/mit-license.php
 **/
var operators;

function mapTerm(a, func) {
	var result = {},
		i,
		mapped;
	for(i in a) {
		if(a.hasOwnProperty(i)) {
			if(!!(mapped = func(a[i]))) {
				result[i] = mapped;
			}
		}
	}
}
function mergeTwoTerms(a, b, func) {
	var result = {},
		i,
		mapped;
	for(i in a) {
		if(a.hasOwnProperty(i)) {
			result[i] = a[i];
		}
	}
	for(i in b) {
		if(b.hasOwnProperty(i)) {
			if(a.hasOwnProperty(i)) {
				if(!!(mapped = func(a[i], b[i]))) {
					result[i] = mapped;
				}
			} else {
				result[i] = b[i];
			}
		}
	}
	return result;
}
function multiplyTerm(t, a) {
	return makeLinearTerm(mapTerm(t, function(x) { return x * a; }));
}
function negateTerm(t) {
	return makeLinearTerm(mapTerm(t, function(x) { return -x; }));
}
function addTerms(t, b) {
	return makeLinearTerm(mergeTwoTerms(t, b, function(x, y) { return x + y; }));
}
function subtractTerms(t, b) {
	return makeLinearTerm(mergeTwoTerms(t, b, function(x, y) { return x - y; }));
}
function substituteFactor(t, factor, substitute) {
	var tWithoutSubst;
	if(!t[factor]) {
		return t;
	}
	tWithoutSubst = mapTerm(t, function(x) { return x; });
	delete tWithoutSubst[factor];
	return addTerms(tWithoutSubst, multiplyTerm(t[factor], substitute));
}
function isConstantTerm(t) {
	var i;
	for(i in t) {
		if(t.hasOwnProperty(i) && i !== "") {
			return false;
		}
	}
	return true;
}
function termToString(term) {
	var result = "",
		i;
	for(i in term) {
		if(term.hasOwnProperty(i)) {
			if(result !== "" && term[i] > 0) {
				result += "+";
			}
			result += term[i] + i;
		}
	}
	return result === "" ? "0" : result;
}

operators = {
	"=": {
		symbol: " = ",
		negate: operators["="]
	},
	"<": {
		symbol: " < ",
		negate: operators[">"]
	},
	"<=": {
		symbol: " <= ",
		negate: operators[">="]
	},
	">": {
		symbol: " > ",
		negate: operators["<"]
	},
	">=": {
		symbol: " >= ",
		negate: operators["<="]
	}
};
function makeInequation(term1, term2, op) {
	function solve(factor) {
		var t1,
			t2,
			t3 = {},
			tLeft,
			tRight,
			opNew,
			i;
		if(term1[factor]) {
			t1 = term1;
			t2 = term2;
			opNew = t1[factor] > 0 ? op : op.negate;
		} else if(term2[factor]) {
			t1 = term2;
			t2 = term1;
			opNew = t1[factor] > 0 ? op.negate : op;
		} else {
			throw new Error("not solve by " + factor);
		}
		for(i in t1) {
			if(i !== factor && t1.hasOwnProperty(i)) {
				t3[i] = -t1[i];
			}
		}
		tLeft = {};
		tLeft[factor] = 1;
		tRight = multiplyTerm(addTerm(t2, t3), t1[factor]);
		return makeInequation(tLeft, tRight, opNew);
	}
	function toString() {
		return termToString(term1) + op.symbol + termToString(term2);
	}
	return function(message) {
		switch(message) {
		case "solve":     return solve;
		case "toString":  return toString;
		default:  throw new Error("invalid message " + message);
		}
	};
}
function makeInterval(sup, supOpen, inf, infOpen) {
	function toString() {
		var result = "";
		if(sup === null) {
			result = "(Inf, ";
		} else {
			result = (supOpen ? "(" : "[") + termToString(sup) + " ";
		}
		if(inf === null) {
			result = "-Inf)";
		} else {
			result = termToString(inf) + (infOpen ? ")" : "]");
		}
		return result;
	}
	function isDetermined() {
		return (sup === null || isConstantTerm(sup)) && (inf === null || isConstantTerm(inf));
	}
	function isContradiction() {
		if(sup === null || inf === null || !isDetermined()) {
			return false;
		} else if(sup[""] < inf[""]) {
			return true;
		} else if(sup[""] === inf[""] && (supOpen || infOpen)) {
			return true;
		} else {
			return false;
		}
	}
	function contains(x) {
		if(!isDetermined() || isContradiction()) {
			return false;
		}
		return (sup === null || (supOpen ? sup[""] > x : sup[""] >= x)) && (inf === null || (infOpen ? x > inf[""] : x >= inf[""]));
	}
	return function(message) {
		switch(message) {
		case "sup":              return sup;
		case "supOpen":          return sup === null || supOpen;
		case "inf":              return inf;
		case "infOpen":          return inf === null || infOpen;
		case "isContradiction":  return isContradiction;
		case "isDetermined":     return isDetermined;
		case "toString":         return toString;
		default:  throw new Error("invalid message " + message);
		}
	}
}
function makeIntervals(/*args of interval*/) {
	var args = Array.prototype.slice.call(arguments);
	function isDetermined() {
		var i;
		for(i = 0; i < args.length; i++) {
			if(!args[i]("isDetermined")()) {
				return false;
			}
		}
		return true;
	}
	function isContradiction() {
		var i;
		for(i = 0; i < args.length; i++) {
			if(args[i]("isContradiction")()) {
				return true;
			}
		}
		return false;
	}
	function reduce() {
		var i,
			sup = null,
			supOpen = true,
			inf = null,
			infOpen = true,
			supNew,
			supOpenNew,
			infNew,
			infOpenNew;
		if(!isDetermined()) {
			return null;
		}
		for(i = 0; i < args.length; i++) {
			supNew = args[i]("sup");
			supOpenNew = args[i]("supOpen");
			if(sup === null || sup > supNew || (sup === supNew && supOpenNew)) {
				sup = supNew;
				supOpen = supOpenNew;
			}
			infNew = args[i]("inf");
			infOpenNew = args[i]("infOpen");
			if(inf === null || inf < infNew || (inf === infNew && infOpenNew)) {
				inf = infNew;
				infOpen = infOpenNew;
			}
		}
		return makeInterval(sup, supOpen, inf, infOpen);
	}
	return function(message) {
		switch(message) {
		case "reduce":           return reduce;
		case "isContradiction":  return isContradiction;
		case "isDetermined":     return isDetermined;
		default:  throw new Error("invalid message " + message);
		}
	}
}

module.exports = {
	multiplyTerm,
	negateTerm,
	addTerms,
	subtractTerms,
	substituteFactor,
	isConstantTerm,
	termToString,
	makeInequation,
	makeInterval,
	makeIntervals
};
