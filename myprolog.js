/**
 * myprolog
 *
 * Copyright (c) 2018 Yuichiro MORIGUCHI
 *
 * This software is released under the MIT License.
 * http://opensource.org/licenses/mit-license.php
 **/
var R = require("./node_modules/rena-js").clone(),
	K = require("./node_modules/kalimotxo").K;
R.ignore(/[ \t\n]+/);

function makeProlog(ngFunction) {
	var allRules = makeList(),
		currentRuleId = 1,
		parser,
		operator;
	function cutFunction() {
		return ngFunction();
	}

	function addOperator(name, command, precedence) {
		operator["add" + command](name,
			1200 - precedence,
			function(/* args */) { return makeCompoundTerm(name, Array.prototype.slice.call(arguments)); });
	}
	parser = R.or(
		R.t(/[a-z][a-zA-Z0-9_]*/, function(name) { return { name: name, args: [] }; })
			.t("(")
			.t(R.delimit(function(str, index) { return operator.parse(str, index); },
				",",
				function(x, op, inherit) { inherit.args.push(op); return inherit; }))
			.t(")")
			.action(function(x) { return makeCompoundTerm(x.name, x.args); }),
		R.t(/[a-z][a-zA-Z0-9_]*/, function(name) { return makeSymbol(name); }),
		R.t("!", function(name) { return makeSymbol("!"); }),
		R.t(/[A-Z][a-zA-Z0-9_]*/, function(name) { return makeVariable(name); }));
	operator = K.Operator({
		id: function(str, index) {
			var result = parser.parse(str, index);
			return !result ? result : {
				match: result.attribute,
				index: result.lastIndex
			};
		},
		actionId: function(x) { return x; },
		follow: /\)|$/
	});
	addOperator(":-", "InfixNonAssoc", 1200);
	addOperator(";", "InfixRToL", 1100);
	addOperator(",", "InfixRToL", 1000);
	function parseQuery(program) {
		var query = /\?- */g,
			match;
		if(query.exec(program)) {
			return operator.parse(program, query.lastIndex).attribute;
		} else {
			return null;
		}
	}
	function execute(program) {
		var resultQuery,
			resultRule;
		if(!!(resultQuery = parseQuery(program))) {
			return executeQuery(resultQuery);
		} else {
			resultRule = operator.parse(program, 0).attribute;
			if(resultRule.isCompoundTerm() && resultRule.getName() === ":-") {
				addRule(resultRule.getTerm(0), resultRule.getTerm(1));
			} else {
				addRule(resultRule, null);
			}
			return null;
		}
	}

	function executeQuery(query, aFrame) {
		var frame = aFrame ? aFrame : makeEmptyFrame();
		if(!query) {
			return function(success, fail) {
				return success(frame, fail);
			};
		} else if(query.isSymbol() && query.getValue() === "!") {
			return function(success, fail) {
				return success(frame, cutFunction);
			};
		} else if(query.isCompoundTerm() && query.getName() === ",") {
			return conjoin(query, frame);
		} else if(query.isCompoundTerm() && query.getName() === ";") {
			return disjoin(query, frame);
		} else {
			return simpleQuery(query, frame);
		}
	}
	function conjoin(query, frame) {
		return function(success, fail) {
			function successFunction(frame, fail) {
				return executeQuery(query.getTerm(1), frame)(success, fail);
			}
			return executeQuery(query.getTerm(0), frame)(successFunction, fail);
		};
	}
	function disjoin(query, frame) {
		return function(success, fail) {
			function failFunction() {
				return fail === cutFunction ? fail() : executeQuery(query.getTerm(1), frame);
			}
			return executeQuery(query.getTerm(0), frame)(success, failFunction);
		};
	}
	function simpleQuery(queryPattern, queryFrame) {
		var applied = getRules(queryPattern, queryFrame);
		function searchRule(applied) {
			if(applied.isNull()) {
				return function(success, fail) {
					return fail();
				}
			}
			return function(success, fail) {
				var ruleNew,
					unified;
				function failFunction() {
					return fail === cutFunction ? fail() : searchRule(applied.rest())(success, fail);
				}
				ruleNew = renameRuleVariable(applied.value());
				unified = unify(queryPattern, ruleNew.getConclusion(), queryFrame);
				return unified ? executeQuery(ruleNew.getBody(), unified)(success, failFunction) : failFunction();
			};
		}
		return searchRule(applied);
	}
	function renameRuleVariable(rule) {
		var ruleId = currentRuleId++;
		function retrieve(term) {
			var elements,
				i;
			if(!term) {
				return term;
			} else if(term.isVariable()) {
				return makeVariable(term.getName(), ruleId);
			} else if(term.isCompoundTerm()) {
				elements = [];
				for(i = 0; i < term.arity(); i++) {
					elements.push(retrieve(term.getTerm(i)));
				}
				return makeCompoundTerm(term.getName(), elements);
			} else {
				return term;
			}
		}
		return makeRule(retrieve(rule.getConclusion()), retrieve(rule.getBody()));
	}
	function unify(p1, p2, frame) {
		var tmpFrame,
			i;
		if(isEqual(p1, p2)) {
			return frame;
		} else if(p1.isVariable()) {
			return extendFrame(p1, p2, frame);
		} else if(p2.isVariable()) {
			return extendFrame(p2, p1, frame);
		} else if(p1.isCompoundTerm() && p2.isCompoundTerm() && p1.getName() === p2.getName() && p1.arity() === p2.arity()) {
			tmpFrame = frame;
			for(i = 0; i < p1.arity(); i++) {
				tmpFrame = unify(p1.getTerm(i), p2.getTerm(i), tmpFrame);
				if(!tmpFrame) {
					return null;
				}
			}
			return tmpFrame;
		} else {
			return null;
		}
	}
	function extendFrame(variable, val, frame) {
		var binding = getBoundValue(variable, frame);
		function isDependent(term) {
			var b,
				i;
			if(term.isVariable()) {
				return isEqual(variable, term) || ((b = getBoundValue(term, frame)) ? isDependent(b) : false);
			} else if(term.isCompoundTerm()) {
				for(i = 0; i < term.arity(); i++) {
					if(isDependent(term.getTerm(i))) {
						return true;
					}
				}
				return false;
			} else {
				return false;
			}
		}
		if(binding) {
			return unify(bindingVal, val, frame);
		} else if(val.isVariable()) {
			binding = getBoundValue(val, frame);
			return binding ? unify(variable, binding, frame) : bindValue(variable, val, frame);
		} else if(isDependent(val, variable, frame)) {
			return null;
		} else {
			return bindValue(variable, val, frame);
		}
	}

	function getRules(pattern, frame) {
		return allRules.getStream();
	}
	function addRuleFirst(conclusion, body) {
		var rule = makeRule(conclusion, body);
		allRules.unshift(rule);
	}
	function addRule(conclusion, body) {
		var rule = makeRule(conclusion, body);
		allRules.push(rule);
	}

	return {
		execute: execute,
		executeQuery: executeQuery,
		addRule: addRule,
		addRuleFirst: addRuleFirst
	};	
}

function makeList(aList) {
	var list = aList ? [].concat(aList) : [],
		me;
	function getStream(list, index) {
		return {
			value: function() {
				return list[index];
			},
			rest: function() {
				return getStream(list, index + 1);
			},
			isNull: function() {
				return index >= list.length;
			}
		};
	}
	return {
		unshift: function(element) {
			list.unshift(element);
		},
		push: function(element) {
			list.push(element);
		},
		getStream: function() {
			var listNew = [].concat(list);
			return getStream(listNew, 0);
		},
		toArray: function() {
			return [].concat(list);
		}
	};
}

function makeEmptyFrame() {
	return {
		key: function() { return void 0; },
		value: function() { return void 0; },
		rest: function() {
			throw new Error("frame not found");
		},
		isNull: function() { return true; }
	};
}
function getBoundValue(variable, frame) {
	var nowFrame = frame;
	for(; !nowFrame.isNull(); nowFrame = nowFrame.rest()) {
		if(nowFrame.key() === variable.toString()) {
			return nowFrame.value();
		}
	}
	return null;
}
function bindValue(variable, value, frame) {
	return {
		key: function() { return variable.toString(); },
		value: function() { return value; },
		rest: function() { return frame; },
		isNull: function() { return false; }
	};
}
function frameToObject(frame) {
	var nowFrame = frame,
		result = {};
	for(; !nowFrame.isNull(); nowFrame = nowFrame.rest()) {
		result[nowFrame.key()] = nowFrame.value();
	}
	return result;
}

function makeCompoundTerm(name, argsList) {
	var args = [].concat(argsList),
		me;
	me = {
		isCompoundTerm: function() { return true; },
		isVariable: function() { return false; },
		isSymbol: function() { return false; },
		arity: function() { return args.length; },
		getName: function() { return name; },
		getTerm: function(index) { return args[index]; },
		toString: function() {
			return termToString(this);
		}
	};
	return me;
}
function makeVariable(variable, ruleApplicationId) {
	var id = ruleApplicationId ? ruleApplicationId : null,
		me;
	me = {
		isCompoundTerm: function() { return false; },
		isVariable: function() { return true; },
		isSymbol: function() { return false; },
		getName: function() { return variable; },
		getId: function() { return id; },
		toString: function() {
			var result = "?" + variable;
			if(id) {
				result += "#" + id;
			}
			return result;
		}
	};
	return me;
}
function makeSymbol(val) {
	var me;
	me = {
		isCompoundTerm: function() { return false; },
		isVariable: function() { return false; },
		isSymbol: function() { return true; },
		getValue: function() { return val; },
		toString: function() { return val; }
	};
	return me;
}
function makeRule(conclusion, body) {
	var me;
	me = {
		getConclusion: function() { return conclusion; },
		getBody: function() { return body; }
	};
	return me;
}
function isEqual(exp1, exp2) {
	var i;
	if(typeof exp1 !== "object" && typeof exp2 !== "object") {
		return exp1 === exp2;
	} else if(exp1 === null && exp2 === null) {
		return true;
	} else if(typeof exp1 !== "object" || typeof exp2 !== "object") {
		return false;
	} else if(exp1 === null || exp2 === null) {
		return false;
	} else if(exp1.isSymbol() && exp2.isSymbol()) {
		return exp1.getValue() === exp2.getValue();
	} else if(exp1.isVariable() && exp2.isVariable()) {
		return exp1.getName() === exp2.getName() && exp1.getId() === exp2.getId();
	} else if(exp1.isCompoundTerm() && exp2.isCompoundTerm() && exp1.getName() === exp2.getName() && exp1.arity() === exp2.arity()) {
		for(i = 0; i < exp1.arity(); i++) {
			if(!isEqual(exp1.getTerm(i), exp2.getTerm(i))) {
				return false;
			}
		}
		return true;
	} else {
		return false;
	}
}
function termToString(term) {
	var result,
		i;
	if(typeof term !== "object") {
		return term.toString();
	} else if(term === null) {
		return "null";
	} else if(term.isSymbol()) {
		return term.getValue().toString();
	} else if(term.isVariable()) {
		result = term.getName();
		if(term.getId()) {
			result += "#" + term.getId();
		}
		return result;
	} else if(term.isCompoundTerm()) {
		result = term.getName();
		for(i = 0; i < term.arity(); i++) {
			result += i > 0 ? ", " : "(";
			result += termToString(term.getTerm(i));
		}
		return result + ")";
	} else {
		return term + "";
	}
}

module.exports = {
	makeProlog,
	makeRule,
	makeCompoundTerm,
	makeVariable,
	makeSymbol,
	frameToObject
};
