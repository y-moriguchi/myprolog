/**
 * myprolog
 *
 * Copyright (c) 2018 Yuichiro MORIGUCHI
 *
 * This software is released under the MIT License.
 * http://opensource.org/licenses/mit-license.php
 **/
var R = require("rena-js").clone(),
	K = require("kalimotxo"),
	anonymousVariableId = 1;
R.ignore(/[ \t\n]+/);

function makeProlog() {
	var allRules = makeList(),
		currentRuleId = 1,
		parser,
		parserTerm,
		operator;
	function addOperator(name, command, precedence) {
		function binary(x, y) {
			return makeCompoundTerm(name, [x, y]);
		}
		function unary(x) {
			return makeCompoundTerm(name, [x]);
		}
		operator["add" + command](name, 1200 - precedence, command.startsWith("Infix") ? binary : unary);
	}
	function makeOperatorMatcher(follow) {
		return function(str, index) {
			return operator.parse(str, index, follow);
		};
	}
	function concatTerm(inherit, op) {
		return {
			name: inherit.name,
			args: inherit.args.concat([op])
		};
	}
	parser = R.or(
		R.t(/[a-z][a-zA-Z0-9_]*/, function(name) { return makeSymbol(name); }),
		R.t("!", function(name) { return makeSymbol("!"); }),
		R.t(/[0-9]+/, function(num) { return makeNumber(parseInt(num)); }),
		R.t(/[A-Z_][a-zA-Z0-9_]*/, function(name) { return name === "_" ? makeAnonymousVariable() : makeVariable(name); }),
		R.t(/[\+\-\*\/<>=:\.&_~\^\\@]+/, function(name) { return makeSymbol(name); }),
		R.t(/\'[^\']+\'/, function(name) { return makeSymbol(name.substring(1, name.length - 1)); }),
		R.t("[")
			.attr([])
			.or(R.t("]", function() { return makeSymbol("[]"); }),
				R.t(R.delimit(makeOperatorMatcher(/[,\|\]]/),
					",",
					function(x, result, list) { return list.concat([result]); }))
				.or(R.t("|")
					.t(makeOperatorMatcher(/[\]]/), function(_, result, list) { return list.concat([result]); })
					.t("]")
					.action(function(list) { return arrayToPrologList(list.slice(0, list.length - 1), list[list.length - 1]); }),
					R.t("]").action(arrayToPrologList))));
	parserTerm = R.t(/[a-z][a-zA-Z0-9_]*|[\+\-\*\/<>=:\.&_~\^\\@]+/, function(name) { return { name: name, args: [] }; })
		.t("(")
		.t(R.delimit(makeOperatorMatcher(/[,\)]/),
			",",
			function(x, op, inherit) { return concatTerm(inherit, op); }))
		.t(")")
		.action(function(x) { return makeCompoundTerm(x.name, x.args); });
	operator = K.Operator({
		id: function(str, index) {
			return parser.parse(str, index);
		},
		preId: function(str, index) {
			return parserTerm.parse(str, index);
		},
		actionId: function(x) { return x; }
	});
	addOperator(":-", "InfixNonAssoc", 1200);
	addOperator(":-", "PrefixNonAssoc", 1200);
	addOperator(";", "InfixRToL", 1100);
	addOperator(",", "InfixRToL", 1000);
	addOperator("=", "InfixNonAssoc", 700);
	addOperator("is", "InfixNonAssoc", 700);
	addOperator("<", "InfixNonAssoc", 700);
	addOperator(">", "InfixNonAssoc", 700);
	addOperator("<=", "InfixNonAssoc", 700);
	addOperator(">=", "InfixNonAssoc", 700);
	addOperator("=:=", "InfixNonAssoc", 700);
	addOperator("=\\=", "InfixNonAssoc", 700);
	addOperator("+", "InfixLToR", 500);
	addOperator("-", "InfixLToR", 500);
	addOperator("*", "InfixLToR", 400);
	addOperator("/", "InfixLToR", 400);
	function parseQuery(program) {
		var query = /\?- */g,
			match;
		if(query.exec(program)) {
			return operator.parse(program, query.lastIndex).attribute;
		} else {
			return null;
		}
	}
	function execute(program, fail) {
		var resultQuery,
			resultRule;
		if(!!(resultQuery = parseQuery(program))) {
			return executeQuery(resultQuery, fail);
		} else {
			resultRule = operator.parse(program, 0).attribute;
			if(resultRule.isCompoundTerm() && resultRule.arity() === 2 && resultRule.getName() === ":-") {
				addRule(resultRule.getTerm(0), resultRule.getTerm(1));
			} else if(resultRule.isCompoundTerm() && resultRule.arity() === 1 && resultRule.getName() === ":-") {
				executeQuery(resultRule.getTerm(0), function() {})(function() {}, function() {});
			} else {
				addRule(resultRule, null);
			}
			return null;
		}
	}

	function executeQuery(query, cutFailFunction, aFrame) {
		var frame = aFrame ? aFrame : makeEmptyFrame(),
			relationalOps,
			relationalFunc;
		relationalOps = {
			"<": makeRelationalFunc(function(x, y) { return x < y; }),
			">": makeRelationalFunc(function(x, y) { return x > y; }),
			"<=": makeRelationalFunc(function(x, y) { return x <= y; }),
			">=": makeRelationalFunc(function(x, y) { return x >= y; }),
			"=:=": makeRelationalFunc(function(x, y) { return x === y; }),
			"=\\=": makeRelationalFunc(function(x, y) { return x !== y; })
		};
		function makeRelationalFunc(func) {
			function getValue(term) {
				var value = term.isVariable() ? getBoundValueRecursively(term, frame) : term;
				if(!value.isNumber()) {
					throw new Error(term + " must be bound to a number");
				}
				return value.getValue();
			}
			return function(term1, term2) {
				var val1 = getValue(term1),
					val2 = getValue(term2);
				return func(val1, val2);
			}
		}
		function simplySuccess(success, fail) {
			return success(frame, fail);
		}
		function cutFunction() {
			return cutFailFunction();
		}
		function conjoin(query, frame) {
			return function(success, fail) {
				function successFunction(frame, fail) {
					return executeQuery(query.getTerm(1), cutFailFunction, frame)(success, fail);
				}
				return executeQuery(query.getTerm(0), cutFailFunction, frame)(successFunction, fail);
			};
		}
		function disjoin(query, frame) {
			return function(success, fail) {
				function failFunction() {
					return fail === cutFunction ? fail() : executeQuery(query.getTerm(1), cutFailFunction, frame);
				}
				return executeQuery(query.getTerm(0), cutFailFunction, frame)(success, failFunction);
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
					return unified ? executeQuery(ruleNew.getBody(), cutFailFunction, unified)(success, failFunction) : failFunction();
				};
			}
			return searchRule(applied);
		}
		if(!query) {
			return simplySuccess;
		} else if(query.isSymbol() && query.getValue() === "!") {
			return function(success, fail) {
				return success(frame, cutFunction);
			};
		} else if(query.isCompoundTerm() && query.arity() === 2 && query.getName() === ",") {
			return conjoin(query, frame);
		} else if(query.isCompoundTerm() && query.arity() === 2 && query.getName() === ";") {
			return disjoin(query, frame);
		} else if(query.isCompoundTerm() && query.arity() === 2 && query.getName() === "=") {
			return function(success, fail) {
				var frameNew = unify(query.getTerm(0), query.getTerm(1), frame);
				return frameNew ? success(frameNew, fail) : fail();
			}
		} else if(query.isCompoundTerm() && query.arity() === 2 && query.getName() === "is") {
			return function(success, fail) {
				return success(compute(query.getTerm(0), query.getTerm(1), frame), fail);
			}
		} else if(query.isCompoundTerm() && query.arity() === 3 && query.getName() === "op") {
			addOperatorByOp(query.getTerm(0), query.getTerm(1), query.getTerm(2));
			return simplySuccess;
		} else if(query.isCompoundTerm() && query.arity() === 2 && !!(relationalFunc = relationalOps[query.getName()])) {
			return function(success, fail) {
				return relationalFunc(query.getTerm(0), query.getTerm(1)) ? success(frame, fail) : fail();
			}
		} else {
			return simpleQuery(query, frame);
		}
	}
	function addOperatorByOp(priority, specifier, name) {
		var priorityNumber,
			command;
		if(!priority.isNumber()) {
			throw new Error("priority must be a number");
		} else if((priorityNumber = priority.getValue()) < 0 || priorityNumber > 1200) {
			throw new Error("priority must be between 0 and 1200");
		}
		if(!specifier.isSymbol()) {
			throw new Error("specifier must be a symbol");
		}
		switch(specifier.getValue()) {
			case "xfx":  command = "InfixNonAssoc";  break;
			case "yfx":  command = "InfixLToR";  break;
			case "xfy":  command = "InfixRToL";  break;
			case "fx":   command = "PrefixNonAssoc";  break;
			case "fy":   command = "Prefix";  break;
			case "xf":   command = "PostfixNonAssoc";  break;
			case "yf":   command = "Postfix";  break;
			default:
				throw new Error("invalid specifier: " + specifier.getName());
		}
		if(!name.isSymbol()) {
			throw new Error("operator must be a symbol");
		}
		addOperator(name.getValue(), command, priorityNumber);
	}
	function renameRuleVariable(rule) {
		var ruleId = currentRuleId++;
		function retrieve(term) {
			var elements,
				i;
			if(!term) {
				return term;
			} else if(term.isVariable()) {
				return term.isAnonymous() ? makeAnonymousVariable() : makeVariable(term.getName(), ruleId);
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
			return unify(binding, val, frame);
		} else if(val.isVariable()) {
			binding = getBoundValue(val, frame);
			return binding ? unify(variable, binding, frame) : bindValue(variable, val, frame);
		} else if(isDependent(val, variable, frame)) {
			return null;
		} else {
			return bindValue(variable, val, frame);
		}
	}
	function compute(left, right, frame) {
		var variableToBound,
			tableBinary,
			tableUnary;
		tableBinary = {
			"+": function(x, y) { return x + y; },
			"-": function(x, y) { return x - y; },
			"*": function(x, y) { return x * y; },
			"/": function(x, y) { return x / y; }
		};
		tableUnary = {
			"-": function(x) { return -x; }
		};
		function walk(term) {
			var val1,
				val2,
				func;
			if(term.isCompoundTerm()) {
				if(term.arity() === 2) {
					val1 = walk(term.getTerm(0));
					val2 = walk(term.getTerm(1));
					func = tableBinary[term.getName()];
					if(!func) {
						throw new Error(term.getName() + "/2 is not computable");
					}
					return func(val1, val2);
				} else if(term.arity() === 1) {
					val1 = walk(term.getTerm(0));
					func = tableUnary(term.getName());
					if(!func) {
						throw new Error(term.getName() + "/1 is not computable");
					}
					return func(val1, val2);
				} else {
					throw new Error(term.getName() + "/" + term.getArity() + " is not computable");
				}
			} else if(term.isNumber()) {
				return term.getValue();
			} else if(term.isVariable()) {
				val1 = getBoundValueRecursively(term, frame);
				if(val1 === null) {
					throw new Error(term.getName() + " must be bound variable");
				} else if(!val1.isNumber()) {
					throw new Error(term.getName() + " must be bound to a number");
				}
				return val1.getValue();
			} else {
				throw new Error(term.toString() + " is not computable");
			}
		}
		if(!left.isVariable() && (variableToBound = getBoundValueRecursively(left, frame)) !== null) {
			throw new Error("left value of `is` must be free variable");
		}
		return bindValue(left, makeNumber(walk(right)), frame);
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
function getBoundValueRecursively(variable, frame) {
	var value,
		valueNew;
	function walk(term) {
		var compounds,
			compound,
			i;
		if(term.isCompoundTerm()) {
			compounds = [];
			for(i = 0; i < term.arity(); i++) {
				compound = walk(term.getTerm(i));
				if(!compound) {
					return null;
				}
				compounds.push(compound);
			}
			return makeCompoundTerm(term.getName(), compounds);
		} else if(term.isVariable()) {
			return getBoundValue(term, frame);
		} else {
			return term;
		}
	}
	if(!variable.isVariable()) {
		return null;
	}
	value = getBoundValue(variable, frame);
	for(; value !== null; value = valueNew) {
		valueNew = walk(value);
		if(isEqual(value, valueNew)) {
			return value;
		}
	}
	return null;
}
function bindValue(variable, value, frame) {
	return {
		key: function() { return variable.toString(); },
		keyVariable: function() { return variable; },
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
		isNumber: function() { return false; },
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
		isNumber: function() { return false; },
		getName: function() { return variable; },
		getId: function() { return id; },
		isAnonymous: function() { return false; },
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
function makeAnonymousVariable() {
	var variableId = anonymousVariableId++,
		me;
	me = {
		isCompoundTerm: function() { return false; },
		isVariable: function() { return true; },
		isSymbol: function() { return false; },
		isNumber: function() { return false; },
		getName: function() { return "#" + variableId; },
		getId: function() { return -1; },
		isAnonymous: function() { return true; },
		toString: function() {
			var result = "?##" + variableId;
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
		isNumber: function() { return false; },
		getValue: function() { return val; },
		toString: function() { return val; }
	};
	return me;
}
function makeNumber(val) {
	var me;
	if(typeof val !== "number") {
		throw new Error(val + " must be a number");
	}
	me = {
		isCompoundTerm: function() { return false; },
		isVariable: function() { return false; },
		isSymbol: function() { return false; },
		isNumber: function() { return true; },
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
	} else if(exp1.isNumber() && exp2.isNumber()) {
		return exp1.getValue() === exp2.getValue();
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
		array,
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
	} else if(term.isNumber()) {
		return term.getValue().toString();
	} else if(isPrologList(term)) {
		array = prologListToArray(term);
		result = "";
		for(i = 0; i < array[0].length; i++) {
			result += i > 0 ? ", " : "[";
			result += termToString(array[0][i]);
		}
		if(!isPrologNil(array[1])) {
			result += " | " + termToString(array[1]);
		}
		return result + "]";
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

function arrayToPrologList(array, dot) {
	var i,
		result = dot ? dot : makeSymbol("[]");
	for(i = array.length - 1; i >= 0; i--) {
		result = makeCompoundTerm(".", [array[i], result]);
	}
	return result;
}
function isPrologList(list) {
	return list.isCompoundTerm() && list.getName() === "." && list.arity() === 2;
}
function isPrologNil(list) {
	return list.isSymbol() && list.getValue() === "[]";
}
function prologListToArray(list) {
	var listPtr = list,
		result = [];
	for(; isPrologList(listPtr); listPtr = listPtr.getTerm(1)) {
		result.push(listPtr.getTerm(0));
	}
	return [result, listPtr];
}

function getAllBoundVariablesMap(frame, func) {
	var nowFrame = frame,
		result = {},
		variable;
	for(; !nowFrame.isNull(); nowFrame = nowFrame.rest()) {
		variable = nowFrame.keyVariable();
		if(!variable.getId()) {
			result[variable.getName()] = func(getBoundValueRecursively(variable, frame));
		}
	}
	return result;
}
function getAllBoundVariables(frame) {
	return getAllBoundVariablesMap(frame, function(x) { return x; });
}
function getAllBoundVariablesToString(frame) {
	return getAllBoundVariablesMap(frame, function(x) { return x.toString(); });
}

module.exports = {
	makeProlog,
	makeRule,
	makeCompoundTerm,
	makeVariable,
	makeSymbol,
	frameToObject,
	getAllBoundVariablesMap,
	getAllBoundVariables,
	getAllBoundVariablesToString
};
