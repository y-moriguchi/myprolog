/**
 * myprolog
 *
 * Copyright (c) 2018 Yuichiro MORIGUCHI
 *
 * This software is released under the MIT License.
 * http://opensource.org/licenses/mit-license.php
 **/
var Prolog = require("./myprolog.js"),
	readlineSync = require("readline-sync"),
	prolog = Prolog.makeProlog(),
	lineInput,
	nowPrompt,
	input,
	cont;

function fail() {
	console.log("false.");
}

function success(frame, fail) {
	var boundVariables = Prolog.getAllBoundVariablesToString(frame),
		variableArray = [],
		i,
		count,
		comma,
		action;
	for(i in boundVariables) {
		if(boundVariables.hasOwnProperty(i)) {
			variableArray.push(i + " = " + boundVariables[i]);
		}
	}
	for(i = 0; i < variableArray.length; i++) {
		comma = i < variableArray.length - 1 ? ",\n" : "";
		process.stdout.write(variableArray[i] + comma);
	}
	action = readlineSync.keyIn();
	if(action === ";") {
		fail();
	}
}

while(true) {
	input = "";
	nowPrompt = "> ";
	while(true) {
		lineInput = readlineSync.prompt({ prompt: nowPrompt }).replace(/^\s+|\s+$/g, '');
		if(lineInput.substr(-1) === ".") {
			input += lineInput.substring(0, lineInput.length - 1);
			break;
		} else {
			input += lineInput + " ";
			nowPrompt = ">>";
		}
	}
	if(input === "halt") {
		break;
	}
	cont = prolog.execute(input, fail);
	if(cont) {
		cont(success, fail);
	}
}
