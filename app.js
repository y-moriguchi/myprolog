/**
 * myprolog
 *
 * Copyright (c) 2018 Yuichiro MORIGUCHI
 *
 * This software is released under the MIT License.
 * http://opensource.org/licenses/mit-license.php
 **/
var Prolog = require("./myprolog.js"),
    fs = require("fs"),
    readlineSync = require("readline-sync"),
    prolog = Prolog.makeProlog(),
    defaultSuccess = createSuccess(function() {
        return readlineSync.keyIn();
    });

function fail() {
    console.log("false.");
}

function createSuccess(keyIn) {
    return function(frame, fail) {
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
        if(variableArray.length > 0) {
            for(i = 0; i < variableArray.length; i++) {
                comma = i < variableArray.length - 1 ? ",\n" : "";
                process.stdout.write(variableArray[i] + comma);
            }
            action = keyIn();
            if(action === ";") {
                fail();
            }
        } else {
            console.log("yes");
        }
    };
}

function readProgram(success, handler) {
    var input,
        nowPrompt,
        lineInput,
        cont;

    while(true) {
        input = "";
        nowPrompt = "> ";
        while(true) {
            lineInput = handler({ prompt: nowPrompt });
            if(!lineInput && lineInput !== "") {
                return;
            }
            lineInput = lineInput.replace(/^\s+|\s+$/g, '');
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
}

function isFile(file) {
    try {
        fs.statSync(file);
        return true;
    } catch(e) {
        return false;
    }
}

function readFile(file) {
    var fileString;

    if(isFile(file)) {
        fileString = fs.readFileSync(file, "utf8");
        return fileString;
    } else {
        console.log("File not found: " + file);
        process.exit(2);
    }
}

function readPrompt(success) {
    readProgram(success, function(option) {
        return readlineSync.prompt(option);
    });
}

function readFromFile(success, file, echo) {
    var program = readFile(file),
        lines = program.split(/\r\n|\n|\r/),
        count = 0;

    readProgram(success, function(option) {
        if(count < lines.length) {
            if(echo && lines[count] !== "") {
                console.log(lines[count]);
            }
            return lines[count++];
        } else {
            return null;
        }
    });
}

function main() {
    var success,
        argvFlag = 3,
        flagString,
        interactive = false,
        echo = true;

    success = defaultSuccess;
    for(; argvFlag < process.argv.length; argvFlag++) {
        flagString = process.argv[argvFlag - 1];
        if(flagString === "-i") {
            interactive = true;
        } else if(flagString === "-f") {
            success = createSuccess(function() {
                console.log(";");
                return ";";
            });
        } else if(flagString === "-s") {
            echo = false;
        } else if(/^-/.test(flagString)) {
            console.log("Invalid flag: " + flagString);
            process.exit(2);
        } else {
            break;
        }
    }
    if(process.argv.length < argvFlag) {
        readPrompt(defaultSuccess);
    } else if(process.argv.length === argvFlag) {
        readFromFile(success, process.argv[argvFlag - 1], echo);
        if(interactive) {
            readPrompt(success);
        }
    }
}

main();

