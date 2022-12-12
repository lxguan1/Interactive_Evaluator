/*
*This program is an interactive expression evaluator that generates a proof of
*the evaluation's correctness in Coq.
*Author: Lingxiao Guan
*Last edit: 12/12/2022
*/


//Associativity and precedences of the operations
//Associativity not used as of now
var assoc = {
    "*" : "left",
    "/" : "left",
    "+" : "left",
    "-" : "left"
   };

var prec = {
    "*" : 3,
    "/" : 3,
    "+" : 2,
    "-" : 2
};

//Global variable that represents the most recently generated expression
//e.g.
//1 + 2 + 3
//3 + 3 <- the currDomLayer
var currDomLayer = 0;

//The asts of all of the expression layers
var asts = [];

//The proofs of all of the expression layers
var coq_proof = [];

//Start up the document
$(document).ready(function () {
    $('#enter').click(process_input);
});


//The data structure for each element in an expression
//Contain:
//val (either a number, variable, or operation)
//index (location of the element if the expression is displayed left to right)
//paren_level (how many parentheses deep is the element)
//left the left child
//right the right child
class AstNode {
    constructor(val, left, right) {
        this.val = val;
        this.index = 0;
        this.paren_level = 0;

        this.left = left;
        this.right = right;
    }
}

// AST: data structure that represents one expression
class Ast {
    constructor(input_str, ast = null) {
        this.input_str = input_str;
        this.ast = ast;
        this.operators = ["+", "-", "*", "/"];
    }
    
    //Handle negative values (e.g. -1), turn them into a single integer
    //Needed since otherwise clicking on the '-' will evaluate a subexpression
    handle_negatives(token_arr) {
        let out_arr = [];
        let operator_set = new Set(['+', '-', '*', '/', '(']);

        for (var i = 0; i < token_arr.length; i++) {
            //Negative at start of equation
            if (i == 1 
                && operator_set.has(token_arr[i - 1] == '-' 
                && !operator_set.has(token_arr[i]))) {
                    out_arr.push('-' + token_arr[i]);
                    i++;
            }
            //Negative in the equation
            else if (i > 1
                && operator_set.has(token_arr[i - 2])
                && operator_set.has(token_arr[i - 1] == '-' 
                && !operator_set.has(token_arr[i]))) {
                    out_arr.push('-' + token_arr[i]);
                    i++;
            }
            //Not a negative
            else {
                out_arr.push(token_arr[i]);
            }
        }
        return out_arr
    }
    
    //Create a node, with its val as an operator, and its children being other nodes
    addNode(operandStack, top, incr_paren_level = false) {
        let left = operandStack.pop();
        let right = operandStack.pop();
        let new_node = new AstNode(top, left, right);

        //If the value is inside of a set of parentheses
        if (incr_paren_level) {
            new_node.paren_level++;
        }
        operandStack.push(new_node);
    }
    
    //Make the AST from the input string, using the Shunting-Yard Algorithm
    //This function is Adapted from the Java implementation of the Shunting-Yard Algorithm:
    //https://www.klittlepage.com/2013/12/22/twelve-days-2013-shunting-yard-algorithm/
    initialize_ast() {
        //Split the input string into individual elements
        let split_input = this.input_str.split(/(\D)/);
        let processed_input = this.handle_negatives(split_input);

        //Make AST with Shunting-yard algorithm
        
        let operatorStack = [];
        let operandStack = [];

        outer: for (var i = 0; i < processed_input.length; i++) {
            let char = processed_input[i];
            switch(char) {
                case "":
                    break;
                case '(':
                    operatorStack.push('(');
                    break;
                case ')':
                    while (operatorStack.length != 0) {
                        let top = operatorStack.pop();
                        if (top == "(") {
                            continue outer;
                        }
                        else {
                            this.addNode(operandStack, top, true);
                        }
                    }
                    //Parentheses won't be matched if this is reached
                    //The continue in the while loop would have run
                    throw new Error('Unbalanced Left and Right Parentheses');
                default:
                    if (this.operators.includes(char)) {
                        while (operatorStack.length != 0) {
                            let op2 = operatorStack[operatorStack.length - 1];
                            if (prec[char] >= prec[op2]) {
                                operatorStack.pop();
                                this.addNode(operandStack, op2);
                            }
                            else {
                                break;
                            }
                        }
                        operatorStack.push(char);
                    }
                    else {
                        operandStack.push(new AstNode(char, null, null));
                    }
                    break;
                    
            }
        }

        while(operatorStack.length != 0) {
            this.addNode(operandStack, operatorStack.pop());
        }
        this.ast = operandStack.pop();

        //Set indices
        let expression = this.get_expr(this.ast, [], true);
        for (var i = 0; i < expression.length; i++) {
            expression[i].index = i;
        }
    }

    inorder_helper(node) {
        if (node != null) {
            //TODO: add parentheses
            //Have to do right first
            this.inorder_helper(node.right);
            let dom_el = "<div class='equation' onclick='handle_eval(\"" + currDomLayer.toString() + "\", \"" 
            + node.index.toString() + "\")' id='" + currDomLayer.toString() 
            + "index" + node.index.toString() + "' style='display:inline'>" + node.val + "</div>";
            $('#output' + currDomLayer.toString()).append(dom_el);
            this.inorder_helper(node.left);
        }
    }
    
    //Add the AST's expression to the dom
    to_html() {
        if (this.ast == null) {
            throw new Error('Initialize the AST');
        }

        //Make a div container to hold the expression
        $("#outputs").append("<div id='output" + currDomLayer.toString() + "'></div>");

        this.inorder_helper(this.ast);

    }
    
    //Look for a node based on its index
    //Returns the node if found
    //Returns null if not
    binary_search(node, index) {
        if (node == null) {
            return null;
        }
        if (node.index == index) {
            return node;
        }
        let left = this.binary_search(node.left, index);
        if (left != null) {
            return left;
        }
        let right = this.binary_search(node.right, index);
        return right;
    }

    //Handle parentheses with precedence levels
    compare_prec(node1, node2) {
        let prec1 = prec[node1.val];
        let prec2 = prec[node2.val];
        prec1 += node1.paren_level * 10;
        prec2 += node2.paren_level * 10;
        return prec1 > prec2;
    }


    //Get the unique variables in an expression
    get_unique_vars(node, currList) {
        //The current node value isn't in currList, isn't an operator, and isn't a number
        if (!currList.includes(node.val) && !this.operators.includes(node.val) && isNaN(parseInt(node.val))) {
            currList.push(node.val);
        }
        if (node.left != null) {
            currList = this.get_unique_vars(node.left, currList);
        }
        if (node.right != null) {
            currList = this.get_unique_vars(node.right, currList);
        }
        return currList;
    }

    //Returns a list that contains either the element values of the expression if nodelist = false
    //Or it contains the nodes of each element of the expression.
    get_expr(node, currList, nodelist = false) {
        if (node.right != null) {
            currList = this.get_expr(node.right, currList, nodelist);
        }
        if (nodelist) {
            currList.push(node);
        }
        else {
            currList.push(node.val);
        }
        if (node.left != null) {
            currList = this.get_expr(node.left, currList, nodelist);
        }
        return currList;
    }

    //Creates a Coq proof that proves the step from the previous expression to the current expression
    //is valid. Stores it in the coq_proof array.
    to_coq(asts, coq_proof) {
        //Start the Lemma
        let file_header = "Lemma equiv_exp" + currDomLayer + ":";

        //Get variables in the expressions
        let unique_var = this.get_unique_vars(this.ast, []);
        if (unique_var.length != 0) {
            file_header += "forall ";
        }
        for (var i = 0; i < unique_var.length; i++) {
            file_header += unique_var[i] + ", ";
        }

        //Get the index of the rewrite
        let prev_expression = asts[asts.length - 1].get_expr(asts[asts.length - 1].ast, [], true);
        let expr_idx = 1;
        for (var i = 0; i < prev_expression.length; i++) {
            if (parseInt(prev_expression[i].index) == this.index) {
                break;
            }
            else if (parseInt(prev_expression[i].val) >= this.result) {
                expr_idx += 1;
            }
        }

        //Write the Proof
        file_header += asts[asts.length - 1].get_expr(asts[asts.length - 1].ast, []).join('') + ' = ' + this.get_expr(this.ast, []).join('') + ".\n";
        file_header += "Proof.\n intros.\n";
        file_header += "cut (" + this.cut  + "=" + this.result + ").\n";
        file_header += "- intros. rewrite <- H at " + expr_idx + ". " + this.assoc + " reflexivity.\n";
        file_header += "- intros. cbv. reflexivity.\n";
        file_header += "Qed.\n";

        //Push the lemma to the whole proof
        coq_proof.push(file_header);
        
        

    }

    //Evaluates an operation
    //Gets the list of this expression, then iterates through it until it reaches the index that was clicked.
    //Then does evaluation only if one of numbers on the left or right isn't a part of a higher precedence
    //Operation.
    recursive_eval(node) {
        let expression = this.get_expr(this.ast, [], true);
        for (var i = 0; i < expression.length; i++) {
            if (expression[i].index == node.index) {
                //Compare Left
                if (i > 2 && this.compare_prec(expression[i - 2], node) || isNaN(parseInt(expression[i - 1].val))) {
                    //Don't evaluate when one of the terms on either side of the operator
                    //is part of a subterm that has higher precedence
                    return null;
                }
                let leftVal = expression[i - 1].val;
                //Handle subtraction on left
                if (expression[i - 1].val == "-") {
                    leftVal = parseInt(leftVal) > 0 ? "-" + leftVal : leftVal;
                    expression[i - 1].val = "+";
                }
                leftVal = parseInt(leftVal);
                

                //Compare Right
                if (i < expression.length - 3 
                    && this.compare_prec(expression[i + 2], node) || isNaN(parseInt(expression[i + 1].val))) {
                    //Don't evaluate when one of the terms on either side of the operator
                    //Is part of a subterm that has higher precedence
                    return null;
                }
                let rightVal = parseInt(expression[i + 1].val);
                let expression_vals = this.get_expr(this.ast, []);
                let ret_arr = expression_vals.slice(0,i - 1);

                //The index of the resulting element
                this.index = i - 1;
                //Switch over the possible oeprators
                //Code duplication in the switch statement due to strange Javascript behavior if the retval.push
                //is placed after the switch statement.
                switch (node.val) {
                    case "+":
                        //Handles the parentheses the '+' rewrite adds
                        this.assoc = "rewrite -> Nat.add_assoc. ";
                        //The operation that was done, will be placed in the cut tactic
                        this.cut = leftVal + "+" + rightVal;
                        //Result of the '+' op
                        this.result = leftVal + rightVal;
                        ret_arr.push(this.result);
                        return ret_arr.concat(expression_vals.slice(i + 2)).join('');
                    case "-":
                        this.assoc = "";
                        this.cut = leftVal + "-" + rightVal;
                        this.result = leftVal - rightVal;
                        ret_arr.push(this.result);
                        return ret_arr.concat(expression_vals.slice(i + 2)).join('');
                    case "*":
                        this.assoc = "";
                        this.cut = leftVal + "*" + rightVal;
                        this.result = leftVal * rightVal;
                        ret_arr.push(this.result);
                        return ret_arr.concat(expression_vals.slice(i + 2)).join('');
                    case "/":
                        this.assoc = "";
                        this.cut = leftVal + "/" + rightVal;
                        this.result = leftVal / rightVal;
                        ret_arr.push(this.result);
                        return ret_arr.concat(expression_vals.slice(i + 2)).join('');
                    default:
                        throw Error();
                }
                


            }
        }
    }

    handle_eval(index) {
        //binary search
        let clicked_node = this.binary_search(this.ast, index);

        //Issue: currently deletes an extra line if an operater on a line that has a currDomLayer > 0 is pressed.
        if (!this.operators.includes(clicked_node.val)) {
            console.log("Can't click on numbers");
            return null;
        }
        let new_val = this.recursive_eval(clicked_node);


        //this.result = new_val;

        let new_ast = new Ast(new_val);
        new_ast.initialize_ast();
        
       return new_ast;

    }

    
}

function coq_proof_construction() {
    file_header = "Require Import Nat. \n";
    file_header += "Require Export Plus.\n";
    file_header += "Require Export Mult.\n";

    //Add Lemmas for each step
    coq_proof.slice().reverse().forEach(x => file_header += x);
    file_header += "Theorem equiv_exp:";

    initial = asts[0].get_expr(asts[0].ast, []);
    end = asts[asts.length - 1].get_expr(asts[asts.length - 1].ast, []);

    //If there are variables
    let unique_var = asts[0].get_unique_vars(asts[0].ast, []);
    if (unique_var.length != 0) {
        file_header += "forall ";
    }
    for (var i = 0; i < unique_var.length; i++) {
        file_header += unique_var[i] + ", ";
    }

    //Add expressions
    file_header += end.join('')  + "=" + initial.join('') + ".\n";

    //Rewrite everything using the lemmas, from last to first
    file_header += "Proof.\n intros.\n";
    for (var i = coq_proof.length - 1; i >= 0; i--) {
        file_header += "rewrite -> equiv_exp" + (i + 1) + ".\n";
    }
    //Reflexivity
    file_header += "reflexivity. Qed.";

    //Write to file, execute on command line/copy to interactive Coq interfaces
    var blob = new Blob([file_header],
        { type: "text/plain;charset=utf-8" });
    let coq_file = document.createElement('a');
    coq_file.href= URL.createObjectURL(blob);
    coq_file.download = "static.txt";
    coq_file.click();

    URL.revokeObjectURL(coq_file.href);
}

//Handles evaluation when a user clicks on an element in an expression
function handle_eval(currDom, index) {

    //Remove all elements after the currDom val
    for (var i = asts.length - 1; i > parseInt(currDom); i--) {
        $("#outputs").children().last().remove();
        asts.pop();
        coq_proof.pop();
    }
    currDomLayer = parseInt(currDom) + 1;
    //Evaluate
    new_ast = asts[asts.length - 1].handle_eval(parseInt(index));

    //Terminate if there is a problem with evaluation
    if (new_ast == null) {
        currDomLayer--;
        return;
    }

    
    //Calculate the Coq proof for this evaluation, put the new expression on the dom    
    asts.push(new_ast);
    asts[asts.length - 2].to_coq(asts, coq_proof);
    new_ast.to_html();
}


//Start evaluation of the expression that the user inputted into the input area
function process_input() {
    //Clear previous inputs
    document.getElementById('outputs').replaceChildren();
    asts = [];
    coq_proof = [];
    currDomLayer = 0;

    //Turn the input into an Ast and display it onto the dom
    let input_str = $('#input').val();

    let new_ast = new Ast(input_str);
    new_ast.initialize_ast();
    new_ast.to_html();
    asts.push(new_ast);


}