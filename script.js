// Special classes to handle +,-,*,=?
// Connection to Coq, 
// Div for each supported element, render them somehow?
// Use AST to get the necessary div elements <-
// Tokenize the input, wrapping each token in a span. Then have an onclick



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

var astIndex = 0; //Incremented infinitely
var currDomLayer = 0;

var asts = [];
var coq_proof = [];
var operators = ["+", "-", "*", "/"];

$(document).ready(function () {
    $('#enter').click(process_input);
});

// class Node {
//     constructor(val, precedence, parent) {
//         this.val = val;
//         this.precedence = precedence;
//         this.parent = parent;
//         this.children = [];
//         this.index = astIndex;

//         astIndex++;
//     }
// }

// class AST {
//     constructor(input_str, ast = null) {
//         this.input_str = input_str;
//         this.ast = ast;
//     }

//     parse_input() {
//         let token_list = [];
//         let input_split = this.input_str.split(/(\D)/);
//         for (var i = 0; i < this.input_split.length; i++) {
//             if (input_split[i] == "") {
//                 continue;
//             }
//             else if (input_split[i] == "-") {
//                 token_list.append("+");
//                 token_list.append("-" + input_split[i + 1]);
//                 i++;
//             }
//             else {
//                 token_list.append(input_split[i]);
//             }
//         }
//         return token_list;
//     }

//     initialize_ast() {
//         let processed_input = parse_input();

//         let head_node = new Node(null, 0, null);
//         let curr_node = head_node;
//         for (var i = 0; i < processed_input.length; i++) {
//             switch(processed_input[i]) {
//                 case "(":
//                     let paren_node = new Node(null, 4, head_node);
//                     head_node.children.append(paren_node);
//                     curr_node = paren_node;
//                     break;
//                 case ")":
//                     curr_node = curr_node.parent;
//                 default:

//             }
//         }
//     }
// }

class AstNode {
    constructor(val, left, right, parent = null) {
        this.val = val;
        this.index = astIndex;
        this.parent = parent;
        this.paren_level = 0;

        //Global astIndex count
        //Might change to some local counter later
        astIndex++;
        this.left = left;
        this.right = right;
    }

    setRight(node) {
        this.right = node;
    }

    setLeft(node) {
        this.left = node;
    }
}

// AST:
// val
// list of children
class Ast {
    constructor(input_str, ast = null) {
        this.input_str = input_str;
        this.ast = ast;
    }
    
    handle_negatives(token_arr) {
        let out_arr = [];
        let operator_set = new Set(['+', '-', '*', '/', '(']);

        for (var i = 0; i < token_arr.length; i++) {
            //start of equation
            
            if (i == 1 
                && operator_set.has(token_arr[i - 1] == '-' 
                && !operator_set.has(token_arr[i]))) {
                    out_arr.push('-' + token_arr[i]);
                    i++;
            }
            //In the equation
            else if (i > 1
                && operator_set.has(token_arr[i - 2])
                && operator_set.has(token_arr[i - 1] == '-' 
                && !operator_set.has(token_arr[i]))) {
                    out_arr.push('-' + token_arr[i]);
                    i++;
            }
            else {
                out_arr.push(token_arr[i]);
            }
        }
        return out_arr
    }
    
    addNode(operandStack, top, incr_paren_level = false) {
        let left = operandStack.pop();
        let right = operandStack.pop();
        left.parent = top;
        right.parent = top;
        let new_node = new AstNode(top, left, right);
        if (incr_paren_level) {
            new_node.paren_level++;
        }
        operandStack.push(new_node);
        //Need return?
        return operandStack;
    }
    //Have all elements be some new datatype
    //Store parenthesized objects together (another array?)
    //Check the precedence of surrounding elements when clicking
    // {elt:, parent:, children:, precedence:}
    //Adapted from the Java implementation of the Shunting-Yard Algorithm:
    //https://www.klittlepage.com/2013/12/22/twelve-days-2013-shunting-yard-algorithm/
    initialize_ast() {
        let split_input = this.input_str.split(/(\D)/);
        let processed_input = this.handle_negatives(split_input);

        //Make AST with Shunting-yard algorithm
        
        let operatorStack = [];
        let operandStack = [];

        outer: for (var i = 0; i < processed_input.length; i++) {
            let char = processed_input[i];
            //console.log(char);
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
                    throw new Error('Unbalanced Left and Right Parentheses');
                default:
                    if (operators.includes(char)) {
                        while (operatorStack.length != 0) {
                            let op2 = operatorStack[operatorStack.length - 1];
                            if (prec[char] >= prec[op2]) {
                                operatorStack.pop();
                                operandStack = this.addNode(operandStack, op2);
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
        //console.log(operandStack);
        //console.log(this.ast);
    }

    inorder_helper(node) {
        if (node != null) {
            //TODO: add parentheses
            //Have to do right first for some reason
            this.inorder_helper(node.right);
            let dom_el = "<div class='equation' onclick='handle_eval(\"" + currDomLayer.toString() + "\", \"" 
            + node.index.toString() + "\")' id='" + currDomLayer.toString() 
            + "index" + node.index.toString() + "' style='display:inline'>" + node.val + "</div>";
            $('#output' + currDomLayer.toString()).append(dom_el);
            console.log('hello');
            this.inorder_helper(node.left);
        }
    }
    
    to_html() {
        if (this.ast == null) {
            throw new Error('Initialize the AST');
        }
        $("#outputs").append("<div id='output" + currDomLayer.toString() + "'></div>");

        //Issue: how to access them later when clicked on?
        //Assign an index to each astNode, binary search in evaluation
        this.inorder_helper(this.ast);

    }

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

    //Need to handle left.right.right
    // closest_predecessor(node) {
    //     if (node.left.right != null) {
    //         //Compare precedence
    //         let currnode = node.left;
    //         while (currnode.right.right != null) {
    //             currnode = currnode.right;
    //         }
    //         if (this.compare_prec(currnode, node)) {
    //             return null;
    //         }
    //         return parseInt(currnode.right.val);
    //     }
    //     return parseInt(node.left.val);
    // }

    // closest_successor(node) {
    //     if (node.right.left != null) {
    //         //Compare precedence
    //         let currnode = node.right;
    //         while (currnode.left.left != null) {
    //             currnode = currnode.left;
    //         }
    //         if (this.compare_prec(currnode, node)) {
    //             return null;
    //         }
    //         return parseInt(currnode.left.val);
    //     }
    //     return parseInt(node.right.val);
    // }

    get_unique_vars(node, currList) {
        if (!currList.includes(node.val) && !operators.includes(node.val) && isNaN(parseInt(node.val))) {
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

    to_coq(index) {
        //Import libraries
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
            console.log(prev_expression[i]);
            if (parseInt(prev_expression[i].index) == this.index) {
                console.log(prev_expression[i]);
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

    //Issue: currently evaluates the subtrees
    //Desired behavior: closest successor/closest predecessor
    //Bug: sometimes evaluates incorrectly
    recursive_eval(node) {
        let expression = this.get_expr(this.ast, [], true);
        //(expression);
        for (var i = 0; i < expression.length; i++) {
            if (expression[i].index == node.index) {
                //Compare Left
                //console.log(expression[i - 1].val);
                if (i > 2 && this.compare_prec(expression[i - 2], node) || isNaN(parseInt(expression[i - 1].val))) {
                    //Don't evaluate when one of the terms on either side of the operator
                    //Is part of a subterm that has higher precedence
                    console.log("left");
                    return null;
                }
                let leftVal = parseInt(expression[i - 1].val);

                //Compare Right
                if (i < expression.length - 3 
                    && this.compare_prec(expression[i + 2], node) || isNaN(parseInt(expression[i + 1].val))) {
                    console.log("right");
                    //Don't evaluate when one of the terms on either side of the operator
                    //Is part of a subterm that has higher precedence
                    return null;
                }
                let rightVal = parseInt(expression[i + 1].val);
                let expression_vals = this.get_expr(this.ast, []);
                let ret_arr = expression_vals.slice(0,i - 1);
                console.log(expression[i]);
                this.index = i - 1;
                //Switch
                //let result = 0;
                switch (node.val) {
                    case "+":
                        this.assoc = "rewrite -> Nat.add_assoc. ";
                        this.cut = leftVal + "+" + rightVal;
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
                
                
                //console.log(this.result);
                


            }
        }
    }

    handle_eval(index) {
        //binary search
        let clicked_node = this.binary_search(this.ast, index);

        //Issue: currently deletes an extra line if an operater on a line that has a currDomLayer > 0 is pressed.
        if (!operators.includes(clicked_node.val)) {
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

    //Write to file, execute on command line
    var blob = new Blob([file_header],
        { type: "text/plain;charset=utf-8" });
    let coq_file = document.createElement('a');
    coq_file.href= URL.createObjectURL(blob);
    coq_file.download = "static.txt";
    coq_file.click();

    URL.revokeObjectURL(coq_file.href);
}

function handle_eval(currDom, index) {
    
    astIndex = 0;

    //Remove all elements after the currDom val
    for (var i = parseInt(currDom); i < asts.length - 1; i++) {
        $("#outputs").children().last().remove();
        asts.pop();
        coq_proof.pop();
    }
    currDomLayer = parseInt(currDom) + 1;
    new_ast = asts[asts.length - 1].handle_eval(parseInt(index));
    if (new_ast == null) {
        currDomLayer--;
        return;
    }


    //let next_ast = new Ast("", new_ast);
    
    asts.push(new_ast);
    asts[asts.length - 2].to_coq(index);
    //console.log(asts[asts.length - 1]);
    new_ast.to_html();
}



function process_input() {
    document.getElementById('outputs').replaceChildren();
    asts = [];
    coq_proof = [];
    currDomLayer = 0;
    astIndex = 0;
    let input_str = $('#input').val();

    let new_ast = new Ast(input_str);
    new_ast.initialize_ast();
    new_ast.to_html();
    asts.push(new_ast);


}