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
            console.log(char);
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
        console.log(operandStack);
        console.log(this.ast);
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
    closest_predecessor(node) {
        if (node.left.right != null) {
            //Compare precedence
            let currnode = node.left;
            while (currnode.right.right != null) {
                currnode = currnode.right;
            }
            if (this.compare_prec(currnode, node)) {
                return null;
            }
            return parseInt(currnode.right.val);
        }
        return parseInt(node.left.val);
    }

    closest_successor(node) {
        if (node.right.left != null) {
            //Compare precedence
            let currnode = node.right;
            while (currnode.left.left != null) {
                currnode = currnode.left;
            }
            if (this.compare_prec(currnode, node)) {
                return null;
            }
            return parseInt(currnode.left.val);
        }
        return parseInt(node.right.val);
    }

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
            currList = this.get_expr(node.right, currList);
        }
        if (nodelist) {
            currList.push(node);
        }
        else {
            currList.push(node.val);
        }
        if (node.left != null) {
            currList = this.get_expr(node.left, currList);
        }
        return currList;
    }

    to_coq(index) {
        //Import libraries
        let file_header = "Require Import Reals.\n" + this.coq_import + "\nTheorem equiv_exp:";

        //Get variables in the expressions
        let unique_var = this.get_unique_vars(this.ast, []);
        if (unique_var.length != 0) {
            file_header += "forall ";
        }
        for (var i = 0; i < unique_var.length; i++) {
            file_header += unique_var[i] + ", ";
        }

        //Get the index of the rewrite
        let prev_expression = asts[currDomLayer - 1].get_expr(asts[currDomLayer - 1].ast, [], true);
        let expr_idx = 1;
        for (var i = 0; i < prev_expression.length; i++) {
            if (parseInt(prev_expression[i].index) == index) {
                expr_idx += 1;
                break;
            }
            else if (parseInt(prev_expression[i].val) >= this.result) {
                expr_idx += 1;
            }
        }

        //Write the Proof
        file_header += this.get_expr(this.ast, []).join('') + ' = ' + asts[asts.length - 1].get_expr(asts[asts.length - 1].ast, []).join('') + ".\n";
        file_header += "Proof.\n intros.\n";
        file_header += "cut (" + this.cut  + "=" + this.result + ").\n";
        file_header += "- intros. rewrite <- H at " + expr_idx + ". reflexivity.\n";
        file_header += "- intros. cbv. reflexivity.\n";
        file_header += "Qed.";
        //Write to file, execute on command line
        var blob = new Blob([file_header],
                { type: "text/plain;charset=utf-8" });
        let coq_file = document.createElement('a');
        coq_file.href= URL.createObjectURL(blob);
        coq_file.download = "static.txt";
        coq_file.click();

        URL.revokeObjectURL(coq_file.href);

    }

    //Issue: currently evaluates the subtrees
    //Desired behavior: closest successor/closest predecessor
    //Bug: sometimes evaluates incorrectly
    recursive_eval(node) {
        let leftval = this.closest_predecessor(node);
        let rightval = this.closest_successor(node);
        if ((node.parent != null && this.compare_prec(node.parent, node)) || leftval == null || rightval == null) {
            return null;
        }
        switch (node.val) {
            case "+":
                this.coq_import = "Require Export Plus.";
                this.cut = leftval + "+" + rightval;
                return leftval + rightval;
            case "-":
                this.coq_import = "Require Export Minus.";
                this.cut = leftval + "-" + rightval;
                return leftval - rightval;
            case "*":
                this.coq_import = "Require Export Mult.";
                this.cut = leftval + "*" + rightval;
                return leftval * rightval;
            case "/":
                this.coq_import = "Require Export Div.";
                this.cut = leftval + "/" + rightval;
                return leftval / rightval;
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
        console.log(new_val);
        if (new_val == null) {
            console.log("Can't evaluate");
            return null;
        }

        this.result = new_val;
        
        let new_ast = structuredClone(this.ast);
        let new_ast_node = this.binary_search(new_ast, index);
        //Need to redo this part
        //remove node, remove two values, set leftnode of the closest successor to be the original leftnode, set the rightnode
        //of the closest predecessor to be the new value
        // let leftval = this.closest_predecessor(clicked_node);
        // let rightval = this.closest_successor(clicked_node);
        // let parentNode = null;
        // if (parentNode.left == clicked_node) {
            
        // }
        // else {

        // }
        new_ast_node.val = new_val;
        new_ast_node.left = null;
        new_ast_node.right = null;
        
       return new_ast;

    }

    
}

function handle_eval(currDom, index) {
    


    //Remove all elements after the currDom val
    for (var i = parseInt(currDom); i < asts.length - 1; i++) {
        $("#outputs").children().last().remove();
        asts.pop();
    }
    currDomLayer = parseInt(currDom) + 1;
    new_ast = asts[asts.length - 1].handle_eval(parseInt(index));
    if (new_ast == null) {
        currDomLayer--;
        return;
    }


    let next_ast = new Ast("", new_ast);
    
    asts.push(next_ast);
    asts[asts.length - 2].to_coq(index);
    console.log(asts[asts.length - 1]);
    next_ast.to_html();
}



function process_input() {
    document.getElementById('outputs').replaceChildren();
    asts = [];
    currDomLayer = 0;
    astIndex = 0;
    let input_str = $('#input').val();

    let new_ast = new Ast(input_str);
    new_ast.initialize_ast();
    new_ast.to_html();
    asts.push(new_ast);


}