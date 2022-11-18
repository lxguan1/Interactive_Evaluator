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

class AstNode {
    constructor(val, left, right) {
        this.val = val;
        this.index = astIndex;

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
    
    addNode(operandStack, top) {
        let left = operandStack.pop();
        let right = operandStack.pop();

        operandStack.push(new AstNode(top, left, right));
        //Need return?
        return operandStack;
    }

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
                            this.addNode(operandStack, top);
                        }
                    }
                    throw new Error('Unbalanced Left and Right Parentheses');
                default:
                    if (operators.includes(char)) {
                        while (operatorStack.length != 0) {
                            let op2 = operatorStack[operatorStack.length - 1];
                            if (prec[char] <= prec[op2]) {
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
    
    //Issue: currently evaluates the subtrees
    //Desired behavior: closest successor/closest predecessor
    //Bug: sometimes evaluates incorrectly
    recursive_eval(node) {
        switch (node.val) {
            case "+":
                return this.recursive_eval(node.left) + this.recursive_eval(node.right);
            case "-":
                return this.recursive_eval(node.left) - this.recursive_eval(node.right);
            case "*":
                return this.recursive_eval(node.left) * this.recursive_eval(node.right);
            case "/":
                return this.recursive_eval(node.left) / this.recursive_eval(node.right);
            default:
                return parseInt(node.val);
        }
    }

    handle_eval(index) {
        //binary search
        let clicked_node = this.binary_search(this.ast, index);

        //Issue: currently deletes an extra line if an operater on a line that has a currDomLayer > 0 is pressed.
        if (!operators.includes(clicked_node.val)) {
            console.log("Can't click on numbers");
            return;
        }
        let new_val = this.recursive_eval(clicked_node);
        
        let new_ast = structuredClone(this.ast);
        let new_ast_node = this.binary_search(new_ast, index);
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

    let next_ast = new Ast("", new_ast);
    asts.push(next_ast);
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