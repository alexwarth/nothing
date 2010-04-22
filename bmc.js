ometa BMLParser <: Parser {
  ach  = ~('(' | ')' | space) char,
  atom = spaces <ach+>:x            -> ["atom", x],
  num  = spaces <digit+>:x          -> ["num",  x],
  expr = num
       | atom
       | "(" expr*:xs ")"           -> ["expr", xs]
}

ometa BMLCompiler {
  compile = comp -> this.makeOutput(),
  comp    = ['num' anything:n]                               -> this.output.push("PUSH(" + n + ")")
          | ['atom' anything:n]                              -> this.output.push("ARG(" + this.symtab()[n] + ")")
          | ['expr' [['atom' 'unless'] comp
                       {this.output.length}:jnzIdx
                       {this.output.push(null)}
                       comp
                       {this.output.push("RET")}
                       {this.output[jnzIdx] = "JNZ(" + (this.output.length - jnzIdx - 1) + ")"}
                       comp]]
          | ['expr' [['atom' '+']      comp comp]]           -> this.output.push("ADD")
          | ['expr' [['atom' '-']      comp comp]]           -> this.output.push("SUB")
          | ['expr' [['atom' '*']      comp comp]]           -> this.output.push("MUL")
          | ['expr' [['atom' 'lambda'] lambdaArgsAndBody]]
          | ['expr' [comp boxArg (&anything comp boxArg)*:args]] -> this.output.push("CALL(" + args.length + ")")
          | {throw "compilation failed"},
  boxArg  = {this.output.push("BOX")},

  lambdaArgsAndBody = {this.output}:oldOutput
                        {this.output = ["nil"]; this.symtabs.push({_numVars: 0}); this.addArg("thisFunction")}
                        ['expr' [(['atom' :a] -> this.addArg(a))*]]
                        comp
                        {this.output.push("RET");
                         this.symtabs.pop();
                         this.lambdas.push(this.output);
                         this.output = oldOutput;
                         this.output.push("mk2(Int(IPUSH), l" + this.lambdas.length + ")")}
}
BMLCompiler.initialize = function() {
  this.symtabs = []
  this.output = []
  this.lambdas = []
}
BMLCompiler.symtab = function() { return this.symtabs[this.symtabs.length - 1] }
BMLCompiler.addArg = function(a) {
  this.symtab()[a] = this.symtab()._numVars++
}
BMLCompiler.iMakeOutput = function(name, instrs, ws) {
    ws.nextPutAll("value_t " + name + " = mk(" + instrs.length + ");\n")
    ws.nextPutAll("addGlobal(" + name + ");\n");
    for (var i = 0; i < instrs.length; i++)
      ws.nextPutAll("slotAtPut(" + name + ", Int(" + i + "), " + instrs[i] + ");\n")
}
BMLCompiler.makeOutput = function() {
  var ws = new StringBuffer()
  for (var i = 0; i < this.lambdas.length; i++)
    this.iMakeOutput("l" + (i + 1), this.lambdas[i], ws)
  this.output.push("HALT")
  this.iMakeOutput("prog", this.output, ws)
  return ws.contents()
}

tree = BMLParser.matchAll("((lambda (n) (unless n 1 (* n (thisFunction (- n 1))))) 5)", "expr")
//tree = BMLParser.matchAll("((lambda (x) (+ x 1)) 5)", "expr")
code = BMLCompiler.match(tree, "compile") 
