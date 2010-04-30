ometa BMLParser <: Parser {
  atomChar = ~('(' | ')' | space) char,
  atom     = spaces <atomChar+>:x          -> ["atom", x],
  num      = spaces <digit+>:x             -> ["num",  x],
  expr     = num | atom | "(" expr*:xs ")" -> ["expr", xs],
  parse    = expr:tree spaces end          -> tree
}

ometa BMLCompiler {
  compile          = comp                                               -> this.makeOutput(),
  builtIn          = ['atom' ('if' | '=' | '+' | '-' | '*' | 'lambda')],
  comp             = ['num' anything:n]                                    emit("Push(" + n + ")")
                   | ['atom' anything:n]                                   emit(this.lookup(n)) emit("Unbox")
                   | ['expr' [['atom' 'if']     comp
                              blankInstr:jzIdx  comp                       emitAt(jzIdx,  "JZ("  + (this.ic() - jzIdx)      + ")")
                              blankInstr:jmpIdx comp              ]]       emitAt(jmpIdx, "Jmp(" + (this.ic() - jmpIdx - 1) + ")")
                   | ['expr' [['atom' '='     ] comp comp         ]]       emit("Eq")
                   | ['expr' [['atom' '+'     ] comp comp         ]]       emit("Add")
                   | ['expr' [['atom' '-'     ] comp comp         ]]       emit("Sub")
                   | ['expr' [['atom' '*'     ] comp comp         ]]       emit("Mul")
                   | ['expr' [['atom' 'lambda'] lambda            ]]
                   | ['expr' [~builtIn                                     emit("PrepCall")
                              comp box (&anything comp box)*:args ]]       emit("Call(" + args.length + ")")
                   | { throw "compilation failed" },
  tcComp           = ['expr' [['atom' 'if']     comp
                              blankInstr:jzIdx  tcComp                     emitAt(jzIdx,  "JZ("  + (this.ic() - jzIdx)      + ")")
                              blankInstr:jmpIdx tcComp   ]]                emitAt(jmpIdx, "Jmp(" + (this.ic() - jmpIdx - 1) + ")")
                   | ['expr' [~builtIn
                              comp box (&anything comp box)*:args ]]       emit("TCall(" + args.length + ")")
                   | comp,
  blankInstr       = emit(null)                                         -> (this.level().out.length - 1),
  emit        :ins =                                                    -> this.level().out.push(ins),
  emitAt :idx :ins =                                                    -> (this.level().out[idx] = ins),
  box              =                                                       emit("Box"),
  lambda           = { this.levels.push({fvs: [],
                                         syms: {_numVars: 0},
                                         out: []})
                       this.addArg("thisFunction")
                       this.level()                          }:level
                     ['expr' [(['atom' :a] -> this.addArg(a))*]] tcComp    emit("Ret")
                     { this.levels.pop()
                       this.lambdas.push(level.out) }                      emit("mk2(Int(oPush), l" + this.lambdas.length + ")")
                     { for (var i = 0; i < level.fvs.length; i++)          this._applyWithArgs("emit", this.lookup(level.fvs[i])) }
                                                                           emit("MkFun(" + level.fvs.length + ")")
}
BMLCompiler.initialize  = function()      { this.levels = [{fvs: [], syms: {_numVars: 0}, out: []}]
                                            this.lambdas = [] }
BMLCompiler.level       = function()      { return this.levels[this.levels.length - 1] }
BMLCompiler.ic          = function()      { return this.level().out.length }
BMLCompiler.addArg      = function(a)     { this.level().syms[a] = this.level().syms._numVars++ }
BMLCompiler.lookup      = function(n)     { var li = this.levels.length - 1
                                            while (li > 0) {
                                              var vi = this.levels[li].syms[n]
                                              if (vi != undefined) {
                                                if (this.levels[li] == this.level())
                                                  return "Arg(" + vi + ")"
                                                while (++li < this.levels.length)
                                                  vi = this.addFv(li, n)
                                                return "FV(" + vi + ")"
                                              }
                                              li--
                                            }
                                            throw "undeclared variable " + n }
BMLCompiler.addFv       = function(li, n) { var fvs = this.levels[li].fvs
                                            for (var i = 0; i < fvs.length; i++)
                                              if (fvs[i] == n)
                                                return i
                                            fvs.push(n)
                                            return fvs.length - 1 }
BMLCompiler.iMakeOutput = function(name, instrs, ws) {
                                            ws.nextPutAll("value_t " + name + " = mk(" + instrs.length + ");\n")
                                            ws.nextPutAll("addGlobal(" + name + ");\n");
                                            for (var i = 0; i < instrs.length; i++)
                                              ws.nextPutAll("slotAtPut(" + name + ", Int(" + i + "), " + instrs[i] + ");\n") }
BMLCompiler.makeOutput  = function()      { var ws = new StringBuffer()
                                            for (var i = 0; i < this.lambdas.length; i++)
                                              this.iMakeOutput("l" + (i + 1), this.lambdas[i], ws)
                                            this.level().out.push("Halt")
                                            this.iMakeOutput("prog", this.level().out, ws)
                                            return ws.contents() }

//tree = BMLParser.matchAll("((lambda (x) (+ x 1)) 5)", "parse")
//tree = BMLParser.matchAll("((lambda (x y) (- x y)) 5 6)", "parse")
//tree = BMLParser.matchAll("(((lambda (x) (lambda () x)) 5))", "parse")
//tree = BMLParser.matchAll("(((lambda (x) (lambda (y) (- x y))) 5) 6)", "parse")
//tree = BMLParser.matchAll("((((lambda (x) (lambda (y) (lambda () (+ x y)))) 5) 6))", "parse")
//tree = BMLParser.matchAll("(((lambda (x y) (lambda () (+ x (+ y x)))) 5 6))", "parse")
//tree = BMLParser.matchAll("(((lambda (x y) (lambda () (+ x y))) 5 6))", "parse")
//tree = BMLParser.matchAll("(((((lambda (x) (lambda (y) (lambda (z) (lambda () (+ x (+ y z)))))) 1) 2) 3))", "parse")
//tree = BMLParser.matchAll("((lambda (n) (if (= n 0) 1 (* n (thisFunction (- n 1))))) 5)", "parse")
tree = BMLParser.matchAll("((lambda (n acc) (if (= n 0) acc (thisFunction (- n 1) (* acc n)))) 5 1)", "parse")

code = BMLCompiler.match(tree, "compile")

