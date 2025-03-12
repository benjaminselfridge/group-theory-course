import Lean.Parser.Command

macro "definition" : tactic => `(tactic| rfl)
set_option pp.all true
