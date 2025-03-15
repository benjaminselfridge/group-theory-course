import Lean.Parser.Command

macro "definition" : tactic => `(tactic| rfl)
