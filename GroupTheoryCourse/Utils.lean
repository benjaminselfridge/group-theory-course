import Lean.Parser.Command

macro "definition" : tactic => `(tactic| rfl)

class One (α : Type u) where
  one : α

instance (priority := 300) One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1
instance (priority := 200) One.ofOfNat1 {α} [OfNat α (nat_lit 1)] : One α where
  one := 1

class Inv (α : Type u) where
  /-- Invert an element of α, denoted by `a⁻¹`. -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv.inv

section
open Lean

-- higher priority to override the one in Batteries
/-- `lemma` means the same as `theorem`. It is used to denote "less important" theorems -/
syntax (name := lemma) (priority := default + 1) declModifiers
  group("lemma " declId ppIndent(declSig) declVal) : command

/-- Implementation of the `lemma` command, by macro expansion to `theorem`. -/
@[macro «lemma»] def expandLemma : Macro := fun stx =>
  -- Not using a macro match, to be more resilient against changes to `lemma`.
  -- This implementation ensures that any future changes to `theorem` are reflected in `lemma`
  let stx := stx.modifyArg 1 fun stx =>
    let stx := stx.modifyArg 0 (mkAtomFrom · "theorem" (canonical := true))
    stx.setKind ``Parser.Command.theorem
  pure <| stx.setKind ``Parser.Command.declaration
end

notation "ℕ" => Nat
notation "ℤ" => Int
