module

public meta import Lean

public meta section

/-!
# No-op stand-in for LeanArchitect

The vendored PrimeNumberTheoremAnd sources annotate declarations for their blueprint with
LeanArchitect's `@[blueprint ...]` attribute and `blueprint_comment /-- ... -/` command.
This module accepts the same syntax and ignores it, so the sources build unchanged without
LeanArchitect. The syntax mirrors `Architect/Attribute.lean` and `Architect/Command.lean` of
https://github.com/hanwenzhu/LeanArchitect.
-/

namespace Architect

open Lean Elab Command

syntax blueprintSingleUses := "-"? (ident <|> str)
syntax blueprintUses := "[" blueprintSingleUses,* "]"

syntax blueprintStatementOption := &"statement" " := " plainDocComment
syntax blueprintHasProofOption := &"hasProof" " := " (&"true" <|> &"false")
syntax blueprintProofOption := &"proof" " := " plainDocComment
syntax blueprintUsesOption := &"uses" " := " blueprintUses
syntax blueprintProofUsesOption := &"proofUses" " := " blueprintUses
syntax blueprintTitleOption := &"title" " := " (plainDocComment <|> str)
syntax blueprintNotReadyOption := &"notReady" " := " (&"true" <|> &"false")
syntax blueprintDiscussionOption := &"discussion" " := " num
syntax blueprintLatexEnvOption := &"latexEnv" " := " str
syntax blueprintLatexLabelOption := &"latexLabel" " := " str

syntax blueprintOption := "("
  blueprintStatementOption <|>
  blueprintHasProofOption <|> blueprintProofOption <|>
  blueprintUsesOption <|> blueprintProofUsesOption <|>
  blueprintTitleOption <|>
  blueprintNotReadyOption <|> blueprintDiscussionOption <|>
  blueprintLatexEnvOption <|> blueprintLatexLabelOption ")"
syntax blueprintOptions := (ppSpace str)? (ppSpace blueprintOption)*

/-- Blueprint metadata, accepted and ignored. -/
syntax (name := blueprint) "blueprint" "?"? blueprintOptions : attr

initialize registerBuiltinAttribute {
  name := `blueprint
  descr := "Blueprint metadata (ignored)"
  applicationTime := .afterCompilation
  add := fun _ _ _ => pure ()
}

/-- Blueprint text, accepted and ignored. -/
elab (name := blueprintComment) "blueprint_comment " _stx:plainDocComment : command =>
  pure ()

end Architect
