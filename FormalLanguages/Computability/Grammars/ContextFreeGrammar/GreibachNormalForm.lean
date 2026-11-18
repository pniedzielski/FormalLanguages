/-
Copyright (c) 2026 Patrick M. Niedzielski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick M. Niedzielski
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar

public import FormalLanguages.Computability.Grammars.ContextFreeGrammar.IsEpsilonFree

/-!
# Greibach Normal Form

This file contains the definition of Greibach Normal Form, a normal form for context-free grammars
in which every production produces a terminal followed by zero or more nonterminals.

## Main definitions
* `IsGreibachNormalForm`: Whether a context-free grammar is in Greibach Normal Form.
-/

@[expose] public section

namespace ContextFreeGrammar

/-- A context-free grammar is in Greibach Normal Form if every production produces a terminal
    followed by zero or more nonterminals. -/
def IsGreibachNormalForm {T : Type*} (g : ContextFreeGrammar T) : Prop :=
    ∀ p ∈ g.rules,
      ∃ (t : T) (ns : List g.NT), p.output = Symbol.terminal t :: ns.map Symbol.nonterminal

/-- A grammar in Greibach Normal Form is ε-free. -/
lemma IsGreibachNormalForm.epsilon_free {T : Type*} (g : ContextFreeGrammar T)
    (hg : g.IsGreibachNormalForm) :
    g.IsEpsilonFree := by
  intro r hr
  have ⟨_, _, hout⟩ := hg r hr
  simp [hout]

/-- A grammar in Greibach Normal Form cannot derive the empty string. -/
theorem IsGreibachNormalForm.nil_notMem_language {T : Type*} (g : ContextFreeGrammar T)
    (hg : g.IsGreibachNormalForm) :
    [] ∉ g.language := by
  have := hg.epsilon_free g
  exact this.nil_notMem_language g

end ContextFreeGrammar
