/-
Copyright (c) 2026 Patrick M. Niedzielski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick M. Niedzielski
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar

/-!
# Greibach Normal Form

This file contains the definition of Greibach Normal Form, a normal form for context-free grammars
in which every production produces a terminal followed by zero or more nonterminals.

## Main definitions
* `is_greibach_normal_form`: Whether a context-free grammar is in Greibach Normal Form.
-/

@[expose] public section

/-- A context-free grammar is in Greibach Normal Form if every production produces a terminal
    followed by zero or more nonterminals. -/
def is_greibach_normal_form {T : Type} (g : ContextFreeGrammar T) : Prop :=
    ∀ p ∈ g.rules,
      ∃ (t : T) (ns : List g.NT), p.output = Symbol.terminal t :: ns.map Symbol.nonterminal

theorem greibach_normal_form_nonempty {T : Type} (g : ContextFreeGrammar T) :
    is_greibach_normal_form g → [] ∉ g.language := by
  rintro hgnf hempty
  have hder : g.Derives [Symbol.nonterminal g.initial] [] := by simpa using hempty
  rcases hder.eq_or_tail with h | ⟨v, ⟨_, ⟨r, ⟨hrule, hrewrites⟩⟩⟩⟩
  · contradiction
  have : r.output = [] := by
    rw [ContextFreeRule.rewrites_iff] at hrewrites
    rcases hrewrites with ⟨p, q, _, h⟩
    have hparts := by simpa using h
    exact hparts.2.1
  obtain ⟨t, ns, houtput⟩ := hgnf r hrule
  rw [this] at houtput
  contradiction
