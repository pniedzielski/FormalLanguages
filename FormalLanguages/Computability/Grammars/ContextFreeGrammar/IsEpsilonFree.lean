/-
Copyright (c) 2026 Patrick M. Niedzielski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick M. Niedzielski
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar

/-!
# ε-Freeness

This file contains the definition of ε-Freeness, a property of context-free grammars in which no
rule produces the empty string ε.

## Main definitions
* `IsEpsilonFree`: Whether a grammar contains no rules that can produce the empty string.

## Main proofs
* `IsEpsilonFree.nil_notMem_language`: An ε-free grammar cannot generate the empty string.
-/

@[expose] public section

namespace ContextFreeRule

/-- A rule that does not produce the empty string never shortens the sentential form. -/
lemma Rewrites.length_le {T N : Type*} {r : ContextFreeRule T N} {u v : List (Symbol T N)}
    (hr : r.output ≠ []) (hrw : r.Rewrites u v) :
    u.length ≤ v.length := by
  obtain ⟨pref, suff, rfl, rfl⟩ := hrw.exists_parts
  have := List.length_pos_iff.mpr hr
  simp only [List.length_append, List.length_singleton]
  omega

end ContextFreeRule

namespace ContextFreeGrammar

/-- A context-free grammar ε-free if no production rewrites to the empty string. -/
def IsEpsilonFree {T : Type*} (g : ContextFreeGrammar T) : Prop :=
  ∀ r ∈ g.rules, r.output ≠ []

/-- Derivations in an ε-free grammar never shorten the sentential form. -/
lemma IsEpsilonFree.length_le_of_derives {T : Type*} (g : ContextFreeGrammar T)
    (hg : g.IsEpsilonFree) {u v : List (Symbol T g.NT)} (hd : g.Derives u v) :
    u.length ≤ v.length := by
  induction hd with
  | refl => rfl
  | tail _ hp ih =>
    obtain ⟨r, hr, hrw⟩ := hp
    apply hg at hr
    exact ih.trans (hrw.length_le hr)

/-- An ε-free grammar cannot generate the empty string. -/
theorem IsEpsilonFree.nil_notMem_language {T : Type*} (g : ContextFreeGrammar T)
    (hg : g.IsEpsilonFree) : [] ∉ g.language := by
  intro hempty
  have hd : g.Derives [Symbol.nonterminal g.initial] [] := by
    simpa using (g.mem_language_iff []).mp hempty
  have := hg.length_le_of_derives g hd
  simp at this

end ContextFreeGrammar
