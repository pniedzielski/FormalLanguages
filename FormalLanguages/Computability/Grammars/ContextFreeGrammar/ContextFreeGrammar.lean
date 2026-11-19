/-
Copyright (c) 2026 Patrick M. Niedzielski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick M. Niedzielski
-/
module

public import Mathlib.Data.Fintype.Sets
public import Mathlib.Computability.Language
public import Mathlib.Computability.ContextFreeGrammar
public import Mathlib.Computability.DFA

/-!
# Context-Free Grammars

This file contains auxiliary proofs about Context-Free Grammars that are missing from mathlib and
cslib.
-/

@[expose] public section

namespace Language

theorem IsContextFree.if_regular {T : Type*} {L : Language T} (hl : L.IsRegular) :
    L.IsContextFree := by
  obtain ⟨σ, hσ_fin, M, hM⟩ := hl
  let terminal_rules := { r : ContextFreeRule T σ | ∃ s ∈ (M.accept).toFinSet, r = ⟨s, []⟩ }
  have hterminal_rules_fin : Finset terminal_rules := by
    
  let g : ContextFreeGrammar T := ⟨σ, M.start, ⟩
  use g

end Language
