/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.Unravelling

/-!
# Regression examples: unravelling a graph

These examples check the colouring of `List ℚ` by a code of the language of graphs:

* the vertices of the node `[1/2, 1]` are `(1, 0)`;
* the root has the same colour for every code, and on simple graphs every node of length one has
  the same colour, so colours begin to distinguish simple graphs at length two;
* outside the simple graphs, the length-one node `[1]` already separates the constant-true code
  (a loop) from the empty graph, and by the unravelling lemma the two codes are not isomorphic;
* the colour records ordered bits: for the code whose only true atom is `adjAtom 0 1`, the nodes
  `[1/2, 1]` and `[1, 1/2]` have different colours.
-/

public section

open TauCeti TauCeti.RelationalConfiguration

open _root_.FirstOrder (Language)

namespace UnravellingChecks

private theorem ratColor_half : ratColor 2⁻¹ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : (2⁻¹ : ℚ).den = 2 ^ 1 := by simp
  rw [ratColor_def, h, Nat.multiplicity_prime_pow]

private theorem ratColor_one : ratColor 1 = 0 := by
  simp [ratColor_def]

/-! ### Vertices of a node -/

example : unravelVertex [1 / 2, 1] 0 = 1 := by
  simp [unravelVertex_def, ratColor_half]

example : unravelVertex [1 / 2, 1] 1 = 0 := by
  simp [unravelVertex_def, ratColor_one]

/-! ### The root and the nodes of length one -/

-- The root has the same colour for every code.
example (c d : RelationalConfiguration Language.graph ℕ) :
    unravelColor c [] = unravelColor d [] :=
  unravelColor_eq_iff.2 ⟨rfl, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

-- On simple graphs every node of length one has the same colour.
example {c d : RelationalConfiguration Language.graph ℕ} (hc : IsSimpleGraph c)
    (hd : IsSimpleGraph d) (r s : ℚ) : unravelColor c [r] = unravelColor d [s] := by
  refine unravelColor_eq_iff.2 ⟨rfl, fun i hi j hj ↦ ?_⟩
  obtain rfl : i = 0 := by simpa using hi
  obtain rfl : j = 0 := by simpa using hj
  ext <;> simp [isSimpleGraph_iff.1 hc |>.2, isSimpleGraph_iff.1 hd |>.2]

/-! ### A loop is seen at length one -/

/-- The constant-true code: every pair of vertices is related, including each vertex to itself. -/
noncomputable def full : RelationalConfiguration Language.graph ℕ := mk fun _ ↦ true

/-- The empty graph. -/
noncomputable def empty : RelationalConfiguration Language.graph ℕ := mk fun _ ↦ false

-- The colour of `[1]` for the constant-true code occurs at no node for the empty graph.
private theorem unravelColor_empty_ne (y : List ℚ) :
    unravelColor empty y ≠ unravelColor full [1] := by
  intro h
  obtain ⟨hl, hb⟩ := unravelColor_eq_iff.1 h
  simp only [List.length_singleton] at hl
  have := congrArg Prod.snd (hb 0 (by omega) 0 (by omega))
  simp [empty, full] at this

-- So the two codes are not isomorphic.
example : ¬ isoSetoid Language.graph ℕ full empty := by
  rintro h
  obtain ⟨Φ, hΦ⟩ := isoSetoid_iff_exists_orderIso_unravelColor.1 h
  exact unravelColor_empty_ne (Φ [1]) (congrFun hΦ [1])

/-! ### The colour records ordered bits -/

/-- The code whose only true atom is `adjAtom 0 1`. -/
noncomputable def edge01 : RelationalConfiguration Language.graph ℕ :=
  adjArrayEquiv.symm fun p ↦ decide (p = (0, 1))

example : unravelColor edge01 [1 / 2, 1] ≠ unravelColor edge01 [1, 1 / 2] := by
  intro h
  have := congrArg Prod.snd ((unravelColor_eq_iff.1 h).2 1 (by simp) 0 (by simp))
  simp [unravelVertex_def, edge01, ratColor_half, ratColor_one] at this

end UnravellingChecks
