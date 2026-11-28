/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card.Arithmetic
public import TauCeti.NumberTheory.UnitEquation.Nondegenerate

/-!
# Counting nondegenerate solutions through a finite set of centres

Let `B` be a finite set of tuples and `s` a set of tuples, over a semiring. Every solution `y` of
`∑ aᵢ yᵢ = 1` of the form `y = b w` with `b ∈ B` and `w ∈ s` gives the solution `w` of the
translated equation `∑ aᵢ bᵢ wᵢ = 1`, and it is nondegenerate exactly when `w` is
(`TauCeti.isNondegenerateSolution_mul_iff`). Distinct solutions `y` with the same centre `b` come
from distinct points `w`. So the nondegenerate solutions `y` number at most `|B|` times the
supremum in `ℕ∞`, over `b ∈ B`, of the number of nondegenerate solutions `w ∈ s` of the
translated equation.

This is the counting step behind the small-height regime of the unit equation, where `B` is a
packing of a group of `S`-units and `s` is a sublevel set of a height; see
`TauCeti.NumberTheory.UnitEquation.SmallSolutions.SUnit`.

## Main results

* `TauCeti.encard_isNondegenerateSolution_le_card_mul`: the nondegenerate solutions `y = b w` with
  `b ∈ B` and `w ∈ s` number at most `|B|` times the supremum over `b ∈ B` of the numbers of
  nondegenerate solutions `w ∈ s` of `∑ aᵢ bᵢ wᵢ = 1`.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), Lemma 11.2 and
  Corollary 11.3.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [Semiring R] {ι : Type*} [Fintype ι]

/-- **Counting solutions through centres.** Let `B` be a finite set of tuples and `s` a set of
tuples. The nondegenerate solutions `y` of `∑ aᵢ yᵢ = 1` of the form `y = b w` with `b ∈ B` and
`w ∈ s` number at most `|B|` times the supremum in `ℕ∞`, over `b ∈ B`, of the numbers of
nondegenerate solutions `w ∈ s` of the translated equation `∑ aᵢ bᵢ wᵢ = 1`. For `B = ∅` the
supremum is zero, and so is the left-hand side. -/
theorem encard_isNondegenerateSolution_le_card_mul (a : ι → R) (B : Finset (ι → R))
    (s : Set (ι → R)) :
    {y | IsNondegenerateSolution a y ∧ ∃ b ∈ B, ∃ w ∈ s, y = b * w}.encard ≤
      #B * ⨆ b ∈ B, {w | IsNondegenerateSolution (a * b) w ∧ w ∈ s}.encard := by
  set T : (ι → R) → Set (ι → R) := fun b ↦ {w | IsNondegenerateSolution (a * b) w ∧ w ∈ s}
  -- Each solution `y = b w` is the image of the solution `w` of the translated equation under
  -- multiplication by `b`.
  calc _ ≤ (⋃ b ∈ B, (b * ·) '' T b).encard := by
        refine Set.encard_le_encard fun y ⟨hy, b, hb, w, hw, hyw⟩ ↦ Set.mem_iUnion₂.2
          ⟨b, hb, w, ⟨isNondegenerateSolution_mul_iff.2 (hyw ▸ hy), hw⟩, hyw.symm⟩
    _ ≤ ∑ b ∈ B, ((b * ·) '' T b).encard := B.set_encard_biUnion_le _
    _ ≤ ∑ b ∈ B, (T b).encard := sum_le_sum fun b _ ↦ Set.encard_image_le _ _
    _ ≤ #B • ⨆ b ∈ B, (T b).encard :=
        sum_le_card_nsmul _ _ _ fun b hb ↦ le_iSup₂ (f := fun b (_ : b ∈ B) ↦ (T b).encard) b hb
    _ = _ := nsmul_eq_mul _ _

end TauCeti
