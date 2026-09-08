/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.StandardComodule
public import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.CoordinateRotation

/-!
# Irreducibility of the special orthogonal standard comodule

Over a field in which `2` is invertible, the standard representation of `SOₙ` is irreducible in
dimension at least three. Coordinate half-turns isolate a chosen coordinate of a vector in an
invariant subspace, and coordinate rotations then carry that standard basis vector to every other
one. Thus every nonzero subcomodule is the whole standard representation.

The dimension bound is sharp for this argument and for the statement: over an algebraically
closed field, the standard representation of `SO₂` is the sum of two one-dimensional characters.
That representation is completely reducible but not irreducible.

## Main declarations

* `TauCeti.SpecialOrthogonal.isSimpleOrder_subcomodule_of_three_le`: the subcomodules of the
  standard representation form a simple order in dimension at least three.
* `TauCeti.SpecialOrthogonal.isCompletelyReducible_standardComodule_of_three_le`: the standard
  representation is completely reducible in those dimensions.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§2.3 and 4.a.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.

The proof uses the point-action interface of
`TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.StandardComodule`.
-/

public section

open Module
open Matrix.SpecialOrthogonalGroup
open scoped Matrix

namespace TauCeti.SpecialOrthogonal

universe u

noncomputable section

variable (k : Type u) [Field k] (n : ℕ) [Invertible (2 : k)]

attribute [local instance] standardComodule

/-- Three distinguished coordinates in `Fin n`, available when `3 ≤ n`. -/
private def firstThree (hn : 3 ≤ n) : Fin 3 ↪ Fin n := Fin.castLEEmb hn

/-- The first three distinguished coordinates are pairwise distinct. -/
private theorem firstThree_ne (hn : 3 ≤ n) {a b : Fin 3} (hab : a ≠ b) :
    firstThree n hn a ≠ firstThree n hn b :=
  (firstThree n hn).injective.ne hab

omit [Invertible (2 : k)] in
/-- In an invariant subspace, three coordinate half-turns isolate four times one coordinate of
a vector. -/
private theorem four_smul_single_mem
    (N : Subcomodule k (coordinateHopfAlgebra k n) (Fin n → k))
    {w : Fin n → k} (hw : w ∈ N) (hn : 3 ≤ n) :
    (4 * w (firstThree n hn 0)) • Pi.single (firstThree n hn 0) 1 ∈ N := by
  let i := firstThree n hn 0
  let j := firstThree n hn 1
  let l := firstThree n hn 2
  change (4 * w i) • Pi.single i 1 ∈ N
  have hij : i ≠ j := firstThree_ne n hn (by decide)
  have hil : i ≠ l := firstThree_ne n hn (by decide)
  have hjl : j ≠ l := firstThree_ne n hn (by decide)
  let gij := coordinateHalfTurn (R := k) i j hij
  let gil := coordinateHalfTurn (R := k) i l hil
  let gjl := coordinateHalfTurn (R := k) j l hjl
  have hijw : (gij : Matrix (Fin n) (Fin n) k) *ᵥ w ∈ N := mulVec_mem k n N gij hw
  have hilw : (gil : Matrix (Fin n) (Fin n) k) *ᵥ w ∈ N := mulVec_mem k n N gil hw
  have hjlw : (gjl : Matrix (Fin n) (Fin n) k) *ᵥ w ∈ N := mulVec_mem k n N gjl hw
  have hcomb :
      (w - (gij : Matrix (Fin n) (Fin n) k) *ᵥ w) +
          (w - (gil : Matrix (Fin n) (Fin n) k) *ᵥ w) -
        (w - (gjl : Matrix (Fin n) (Fin n) k) *ᵥ w) ∈ N :=
    N.toSubmodule.sub_mem
      (N.toSubmodule.add_mem (N.toSubmodule.sub_mem hw hijw) (N.toSubmodule.sub_mem hw hilw))
      (N.toSubmodule.sub_mem hw hjlw)
  convert hcomb using 1
  ext a
  simp only [gij, gil, gjl, Pi.sub_apply, Pi.add_apply, coordinateHalfTurn_mulVec,
    Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hai : a = i
  · subst a
    simp_all
    ring
  · by_cases haj : a = j
    · subst a
      simp_all
    · by_cases hal : a = l
      · subst a
        simp_all
      · simp_all

/-- Every standard basis vector belongs to a nonzero invariant subspace of the standard
special orthogonal representation in dimension at least three. -/
private theorem single_one_mem_of_ne_bot
    (N : Subcomodule k (coordinateHopfAlgebra k n) (Fin n → k)) (hN : N ≠ ⊥)
    (hn : 3 ≤ n) (a : Fin n) : Pi.single a 1 ∈ N := by
  let i := firstThree n hn 0
  obtain ⟨w, hw, hw0⟩ := N.ne_bot_iff.mp hN
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hw0
  simp only [Pi.zero_apply] at hp
  obtain ⟨v, hv, hvi⟩ : ∃ v : Fin n → k, v ∈ N ∧ v i ≠ 0 := by
    by_cases hpi : p = i
    · exact ⟨w, hw, by simpa [hpi] using hp⟩
    · let g := coordinateRotation (R := k) p i hpi
      refine ⟨(g : Matrix (Fin n) (Fin n) k) *ᵥ w, mulVec_mem k n N g hw, ?_⟩
      rw [coordinateRotation_mulVec]
      simpa [Ne.symm hpi] using hp
  have hmultiple := four_smul_single_mem k n N hv hn
  change ((4 : k) * v i) • Pi.single i 1 ∈ N at hmultiple
  have htwo : (2 : k) ≠ 0 := IsUnit.ne_zero (isUnit_of_invertible (2 : k))
  have hfour : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have hc : (4 : k) * v i ≠ 0 := mul_ne_zero hfour hvi
  have hi : Pi.single i 1 ∈ N := by
    have hscaled := N.toSubmodule.smul_mem ((4 : k) * v i)⁻¹ hmultiple
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at hscaled
    exact hscaled
  by_cases hai : i = a
  · simpa [hai] using hi
  · let g := coordinateRotation (R := k) i a hai
    have hrotated := mulVec_mem k n N g hi
    rw [coordinateRotation_mulVec_single_left] at hrotated
    exact hrotated

/-- **The standard comodule of `SOₙ` is simple in dimension at least three** over a field in
which `2` is invertible. -/
theorem isSimpleOrder_subcomodule_of_three_le (hn : 3 ≤ n) :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k n) (Fin n → k)) := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have hone : (Pi.single (firstThree n hn 0) (1 : k) : Fin n → k) ∈
        (⊥ : Subcomodule k (coordinateHopfAlgebra k n) (Fin n → k)) :=
      h ▸ Subcomodule.mem_top _
    rw [Subcomodule.mem_bot] at hone
    simpa using congrFun hone (firstThree n hn 0)
  · intro N
    by_cases hN : N = ⊥
    · exact Or.inl hN
    · right
      apply top_unique
      intro v _
      rw [pi_eq_sum_univ' v]
      exact N.toSubmodule.sum_mem fun a _ ↦
        N.toSubmodule.smul_mem (v a) (single_one_mem_of_ne_bot k n N hN hn a)

/-- **The standard comodule of `SOₙ` is completely reducible in dimension at least three** over
a field in which `2` is invertible. -/
theorem isCompletelyReducible_standardComodule_of_three_le (hn : 3 ≤ n) :
    Comodule.IsCompletelyReducible k (coordinateHopfAlgebra k n) (Fin n → k) := by
  let _ : IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra k n) (Fin n → k)) :=
    isSimpleOrder_subcomodule_of_three_le k n hn
  exact Comodule.isCompletelyReducible_of_isSimpleOrder

end

end TauCeti.SpecialOrthogonal
