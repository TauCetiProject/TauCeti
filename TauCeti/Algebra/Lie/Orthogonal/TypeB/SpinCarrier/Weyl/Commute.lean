/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.ChevalleyRelations

/-!
# Commuting orthogonal Weyl words in the type-B spin carrier

For orthogonal numbered simple roots, the rank-one words
`xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` and `xⱼ(v) x₋ⱼ(-v⁻¹) xⱼ(v)` commute.
This is the length-two braid relation, with independent unit parameters, over every
commutative coefficient ring. In particular, taking both parameters to be one gives the
relation for the pinned simple Weyl representatives.

The result supplies braid-move coherence for transporting numbered root subgroups in the
full-weight spin carrier. It does not assert braid relations at adjacent nodes or identify
the carrier with an independently pinned simply connected group scheme.

## Main result

* `TauCeti.TypeBSpinCarrier.commute_weylWord_of_cartanMatrix_eq_zero`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.

The proof uses the four signed simple-root commutation equations in
`TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.ChevalleyRelations` and Mathlib's
`Commute.mul_left` and `Commute.mul_right`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

universe u

/-- Weyl words at orthogonal type-`B` nodes commute, for independent unit parameters over any
commutative coefficient ring. The hypothesis is on the numbered Bourbaki Cartan matrix. -/
theorem commute_weylWord_of_cartanMatrix_eq_zero {n : ℕ} {i j : Fin (n + 1)}
    (hij : CartanMatrix.B (n + 1) i j = 0) (A : Type u) [CommRing A] (s t : Aˣ) :
    Commute
      (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (s : A)) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-(↑s⁻¹ : A))) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (s : A)))
      (rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd (t : A)) *
        rootSubgroupPoints n (.inr j) A (Multiplicative.ofAdd (-(↑t⁻¹ : A))) *
        rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd (t : A))) := by
  have hne : i ≠ j := by
    rintro rfl
    have hdiag : (2 : ℤ) = 0 := by simpa only [CartanMatrix.B_diag] using hij
    norm_num at hdiag
  have hpp := commute_rootSubgroupPoints_inl_inl hij A
    (Multiplicative.ofAdd (s : A)) (Multiplicative.ofAdd (t : A))
  have hpn := commute_rootSubgroupPoints_inl_inr hne A
    (Multiplicative.ofAdd (s : A)) (Multiplicative.ofAdd (-(↑t⁻¹ : A)))
  have hnp := commute_rootSubgroupPoints_inr_inl hne A
    (Multiplicative.ofAdd (-(↑s⁻¹ : A))) (Multiplicative.ofAdd (t : A))
  have hnn := commute_rootSubgroupPoints_inr_inr hij A
    (Multiplicative.ofAdd (-(↑s⁻¹ : A))) (Multiplicative.ofAdd (-(↑t⁻¹ : A)))
  have hpos := (hpp.mul_left hnp).mul_left hpp
  have hneg := (hpn.mul_left hnn).mul_left hpn
  exact (hpos.mul_right hneg).mul_right hpos

end TauCeti.TypeBSpinCarrier
