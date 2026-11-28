/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.Symplectic.Transvection
import TauCeti.Algebra.Lie.Basic
import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Simplicity of the symplectic Lie algebra

For a nondegenerate alternating form on a nonzero finite-dimensional space over a field of
characteristic different from two, the Lie algebra of skew-adjoint endomorphisms is simple.
The matrix form gives simplicity of `LieAlgebra.Symplectic.sp` on a nonempty finite index type.

Write `N(u)` for the endomorphism `x ↦ B x u • u`. If a Lie ideal contains a nonzero `X`,
the symmetric form `(x,y) ↦ B (X x) y` has a nonzero diagonal value. The double bracket
`⁅N(u), ⁅N(u), X⁆⁆` then puts a nonzero scalar multiple of `N(u)` in the ideal. A vector
pairing nontrivially with each of two given nonzero vectors propagates membership from one
rank-one operator to the other. The rank-one spanning theorem from
`TauCeti.Algebra.Lie.Symplectic.Transvection` gives the full ideal.

## References

* J. S. Milne, *Lie Algebras, Algebraic Groups, and Lie Groups*, Example (Cₙ), pp. 94–95.
* P. Deligne, *La conjecture de Weil. I*, Lemme 5.11, for the rank-one spanning argument.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

attribute [local instance 100] LieRing.ofAssociativeRing

section CommRing

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

private abbrev rankOne (hB : B.IsAlt) (u : V) : skewAdjointLieSubalgebra B :=
  ⟨(B.flip u).smulRight u, smulRight_flip_mem_skewAdjointSubmodule hB u⟩

end CommRing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

private theorem rankOne_mem_of_pairing_ne_zero [NeZero (2 : K)] (hB : B.IsAlt)
    (I : LieIdeal K (skewAdjointLieSubalgebra B)) {X : skewAdjointLieSubalgebra B}
    (hX : X ∈ I) {u : V} (hu : B (X.val u) u ≠ 0) : rankOne hB u ∈ I := by
  have hm := I.lie_mem (x := rankOne hB u) (I.lie_mem (x := rankOne hB u) hX)
  have heq : ⁅rankOne hB u, ⁅rankOne hB u, X⁆⁆ = (-(2 : K) * B (X.val u) u) • rankOne hB u :=
    Subtype.ext (lie_smulRight_flip_lie_smulRight_flip hB u X.val)
  rw [heq] at hm
  exact (I.toSubmodule.smul_mem_iff (mul_ne_zero (neg_ne_zero.mpr (NeZero.ne _)) hu)).mp hm

private theorem exists_pairing_ne_zero [NeZero (2 : K)] (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {X : skewAdjointLieSubalgebra B} (hX : X ≠ 0) :
    ∃ u, B (X.val u) u ≠ 0 := by
  let : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne _)
  have hsk := (LinearMap.mem_skewAdjointSubmodule (B := B) X.val).mp X.property
  apply exists_bilinForm_self_ne_zero (B := B.compLeft X.val)
  · intro h
    apply hX
    apply Subtype.ext
    ext x
    exact hnd.1 _ fun y ↦ by
      simpa only [compLeft_apply, LinearMap.zero_apply] using
        congrArg (fun f : BilinForm K V ↦ f x y) h
  · constructor
    intro x y
    change B (X.val x) y = B (X.val y) x
    rw [hsk x y, Pi.neg_apply, map_neg, hB.neg_eq]

/-- Membership of a rank-one operator propagates along every nonzero pairing. -/
private theorem rankOne_mem_of_apply_ne_zero [NeZero (2 : K)] (hB : B.IsAlt)
    (I : LieIdeal K (skewAdjointLieSubalgebra B)) {u v : V} (hu : rankOne hB u ∈ I)
    (huv : B u v ≠ 0) : rankOne hB v ∈ I := by
  apply rankOne_mem_of_pairing_ne_zero hB I hu
  have hvu : B v u ≠ 0 := by rwa [← hB.neg_eq, neg_ne_zero]
  simpa [rankOne, smul_eq_mul] using mul_ne_zero hvu huv

private theorem eq_top_of_rankOne_mem [FiniteDimensional K V] (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (I : LieIdeal K (skewAdjointLieSubalgebra B))
    (hall : ∀ v, rankOne hB v ∈ I) : I = ⊤ := by
  have hspan : B.skewAdjointSubmodule ≤
      I.toSubmodule.map (skewAdjointLieSubalgebra B).toSubmodule.subtype := by
    rw [← span_smulRight_flip_eq_skewAdjointSubmodule hB hnd, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    exact ⟨rankOne hB v, hall v, rfl⟩
  apply top_unique
  intro X _
  obtain ⟨Y, hY, hYX⟩ := hspan X.property
  exact (Subtype.ext hYX : Y = X) ▸ hY

private theorem eq_top_of_skewAdjoint_ideal_ne_bot [NeZero (2 : K)] [FiniteDimensional K V]
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (I : LieIdeal K (skewAdjointLieSubalgebra B))
    (hI : I ≠ ⊥) : I = ⊤ := by
  obtain ⟨X, hX, hX0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (p := I.toSubmodule) (fun he ↦ hI (LieSubmodule.toSubmodule_injective he))
  obtain ⟨u, hu⟩ := exists_pairing_ne_zero hB hnd hX0
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hNu := rankOne_mem_of_pairing_ne_zero hB I hX hu
  apply eq_top_of_rankOne_mem hB hnd I
  intro v
  by_cases hv : v = 0
  · subst v
    have hz : rankOne hB 0 = 0 := Subtype.ext (by simp)
    rw [hz]
    exact I.zero_mem
  obtain ⟨w, huw, hvw⟩ := hnd.exists_apply_ne_zero_and_apply_ne_zero hu0 hv
  exact rankOne_mem_of_apply_ne_zero hB I (rankOne_mem_of_apply_ne_zero hB I hNu huw)
    (by rwa [← hB.neg_eq, neg_ne_zero])

private theorem not_isLieAbelian_skewAdjoint [Nontrivial V] (hB : B.IsAlt)
    (hnd : B.Nondegenerate) : ¬ IsLieAbelian (skewAdjointLieSubalgebra B) := by
  intro hab
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  obtain ⟨v, huv⟩ := hnd.exists_apply_ne_zero hu
  have hvu : B v u ≠ 0 := by rwa [← hB.neg_eq, neg_ne_zero]
  have h := congrArg (fun X : skewAdjointLieSubalgebra B ↦ X.val u)
    (hab.trivial (rankOne hB u) (rankOne hB v))
  change (((B.flip u).smulRight u * (B.flip v).smulRight v -
    (B.flip v).smulRight v * (B.flip u).smulRight u) u) = 0 at h
  simp [hB.self_eq_zero] at h
  exact hu ((h.resolve_left huv).resolve_left hvu)

/-- A nondegenerate alternating form on a nonzero finite-dimensional vector space over a
field of characteristic different from two has simple skew-adjoint Lie algebra. -/
theorem IsAlt.isSimple_skewAdjointLieSubalgebra [NeZero (2 : K)] [FiniteDimensional K V]
    [Nontrivial V] (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    LieAlgebra.IsSimple K (skewAdjointLieSubalgebra B) where
  eq_bot_or_eq_top I := or_iff_not_imp_left.mpr (eq_top_of_skewAdjoint_ideal_ne_bot hB hnd I)
  non_abelian := not_isLieAbelian_skewAdjoint hB hnd

end LinearMap.BilinForm

namespace LieAlgebra.Symplectic

open Matrix

/-- The standard symplectic matrix Lie algebra of any positive rank is simple over fields
whose characteristic is different from two. -/
instance isSimple_sp (l K : Type*) [Fintype l] [DecidableEq l] [Nonempty l] [Field K]
    [NeZero (2 : K)] : LieAlgebra.IsSimple K (sp l K) := by
  let B := (J l K).toBilin'
  have hB : B.IsAlt := (Matrix.isAlt_toBilin'_iff _).mpr
    ⟨J_transpose l K, fun i ↦ by cases i <;> simp [J]⟩
  have hnd : B.Nondegenerate := Matrix.nondegenerate_toBilin'_iff.mpr
    (Matrix.Nondegenerate.of_det_mem_nonZeroDivisors (isUnit_det_J l K).mem_nonZeroDivisors)
  have hs := hB.isSimple_skewAdjointLieSubalgebra hnd
  let e : sp l K ≃ₗ⁅K⁆ skewAdjointLieSubalgebra B :=
    TauCeti.skewAdjointLieEquivOfBasis (Pi.basisFun K _) B (by
      rw [LinearMap.BilinForm.toMatrix_basisFun]
      exact LinearMap.BilinForm.toMatrix'_toBilin' _)
  exact (LieAlgebra.isSimple_iff_of_not_isLieAbelian K _
    (hs.non_abelian ∘ (lie_abelian_iff_equiv_lie_abelian e).mp)).mp
      ((LieIdeal.orderIsoMapComap e).isSimpleOrder_iff.mpr inferInstance)

end LieAlgebra.Symplectic
