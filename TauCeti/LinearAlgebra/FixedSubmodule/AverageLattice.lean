/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Permutation
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Index

/-!
# The lattice of orbit averages

Averaging rational coordinates along the cycles of a finite permutation projects onto its
fixed space. The image of the integral coordinate lattice is generally larger than the integral
fixed lattice: on a cycle of length `n`, its constant coordinate may be any element of `n⁻¹ ℤ`.
We characterize this image and compute the index of the integral fixed lattice in it as the
product of the cycle lengths. In particular, averaging is not an integral retraction.

This is the lattice comparison between projected simple roots and distinct-orbit sums in diagram
folding. It does not identify either lattice with a character or cocharacter lattice.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.

The fixed-coordinate parametrization is `Equiv.Perm.permutationFixedEquiv`.
-/

public noncomputable section

open Finset

namespace Equiv.Perm

variable {I : Type*} [Fintype I] (σ : Equiv.Perm I)

private abbrev Cycles := Quotient (SameCycle.setoid σ)

open Classical in
private def cycleSize (c : Cycles σ) : ℕ :=
  Fintype.card {i : I // Quotient.mk (SameCycle.setoid σ) i = c}

private theorem cycleSize_pos (c : Cycles σ) : 0 < cycleSize σ c := by
  classical
  have : Nonempty {i : I // Quotient.mk (SameCycle.setoid σ) i = c} :=
    ⟨⟨c.out, Quotient.out_eq c⟩⟩
  exact Fintype.card_pos_iff.mpr this

private def averageCoordinates : (Cycles σ → ℚ) ≃ₗ[ℚ] (Cycles σ → ℚ) :=
  LinearEquiv.piCongrRight fun c ↦ LinearEquiv.smulOfNeZero ℚ ℚ
    (cycleSize σ c : ℚ)⁻¹ (inv_ne_zero (Nat.cast_ne_zero.mpr (cycleSize_pos σ c).ne'))

private theorem averageCoordinates_apply (a : Cycles σ → ℚ) (c : Cycles σ) :
    averageCoordinates σ a c = a c / cycleSize σ c := by
  simp [averageCoordinates, div_eq_mul_inv, mul_comm]

open Classical in
/-- Average each coordinate over its permutation cycle. This is a rational linear projection,
not the section-dependent integral retraction `permutationFixedProjection`. -/
def permutationAverage : (I → ℚ) →ₗ[ℚ]
    (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule :=
  (permutationFixedEquiv (R := ℚ) σ).toLinearMap.comp
    ((averageCoordinates σ).toLinearMap.comp
      (LinearMap.pi fun c ↦ ∑ i : {i : I // Quotient.mk (SameCycle.setoid σ) i = c},
        LinearMap.proj i.val))

open Classical in
/-- Every output coordinate is the mean over its cycle. -/
@[simp]
theorem permutationAverage_apply (v : I → ℚ) (i : I) :
    (permutationAverage σ v).val i =
      (∑ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i}, v j.val) /
        Fintype.card {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i} := by
  simp [permutationAverage, averageCoordinates_apply, cycleSize]

/-- Averaging fixes every rational fixed vector. -/
@[simp]
theorem permutationAverage_fixed
    (v : (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule) :
    permutationAverage σ v.val = v := by
  classical
  apply Subtype.ext
  funext i
  rw [permutationAverage_apply]
  have hv (j : {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i}) :
      v.val j.val = v.val i := by
    rw [← permutationFixedEquiv_symm_apply σ v j.val, j.property,
      permutationFixedEquiv_symm_apply]
  simp only [hv, sum_const, card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (cycleSize_pos σ _).ne')

private def integralCoordinates : (Cycles σ → ℤ) →ₗ[ℤ]
    (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule :=
  ((permutationFixedEquiv (R := ℚ) σ).toLinearMap.restrictScalars ℤ).comp
    (LinearMap.pi fun c ↦ (Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj c))

private def projectedCoordinates : (Cycles σ → ℤ) →ₗ[ℤ]
    (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule :=
  ((permutationFixedEquiv (R := ℚ) σ).toLinearMap.restrictScalars ℤ).comp
    (((averageCoordinates σ).toLinearMap.restrictScalars ℤ).comp
      (LinearMap.pi fun c ↦ (Int.castAddHom ℚ).toIntLinearMap.comp (LinearMap.proj c)))

omit [Fintype I] in
private theorem integralCoordinates_apply (a : Cycles σ → ℤ) (i : I) :
    (integralCoordinates σ a).val i = a (Quotient.mk _ i) := by
  simp [integralCoordinates]

private theorem projectedCoordinates_apply (a : Cycles σ → ℤ) (i : I) :
    (projectedCoordinates σ a).val i = (a (Quotient.mk _ i) : ℚ) /
      cycleSize σ (Quotient.mk _ i) := by
  simp [projectedCoordinates, averageCoordinates_apply]

private theorem projectedCoordinates_injective : Function.Injective (projectedCoordinates σ) := by
  classical
  intro a b hab
  funext c
  have h := congrArg (fun v ↦ v.val c.out) hab
  simp only [projectedCoordinates_apply, Quotient.out_eq] at h
  exact Int.cast_injective ((div_left_inj'
    (Nat.cast_ne_zero (R := ℚ) |>.mpr (cycleSize_pos σ c).ne')).mp h)

/-- The integral vectors in the rational permutation-fixed space. -/
def permutationIntegralLattice : Submodule ℤ
    (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule :=
  LinearMap.range (integralCoordinates σ)

/-- The lattice of cycle averages of integral coordinate vectors. Its coordinate on a cycle
of length `n` lies in `n⁻¹ ℤ`. -/
def permutationProjectedLattice : Submodule ℤ
    (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule :=
  LinearMap.range (projectedCoordinates σ)

omit [Fintype I] in
/-- A rational fixed vector is integral exactly when all its coordinates are integers. -/
@[simp]
theorem mem_permutationIntegralLattice_iff
    (v : (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule) :
    v ∈ permutationIntegralLattice σ ↔ ∀ i, ∃ z : ℤ, v.val i = z := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ i
    exact ⟨a (Quotient.mk _ i), integralCoordinates_apply σ a i⟩
  · intro h
    choose a ha using fun c : Cycles σ ↦ h c.out
    refine ⟨a, ?_⟩
    apply (permutationFixedEquiv (R := ℚ) σ).symm.injective
    funext c
    induction c using Quotient.inductionOn with | _ i =>
      simp only [permutationFixedEquiv_symm_apply, integralCoordinates_apply]
      rw [← ha (Quotient.mk _ i)]
      rw [← permutationFixedEquiv_symm_apply σ v, Quotient.out_eq,
        permutationFixedEquiv_symm_apply]

open Classical in
/-- A fixed vector belongs to the projected integral lattice exactly when its coordinate on
each cycle of length `n` is an integer divided by `n`. -/
@[simp]
theorem mem_permutationProjectedLattice_iff
    (v : (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule) :
    v ∈ permutationProjectedLattice σ ↔ ∀ i, ∃ z : ℤ,
      v.val i = (z : ℚ) /
        Fintype.card {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i} := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact ⟨a (Quotient.mk _ i), projectedCoordinates_apply σ a i⟩
  · intro h
    choose a ha using fun c : Cycles σ ↦ h c.out
    refine ⟨a, ?_⟩
    apply (permutationFixedEquiv (R := ℚ) σ).symm.injective
    funext c
    induction c using Quotient.inductionOn with | _ i =>
      simp only [permutationFixedEquiv_symm_apply, projectedCoordinates_apply]
      rw [← permutationFixedEquiv_symm_apply σ v i]
      have hc := ha (Quotient.mk _ i)
      simpa only [← permutationFixedEquiv_symm_apply σ v, Quotient.out_eq,
        cycleSize] using hc.symm

/-- The lattice described by cycle denominators is precisely the image of the integral
coordinate lattice under rational averaging. -/
theorem mem_permutationProjectedLattice_iff_exists_average
    (v : (LinearEquiv.funCongrLeft ℚ ℚ σ).toLinearMap.fixedSubmodule) :
    v ∈ permutationProjectedLattice σ ↔
      ∃ a : I → ℤ, permutationAverage σ (fun i ↦ (a i : ℚ)) = v := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    let b : I → ℤ := fun i ↦ if i = (Quotient.mk (SameCycle.setoid σ) i).out
      then a (Quotient.mk _ i) else 0
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    rw [permutationAverage_apply, projectedCoordinates_apply]
    congr 1
    let c : Cycles σ := Quotient.mk _ i
    let j₀ : {j : I // Quotient.mk (SameCycle.setoid σ) j = c} :=
      ⟨c.out, Quotient.out_eq c⟩
    have hsum : (∑ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = c},
        (b j.val : ℚ)) = a c := by
      rw [Fintype.sum_eq_single j₀]
      · simp [b, j₀, Quotient.out_eq]
      · intro j hj
        have hne : j.val ≠ c.out := fun he ↦ hj (Subtype.ext he)
        simp [b, j.property, hne]
    exact hsum
  · rintro ⟨a, rfl⟩
    rw [mem_permutationProjectedLattice_iff]
    intro i
    refine ⟨∑ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i},
      a j.val, ?_⟩
    simp [permutationAverage_apply]

private def cycleMultiples : AddSubgroup (Cycles σ → ℤ) :=
  AddSubgroup.pi _root_.Set.univ fun c ↦ AddSubgroup.zmultiples (cycleSize σ c : ℤ)

private theorem integralLattice_eq_map :
    (permutationIntegralLattice σ).toAddSubgroup =
      (cycleMultiples σ).map (projectedCoordinates σ).toAddMonoidHom := by
  classical
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun c ↦ (cycleSize σ c : ℤ) * a c, ?_, ?_⟩
    · simp [cycleMultiples, AddSubgroup.mem_pi, Int.mem_zmultiples_iff]
    · apply Subtype.ext
      funext i
      rw [LinearMap.toAddMonoidHom_coe, projectedCoordinates_apply,
        integralCoordinates_apply, Int.cast_mul, Int.cast_natCast]
      exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (cycleSize_pos σ _).ne')
  · rintro ⟨a, ha, rfl⟩
    have hd : ∀ c, (cycleSize σ c : ℤ) ∣ a c := by
      simpa [cycleMultiples, AddSubgroup.mem_pi, Int.mem_zmultiples_iff] using ha
    choose b hb using hd
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    rw [LinearMap.toAddMonoidHom_coe, integralCoordinates_apply, projectedCoordinates_apply, hb,
      Int.cast_mul, Int.cast_natCast]
    exact (mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (cycleSize_pos σ _).ne')).symm

/-- Integral fixed vectors are averages of integral vectors, but the converse need not hold. -/
theorem permutationIntegralLattice_le_projectedLattice :
    permutationIntegralLattice σ ≤ permutationProjectedLattice σ := by
  intro v hv
  -- Forgetting the scalar action does not change lattice membership.
  have hmem : v ∈ (permutationIntegralLattice σ).toAddSubgroup := hv
  rw [integralLattice_eq_map] at hmem
  obtain ⟨a, _, rfl⟩ := hmem
  exact LinearMap.mem_range_self _ a

open Classical in
/-- The index of the integral fixed lattice in the projected lattice is the product of the
cycle lengths. This includes the empty coordinate set, for which the index is one. -/
theorem relIndex_permutationIntegralLattice_projectedLattice :
    (permutationIntegralLattice σ).toAddSubgroup.relIndex
      (permutationProjectedLattice σ).toAddSubgroup =
        ∏ c : Quotient (SameCycle.setoid σ),
          Fintype.card {i : I // Quotient.mk (SameCycle.setoid σ) i = c} := by
  have hrange : (permutationProjectedLattice σ).toAddSubgroup =
      (⊤ : AddSubgroup (Cycles σ → ℤ)).map (projectedCoordinates σ).toAddMonoidHom := by
    simp [permutationProjectedLattice, LinearMap.range_toAddSubgroup, AddSubgroup.map_top]
  rw [integralLattice_eq_map, hrange,
    AddSubgroup.relIndex_map_map_of_injective _ _ (projectedCoordinates_injective σ),
    AddSubgroup.relIndex_top_right]
  simp [cycleMultiples, AddSubgroup.index_pi, Int.index_zmultiples, cycleSize]

end Equiv.Perm
