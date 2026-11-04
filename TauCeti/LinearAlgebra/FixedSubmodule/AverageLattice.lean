/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FixedSubmodule.Norm
public import TauCeti.GroupTheory.Perm.Partition
public import Mathlib.GroupTheory.Index

/-!
# The lattice of orbit averages

Averaging coordinates in a characteristic-zero field along the cycles of a finite permutation
projects onto its fixed space. The image of the integral coordinate lattice is generally larger
than the integral fixed lattice: on a cycle of length `n`, its constant coordinate may be any
element of `n⁻¹ ℤ`. We characterize this image and compute the index of the integral fixed lattice
in it as the product of the cycle lengths. In particular, averaging need not be an integral
retraction: it is one exactly when every cycle has length one.

This is the lattice comparison between projected simple roots and distinct-orbit sums in diagram
folding. It does not identify either lattice with a character or cocharacter lattice.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §7.9.

The averaging map is the normalized full cyclic sum `Equiv.Perm.permutationNorm`.
The fixed-coordinate parametrization is `Equiv.Perm.permutationFixedEquiv`.
-/

public noncomputable section

open Function Finset

namespace Equiv.Perm

variable {I : Type*} (σ : Equiv.Perm I)

private abbrev Cycles := Quotient (SameCycle.setoid σ)

variable [Finite I]

variable {K : Type*} [Field K] [CharZero K]

private theorem minimalPeriod_cast_ne_zero (c : Cycles σ) :
    (minimalPeriod σ c.out : K) ≠ 0 :=
  Nat.cast_ne_zero.mpr
    (minimalPeriod_pos_of_mem_periodicPts (σ.injective.mem_periodicPts c.out)).ne'

private def averageCoordinates : (Cycles σ → K) ≃ₗ[K] (Cycles σ → K) :=
  LinearEquiv.piCongrRight fun c ↦ LinearEquiv.smulOfNeZero K K
    (minimalPeriod σ c.out : K)⁻¹ (inv_ne_zero (minimalPeriod_cast_ne_zero σ c))

private theorem averageCoordinates_apply (a : Cycles σ → K) (c : Cycles σ) :
    averageCoordinates σ a c = a c / minimalPeriod σ c.out := by
  simp [averageCoordinates, div_eq_mul_inv, mul_comm]

open Classical in
/-- Average each coordinate over its permutation cycle. This is a linear projection over `K`,
not the section-dependent integral retraction `permutationFixedProjection`. -/
def permutationAverage : (I → K) →ₗ[K]
    (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule :=
  letI := Fintype.ofFinite I
  (orderOf σ : K)⁻¹ • σ.permutationNorm (R := K) (orderOf σ) (pow_orderOf_eq_one σ)

/-- Every output coordinate is the mean over its cycle. The finite sum is expressed without
choosing decidability or enumeration instances on that cycle. -/
@[simp]
theorem permutationAverage_apply (v : I → K) (i : I) :
    (permutationAverage σ v).val i =
      (∑ᶠ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i}, v j.val) /
        minimalPeriod σ i := by
  classical
  let := Fintype.ofFinite I
  let c : Cycles σ := Quotient.mk _ i
  rw [← (Quotient.exact (Quotient.out_eq c)).minimalPeriod_eq]
  have hsum : (∑ᶠ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = c}, v j.val) =
      ∑ j with σ.SameCycle c.out j, v j := by
    rw [finsum_eq_sum_of_fintype,
      ← Finset.sum_subtype (univ.filter (σ.SameCycle c.out)) (fun j ↦ ?_) v]
    simp only [mem_filter, mem_univ, true_and]
    exact σ.sameCycle_out_iff
  have hp : IsPeriodicPt σ (orderOf σ) c.out := by
    simp only [IsPeriodicPt, IsFixedPt, ← coe_pow, pow_orderOf_eq_one, one_apply]
  have hd : minimalPeriod σ c.out ∣ orderOf σ := hp.minimalPeriod_dvd
  have hmul : ((orderOf σ / minimalPeriod σ c.out : ℕ) : K) *
      (minimalPeriod σ c.out : K) = (orderOf σ : K) := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hquot : (orderOf σ : K)⁻¹ * ((orderOf σ / minimalPeriod σ c.out : ℕ) : K) =
      (minimalPeriod σ c.out : K)⁻¹ := by
    apply mul_right_cancel₀ (minimalPeriod_cast_ne_zero (K := K) σ c)
    rw [mul_assoc, hmul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (orderOf_pos σ).ne'),
      inv_mul_cancel₀ (minimalPeriod_cast_ne_zero σ c)]
  calc
    (permutationAverage σ v).val i = (permutationAverage σ v).val c.out :=
      permutationFixed_apply_eq_of_quotient_eq σ _ (Quotient.out_eq c).symm
    _ = _ := by
      rw [permutationAverage, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
        smul_eq_mul, permutationNorm_apply_eq_nsmul_sum_cycle, nsmul_eq_mul,
        ← mul_assoc, hquot]
      simpa only [c, div_eq_mul_inv, mul_comm] using
        congrArg ((minimalPeriod σ c.out : K)⁻¹ * ·) hsum.symm

/-- Averaging fixes every fixed vector over `K`. -/
@[simp]
theorem permutationAverage_fixed
    (v : (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule) :
    permutationAverage σ v.val = v := by
  classical
  let := Fintype.ofFinite I
  apply Subtype.ext
  funext i
  rw [permutationAverage_apply, finsum_eq_sum_of_fintype,
    ← (Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid σ) i))).minimalPeriod_eq]
  have hv (j : {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i}) :
      v.val j.val = v.val i :=
    permutationFixed_apply_eq_of_quotient_eq σ v j.property
  have hcard : Nat.card {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i} =
      minimalPeriod σ (Quotient.mk (SameCycle.setoid σ) i).out := by
    have h : (fun j ↦ Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i) =
        (fun j ↦ σ.SameCycle (Quotient.mk (SameCycle.setoid σ) i).out j) := by
      funext j
      exact propext σ.sameCycle_out_iff.symm
    rw [h]
    exact ncard_setOf_sameCycle σ _
  simp only [hv, sum_const, card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hcard]
  exact mul_div_cancel_left₀ _ (minimalPeriod_cast_ne_zero σ _)

/-- Averaging is a linear retraction of the fixed-submodule inclusion. -/
theorem permutationAverage_comp_subtype :
    (permutationAverage (K := K) σ).comp
      (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule.subtype = LinearMap.id := by
  ext v i
  exact congrFun (congrArg Subtype.val (permutationAverage_fixed σ v)) i

private def integralCoordinates : (Cycles σ → ℤ) →ₗ[ℤ]
    (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule :=
  ((permutationFixedEquiv (R := K) σ).toLinearMap.restrictScalars ℤ).comp
    (LinearMap.pi fun c ↦ (Int.castAddHom K).toIntLinearMap.comp (LinearMap.proj c))

private def projectedCoordinates : (Cycles σ → ℤ) →ₗ[ℤ]
    (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule :=
  ((permutationFixedEquiv (R := K) σ).toLinearMap.restrictScalars ℤ).comp
    (((averageCoordinates σ).toLinearMap.restrictScalars ℤ).comp
      (LinearMap.pi fun c ↦ (Int.castAddHom K).toIntLinearMap.comp (LinearMap.proj c)))

omit [Finite I] [CharZero K] in
private theorem integralCoordinates_apply (a : Cycles σ → ℤ) (i : I) :
    (integralCoordinates (K := K) σ a).val i = a (Quotient.mk _ i) := by
  simp [integralCoordinates]

private theorem projectedCoordinates_apply (a : Cycles σ → ℤ) (i : I) :
    (projectedCoordinates (K := K) σ a).val i = (a (Quotient.mk _ i) : K) /
      minimalPeriod σ (Quotient.mk (SameCycle.setoid σ) i).out := by
  simp [projectedCoordinates, averageCoordinates_apply]

private theorem projectedCoordinates_injective :
    Function.Injective (projectedCoordinates (K := K) σ) := by
  classical
  intro a b hab
  funext c
  have h := congrArg (fun v ↦ v.val c.out) hab
  simp only [projectedCoordinates_apply, Quotient.out_eq] at h
  exact Int.cast_injective ((div_left_inj' (minimalPeriod_cast_ne_zero σ c)).mp h)

/-- The integral vectors in the permutation-fixed space over `K`. -/
def permutationIntegralLattice : Submodule ℤ
    (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule :=
  LinearMap.range (integralCoordinates σ)

/-- The lattice of cycle averages of integral coordinate vectors. Its coordinate on a cycle
of length `n` lies in `n⁻¹ ℤ`. -/
def permutationProjectedLattice : Submodule ℤ
    (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule :=
  LinearMap.range (projectedCoordinates σ)

omit [Finite I] [CharZero K] in
/-- A fixed vector is integral exactly when all its coordinates are integers. -/
@[simp]
theorem mem_permutationIntegralLattice_iff
    (v : (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule) :
    v ∈ permutationIntegralLattice (K := K) σ ↔ ∀ i, ∃ z : ℤ, v.val i = z := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ i
    exact ⟨a (Quotient.mk _ i), integralCoordinates_apply σ a i⟩
  · intro h
    choose a ha using fun c : Cycles σ ↦ h c.out
    refine ⟨a, ?_⟩
    apply Subtype.ext
    funext i
    rw [integralCoordinates_apply, ← ha]
    exact permutationFixed_apply_eq_of_quotient_eq σ v (Quotient.out_eq _)

/-- A fixed vector belongs to the projected integral lattice exactly when its coordinate on
each cycle of length `n` is an integer divided by `n`. -/
@[simp]
theorem mem_permutationProjectedLattice_iff
    (v : (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule) :
    v ∈ permutationProjectedLattice (K := K) σ ↔ ∀ i, ∃ z : ℤ,
      v.val i = (z : K) / minimalPeriod σ i := by
  classical
  constructor
  · rintro ⟨a, rfl⟩ i
    refine ⟨a (Quotient.mk _ i), ?_⟩
    rw [projectedCoordinates_apply,
      (Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid σ) i))).minimalPeriod_eq]
  · intro h
    choose a ha using fun c : Cycles σ ↦ h c.out
    refine ⟨a, ?_⟩
    apply Subtype.ext
    funext i
    rw [projectedCoordinates_apply]
    have hc := ha (Quotient.mk _ i)
    exact hc.symm.trans (permutationFixed_apply_eq_of_quotient_eq σ v (Quotient.out_eq _))

/-- The lattice described by cycle denominators is precisely the image of the integral
coordinate lattice under averaging over `K`. -/
theorem mem_permutationProjectedLattice_iff_exists_average
    (v : (LinearEquiv.funCongrLeft K K σ).toLinearMap.fixedSubmodule) :
    v ∈ permutationProjectedLattice (K := K) σ ↔
      ∃ a : I → ℤ, permutationAverage σ (fun i ↦ (a i : K)) = v := by
  classical
  let := Fintype.ofFinite I
  constructor
  · rintro ⟨a, rfl⟩
    let b : I → ℤ := fun i ↦ if i = (Quotient.mk (SameCycle.setoid σ) i).out
      then a (Quotient.mk _ i) else 0
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    rw [permutationAverage_apply, finsum_eq_sum_of_fintype, projectedCoordinates_apply,
      (Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid σ) i))).minimalPeriod_eq]
    congr 1
    let c : Cycles σ := Quotient.mk _ i
    have hsum : (∑ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = c},
        b j.val) = a c := by
      rw [← Finset.sum_subtype (univ.filter (σ.SameCycle c.out)) (fun j ↦ ?_) b]
      · simpa only [b] using sum_sameCycle_ite_out_eq σ a c
      · simp only [mem_filter, mem_univ, true_and]
        exact σ.sameCycle_out_iff
    exact_mod_cast hsum
  · rintro ⟨a, rfl⟩
    rw [mem_permutationProjectedLattice_iff]
    intro i
    refine ⟨∑ j : {j : I // Quotient.mk (SameCycle.setoid σ) j = Quotient.mk _ i},
      a j.val, ?_⟩
    simp [permutationAverage_apply, finsum_eq_sum_of_fintype]

private def cycleMultiples : AddSubgroup (Cycles σ → ℤ) :=
  AddSubgroup.pi _root_.Set.univ fun c ↦
    AddSubgroup.zmultiples (minimalPeriod σ c.out : ℤ)

private theorem integralLattice_eq_map :
    (permutationIntegralLattice (K := K) σ).toAddSubgroup =
      (cycleMultiples σ).map (projectedCoordinates σ).toAddMonoidHom := by
  classical
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨fun c ↦ (minimalPeriod σ c.out : ℤ) * a c, ?_, ?_⟩
    · simp [cycleMultiples, AddSubgroup.mem_pi, Int.mem_zmultiples_iff]
    · apply Subtype.ext
      funext i
      rw [LinearMap.toAddMonoidHom_coe, projectedCoordinates_apply,
        integralCoordinates_apply, Int.cast_mul, Int.cast_natCast]
      exact mul_div_cancel_left₀ _ (minimalPeriod_cast_ne_zero σ _)
  · rintro ⟨a, ha, rfl⟩
    have hd : ∀ c, (minimalPeriod σ c.out : ℤ) ∣ a c := by
      simpa [cycleMultiples, AddSubgroup.mem_pi, Int.mem_zmultiples_iff] using ha
    choose b hb using hd
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext i
    rw [LinearMap.toAddMonoidHom_coe, integralCoordinates_apply, projectedCoordinates_apply, hb,
      Int.cast_mul, Int.cast_natCast]
    exact (mul_div_cancel_left₀ _ (minimalPeriod_cast_ne_zero σ _)).symm

/-- Integral fixed vectors are averages of integral vectors, but the converse need not hold. -/
theorem permutationIntegralLattice_le_permutationProjectedLattice :
    permutationIntegralLattice (K := K) σ ≤ permutationProjectedLattice σ := by
  intro v hv
  -- Forgetting the scalar action does not change lattice membership.
  have hmem : v ∈ (permutationIntegralLattice σ).toAddSubgroup := hv
  rw [integralLattice_eq_map] at hmem
  obtain ⟨a, _, rfl⟩ := hmem
  exact LinearMap.mem_range_self _ a

/-- The index of the integral fixed lattice in the projected lattice is the product of the
cycle lengths. This includes the empty coordinate set, for which the index is one. -/
theorem relIndex_permutationIntegralLattice_permutationProjectedLattice :
    (permutationIntegralLattice (K := K) σ).toAddSubgroup.relIndex
      (permutationProjectedLattice σ).toAddSubgroup =
        ∏ᶠ c : Quotient (SameCycle.setoid σ), minimalPeriod σ c.out := by
  classical
  let := Fintype.ofFinite I
  have hrange : (permutationProjectedLattice (K := K) σ).toAddSubgroup =
      (⊤ : AddSubgroup (Cycles σ → ℤ)).map (projectedCoordinates σ).toAddMonoidHom := by
    simp [permutationProjectedLattice, LinearMap.range_toAddSubgroup, AddSubgroup.map_top]
  rw [integralLattice_eq_map, hrange,
    AddSubgroup.relIndex_map_map_of_injective _ _ (projectedCoordinates_injective σ),
    AddSubgroup.relIndex_top_right]
  simp [cycleMultiples, AddSubgroup.index_pi, Int.index_zmultiples,
    finprod_eq_prod_of_fintype]

end Equiv.Perm
