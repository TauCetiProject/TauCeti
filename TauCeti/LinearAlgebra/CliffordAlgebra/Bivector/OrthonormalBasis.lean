/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic

/-!
# Clifford bivectors in an orthonormal basis

Let `V` be a finite-dimensional real inner product space, `Q` a quadratic form on `V` and
`(eₖ)` an orthonormal basis. The bivector map `c₂ = CliffordAlgebra.bivectorExterior Q` of a
two-vector expands over all ordered pairs of basis vectors,
`2 c₂(x) = ∑ⱼ ∑ₖ ⟪x, eⱼ ∧ eₖ⟫ c₂(eⱼ, eₖ)`. For a Clifford module of `Q v = -‖v‖²` this gives the
contraction `∑ⱼ ∑ₖ c(eⱼ) c(eₖ) T j k = -∑ₖ T k k + c₂(F) z` of a two-index family whose
antisymmetric part is `⟪F, eⱼ ∧ eₖ⟫ z`, the algebraic step of the Weitzenböck formula.

## Main results

* `CliffordAlgebra.two_smul_bivectorExterior_eq_sum`: the basis expansion of `2 c₂(x)`.
* `CliffordAlgebra.sum_ι_sum_ι_apply`: the Clifford contraction of a two-index family.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989,
  Chapter II, §8.
-/

public section

namespace CliffordAlgebra

open Module
open scoped RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V}
  {S W : Type*} [CommRing S] [Algebra ℝ S] [AddCommGroup W] [Module S W] [Module ℝ W]
  [IsScalarTower ℝ S W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End S W)

/-- **The Clifford action of a two-vector in an orthonormal basis**:
`2 c₂(x) = ∑ⱼ ∑ₖ ⟪x, eⱼ ∧ eₖ⟫ c₂(eⱼ, eₖ)`, where `c₂(u, w) = (c(u) c(w) - c(w) c(u)) / 2` is the
Clifford bivector of `u` and `w`. -/
theorem two_smul_bivectorExterior_eq_sum {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ V) (x : ⋀[ℝ]^2 V) :
    (2 : ℝ) • bivectorExterior Q x =
      ∑ j, ∑ k, ⟪x, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ • bivector Q (e j) (e k) := by
  have h := LinearMap.congr_fun (e.sum_rankOne_ιMulti_two) x
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    LinearMap.smul_apply, LinearMap.id_apply] at h
  rw [← map_smul, ← h]
  simp [map_sum, map_smul, real_inner_comm]

/-- **The Clifford contraction of a two-index family.** For a Clifford module of
`Q v = -‖v‖²`, if the antisymmetric part of `T` is `T j k - T k j = ⟪F, eⱼ ∧ eₖ⟫ z`, then
`∑ⱼ ∑ₖ c(eⱼ) c(eₖ) T j k = -∑ₖ T k k + c₂(F) z`. This is the Clifford algebra of the
Weitzenböck formula. -/
theorem sum_ι_sum_ι_apply (hQ : ∀ v, Q v = -‖v‖ ^ 2) {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ V) (F : ⋀[ℝ]^2 V) (z : W) (T : κ → κ → W)
    (hT : ∀ j k, T j k - T k j = ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ • z) :
    ∑ j, ρ (ι Q (e j)) (∑ k, ρ (ι Q (e k)) (T j k)) =
      -∑ k, T k k + ρ (bivectorExterior Q F) z := by
  classical
  -- `c(eⱼ) c(eₖ) = c₂(eⱼ, eₖ) - ⟪eⱼ, eₖ⟫`, by the Clifford relation.
  have hcc (j k : κ) (y : W) :
      ρ (ι Q (e j)) (ρ (ι Q (e k)) y) = ρ (bivector Q (e j) (e k)) y - ⟪e j, e k⟫ • y := by
    have hpolar : QuadraticMap.polar Q (e j) (e k) = -2 * ⟪e j, e k⟫ := by
      simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
      ring
    rw [← mul_apply_eq_comp, ← map_mul, ι_mul_ι_eq_bivector_add, hpolar, map_add, map_smul,
      AlgHom.commutes, LinearMap.add_apply, LinearMap.smul_apply, Module.algebraMap_end_apply,
      smul_smul, invOf_eq_inv]
    module
  -- The symmetric part contracts to the trace.
  have hsym : ∑ j, ∑ k, ⟪e j, e k⟫ • T j k = ∑ k, T k k := by
    simp only [e.inner_eq_ite, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
  -- The antisymmetric part: `S = c₂(F) z`, computed from `2 S`.
  set S := ∑ j, ∑ k, ρ (bivector Q (e j) (e k)) (T j k) with hS
  have hswap : S = -∑ j, ∑ k, ρ (bivector Q (e j) (e k)) (T k j) := by
    rw [hS, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [bivector_swap Q (e j) (e k), map_neg, LinearMap.neg_apply]
  have h2 : (2 : ℝ) • S = (2 : ℝ) • ρ (bivectorExterior Q F) z := by
    calc (2 : ℝ) • S = S + S := two_smul ℝ S
      _ = ∑ j, ∑ k, ρ (bivector Q (e j) (e k)) (T j k - T k j) := by
        nth_rw 2 [hswap]
        simp only [hS, map_sub, Finset.sum_sub_distrib]
        abel
      _ = ρ (∑ j, ∑ k,
          ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ • bivector Q (e j) (e k)) z := by
        simp [hT, map_sum, LinearMap.map_smul_of_tower]
      _ = (2 : ℝ) • ρ (bivectorExterior Q F) z := by
        rw [← two_smul_bivectorExterior_eq_sum e F, map_smul, LinearMap.smul_apply]
  have hSF : S = ρ (bivectorExterior Q F) z := smul_right_injective W two_ne_zero h2
  simp only [map_sum, hcc, Finset.sum_sub_distrib, ← hS, hsym, hSF]
  abel

end CliffordAlgebra
