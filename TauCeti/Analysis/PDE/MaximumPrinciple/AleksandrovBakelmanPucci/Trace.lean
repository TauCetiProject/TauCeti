/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Sobolev
public import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
import TauCeti.Topology.Frontier

/-!
# The weak maximum principle for strong subsolutions in trace form

Let `Ω` be a bounded open subset of a finite-dimensional real inner product space `F` of
dimension `n`, and let `u ∈ W^{2,n}(Ω)` have a representative `ū` continuous on `closure Ω`. A
non-divergence-form operator `L u = tr (A ∘ D²u) + c u` with coefficients `A(x) : F → F` and
`c(x) ∈ ℝ` is written here without coordinates, as the trace of the composition of `A(x)` with the
weak Hessian `D²u(x)`; in an orthonormal basis it is `∑ᵢⱼ aʲⁱ ∂ᵢ∂ⱼu + c u`. This file proves the
**weak maximum principle** for strong subsolutions, `L u ≥ 0` almost everywhere: if `A(x)` is
positive definite, `⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, almost everywhere, then

* for `c = 0`, `ū ≤ m` on `Ω` whenever `ū ≤ m` on `frontier Ω`
  (`TauCeti.PDE.le_of_nonneg_traceCLM_comp_iteratedGradient_le_frontier`);
* for `c ≤ 0`, `ū ≤ m` on `Ω` whenever `ū ≤ m` on `frontier Ω` and `m ≥ 0`
  (`TauCeti.PDE.le_of_nonneg_traceCLM_comp_iteratedGradient_add_mul_le_frontier`).

The coefficients need no regularity, not even measurability, and `A(x)` need not be symmetric.
This is the uniqueness input for strong solutions of the Dirichlet problem: two solutions in
`W^{2,n}(Ω)` with the same continuous boundary values agree. The sign condition `c ≤ 0` cannot be
dropped: `u = sin x` on `(0, π)` solves `u'' + u = 0`, vanishes on the boundary and is positive
inside.

## The argument

The case `c = 0` is the Aleksandrov–Bakelman–Pucci estimate
`TauCeti.PDE.le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp` with right-hand side `0`, after
transporting `u` to `EuclideanSpace ℝ (Fin n)` along the coordinate isometry of an orthonormal
basis `(bᵢ)` (`TauCeti.Wkp.compLinearIsometryEquiv`). There the coefficient matrix is that of the
symmetric part `S = (A + A†) / 2` of `A` in this basis, which is positive definite. Since the weak
Hessian is self-adjoint almost everywhere (`TauCeti.Wkp.adjoint_iteratedGradient_one_ae_eq`),
`∑ᵢⱼ ⟪bᵢ, S bⱼ⟫ ⟪bᵢ, D²u bⱼ⟫ = tr (S ∘ D²u) = tr (A ∘ D²u)`.

For `c ≤ 0`, apply the case `c = 0` on the open set `{x ∈ Ω | ū x > m}`, where `ū > 0` and hence
`tr (A ∘ D²u) ≥ -c ū ≥ 0`, and whose frontier points satisfy `ū ≤ m`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.1 and Lemma 9.3.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Module Set TopologicalSpace
open scoped ENNReal Matrix RealInnerProductSpace

namespace TauCeti

namespace PDE

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] {Ω : Opens F} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {ū : F → ℝ} {A : F → F →L[ℝ] F} {m : ℝ}

/-- **The weak maximum principle for strong subsolutions** (Gilbarg–Trudinger, Theorem 9.1 with
`b = 0`, `c = 0` and `f = 0`). Let `Ω` be a bounded open subset of a real inner product space of
dimension `n`, let `u ∈ W^{2,n}(Ω)` have a representative `ū` continuous on `closure Ω`, and let
`A(x)` be positive definite, `⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, for almost every `x ∈ Ω`. If
`tr (A ∘ D²u) ≥ 0` almost everywhere on `Ω` and `ū ≤ m` on `frontier Ω`, then `ū ≤ m` on `Ω`. -/
theorem le_of_nonneg_traceCLM_comp_iteratedGradient_le_frontier
    (hΩb : Bornology.IsBounded (Ω : Set F)) (hp : p = finrank ℝ F) (u : Wkp volume Ω p 2)
    (hcont : ContinuousOn ū (closure Ω)) (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū)
    (hA : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫)
    (hL : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ traceCLM ℝ F (A x ∘L Wkp.iteratedGradient 1 u x))
    (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) : ū x ≤ m := by
  -- Transport everything to `ℝⁿ` along the coordinates `e` of an orthonormal basis `b`.
  set b := stdOrthonormalBasis ℝ F
  set e := b.repr
  let Ω' : Opens (EuclideanSpace ℝ (Fin (finrank ℝ F))) :=
    ⟨e.symm ⁻¹' Ω, Ω.isOpen.preimage e.symm.continuous⟩
  have hUW : (Ω' : Set (EuclideanSpace ℝ (Fin (finrank ℝ F)))) = e.symm ⁻¹' Ω := rfl
  have he : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have he' := (he.restrict_preimage Ω.isOpen.measurableSet).quasiMeasurePreserving
  set u' := Wkp.compLinearIsometryEquiv he hUW 2 u
  set a : EuclideanSpace ℝ (Fin (finrank ℝ F)) →
      Matrix (Fin (finrank ℝ F)) (Fin (finrank ℝ F)) ℝ := fun y =>
    LinearMap.toMatrix b.toBasis b.toBasis
      (((2⁻¹ : ℝ) • (A (e.symm y) + (A (e.symm y)).adjoint) : F →L[ℝ] F) : F →ₗ[ℝ] F)
  have hsub : ∀ {P : EuclideanSpace ℝ (Fin (finrank ℝ F)) → Prop},
      (∀ᵐ y ∂volume.restrict (Ω' : Set _), P y) →
        ∀ᵐ y ∂volume.restrict (upperContactSet (ū ∘ e.symm) Ω'), P y := fun h =>
    ae_restrict_of_ae_restrict_of_subset (fun _ hy => (mem_upperContactSet.1 hy).1) h
  have hclosure : closure (Ω' : Set (EuclideanSpace ℝ (Fin (finrank ℝ F)))) =
      e.symm ⁻¹' closure Ω := (e.symm.toHomeomorph.preimage_closure _).symm
  have hfrontier : frontier (Ω' : Set (EuclideanSpace ℝ (Fin (finrank ℝ F)))) =
      e.symm ⁻¹' frontier Ω := (e.symm.toHomeomorph.preimage_frontier _).symm
  have key := le_add_mul_eLpNorm_negPart_div_det_rpow_of_wkp (Ω := Ω') (f := 0) (a := a)
    (m := m) (x := e x)
    (by rw [hUW, ← e.image_eq_preimage_symm]; exact e.lipschitzWith.isBounded_image hΩb)
    (by simpa using hp) u'
    (by rw [hclosure]; exact hcont.comp e.symm.continuous.continuousOn fun y hy => hy)
    ((Wkp.value_compLinearIsometryEquiv_ae he hUW 2 u).trans (he'.ae_eq_comp hū))
    (hsub (he'.ae (hA.mono fun y hy => ContinuousLinearMap.posDef_toMatrix_symmPart hy b)))
    (hsub ?_) (by simp) (fun z hz => hm _ (by rwa [hfrontier] at hz))
    (by
      rw [← SetLike.mem_coe, hUW, mem_preimage, LinearIsometryEquiv.symm_apply_apply]
      exact hx)
  · simpa using key
  -- The principal part in coordinates is `tr (A ∘ D²u) ≥ 0`.
  filter_upwards [he'.ae hL, he'.ae (Wkp.adjoint_iteratedGradient_one_ae_eq u),
    Wkp.iteratedGradient_compLinearIsometryEquiv_ae he hUW 1 u] with y hy hsym hD
  rw [Pi.zero_apply, hD]
  refine hy.trans_eq
    ((ContinuousLinearMap.sum_toMatrix_symmPart_mul_repr _ _ hsym b).symm.trans ?_)
  -- In coordinates the weak Hessian of `u'` is `e ∘ D²u ∘ e⁻¹`, with columns `e (D²u bⱼ)`.
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [LinearIsometryEquiv.iteratedGradientCongr_symm_succ_apply e.symm 0]
  congr 1
  rw [LinearIsometryEquiv.iteratedGradientCongr_zero, LinearIsometryEquiv.symm_symm]
  -- The composite `e ∘ D²u ∘ e⁻¹` applied to `eⱼ` unfolds to `e (D²u (e⁻¹ eⱼ))`.
  exact congrArg (fun v => (b.repr (Wkp.iteratedGradient 1 u (e.symm y) v)).ofLp i)
    (b.repr_symm_single j).symm

/-- **The weak maximum principle for strong subsolutions with a zeroth-order term**
(Gilbarg–Trudinger, Theorem 9.1 with `b = 0` and `f = 0`). Let `Ω` be a bounded open subset of a
real inner product space of dimension `n`, let `u ∈ W^{2,n}(Ω)` have a representative `ū`
continuous on `closure Ω`, let `A(x)` be positive definite, `⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, and let
`c(x) ≤ 0`, for almost every `x ∈ Ω`. If `tr (A ∘ D²u) + c u ≥ 0` almost everywhere on `Ω` and
`ū ≤ m` on `frontier Ω` with `m ≥ 0`, then `ū ≤ m` on `Ω`. -/
theorem le_of_nonneg_traceCLM_comp_iteratedGradient_add_mul_le_frontier
    (hΩb : Bornology.IsBounded (Ω : Set F)) (hp : p = finrank ℝ F) (u : Wkp volume Ω p 2)
    (hcont : ContinuousOn ū (closure Ω)) (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū)
    (hA : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫) {c : F → ℝ}
    (hc : ∀ᵐ x ∂volume.restrict Ω, c x ≤ 0)
    (hL : ∀ᵐ x ∂volume.restrict Ω,
      0 ≤ traceCLM ℝ F (A x ∘L Wkp.iteratedGradient 1 u x) + c x * Wkp.value 2 u x)
    (hm0 : 0 ≤ m) (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) : ū x ≤ m := by
  by_contra! hxm
  -- Apply the case `c = 0` on `V = {y ∈ Ω | m < ū y}`, where `ū > 0`.
  let V : Opens F := ⟨Ω ∩ ū ⁻¹' Ioi m,
    (hcont.mono subset_closure).isOpen_inter_preimage Ω.isOpen isOpen_Ioi⟩
  have hVΩ : V ≤ Ω := fun _ hy => hy.1
  have hVsub {P : F → Prop} (h : ∀ᵐ y ∂volume.restrict Ω, P y) :
      ∀ᵐ y ∂volume.restrict (V : Set F), P y :=
    ae_restrict_of_ae_restrict_of_subset hVΩ h
  have hVae : ∀ᵐ y ∂volume.restrict (V : Set F), y ∈ V :=
    ae_restrict_mem V.isOpen.measurableSet
  refine (le_of_nonneg_traceCLM_comp_iteratedGradient_le_frontier (hΩb.subset hVΩ) hp
    (Wkp.restrictL hVΩ 2 u) (hcont.mono (closure_mono hVΩ))
    ((Wkp.value_restrictL_ae hVΩ 2 u).trans (hVsub hū)) (hVsub hA) ?_ (fun z hz => ?_)
    ⟨hx, hxm⟩).not_gt hxm
  · filter_upwards [hVsub hL, hVsub hc, hVsub hū, hVae,
      Wkp.iteratedGradient_restrictL_ae hVΩ 1 u] with y hy hcy hūy hyV hD
    rw [hD]
    have : c y * Wkp.value 2 u y ≤ 0 := by
      rw [hūy]
      exact mul_nonpos_of_nonpos_of_nonneg hcy (hm0.trans hyV.2.le)
    linarith
  · exact le_of_mem_frontier_inter_preimage_Ioi Ω.isOpen (hcont.mono subset_closure) hm hz

end PDE

end TauCeti
