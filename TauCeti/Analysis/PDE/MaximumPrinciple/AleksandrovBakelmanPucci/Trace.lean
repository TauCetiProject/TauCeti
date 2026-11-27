/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.MaximumPrinciple.AleksandrovBakelmanPucci.Sobolev
public import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Positive.Definite
import TauCeti.Analysis.InnerProductSpace.Trace.Free
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.Analysis.Sobolev.Wkp.LineDeriv.Basic
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
  (`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_nonneg_le_frontier`);
* for `c ≤ 0`, `ū ≤ m` on `Ω` whenever `ū ≤ m` on `frontier Ω` and `m ≥ 0`
  (`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier`).

The coefficients need no regularity, not even measurability, and `A(x)` need not be symmetric.
This is the uniqueness input for strong solutions of the Dirichlet problem: two solutions in
`W^{2,n}(Ω)` with the same continuous boundary values agree. The sign condition `c ≤ 0` cannot be
dropped: `u = sin x` on `(0, π)` solves `u'' + u = 0`, vanishes on the boundary and is positive
inside.

The same conclusions hold for operators with a drift, `L u = tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u`, when
`ū` is moreover `C¹` in `Ω` and `|b| / D*` lies in `Lⁿ(Ω)`, where `D* = (det S)^{1/n}` for the
symmetric part `S = (A + A†) / 2` of `A`
(`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_inner_nonneg_le_frontier` and
`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_nonneg_le_frontier`). This is
the hypothesis of Gilbarg–Trudinger, Theorem 9.1. Every `u ∈ W^{2,p}(Ω)` with `p > n` has a `C¹`
representative by Morrey's embedding, so the drift form applies to the strong solutions of
`W^{2,p}` Dirichlet problems with bounded drift.

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

With a drift, suppose that `ū x > m` and let `R = (ū x - m) / diam Ω`. For `0 < r ≤ R` the
Aleksandrov measure estimate restricted to slopes of norm at most `r`
(`TauCeti.PDE.addHaar_ball_le_lintegral_abs_det_iteratedGradient_of_le`) bounds `|B(0, r)|` by the
integral of `|det D²u|` over the contact points whose supporting slope has norm at most `r`. Since
`ū` is differentiable, that slope is `∇ū`, which is the weak gradient almost everywhere. There
`tr (A ∘ D²u) ≥ -⟪b, ∇u⟫ ≥ -|b| r`, so the pointwise bound
(`TauCeti.PDE.abs_det_le_negPart_div_finrank_pow_div_det_symmPart`) gives
`|det D²u| ≤ (r / n)ⁿ |b|ⁿ / det S`, and it gives `0` where `∇u = 0`. Hence
`|B(0, 1)| ≤ n⁻ⁿ ∫ |b|ⁿ / det S` over the points where `0 < |∇u| ≤ r`. As `r → 0` these sets
decrease to the empty set, so the right side tends to `0`, which is absurd.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.1 and Lemma 9.3.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Module Set TopologicalSpace
open scoped ENNReal Gradient Matrix NNReal RealInnerProductSpace

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
theorem le_of_traceCLM_comp_iteratedGradient_nonneg_le_frontier
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

/-- The reduction of the weak maximum principles with `c ≤ 0` to `c = 0`: if `ū x > m ≥ 0` at
`x ∈ Ω`, then `x` lies in the open set `V = {y ∈ Ω | m < ū y} ⊆ Ω`, on whose frontier `ū ≤ m`, and
`c u ≤ 0` almost everywhere on `V`. -/
private theorem exists_le_and_mem_and_le_frontier_and_mul_value_nonpos
    (hcont : ContinuousOn ū (closure Ω)) {u : Wkp volume Ω p 2}
    (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū) {c : F → ℝ}
    (hc : ∀ᵐ x ∂volume.restrict Ω, c x ≤ 0) (hm0 : 0 ≤ m)
    (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) (hxm : m < ū x) :
    ∃ V : Opens F, V ≤ Ω ∧ x ∈ V ∧ (∀ z ∈ frontier (V : Set F), ū z ≤ m) ∧
      ∀ᵐ y ∂volume.restrict (V : Set F), c y * Wkp.value 2 u y ≤ 0 := by
  let V : Opens F := ⟨Ω ∩ ū ⁻¹' Ioi m,
    (hcont.mono subset_closure).isOpen_inter_preimage Ω.isOpen isOpen_Ioi⟩
  have hVΩ : V ≤ Ω := fun _ hy => hy.1
  refine ⟨V, hVΩ, ⟨hx, hxm⟩,
    fun z hz => le_of_mem_frontier_inter_preimage_Ioi Ω.isOpen (hcont.mono subset_closure) hm hz,
    ?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hVΩ hc,
    ae_restrict_of_ae_restrict_of_subset hVΩ hū, ae_restrict_mem V.isOpen.measurableSet]
    with y hcy hūy hyV
  rw [hūy]
  exact mul_nonpos_of_nonpos_of_nonneg hcy (hm0.trans hyV.2.le)

/-- **The weak maximum principle for strong subsolutions with a zeroth-order term**
(Gilbarg–Trudinger, Theorem 9.1 with `b = 0` and `f = 0`). Let `Ω` be a bounded open subset of a
real inner product space of dimension `n`, let `u ∈ W^{2,n}(Ω)` have a representative `ū`
continuous on `closure Ω`, let `A(x)` be positive definite, `⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, and let
`c(x) ≤ 0`, for almost every `x ∈ Ω`. If `tr (A ∘ D²u) + c u ≥ 0` almost everywhere on `Ω` and
`ū ≤ m` on `frontier Ω` with `m ≥ 0`, then `ū ≤ m` on `Ω`. -/
theorem le_of_traceCLM_comp_iteratedGradient_add_mul_nonneg_le_frontier
    (hΩb : Bornology.IsBounded (Ω : Set F)) (hp : p = finrank ℝ F) (u : Wkp volume Ω p 2)
    (hcont : ContinuousOn ū (closure Ω)) (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū)
    (hA : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫) {c : F → ℝ}
    (hc : ∀ᵐ x ∂volume.restrict Ω, c x ≤ 0)
    (hL : ∀ᵐ x ∂volume.restrict Ω,
      0 ≤ traceCLM ℝ F (A x ∘L Wkp.iteratedGradient 1 u x) + c x * Wkp.value 2 u x)
    (hm0 : 0 ≤ m) (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) : ū x ≤ m := by
  by_contra! hxm
  -- Apply the case `c = 0` on `V = {y ∈ Ω | m < ū y}`, where `c u ≤ 0`.
  obtain ⟨V, hVΩ, hxV, hVm, hcV⟩ :=
    exists_le_and_mem_and_le_frontier_and_mul_value_nonpos hcont hū hc hm0 hm hx hxm
  have hVsub {P : F → Prop} (h : ∀ᵐ y ∂volume.restrict Ω, P y) :
      ∀ᵐ y ∂volume.restrict (V : Set F), P y :=
    ae_restrict_of_ae_restrict_of_subset hVΩ h
  refine (le_of_traceCLM_comp_iteratedGradient_nonneg_le_frontier (hΩb.subset hVΩ) hp
    (Wkp.restrictL hVΩ 2 u) (hcont.mono (closure_mono hVΩ))
    ((Wkp.value_restrictL_ae hVΩ 2 u).trans (hVsub hū)) (hVsub hA) ?_ hVm hxV).not_gt hxm
  filter_upwards [hVsub hL, hcV, Wkp.iteratedGradient_restrictL_ae hVΩ 1 u] with y hy hcy hD
  rw [hD]
  linarith

section Drift

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- The exponent `p = n` of the maximum principles is at least `1`, so the dimension `n` is
positive. -/
private theorem one_le_finrank_of_eq (hp : p = finrank ℝ F) : 1 ≤ finrank ℝ F := by
  have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  rw [hp] at h1
  exact_mod_cast h1

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- The set where a strongly measurable `G` is nonzero with `‖G‖ ≤ r` is measurable. -/
private theorem measurableSet_setOf_ne_zero_and_norm_le {G : F → F} (hG : StronglyMeasurable G)
    (r : ℝ) : MeasurableSet {y | G y ≠ 0 ∧ ‖G y‖ ≤ r} :=
  (hG.measurable (measurableSet_singleton 0)).compl.inter
    (measurableSet_le hG.measurable.norm measurable_const)

omit [MeasurableSpace F] [BorelSpace F] in
/-- **The pointwise bound by the elliptic operator, without coordinates.** If `-T` is a positive
operator on a real inner product space of dimension `n`, `A` is positive definite and
`c ≤ tr (A ∘ T)`, then `|det T| ≤ (c⁻ / n)ⁿ / det S` for the symmetric part `S = (A + A†) / 2` of
`A`. This is `TauCeti.PDE.abs_det_le_negPart_div_card_pow_div_det` read in an orthonormal basis. -/
theorem abs_det_le_negPart_div_finrank_pow_div_det_symmPart {T A : F →L[ℝ] F}
    (hT : (-T).IsPositive) (hA : ∀ ξ, ξ ≠ 0 → 0 < ⟪A ξ, ξ⟫) {c : ℝ}
    (hc : c ≤ traceCLM ℝ F (A ∘L T)) :
    |T.det| ≤ (c⁻ / finrank ℝ F) ^ finrank ℝ F / ((2⁻¹ : ℝ) • (A + A.adjoint)).det := by
  set b := stdOrthonormalBasis ℝ F
  set e := b.repr
  have hTsa : T.adjoint = T := by
    have h := hT.isSelfAdjoint
    rwa [ContinuousLinearMap.isSelfAdjoint_iff', map_neg, neg_inj] at h
  -- `T` in the coordinates of `b`.
  set T' : EuclideanSpace ℝ (Fin (finrank ℝ F)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ F)) :=
    e.toLinearEquiv.toLinearMap ∘ₗ (T : F →ₗ[ℝ] F) ∘ₗ e.symm.toLinearEquiv.toLinearMap
  have hT' : (-T').IsPositive := by
    have hadj : LinearMap.adjoint e.toLinearEquiv.toLinearMap =
        e.symm.toLinearEquiv.toLinearMap := by
      ext x
      exact congrArg (fun L : EuclideanSpace ℝ (Fin (finrank ℝ F)) →L[ℝ] F => L x)
        e.adjoint_eq_symm
    have h := hT.toLinearMap.conj_adjoint e.toLinearEquiv.toLinearMap
    rw [hadj] at h
    simpa [T', LinearMap.comp_neg, LinearMap.neg_comp] using h
  have hcol (j : Fin (finrank ℝ F)) : T' (EuclideanSpace.single j 1) = b.repr (T (b j)) := by
    simp [T', e, b.repr_symm_single]
  have key := abs_det_le_negPart_div_card_pow_div_det hT'
    (ContinuousLinearMap.posDef_toMatrix_symmPart hA b) (c := c) (by
      simpa only [hcol] using
        hc.trans_eq (ContinuousLinearMap.sum_toMatrix_symmPart_mul_repr A T hTsa b).symm)
  have hdet : LinearMap.det T' = T.det := LinearMap.det_conj (T : F →ₗ[ℝ] F) e.toLinearEquiv
  rw [hdet, LinearMap.det_toMatrix, Fintype.card_fin] at key
  exact key

omit [MeasurableSpace F] [BorelSpace F] in
/-- The pointwise bound with a drift: if `-T` is positive, `A` is positive definite,
`tr (A ∘ T) + ⟪b, v⟫ ≥ 0` and `‖v‖ ≤ r`, then `|det T| ≤ (r / n)ⁿ |b|ⁿ / det S` for the symmetric
part `S` of `A`. For `v = 0` this is `det T = 0`, the case `r = 0`. -/
private theorem abs_det_le_div_finrank_pow_mul_norm_pow_div_det {T A : F →L[ℝ] F}
    (hT : (-T).IsPositive) (hA : ∀ ξ, ξ ≠ 0 → 0 < ⟪A ξ, ξ⟫) {b v : F} {r : ℝ}
    (hL : 0 ≤ traceCLM ℝ F (A ∘L T) + ⟪b, v⟫) (hv : ‖v‖ ≤ r) :
    |T.det| ≤ (r / finrank ℝ F) ^ finrank ℝ F *
      (‖b‖ ^ finrank ℝ F / ((2⁻¹ : ℝ) • (A + A.adjoint)).det) := by
  refine (abs_det_le_negPart_div_finrank_pow_div_det_symmPart hT hA (c := -⟪b, v⟫)
    (by linarith)).trans ?_
  have hc : (-⟪b, v⟫)⁻ ≤ ‖b‖ * r := by
    rw [negPart_neg]
    exact (sup_le (le_abs_self _) (abs_nonneg _)).trans
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hv (norm_nonneg _)))
  calc ((-⟪b, v⟫)⁻ / finrank ℝ F) ^ finrank ℝ F / _ ≤
        (‖b‖ * r / finrank ℝ F) ^ finrank ℝ F / ((2⁻¹ : ℝ) • (A + A.adjoint)).det :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity)
          (div_le_div_of_nonneg_right hc (by positivity)) _)
          (ContinuousLinearMap.det_two_inv_smul_add_adjoint_pos hA).le
    _ = _ := by ring

omit [MeasurableSpace F] [BorelSpace F] in
/-- The integrand of the Aleksandrov measure estimate with a drift: under the hypotheses of
`abs_det_le_div_finrank_pow_mul_norm_pow_div_det` in positive dimension, `|det T|` is at most
`(r / n)ⁿ |b|ⁿ / det S` where `v ≠ 0`, and it vanishes where `v = 0`. -/
private theorem ofReal_abs_det_le_indicator {T A : F →L[ℝ] F} (hn : finrank ℝ F ≠ 0)
    (hT : (-T).IsPositive) (hA : ∀ ξ, ξ ≠ 0 → 0 < ⟪A ξ, ξ⟫) {b v : F} {r : ℝ}
    (hL : 0 ≤ traceCLM ℝ F (A ∘L T) + ⟪b, v⟫) (hv : ‖v‖ ≤ r) :
    ENNReal.ofReal |T.det| ≤ {w : F | w ≠ 0}.indicator (fun _ => ENNReal.ofReal
      ((r / finrank ℝ F) ^ finrank ℝ F *
        (‖b‖ ^ finrank ℝ F / ((2⁻¹ : ℝ) • (A + A.adjoint)).det))) v := by
  by_cases hv0 : v = 0
  · -- Without slope the determinant vanishes: this is the bound with `r = 0`.
    have h0 := abs_det_le_div_finrank_pow_mul_norm_pow_div_det hT hA hL (r := 0) (by simp [hv0])
    rw [zero_div, zero_pow hn, zero_mul, abs_nonpos_iff] at h0
    simp [h0]
  rw [indicator_of_mem hv0]
  exact ENNReal.ofReal_le_ofReal (abs_det_le_div_finrank_pow_mul_norm_pow_div_det hT hA hL hv)

omit [MeasurableSpace F] [BorelSpace F] in
/-- For `ū` differentiable on an open set `Ω`, the points of `Ω` at which `ū` is touched from above
on `Ω` by an affine function with slope in `closedBall 0 r` are the contact points with
`‖∇ū‖ ≤ r`: there the supporting slope is the gradient. -/
private theorem setOf_forall_le_add_inner_subset_upperContactSet_inter (hdiff : ContDiffOn ℝ 1 ū Ω)
    (r : ℝ) :
    {y | y ∈ Ω ∧ ∃ q ∈ Metric.closedBall (0 : F) r, ∀ z ∈ Ω, ū z ≤ ū y + ⟪q, z - y⟫} ⊆
      upperContactSet ū Ω ∩ ∇ ū ⁻¹' Metric.closedBall 0 r := fun y ⟨hyΩ, q, hq, hsupp⟩ => by
  have hqy : q = ∇ ū y := eq_gradient_of_forall_le (Ω.isOpen.mem_nhds hyΩ)
    ((hdiff.differentiableOn one_ne_zero y hyΩ).differentiableAt (Ω.isOpen.mem_nhds hyΩ)) hsupp
  refine ⟨mem_upperContactSet.2 ⟨hyΩ, q, hsupp⟩, ?_⟩
  rwa [mem_preimage, ← hqy]

open Metric in
/-- The measure estimate with a drift, for one radius: under the hypotheses of
`TauCeti.PDE.le_of_traceCLM_comp_iteratedGradient_add_inner_nonneg_le_frontier`, for
`0 ≤ r ≤ (ū x - m) / diam Ω`, `|B(0, r)| ≤ (r / n)ⁿ ∫ |b|ⁿ / det S` over the points of `Ω` where
`∇u ≠ 0` and `|∇u| ≤ r`. -/
private theorem volume_ball_le_ofReal_mul_setLIntegral_of_add_inner_nonneg
    (hΩb : Bornology.IsBounded (Ω : Set F)) (hp : p = finrank ℝ F) (u : Wkp volume Ω p 2)
    (hcont : ContinuousOn ū (closure Ω)) (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū)
    (hdiff : ContDiffOn ℝ 1 ū Ω)
    (hA : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫) {b : F → F}
    (hL : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ traceCLM ℝ F (A x ∘L Wkp.iteratedGradient 1 u x) +
      ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫)
    (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ (ū x - m) / diam (Ω : Set F)) :
    volume (ball (0 : F) r) ≤ ENNReal.ofReal ((r / finrank ℝ F) ^ finrank ℝ F) *
      ∫⁻ y in {y | Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y ≠ 0 ∧
        ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y‖ ≤ r},
        ENNReal.ofReal (‖b y‖ ^ finrank ℝ F / ((2⁻¹ : ℝ) • (A y + (A y).adjoint)).det)
        ∂volume.restrict Ω := by
  have hn : finrank ℝ F ≠ 0 := Nat.one_le_iff_ne_zero.1 (one_le_finrank_of_eq hp)
  set G : F → F := fun y => Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y
  set D := {y | G y ≠ 0 ∧ ‖G y‖ ≤ r}
  set h : F → ℝ≥0∞ := fun y => ENNReal.ofReal ((r / finrank ℝ F) ^ finrank ℝ F *
    (‖b y‖ ^ finrank ℝ F / ((2⁻¹ : ℝ) • (A y + (A y).adjoint)).det))
  have hGm : StronglyMeasurable G := Lp.stronglyMeasurable _
  have hDm : MeasurableSet D := measurableSet_setOf_ne_zero_and_norm_le hGm r
  -- The weak gradient is the classical gradient of the `C¹` representative.
  have hG : G =ᵐ[volume.restrict Ω] ∇ ū := by
    simpa only [iteratedGradientChain_zero] using
      Wkp.iteratedGradient_ae_eq_of_contDiffOn 0 (Wkp.lowerOrder 1 u) (f := ū)
        (by simpa using hdiff) (by simpa only [Wkp.value_succ] using hū)
  -- The contact points with slope of norm at most `r` lie in the measurable set `T`.
  set T := upperContactSet ū Ω ∩ ∇ ū ⁻¹' closedBall 0 r
  have hTm : MeasurableSet T :=
    (measurableSet_upperContactSet Ω.isOpen hdiff).inter
      (measurable_gradient ū measurableSet_closedBall)
  have hTΩ : T ⊆ Ω := fun y hy => upperContactSet_subset hy.1
  have hsub {P : F → Prop} (h : ∀ᵐ y ∂volume.restrict Ω, P y) : ∀ᵐ y ∂volume.restrict T, P y :=
    ae_restrict_of_ae_restrict_of_subset hTΩ h
  refine (addHaar_ball_le_lintegral_abs_det_iteratedGradient_of_le hΩb hp u hcont hū hm hx
    hr).trans ((lintegral_mono_set
      (setOf_forall_le_add_inner_subset_upperContactSet_inter hdiff r)).trans ?_)
  calc _ ≤ ∫⁻ y in T, D.indicator h y := by
        refine lintegral_mono_ae ?_
        filter_upwards [hsub hA, hsub hL, hsub hG, ae_restrict_mem hTm] with y hAy hLy hGy hyT
        have hGr : ‖G y‖ ≤ r := by
          have := hyT.2
          rwa [mem_preimage, mem_closedBall_zero_iff, ← hGy] at this
        by_cases hpos : (-(Wkp.iteratedGradient 1 u y : F →L[ℝ] F)).IsPositive
        · rw [indicator_of_mem hpos]
          refine (ofReal_abs_det_le_indicator hn hpos hAy hLy hGr).trans_eq ?_
          by_cases hG0 : G y = 0
          · rw [indicator_of_notMem fun h : G y ≠ 0 => h hG0,
              indicator_of_notMem fun hy : y ∈ D => hy.1 hG0]
          · rw [indicator_of_mem hG0, indicator_of_mem (⟨hG0, hGr⟩ : y ∈ D)]
        · rw [indicator_of_notMem hpos]
          exact zero_le
    _ ≤ ∫⁻ y in Ω, D.indicator h y := lintegral_mono_set hTΩ
    _ = ∫⁻ y in D, h y ∂volume.restrict Ω := lintegral_indicator hDm _
    _ = _ := by
        simp_rw [h, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (r / finrank ℝ F) ^ finrank ℝ F)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

open Topology in
/-- Under a finite integral `∫_Ω g`, the integrals of `g` over the sets where `G ≠ 0` and
`‖G‖ ≤ R / (k + 1)` tend to `0`: these sets decrease to the empty set. -/
private theorem tendsto_setLIntegral_setOf_ne_zero_and_norm_le {G : F → F}
    (hG : StronglyMeasurable G) {g : F → ℝ≥0∞} (hg : ∫⁻ y in Ω, g y ≠ ∞) {R : ℝ} (hR : 0 ≤ R) :
    Filter.Tendsto (fun k : ℕ => ∫⁻ y in {y | G y ≠ 0 ∧ ‖G y‖ ≤ R / (k + 1)}, g y
      ∂volume.restrict Ω) Filter.atTop (𝓝 0) := by
  set D : ℕ → Set F := fun k => {y | G y ≠ 0 ∧ ‖G y‖ ≤ R / (k + 1)}
  set ν := (volume.restrict (Ω : Set F)).withDensity g
  have hν (s : Set F) : ν s = ∫⁻ y in s, g y ∂volume.restrict Ω := withDensity_apply' _ s
  have hanti : Antitone D := fun i j hij y hy =>
    ⟨hy.1, hy.2.trans (div_le_div_of_nonneg_left hR (by positivity) (by gcongr))⟩
  have hinter : ⋂ k, D k = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun y hy => ?_
    rw [mem_iInter] at hy
    have hlim : Filter.Tendsto (fun k : ℕ => R / (k + 1)) Filter.atTop (𝓝 0) :=
      ((tendsto_const_div_atTop_nhds_zero_nat R).comp (Filter.tendsto_add_atTop_nat 1)).congr
        fun k => by simp
    obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds (norm_pos_iff.2 (hy 0).1))).exists
    exact (hy k).2.not_gt hk
  have hfin : ν (D 0) ≠ ∞ :=
    ne_top_of_le_ne_top (by rwa [hν, Measure.restrict_univ]) (measure_mono (subset_univ _))
  have h := tendsto_measure_iInter_atTop (s := D)
    (fun k => (measurableSet_setOf_ne_zero_and_norm_le hG _).nullMeasurableSet) hanti
    ⟨0, hfin⟩
  rw [hinter, measure_empty] at h
  simpa only [Function.comp_def, hν] using h

open Filter Metric Topology in
/-- **The weak maximum principle for strong subsolutions with a drift** (Gilbarg–Trudinger,
Theorem 9.1 with `c = 0` and `f = 0`, for `C¹` functions). Let `Ω` be a bounded open subset of a
real inner product space of dimension `n`, and let `u ∈ W^{2,n}(Ω)` have a representative `ū`
continuous on `closure Ω` and `C¹` in `Ω`. Let `A(x)` be positive definite,
`⟪A(x) ξ, ξ⟫ > 0` for `ξ ≠ 0`, for almost every `x ∈ Ω`, with symmetric part
`S(x) = (A(x) + A(x)†) / 2`, and let the drift `b` satisfy `∫_Ω |b|ⁿ / det S < ∞`, that is
`|b| / D* ∈ Lⁿ(Ω)` for `D* = (det S)^{1/n}`. If `tr (A ∘ D²u) + ⟪b, ∇u⟫ ≥ 0` almost everywhere on
`Ω` and `ū ≤ m` on `frontier Ω`, then `ū ≤ m` on `Ω`. -/
theorem le_of_traceCLM_comp_iteratedGradient_add_inner_nonneg_le_frontier
    (hΩb : Bornology.IsBounded (Ω : Set F)) (hp : p = finrank ℝ F) (u : Wkp volume Ω p 2)
    (hcont : ContinuousOn ū (closure Ω)) (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū)
    (hdiff : ContDiffOn ℝ 1 ū Ω)
    (hA : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫) {b : F → F}
    (hb : ∫⁻ x in Ω, ENNReal.ofReal (‖b x‖ ^ finrank ℝ F /
      ((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det) ≠ ∞)
    (hL : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ traceCLM ℝ F (A x ∘L Wkp.iteratedGradient 1 u x) +
      ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫)
    (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) : ū x ≤ m := by
  by_contra! hxm
  set n := finrank ℝ F
  have hn : 1 ≤ n := one_le_finrank_of_eq hp
  have : Nontrivial F := Module.nontrivial_of_finrank_pos hn
  set I : ℕ → ℝ≥0∞ := fun k => ∫⁻ y in {y | Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y ≠ 0 ∧
    ‖Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) y‖ ≤ (ū x - m) / diam (Ω : Set F) / (k + 1)},
    ENNReal.ofReal (‖b y‖ ^ n / ((2⁻¹ : ℝ) • (A y + (A y).adjoint)).det) ∂volume.restrict Ω
  -- Along `r k = R / (k + 1) → 0`, `R = (ū x - m) / diam Ω`, the integrals `I k` of `|b|ⁿ / det S`
  -- over `{∇u ≠ 0, |∇u| ≤ r k}` tend to `0`, while `|B(0, 1)| ≤ n⁻ⁿ I k` for every `k`.
  have hR : 0 < (ū x - m) / diam (Ω : Set F) := div_pos (sub_pos.2 hxm)
    (diam_pos (infinite_of_mem_nhds x (Ω.isOpen.mem_nhds hx)).nontrivial hΩb)
  have hlim : Tendsto I atTop (𝓝 0) :=
    tendsto_setLIntegral_setOf_ne_zero_and_norm_le (Lp.stronglyMeasurable _) hb hR.le
  have hV (k : ℕ) : volume (ball (0 : F) 1) ≤ ENNReal.ofReal ((1 / n) ^ n) * I k := by
    have hr0 : 0 < (ū x - m) / diam (Ω : Set F) / (k + 1) := by positivity
    set r := (ū x - m) / diam (Ω : Set F) / (k + 1)
    have h := volume_ball_le_ofReal_mul_setLIntegral_of_add_inner_nonneg hΩb hp u hcont hū hdiff
      hA hL hm hx hr0.le (div_le_self hR.le (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]))
    -- Rescale: `(r / n)ⁿ = rⁿ (1 / n)ⁿ` and `|B(0, r)| = rⁿ |B(0, 1)|`, then cancel `rⁿ`.
    have hpow : ENNReal.ofReal ((r / n) ^ n) =
        ENNReal.ofReal (r ^ n) * ENNReal.ofReal ((1 / n) ^ n) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      ring_nf
    rw [Measure.addHaar_ball _ _ hr0.le, hpow, mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (by positivity)).ne'
      ENNReal.ofReal_ne_top).1 h
  have h0 : volume (ball (0 : F) 1) ≤ 0 := by
    have := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.ofReal_ne_top (r := (1 / n) ^ n)))
    rw [mul_zero] at this
    exact ge_of_tendsto this (Eventually.of_forall hV)
  exact (measure_ball_pos volume (0 : F) one_pos).ne' (le_antisymm h0 zero_le)

/-- **The weak maximum principle for strong subsolutions with a drift and a zeroth-order term**
(Gilbarg–Trudinger, Theorem 9.1 with `f = 0`, for `C¹` functions). Let `Ω` be a bounded open subset
of a real inner product space of dimension `n`, and let `u ∈ W^{2,n}(Ω)` have a representative `ū`
continuous on `closure Ω` and `C¹` in `Ω`. Let `A(x)` be positive definite, `⟪A(x) ξ, ξ⟫ > 0` for
`ξ ≠ 0`, and `c(x) ≤ 0`, for almost every `x ∈ Ω`, and let the drift `b` satisfy
`∫_Ω |b|ⁿ / det S < ∞` for the symmetric part `S = (A + A†) / 2` of `A`. If
`tr (A ∘ D²u) + ⟪b, ∇u⟫ + c u ≥ 0` almost everywhere on `Ω` and `ū ≤ m` on `frontier Ω` with
`m ≥ 0`, then `ū ≤ m` on `Ω`. -/
theorem le_of_traceCLM_comp_iteratedGradient_add_inner_add_mul_nonneg_le_frontier
    (hΩb : Bornology.IsBounded (Ω : Set F)) (hp : p = finrank ℝ F) (u : Wkp volume Ω p 2)
    (hcont : ContinuousOn ū (closure Ω)) (hū : Wkp.value 2 u =ᵐ[volume.restrict Ω] ū)
    (hdiff : ContDiffOn ℝ 1 ū Ω)
    (hA : ∀ᵐ x ∂volume.restrict Ω, ∀ ξ, ξ ≠ 0 → 0 < ⟪A x ξ, ξ⟫) {b : F → F}
    (hb : ∫⁻ x in Ω, ENNReal.ofReal (‖b x‖ ^ finrank ℝ F /
      ((2⁻¹ : ℝ) • (A x + (A x).adjoint)).det) ≠ ∞) {c : F → ℝ}
    (hc : ∀ᵐ x ∂volume.restrict Ω, c x ≤ 0)
    (hL : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ traceCLM ℝ F (A x ∘L Wkp.iteratedGradient 1 u x) +
      ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫ + c x * Wkp.value 2 u x)
    (hm0 : 0 ≤ m) (hm : ∀ z ∈ frontier (Ω : Set F), ū z ≤ m) {x : F} (hx : x ∈ Ω) : ū x ≤ m := by
  by_contra! hxm
  -- Apply the case `c = 0` on `V = {y ∈ Ω | m < ū y}`, where `c u ≤ 0`.
  obtain ⟨V, hVΩ, hxV, hVm, hcV⟩ :=
    exists_le_and_mem_and_le_frontier_and_mul_value_nonpos hcont hū hc hm0 hm hx hxm
  have hVsub {P : F → Prop} (h : ∀ᵐ y ∂volume.restrict Ω, P y) :
      ∀ᵐ y ∂volume.restrict (V : Set F), P y :=
    ae_restrict_of_ae_restrict_of_subset hVΩ h
  have hgrad : Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 (Wkp.restrictL hVΩ 2 u)) =ᵐ[volume.restrict
      (V : Set F)] Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) := by
    rw [Wkp.lowerOrder_restrictL]
    exact Wkp.iteratedGradient_restrictL_ae hVΩ 0 _
  refine (le_of_traceCLM_comp_iteratedGradient_add_inner_nonneg_le_frontier (hΩb.subset hVΩ) hp
    (Wkp.restrictL hVΩ 2 u) (hcont.mono (closure_mono hVΩ))
    ((Wkp.value_restrictL_ae hVΩ 2 u).trans (hVsub hū)) (hdiff.mono hVΩ) (hVsub hA)
    (ne_top_of_le_ne_top hb (lintegral_mono_set hVΩ)) ?_ hVm hxV).not_gt hxm
  filter_upwards [hVsub hL, hcV, Wkp.iteratedGradient_restrictL_ae hVΩ 1 u, hgrad]
    with y hy hcy hD hG
  rw [hD, hG]
  linarith

end Drift

end PDE

end TauCeti
