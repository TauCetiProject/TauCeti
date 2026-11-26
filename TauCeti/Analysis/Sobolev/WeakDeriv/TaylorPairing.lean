/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.Taylor.Pairing.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.IntegrationByParts
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Weak-derivative commutation for Taylor-monomial pairings

If `u` has weak directional derivative `u'` along `h` on `Ω`, differentiating the degree-`(j + 1)`
orthonormal-basis Taylor-monomial pairing of `u` at `x` along `h` transfers one derivative onto `u`
via weak integration by parts, yielding `-(j + 1)` times the degree-`j` pairing of `u'`
(`TauCeti.HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul`).
-/

public section

noncomputable section

namespace TauCeti

open _root_.MeasureTheory TopologicalSpace
open scoped ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]

private theorem sum_slot_setIntegral_iteratedFDerivAlong_eq_neg
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) {j : ℕ} {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω)
    (x : E) (p : Fin (j + 1)) :
    (∑ I : Fin (j + 1) → ι, ⟪b (I p), h⟫_ℝ * ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
      (fun z => (∏ l ∈ Finset.univ.erase p, ⟪b (I l), x - z⟫_ℝ) * φ z) y * u y ∂μ) =
      -∑ J : Fin j → ι, ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y * u' y ∂μ := by
  rw [← (p.insertNthEquiv fun _ : Fin (j + 1) => ι).sum_comp]
  simp only [Fintype.sum_prod_type, Fin.insertNthEquiv_apply]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  let qg : E → ℝ := fun z => ∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ
  let g : E → ℝ := iteratedFDerivAlong ℝ (List.ofFn (b ∘ J)) (fun z => qg z * φ z)
  have hqg : ContDiff ℝ (j + 1) qg := (contDiff_prod fun l _ =>
    (innerSL ℝ (b (J l))).contDiff.comp (contDiff_const.sub contDiff_id)).of_le le_top
  have hg : ContDiff ℝ 1 g :=
    (hqg.mul hφ).iteratedFDerivAlong (List.ofFn (b ∘ J)) (by simp [add_comm])
  have hgc : HasCompactSupport g := hφc.mul_left.iteratedFDerivAlong ℝ (List.ofFn (b ∘ J))
  have hgs : tsupport g ⊆ Ω :=
    ((tsupport_iteratedFDerivAlong_subset ℝ _ _).trans tsupport_mul_subset_right).trans hφs
  have hcomp : ∀ i : ι, b ∘ p.insertNth (α := fun _ => ι) i J = p.insertNth (b i) (b ∘ J) :=
    fun i => funext (p.succAboveCases (by simp) fun _ => by simp)
  have hstep : ∀ i y, iteratedFDerivAlong ℝ (List.ofFn (b ∘ p.insertNth (α := fun _ => ι) i J))
      (fun z => (∏ l ∈ Finset.univ.erase p,
        ⟪b (p.insertNth (α := fun _ => ι) i J l), x - z⟫_ℝ) * φ z) y = fderiv ℝ g y (b i) :=
    fun i y => by
      simp_rw [hcomp i, ← Function.comp_apply (f := b), hcomp i]
      exact iteratedFDerivAlong_insertNth_prod_inner_sub_erase_mul p (b i) (b ∘ J) hφ x y
  have hint_i : ∀ i : ι, IntegrableOn (fun y => ⟪b i, h⟫_ℝ * fderiv ℝ g y (b i) * u y) Ω μ :=
    fun i => by
      simpa only [smul_eq_mul, mul_assoc] using
        ((hu.locallyIntegrableOn.integrable_smul_left_of_hasCompactSupport
          (((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousOn)
          (hgc.fderiv_apply ℝ (b i))
          ((tsupport_fderiv_apply_subset ℝ (b i)).trans hgs)).const_mul ⟪b i, h⟫_ℝ).integrableOn
  simp_rw [Fin.insertNth_apply_same, hstep, ← integral_const_mul, ← mul_assoc]
  rw [← integral_finsetSum _ fun i _ => hint_i i, ← hu.setIntegral_fderiv_mul_eq_neg hg hgc hgs]
  refine setIntegral_congr_fun Ω.isOpen.measurableSet fun y _ => ?_
  rw [← Finset.sum_mul]; congr 1
  conv_rhs => rw [← b.sum_repr' h, map_sum]
  exact Finset.sum_congr rfl fun _ _ => by rw [map_smul, smul_eq_mul]

/-- **Single-step weak derivative commutation for Taylor-monomial pairings.** -/
theorem HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) (j : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (x : E) :
    fderiv ℝ (fun x' => ∑ I : Fin (j + 1) → ι, ∫ y in Ω, iteratedFDeriv ℝ (j + 1)
      (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x h =
      -(j + 1 : ℝ) * ∑ J : Fin j → ι, ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * u' y ∂μ := by
  have hconv : ∀ {k : ℕ} {ψ : E → ℝ}, ContDiff ℝ k ψ → ∀ (w : E → ℝ) (I : Fin k → ι) (x' : E),
      ∫ y in Ω, iteratedFDeriv ℝ k (fun z => (∏ l, ⟪b (I l), x' - z⟫_ℝ) * ψ z) y (b ∘ I) * w y ∂μ =
      ∫ y in Ω, iteratedFDerivAlong ℝ (List.ofFn (b ∘ I))
        (fun z => (∏ l, ⟪b (I l), x' - z⟫_ℝ) * ψ z) y * w y ∂μ := fun hψ w I x' =>
    setIntegral_iteratedFDeriv_prod_inner_sub_mul_eq_iteratedFDerivAlong (b ∘ I) hψ w x'
  simp_rw [hconv hφ u, hconv (hφ.of_le (by exact_mod_cast Nat.le_succ j)) u']
  have hsum_d := HasFDerivAt.fun_sum (x := x)
    fun I (_ : I ∈ (Finset.univ : Finset (Fin (j + 1) → ι))) =>
      (((contDiff_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul (m := 1) Finset.univ
        (fun l => b (I l)) hφ hφc hφs (List.ofFn (b ∘ I)) (by simp)
        hu.locallyIntegrableOn).differentiable one_ne_zero) x).hasFDerivAt
  rw [hsum_d.fderiv, FunLike.coe_sum, Finset.sum_apply, Finset.sum_congr rfl fun I _ =>
    fderiv_setIntegral_iteratedFDerivAlong_prod_inner_sub_mul Finset.univ (fun l => b (I l))
      hφ hφc hφs (List.ofFn (b ∘ I)) (by simp) hu.locallyIntegrableOn x h, Finset.sum_comm]
  simp_rw [sum_slot_setIntegral_iteratedFDerivAlong_eq_neg b hu hφ hφc hφs x]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- Constant-multiple form of
`TauCeti.HasWeakLineDerivOn.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul`. -/
theorem HasWeakLineDerivOn.fderiv_const_mul_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) {μ : Measure E} {Ω : Opens E}
    {u u' : E → ℝ} {h : E} (hu : HasWeakLineDerivOn μ Ω u u' h) (c : ℝ) (j : ℕ) {φ : E → ℝ}
    (hφ : ContDiff ℝ (j + 1) φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ω) (x : E) :
    fderiv ℝ (fun x' => c * ∑ I : Fin (j + 1) → ι, ∫ y in Ω, iteratedFDeriv ℝ (j + 1)
      (fun z => (∏ l : Fin (j + 1), ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x h =
      c * -(j + 1 : ℝ) * ∑ J : Fin j → ι, ∫ y in Ω, iteratedFDeriv ℝ j
        (fun z => (∏ l : Fin j, ⟪b (J l), x - z⟫_ℝ) * φ z) y (b ∘ J) * u' y ∂μ := by
  have hdiff : DifferentiableAt ℝ (fun x' => ∑ I : Fin (j + 1) → ι, ∫ y in Ω,
      iteratedFDeriv ℝ (j + 1) (fun z => (∏ l, ⟪b (I l), x' - z⟫_ℝ) * φ z) y (b ∘ I) * u y ∂μ) x :=
    DifferentiableAt.fun_sum fun I _ =>
      ((contDiff_setIntegral_iteratedFDeriv_prod_inner_sub_mul (m := 1) (b ∘ I) hφ hφc hφs
        hu.locallyIntegrableOn).differentiable one_ne_zero) x
  rw [(hdiff.hasFDerivAt.const_mul c).fderiv, smul_apply, smul_eq_mul,
    hu.fderiv_sum_setIntegral_iteratedFDeriv_prod_inner_sub_mul b j hφ hφc hφs x, mul_assoc]

end TauCeti
