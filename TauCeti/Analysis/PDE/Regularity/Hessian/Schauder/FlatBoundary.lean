/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Basic
import TauCeti.Analysis.Analytic.AffineHyperplane
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.PDE.Regularity.Boundary.Campanato
import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
import TauCeti.Analysis.Sobolev.W1p.HyperplaneReflection
import TauCeti.Topology.MetricSpace.Holder

/-!
# Schauder estimates up to a flat boundary for Poisson's equation

Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, and let `0 < α < 1`. This
file proves the `C^{2,α}` estimate up to the flat part of the boundary for classical solutions of
Poisson's equation with zero boundary values: if `u` is `C²` on an open set containing
`cthickening R S ∩ closure H`, for a bounded set `S` of the closed half-space, `u` vanishes on the
hyperplane `∂H`, and `Δu` is `α`-Hölder with constant `K` on `S_R ∩ H`, where `S_R` is the open
`R`-thickening of `S`, then `D²u` is `α`-Hölder on `S`, with constant

`C (K + R^{-(n+1)/2-α} ‖D²u‖_{L²(S_R ∩ H)})`,

where `C` depends only on `n` and `α`
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_laplacian_of_halfSpace`). The set `S` may
meet the hyperplane, and only the part of `S_R` in `H`, where the equation holds, enters the
constant. This is the boundary counterpart of the interior estimate
`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_laplacian`, and the estimate for the frozen
operator in the perturbation argument for the `C^{2,α}` estimate near a flat boundary portion.

## The argument

For a direction `e ⊥ ν`, the tangential derivative `∂ₑu` vanishes on the hyperplane, since `u`
does, and it solves `-Δ(∂ₑu) = -div ((Δu) e)` in `H`: moving `∂ₑ` onto the test function
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn`) and Green's identity
give `∫ ⟨∇∂ₑu, ∇φ⟩ = ∫ Δu ∂ₑφ`
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_inner_laplacian_smul`). The datum
`(Δu) e` is `α`-Hölder in `H`, but its tangential direction means that it has no Hölder continuous
odd reflection, which is why the flat-boundary estimate for divergence data with no condition on
the tangential part is the right input. A cutoff makes the extension of `∂ₑu` by zero across the
hyperplane an element of `H¹` with zero boundary values
(`TauCeti.W1p.exists_value_eq_zero_and_value_ae_eq`), and Campanato's estimate at a flat boundary
for divergence data, from `TauCeti.Analysis.PDE.Regularity.Boundary.Campanato`, makes `∇∂ₑu`
`α`-Hölder up to the hyperplane. Its `L²` term is controlled by `D²u` on `S_R ∩ H`.

This bounds every second derivative with at least one tangential direction. The normal one comes
from the equation: for an orthonormal basis `(bᵢ)` with `b₀ = ν / ‖ν‖`,
`D²u(b₀, b₀) = Δu - ∑_{i ≠ 0} D²u(bᵢ, bᵢ)`
(`OrthonormalBasis.norm_gradient_fderiv_sub_le_of_laplacian`). The estimate is first proved on
the points of `S_R/4` in `H`, and passes to `S` by continuity of `D²u`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_laplacian_of_halfSpace`: the Schauder
  estimate up to a flat boundary for `C²` solutions of Poisson's equation vanishing on the boundary
  hyperplane.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 4.4, Theorem 4.11 (the `C^{2,α}` estimate for Poisson's equation near a flat boundary
  portion on which the solution vanishes).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates up to a flat boundary
  by Campanato's method, applied to the tangential derivatives).
-/

public section

noncomputable section

open InnerProductSpace Laplacian LineDeriv MeasureTheory Metric Set TopologicalSpace
  TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal ENNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The odd reflection of a tangential derivative.** Let `u` be `C²` on an open set `U`, let `U₁`
be a bounded open set invariant under the reflection `ρ` in `∂H` with `closure (U₁ ∩ H) ⊆ U`, and
let `w₀ ∈ H¹(U₁)` vanish on `U₁ ∖ H` and represent `∂ₑu` on `U₁ ∩ H`, for a unit vector `e`. Then on
`U₁ ∩ H` the precise representative of the gradient of the odd reflection `w = w₀ - w₀ ∘ ρ` is the
classical gradient of `∂ₑu`, and `‖∇w‖_{L²(U₁)} ≤ 2 ‖D²u‖_{L²(U₁ ∩ H)}`. -/
private theorem eqOn_preciseRepresentative_gradient_and_norm_le {H U₁ : Opens E} {ν : E} {c₀ : ℝ}
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (hU₁ : MapsTo (hyperplaneReflection ν c₀) U₁ U₁) (hU₁b : Bornology.IsBounded (U₁ : Set E))
    {U : Set E} {u : E → ℝ} (hU : IsOpen U) (hu : ContDiffOn ℝ 2 u U)
    (hUH : closure ((U₁ ⊓ H : Opens E) : Set E) ⊆ U) {e : E} (he : ‖e‖ = 1) {w₀ : W1p volume U₁ 2}
    (hw₀0 : ∀ᵐ x ∂volume.restrict U₁, x ∉ H → W1p.value w₀ x = 0)
    (hval : W1p.value (W1p.restrictL (inf_le_left : U₁ ⊓ H ≤ U₁) w₀) =ᵐ[volume.restrict (U₁ ⊓ H)]
      fun x => fderiv ℝ u x e) :
    EqOn (preciseRepresentative volume (W1p.gradient
        (w₀ - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU₁ w₀) : E → E))
      (∇ fun x => fderiv ℝ u x e) (U₁ ⊓ H) ∧
    ‖W1p.gradient (w₀ - W1p.compHyperplaneReflectionL ENNReal.ofNat_ne_top ν c₀ hU₁ w₀)‖ ≤
      2 * (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (U₁ ⊓ H : Opens E))).toReal := by
  set V₁ : Opens E := U₁ ⊓ H
  have hV₁U : (V₁ : Set E) ⊆ U := subset_closure.trans hUH
  have hd1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ u x e) V₁ :=
    ((hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const).mono hV₁U
  have hgradr := W1p.gradient_ae_eq_of_contDiffOn _ hd1 hval
  refine ⟨eqOn_preciseRepresentative_of_continuousOn V₁.isOpen
    ((W1p.locallyIntegrableOn_gradient _).mono_set inter_subset_left)
    ((W1p.gradient_sub_compHyperplaneReflectionL_ae ENNReal.ofNat_ne_top hν hH hU₁ hw₀0).trans
      ((W1p.gradient_restrictL_ae inf_le_left w₀).symm.trans hgradr))
    ((InnerProductSpace.toDual ℝ E).symm.continuous.comp_continuousOn
      (hd1.continuousOn_fderiv_of_isOpen V₁.isOpen le_rfl)), ?_⟩
  -- `‖∇w‖² ≤ 2 ‖∇(w₀|_{V₁})‖²`, and `∇(w₀|_{V₁}) = ∇∂ₑu` is bounded by `D²u`.
  have hfin : eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (V₁ : Set E)) ≠ ⊤ :=
    (((ContinuousOn.continuousOn_iteratedFDeriv hu hU (by norm_num)).mono hUH
      ).memLp_restrict_of_subset_isCompact (hU₁b.subset inter_subset_left).isCompact_closure
      V₁.isOpen.measurableSet subset_closure 2).eLpNorm_ne_top
  have hnr := norm_gradient_le_toReal_eLpNorm_iteratedFDeriv_two he hV₁U
    (fun x hx => ((hu.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)
      ).differentiableAt one_ne_zero) hgradr hfin
  have hsq := W1p.norm_gradient_sub_compHyperplaneReflectionL_sq_le hν hH hU₁
    hU₁b.measure_lt_top.ne hw₀0
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) (hsq.trans ?_)
  nlinarith [pow_le_pow_left₀ (norm_nonneg _) hnr 2]

/-- The bookkeeping of the constants in `exists_holderOnWith_gradient_fderiv_of_inner_eq_zero`:
the estimate is applied at the radius `R / 4`, with `L²` term `g ≤ 2 M`. -/
private theorem mul_add_div_four_rpow_neg_mul_le {C₀ K R M g β : ℝ} (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hR : 0 < R) (hβ : 0 ≤ β) (hg : g ≤ 2 * M) :
    C₀ * (K + (R / 4) ^ (-β) * g) ≤ C₀ * 4 ^ β * 2 * (K + R ^ (-β) * M) := by
  have h4 : (1 : ℝ) ≤ 4 ^ β := Real.one_le_rpow (by norm_num) hβ
  have hrβ : (R / 4) ^ (-β) = 4 ^ β * R ^ (-β) := by
    rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      div_inv_eq_mul, mul_comm]
  have h1 : K + 4 ^ β * R ^ (-β) * g ≤ 4 ^ β * 2 * (K + R ^ (-β) * M) :=
    calc K + 4 ^ β * R ^ (-β) * g
        ≤ 4 ^ β * 2 * K + 4 ^ β * R ^ (-β) * (2 * M) :=
          add_le_add (le_mul_of_one_le_left hK (by linarith))
            (mul_le_mul_of_nonneg_left hg (by positivity))
      _ = 4 ^ β * 2 * (K + R ^ (-β) * M) := by ring
  rw [hrβ]
  calc C₀ * (K + 4 ^ β * R ^ (-β) * g) ≤ C₀ * (4 ^ β * 2 * (K + R ^ (-β) * M)) :=
        mul_le_mul_of_nonneg_left h1 hC₀
    _ = C₀ * 4 ^ β * 2 * (K + R ^ (-β) * M) := by ring

/-- **The tangential derivative extended by zero.** Let `u` be `C²` on an open set `U` containing
`cthickening R S ∩ closure H`, vanishing on the part of `∂H` in `U`, and let `e ⊥ ν`. On every open
`U₁` whose points in `H` lie in `S_{R/2}` there is `w₀ ∈ H¹(U₁)` vanishing on `U₁ ∖ H` and equal to
`∂ₑu` on `U₁ ∩ H`. -/
private theorem exists_w1p_fderiv_value_eq_zero_and_value_ae_eq {H : Opens E} {ν e : E} {c₀ R : ℝ}
    (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {U S : Set E} {u : E → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) (hS : Bornology.IsBounded S) (hR : 0 < R)
    (hSU : cthickening R S ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U) (hu0 : ∀ x ∈ U, ⟪x, ν⟫_ℝ = c₀ → u x = 0)
    (heν : ⟪e, ν⟫_ℝ = 0) (U₁ : Opens E) (hU₁ : (U₁ : Set E) ∩ H ⊆ thickening (R / 2) S) :
    ∃ w₀ : W1p volume U₁ 2, (∀ᵐ x ∂volume.restrict U₁, x ∉ H → W1p.value w₀ x = 0) ∧
      W1p.value (W1p.restrictL (inf_le_left : U₁ ⊓ H ≤ U₁) w₀) =ᵐ[volume.restrict
        (U₁ ⊓ H : Opens E)] fun x => fderiv ℝ u x e := by
  -- `∂ₑu` vanishes on the hyperplane, since `u` does and `e` is tangential.
  have hd0 : ∀ x ∈ U, ⟪x, ν⟫_ℝ = c₀ → fderiv ℝ u x e = 0 := fun x hx hxc =>
    ((hu.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
      ).fderiv_apply_eq_zero_of_eventually_eq_zero (ℓ := innerSL ℝ ν) (b := c₀)
      (by simpa [real_inner_comm] using hxc)
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy hyc =>
        hu0 y hy (by simpa [real_inner_comm] using hyc))
      (by simpa [real_inner_comm] using heν)
  obtain ⟨w₀, hw₀0, hw₀⟩ := W1p.exists_value_eq_zero_and_value_ae_eq (mu := volume) (p := 2)
    ENNReal.ofNat_ne_top hH hU
    ((hu.fderiv_of_isOpen hU (by norm_num)).clm_apply contDiffOn_const) hd0
    (V := thickening (3 * R / 4) S) isOpen_thickening hS.thickening
    (subset_trans (inter_subset_inter_left _ ((closure_thickening_subset_cthickening _ S).trans
      (cthickening_mono (by linarith) S))) hSU)
    hS.thickening.isCompact_closure
    ((closure_thickening_subset_cthickening _ S).trans
      (cthickening_subset_thickening' (by positivity) (by linarith) S))
    U₁ (hU₁.trans subset_closure)
  exact ⟨w₀, hw₀0, (W1p.value_restrictL_ae inf_le_left w₀).trans hw₀⟩

/-- **Tangential second derivatives up to a flat boundary.** Under the hypotheses of
`exists_holderOnWith_iteratedFDeriv_two_of_laplacian_of_halfSpace`, for every unit vector `e`
orthogonal to `ν`, the gradient of `∂ₑu` is `α`-Hölder on the points of `S_{R/4}` in `H`, with
constant `C (K + R^{-(n+1)/2-α} ‖D²u‖_{L²(S_R ∩ H)})`. -/
private theorem exists_holderOnWith_gradient_fderiv_of_inner_eq_zero {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U S : Set E} {u : E → ℝ} {ν : E} {c₀ : ℝ} {K : ℝ≥0} {R : ℝ},
      ν ≠ 0 → IsOpen U → ContDiffOn ℝ 2 u U → Bornology.IsBounded S →
      0 < R → cthickening R S ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U →
      (∀ x ∈ U, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      HolderOnWith K α (Δ u) (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
      ∀ e : E, ‖e‖ = 1 → ⟪e, ν⟫_ℝ = 0 →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 u) 2
            (volume.restrict (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))).toReal)).toNNReal α
          (∇ fun z => fderiv ℝ u z e) (thickening (R / 4) S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) := by
  obtain ⟨C₀, hC₀, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_sub_compHyperplaneReflectionL_of_divergence
      hα hα1 (n := n)
  refine ⟨C₀ * 4 ^ (((n : ℝ) + 1) / 2 + α) * 2, by positivity,
    fun {U S u ν c₀ K R} hν hU hu hS hR hSU hu0 hK e he heν => ?_⟩
  set H : Opens E := ⟨{x | c₀ < ⟪x, ν⟫_ℝ},
    isOpen_lt continuous_const (continuous_id.inner continuous_const)⟩
  have hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ := fun x => Iff.rfl
  -- The points of `S' = S_{R/4} ∩ closure H` and the reflection-invariant `U₁ ⊇ (S')_{R/4}`, whose
  -- points in `H` lie in `S_{R/2}`.
  set S' := thickening (R / 4) S ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ}
  obtain ⟨U₁, hU₁, hTU₁, hU₁T, hU₁b⟩ := exists_opens_mapsTo_hyperplaneReflection (r := R / 4)
    (hS.thickening.subset inter_subset_left) fun x (hx : x ∈ S') => hx.2
  have hTS : thickening (R / 4) S' ⊆ thickening (R / 2) S :=
    (thickening_subset_of_subset _ inter_subset_left).trans
      ((thickening_thickening_subset _ _ S).trans
        (thickening_mono (by linarith) S))
  have hU₁H : (U₁ : Set E) ∩ H ⊆ thickening (R / 2) S := hU₁T.trans hTS
  have hR2 : thickening (R / 2) S ⊆ thickening R S := thickening_mono (by linarith) S
  -- Closures of the parts in `H` of subsets of `S_R` lie in `U`.
  have hcl : ∀ {A : Set E}, A ⊆ thickening R S → closure (A ∩ H) ⊆ U := fun hA =>
    (closure_inter_subset_inter_closure _ _).trans (subset_trans (inter_subset_inter
      ((closure_mono hA).trans (closure_thickening_subset_cthickening R S))
      (closure_setOf_lt_inner_subset ν c₀)) hSU)
  have hUH : closure ((U₁ ⊓ H : Opens E) : Set E) ⊆ U :=
    (closure_mono (s := ((U₁ ⊓ H : Opens E) : Set E)) (t := thickening (R / 2) S ∩ H)
      fun x hx => ⟨hU₁H hx, hx.2⟩).trans (hcl hR2)
  obtain ⟨w₀, hw₀0, hval⟩ := exists_w1p_fderiv_value_eq_zero_and_value_ae_eq hH hU hu hS hR hSU
    hu0 heν U₁ hU₁H
  -- It solves `-Δ(∂ₑu) = -div ((Δu) e)` in `U₁ ∩ H`, with an `α`-Hölder datum.
  have heq := energyFormH1_ofTestFunctionₗ_eq_setIntegral_inner_laplacian_smul hU hu
    (hU₁b.subset inter_subset_left) hUH hval
  have hG : HolderOnWith K α (fun x => Δ u x • e) (thickening (R / 4) S' ∩ H) :=
    HolderOnWith.of_dist_le fun x hx y hy => by
      rw [dist_eq_norm, ← sub_smul, norm_smul, he, mul_one, ← dist_eq_norm]
      exact (hK.mono (t := thickening (R / 4) S' ∩ H) fun z hz =>
        ⟨hR2 (hTS hz.1), hz.2⟩).dist_le hx hy
  have hmain := h hν hH hU₁ hw₀0 heq hG (fun x hx => hx.2) (by positivity) hTU₁
  obtain ⟨hprec, hnorm⟩ :=
    eqOn_preciseRepresentative_gradient_and_norm_le hν hH hU₁ hU₁b hU hu hUH he hw₀0 hval
  -- The `L²` term on `U₁ ∩ H` is at most that on `S_R ∩ H`.
  have hMV : (eLpNorm (iteratedFDeriv ℝ 2 u) 2 (volume.restrict (U₁ ⊓ H : Opens E))).toReal ≤
      (eLpNorm (iteratedFDeriv ℝ 2 u) 2
        (volume.restrict (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))).toReal :=
    ENNReal.toReal_mono (((ContinuousOn.continuousOn_iteratedFDeriv hu hU (by norm_num)).mono
      (hcl subset_rfl)).memLp_restrict_of_subset_isCompact
        (hS.thickening.subset inter_subset_left).isCompact_closure
        ((isOpen_thickening.inter H.isOpen).measurableSet) subset_closure 2).eLpNorm_ne_top
      (eLpNorm_mono_measure _ (Measure.restrict_mono (fun x hx =>
        Set.mem_inter (hR2 (hU₁H hx)) hx.2) le_rfl))
  -- Transfer the estimate from the precise representative to `∇ ∂ₑu` and compare constants.
  have hsub : thickening (R / 4) S ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ S' := fun x hx =>
    ⟨hx.1, Set.mem_ofPred.2 (le_of_lt (Set.mem_ofPred.1 hx.2))⟩
  have hsubV : thickening (R / 4) S ∩ {x | c₀ < ⟪x, ν⟫_ℝ} ⊆ (U₁ ⊓ H : Opens E) := fun x hx =>
    ⟨hTU₁ (self_subset_thickening (by positivity) S' (hsub hx)), hx.2⟩
  refine ((hmain.mono hsub).congr fun x hx => hprec (hsubV hx)).mono_const
    (Real.toNNReal_le_toNNReal ?_)
  exact mul_add_div_four_rpow_neg_mul_le hC₀ K.coe_nonneg hR (by positivity)
    (hnorm.trans (by linarith [hMV]))

/-- **The Schauder estimate near a flat boundary, at interior points.** Under the hypotheses of
`exists_holderOnWith_iteratedFDeriv_two_of_laplacian_of_halfSpace`, `D²u` is `α`-Hölder on the
points of `S_{R/4}` in `H`. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_thickening_inter_of_halfSpace {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U S : Set E} {u : E → ℝ} {ν : E} {c₀ : ℝ} {K : ℝ≥0} {R : ℝ},
      ν ≠ 0 → IsOpen U → ContDiffOn ℝ 2 u U → Bornology.IsBounded S →
      0 < R → cthickening R S ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U →
      (∀ x ∈ U, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      HolderOnWith K α (Δ u) (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 u) 2
            (volume.restrict (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))).toReal)).toNNReal α
          (iteratedFDeriv ℝ 2 u) (thickening (R / 4) S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_holderOnWith_gradient_fderiv_of_inner_eq_zero hα hα1 (n := n)
  refine ⟨(n + 1) * (1 + 2 * (n + 1) * C₀), by positivity,
    fun {U S u ν c₀ K R} hν hU hu hS hR hSU hu0 hK => ?_⟩
  set Q := (K : ℝ) + R ^ (-(((n : ℝ) + 1) / 2 + α)) * (eLpNorm (iteratedFDeriv ℝ 2 u) 2
    (volume.restrict (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))).toReal
  have hKQ : (K : ℝ) ≤ Q := le_add_of_nonneg_right (by positivity)
  have hQ0 : 0 ≤ Q := K.coe_nonneg.trans hKQ
  set T := thickening (R / 4) S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}
  have hTS : T ⊆ thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ} := fun x hx =>
    ⟨thickening_mono (by linarith) S hx.1, hx.2⟩
  have hTU : T ⊆ U := fun x hx =>
    hSU ⟨thickening_subset_cthickening R S (hTS hx).1,
      Set.mem_ofPred.2 (le_of_lt (Set.mem_ofPred.1 (hTS hx).2))⟩
  -- An orthonormal basis `b` with `b 0 = ν / ‖ν‖`; the other `b i` are tangential.
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (n + 1)) ℝ E, b 0 = (‖ν‖⁻¹ : ℝ) • ν := by
    obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
      (by simp) (v := fun _ : Fin (n + 1) => (‖ν‖⁻¹ : ℝ) • ν) (s := {0})
      (orthonormal_subsingleton_iff.2 fun _ => norm_smul_inv_norm hν)
    exact ⟨b, hb 0 rfl⟩
  have hbν : ∀ i : Fin n, ⟪b i.succ, ν⟫_ℝ = 0 := fun i => by
    have h0 : ⟪b i.succ, b 0⟫_ℝ = 0 := b.orthonormal.2 (Fin.succ_ne_zero i)
    rw [hb, inner_smul_right] at h0
    exact (mul_eq_zero.1 h0).resolve_left (inv_ne_zero (norm_ne_zero_iff.2 hν))
  have htan : ∀ i : Fin n, ∀ x ∈ T, ∀ y ∈ T,
      ‖∇ (fun z => fderiv ℝ u z (b i.succ)) x - ∇ (fun z => fderiv ℝ u z (b i.succ)) y‖ ≤
        C₀ * Q * dist x y ^ (α : ℝ) := fun i x hx y hy => by
    have := (h hν hU hu hS hR hSU hu0 hK (b i.succ) (b.orthonormal.1 _) (hbν i)).dist_le hx hy
    rwa [Real.coe_toNNReal _ (by positivity), dist_eq_norm] at this
  have hcd : ∀ x ∈ T, ContDiffAt ℝ 2 u x := fun x hx => hu.contDiffAt (hU.mem_nhds (hTU hx))
  -- Every direction is controlled by `D = K + 2 (n + 1) C₀ Q`.
  have hdir : ∀ i, ∀ x ∈ T, ∀ y ∈ T,
      dist (∇ (fun z => fderiv ℝ u z (b i)) x) (∇ (fun z => fderiv ℝ u z (b i)) y) ≤
        (K + 2 * (n + 1) * (C₀ * Q)) * dist x y ^ (α : ℝ) := by
    intro i x hx y hy
    have hd : 0 ≤ dist x y ^ (α : ℝ) := by positivity
    rw [dist_eq_norm]
    refine Fin.cases ?_ (fun i => ?_) i
    · refine (b.norm_gradient_fderiv_sub_le_of_laplacian (hcd x hx) (hcd y hy)
        (htan · x hx y hy)).trans ?_
      have hΔ := (hK.mono hTS).dist_le hx hy
      rw [Real.dist_eq] at hΔ
      nlinarith [mul_nonneg (mul_nonneg hC₀ hQ0) hd]
    · have h1 := mul_nonneg (mul_nonneg hC₀ hQ0) hd
      have h2 := mul_nonneg K.coe_nonneg hd
      exact (htan i x hx y hy).trans (by nlinarith)
  refine (b.holderOnWith_iteratedFDeriv_two_of_dist_gradient_le (by positivity)
    (fun x hx => ((hcd x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    hdir).mono_const (Real.toNNReal_le_toNNReal ?_)
  rw [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  have : (K : ℝ) + 2 * (n + 1) * (C₀ * Q) ≤ (1 + 2 * (n + 1) * C₀) * Q := by nlinarith
  calc ((n : ℝ) + 1) * (K + 2 * (n + 1) * (C₀ * Q))
      ≤ ((n : ℝ) + 1) * ((1 + 2 * (n + 1) * C₀) * Q) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

/-- **Schauder estimate up to a flat boundary for Poisson's equation, classical form.** Let
`0 < α < 1`. There is a constant `C`, depending only on `n` and `α`, such that the following holds.
Let `H = {x | c₀ < ⟪x, ν⟫}` be an open half-space of `ℝ^{n+1}`, `ν ≠ 0`, let `S` be a bounded set
in the closed half-space `{x | c₀ ≤ ⟪x, ν⟫}` and `R > 0`. Let `u` be of class `C²` on an open set
`U` containing `cthickening R S ∩ {x | c₀ ≤ ⟪x, ν⟫}`, vanishing on the part of the hyperplane
`{x | ⟪x, ν⟫ = c₀}` in `U`, and suppose that `Δu` is `α`-Hölder with constant `K` on `S_R ∩ H`,
where `S_R` is the open `R`-thickening of `S`. Then the second derivative `D²u` is `α`-Hölder on
`S`, with constant

`C (K + R^{-(n+1)/2-α} ‖D²u‖_{L²(S_R ∩ H)})`.

The set `S` may meet the hyperplane, so this is the `C^{2,α}` estimate up to the flat part of the
boundary of `U ∩ H`. The constant sees `Δu` and `D²u` only on the part of `S_R` in `H`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_laplacian_of_halfSpace {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {U S : Set E} {u : E → ℝ} {ν : E} {c₀ : ℝ} {K : ℝ≥0} {R : ℝ},
      ν ≠ 0 → IsOpen U → ContDiffOn ℝ 2 u U → Bornology.IsBounded S →
      (∀ x ∈ S, c₀ ≤ ⟪x, ν⟫_ℝ) → 0 < R → cthickening R S ∩ {x | c₀ ≤ ⟪x, ν⟫_ℝ} ⊆ U →
      (∀ x ∈ U, ⟪x, ν⟫_ℝ = c₀ → u x = 0) →
      HolderOnWith K α (Δ u) (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}) →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) *
          (eLpNorm (iteratedFDeriv ℝ 2 u) 2
            (volume.restrict (thickening R S ∩ {x | c₀ < ⟪x, ν⟫_ℝ}))).toReal)).toNNReal α
          (iteratedFDeriv ℝ 2 u) S := by
  obtain ⟨C, hC, h⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_thickening_inter_of_halfSpace hα hα1 (n := n)
  refine ⟨C, hC, fun {U S u ν c₀ K R} hν hU hu hS hSc hR hSU hu0 hK => ?_⟩
  have hT := h hν hU hu hS hR hSU hu0 hK
  -- Push each point of `S` into `H` along `ν`: the translates `x + tₖ ν` with `tₖ ↓ 0` lie in
  -- `S_{R/4} ∩ H`, where `D²u` is Hölder, and `D²u (x + tₖ ν) → D²u x`.
  set t : ℕ → ℝ := fun k => R / (4 * ‖ν‖) / ((k : ℝ) + 2) with ht
  have ht0 : ∀ k, 0 < t k := fun k => by positivity
  have htR : ∀ k, t k * ‖ν‖ < R / 4 := fun k => by
    have hk : (1 : ℝ) < k + 2 := by have := k.cast_nonneg (α := ℝ); linarith
    have : t k * ‖ν‖ = R / 4 / (k + 2) := by simp only [ht]; field_simp
    rw [this]
    exact div_lt_self (by positivity) hk
  have hmem : ∀ k, ∀ x ∈ S, x + t k • ν ∈ thickening (R / 4) S ∩ {x | c₀ < ⟪x, ν⟫_ℝ} :=
    fun k x hx => by
      refine ⟨mem_thickening_iff.2 ⟨x, hx, ?_⟩, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (ht0 k).le]
        exact htR k
      · have : 0 < t k * ⟪ν, ν⟫_ℝ := mul_pos (ht0 k) (real_inner_self_pos.2 hν)
        simp only [mem_ofPred_eq, inner_add_left, inner_smul_left, RCLike.conj_to_real]
        linarith [hSc x hx]
  refine HolderOnWith.of_tendsto (l := Filter.atTop) (u := fun k x => iteratedFDeriv ℝ 2 u
    (x + t k • ν)) (fun x hx => ?_) (.of_forall fun k y hy z hz => ?_)
  · have htend : Filter.Tendsto t Filter.atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hxU : x ∈ U := hSU ⟨self_subset_cthickening S hx, hSc x hx⟩
    have hc : ContinuousAt (iteratedFDeriv ℝ 2 u) x :=
      (ContinuousOn.continuousOn_iteratedFDeriv hu hU (by norm_num)).continuousAt
        (hU.mem_nhds hxU)
    refine hc.tendsto.comp ?_
    simpa using tendsto_const_nhds.add (htend.smul_const ν)
  · simpa [edist_add_right] using hT _ (hmem k y hy) _ (hmem k z hz)

end PDE

end TauCeti
