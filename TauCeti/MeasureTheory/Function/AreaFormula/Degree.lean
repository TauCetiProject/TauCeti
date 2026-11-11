/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.RegularValue
public import TauCeti.MeasureTheory.Function.AreaFormula.Multiplicity
import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The degree formula for integrals

Let `E` be a finite-dimensional real inner product space and `f : E → E` a proper `C¹` map. For
every continuous compactly supported `g : E → F` with values in a real normed space,

`∫ det Df(x) • g (f x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the homological degree of `f` for any orientation of `E`, used on both source
and target (`TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_smul_integral`).
For a two-form `β = b dy₁ ∧ dy₂` on the plane the pullback is `f^* β = (b ∘ f) det Df dx₁ ∧ dx₂`, so
this is the classical formula `∫ f^* β = deg f ∫ β` for compactly supported top-degree forms, here
proved with the degree defined by local homology rather than by counting preimages of regular
values or by de Rham cohomology.

The proof has two halves. The first is the signed area formula with multiplicity
(`TauCeti.integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul`), valid for any
differentiable map with almost every fibre finite, any strongly measurable `g`, and integrable
`det Df • g ∘ f`:

`∫ det Df(x) • g (f x) dx = ∫ (N⁺(y) - N⁻(y)) • g(y) dy`,

where `N^±(y)` is the number of preimages of `y` at which `det Df` is positive, respectively
negative. It splits the regular set into the measurable sets where the Jacobian is positive and
negative, where the area formula with multiplicity
(`TauCeti.lintegral_normDet_fderiv_mul_eq_lintegral_tsum_of_injective_fderiv`) identifies the
pushforward of `|det Df| dx` with the counting density `N^±(y) dy`
(`TauCeti.map_withDensity_abs_det_fderiv_eq_withDensity_encard`). For a proper `C¹` map the
integrand is continuous with compact support, hence integrable. The second half is that
`N⁺(y) - N⁻(y) = deg f` at every regular value `y`
(`TauCeti.HomologicalOrientation.degree_eq_ncard_sub_ncard`), and that almost every point is a
regular value by Sard's theorem (`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`).

## Main results

* `TauCeti.HomologicalOrientation.integral_det_fderiv_smul_comp_eq_degree_smul_integral`: the
  degree formula.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
-/

public section

noncomputable section

open Set Function MeasureTheory Measure Module
open scoped ENNReal

namespace TauCeti

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **The degree formula for integrals.** Let `o` be an orientation of the finite-dimensional real
inner product space `E`, and let `f : E → E` be a proper `C¹` map. For every continuous compactly
supported `g : E → F`,

`∫ det Df(x) • g (f x) dx = deg f • ∫ g(y) dy`,

where `deg f` is the degree of `f` for the orientation `o` on both source and target. -/
theorem integral_det_fderiv_smul_comp_eq_degree_smul_integral (o : HomologicalOrientation E E n)
    (hE : finrank ℝ E = n) {f : C(E, E)} (hf : ContDiff ℝ 1 f) (hp : IsProperMap f) {g : E → F}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ x, (fderiv ℝ f x).det • g (f x) = o.degree o hE f • ∫ y, g y := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  -- The integrand is continuous with compact support, since `f` is proper.
  have hgf : HasCompactSupport (g ∘ f) :=
    IsCompact.of_isClosed_subset (hp.isCompact_preimage hgc) (isClosed_tsupport _)
      (closure_minimal (by rw [support_comp_eq_preimage]; exact preimage_mono (subset_tsupport g))
        ((isClosed_tsupport g).preimage f.continuous))
  have hint : Integrable fun x ↦ (fderiv ℝ f x).det • g (f x) :=
    ((ContinuousLinearMap.continuous_det.comp (hf.continuous_fderiv one_ne_zero)).smul
      (hg.comp f.continuous)).integrable_of_hasCompactSupport hgf.smul_left
  -- By Sard's theorem almost every point is a regular value.
  have hsard : ∀ᵐ y, ∀ x ∈ f ⁻¹' {y}, (fderiv ℝ f x).det ≠ 0 := by
    have h0 := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume) (f := f)
      (s := {x | (fderiv ℝ f x).det = 0}) (fun x _ ↦ (hd x).hasFDerivAt.hasFDerivWithinAt)
      fun x hx ↦ hx
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy x hx hJx
    exact hy ⟨x, hJx, hx⟩
  -- The fibre over a regular value is finite, and its signed count is the degree.
  have hfin : ∀ᵐ y, (f ⁻¹' {y}).Finite := hsard.mono fun y hy ↦
    (hp.isCompact_preimage isCompact_singleton).finite_of_hasFDerivAt
      (fun x _ ↦ (hd x).hasFDerivAt) fun x hx ↦
        ⟨_, ((fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hy x hx)).antilipschitzWith⟩
  rw [integral_det_fderiv_smul_comp_eq_integral_ncard_sub_ncard_smul hd hfin
      hg.stronglyMeasurable hint, ← Int.cast_smul_eq_zsmul ℝ, ← integral_smul]
  refine integral_congr_ae (hsard.mono fun y hy ↦ ?_)
  simp [o.degree_eq_ncard_sub_ncard hE hp (fun x _ ↦ (hd x).hasFDerivAt) hy]

end HomologicalOrientation

end TauCeti
