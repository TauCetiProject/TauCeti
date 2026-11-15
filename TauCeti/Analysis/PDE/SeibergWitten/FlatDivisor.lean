/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.TransverseDivisor

/-!
# The section of a confined flat limit and the plane vortex with the same zeros

Rescaling a large-parameter Seiberg–Witten solution near a pseudoholomorphic curve gives, in the
limit, fields on `ℂ_base × ℂ_normal` (`TauCeti.Analysis.PDE.SeibergWitten.FlatLimit`). On the
canonical line the spinor of such a limit is a section `α` with `∂bar_a α = 0`, and when the
`(0,2)`-part of the curvature vanishes a smooth complex gauge makes it holomorphic:
`α = exp g · f` with `f` entire (`TauCeti.exists_contDiff_differentiable_exp_smul`). The transverse
vacuum condition `|α| → 1` as the normal coordinate tends to infinity confines the zeros of `α` to
a slab `{‖w‖ < K}`.

This file compares such a section with the plane vortex that has the same zeros. Let the base `E`
be a finite-dimensional complex normed space (`ℂ_base` in the application), and let
`α = exp g · f : E × ℂ → ℂ` with `g` smooth and `f` holomorphic, nonzero wherever `K ≤ ‖w‖`.
Then (`TauCeti.SeibergWitten.exists_contDiff_eq_mul_sectionValue_of_forall_le_norm_ne_zero`):

* the zeros of `α` are `E × D` for one effective divisor `D ∈ Sym ℂ m` of points of norm less
  than `K`, since `f = q ∏_{a ∈ D} (w - a)` with `q` holomorphic and nowhere zero
  (`Differentiable.exists_eq_mul_prod_sub_of_forall_le_norm_ne_zero`);
* there is a smooth framed degree-`m` plane vortex `x` whose zero divisor is `D`, with section
  `exp (u w) ∏_{a ∈ D} (w - a)`
  (`TauCeti.Vortex.exists_contDiff_equation_amplitudeField_prod_sub_eq_zero`);
* `α (z, w) = h (z, w) α_x (w)` for a smooth nowhere-zero function `h`, where `α_x` is the section
  of `x`.

The function `h` is the ratio of the two sections across their common zeros, and its log-modulus
`log |h|² = log |α|² - log |α_x|²` is the scalar of Taubes's comparison of the limit with the
base-independent plane vortex. A factorization `α = h α'` with `h` a nowhere-zero `C²` function is
the input of that comparison (`TauCeti.SeibergWitten.norm_eq_one_and_eq_sub_phaseForm_of_tendsto`),
which shows that when `log |h|²` is bounded and both pairs solve the flat vortex equations with the
transverse vacuum condition, `|h| = 1` and the pairs differ by the gauge transformation `h`. The
boundedness of `log |h|²` is not proved here.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 4.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

open Complex Filter Topology
open scoped ContDiff

namespace TauCeti.SeibergWitten

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **A confined section and the plane vortex with the same zeros.** Let `α = exp g · f` on
`E × ℂ`, with `g` smooth, `f` holomorphic and `α (z, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there are an
effective divisor `D ∈ Sym ℂ m` of points of norm less than `K`, a smooth framed degree-`m` plane
vortex `x` with zero divisor `D`, and a smooth nowhere-zero `h : E × ℂ → ℂ` with
`α (z, w) = h (z, w) α_x (w)`, where `α_x` is the section of `x`. -/
theorem exists_contDiff_eq_mul_sectionValue_of_forall_le_norm_ne_zero {α g f : E × ℂ → ℂ}
    (hg : ContDiff ℝ ∞ g) (hf : Differentiable ℂ f) (hα : ∀ p, α p = cexp (g p) * f p) {K : ℝ}
    (hK : ∀ z w, K ≤ ‖w‖ → α (z, w) ≠ 0) :
    ∃ (m : ℕ) (D : Sym ℂ m) (x : ℂ → EuclideanSpace ℝ (Fin 4)),
      (∀ a ∈ (D : Multiset ℂ), ‖a‖ < K) ∧ ContDiff ℝ ∞ x ∧ (∀ w, Vortex.equation x w = 0) ∧
      Tendsto (fun w ↦ Vortex.sectionValue x w * ((w / (‖w‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1) ∧
      IsZeroMultiplicity (Vortex.sectionValue x) (fun w ↦ (D : Multiset ℂ).count w) ∧
      ∃ h : E × ℂ → ℂ, ContDiff ℝ ∞ h ∧ (∀ p, h p ≠ 0) ∧
        ∀ p, α p = h p * Vortex.sectionValue x p.2 := by
  have hfK (z : E) (w : ℂ) (hw : K ≤ ‖w‖) : f (z, w) ≠ 0 := by
    have h := hK z w hw
    rw [hα] at h
    exact right_ne_zero_of_mul h
  obtain ⟨s, hsK, q, hq, hq₀, hfq⟩ := hf.exists_eq_mul_prod_sub_of_forall_le_norm_ne_zero hfK
  obtain ⟨u, hu, hx, hsol, hfr⟩ :=
    Vortex.exists_contDiff_equation_amplitudeField_prod_sub_eq_zero (⟨s, rfl⟩ : Sym ℂ s.card)
  refine ⟨_, ⟨s, rfl⟩, _, hsK, hx, hsol, hfr,
    Vortex.isZeroMultiplicity_sectionValue_amplitudeField_prod_sub hu.continuous _,
    fun p ↦ cexp (g p) * q p * cexp (-(u p.2 : ℂ)), ?_, fun p ↦ by simp [hq₀ p], fun p ↦ ?_⟩
  · have hqc : ContDiff ℝ ∞ q := (hq.contDiff_of_finiteDimensional (n := ∞)).restrict_scalars ℝ
    have huc : ContDiff ℝ ∞ fun p : E × ℂ ↦ -(u p.2 : ℂ) :=
      (ofRealCLM.contDiff.comp (hu.comp contDiff_snd)).neg
    exact ((contDiff_exp.comp hg).mul hqc).mul (contDiff_exp.comp huc)
  · rw [hα, hfq, Vortex.sectionValue_amplitudeField, ofReal_exp, Sym.coe_mk]
    have he : cexp (-(u p.2 : ℂ)) * cexp (u p.2 : ℂ) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    linear_combination (-(cexp (g p) * q p * (s.map fun a ↦ p.2 - a).prod)) * he

end TauCeti.SeibergWitten
