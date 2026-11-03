/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.PDE.Vortex.Uniqueness

/-!
# Uniqueness in the smooth framed gauge group

The smooth framed gauge action on plane fields is free, even on fields with identically zero
section: a stabilizing gauge has zero logarithmic derivative, hence is constant, and the end
condition fixes that constant to one.

For two classical vortices with a common end framing, a smooth nonvanishing factor relating
their sections determines a unique smooth framed gauge relating the fields. The factor tends
to one by the common framing and has unit modulus by the scalar maximum principle. No decay
of a chosen real logarithm is needed, and no Sobolev membership is asserted. The existence of
the nonvanishing factor from equality of zero divisors is a separate local analytic question.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter
open scoped Topology ContDiff

/-- Two classical plane vortices with a common unit-modulus end phase and sections related
by a smooth nowhere-zero factor are related by a unique smooth framed gauge. The zero set
of the second section is required to have empty interior. This theorem does not construct
the factor from a prescribed zero divisor. -/
theorem existsUnique_framedGauge_of_forall_section_eq_mul
    {x y : ℂ → EuclideanSpace ℝ (Fin 4)} {h phase : ℂ → ℂ}
    (hxb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hxb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hxp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hxq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hyb₁ : Differentiable ℝ (fun w ↦ y w 0)) (hyb₂ : Differentiable ℝ (fun w ↦ y w 1))
    (hyp : ContDiff ℝ 2 (fun w ↦ y w 2)) (hyq : ContDiff ℝ 2 (fun w ↦ y w 3))
    (hxsol : ∀ z, equation x z = 0) (hysol : ∀ z, equation y z = 0)
    (hphase : ∀ᶠ z in cocompact ℂ, ‖phase z‖ = 1)
    (hxlim : Tendsto (fun z ↦ sectionValue x z * phase z) (cocompact ℂ) (𝓝 1))
    (hylim : Tendsto (fun z ↦ sectionValue y z * phase z) (cocompact ℂ) (𝓝 1))
    (hh : ContDiff ℝ ∞ h) (hh₀ : ∀ z, h z ≠ 0)
    (hα : ∀ z, sectionValue x z = h z * sectionValue y z)
    (hdense : Dense {z | y z 2 ^ 2 + y z 3 ^ 2 ≠ 0}) :
    ∃! u : framedGaugeGroup, (∀ z, (u.val z : ℂ) = h z) ∧ x = u • y := by
  have hα' (z : ℂ) : (x z 2 + x z 3 * I : ℂ) = h z * (y z 2 + y z 3 * I) := by
    have hz := hα z
    simp only [sectionValue_apply] at hz
    linear_combination hz / 2
  -- A common unit end phase supplies both modulus limits used by the maximum principle.
  have hmod (v : ℂ → EuclideanSpace ℝ (Fin 4))
      (hv : Tendsto (fun z ↦ sectionValue v z * phase z) (cocompact ℂ) (𝓝 1)) :
      Tendsto (fun z ↦ 4 * (v z 2 ^ 2 + v z 3 ^ 2)) (cocompact ℂ) (𝓝 1) := by
    have hn := hv.norm.pow 2
    simp only [norm_one, one_pow] at hn
    apply hn.congr'
    filter_upwards [hphase] with z hz
    rw [norm_mul, hz, mul_one, Complex.sq_norm, sectionValue_apply, normSq_mul,
      normSq_ofNat, normSq_add_mul_I]
    ring
  obtain ⟨f, hf, hfactor, hfields⟩ :=
    exists_eq_phaseGauge_of_forall_section_eq_mul hxb₁ hxb₂ hxp hxq hyb₁ hyb₂ hyp hyq
      hxsol hysol (hmod x hxlim) (hmod y hylim) (hh.of_le (by simp)) hh₀ hα' hdense
  let u : ℂ → Circle := fun z ↦ Circle.exp (f z)
  have hucoe (z : ℂ) : (u z : ℂ) = h z := (hfactor z).symm
  -- The ratio of the two framed sections tends to one, independently of a real lift.
  have ht : Tendsto h (cocompact ℂ) (𝓝 1) := by
    have hdiv := hxlim.div hylim one_ne_zero
    simp only [div_one] at hdiv
    apply hdiv.congr'
    filter_upwards [hylim.eventually_ne one_ne_zero] with z hz
    rw [Pi.div_apply, div_eq_iff hz, hα z]
    ring
  have hu : u ∈ framedGaugeGroup := by
    apply (mem_framedGaugeGroup _).mpr
    refine ⟨?_, ?_⟩
    · simpa only [hucoe] using hh
    · apply tendsto_subtype_rng.mpr
      simpa only [hucoe, Circle.coe_one] using ht
  have hxy : x = (⟨u, hu⟩ : framedGaugeGroup) • y := by
    rw [framedGaugeGroup_smul, gaugeTransform_exp (hf.differentiable two_ne_zero), hfields]
  refine ⟨⟨u, hu⟩, ⟨hucoe, hxy⟩, fun v hv ↦ ?_⟩
  exact IsCancelSMul.right_cancel v ⟨u, hu⟩ y (hv.2.symm.trans hxy)

end TauCeti.Vortex
