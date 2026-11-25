/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.TransverseDivisor
public import TauCeti.Analysis.PDE.Vortex.AmplitudeForm
public import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# The ratio of a confined holomorphic section to a plane vortex with the same zeros

In Taubes's analysis of large-parameter Seiberg–Witten solutions near a pseudoholomorphic curve,
the rescaled limits are fields `(a, α)` on `ℂ_base × ℂ_normal` with `∂bar_a α = 0`, whose zeros are
confined to a bounded normal disc. In a holomorphic gauge `α` becomes a holomorphic function `f`
(`TauCeti.exists_contDiff_differentiable_exp_smul`), and its transverse divisor is a fixed multiset
`s` of the normal line (`Differentiable.exists_forall_analyticOrderAt_eq_count`). To identify the
whole field, not only its divisor, with the pullback of a plane vortex along the normal
coordinate, one compares `α` with the section `α'` of a plane vortex whose divisor is `s`, through
the **log-modulus ratio** `log |h|²` of `α = h α'`
(`TauCeti.SeibergWitten.norm_eq_one_and_eq_sub_phaseForm_of_tendsto`). This needs the ratio `h`
to be a smooth function with no zeros, although `α` and `α'` both vanish on `ℂ_base × s`.

This file constructs that ratio. Let `E` be a finite-dimensional complex normed space, the base,
let `f : E × ℂ → ℂ` be holomorphic, and let `x` be a smooth plane vortex with the degree-`m` end
framing whose section vanishes exactly at the points of `s`, with the multiplicities of `s`.

* If the transverse divisor of `f` is `s`, then `f (y, w) = h (y, w) α'(w)` for a smooth `h` with
  no zeros, where `α'` is the section of `x` (`exists_contDiff_eq_mul_sectionValue`). Indeed
  `f (y, w) = ∏_{a ∈ s} (w - a) u (y, w)` with `u` holomorphic and nowhere zero
  (`Differentiable.exists_eq_prod_sub_mul`), while `α'(w) = g(w) e^{v(w)} ∏_{a ∈ s} (w - a)` for a
  smooth framed gauge `g` and a smooth real `v`, by the amplitude form of a vortex
  (`TauCeti.Vortex.exists_framedGaugeGroup_smul_amplitudeField_eq`). So
  `h = u / (g e^v)`, and the log-modulus ratio `log |h|²` is smooth.
* If the zeros of `f` are confined to `‖w‖ < K`, there are a multiset `s` of points of norm less
  than `K`, a smooth framed vortex `x` of degree `card s` with divisor `s`, and such a ratio `h`
  (`exists_vortex_contDiff_eq_mul_sectionValue`). The vortex exists by Taubes's existence theorem
  (`TauCeti.Vortex.exists_contDiff_equation_eq_zero_isZeroMultiplicity`) and is unique up to a
  framed gauge.
* The same holds for a section `α` that becomes holomorphic in a complex gauge, `e^g α`
  holomorphic for a smooth `g`, as produced by the `∂bar`-Poincaré lemma
  (`exists_vortex_contDiff_eq_mul_sectionValue_of_differentiable_exp_mul`).
* The zeros of the pulled-back section `(y, w) ↦ α'(w)` have dense complement
  (`dense_setOf_sectionValue_snd_ne_zero`), as the comparison of connections across the common
  zeros requires.

The boundedness of the log-modulus ratio, its transverse vacuum normalization and the resulting
gauge equivalence of the fields are not proved here.

## Main results

All in the namespace `TauCeti.Vortex`:

* `exists_contDiff_eq_mul_sectionValue`: a holomorphic function on `E × ℂ` with the transverse
  divisor of a smooth framed vortex is a smooth nowhere vanishing multiple of its section.
* `exists_vortex_contDiff_eq_mul_sectionValue`: a holomorphic function with confined zeros is a
  smooth nowhere vanishing multiple of the section of a smooth framed vortex.
* `exists_vortex_contDiff_eq_mul_sectionValue_of_differentiable_exp_mul`: the same for a section
  that is holomorphic in a smooth complex gauge.
* `dense_setOf_sectionValue_snd_ne_zero`: the pulled-back vortex section vanishes only on a closed
  set with dense complement.

## References

* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

open Complex Filter Set Topology
open scoped ContDiff

namespace TauCeti.Vortex

/-- **The common zeros are negligible.** If the section of `x` vanishes exactly at the points of a
multiset `s`, then the pulled-back section `(y, w) ↦ α'(w)` on `E × ℂ` is nonzero on a dense set. -/
theorem dense_setOf_sectionValue_snd_ne_zero {E : Type*} [TopologicalSpace E]
    {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    {s : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ s.count z) :
    Dense {p : E × ℂ | sectionValue x p.2 ≠ 0} := by
  classical
  have h : {p : E × ℂ | sectionValue x p.2 ≠ 0} = univ ×ˢ (univ \ ↑s.toFinset) := by
    ext ⟨y, w⟩
    simp [← hD.eq_zero_iff, Multiset.count_eq_zero]
  rw [h]
  exact dense_univ.prod (dense_univ.sdiff_finset _)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **The vortex ratio of a holomorphic section.** Let `f : E × ℂ → ℂ` be holomorphic, with `E`
finite-dimensional, and let `x` be a smooth plane vortex with the degree-`m` end framing whose
section vanishes to order `s.count w` at each `w`. If the transverse divisor of `f` is `s`, that
is, every slice `w ↦ f (y, w)` vanishes to order `s.count w` at `w`, then
`f (y, w) = h (y, w) * α'(w)` for a smooth `h` with no zeros, where `α'` is the section of `x`. -/
theorem exists_contDiff_eq_mul_sectionValue {f : E × ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Multiset ℂ} (hs : ∀ y w, analyticOrderAt (fun w ↦ f (y, w)) w = s.count w)
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : ContDiff ℝ ∞ x) (hsol : ∀ z, equation x z = 0)
    {m : ℕ}
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ s.count z) :
    ∃ h : E × ℂ → ℂ, ContDiff ℝ ∞ h ∧ (∀ p, h p ≠ 0) ∧ ∀ p, f p = h p * sectionValue x p.2 := by
  obtain ⟨u, hu, hu0, hfu⟩ := hf.exists_eq_prod_sub_mul hs
  obtain ⟨v, hv, -, -, g, hg⟩ := exists_framedGaugeGroup_smul_amplitudeField_eq hx hsol hframe hD
  -- The section of `x` is `g e^v ∏ (w - a)`, with `k = g e^v` smooth and nowhere zero.
  set k : ℂ → ℂ := fun w ↦ (g.val w : ℂ) * (Real.exp (v w) : ℂ) with hk
  have hxk (w : ℂ) : sectionValue x w = k w * (s.map fun a ↦ w - a).prod := by
    rw [← hg, framedGaugeGroup_smul, sectionValue_gaugeTransform, sectionValue_amplitudeField,
      hk, mul_assoc]
  have hk0 (w : ℂ) : k w ≠ 0 :=
    mul_ne_zero (Circle.coe_ne_zero _) (ofReal_ne_zero.2 (Real.exp_pos _).ne')
  have hkd : ContDiff ℝ ∞ k :=
    ((mem_framedGaugeGroup _).1 g.property).1.mul (ofRealCLM.contDiff.comp
        (Real.contDiff_exp.comp hv))
  have hud : ContDiff ℝ ∞ u := hu.contDiff_of_finiteDimensional.restrict_scalars ℝ
  refine ⟨fun p ↦ u p * (k p.2)⁻¹, hud.mul ((hkd.comp contDiff_snd).inv fun p ↦ hk0 p.2),
    fun p ↦ mul_ne_zero (hu0 p) (inv_ne_zero (hk0 p.2)), fun p ↦ ?_⟩
  rw [hfu, hxk]
  field_simp [hk0 p.2]

/-- **The vortex ratio of a holomorphic section with confined zeros.** Let `f : E × ℂ → ℂ` be
holomorphic, with `E` finite-dimensional, and suppose that `f (y, w) ≠ 0` whenever `K ≤ ‖w‖`. Then
there are a multiset `s` of points of norm less than `K`, a smooth plane vortex `x` with the
degree-`card s` end framing whose section vanishes exactly at the points of `s`, with their
multiplicities, and a smooth `h` with no zeros such that `f (y, w) = h (y, w) * α'(w)`, where `α'`
is the section of `x`. -/
theorem exists_vortex_contDiff_eq_mul_sectionValue {f : E × ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : ℝ} (hK : ∀ y w, K ≤ ‖w‖ → f (y, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧ ∃ x : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ Multiset.card s)⁻¹) (cocompact ℂ)
        (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) (fun z ↦ s.count z) ∧
      ∃ h : E × ℂ → ℂ, ContDiff ℝ ∞ h ∧ (∀ p, h p ≠ 0) ∧ ∀ p, f p = h p * sectionValue x p.2 := by
  obtain ⟨s, hsK, hs⟩ := hf.exists_forall_analyticOrderAt_eq_count hK
  obtain ⟨x, hx, hsol, hframe, hD⟩ :=
    exists_contDiff_equation_eq_zero_isZeroMultiplicity (⟨s, rfl⟩ : Sym ℂ (Multiset.card s))
  exact ⟨s, hsK, x, hx, hsol, hframe, hD,
    exists_contDiff_eq_mul_sectionValue hf hs hx hsol hframe hD⟩

/-- **The vortex ratio in a complex gauge.** Let `α : E × ℂ → ℂ` be a section which becomes
holomorphic in the complex gauge `e^g` of a smooth `g`, that is, `e^g α` is holomorphic, and
suppose that `α (y, w) ≠ 0` whenever `K ≤ ‖w‖`. Then there are a multiset `s` of points of norm
less than `K`, a smooth plane vortex `x` with the degree-`card s` end framing and divisor `s`, and a
smooth `h` with no zeros such that `α (y, w) = h (y, w) * α'(w)`, where `α'` is the section of
`x`. -/
theorem exists_vortex_contDiff_eq_mul_sectionValue_of_differentiable_exp_mul
    {α g : E × ℂ → ℂ} (hg : ContDiff ℝ ∞ g) (hα : Differentiable ℂ fun p ↦ cexp (g p) * α p)
    {K : ℝ} (hK : ∀ y w, K ≤ ‖w‖ → α (y, w) ≠ 0) :
    ∃ s : Multiset ℂ, (∀ a ∈ s, ‖a‖ < K) ∧ ∃ x : ℂ → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ x ∧ (∀ z, equation x z = 0) ∧
      Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ Multiset.card s)⁻¹) (cocompact ℂ)
        (𝓝 1) ∧
      IsZeroMultiplicity (sectionValue x) (fun z ↦ s.count z) ∧
      ∃ h : E × ℂ → ℂ, ContDiff ℝ ∞ h ∧ (∀ p, h p ≠ 0) ∧ ∀ p, α p = h p * sectionValue x p.2 := by
  obtain ⟨s, hsK, x, hx, hsol, hframe, hD, h, hh, hh0, hfh⟩ :=
    exists_vortex_contDiff_eq_mul_sectionValue hα fun y w hw ↦
      mul_ne_zero (Complex.exp_ne_zero _) (hK y w hw)
  refine ⟨s, hsK, x, hx, hsol, hframe, hD, fun p ↦ cexp (-g p) * h p,
    (Complex.contDiff_exp.comp hg.neg).mul hh,
    fun p ↦ mul_ne_zero (Complex.exp_ne_zero _) (hh0 p), fun p ↦ ?_⟩
  rw [mul_assoc, ← hfh]
  simp [← mul_assoc, ← Complex.exp_add]

end TauCeti.Vortex
