/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.RealIntegral

/-!
# The real winding integrand at a smooth crossing

This file proves the local crossing-value calculation in Hungerbühler–Wasem Proposition 2.3.
For a twice differentiable plane curve `γ` passing through `s` at `t₀`, the apparently singular
real winding integrand

`(x ẏ - y ẋ) / (x² + y²)`, where `x + iy = γ - s`,

tends to

`(ẋ ÿ - ẏ ẍ) / (2 (ẋ² + ẏ²))`.

The theorem is stated using the two Peano expansions it actually needs. This keeps it independent
of any particular second-derivative API and lets clients obtain the hypotheses from `C²`, strict
second derivative, or Taylor estimates. The intermediate theorem isolates the algebraic limit and
is useful whenever the chord and velocity expansions come from different regularity packages.

Mathlib has no signed-curvature API for plane curves. Accordingly, as prescribed by the contour
integration roadmap, the answer is given by the explicit coordinate formula. It is one half of
signed curvature times speed.

## Main results

* `Contour.realWindingIntegrand` is the real integrand of Hungerbühler–Wasem Proposition 2.3.
* `Contour.tendsto_realWindingIntegrand_mul_add` is the algebraic limit for second-order chord
  and first-order velocity expansions.
* `Contour.tendsto_realWindingIntegrand_at_crossing` gives the crossing value for a curve.

## References

N. Hungerbühler and M. Wasem, *Non-integer valued winding numbers and a generalized Residue
Theorem*, arXiv:1808.00997 (2018), Proposition 2.3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Complex Filter Topology

/-- The real winding integrand `(x ẏ - y ẋ) / (x² + y²)` for a position `z = x + iy`
and velocity `v = ẋ + iẏ`. It is defined to be `0` at `z = 0`, following division in `ℝ`;
the crossing theorem below supplies its canonical continuous extension along a regular `C²`
curve. -/
def realWindingIntegrand (z v : ℂ) : ℝ :=
  (z.re * v.im - z.im * v.re) / Complex.normSq z

/-- The real winding integrand is the imaginary part of the complex winding integrand. -/
theorem realWindingIntegrand_eq_im_inv_mul (z v : ℂ) :
    realWindingIntegrand z v = (z⁻¹ * v).im := by
  rw [realWindingIntegrand, inv_mul_eq_div, Complex.div_im]
  ring

/-- Scaling position and velocity by the same nonzero real parameter leaves the real winding
integrand unchanged. -/
theorem realWindingIntegrand_ofReal_mul {c : ℝ} (hc : c ≠ 0) (z v : ℂ) :
    realWindingIntegrand ((c : ℂ) * z) ((c : ℂ) * v) = realWindingIntegrand z v := by
  simp only [realWindingIntegrand, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.normSq_mul, Complex.normSq_ofReal]
  field_simp
  ring

/-- Algebraic form of the smooth-crossing limit. If `q → L`, `(q - L) / τ → A/2`, and
`d → A`, then the real winding integrand of position `τq` and velocity `L + τd` tends to
`(L.re * A.im - L.im * A.re) / (2‖L‖²)`.

The hypotheses are precisely the normalized second-order position expansion and first-order
velocity expansion. -/
theorem tendsto_realWindingIntegrand_mul_add {α : Type*} {l : Filter α}
    {τ : α → ℝ} {q r d : α → ℂ} {L A : ℂ} (hL : L ≠ 0)
    (hq : Tendsto q l (𝓝 L)) (hr : Tendsto r l (𝓝 (A / 2)))
    (hd : Tendsto d l (𝓝 A))
    (hqr : ∀ᶠ i in l, q i - L = ((τ i : ℝ) : ℂ) * r i)
    (hτ : ∀ᶠ i in l, τ i ≠ 0) :
    Tendsto (fun i ↦ realWindingIntegrand (((τ i : ℝ) : ℂ) * q i)
      (L + ((τ i : ℝ) : ℂ) * d i)) l
      (𝓝 ((L.re * A.im - L.im * A.re) / (2 * Complex.normSq L))) := by
  have hnorm : Tendsto (fun i ↦ Complex.normSq (q i)) l (𝓝 (Complex.normSq L)) :=
    (Complex.continuous_normSq.tendsto L).comp hq
  have hq_re := (Complex.continuous_re.tendsto L).comp hq
  have hq_im := (Complex.continuous_im.tendsto L).comp hq
  have hr_re := (Complex.continuous_re.tendsto (A / 2)).comp hr
  have hr_im := (Complex.continuous_im.tendsto (A / 2)).comp hr
  have hd_re := (Complex.continuous_re.tendsto A).comp hd
  have hd_im := (Complex.continuous_im.tendsto A).comp hd
  have hnum : Tendsto (fun i ↦
      (r i).re * L.im - (r i).im * L.re +
        ((q i).re * (d i).im - (q i).im * (d i).re)) l
      (𝓝 ((L.re * A.im - L.im * A.re) / 2)) := by
    convert (((hr_re.mul_const L.im).sub (hr_im.mul_const L.re)).add
      ((hq_re.mul hd_im).sub (hq_im.mul hd_re))) using 1
    all_goals simp <;> ring_nf
  have hdiv := hnum.div hnorm ((Complex.normSq_eq_zero.not.mpr hL))
  have hq_ne : ∀ᶠ i in l, q i ≠ 0 :=
    hq.eventually (isOpen_compl_singleton.mem_nhds hL)
  convert hdiv.congr' ?_ using 1
  · ring_nf
  filter_upwards [hqr, hτ, hq_ne] with i hqi hτi hqi_ne
  rw [realWindingIntegrand]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, Complex.add_re, Complex.add_im, Complex.normSq_mul, Complex.normSq_ofReal]
  have hτsq : τ i ^ 2 ≠ 0 := pow_ne_zero _ hτi
  have hLre : L.re = (q i).re - τ i * (r i).re := by
    have := congrArg Complex.re hqi
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] at this
    linarith
  have hLim : L.im = (q i).im - τ i * (r i).im := by
    have := congrArg Complex.im hqi
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero] at this
    linarith
  rw [hLre, hLim]
  simp only [Pi.div_apply]
  field_simp [hτi, Complex.normSq_eq_zero.not.mpr hqi_ne]
  ring

/-- **Hungerbühler–Wasem Proposition 2.3, crossing value.** At a regular crossing
`γ t₀ = s`, a second-order chord expansion with acceleration `A` and the matching first-order
velocity expansion imply

`(x ẏ - y ẋ) / (x² + y²) → (ẋ ÿ - ẏ ẍ) / (2 (ẋ² + ẏ²))`.

This is the explicit form of one half of signed curvature times speed. -/
theorem tendsto_realWindingIntegrand_at_crossing {α : Type*} {l : Filter α}
    {t : α → ℝ} {t₀ : ℝ} {γ : ℝ → ℂ} {s L A : ℂ} (hL : L ≠ 0)
    (htend : Tendsto t l (𝓝 t₀)) (hcross : γ t₀ = s)
    (hpos : Tendsto (fun i ↦ ((γ (t i) - s) / (((t i - t₀ : ℝ) : ℂ)))) l (𝓝 L))
    (hpos₂ : Tendsto (fun i ↦
      (((γ (t i) - s) / (((t i - t₀ : ℝ) : ℂ))) - L) /
        (((t i - t₀ : ℝ) : ℂ))) l (𝓝 (A / 2)))
    (hvel : Tendsto (fun i ↦ (deriv γ (t i) - L) /
      (((t i - t₀ : ℝ) : ℂ))) l (𝓝 A))
    (ht : ∀ᶠ i in l, t i ≠ t₀) :
    Tendsto (fun i ↦ realWindingIntegrand (γ (t i) - s) (deriv γ (t i))) l
      (𝓝 ((L.re * A.im - L.im * A.re) / (2 * Complex.normSq L))) := by
  subst s
  have hpos' := tendsto_snd.comp (Tendsto.prodMk htend hpos)
  change Tendsto (fun i ↦ (γ (t i) - γ t₀) / (((t i - t₀ : ℝ) : ℂ))) l (𝓝 L) at hpos'
  let τ : α → ℝ := fun i ↦ t i - t₀
  let q : α → ℂ := fun i ↦ (γ (t i) - γ t₀) / ((τ i : ℝ) : ℂ)
  let r : α → ℂ := fun i ↦ (q i - L) / ((τ i : ℝ) : ℂ)
  let d : α → ℂ := fun i ↦ (deriv γ (t i) - L) / ((τ i : ℝ) : ℂ)
  have hτ : ∀ᶠ i in l, τ i ≠ 0 := ht.mono fun i hi ↦ sub_ne_zero.mpr hi
  have hqr : ∀ᶠ i in l, q i - L = ((τ i : ℝ) : ℂ) * r i := hτ.mono fun i hi ↦ by
    simp only [r]
    field_simp [Complex.ofReal_ne_zero.mpr hi]
  have hmain := tendsto_realWindingIntegrand_mul_add hL hpos' hpos₂ hvel hqr hτ
  apply hmain.congr'
  filter_upwards [hτ] with i hi
  have hiℂ : ((τ i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hi
  congr 1
  · simp only [τ] at hiℂ ⊢
    field_simp [hiℂ]
  · simp only [τ] at hiℂ ⊢
    field_simp [hiℂ]
    ring

end TauCeti.Contour

end
