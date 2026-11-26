/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.WittenLaplacian.Gap
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.Morse.Pi
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Pi.Prod

/-!
# The gap of the Witten Laplacian at nondegenerate critical points

`TauCeti.Analysis.Calculus.WittenLaplacian.Gap` proves Witten's localization estimate for a
function `f` on `ℝ^ι` that is *exactly* a diagonal quadratic model near each of its critical points.
This file removes that assumption from the linear-in-`t` gap: it is enough that each critical
point `p` is nondegenerate with Hessian `∑ᵢ aᵢ vᵢ wᵢ`, diagonal in the coordinates of `ℝ^ι`. The
quadratic model is then only the second-order Taylor approximation of `f` at `p`, and the
remainder is controlled on a small ball.

**Near a critical point.** By the comparison of the Witten Laplacians of two functions
(`integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul`)
with the translated quadratic model `y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2` and its harmonic-oscillator gap, a
form supported where `|df(x)|² ≥ ∑ᵢ aᵢ² (xᵢ - pᵢ)²` and the Hessian of `f` is within `e` of
`diag(a)` satisfies

`2 t c ‖φ_{≠ s₀}‖² - t e ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`

(`TauCeti.two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`),
where `c ≤ |aᵢ|` for all `i` and `φ_{≠ s₀}` omits the component in the degree `s₀ = {i | aᵢ < 0}`
of the Morse index. At a nondegenerate critical point with Hessian `diag(a)`, Taylor's theorem
gives both hypotheses on a small ball for the slightly weakened model `θ a`, `θ < 1`, with `e`
small plus `(1 - θ) ∑ᵢ |aᵢ|` (`TauCeti.eventually_sum_mul_sq_le_and_sum_sum_abs_sub_le`): the
gradient of `f` is `diag(a) (x - p)` up to `o(|x - p|)` and the Hessian is continuous.

**The gap.** Combining these local bounds with the bound away from the critical points by IMS
localization
(`TauCeti.sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one`)
gives the gap: if `f` is `C²`, the points of a finite set `P` are critical points with diagonal
Hessians with every `|aᵢ| ≥ c > 0`, every critical point within distance `ρ` of `P` lies in `P`,
and at distance more than `ρ` from `P` the gradient is bounded below and the Hessian bounded
above, then in every degree `m` that is no Morse index the quadratic form of `Δ_t` is at least
`t c ‖φ‖²` for all large `t`
(`exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero`).
The localization scale is dictated by the Taylor remainders, so it may be smaller than `ρ`; between
the two scales the gradient does not vanish on a compact set and is bounded below there
(`TauCeti.exists_pos_forall_le_sum_fderiv_apply_single_sq_and_le`). If `f` is exactly the
quadratic model near each point of `P`, then the point is its only critical point nearby, which
gives the gap for exact models
(`TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`). As in
`TauCeti.Analysis.Calculus.WittenLaplacian.Gap`, the statements concern the quadratic form on
compactly supported forms, not the spectrum of a self-adjoint realization of `Δ_t`.

## Main results

* `TauCeti.two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`:
  the harmonic-oscillator gap for forms supported where `f` is close to a quadratic model.
* `exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero`:
  the gap `t c ‖φ‖²` for large `t` in a degree that is no Morse index.
* `TauCeti.exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul`: the same gap
  when `f` is exactly a quadratic model near its critical points.

## References

* E. Witten, *Supersymmetry and Morse theory*, J. Differential Geom. **17** (1982), 661–692, §2.
* H. L. Cycon, R. G. Froese, W. Kirsch and B. Simon, *Schrödinger Operators*, Texts and
  Monographs in Physics, Springer (1987), Chapter 11 (Witten's proof of the Morse inequalities,
  where the quadratic model is the Taylor approximation of the function at its critical points).
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ### The gap near a quadratic model -/

/-- **The harmonic-oscillator gap near a quadratic model.** Let `φ` be a compactly supported `C²`
form and `f` a function that is `C²` at every point of the support of `φ`. Suppose that wherever `φ`
does not vanish, the gradient of `f` is at least that of the quadratic model
`y ↦ ∑ᵢ aᵢ (yᵢ - pᵢ)² / 2`, that is `∑ᵢ aᵢ² (xᵢ - pᵢ)² ≤ |df(x)|²`, and the Hessian of `f` is within
`e` of `diag(a)`, that is `∑_{i,j} |∂ᵢ∂ⱼf(x) - aᵢ δᵢⱼ| ≤ e`. If `c ≤ |aᵢ|` for every `i` and
`t ≥ 0`, then

`2 t c ‖φ_{≠ s₀}‖² - t e ‖φ‖² ≤ ∫ ⟨Δ_t φ, φ⟩`,

where `φ_{≠ s₀}` omits the component at the multi-index `s₀ = {i | aᵢ < 0}`, whose cardinality is
the Morse index of the model. -/
theorem two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    {f : (ι → ℝ) → ℝ} {φ : (ι → ℝ) → Finset ι → ℝ} {a p : ι → ℝ} {t c e : ℝ} (ht : 0 ≤ t)
    (hc : ∀ i, c ≤ |a i|) (hf : ∀ x ∈ tsupport φ, ContDiffAt ℝ 2 f x) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ)
    (hdf : ∀ x, φ x ≠ 0 →
      ∑ i, (a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (he : ∀ x, φ x ≠ 0 → ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) - if i = j then a i else 0| ≤ e) :
    2 * t * c * (∫ x, ∑ s ∈ Finset.univ.erase (Finset.univ.filter fun i ↦ a i < 0), φ x s ^ 2) -
        t * e * ∫ x, ∑ s, φ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  have hg : ContDiff ℝ 2 fun y ↦ diagonalQuadratic a (y - p) :=
    (contDiff_diagonalQuadratic a).comp (contDiff_id.sub contDiff_const)
  -- Compare `f` with the translated quadratic model, then use the gap of the model.
  have hcmp :=
    integral_sum_euclideanWittenLaplacian_mul_sub_le_integral_sum_euclideanWittenLaplacian_mul hf
      (fun x _ ↦ hg.contDiffAt) hφ hφc
      (fun x hx ↦ by simpa only [fderiv_diagonalQuadratic_comp_sub_apply_single] using hdf x hx)
      (fun x hx ↦ by
        simpa only [fderiv_fderiv_diagonalQuadratic_comp_sub_apply_single] using he x hx) t
  have hmodel := two_mul_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_eventuallyEq
    (f := fun y ↦ diagonalQuadratic a (y - p)) (p := p) (b := 0) ht hc hφ hφc
    fun x _ ↦ Eventually.of_forall fun y ↦ (zero_add _).symm
  rw [abs_of_nonneg ht] at hcmp
  linarith

/-! ### The gap at nondegenerate critical points -/

/-- A factor `θ ∈ [7/8, 1)` so close to `1` that `(1 - θ) S ≤ c / 8`. -/
private theorem exists_le_lt_one_mul_le {S c : ℝ} (hS : 0 ≤ S) (hc : 0 < c) :
    ∃ θ : ℝ, 7 / 8 ≤ θ ∧ θ < 1 ∧ (1 - θ) * S ≤ c / 8 := by
  have hδ : 0 < c / (8 * (S + c)) := by positivity
  refine ⟨1 - c / (8 * (S + c)), ?_, by linarith, ?_⟩
  · have : c / (8 * (S + c)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  · rw [sub_sub_cancel, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- Under the hypotheses of the gap at nondegenerate critical points, there is a radius `r > 0`
that separates the points of `P` and on which the hypotheses of the gap near the weakened model
`θ a p` hold around every `p ∈ P`, with error at most `c / 4` when `(1 - θ) ∑ₚ ∑ᵢ |a p i| ≤ c / 8`.
-/
private theorem exists_pos_forall_mem_ball_and_two_mul_le_dist {f : (ι → ℝ) → ℝ}
    (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} (hP : ∀ p ∈ P, fderiv ℝ f p = 0)
    {a : (ι → ℝ) → ι → ℝ}
    (ha : ∀ p ∈ P, ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a p i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {θ : ℝ} (hθ₀ : 0 ≤ θ)
    (hθ₁ : θ < 1) (hθS : (1 - θ) * ∑ p ∈ P, ∑ i, |a p i| ≤ c / 8) :
    ∃ r > 0, ∀ p ∈ P,
      (∀ x ∈ ball p r, ∑ i, (θ * a p i * (x i - p i)) ^ 2 ≤
        ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2 ∧
        ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
          if i = j then θ * a p i else 0| ≤ c / 4) ∧
      ∀ q ∈ P, p ≠ q → 2 * r ≤ dist p q := by
  -- Every small enough radius works.
  refine ((?_ : ∀ᶠ r in 𝓝[>] (0 : ℝ), _).and self_mem_nhdsWithin).exists.imp
    fun r hr ↦ ⟨hr.2, hr.1⟩
  rw [eventually_all_finset]
  intro p hp
  refine Eventually.and ?_ ?_
  · obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
      (eventually_sum_mul_sq_le_and_sum_sum_abs_sub_le hf.contDiffAt (hP p hp) (ha p hp) hc
        (hca p hp) hθ₀ hθ₁ (η := c / 8) (by positivity))
    -- The cost of the weakening at `p` is at most that over all of `P`.
    have he : (1 - θ) * ∑ i, |a p i| ≤ c / 8 :=
      (mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun p ↦ ∑ i, |a p i|)
        (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hp) (by linarith)).trans hθS
    filter_upwards [Ioo_mem_nhdsGT hε] with r hr x hx
    have hx := hball x (ball_subset_ball hr.2.le hx)
    exact ⟨hx.1, by linarith [hx.2]⟩
  · rw [eventually_all_finset]
    intro q _
    by_cases hpq : p = q
    · exact Eventually.of_forall fun _ h ↦ absurd hpq h
    · filter_upwards [Ioo_mem_nhdsGT (half_pos (dist_pos.2 hpq))] with r hr _
      linarith [hr.2]

/-- The gap at one critical point in a degree `m` that is not its Morse index: let `c ≤ |aᵢ|` for
every `i`, with `0 < c`, and `0 ≤ t`. If the form `ψ` of degree `m` is supported where `f` satisfies
the hypotheses of the gap near the weakened model `θ a`, with `7/8 ≤ θ` and error at most `c / 4`,
then its energy is at least `3 t c / 2` times its squared norm. -/
private theorem three_div_two_mul_mul_integral_le_of_card_ne
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {ψ : (ι → ℝ) → Finset ι → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) {m : ℕ} (hψm : ∀ x s, ψ x s ≠ 0 → s.card = m) {a p : ι → ℝ}
    (hm : (Finset.univ.filter fun i ↦ a i < 0).card ≠ m) {c θ e t : ℝ}
    (hca : ∀ i, c ≤ |a i|) (hc : 0 < c) (hθ₀ : 7 / 8 ≤ θ) (he : e ≤ c / 4) (ht : 0 ≤ t)
    (hdf : ∀ x, ψ x ≠ 0 →
      ∑ i, (θ * a i * (x i - p i)) ^ 2 ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    (hH : ∀ x, ψ x ≠ 0 → ∑ i, ∑ j,
      |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) -
        if i = j then θ * a i else 0| ≤ e) :
    3 / 2 * t * c * ∫ x, ∑ s, ψ x s ^ 2 ≤
      ∫ x, ∑ s, euclideanWittenLaplacian f t ψ x s * ψ x s := by
  have hθ : 0 < θ := by linarith
  have hloc := two_mul_mul_integral_sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    (a := fun i ↦ θ * a i) (p := p) (c := θ * c) ht
    (fun i ↦ by
      rw [abs_mul, abs_of_pos hθ]
      exact mul_le_mul_of_nonneg_left (hca i) hθ.le)
    (fun x _ ↦ hf.contDiffAt) hψ hψc hdf hH
  -- In degree `m`, the component at `{i | θ aᵢ < 0} = {i | aᵢ < 0}` vanishes.
  have hfilt : (Finset.univ.filter fun i ↦ θ * a i < 0) = Finset.univ.filter fun i ↦ a i < 0 := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h' <;> nlinarith
  simp only [hfilt, sum_erase_sq_eq_sum_sq_of_card_ne hψm hm] at hloc
  have hN : 0 ≤ ∫ x, ∑ s, ψ x s ^ 2 :=
    integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  -- The gap `2 t θ c ≥ 7 t c / 4` of the model minus the error `t e ≤ t c / 4`.
  have hcoef : 3 / 2 * t * c ≤ 2 * t * (θ * c) - t * e := by
    nlinarith [mul_nonneg (mul_nonneg ht (sub_nonneg.2 hθ₀)) hc.le, mul_nonneg ht (sub_nonneg.2 he)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef hN]

/-- **The gap of the Witten Laplacian in a degree that is no Morse index, for nondegenerate
critical points.** Let `f` be a `C²` function on `ℝ^ι` and `P` a finite set of critical points of
`f` at which the Hessian is diagonal, `∑ᵢ a p i vᵢ wᵢ`, with every `|a p i| ≥ c > 0`, so that the
Morse index of `p` is the number of negative `a p i`. Suppose that every critical point of `f`
within distance `ρ` of `P` lies in `P`, and that at distance more than `ρ` from `P` the gradient
of `f` is bounded below, `|df|² ≥ c₀ > 0`, and its Hessian bounded above, `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h`.
If `m` is not the Morse index of any `p ∈ P`, then for all large `t` the quadratic form of the
Witten Laplacian is at least `t c ‖φ‖²` on compactly supported `C²` forms `φ` of degree `m`. -/
theorem exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)}
    (hP : ∀ p ∈ P, fderiv ℝ f p = 0) {a : (ι → ℝ) → ι → ℝ}
    (ha : ∀ p ∈ P, ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a p i * v i * w i)
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {ρ : ℝ}
    (hcrit : ∀ x, fderiv ℝ f x = 0 → (∃ p ∈ P, dist x p ≤ ρ) → x ∈ P) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdf : ∀ x, (∀ p ∈ P, ρ < dist x p) → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {h : ℝ} (hh : ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    {m : ℕ} (hm : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card ≠ m) :
    ∃ T, ∀ t, T ≤ t → ∀ φ : (ι → ℝ) → Finset ι → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∀ x s, φ x s ≠ 0 → s.card = m) →
      t * c * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  -- Weaken the models to `θ a p`, at the cost `(1 - θ) ∑ᵢ |a p i| ≤ c / 8` in the Hessian, and
  -- localize at a scale `r` on which the Taylor estimates hold.
  obtain ⟨θ, hθ₀, hθ₁, hθS⟩ := exists_le_lt_one_mul_le (S := ∑ p ∈ P, ∑ i, |a p i|)
    (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hc
  obtain ⟨r, hr0, hrQ⟩ :=
    exists_pos_forall_mem_ball_and_two_mul_le_dist hf hP ha hc hca (by linarith) hθ₁ hθS
  obtain ⟨J₀, J, hJ₀, hJ, hJ1, hJr, hJ₀ρ, hJ₀c, hJc⟩ := exists_sq_add_sum_sq_eq_one
    (half_pos hr0) (half_lt_self hr0) fun p hp q hq hpq ↦ (hrQ p hp).2 q hq hpq
  replace hJ₀ : ContDiff ℝ 2 J₀ := hJ₀.of_le (by simp)
  replace hJ : ∀ p, ContDiff ℝ 2 (J p) := fun p ↦ (hJ p).of_le (by simp)
  obtain ⟨c₁, hc₁, h₁, hb⟩ :=
    exists_pos_forall_le_sum_fderiv_apply_single_sq_and_le hf hcrit hc₀ hdf hh (half_pos hr0)
  obtain ⟨K₀, hK₀⟩ :=
    (hJ₀.of_le one_le_two).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv hJ₀c
  choose K hK using fun p ↦
    ((hJ p).of_le one_le_two).exists_forall_sum_fderiv_single_sq_le_of_hasCompactSupport_fderiv
      ((hJc p).fderiv (𝕜 := ℝ))
  refine ⟨max (max ((3 / 2 * c + h₁) / c₁) (2 * (K₀ + ∑ p ∈ P, K p) / c)) 0,
    fun t ht φ hφ hφc hφm ↦ ?_⟩
  have ht₀ : 0 ≤ t := (le_max_right _ _).trans ht
  have ht₁ : 3 / 2 * c + h₁ ≤ t * c₁ :=
    (div_le_iff₀ hc₁).1 ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  have ht₂ : 2 * (K₀ + ∑ p ∈ P, K p) ≤ t * c :=
    (div_le_iff₀ hc).1 ((le_max_right _ _).trans ((le_max_left _ _).trans ht))
  -- IMS localization, with the bound `3 t c / 2` at every piece.
  have key := sub_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_sq_add_sum_sq_eq_one
    (t := t) (κ := 3 / 2 * t * c) (fun x _ ↦ hf.contDiffAt) (fun x _ ↦ hJ₀.contDiffAt)
    (fun p _ x _ ↦ (hJ p).contDiffAt) hφ hφc (fun x _ ↦ hJ1 x)
    (fun x _ ↦ add_le_add (hK₀ x) (Finset.sum_le_sum fun p (_ : p ∈ P) ↦ hK p x)) ?_
    fun p hp ↦ ?_
  · have hN : 0 ≤ ∫ x, ∑ s, φ x s ^ 2 :=
      integral_nonneg fun x ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    nlinarith
  · -- Away from `P`, the potential `t² c₁ - t h₁` is at least `3 t c / 2`.
    rw [show 3 / 2 * t * c = t * (3 / 2 * c) by ring]
    exact mul_mul_integral_sum_sq_le_integral_sum_euclideanWittenLaplacian_mul_of_add_le_mul
      (fun x _ ↦ hf.contDiffAt) (hJ₀.smul hφ) hφc.smul_left
      (fun x hx ↦ (hb x (hJ₀ρ x (Function.support_smul_subset_left J₀ φ hx))).1)
      (fun x hx ↦ (hb x (hJ₀ρ x (Function.support_smul_subset_left J₀ φ hx))).2) ht₀ ht₁
  · -- Near `p`, the gap of the weakened model.
    have hball : ∀ x, (J p • φ) x ≠ 0 → x ∈ ball p r := fun x hx ↦
      mem_ball.2 (hJr p x (Function.support_smul_subset_left (J p) φ hx))
    exact three_div_two_mul_mul_integral_le_of_card_ne hf ((hJ p).smul hφ) hφc.smul_left
      (fun x s hx ↦ hφm x s (right_ne_zero_of_mul hx)) (hm p hp) (hca p hp) hc hθ₀ le_rfl ht₀
      (fun x hx ↦ ((hrQ p hp).1 x (hball x hx)).1) (fun x hx ↦ ((hrQ p hp).1 x (hball x hx)).2)

/-- **The gap of the Witten Laplacian in a degree that is no Morse index, for exact quadratic
models.** Let `f` be a `C²` function on `ℝ^ι` and `P` a finite set of points. Suppose that on the
ball of radius `r` around each `p ∈ P`, `f` is the quadratic model
`y ↦ f p + ∑ᵢ a p i (yᵢ - pᵢ)² / 2` with every `|a p i| ≥ c > 0`, so that `p` is a nondegenerate
critical point whose Morse index is the number of negative `a p i`, and that outside the balls of
radius `ρ < r` around the points of `P`, `|df|² ≥ c₀ > 0` and `∑_{i,j} |∂ᵢ∂ⱼf| ≤ h`. If `m` is not
the Morse index of any `p ∈ P`, then for all large `t` the quadratic form of the Witten Laplacian
is at least `t c ‖φ‖²` on compactly supported `C²` forms `φ` of degree `m`. This is the case of
`exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero` in
which `p` is the only critical point of `f` in the ball of radius `r` around `p`. -/
theorem exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul
    {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {P : Finset (ι → ℝ)} {ρ r : ℝ} (hr : 0 < r)
    (hρr : ρ < r) {a : (ι → ℝ) → ι → ℝ}
    (hfa : ∀ p ∈ P, EqOn f (fun y ↦ f p + diagonalQuadratic (a p) (y - p)) (ball p r))
    {c : ℝ} (hc : 0 < c) (hca : ∀ p ∈ P, ∀ i, c ≤ |a p i|) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdf : ∀ x, (∀ p ∈ P, ρ < dist x p) → c₀ ≤ ∑ i, fderiv ℝ f x (Pi.single i 1) ^ 2)
    {h : ℝ} (hh : ∀ x, (∀ p ∈ P, ρ < dist x p) →
      ∑ i, ∑ j, |fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)| ≤ h)
    {m : ℕ} (hm : ∀ p ∈ P, (Finset.univ.filter fun i ↦ a p i < 0).card ≠ m) :
    ∃ T, ∀ t, T ≤ t → ∀ φ : (ι → ℝ) → Finset ι → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∀ x s, φ x s ≠ 0 → s.card = m) →
      t * c * ∫ x, ∑ s, φ x s ^ 2 ≤ ∫ x, ∑ s, euclideanWittenLaplacian f t φ x s * φ x s := by
  -- On the ball of radius `r` around `p`, `f` is the translated quadratic model.
  have hfe : ∀ p ∈ P, ∀ x ∈ ball p r, f =ᶠ[𝓝 x] fun y ↦ f p + diagonalQuadratic (a p) (y - p) :=
    fun p hp x hx ↦ eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) (hfa p hp)
  have hd : ∀ p ∈ P, ∀ x ∈ ball p r, ∀ i, fderiv ℝ f x (Pi.single i 1) = a p i * (x i - p i) :=
    fun p hp x hx i ↦ by
      rw [(hfe p hp x hx).fderiv_eq, fderiv_const_add,
        fderiv_diagonalQuadratic_comp_sub_apply_single]
  have hP : ∀ p ∈ P, fderiv ℝ f p = 0 := fun p hp ↦
    ContinuousLinearMap.pi_ext_one fun i ↦ by simp [hd p hp p (mem_ball_self hr) i]
  have ha : ∀ p ∈ P, ∀ v w, fderiv ℝ (fderiv ℝ f) p v w = ∑ i, a p i * v i * w i :=
    fun p hp v w ↦ by
      have hmod : fderiv ℝ (fun y ↦ f p + diagonalQuadratic (a p) (y - p)) =
          fun y ↦ fderiv ℝ (diagonalQuadratic (a p)) (y - p) :=
        funext fun y ↦ by rw [fderiv_const_add, fderiv_comp_sub]
      rw [(hfe p hp p (mem_ball_self hr)).fderiv.fderiv_eq, hmod, fderiv_comp_sub,
        fderiv_fderiv_diagonalQuadratic_apply]
  -- The model has no critical point in the ball other than its centre.
  have hcrit : ∀ x, fderiv ℝ f x = 0 → (∃ p ∈ P, dist x p ≤ ρ) → x ∈ P := by
    rintro x hx ⟨p, hp, hxp⟩
    convert hp
    funext i
    have hi := hd p hp x (mem_ball.2 (hxp.trans_lt hρr)) i
    rw [hx, zero_apply, eq_comm, mul_eq_zero, sub_eq_zero] at hi
    exact hi.resolve_left fun h₀ ↦ by linarith [hca p hp i, abs_eq_zero.2 h₀]
  exact exists_forall_mul_integral_le_integral_sum_euclideanWittenLaplacian_mul_of_fderiv_eq_zero
    hf hP ha hc hca hcrit hc₀ hdf hh hm

end TauCeti
