/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.RingTheory.PowerSeries.GaussNorm
public import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Weighted coefficient bounds for products, powers and substitutions of power series

Let `R` be an ultrametric seminormed commutative ring and `c : σ → ℝ` nonnegative radii. The
weighted coefficient norms `‖coeff n f‖ * ∏ᵢ cᵢ ^ nᵢ` of a multivariate power series `f` are the
terms whose supremum is Mathlib's Gauss norm `MvPowerSeries.gaussNorm norm c f`. This file bounds
them for products `f * g`, for powers `g ^ j` and for substitutions `f(g)` of a series `g` into a
series `f` in one variable: if the weighted coefficients of `g` are at most `ρ` and
`‖fⱼ‖ ρ ^ j ≤ s` for every `j`, then those of `f(g)` are at most `s`.

The bounds hold coefficient by coefficient, by the ultrametric inequality applied to the
coefficient formulas. The coefficient at `n` of a product, a power or a substitution involves only
coefficients at exponents `m ≤ n`, so each bound at `n` assumes the bounds on the inputs only at
the exponents `m ≤ n`. This gives at once the forms truncated up to an exponent `κ` (all `n ≤ κ`)
and up to a total degree.

In Gauss-norm form: if `g` has a Gauss norm at `c` (its weighted coefficients are bounded), of
size at most `ρ`, and `f` has a Gauss norm at radius `ρ`, then `f(g)` has a Gauss norm at `c`, and
`‖f(g)‖_c ≤ ‖f‖_ρ`. Unlike for restricted series, the weighted coefficients need not tend to
zero.

## Main results

* `MvPowerSeries.norm_coeff_mul_mul_prod_le`: the weighted coefficients of `f * g` at `n` are at
  most `r * s` when those of `f` and `g` at the exponents `m ≤ n` are at most `r` and `s`.
* `MvPowerSeries.norm_coeff_pow_mul_prod_le`: the same for `g ^ j`, with the bound `ρ ^ j`.
* `MvPowerSeries.norm_coeff_pow_succ_mul_prod_le`: the positive-power bound without an assumption
  on `‖1‖`.
* `PowerSeries.norm_coeff_subst_mul_prod_le`: the same for the substitution `f(g)`.
* `PowerSeries.hasGaussNorm_subst`, `PowerSeries.gaussNorm_subst_le`: the Gauss-norm form.

## Provenance

`MvPowerSeries.norm_coeff_pow_mul_prod_le` and `PowerSeries.norm_coeff_subst_mul_prod_le` are
adapted from `New.norm_coeff_pow_le` and `New.norm_coeff_subst_le` (file
`src/Lib/General/Algebra/SeriesBounds.lean`) in grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic, PBC), which treat `ℂ_[p]` at radius `1`, with the bounds
read up to a total degree; the generalisation to ultrametric seminormed rings, to arbitrary radii
and to the truncation below an exponent, the product bound and the Gauss-norm form are new here.

## References

* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §5.1.
-/

public section

namespace MvPowerSeries

variable {σ R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- If the weighted coefficients `‖coeff m f‖ * ∏ᵢ cᵢ ^ mᵢ` of `f` are at most `r` and those of `g`
at most `s` for `m ≤ n`, then the weighted coefficient of `f * g` at `n` is at most `r * s`. -/
theorem norm_coeff_mul_mul_prod_le (hc : 0 ≤ c) {f g : MvPowerSeries σ R} {n : σ →₀ ℕ}
    {r s : ℝ} (hf : ∀ m ≤ n, ‖coeff m f‖ * m.prod (c · ^ ·) ≤ r)
    (hg : ∀ m ≤ n, ‖coeff m g‖ * m.prod (c · ^ ·) ≤ s) :
    ‖coeff n (f * g)‖ * n.prod (c · ^ ·) ≤ r * s := by
  classical
  have hw (t : σ →₀ ℕ) : 0 ≤ t.prod (c · ^ ·) :=
    Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _
  have hr : 0 ≤ r := (mul_nonneg (norm_nonneg _) (hw 0)).trans (hf 0 zero_le)
  rw [coeff_mul]
  -- By the ultrametric inequality one term of the sum over the antidiagonal dominates.
  obtain ⟨x, hx, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    ⟨(n, 0), Finset.mem_antidiagonal.2 (add_zero n)⟩ fun x ↦ coeff x.1 f * coeff x.2 g
  rw [Finset.mem_antidiagonal] at hx
  have hprod : n.prod (c · ^ ·) = x.1.prod (c · ^ ·) * x.2.prod (c · ^ ·) := by
    rw [← hx, Finsupp.prod_add_index' (fun _ ↦ pow_zero _) fun _ _ _ ↦ pow_add _ _ _]
  calc ‖∑ x ∈ Finset.antidiagonal n, coeff x.1 f * coeff x.2 g‖ * n.prod (c · ^ ·)
      ≤ ‖coeff x.1 f‖ * ‖coeff x.2 g‖ * (x.1.prod (c · ^ ·) * x.2.prod (c · ^ ·)) := by
        rw [hprod]
        gcongr
        · exact mul_nonneg (hw _) (hw _)
        · exact hle.trans (norm_mul_le _ _)
    _ = (‖coeff x.1 f‖ * x.1.prod (c · ^ ·)) * (‖coeff x.2 g‖ * x.2.prod (c · ^ ·)) := by ring
    _ ≤ r * s := by
        gcongr
        · exact mul_nonneg (norm_nonneg _) (hw _)
        · exact hf _ (hx ▸ le_self_add)
        · exact hg _ (hx ▸ le_add_self)

/-- The bound of `norm_coeff_pow_mul_prod_le` for positive powers, which needs no assumption on
`‖1‖`. -/
theorem norm_coeff_pow_succ_mul_prod_le (hc : 0 ≤ c) {g : MvPowerSeries σ R}
    {n : σ →₀ ℕ} {ρ : ℝ} (hg : ∀ m ≤ n, ‖coeff m g‖ * m.prod (c · ^ ·) ≤ ρ) (j : ℕ) :
    ‖coeff n (g ^ (j + 1))‖ * n.prod (c · ^ ·) ≤ ρ ^ (j + 1) := by
  induction j generalizing n with
  | zero => simpa using hg n le_rfl
  | succ j ih =>
    rw [pow_succ g, pow_succ ρ]
    exact norm_coeff_mul_mul_prod_le hc (fun m hm ↦ ih fun m' hm' ↦ hg m' (hm'.trans hm)) hg

/-- If the weighted coefficients `‖coeff m g‖ * ∏ᵢ cᵢ ^ mᵢ` of `g` are at most `ρ` for `m ≤ n`,
then the weighted coefficient of `g ^ j` at `n` is at most `ρ ^ j`. -/
theorem norm_coeff_pow_mul_prod_le [NormOneClass R] (hc : 0 ≤ c) {g : MvPowerSeries σ R}
    {n : σ →₀ ℕ} {ρ : ℝ} (hg : ∀ m ≤ n, ‖coeff m g‖ * m.prod (c · ^ ·) ≤ ρ) (j : ℕ) :
    ‖coeff n (g ^ j)‖ * n.prod (c · ^ ·) ≤ ρ ^ j := by
  classical
  rcases j with _ | j
  · rw [pow_zero, pow_zero, coeff_one]
    split_ifs with h <;> simp [h]
  · exact norm_coeff_pow_succ_mul_prod_le hc hg j

end MvPowerSeries

namespace PowerSeries

variable {σ R : Type*} [SeminormedCommRing R] [IsUltrametricDist R] {c : σ → ℝ}

/-- Let the weighted coefficients `‖coeff m g‖ * ∏ᵢ cᵢ ^ mᵢ` of a substitutable series `g` be at
most `ρ` for `m ≤ n`, and let `f = ∑ fⱼ Xʲ` satisfy `‖fⱼ‖ ρ ^ j ≤ s` for every `j`. Then the
weighted coefficient of `f(g)` at `n` is at most `s`. -/
theorem norm_coeff_subst_mul_prod_le (hc : 0 ≤ c) {g : MvPowerSeries σ R} (hg : HasSubst g)
    {n : σ →₀ ℕ} {ρ s : ℝ} (hgn : ∀ m ≤ n, ‖MvPowerSeries.coeff m g‖ * m.prod (c · ^ ·) ≤ ρ)
    {f : R⟦X⟧} (hf : ∀ j, ‖coeff j f‖ * ρ ^ j ≤ s) :
    ‖MvPowerSeries.coeff n (f.subst g)‖ * n.prod (c · ^ ·) ≤ s := by
  classical
  have hw : 0 ≤ n.prod (c · ^ ·) := Finset.prod_nonneg fun i _ ↦ pow_nonneg (hc i) _
  have hs : 0 ≤ s := (mul_nonneg (norm_nonneg _) (pow_zero ρ ▸ zero_le_one)).trans (hf 0)
  rw [coeff_subst hg]
  -- The bound is preserved by sums, by the ultrametric inequality, and holds for each term.
  refine finsum_induction (fun x ↦ ‖x‖ * n.prod (c · ^ ·) ≤ s) (by simpa using hs)
    (fun x y hx hy ↦ ?_) fun j ↦ ?_
  · grw [IsUltrametricDist.norm_add_le_max, max_mul_of_nonneg _ _ hw]
    exact max_le hx hy
  rcases j with _ | j
  · rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs with h
    · simpa [h] using hf 0
    · simpa using hs
  · grw [smul_eq_mul, norm_mul_le, mul_assoc,
      MvPowerSeries.norm_coeff_pow_succ_mul_prod_le hc hgn j]
    exact hf (j + 1)

/-- If `g` is substitutable and has a Gauss norm at radii `c`, of size at most `ρ`, and `f` has a
Gauss norm at radius `ρ`, then `f(g)` has a Gauss norm at `c`. -/
theorem hasGaussNorm_subst (hc : 0 ≤ c) {g : MvPowerSeries σ R} (hg : HasSubst g)
    (hg' : MvPowerSeries.HasGaussNorm norm c g) {ρ : ℝ}
    (hgρ : MvPowerSeries.gaussNorm norm c g ≤ ρ) {f : R⟦X⟧} (hf : f.HasGaussNorm norm ρ) :
    MvPowerSeries.HasGaussNorm norm c (f.subst g) :=
  ⟨_, Set.forall_mem_range.2 fun _ ↦ norm_coeff_subst_mul_prod_le hc hg
    (fun m _ ↦ (MvPowerSeries.le_gaussNorm _ _ _ hg' m).trans hgρ)
    (fun j ↦ le_gaussNorm _ _ _ hf j)⟩

/-- If `g` is substitutable and has a Gauss norm at radii `c`, of size at most `ρ`, and `f` has a
Gauss norm at radius `ρ`, then `‖f(g)‖_c ≤ ‖f‖_ρ`. -/
theorem gaussNorm_subst_le (hc : 0 ≤ c) {g : MvPowerSeries σ R} (hg : HasSubst g)
    (hg' : MvPowerSeries.HasGaussNorm norm c g) {ρ : ℝ}
    (hgρ : MvPowerSeries.gaussNorm norm c g ≤ ρ) {f : R⟦X⟧} (hf : f.HasGaussNorm norm ρ) :
    MvPowerSeries.gaussNorm norm c (f.subst g) ≤ f.gaussNorm norm ρ :=
  ciSup_le fun _ ↦ norm_coeff_subst_mul_prod_le hc hg
    (fun m _ ↦ (MvPowerSeries.le_gaussNorm _ _ _ hg' m).trans hgρ)
    (fun j ↦ le_gaussNorm _ _ _ hf j)

end PowerSeries
