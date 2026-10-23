/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished

/-!
# Radius selection for distinguished overconvergent series

Let `K` be a complete ultrametric normed field and write the Monsky–Washnitzer algebra in the
variables `Option σ` as `W = K⟨X, Y⟩†`, with `Y = X none`. Separating `Y` writes a series as
`g = ∑ₘ gₘ Yᵐ` with coefficients `gₘ` in the variables `σ`. At unit radius this is
`TauCeti.Huber.restrictedOptionEquiv`, and `g` is `Y`-distinguished of degree `s` when this
series over the Tate algebra in `σ` is `TauCeti.PowerSeries.IsDistinguished` of degree `s` at
radius `1` with a unit coefficient `g_s`.

Weierstrass division by such a `g` must stay inside `W`. It therefore has to take place over a
ring of series restricted at some radius `ρ > 1` in the variables `σ`, at some radius `r > 1` in
`Y`. Distinguishedness does not persist to a common radius `ρ = r > 1`: `Y + X²` is
`Y`-distinguished of degree `1` at unit radius, but `‖X²‖_ρ = ρ² > ρ = ‖1‖_ρ ρ` for all `ρ > 1`.
This file proves that unequal radii work. For every `g` as above there are radii
`1 < ρ ≤ r`, as close to `1` as desired, such that `g` is restricted at `r` and
`∑ₘ gₘ Yᵐ` is distinguished of degree `s` at radius `r` over the series restricted at `ρ`, with
`g_s` a unit there.

## Main results

* `TauCeti.Dagger.exists_isDistinguished_isUnit_of_isDistinguished_one`: radius selection for a
  `Y`-distinguished overconvergent series.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.3.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries
open TauCeti.MvPowerSeries (isRestricted_of_le)

variable {σ K : Type*}

section Field

variable [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- The unit-radius hypotheses of radius selection as bounds on the coefficients of `g`. Let `N`
be the norm of the constant term of `g_s`. Then `N > 0`, every coefficient of `g` has norm at
most `N`, and the coefficients in `Y`-degrees above `s`, as well as the nonconstant ones in
`Y`-degree `s`, have norm less than `N`. -/
private theorem norm_coeff_le_of_isDistinguished_one {g : washnitzerAlgebra (Option σ) K}
    {s : ℕ} (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (washnitzerAlgebra.toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (washnitzerAlgebra.toTate _ K g) : PowerSeries Tate))) :
    0 < ‖coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K)‖ ∧
      (∀ u, ‖coeff u (g : MvPowerSeries (Option σ) K)‖ ≤
        ‖coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K)‖) ∧
      ∀ u, s < u none ∨ u none = s ∧ u.some ≠ 0 → ‖coeff u (g : MvPowerSeries (Option σ) K)‖ <
        ‖coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K)‖ := by
  set Gt := (Huber.restrictedOptionEquiv (washnitzerAlgebra.toTate _ K g) : PowerSeries Tate)
  have hGt (m : ℕ) (t : σ →₀ ℕ) : coeff t (↑(PowerSeries.coeff m Gt) : MvPowerSeries σ K) =
      coeff (t.optionElim m) (g : MvPowerSeries (Option σ) K) := by
    rw [Huber.coeff_restrictedOptionEquiv (c := fun _ ↦ 1), coeff_coeff_optionEquivLeft,
      washnitzerAlgebra.coe_toTate]
  have hone (t : σ →₀ ℕ) : t.prod (fun _ n ↦ (1 : ℝ) ^ n) = 1 := by
    rw [Finsupp.prod_pow_eq_pow_degree, one_pow]
  obtain ⟨ha0, hlt⟩ := (isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt _).1 hu
  have hcN : constantCoeff (↑(PowerSeries.coeff s Gt) : MvPowerSeries σ K) =
      coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K) := by
    rw [← coeff_zero_eq_constantCoeff_apply, hGt]
  -- The Gauss norm of `Gt` is the norm `N` of the constant term of its coefficient `g_s`.
  have hgauss : Gt.gaussNorm norm 1 =
      ‖coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K)‖ := by
    rw [← hg.norm_coeff_mul_pow_eq, one_pow, mul_one,
      norm_eq_norm_constantCoeff_of_norm_coeff_mul_prod_le fun t ht ↦ (hlt t ht).le, hcN]
  have hcoeff_le (m : ℕ) (t : σ →₀ ℕ) :
      ‖coeff (t.optionElim m) (g : MvPowerSeries (Option σ) K)‖ ≤ ‖PowerSeries.coeff m Gt‖ := by
    simpa [← hGt, hone] using MvPowerSeries.norm_coeff_mul_prod_le (PowerSeries.coeff m Gt) t
  refine ⟨norm_pos_iff.2 (hcN ▸ ha0), fun u ↦ ?_, fun u hu ↦ ?_⟩ <;>
    rw [← Finsupp.optionElim_some u]
  · exact (hcoeff_le _ _).trans (by
      simpa [hgauss] using PowerSeries.le_gaussNorm norm 1 Gt hg.hasGaussNorm (u none))
  · rcases hu with hu | ⟨hu, hu0⟩
    · refine (hcoeff_le _ _).trans_lt ?_
      simpa [hgauss] using hg.norm_coeff_mul_pow_lt _ hu
    · rw [hu, ← hGt, ← hcN]
      simpa [hone] using hlt _ hu0

/-- **Radius selection for distinguished overconvergent series.** Let `g` be an overconvergent
series in the variables `Option σ` which, as a series in `Y = X none` over the Tate algebra in the
variables `σ`, is distinguished of degree `s` at radius `1` with a unit coefficient `g_s`. Then for
every `ρ₀ > 1` there are radii `1 < ρ ≤ r ≤ ρ₀` such that `g` is restricted at `r`, and its
coefficient slices `gₘ`, which are restricted at `ρ`, form a series `G = ∑ₘ gₘ Yᵐ` over the
series restricted at `ρ` that is distinguished of degree `s` at radius `r`, with `g_s` a unit.

This is the radius selection behind Weierstrass division by `g` inside the Monsky–Washnitzer
algebra. A single common radius `ρ = r > 1` does not suffice in general. -/
theorem exists_isDistinguished_isUnit_of_isDistinguished_one {g : washnitzerAlgebra (Option σ) K}
    {s : ℕ} (hg : PowerSeries.IsDistinguished 1 s
      (Huber.restrictedOptionEquiv (washnitzerAlgebra.toTate _ K g) : PowerSeries Tate))
    (hu : IsUnit (PowerSeries.coeff s
      (Huber.restrictedOptionEquiv (washnitzerAlgebra.toTate _ K g) : PowerSeries Tate)))
    {ρ₀ : ℝ} (hρ₀ : 1 < ρ₀) :
    ∃ (ρ : ℝ) (_ : Fact (0 < ρ)) (r : ℝ), 1 < ρ ∧ ρ ≤ r ∧ r ≤ ρ₀ ∧
      IsRestricted (fun _ ↦ r) (g : MvPowerSeries (Option σ) K) ∧
      ∃ G : PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)),
        (∀ m, (↑(PowerSeries.coeff m G) : MvPowerSeries σ K) =
          PowerSeries.coeff m (optionEquivLeft σ K (g : MvPowerSeries (Option σ) K))) ∧
        PowerSeries.IsDistinguished r s G ∧ IsUnit (PowerSeries.coeff s G) := by
  -- The proof scales nothing: with `N = ‖g_s‖ = ‖g_s(0)‖`, the unit-radius hypotheses say that
  -- every coefficient of `g` has norm at most `N`, and strictly less than `N` in `Y`-degrees
  -- above `s` and at the nonconstant terms of `g_s`. The strict bounds persist to a radius
  -- `r > 1`. The coefficients in `Y`-degrees below `s` are then made smaller than `N r`, at a
  -- radius `ρ ≤ r` chosen after `r`.
  obtain ⟨hN, hle, hlt⟩ := norm_coeff_le_of_isDistinguished_one hg hu
  set N := ‖coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K)‖
  -- First choice: the strict bounds persist to a radius `ρ₁ > 1`.
  obtain ⟨ρ₁, hρ₁, hgρ₁, hρ₁S⟩ := exists_isRestricted_forall_mem_norm_coeff_mul_pow_lt g.2
    (S := {u | s < u none ∨ u none = s ∧ u.some ≠ 0}) hlt
  set r := min ρ₁ ρ₀
  have hr : 1 < r := lt_min hρ₁ hρ₀
  -- Second choice, depending on `r`: the coefficients in `Y`-degrees below `s` stay below `N r`.
  obtain ⟨ρ₂, hρ₂, -, hρ₂S⟩ := exists_isRestricted_forall_mem_norm_coeff_mul_pow_lt g.2
    (S := {u | u none < s}) (r := N * r) fun u _ ↦ (hle u).trans_lt (lt_mul_of_one_lt_right hN hr)
  set ρ := min ρ₂ r
  have hρ : 1 < ρ := lt_min hρ₂ hr
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have : Fact (0 < ρ) := ⟨hρ0⟩
  have hρr : ρ ≤ r := min_le_right _ _
  have hgρ : IsRestricted (fun _ ↦ ρ) (g : MvPowerSeries (Option σ) K) :=
    isRestricted_of_le hgρ₁ (fun _ ↦ hρ0.le) fun _ ↦ hρr.trans (min_le_left _ _)
  let G : PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)) :=
    PowerSeries.mk fun m ↦ ⟨_, Huber.isRestricted_coeff_optionEquivLeft hρ0 hgρ m⟩
  have hG (m : ℕ) : (↑(PowerSeries.coeff m G) : MvPowerSeries σ K) =
      PowerSeries.coeff m (optionEquivLeft σ K (g : MvPowerSeries (Option σ) K)) := by
    simp [G]
  have hGcoeff (m : ℕ) (t : σ →₀ ℕ) : coeff t (↑(PowerSeries.coeff m G) : MvPowerSeries σ K) =
      coeff (t.optionElim m) (g : MvPowerSeries (Option σ) K) := by
    rw [hG, coeff_coeff_optionEquivLeft]
  have hGs0 : constantCoeff (↑(PowerSeries.coeff s G) : MvPowerSeries σ K) =
      coeff ((0 : σ →₀ ℕ).optionElim s) (g : MvPowerSeries (Option σ) K) := by
    rw [← coeff_zero_eq_constantCoeff_apply, hGcoeff]
  -- In `Y`-degree `s` the constant term is the only coefficient reaching `N`.
  have hs (t : σ →₀ ℕ) (ht : t ≠ 0) :
      ‖coeff t (↑(PowerSeries.coeff s G) : MvPowerSeries σ K)‖ * t.prod (fun _ n ↦ ρ ^ n) < N := by
    rw [hGcoeff, Finsupp.prod_pow_eq_pow_degree]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      (hρ₁S _ (Or.inr ⟨by simp, by simpa using ht⟩))
    exact Finsupp.pow_degree_le_pow_degree_optionElim hρ0.le (hρr.trans (min_le_left _ _)) hρ₁.le
      t s
  -- In every other `Y`-degree `m` the weighted coefficients are below `N r ^ s`.
  have hm (m : ℕ) (hm : m ≠ s) (t : σ →₀ ℕ) :
      ‖coeff t (↑(PowerSeries.coeff m G) : MvPowerSeries σ K)‖ * t.prod (fun _ n ↦ ρ ^ n) *
        r ^ m < N * r ^ s := by
    rw [hGcoeff, Finsupp.prod_pow_eq_pow_degree]
    set w := ‖coeff (t.optionElim m) (g : MvPowerSeries (Option σ) K)‖
    rcases hm.lt_or_gt with hm | hm
    · have hw : w * ρ ^ t.degree < N * r := by
        refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
          (by simpa using hρ₂S _ (by simpa using hm))
        exact Finsupp.pow_degree_le_pow_degree_optionElim hρ0.le (min_le_left _ _) hρ₂.le t m
      calc w * ρ ^ t.degree * r ^ m < N * r * r ^ m :=
            mul_lt_mul_of_pos_right hw (pow_pos (zero_lt_one.trans hr) _)
        _ = N * r ^ (m + 1) := by ring
        _ ≤ N * r ^ s := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr.le hm) hN.le
    · have hρ₁w : ρ ^ t.degree * r ^ m ≤ ρ₁ ^ (t.optionElim m).degree := by
        rw [Finsupp.degree_optionElim, pow_add, mul_comm]
        exact mul_le_mul (pow_le_pow_left₀ (zero_lt_one.trans hr).le (min_le_left _ _) _)
          (pow_le_pow_left₀ hρ0.le (hρr.trans (min_le_left _ _)) _) (by positivity)
          (by positivity)
      calc w * ρ ^ t.degree * r ^ m ≤ w * ρ₁ ^ (t.optionElim m).degree := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hρ₁w (norm_nonneg _)
        _ < N := hρ₁S _ (Or.inl (by simpa using hm))
        _ ≤ N * r ^ s := le_mul_of_one_le_right hN.le (one_le_pow₀ hr.le)
  obtain ⟨hd, hunit⟩ := MvPowerSeries.isDistinguished_isUnit_of_norm_coeff_lt (zero_lt_one.trans hr)
    (by rw [hGs0]; exact norm_pos_iff.1 hN) (by rw [hGs0]; exact hs) (by rw [hGs0]; exact hm)
  exact ⟨ρ, this, r, hρ, hρr, min_le_right _ _,
    isRestricted_of_le hgρ₁ (fun _ ↦ (zero_lt_one.trans hr).le) fun _ ↦ min_le_left _ _, G, hG,
    hd, hunit⟩

end Field

end TauCeti.Dagger
