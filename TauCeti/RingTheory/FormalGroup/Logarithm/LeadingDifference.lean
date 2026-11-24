/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic

/-!
# Comparing formal group laws through their logarithms

Over a `ℚ`-algebra a formal group law is determined by its logarithm, `F(X, Y) =
exp_F(log_F(X) + log_F(Y))`. This file makes the comparison quantitative in the lowest degree where
two laws differ. If `log_F - log_G` has order at least `n`, then so does `F - G`
(`FormalGroup.le_order_sub_of_le_order_log_sub`). If moreover `log_F - log_G = a Xⁿ` up to terms
of degree greater than `n`, then the degree-`n` part of `F - G` is
`-a ((X + Y)ⁿ - Xⁿ - Yⁿ)` (`FormalGroup.homogeneousComponent_sub_of_log_sub`).

Both follow from the identity `log_G(F) - log_G(G) = log_G(F) - log_G(X) - log_G(Y)`, the additivity
defect of `log_G` along `F`, which equals minus the additivity defect of `log_F - log_G` along `F`
since `log_F` is additive along `F`.

## Main results

* `FormalGroup.le_order_sub_of_le_order_log_sub`: laws whose logarithms agree below degree `n`
  agree below degree `n`.
* `FormalGroup.homogeneousComponent_sub_of_log_sub`: if `log_F - log_G = a Xⁿ + O(Xⁿ⁺¹)`, the
  degree-`n` part of `F - G` is `-a ((X + Y)ⁿ - Xⁿ - Yⁿ)`.
-/

public section

noncomputable section

open MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] [Algebra ℚ R] (F G : FormalGroup R)

/-- The difference `log_G(F) - log_G(G)` is minus the additivity defect of `log_F - log_G`
along `F`. -/
theorem subst_log_sub_subst_log :
    PowerSeries.subst F.toPowerSeries G.log - PowerSeries.subst G.toPowerSeries G.log =
      -F.homDefect 𝔾ₐ (F.log - G.log) := by
  rw [homDefect_𝔾ₐ_sub, homDefect_𝔾ₐ, homDefect_𝔾ₐ, F.subst_toPowerSeries_log,
    G.subst_toPowerSeries_log]
  ring

/-- **Laws with close logarithms are close.** If `log_F - log_G` has order at least `n`, so does
`F - G`. -/
theorem le_order_sub_of_le_order_log_sub {n : ℕ} (h : (n : ℕ∞) ≤ (F.log - G.log).order) :
    (n : ℕ∞) ≤ (F.toPowerSeries - G.toPowerSeries).order := by
  have hF := PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hG := PowerSeries.HasSubst.of_constantCoeff_zero G.zero_constantCoeff
  have hlog : (n : ℕ∞) ≤ (PowerSeries.subst F.toPowerSeries G.log -
      PowerSeries.subst G.toPowerSeries G.log).order := by
    rw [subst_log_sub_subst_log, order_neg]
    exact F.le_order_homDefect_𝔾ₐ h
  have hexp : ((1 : ℕ) : ℕ∞) ≤ MvPowerSeries.order (G.exp : MvPowerSeries Unit R) := by
    rw [Nat.cast_one]
    exact one_le_order_iff_constCoeff_eq_zero.mpr G.constantCoeff_exp
  -- apply `exp_G`, which has order at least `1`, to `log_G(F)` and `log_G(G)`
  have h₀ (x : MvPowerSeries (Fin 2) R) (hx : constantCoeff x = 0) :
      constantCoeff (PowerSeries.subst x G.log) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hx _ G.constantCoeff_log
  have := le_order_subst_sub_subst (k := 1) (n := n) hexp
    (a := fun _ ↦ PowerSeries.subst F.toPowerSeries G.log)
    (b := fun _ ↦ PowerSeries.subst G.toPowerSeries G.log)
    (hasSubst_of_constantCoeff_zero fun _ ↦ h₀ _ F.zero_constantCoeff)
    (hasSubst_of_constantCoeff_zero fun _ ↦ h₀ _ G.zero_constantCoeff)
    (fun _ ↦ h₀ _ F.zero_constantCoeff) (fun _ ↦ h₀ _ G.zero_constantCoeff) fun _ ↦ hlog
  rwa [← PowerSeries.subst_def, ← PowerSeries.subst_def, G.subst_subst_log_exp hF,
    G.subst_subst_log_exp hG, Nat.add_sub_cancel] at this

/-- **The leading difference of two laws, read off their logarithms.** If
`log_F - log_G = a Xⁿ` up to terms of degree greater than `n ≠ 0`, the degree-`n` part of `F - G`
is `-a ((X + Y)ⁿ - Xⁿ - Yⁿ)`. -/
theorem homogeneousComponent_sub_of_log_sub {n : ℕ} (hn : n ≠ 0) (a : R)
    (h : ((n + 1 : ℕ) : ℕ∞) ≤ (F.log - G.log - a • PowerSeries.X ^ n).order) :
    homogeneousComponent n (F.toPowerSeries - G.toPowerSeries) =
      -((a • ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n - MvPolynomial.X 0 ^ n -
        MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) : MvPowerSeries (Fin 2) R) := by
  set d := F.log - G.log - a • PowerSeries.X ^ n
  have hd₀ : PowerSeries.constantCoeff d = 0 :=
    PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp (le_trans (by simp) h)
  have hXn : (n : ℕ∞) ≤ (a • PowerSeries.X ^ n : PowerSeries R).order :=
    PowerSeries.nat_le_order _ _ fun k hk ↦ by simp [PowerSeries.coeff_X_pow, hk.ne]
  have hlog : (n : ℕ∞) ≤ (F.log - G.log).order := by
    rw [← sub_add_cancel (F.log - G.log) (a • PowerSeries.X ^ n)]
    exact le_trans (le_min (le_trans (by exact_mod_cast n.le_succ) h) hXn)
      (PowerSeries.min_order_le_order_add _ _)
  have hFG := F.le_order_sub_of_le_order_log_sub G hlog
  -- in degree `n`, `log_G(F) - log_G(G)` is `F - G`, since `log_G(T) = T + ⋯`
  have hlin : homogeneousComponent n (F.toPowerSeries - G.toPowerSeries) =
      homogeneousComponent n
        (PowerSeries.subst F.toPowerSeries G.log - PowerSeries.subst G.toPowerSeries G.log) := by
    ext e
    simp only [coeff_homogeneousComponent]
    split_ifs with he
    · rw [PowerSeries.subst_def, PowerSeries.subst_def,
        MvPowerSeries.coeff_subst_sub_subst_of_degree_le G.log (fun _ ↦ F.zero_constantCoeff)
          (fun _ ↦ G.zero_constantCoeff) (fun _ ↦ hFG) he.le]
      simp [← PowerSeries.coeff_def]
    · rfl
  have hhigh : homogeneousComponent n (F.homDefect 𝔾ₐ d) = 0 :=
    homogeneousComponent_of_lt_order_eq_zero <| lt_of_lt_of_le (by exact_mod_cast n.lt_succ_self)
      (F.le_order_homDefect_𝔾ₐ h)
  have hstep := F.homogeneousComponent_homDefect_add_sub (G := 𝔾ₐ) hd₀ hn a
  rw [map_sub, hhigh, sub_zero, sub_add_cancel] at hstep
  rw [hlin, subst_log_sub_subst_log, map_neg, hstep]

end FormalGroup
