/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.Analysis.SpecificLimits.DecayIteration

/-!
# The two decay steps of Campanato's perturbation argument

In the Campanato approach to the Schauder estimates for an equation with `α`-Hölder coefficients,
a solution is compared on each ball `B_r` of radius `r ≤ R` with the solution of the problem whose
coefficients are frozen at the centre. For a quantity `φ r`, such as `∫_{B_r} ‖∇u‖²` or the square
mean oscillation `∫_{B_r} ‖∇u - (∇u)_{B_r}‖²`, this gives an inequality

`φ ρ ≤ A (ρ / r)^δ φ r + A (r^{2α} K² Φ r + D r)` whenever `0 < ρ ≤ r`,

where `δ` is the decay exponent of the frozen problem, `Φ r = ∫_{B_r} ‖∇u‖²`, `K` is the Hölder
constant of the coefficients divided by the ellipticity constant, and `D r` collects the data.
Two applications of the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` turn such inequalities into decay
estimates, provided that `K R^α ≤ M` and the data decay like `D r ≤ V (r / R)^κ`:

* **Morrey decay** (`TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add`): for
  `φ = Φ` with `δ = d`, the bound `Φ R ≤ V` and `κ = d - γ`, `γ > 0`, there is `θ ∈ (0, 1]`,
  depending only on `A`, `α`, `γ`, `d` and `M`, with `Φ ρ ≤ C V (ρ / R)^{d-γ}` for `ρ ≤ θ R`. On
  balls of radius at most `θ R` the coefficient term is a small perturbation of the decay factor.
* **Campanato decay**
  (`TauCeti.exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow`): for
  any `δ` (in the applications `δ = d + 2`) and a known Morrey bound `Φ t ≤ L V (t / R)^β` on
  `(0, θ R]`, the coefficient term is an inhomogeneity of order `(r / R)^{2α+β}`, and
  `φ ρ ≤ C V (ρ / R)^τ` for `ρ ≤ θ R` and every `τ < δ` with `τ ≤ 2α + β` and `τ ≤ κ`.

The Morrey step alone only reaches exponents `d - γ` with `γ > 0`. Combined with the
bounded-averages step `TauCeti.MeasureTheory.exists_setIntegral_ball_inter_norm_sq_le_mul_div_pow`
(Campanato decay with exponent `d + γ` keeps the averages bounded, hence gives Morrey decay with
the full exponent `d`), the two steps raise the decay exponent of the mean oscillation to `d + 2γ`
through the chain: Morrey `d - γ`, Campanato `d + γ`, Morrey `d`, Campanato `d + 2γ`. This works
for every `γ ≤ α` with `γ < 1`, since the Campanato step needs `τ < δ = d + 2`; so for `α < 1` it
reaches `d + 2α`. Campanato's characterization turns this into the Hölder continuity of `∇u` with
exponent `γ`. The steps only use the inequalities above, so they serve the comparison on balls
in the interior as well as the comparison on half-balls centred on a flat boundary.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates for equations with
  variable coefficients).
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
-/

public section

namespace TauCeti

open Set

/-- One step of the Morrey decay. For `r ≤ θ R`, the coefficient term `A r^{2α} K² Φ_r` of the
comparison estimate is a perturbation `A θ^{2α} M² Φ_r` of the decay factor, and the data term
`A D_r` is an inhomogeneity `A V R^{-β} r^β`, for every `β ≤ κ`, when `K R^α ≤ M` and
`D_r ≤ V (r / R)^κ`. -/
private theorem le_mul_add_mul_rpow_of_le_of_mul_rpow_le {A θ M K R V r q φρ Φr Dr α κ β : ℝ}
    (hA : 0 ≤ A) (hr : 0 < r) (hR : 0 < R) (hrθ : r ≤ θ * R) (hrR : r ≤ R) (hα : 0 ≤ α)
    (hK : 0 ≤ K) (hM : K * R ^ α ≤ M) (hD : Dr ≤ V * (r / R) ^ κ) (hV0 : 0 ≤ V) (hΦr : 0 ≤ Φr)
    (hβ : β ≤ κ) (h1 : φρ ≤ A * q * Φr + A * (r ^ (2 * α) * K ^ 2 * Φr + Dr)) :
    φρ ≤ A * (q + θ ^ (2 * α) * M ^ 2) * Φr + A * V * R ^ (-β) * r ^ β := by
  have hrθR : (r / R) ^ (2 * α) ≤ θ ^ (2 * α) :=
    Real.rpow_le_rpow (by positivity) ((div_le_iff₀ hR).2 hrθ) (by positivity)
  have k1 : r ^ (2 * α) * K ^ 2 * Φr ≤ θ ^ (2 * α) * M ^ 2 * Φr :=
    mul_le_mul_of_nonneg_right ((Real.rpow_mul_sq_le hr hR hK hM).trans
      (mul_le_mul_of_nonneg_right hrθR (sq_nonneg M))) hΦr
  have k2 : Dr ≤ V * R ^ (-β) * r ^ β := by
    refine hD.trans ?_
    rw [mul_assoc, ← Real.div_rpow_eq_rpow_neg_mul_rpow hr.le hR]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (div_pos hr hR)
      ((div_le_one₀ hR).2 hrR) hβ) hV0
  calc φρ ≤ A * q * Φr + A * (r ^ (2 * α) * K ^ 2 * Φr + Dr) := h1
    _ ≤ A * q * Φr + A * (θ ^ (2 * α) * M ^ 2 * Φr + V * R ^ (-β) * r ^ β) := by gcongr
    _ = _ := by ring

/-- **Morrey decay from a perturbed comparison.** Let `α > 0`, `γ > 0` and `A ≥ 0`. There are
`θ ∈ (0, 1]` and `C ≥ 0`, depending only on `A`, `α`, `γ`, `d` and `M`, such that the following
holds. Let `Φ` be nonnegative and nondecreasing on `(0, R]` with `Φ R ≤ V`, let `K ≥ 0` with
`K R^α ≤ M`, and let `D r ≤ V (r / R)^{d-γ}` for `0 < r ≤ R`. If

`Φ ρ ≤ A (ρ / r)^d Φ r + A (r^{2α} K² Φ r + D r)` whenever `0 < ρ ≤ r ≤ R`,

then `Φ ρ ≤ C V (ρ / R)^{d-γ}` for `0 < ρ ≤ θ R`. -/
theorem exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add {A α γ d M : ℝ} (hA : 0 ≤ A)
    (hα : 0 < α) (hγ : 0 < γ) :
    ∃ θ C : ℝ, 0 < θ ∧ θ ≤ 1 ∧ 0 ≤ C ∧ ∀ {Φ D : ℝ → ℝ} {K R V : ℝ}, 0 < R → 0 ≤ K →
      K * R ^ α ≤ M → MonotoneOn Φ (Ioc 0 R) → (∀ r ∈ Ioc 0 R, 0 ≤ Φ r) → Φ R ≤ V →
      (∀ r, 0 < r → r ≤ R → D r ≤ V * (r / R) ^ (d - γ)) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ R →
        Φ ρ ≤ A * (ρ / r) ^ d * Φ r + A * (r ^ (2 * α) * K ^ 2 * Φ r + D r)) →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R → Φ ρ ≤ C * V * (ρ / R) ^ (d - γ) := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hit⟩ :=
    exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hA (sub_lt_self d hγ)
      (sub_lt_self d hγ)
  obtain ⟨θ, hθ, hθ1, hε⟩ := Real.exists_pos_le_one_mul_rpow_le (M ^ 2)
    (by positivity : (0 : ℝ) < 2 * α) hε₀
  refine ⟨θ, C₀ * (θ ^ (-(d - γ)) + A), hθ, hθ1, by positivity, ?_⟩
  intro Φ D K R V hR hK hM hmono hΦ0 hΦR hD hcomp ρ hρ hρθ
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hV0 : 0 ≤ V := (hΦ0 R ⟨hR, le_rfl⟩).trans hΦR
  -- One step of the decay: `Φ(ρ) ≤ A ((ρ / r)^d + θ^{2α} M²) Φ(r) + B r^{d-γ}` for
  -- `ρ ≤ r ≤ θ R`.
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ θ * R →
      Φ ρ ≤ A * ((ρ / r) ^ d + θ ^ (2 * α) * M ^ 2) * Φ r + A * V * R ^ (-(d - γ)) * r ^ (d - γ) :=
    fun ρ r hρ hρr hrθ => le_mul_add_mul_rpow_of_le_of_mul_rpow_le hA (hρ.trans_le hρr) hR hrθ
      (hrθ.trans hθR) hα.le hK hM (hD r (hρ.trans_le hρr) (hrθ.trans hθR)) hV0
      (hΦ0 r ⟨hρ.trans_le hρr, hrθ.trans hθR⟩) le_rfl
      ((hcomp ρ r hρ hρr (hrθ.trans hθR)).trans_eq (by ring))
  have hit' := hit (φ := Φ) (R := θ * R) (B := A * V * R ^ (-(d - γ))) (by positivity)
    (by rwa [mul_comm]) (hmono.mono (Ioc_subset_Ioc_right hθR))
    (fun t ht => hΦ0 t ⟨ht.1, ht.2.trans hθR⟩) hstep ρ (θ * R) hρ hρθ le_rfl
  have hΦθR : Φ (θ * R) ≤ V :=
    (hmono ⟨by positivity, hθR⟩ ⟨hR, le_rfl⟩ hθR).trans hΦR
  refine hit'.trans ?_
  rw [Real.div_mul_rpow_eq hρ.le hθ hR]
  calc C₀ * (θ ^ (-(d - γ)) * (ρ / R) ^ (d - γ) * Φ (θ * R) +
        A * V * R ^ (-(d - γ)) * ρ ^ (d - γ))
      ≤ C₀ * (θ ^ (-(d - γ)) * (ρ / R) ^ (d - γ) * V + A * V * R ^ (-(d - γ)) * ρ ^ (d - γ)) := by
        gcongr
    _ = C₀ * (θ ^ (-(d - γ)) + A) * V * (ρ / R) ^ (d - γ) := by
        rw [Real.div_rpow_eq_rpow_neg_mul_rpow hρ.le hR]; ring

/-- One step of the Campanato decay. If `Φ_r ≤ L V (r / R)^β`, then the coefficient and data
terms `A (r^{2α} K² Φ_r + D_r)` of the comparison estimate are at most
`A (M² L + 1) V R^{-τ} r^τ` for every `τ ≤ 2α + β` with `τ ≤ κ`, when `K R^α ≤ M` and
`D_r ≤ V (r / R)^κ`. -/
private theorem le_mul_add_mul_rpow_of_le_of_le_mul_rpow
    {A M K R V r q φρ φr Φr Dr L α κ β τ : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hR : 0 < R)
    (hrR : r ≤ R) (hK : 0 ≤ K) (hM : K * R ^ α ≤ M) (hD : Dr ≤ V * (r / R) ^ κ) (hV0 : 0 ≤ V)
    (hΦr0 : 0 ≤ Φr) (hΦr : Φr ≤ L * V * (r / R) ^ β) (hτβ : τ ≤ 2 * α + β) (hτκ : τ ≤ κ)
    (h1 : φρ ≤ A * q * φr + A * (r ^ (2 * α) * K ^ 2 * Φr + Dr)) :
    φρ ≤ A * (q + 0) * φr + A * (M ^ 2 * L + 1) * V * R ^ (-τ) * r ^ τ := by
  have hq : (r / R) ^ τ = R ^ (-τ) * r ^ τ :=
    Real.div_rpow_eq_rpow_neg_mul_rpow hr.le hR
  have hrR1 : r / R ≤ 1 := (div_le_one₀ hR).2 hrR
  have hLV : 0 ≤ L * V :=
    (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos (div_pos hr hR) β)).1 (hΦr0.trans hΦr)
  have k1 : r ^ (2 * α) * K ^ 2 * Φr ≤ M ^ 2 * L * V * (R ^ (-τ) * r ^ τ) := by
    calc _ ≤ (r / R) ^ (2 * α) * M ^ 2 * (L * V * (r / R) ^ β) :=
          mul_le_mul (Real.rpow_mul_sq_le hr hR hK hM) hΦr hΦr0 (by positivity)
      _ = M ^ 2 * (L * V) * (r / R) ^ (2 * α + β) := by
          rw [Real.rpow_add (div_pos hr hR)]; ring
      _ ≤ M ^ 2 * (L * V) * (r / R) ^ τ :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge (div_pos hr hR) hrR1 hτβ) (by positivity)
      _ = _ := by rw [hq]; ring
  have k2 : Dr ≤ V * (R ^ (-τ) * r ^ τ) := by
    refine hD.trans ?_
    rw [← hq]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (div_pos hr hR) hrR1 hτκ)
      hV0
  calc φρ ≤ A * q * φr + A * (r ^ (2 * α) * K ^ 2 * Φr + Dr) := h1
    _ ≤ A * q * φr + A * (M ^ 2 * L * V * (R ^ (-τ) * r ^ τ) + V * (R ^ (-τ) * r ^ τ)) := by
        gcongr
    _ = _ := by ring

/-- **Campanato decay from a perturbed comparison and a Morrey bound.** Let `A ≥ 0`, `θ ∈ (0, 1]`
and `τ < δ` with `τ ≤ 2α + β` and `τ ≤ κ`. There is `C ≥ 0`, depending only on `A`, `θ`, `τ`,
`δ`, `M` and `L`, such that the following holds. Let `φ` be nonnegative and nondecreasing on
`(0, θ R]` with `φ (θ R) ≤ V`, let `Φ` be nonnegative on `(0, θ R]` with the Morrey bound
`Φ t ≤ L V (t / R)^β` there, let `K ≥ 0` with `K R^α ≤ M`, and let `D r ≤ V (r / R)^κ` for
`0 < r ≤ θ R`. If

`φ ρ ≤ A (ρ / r)^δ φ r + A (r^{2α} K² Φ r + D r)` whenever `0 < ρ ≤ r ≤ θ R`,

then `φ ρ ≤ C V (ρ / R)^τ` for `0 < ρ ≤ θ R`. -/
theorem exists_le_mul_mul_div_rpow_of_le_mul_div_rpow_mul_add_of_le_mul_mul_div_rpow
    {A α β τ κ δ M θ L : ℝ} (hA : 0 ≤ A) (hτβ : τ ≤ 2 * α + β) (hτκ : τ ≤ κ) (hτ : τ < δ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ Φ D : ℝ → ℝ} {K R V : ℝ}, 0 < R → 0 ≤ K → K * R ^ α ≤ M →
      MonotoneOn φ (Ioc 0 (θ * R)) → (∀ r ∈ Ioc 0 (θ * R), 0 ≤ φ r) → φ (θ * R) ≤ V →
      (∀ r ∈ Ioc 0 (θ * R), 0 ≤ Φ r) →
      (∀ t, 0 < t → t ≤ θ * R → Φ t ≤ L * V * (t / R) ^ β) →
      (∀ r, 0 < r → r ≤ θ * R → D r ≤ V * (r / R) ^ κ) →
      (∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ θ * R →
        φ ρ ≤ A * (ρ / r) ^ δ * φ r + A * (r ^ (2 * α) * K ^ 2 * Φ r + D r)) →
      ∀ ρ, 0 < ρ → ρ ≤ θ * R → φ ρ ≤ C * V * (ρ / R) ^ τ := by
  obtain ⟨ε₀, C₀, hε₀, hC₀, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add hA hτ hτ
  refine ⟨C₀ * (θ ^ (-τ) + A * (M ^ 2 * L + 1)), by positivity, ?_⟩
  intro φ Φ D K R V hR hK hM hmono hφ0 hφV hΦ0 hΦ hD hcomp ρ hρ hρθ
  have hθR : θ * R ≤ R := mul_le_of_le_one_left hR.le hθ1
  have hV0 : 0 ≤ V := (hφ0 (θ * R) ⟨by positivity, le_rfl⟩).trans hφV
  -- One step of the decay: `φ(ρ) ≤ A (ρ / r)^δ φ(r) + B r^τ` for `ρ ≤ r ≤ θ R`.
  have hstep : ∀ ρ r, 0 < ρ → ρ ≤ r → r ≤ θ * R →
      φ ρ ≤ A * ((ρ / r) ^ δ + 0) * φ r + A * (M ^ 2 * L + 1) * V * R ^ (-τ) * r ^ τ :=
    fun ρ r hρ hρr hrθ => le_mul_add_mul_rpow_of_le_of_le_mul_rpow hA (hρ.trans_le hρr) hR
      (hrθ.trans hθR) hK hM (hD r (hρ.trans_le hρr) hrθ) hV0 (hΦ0 r ⟨hρ.trans_le hρr, hrθ⟩)
      (hΦ r (hρ.trans_le hρr) hrθ) hτβ hτκ ((hcomp ρ r hρ hρr hrθ).trans_eq (by ring))
  have hit' := hit (φ := φ) (R := θ * R) (B := A * (M ^ 2 * L + 1) * V * R ^ (-τ))
    (by positivity) hε₀.le hmono hφ0 hstep ρ (θ * R) hρ hρθ le_rfl
  refine hit'.trans ?_
  rw [Real.div_mul_rpow_eq hρ.le hθ hR]
  calc C₀ * (θ ^ (-τ) * (ρ / R) ^ τ * φ (θ * R) + A * (M ^ 2 * L + 1) * V * R ^ (-τ) * ρ ^ τ)
      ≤ C₀ * (θ ^ (-τ) * (ρ / R) ^ τ * V + A * (M ^ 2 * L + 1) * V * R ^ (-τ) * ρ ^ τ) := by
        gcongr
    _ = C₀ * (θ ^ (-τ) + A * (M ^ 2 * L + 1)) * V * (ρ / R) ^ τ := by
        rw [Real.div_rpow_eq_rpow_neg_mul_rpow hρ.le hR]; ring

end TauCeti
