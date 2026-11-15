/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import TauCeti.Analysis.Complex.Sector.Zeros
import TauCeti.Analysis.Complex.Conformal.Rouche

/-!
# Complex sector zeros of Airy functions

The Airy function `airyBi` and its derivative `deriv airyBi` have infinitely many complex zeros in
the open sector `π / 3 < arg z < π / 2` (together with their complex conjugates in
`-π / 2 < arg z < -π / 3`). Following DLMF §9.9(i), `TauCeti.airySectorZero f k` (`k ≥ 1`)
enumerates the zeros of `f` in `π / 3 < arg z < π / 2` in polar order: primarily by modulus and,
among zeros of equal modulus, by principal argument.

Because `airyBi` and `deriv airyBi` are entire and nonzero at the origin, their zeros in
`π / 3 < arg z < π / 2` are unconditionally locally norm-finite, so every zero of `airyBi` or
`deriv airyBi` in that sector already appears as `airySectorZero f k` for some `k ≥ 1`
(`TauCeti.exists_airySectorZero_eq`). Combining `TauCeti.sectorZero` with annular Rouché discs
yields disc localization, simplicity, and the full four-part polar enumeration specification
(`TauCeti.airySectorZero_mem_ball_of_rouche`, `TauCeti.airyBiComplexZero_spec_of_rouche`).

## Main definitions and results

* `TauCeti.airySectorZero`: the `k`-th zero of `f : ℂ → ℂ` in `π / 3 < arg z < π / 2` in polar
  order, equal to `TauCeti.sectorZero (π / 3) (π / 2) f k`.
* `TauCeti.finite_airySectorZeros`: for `f = airyBi` or `f = deriv airyBi`, the zeros of `f` in
  `π / 3 < arg z < π / 2` of norm at most `R` form a finite set.
* `TauCeti.exists_airySectorZero_eq`: unconditional completeness — every zero of `airyBi` or
  `deriv airyBi` in `π / 3 < arg z < π / 2` equals `airySectorZero f k` for some `k ≥ 1`.
* `TauCeti.airySectorZero_mem_ball_of_rouche`: Rouché annular localization, simplicity, and
  eventual strict modulus growth for `airySectorZero`.
* `TauCeti.airyBiComplexZero_spec_of_annular_discs` and
  `TauCeti.airyBiComplexZero_spec_of_rouche`: the full polar enumeration specification for
  `f = airyBi` and `f = deriv airyBi` from annular zero-isolating or Rouché discs.

## References

* NIST Digital Library of Mathematical Functions, §9.9(i), <https://dlmf.nist.gov/9.9>.
-/

public section

noncomputable section

open Complex Filter Topology Set Metric
open scoped Real

namespace TauCeti

/-- The `k`-th zero (`k ≥ 1`) of `f` in the open sector `π / 3 < arg z < π / 2`, ordered by modulus
and, among zeros of equal modulus, by principal argument: exactly `k - 1` zeros in the sector
precede it in that order. -/
def airySectorZero (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon fun z : ℂ =>
    (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z))}.ncard = k - 1

/-- Defining epsilon expression for `TauCeti.airySectorZero`. -/
theorem airySectorZero_def (f : ℂ → ℂ) (k : ℕ) :
    airySectorZero f k =
      Classical.epsilon fun z : ℂ =>
        (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧
          {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
            (‖w‖ < ‖z‖ ∨ (‖w‖ = ‖z‖ ∧ arg w < arg z))}.ncard = k - 1 := (rfl)

/-- `TauCeti.airySectorZero` agrees with `TauCeti.sectorZero` on the sector `(π / 3, π / 2)`. -/
theorem airySectorZero_eq_sectorZero (f : ℂ → ℂ) (k : ℕ) :
    airySectorZero f k = sectorZero (π / 3) (π / 2) f k := by
  rw [airySectorZero_def, sectorZero_def]

/-! ### Entireness, nonvanishing at `0`, and unconditional local finiteness -/

/-- Both `airyBi` and `deriv airyBi` are entire. -/
theorem differentiable_of_eq_airyBi_or_deriv {f : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi) : Differentiable ℂ f := by
  rcases hf with rfl | rfl
  · exact differentiable_airyBi
  · exact differentiable_airyBi.deriv

/-- Neither `airyBi` nor `deriv airyBi` vanishes at `0`. -/
theorem apply_zero_ne_zero_of_eq_airyBi_or_deriv {f : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi) : f 0 ≠ 0 := by
  rcases hf with rfl | rfl
  · exact airyBi_zero_ne_zero
  · exact deriv_airyBi_zero_ne_zero

/-- For `f = airyBi` or `f = deriv airyBi`, `f` has at most finitely many zeros of norm `≤ R` in
the open sector `π / 3 < arg z < π / 2`. -/
theorem finite_airySectorZeros {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi) (R : ℝ) :
    {z : ℂ | (π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0) ∧ ‖z‖ ≤ R}.Finite :=
  finite_sectorZeros_of_differentiable (differentiable_of_eq_airyBi_or_deriv hf)
    ⟨0, apply_zero_ne_zero_of_eq_airyBi_or_deriv hf⟩ R

/-- If `z` is a zero of `airyBi` or `deriv airyBi` in `π / 3 < arg z < π / 2` preceded by `k - 1`
sector zeros in `Complex.polarLt` order, then `airySectorZero f k = z`. -/
theorem airySectorZero_eq_of_ncard {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi)
    {z : ℂ} {k : ℕ} (hz : π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0)
    (hcard : {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧ w.polarLt z}.ncard = k - 1) :
    airySectorZero f k = z := by
  rw [airySectorZero_eq_sectorZero]
  exact sectorZero_eq_of_ncard (finite_airySectorZeros hf) hz hcard

/-- **Unconditional completeness of `airySectorZero`.** For `f = airyBi` or `f = deriv airyBi`,
every zero `z` of `f` in `π / 3 < arg z < π / 2` equals `airySectorZero f k` for some `k ≥ 1`. -/
theorem exists_airySectorZero_eq {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi)
    {z : ℂ} (h₁ : π / 3 < arg z) (h₂ : arg z < π / 2) (hfz : f z = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ airySectorZero f k = z := by
  simpa only [airySectorZero_eq_sectorZero] using
    exists_sectorZero_eq (finite_airySectorZeros hf) h₁ h₂ hfz

/-- When `1 ≤ k` and `(k : ℕ∞) ≤ {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.encard`, the epsilon
`airySectorZero f k` attains its defining predicate for `f = airyBi` or `f = deriv airyBi`. -/
theorem airySectorZero_spec_of_le_encard {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi)
    {k : ℕ} (hk : 1 ≤ k)
    (hle : (k : ℕ∞) ≤ {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.encard) :
    (π / 3 < arg (airySectorZero f k) ∧ arg (airySectorZero f k) < π / 2 ∧
        f (airySectorZero f k) = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖airySectorZero f k‖ ∨
          (‖w‖ = ‖airySectorZero f k‖ ∧ arg w < arg (airySectorZero f k)))}.ncard = k - 1 := by
  simpa only [airySectorZero_eq_sectorZero, Complex.polarLt_def] using
    sectorZero_spec_of_le_encard (finite_airySectorZeros hf) hk hle

/-! ### Properties under infinitude of sector zeros -/

/-- For `f = airyBi` or `f = deriv airyBi`, once the sector zero set in `π / 3 < arg z < π / 2` is
known to be infinite, `airySectorZero f k` attains its defining predicate for every `k ≥ 1`. -/
theorem airySectorZero_spec_of_infinite {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi)
    (hinf : {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    (π / 3 < arg (airySectorZero f k) ∧ arg (airySectorZero f k) < π / 2 ∧
        f (airySectorZero f k) = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖airySectorZero f k‖ ∨
          (‖w‖ = ‖airySectorZero f k‖ ∧ arg w < arg (airySectorZero f k)))}.ncard = k - 1 := by
  simpa only [airySectorZero_eq_sectorZero, Complex.polarLt_def] using
    sectorZero_spec_of_infinite (finite_airySectorZeros hf) hinf hk

/-- Under `Infinite`, `airySectorZero f` is strictly increasing with respect to `Complex.polarLt`
for `1 ≤ j < k`. -/
theorem polarLt_airySectorZero_of_lt {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi)
    (hinf : {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite)
    {j k : ℕ} (hj : 1 ≤ j) (hjk : j < k) :
    (airySectorZero f j).polarLt (airySectorZero f k) := by
  simpa only [airySectorZero_eq_sectorZero] using
    polarLt_sectorZero_of_lt (finite_airySectorZeros hf) hinf hj hjk

/-- Under `Infinite`, every zero of `airyBi` or `deriv airyBi` in `π / 3 < arg z < π / 2` occurs at
a unique positive index `k ≥ 1`. -/
theorem existsUnique_airySectorZero_eq_of_infinite {f : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi)
    (hinf : {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite)
    {z : ℂ} (h₁ : π / 3 < arg z) (h₂ : arg z < π / 2) (hfz : f z = 0) :
    ∃! k : ℕ, 1 ≤ k ∧ airySectorZero f k = z := by
  simpa only [airySectorZero_eq_sectorZero] using
    existsUnique_sectorZero_eq_of_infinite (finite_airySectorZeros hf) hinf h₁ h₂ hfz

/-- Under `Infinite`, the moduli `‖airySectorZero f k‖` are nondecreasing for `k ≥ 1`. -/
theorem norm_airySectorZero_le_succ_of_infinite {f : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi)
    (hinf : {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite)
    {k : ℕ} (hk : 1 ≤ k) :
    ‖airySectorZero f k‖ ≤ ‖airySectorZero f (k + 1)‖ := by
  simpa only [airySectorZero_eq_sectorZero] using
    norm_sectorZero_le_succ (finite_airySectorZeros hf) hinf hk

/-- Under `Infinite`, `‖airySectorZero f k‖ → ∞` as `k → ∞` for `f = airyBi` or
`f = deriv airyBi`. -/
theorem tendsto_norm_airySectorZero_atTop_of_infinite {f : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi)
    (hinf : {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite) :
    Tendsto (fun k : ℕ => ‖airySectorZero f k‖) atTop atTop := by
  simpa only [airySectorZero_eq_sectorZero] using
    tendsto_norm_sectorZero_atTop (finite_airySectorZeros hf) hinf

/-! ### Annular disc and Rouché bridges to the full `airySectorZero` specification -/

/-- **Full polar enumeration specification of `airySectorZero` from annular discs.** Once annularly
separated discs `ball (c n) (r n)` in `π / 3 < arg z < π / 2` isolate one zero of `f` each and cover
all sector zeros of `f` of norm at least `R₀ ≤ ‖c 0‖ - r 0` (for `f = airyBi` or
`f = deriv airyBi`), the epsilons `airySectorZero f k` (`k ≥ 1`) are attained, enumerate all zeros
of `f` in `π / 3 < arg z < π / 2`, have nondecreasing moduli, and have strictly increasing moduli
from some index `k₀` onward. -/
theorem airyBiComplexZero_spec_of_annular_discs {f : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), π / 3 < arg z ∧ arg z < π / 2)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (huniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0)
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, π / 3 < arg z → arg z < π / 2 → f z = 0 → R₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (c n) (r n)) :
    (∀ k, 1 ≤ k → (π / 3 < arg (airySectorZero f k) ∧ arg (airySectorZero f k) < π / 2 ∧
        f (airySectorZero f k) = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖airySectorZero f k‖ ∨
          (‖w‖ = ‖airySectorZero f k‖ ∧ arg w < arg (airySectorZero f k)))}.ncard = k - 1) ∧
    (∀ z, π / 3 < arg z → arg z < π / 2 → f z = 0 → ∃ k, 1 ≤ k ∧ airySectorZero f k = z) ∧
    (∀ k, 1 ≤ k → ‖airySectorZero f k‖ ≤ ‖airySectorZero f (k + 1)‖) ∧
    ∃ k₀, ∀ k, k₀ ≤ k → ‖airySectorZero f k‖ < ‖airySectorZero f (k + 1)‖ := by
  have hfin := finite_airySectorZeros hf
  have hinf : {z : ℂ | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}.Infinite :=
    infinite_sectorZeros_of_annular_discs hsub hsep fun n =>
      let ⟨z, hz, _⟩ := huniq n; ⟨z, hz.1, hz.2⟩
  refine ⟨fun k hk => airySectorZero_spec_of_infinite hf hinf hk,
    fun z h₁ h₂ hfz => exists_airySectorZero_eq hf h₁ h₂ hfz,
    fun k hk => norm_airySectorZero_le_succ_of_infinite hf hinf hk,
    ⟨{w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1, fun k hk => ?_⟩⟩
  simpa only [airySectorZero_eq_sectorZero] using
    norm_sectorZero_lt_succ_of_annular_discs hfin hsub hsep huniq hR₀ hexh hk

/-- **Rouché annular localization of `airySectorZero`.** For `f = airyBi` or `f = deriv airyBi`
and an analytic comparison function `g` satisfying `‖f z - g z‖ < ‖f z‖ + ‖g z‖` on the boundary
circles `sphere (c n) (r n)` of annularly separated discs inside `π / 3 < arg z < π / 2` that cover
all sector zeros of `f` of norm `≥ R₀` (`R₀ ≤ ‖c 0‖ - r 0`), the shifted sequence
`airySectorZero f (k₀ + n)` lies in `ball (c n) (r n)`, consists of simple zeros (`deriv f · ≠ 0`),
and `‖airySectorZero f k‖` is strictly increasing for `k ≥ k₀`. -/
theorem airySectorZero_mem_ball_of_rouche {f g : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hg_an : ∀ n, AnalyticOnNhd ℂ g (closedBall (c n) (r n)))
    (hs : ∀ n, ∀ z ∈ sphere (c n) (r n), ‖f z - g z‖ < ‖f z‖ + ‖g z‖)
    (hg_uniq : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ g z = 0) ∧
      ∀ z ∈ ball (c n) (r n), g z = 0 → deriv g z ≠ 0)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), π / 3 < arg z ∧ arg z < π / 2)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, π / 3 < arg z → arg z < π / 2 → f z = 0 → R₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (c n) (r n)) :
    let k₀ := {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧ ‖w‖ < R₀}.ncard + 1
    (∀ n, airySectorZero f (k₀ + n) ∈ ball (c n) (r n)) ∧
      (∀ n, deriv f (airySectorZero f (k₀ + n)) ≠ 0) ∧
      ∀ k, k₀ ≤ k → ‖airySectorZero f k‖ < ‖airySectorZero f (k + 1)‖ := by
  have hf_an : ∀ n, AnalyticOnNhd ℂ f (closedBall (c n) (r n)) := fun _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_of_eq_airyBi_or_deriv hf)).mono (subset_univ _)
  have h := sectorZero_mem_ball_of_rouche (finite_airySectorZeros hf) hf_an hg_an hs hg_uniq
    hsub hsep hR₀ hexh
  intro k₀
  exact ⟨fun n => by simpa only [airySectorZero_eq_sectorZero] using h.1 n,
    fun n => by simpa only [airySectorZero_eq_sectorZero] using h.2.1 n,
    fun k hk => by simpa only [airySectorZero_eq_sectorZero] using h.2.2 k hk⟩

/-- **Full polar enumeration specification of `airySectorZero` from Rouché discs.** Under the
hypotheses of `TauCeti.airySectorZero_mem_ball_of_rouche`, `airySectorZero f` satisfies all four
clauses of the DLMF §9.9(i) sector-zero specification for `f = airyBi` and `f = deriv airyBi`. -/
theorem airyBiComplexZero_spec_of_rouche {f g : ℂ → ℂ}
    (hf : f = airyBi ∨ f = deriv airyBi)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {R₀ : ℝ}
    (hg_an : ∀ n, AnalyticOnNhd ℂ g (closedBall (c n) (r n)))
    (hs : ∀ n, ∀ z ∈ sphere (c n) (r n), ‖f z - g z‖ < ‖f z‖ + ‖g z‖)
    (hg_uniq : ∀ n, (∃! z, z ∈ ball (c n) (r n) ∧ g z = 0) ∧
      ∀ z ∈ ball (c n) (r n), g z = 0 → deriv g z ≠ 0)
    (hsub : ∀ n, ∀ z ∈ ball (c n) (r n), π / 3 < arg z ∧ arg z < π / 2)
    (hsep : ∀ n, ‖c n‖ + r n < ‖c (n + 1)‖ - r (n + 1))
    (hR₀ : R₀ ≤ ‖c 0‖ - r 0)
    (hexh : ∀ z, π / 3 < arg z → arg z < π / 2 → f z = 0 → R₀ ≤ ‖z‖ →
      ∃ n, z ∈ ball (c n) (r n)) :
    (∀ k, 1 ≤ k → (π / 3 < arg (airySectorZero f k) ∧ arg (airySectorZero f k) < π / 2 ∧
        f (airySectorZero f k) = 0) ∧
      {w : ℂ | (π / 3 < arg w ∧ arg w < π / 2 ∧ f w = 0) ∧
        (‖w‖ < ‖airySectorZero f k‖ ∨
          (‖w‖ = ‖airySectorZero f k‖ ∧ arg w < arg (airySectorZero f k)))}.ncard = k - 1) ∧
    (∀ z, π / 3 < arg z → arg z < π / 2 → f z = 0 → ∃ k, 1 ≤ k ∧ airySectorZero f k = z) ∧
    (∀ k, 1 ≤ k → ‖airySectorZero f k‖ ≤ ‖airySectorZero f (k + 1)‖) ∧
    ∃ k₀, ∀ k, k₀ ≤ k → ‖airySectorZero f k‖ < ‖airySectorZero f (k + 1)‖ := by
  have hf_an : ∀ n, AnalyticOnNhd ℂ f (closedBall (c n) (r n)) := fun _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_of_eq_airyBi_or_deriv hf)).mono (subset_univ _)
  have hf_uniq : ∀ n, ∃! z, z ∈ ball (c n) (r n) ∧ f z = 0 := fun n =>
    ((rouche_symm_existsUnique_eq_zero_and_deriv_ne_zero_iff
      (hf_an n) (hg_an n) (hs n)).mpr (hg_uniq n)).1
  exact airyBiComplexZero_spec_of_annular_discs hf hsub hsep hf_uniq hR₀ hexh

end TauCeti
