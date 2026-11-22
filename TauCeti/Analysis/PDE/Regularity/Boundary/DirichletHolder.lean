/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Boundary.GlobalHolder
public import TauCeti.Analysis.Sobolev.LipschitzDomain.MeasureDensity
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness
import TauCeti.Analysis.PDE.Regularity.Boundary.Oscillation

/-!
# The global Hölder estimate for the Dirichlet problem with zero boundary values

Let `a` be measurable and uniformly elliptic on an open set `Ω ⊆ ℝⁿ`, `n ≥ 1`, with constants
`0 < λ ≤ Λ`, let `f ∈ Lʳ(Ω)` with `r > 1` and `r > n/2`, and let `u ∈ H¹₀(Ω)` be the weak solution
of the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, `u = 0` on `∂Ω`,

that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. This file proves that `u` is Hölder continuous
up to the boundary, with a Hölder constant controlled by `‖f‖_{Lʳ(Ω)} / λ` alone, as soon as `Ω` has
finite measure and its complement has uniform positive density at its own points: for some
`θ > 0` and `R > 0`,

`θ |B(z, s)| ≤ |B(z, s) \ Ω|` for every `z ∉ Ω` and `0 < s ≤ R`.

More precisely, the precise representative of the extension of `u` by zero is `α`-Hölder on all of
`ℝⁿ` with constant

`C R^(-α) (|Ω|^(2/n - 1/r) + R^(2 - n/r)) ‖f‖_{Lʳ(Ω)} / λ`,

where `α > 0` and `C` depend only on `λ`, `Λ`, `θ`, `r`, `n` and the normalization of the Haar
measure
(`TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff`).
Every bounded Lipschitz domain has such an exterior density, so on a bounded Lipschitz domain the
Hölder constant is `C ‖f‖_{Lʳ(Ω)} / λ` with `α` and `C` depending on `Ω`, `λ`, `Λ` and `r`
(`Set.IsLipschitzDomain.exists_holderWith_preciseRepresentative_indicator`). No regularity of the
coefficients beyond measurability is used. This is the case of zero boundary values and a scalar
right-hand side of the global Hölder estimate of Gilbarg–Trudinger, Theorem 8.29.

## The argument

Three estimates already proved are combined.

* **The global bound.** Stampacchia's maximum principle
  (`TauCeti.PDE.exists_ae_abs_value_le_mul_div_mul_rpow_drift`, with no drift) bounds `|u|` on
  `Ω` by
  `M = C ‖f‖_{Lʳ(Ω)} / λ · |Ω|^(2/n - 1/r)`.
* **Decay at the boundary.** At a point `z ∉ Ω`, De Giorgi's boundary estimate
  (`exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff`)
  turns the bound `M` on `Ω ∩ B(z, R)` and the exterior density into the power decay
  `|u| ≤ N (ρ / R)^β` on `Ω ∩ B(z, ρ)`, with `N = C (M + R^(2 - n/r) ‖f‖_{Lʳ(Ω)} / λ)`.
* **Covering.** The bound `M`, the decay at the complement and De Giorgi's interior estimate give
  the Hölder estimate on the whole space
  (`TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence`, with
  no divergence datum).

## Main declarations

* `TauCeti.PDE.exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff`:
  the global Hölder estimate on an open set of finite measure with uniform exterior density.
* `Set.IsLipschitzDomain.exists_holderWith_preciseRepresentative_indicator`: the global Hölder
  estimate on a bounded Lipschitz domain.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 8.16, 8.27 and 8.29.
-/

public section

open Filter MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

/-- The bookkeeping of the constant: with the global bound `M = C_b F P / λ` and the decay constant
`N = C_d (M + Q F / λ)`, the constant `C R^(-α) (M + N + Q F / λ)` of the covering step is at most
`C (1 + C_d) (1 + C_b) R^(-α) (P + Q) F / λ`. -/
private theorem mul_rpow_mul_add_add_div_le {C Cb Cd R α P Q F lam : ℝ} (hC : 0 ≤ C)
    (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd) (hR : 0 ≤ R) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hF : 0 ≤ F)
    (hlam : 0 < lam) :
    C * R ^ (-α) * (Cb * F / lam * P + Cd * (Cb * F / lam * P + Q * F / lam) + Q * F / lam) ≤
      C * (1 + Cd) * (1 + Cb) * R ^ (-α) * (P + Q) * F / lam := by
  have hPQ : Cb * P + Q ≤ (1 + Cb) * (P + Q) := by nlinarith
  calc C * R ^ (-α) * (Cb * F / lam * P + Cd * (Cb * F / lam * P + Q * F / lam) + Q * F / lam)
      = C * R ^ (-α) * (1 + Cd) * ((Cb * P + Q) * (F / lam)) := by ring
    _ ≤ C * R ^ (-α) * (1 + Cd) * ((1 + Cb) * (P + Q) * (F / lam)) := by gcongr
    _ = C * (1 + Cd) * (1 + Cb) * R ^ (-α) * (P + Q) * F / lam := by ring

/-- **The global Hölder estimate for the Dirichlet problem under an exterior density condition.**
Let `n ≥ 1` be the dimension, let `r > 1` with `r > n/2`, and fix a proportion `θ > 0`. There are
`α > 0` and `C > 0`, depending only on `λ`, `Λ`, `θ`, `r`, `n` and the normalization of the additive
Haar measure `mu`, such that the following holds. Let `Ω` be open with finite measure, let `a` be
measurable and uniformly elliptic on `Ω` with constants `λ, Λ`, let `f ∈ Lʳ(Ω)`, and let
`u ∈ H¹₀(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every
`v ∈ H¹₀(Ω)`. Suppose that the complement of `Ω` fills the proportion `θ` of every ball `B(z, s)`
with `z ∉ Ω` and `0 < s ≤ R`. Then the precise representative of the extension of `u` by zero is
Hölder continuous on the whole space with exponent `α` and constant

`C R^(-α) (|Ω|^(2/n - 1/r) + R^(2 - n/r)) ‖f‖_{Lʳ(Ω)} / λ`.

No regularity of `∂Ω` beyond the exterior density condition, and no regularity of the
coefficients beyond measurability, is assumed. -/
theorem exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff
    [Nonempty ι] {lam Lam : ℝ} {r : ℝ≥0} (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ 0 < C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ ι)}
      {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {f : EuclideanSpace ℝ ι → ℝ}
      {u : W1p mu Omega 2} {R : ℝ},
      mu (Omega : Set (EuclideanSpace ℝ ι)) ≠ ∞ →
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      0 < R →
      (∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ s, 0 < s → s ≤ R →
        θ * mu.real (ball z s) ≤ mu.real (ball z s \ (Omega : Set (EuclideanSpace ℝ ι)))) →
      HolderWith (C * R ^ (-(α : ℝ)) *
          (mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^
              (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹) + R ^ (2 - (Fintype.card ι : ℝ) / r)) *
            (eLpNorm f r (mu.restrict Omega)).toReal / lam).toNNReal α
        (preciseRepresentative mu
          ((Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value u))) := by
  obtain ⟨Cb, hCb, hbd⟩ := exists_ae_abs_value_le_mul_div_mul_rpow_drift (mu := mu) hr hrn
  obtain ⟨β, Cd, hβ, hCd, hdecay⟩ :=
    exists_ae_abs_value_le_mul_rpow_mul_add_of_mul_measureReal_le_measureReal_ball_diff
      (mu := mu) (lam := lam) (Lam := Lam) hr hrn hθ
  -- There is no divergence datum, so any admissible exponent `q > max 2 n` serves.
  have hn : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hq : 2 < ((Fintype.card ι + 2 : ℝ≥0) : ℝ) := by push_cast; linarith
  have hqn : (Fintype.card ι : ℝ) < ((Fintype.card ι + 2 : ℝ≥0) : ℝ) := by push_cast; linarith
  obtain ⟨α, C, hα, -, hC, hglob⟩ :=
    exists_holderWith_preciseRepresentative_indicator_of_memLp_add_divergence (mu := mu)
      (lam := lam) (Lam := Lam) hr hrn hq hqn hβ
  refine ⟨α, C * (1 + Cd) * (1 + Cb), hα, by positivity, ?_⟩
  intro Omega a f u R hfin h ha hf hu0 hu hR hext
  have hlam := h.pos
  set F := (eLpNorm f r (mu.restrict Omega)).toReal
  set P := mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^
    (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹)
  set Q := R ^ (2 - (Fintype.card ι : ℝ) / r)
  set M := Cb * F / lam * P
  set N := Cd * (M + Q * F / lam) with hN
  have hM0 : 0 ≤ M := by positivity
  have hN0 : 0 ≤ N := by positivity
  -- Stampacchia's global bound `|u| ≤ M`.
  have hbound : ∀ᵐ x ∂mu.restrict Omega, |W1p.value u x| ≤ M :=
    hbd (u := ⟨u, hu0⟩) (b := 0) (beta := 0) (c := 0) (gamma := 0) hfin h ha
      aestronglyMeasurable_zero aestronglyMeasurable_zero (by simp) (by simp) (by simp)
      (fun _ _ => by rw [mul_zero, zero_mul]; exact mul_nonneg h.pos.le (norm_nonneg _)) hf hu
  -- De Giorgi's decay at the points of the complement, `|u| ≤ N (ρ / R)^β` on `Ω ∩ B(z, ρ)`.
  have hbdry : ∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ ρ, 0 < ρ → ρ ≤ R →
      ∀ᵐ x ∂mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball z ρ),
        |W1p.value u x| ≤ (N.toNNReal : ℝ) * (ρ / R) ^ β := by
    intro z hz ρ hρ hρR
    have hle : mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩ ball z R) ≤
        mu.restrict Omega := Measure.restrict_mono inter_subset_left le_rfl
    have hloc : (eLpNorm f r (mu.restrict ((Omega : Set (EuclideanSpace ℝ ι)) ∩
        ball z R))).toReal ≤ F :=
      ENNReal.toReal_mono hf.eLpNorm_ne_top (eLpNorm_mono_measure f hle)
    filter_upwards [hdecay h ha (hf.mono_measure hle) hu0 hu hρ hρR
      (ae_restrict_of_ae_restrict_of_subset inter_subset_left hbound) (hext z hz)] with x hx
    refine hx.trans ?_
    rw [Real.coe_toNNReal _ hN0, hN, mul_right_comm]
    gcongr
  have hglob' := hglob (F := 0) (M := M.toNNReal) (N := N.toNNReal) h ha hf MemLp.zero
    (fun v => by simp [hu v]) hR
    (by filter_upwards [hbound] with x hx; rwa [Real.coe_toNNReal _ hM0]) hbdry
  refine hglob'.mono (Real.toNNReal_le_toNNReal ?_)
  simp only [eLpNorm_zero, ENNReal.toReal_zero, mul_zero, add_zero, Real.coe_toNNReal _ hM0,
    Real.coe_toNNReal _ hN0]
  exact mul_rpow_mul_add_add_div_le hC.le hCb.le hCd.le hR.le (by positivity) (by positivity)
    ENNReal.toReal_nonneg hlam

end PDE

end TauCeti

namespace Set.IsLipschitzDomain

open TauCeti TauCeti.PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The global Hölder estimate for the Dirichlet problem on a bounded Lipschitz domain.** Let
`Ω ⊆ ℝⁿ`, `n ≥ 1`, be a bounded Lipschitz domain and let `r > 1` with `r > n/2`. There are `α > 0`
and `C > 0`, depending only on `Ω`, `λ`, `Λ`, `r` and the normalization of the additive Haar measure
`mu`, such that the following holds. Let `a` be measurable and uniformly elliptic on `Ω` with
constants `λ, Λ`, let `f ∈ Lʳ(Ω)`, and let `u ∈ H¹₀(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f`, that is `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. Then the precise
representative of the extension of `u` by zero is Hölder continuous on the whole space with
exponent `α` and constant `C ‖f‖_{Lʳ(Ω)} / λ`.

No regularity of the coefficients beyond measurability is assumed. -/
theorem exists_holderWith_preciseRepresentative_indicator [Nonempty ι]
    {Omega : Opens (EuclideanSpace ℝ ι)}
    (hΩ : (Omega : Set (EuclideanSpace ℝ ι)).IsLipschitzDomain E)
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι))) {lam Lam : ℝ} {r : ℝ≥0}
    (hr : 1 < r) (hrn : (Fintype.card ι : ℝ) < 2 * r) :
    ∃ (α : ℝ≥0) (C : ℝ), 0 < α ∧ 0 < C ∧ ∀ {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
      {f : EuclideanSpace ℝ ι → ℝ} {u : W1p mu Omega 2},
      UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam →
      AEStronglyMeasurable a (mu.restrict Omega) →
      MemLp f r (mu.restrict Omega) →
      u ∈ w1p0Submodule mu Omega 2 →
      (∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
        ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu) →
      HolderWith (C * (eLpNorm f r (mu.restrict Omega)).toReal / lam).toNNReal α
        (preciseRepresentative mu
          ((Omega : Set (EuclideanSpace ℝ ι)).indicator (W1p.value u))) := by
  have hK : IsCompact (frontier (Omega : Set (EuclideanSpace ℝ ι))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨c, hc, hdens⟩ :=
    hΩ.exists_pos_mul_measure_ball_le_measure_ball_sdiff_closure (μ := mu) hK one_pos
  -- The exterior density at the radii `s ≤ 1`, in the form of the general estimate.
  have hext : ∀ z ∉ (Omega : Set (EuclideanSpace ℝ ι)), ∀ s, 0 < s → s ≤ 1 →
      (c : ℝ) * mu.real (ball z s) ≤
        mu.real (ball z s \ (Omega : Set (EuclideanSpace ℝ ι))) := by
    intro z hz s hs hs1
    have hfin : mu (ball z s \ (Omega : Set (EuclideanSpace ℝ ι))) ≠ ∞ :=
      ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
    calc (c : ℝ) * mu.real (ball z s) = ((c : ℝ≥0∞) * mu (ball z s)).toReal := by
          rw [ENNReal.toReal_mul, measureReal_def, ENNReal.coe_toReal]
      _ ≤ (mu (ball z s \ (Omega : Set (EuclideanSpace ℝ ι)))).toReal :=
          ENNReal.toReal_mono hfin ((hdens z hz s hs hs1).trans
            (measure_mono (sdiff_subset_sdiff_right subset_closure)))
  obtain ⟨α, C, hα, hC, hmain⟩ :=
    exists_holderWith_preciseRepresentative_indicator_of_measureReal_ball_diff
      (mu := mu) (lam := lam) (Lam := Lam) hr hrn (θ := c) (by exact_mod_cast hc)
  set P := mu.real (Omega : Set (EuclideanSpace ℝ ι)) ^ (2 / (Fintype.card ι : ℝ) - (r : ℝ)⁻¹)
  refine ⟨α, C * (P + 1), hα, by positivity, fun h ha hf hu0 hu => ?_⟩
  have := hmain hb.measure_lt_top.ne h ha hf hu0 hu one_pos hext
  simpa only [Real.one_rpow, mul_one] using this

end Set.IsLipschitzDomain
