/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent

/-!
# Localization of small spinor components near their zeros

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold,
a solution at parameter `r` has normalized spinor `χ = α u₀ + β`, and its *vacuum defect* is
`w₊ = max (1 - |α|²) 0`. Write `h = (2 r)^(-1/2)` for the length scale of the solution and `Z`
for the zero set of `α`. Away from `Z` the curvature component `π_ω (F_A - F_{A₀} - ρ) =
(r / 4) (|α|² - |β|² - 1)`, the comparison of `A` with the canonical connection of `α` and the
estimate on `β` give the **off-zero bound**

`w₊(x) ≤ (C / r) w₊(x) + C / r + C exp (-c d / h)`, for `d ≥ c₀ h`,

where `d` is the distance from `x` to `Z`. This file draws the consequence of the off-zero bound:
after absorbing the term `(C / r) w₊`, a point where `|α|` is bounded away from one lies within
a fixed multiple of `h` of a zero of `α`. Precisely, for every threshold `σ < 1` there are
constants `K` and `r₀`, depending only on `C`, `c`, `c₀` and `σ`, such that for `r ≥ r₀` every
point with `|α|² ≤ σ` lies within distance `K h` of `Z`
(`TauCeti.SeibergWitten.exists_forall_exists_dist_le_of_le`). The constants do not depend on
the space, on the solution or on `h`, which is what makes the statement uniform over a compact
family of geometric data and forcing terms once the off-zero bound holds with uniform constants.

The off-zero bound is used here in the following form: for every radius `R ≥ c₀ h` such that
the open ball of radius `R` about `x` misses `Z`, the defect at `x` is at most
`(C / r) w₊ + C / r + C exp (-c R / h)`. For `C ≥ 0`, `c ≥ 0` and nonempty `Z` this follows from
the bound with `d = dist(x, Z)`, because the exponential is antitone in `R ≤ d`. When `Z` is
empty every radius is allowed, and the conclusion says that no point has `|α|² ≤ σ` once
`r ≥ r₀`. Points closer to `Z` than `c₀ h` satisfy the conclusion because `K ≥ c₀`.

Two thresholds are used in the analysis.

* With `σ = 1 / 2`, the support of the cutoff current `Θ = i F_a + d(χ(|α|²) τ)`, which lies in
  `{|α|² ≤ 1 / 2}` (`TauCeti.SeibergWitten.tsupport_cutoffCurrent_subset`), lies within distance
  `K h` of `Z` (`TauCeti.SeibergWitten.exists_forall_exists_dist_le_of_mem_tsupport_cutoffCurrent`).
* Point constraints only control `|α|` up to a tolerance `ε(r)` tending to zero. With `σ = 1 / 4`
  the radius `K` does not depend on the tolerance: once `ε(r) ≤ 1 / 2`, every point with
  `|α| ≤ ε(r)` lies within distance `K h` of `Z`
  (`TauCeti.SeibergWitten.exists_forall_exists_dist_le_of_le_sq_of_tendsto`).

The core inequality is `TauCeti.SeibergWitten.exists_dist_le_of_forall_max_le`, which states
the explicit conditions on `K` and `r` used in the absorption.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

open Filter Real Set

namespace TauCeti.SeibergWitten

universe u v

variable {X : Type u} [PseudoMetricSpace X]

/-- **Absorption in the off-zero bound.** Let `η > 0` and suppose `w ≥ η` at the point `x`.
Suppose that for every radius `R ≥ c₀ h` such that the open ball of radius `R` about `x` misses
`Z`, the off-zero bound `w₊ ≤ (C / r) w₊ + C / r + C exp (-c R / h)` holds, with `w₊ = max w 0`.
If `K ≥ c₀`, `C exp (-c K) ≤ η / 4`, `2 C ≤ r` and `8 C ≤ η r`, then `x` lies within distance
`K h` of a point of `Z`. -/
theorem exists_dist_le_of_forall_max_le {Z : Set X} {x : X} {w η C c c₀ r h K : ℝ}
    (hη : 0 < η) (hw : η ≤ w) (hr : 0 < r) (hr₁ : 2 * C ≤ r) (hr₂ : 8 * C ≤ η * r)
    (hh : 0 < h) (hK₀ : c₀ ≤ K) (hK : C * exp (-(c * K)) ≤ η / 4)
    (hbound : ∀ R, c₀ * h ≤ R → (∀ z ∈ Z, R ≤ dist x z) →
      max w 0 ≤ C / r * max w 0 + C / r + C * exp (-(c * R / h))) :
    ∃ z ∈ Z, dist x z ≤ K * h := by
  by_contra! hfar
  have hR := hbound (K * h) (mul_le_mul_of_nonneg_right hK₀ hh.le) fun z hz ↦ (hfar z hz).le
  rw [max_eq_left (hη.le.trans hw), mul_div_assoc, mul_div_cancel_right₀ _ hh.ne'] at hR
  -- Multiplying by `r`, the off-zero bound reads `r w ≤ C w + C + r C exp (-c K)`.
  have hRr : r * w ≤ C * w + C + r * (C * exp (-(c * K))) := by
    have := mul_le_mul_of_nonneg_left hR hr.le
    rwa [mul_add, mul_add, ← mul_assoc, mul_div_cancel₀ _ hr.ne'] at this
  -- `2 C ≤ r` absorbs `C w` into `r w / 2`, and then `8 C ≤ η r` contradicts `w ≥ η`.
  nlinarith [mul_le_mul_of_nonneg_left hK hr.le, mul_le_mul_of_nonneg_right hr₁ (hη.le.trans hw),
    mul_le_mul_of_nonneg_left hw hr.le, mul_pos hη hr]

/-- **Quantitative zero localization.** Let `σ < 1` and `c > 0`. There are constants `K` and
`r₀ > 0`, depending only on `C`, `c`, `c₀` and `σ`, with the following property. Let `s = |α|²`
be the squared norm of the component `α` on a pseudometric space `X`, `Z ⊆ X` (the zero set of
`α`), `r ≥ r₀` and `h > 0`. If at a point `x` the off-zero bound
`w₊ ≤ (C / r) w₊ + C / r + C exp (-c R / h)`, `w₊ = max (1 - s) 0`, holds for every radius
`R ≥ c₀ h` of an open ball about `x` missing `Z`, and `s x ≤ σ`, then `x` lies within distance
`K h` of a point of `Z`. -/
theorem exists_forall_exists_dist_le_of_le (C c c₀ : ℝ) (hc : 0 < c) {σ : ℝ} (hσ : σ < 1) :
    ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ {X : Type u} [PseudoMetricSpace X] (s : X → ℝ) (Z : Set X)
      (r h : ℝ), r₀ ≤ r → 0 < h → ∀ x : X,
      (∀ R, c₀ * h ≤ R → (∀ z ∈ Z, R ≤ dist x z) →
        max (1 - s x) 0 ≤ C / r * max (1 - s x) 0 + C / r + C * exp (-(c * R / h))) →
      s x ≤ σ → ∃ z ∈ Z, dist x z ≤ K * h := by
  set η := 1 - σ with hη_def
  have hη : 0 < η := by linarith
  refine ⟨max c₀ (log (4 * C / η) / c), max 1 (max (2 * C) (8 * C / η)), by positivity, ?_⟩
  intro X _ s Z r h hr hh x hbound hs
  have hr₀ : 0 < r := lt_of_lt_of_le (by positivity) hr
  refine exists_dist_le_of_forall_max_le hη (by linarith) hr₀
    ((le_max_left _ _).trans ((le_max_right _ _).trans hr)) ?_ hh (le_max_left _ _) ?_ hbound
  · have := (le_max_right (2 * C) _).trans ((le_max_right _ _).trans hr)
    linarith [(div_le_iff₀ hη).1 this, mul_comm η r]
  · -- The radius `K ≥ log (4 C / η) / c` makes the exponential tail at most `η / 4`.
    rcases le_or_gt C 0 with hC | hC
    · exact (mul_nonpos_of_nonpos_of_nonneg hC (exp_pos _).le).trans (by positivity)
    have hK : log (4 * C / η) ≤ c * max c₀ (log (4 * C / η) / c) := by
      rw [← div_le_iff₀' hc]
      exact le_max_right _ _
    calc C * exp (-(c * max c₀ (log (4 * C / η) / c)))
        ≤ C * exp (-log (4 * C / η)) := by gcongr
      _ = η / 4 := by
        rw [exp_neg, exp_log (by positivity)]
        field_simp

/-- **Localization of the cutoff current.** There are constants `K` and `r₀ > 0`, depending only
on `C`, `c` and `c₀`, with the following property. Let `Θ = i F_a + d(χ(|α|²) τ)` be the cutoff
current of a pair `(a, α)` in a coordinate chart `E`, built with a cutoff `χ` equal to one above
`1 / 2`. For `r ≥ r₀` and `h > 0`, at every point of the support of `Θ` where the off-zero bound
holds, with `w₊ = max (1 - |α|²) 0` and the set `Z` in place of the zero set of `α`, the point
lies within distance `K h` of `Z`. -/
theorem exists_forall_exists_dist_le_of_mem_tsupport_cutoffCurrent (C c c₀ : ℝ) (hc : 0 < c) :
    ∃ K r₀ : ℝ, 0 < r₀ ∧ ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {χ : ℝ → ℝ} {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {α : E → ℂ} (Z : Set E) (r h : ℝ),
      ContDiff ℝ 2 α → Differentiable ℝ b → EqOn χ 1 (Ioi (1 / 2)) → r₀ ≤ r → 0 < h →
      ∀ x ∈ tsupport (cutoffCurrent χ b α),
      (∀ R, c₀ * h ≤ R → (∀ z ∈ Z, R ≤ dist x z) →
        max (1 - Complex.normSq (α x)) 0 ≤
          C / r * max (1 - Complex.normSq (α x)) 0 + C / r + C * exp (-(c * R / h))) →
      ∃ z ∈ Z, dist x z ≤ K * h := by
  obtain ⟨K, r₀, hr₀, hK⟩ := exists_forall_exists_dist_le_of_le C c c₀ hc (σ := 1 / 2)
    (by norm_num)
  refine ⟨K, r₀, hr₀, ?_⟩
  intro E _ _ χ b α Z r h hα hb hχ hr hh x hx hbound
  exact hK (fun y ↦ Complex.normSq (α y)) Z r h hr hh x hbound
    (tsupport_cutoffCurrent_subset (by norm_num) hα hb hχ hx)

/-- **Zero localization at a vanishing tolerance.** There is a constant `K`, depending only on
`C`, `c` and `c₀`, with the following property. For every tolerance `ε(r)` tending to zero as
`r → ∞` there is `r₀ > 0` such that, for `r ≥ r₀` and `h > 0`, every point `x` at which the
off-zero bound holds and `|α(x)| ≤ ε(r)`, that is `s x ≤ ε(r) ^ 2` for `s = |α|²`, lies within
distance `K h` of `Z`. The radius `K` is the one of the threshold `|α| ≤ 1 / 2`. -/
theorem exists_forall_exists_dist_le_of_le_sq_of_tendsto (C c c₀ : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, ∀ ε : ℝ → ℝ, Tendsto ε atTop (nhds 0) → ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ {X : Type u} [PseudoMetricSpace X] (s : X → ℝ) (Z : Set X) (r h : ℝ), r₀ ≤ r → 0 < h →
      ∀ x : X,
      (∀ R, c₀ * h ≤ R → (∀ z ∈ Z, R ≤ dist x z) →
        max (1 - s x) 0 ≤ C / r * max (1 - s x) 0 + C / r + C * exp (-(c * R / h))) →
      s x ≤ ε r ^ 2 → ∃ z ∈ Z, dist x z ≤ K * h := by
  obtain ⟨K, r₀, hr₀, hK⟩ := exists_forall_exists_dist_le_of_le C c c₀ hc (σ := 1 / 4)
    (by norm_num)
  refine ⟨K, fun ε hε ↦ ?_⟩
  obtain ⟨r₁, hr₁⟩ := eventually_atTop.1 <|
    hε.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨max r₀ r₁, hr₀.trans_le (le_max_left _ _),
    fun s Z r h hr hh x hbound hs ↦ hK s Z r h ((le_max_left _ _).trans hr) hh x hbound ?_⟩
  have hεr : |ε r| ≤ 1 / 2 := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hr₁ r ((le_max_right _ _).trans hr)
  calc s x ≤ ε r ^ 2 := hs
    _ = |ε r| ^ 2 := (sq_abs _).symm
    _ ≤ (1 / 2) ^ 2 := by gcongr
    _ = 1 / 4 := by norm_num

end TauCeti.SeibergWitten
