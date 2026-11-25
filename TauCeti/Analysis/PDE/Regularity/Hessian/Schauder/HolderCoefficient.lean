/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import TauCeti.Topology.MetricSpace.Holder

/-!
# The interior Schauder estimate for Hölder coefficients

Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be open and `K ⊆ Ω` compact, and let
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form operator whose coefficients are `α`-Hölder near
each point of `K`, with `a(x)` elliptic at each `x ∈ K`: `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`.
This file proves the interior Schauder estimate
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith`):
there is a constant `C` such that every `u` which is `C²` on `Ω`, with `D²u` `α`-Hölder on each
compact subset of `Ω`, satisfies

`[D²u]_{α; K} ≤ C ([L u]_{α; Ω} + N)`,

where `[·]_{α; S}` is the `α`-Hölder constant on `S` and `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on
`Ω`. The constant depends on `n`, `α`, `K`, `Ω` and the coefficient field `a`, but not on `u`. The
Hölder continuity of `D²u` on compact subsets of `Ω` enters only qualitatively: the estimate does
not depend on its Hölder constants. No boundary condition on `u` and no regularity of `Ω` are
used, and uniform ellipticity on `K` with explicit constants is not needed as a hypothesis.

## The argument

Around each `x ∈ K` choose a radius `Rₓ` with `closedBall x Rₓ ⊆ Ω`, so small that the Hölder
constant of the coefficients near `x` satisfies the scale condition of the interior estimate on
small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`), with
the coefficients frozen at `x`. That estimate bounds the Hölder constant of `D²u` on
`closedBall x (Rₓ / 2)`. Finitely many of the balls `B(x, Rₓ / 2)` cover `K`. If `δ` is a Lebesgue
number of this cover (`lebesgue_number_lemma_of_metric`), two points of `K` at distance less than
`δ` lie in one of these balls, while at larger distances
`‖D²u(x) - D²u(y)‖ ≤ 2N ≤ 2N δ^(-α) ‖x - y‖^α`. This covering argument is
`IsCompact.exists_holderOnWith_of_forall_holderOnWith_ball_inter`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, Theorem 6.2 and Corollary 6.3 (interior Schauder estimates on compact subsets).
-/

public section

noncomputable section

open Metric Set Filter Topology
open scoped NNReal

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The interior Schauder estimate around one point.** If the coefficients are `α`-Hölder near a
point `x` of an open set `Ω` and `a x` is elliptic, there is a radius `R > 0` with
`closedBall x R ⊆ Ω` and a constant `C` such that the Hölder constant of `D²u` on
`closedBall x (R / 2)` is at most `C ([L u]_{α; B_R} + N)` for every `u` as in the interior
estimate on small balls. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_half {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {x : E} (hx : x ∈ Ω)
    (ha : ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α (fun y => a y i j) (ball x r))
    (hell : ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ Ω ∧ ∃ C : ℝ≥0,
      ∀ {u : E → ℝ} {N M V : ℝ≥0}, ContDiffOn ℝ 2 u (ball x R) →
        (∀ y ∈ ball x R, |u y| ≤ N) → (∀ y ∈ ball x R, ‖fderiv ℝ u y‖ ≤ N) →
        (∀ y ∈ ball x R, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x R) →
        HolderOnWith M α (fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x R) →
        HolderOnWith (C * (M + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x (R / 2)) := by
  obtain ⟨C₀, -, hball⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv hα hα1 (n := n)
  obtain ⟨r, hr, L, hL⟩ := ha
  obtain ⟨lam, hlam, hlow⟩ := hell
  -- The upper ellipticity constant of the frozen matrix `a x`, and the coefficient `c` of `R^α`
  -- in the scale condition.
  set Lam := ‖matrixBilinearForm (a x)‖
  set c : ℝ := 2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
    ((1 + 2 ^ (α : ℝ)) * L)
  -- A radius `R < r` with `closedBall x R ⊆ Ω` satisfying the scale condition `c R^α ≤ λ`, which
  -- holds for all small `R` because `R^α → 0` as `R → 0`.
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  have h₁ : ∀ᶠ R in 𝓝[>] (0 : ℝ), R < min r ε :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min hr hε))
  have h₂ : ∀ᶠ R in 𝓝[>] (0 : ℝ), c * R ^ (α : ℝ) < lam := by
    have ht : Tendsto (fun R : ℝ => c * R ^ (α : ℝ)) (𝓝 0) (𝓝 (c * 0 ^ (α : ℝ))) :=
      ((Real.continuous_rpow_const α.coe_nonneg).tendsto 0).const_mul c
    rw [Real.zero_rpow (by exact_mod_cast hα.ne'), mul_zero] at ht
    exact eventually_nhdsWithin_of_eventually_nhds (ht.eventually (eventually_lt_nhds hlam))
  obtain ⟨R, hR, hscale, hR₀⟩ := (h₁.and (h₂.and self_mem_nhdsWithin)).exists
  have hR₀ : 0 < R := hR₀
  have hLR (i j : Fin (n + 1)) : HolderOnWith L α (fun y => a y i j) (closedBall x R) :=
    (hL i j).mono (closedBall_subset_ball (hR.trans_le (min_le_left _ _)))
  -- A bound `M` for the coefficients on `closedBall x R`, where they are continuous.
  choose Ma hMa using fun i j => (isCompact_closedBall x R).exists_bound_of_continuousOn
    ((hLR i j).continuousOn hα)
  set M : ℝ≥0 := ∑ i, ∑ j, (Ma i j).toNNReal
  have hM (y : E) (hy : y ∈ closedBall x R) (i j : Fin (n + 1)) : |a y i j| ≤ M := by
    calc |a y i j| ≤ Ma i j := by simpa only [Real.norm_eq_abs] using hMa i j y hy
      _ ≤ (Ma i j).toNNReal := Real.le_coe_toNNReal _
      _ ≤ M := by
        exact_mod_cast (Finset.single_le_sum (f := fun j => (Ma i j).toNNReal)
          (fun _ _ => zero_le) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, (Ma i j).toNNReal) (fun _ _ => zero_le)
            (Finset.mem_univ i))
  obtain ⟨C, hC⟩ := hball (M := M) hlam (by simpa only [c, mul_assoc] using hscale.le)
    (half_lt_self hR₀)
  refine ⟨R, hR₀, (closedBall_subset_ball (hR.trans_le (min_le_right _ _))).trans hεΩ, C,
    fun hu hN₀ hN₁ hN₂ hV hK => hC hlow (toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq (a x))
      hLR hM hu hN₀ hN₁ hN₂ hV hK⟩

/-- **The interior Schauder estimate for Hölder coefficients.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be open and `K ⊆ Ω` compact, and let `a` be a matrix-valued coefficient which is
`α`-Hölder on a ball around each `x ∈ K`, with `a x` elliptic at each `x ∈ K`, that is,
`λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. Put `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu`. Then there is a constant `C`,
depending on `a`, `K` and `Ω` but not on `u`, with the following property. Let `u` be `C²` on `Ω`,
with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `Ω` and with `D²u` `α`-Hölder on every compact
subset of `Ω` (with any constants). If `L u` is `α`-Hölder on `Ω` with constant `M`, then `D²u` is
`α`-Hölder on `K` with constant `C (M + N)`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α (fun y => a y i j) (ball x r))
    (hell : ∀ x ∈ K, ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ} {N M : ℝ≥0}, ContDiffOn ℝ 2 u Ω →
      (∀ x ∈ Ω, |u x| ≤ N) → (∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ N) →
      (∀ x ∈ Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
      (∀ S ⊆ Ω, IsCompact S → ∃ V : ℝ≥0, HolderOnWith V α (iteratedFDeriv ℝ 2 u) S) →
      HolderOnWith M α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) Ω →
      HolderOnWith (C * (M + N)) α (iteratedFDeriv ℝ 2 u) K := by
  -- Around each point of `K`, a ball in `Ω` carrying the estimate on its concentric half ball.
  choose! R hR hRΩ C hC using fun x hx =>
    exists_holderOnWith_iteratedFDeriv_two_closedBall_half hα hα1 hΩ (hKΩ hx) (ha x hx)
      (hell x hx)
  -- The covering lemma assembles the estimates on the half balls into one on `K`.
  obtain ⟨A, hA⟩ := hK.exists_holderOnWith_of_forall_holderOnWith_ball_inter
    (fun x hx => half_pos (hR x hx)) C (α := α) (Y := E [×2]→L[ℝ] ℝ)
  refine ⟨A, fun {u N M} hu hN₀ hN₁ hN₂ hV hM => hA (fun x hx => (hN₂ x (hKΩ hx)).trans ?_)
    fun z hzK => ?_⟩
  · push_cast
    exact le_add_of_nonneg_left M.coe_nonneg
  have hsub : ball z (R z) ⊆ Ω := ball_subset_closedBall.trans (hRΩ z hzK)
  obtain ⟨V, hV'⟩ := hV _ (hRΩ z hzK) (isCompact_closedBall z (R z))
  exact (hC z hzK (hu.mono hsub) (fun y hy => hN₀ y (hsub hy)) (fun y hy => hN₁ y (hsub hy))
    (fun y hy => hN₂ y (hsub hy)) (hV'.mono ball_subset_closedBall) (hM.mono hsub)).mono
    (inter_subset_left.trans ball_subset_closedBall)

end TauCeti.PDE
