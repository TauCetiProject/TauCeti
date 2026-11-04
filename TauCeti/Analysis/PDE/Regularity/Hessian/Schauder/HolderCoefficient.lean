/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Interior
import TauCeti.Analysis.Holder.LowerOrder
import TauCeti.Topology.MetricSpace.Holder

/-!
# The interior Schauder estimate for Hölder coefficients

Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be open and `K ⊆ Ω` compact, and let
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du·b + c u` be a non-divergence-form operator whose coefficients `a`, `b`
and `c` are `α`-Hölder near each point of `K`, with `a(x)` elliptic at each `x ∈ K`:
`λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. This file proves the interior Schauder estimate
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul`):
there is a constant `C` such that every `u` which is `C²` on `Ω`, with `D²u` `α`-Hölder on each
compact subset of `Ω`, satisfies

`[D²u]_{α; K} ≤ C ([L u]_{α; Ω} + N)`,

where `[·]_{α; S}` is the `α`-Hölder constant on `S` and `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on
`Ω`. The constant depends on `n`, `α`, `K`, `Ω` and the coefficients, but not on `u`. The
Hölder continuity of `D²u` on compact subsets of `Ω` enters only qualitatively: the estimate does
not depend on its Hölder constants. No boundary condition on `u` and no regularity of `Ω` are
used, and uniform ellipticity on `K` with explicit constants is not needed as a hypothesis. The
principal-part estimate is the case `b = 0`, `c = 0`.

## The argument

Around each `x ∈ K` choose a radius `Rₓ` with `closedBall x Rₓ ⊆ Ω`, so small that the Hölder
constant of the coefficients near `x` satisfies the scale condition of the interior estimate on
small balls
(`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`), with
the coefficients frozen at `x`. That estimate bounds the Hölder constant of `D²u` on
`closedBall x (Rₓ / 2)`. The lower-order terms are absorbed on each ball: when `Rₓ ≤ 1`, the
functions `u` and `Du` are `N`-Lipschitz on the convex ball `B(x, Rₓ)`, hence `α`-Hölder with
constant `N 2^{1-α}`, so `Du·b + c u` is `α`-Hölder there with constant `D N`, where `D` depends
only on `α` and the coefficients `b`, `c` near `x`
(`TauCeti.exists_holderOnWith_fderiv_apply_add_mul_ball`).
Thus `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = L u - (Du·b + c u)` is `α`-Hölder with constant `[L u]_{α; Ω} + D N` on
`B(x, Rₓ)`. Finitely many of the balls `B(x, Rₓ / 2)` cover `K`. If `δ` is a Lebesgue number of
this cover (`lebesgue_number_lemma_of_metric`), two points of `K` at distance less than
`δ` lie in one of these balls, while at larger distances
`‖D²u(x) - D²u(y)‖ ≤ 2N ≤ 2N δ^(-α) ‖x - y‖^α` (`HolderOnWith.of_dist_lt_of_dist_le`).

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
point `x` of an open set `Ω` and `a x` is elliptic, there is a radius `0 < R ≤ ρ` with
`closedBall x R ⊆ Ω` and a constant `C` such that the Hölder constant of `D²u` on
`closedBall x (R / 2)` is at most `C ([L u]_{α; B_R} + N)` for every `u` as in the interior
estimate on small balls. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_half {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {x : E} (hx : x ∈ Ω) {ρ : ℝ} (hρ : 0 < ρ)
    (ha : ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α (fun y => a y i j) (ball x r))
    (hell : ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ R : ℝ, 0 < R ∧ R ≤ ρ ∧ closedBall x R ⊆ Ω ∧ ∃ C : ℝ≥0,
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
  -- A radius `R < min r ρ` with `closedBall x R ⊆ Ω` satisfying the scale condition
  -- `c R^α ≤ λ`, which holds for all small `R` because `R^α → 0` as `R → 0`.
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  have h₁ : ∀ᶠ R in 𝓝[>] (0 : ℝ), R < min (min r ρ) ε :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (lt_min (lt_min hr hρ) hε))
  have h₂ : ∀ᶠ R in 𝓝[>] (0 : ℝ), c * R ^ (α : ℝ) < lam := by
    have ht : Tendsto (fun R : ℝ => c * R ^ (α : ℝ)) (𝓝 0) (𝓝 (c * 0 ^ (α : ℝ))) :=
      ((Real.continuous_rpow_const α.coe_nonneg).tendsto 0).const_mul c
    rw [Real.zero_rpow (by exact_mod_cast hα.ne'), mul_zero] at ht
    exact eventually_nhdsWithin_of_eventually_nhds (ht.eventually (eventually_lt_nhds hlam))
  obtain ⟨R, hR, hscale, hR₀⟩ := (h₁.and (h₂.and self_mem_nhdsWithin)).exists
  have hR₀ : 0 < R := hR₀
  obtain ⟨C, hC⟩ := hball hlam hlow (toQuadraticForm'_le_norm_matrixBilinearForm_mul_sq (a x)) hR₀
    (by simpa only [c, mul_assoc] using hscale.le)
    (fun i j => (hL i j).mono (closedBall_subset_ball
      (hR.trans_le ((min_le_left _ _).trans (min_le_left _ _)))))
    (half_lt_self hR₀)
  refine ⟨R, hR₀, (hR.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le,
    (closedBall_subset_ball (hR.trans_le (min_le_right _ _))).trans hεΩ, C,
    fun hu hN₀ hN₁ hN₂ hV hM => hC hu hN₀ hN₁ hN₂ hV hM⟩

/-- **The interior Schauder estimate around one point, with lower-order terms.** If the
coefficients `a`, `b` and `c` are `α`-Hölder near a point `x` of an open set `Ω` and `a x` is
elliptic, there is a radius `R > 0` with `closedBall x R ⊆ Ω` and a constant `C` such that the
Hölder constant of `D²u` on `closedBall x (R / 2)` is at most `C ([L u]_{α; B_R} + N)`, where
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du·b + c u`. -/
private theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_half_of_add {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Ω : Set E} (hΩ : IsOpen Ω)
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ} {x : E} (hx : x ∈ Ω)
    (ha : ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α (fun y => a y i j) (ball x r))
    (hb : ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α b (ball x r))
    (hc : ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α c (ball x r))
    (hell : ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ R : ℝ, 0 < R ∧ closedBall x R ⊆ Ω ∧ ∃ C : ℝ≥0,
      ∀ {u : E → ℝ} {N M V : ℝ≥0}, ContDiffOn ℝ 2 u (ball x R) →
        (∀ y ∈ ball x R, |u y| ≤ N) → (∀ y ∈ ball x R, ‖fderiv ℝ u y‖ ≤ N) →
        (∀ y ∈ ball x R, ‖iteratedFDeriv ℝ 2 u y‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x R) →
        HolderOnWith M α (fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u y (b y) +
            c y * u y) (ball x R) →
        HolderOnWith (C * (M + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x (R / 2)) := by
  obtain ⟨rb, hrb, Lb, hLb⟩ := hb
  obtain ⟨rc, hrc, Lc, hLc⟩ := hc
  set r := min (min rb rc) 1
  have hr : 0 < r := lt_min (lt_min hrb hrc) one_pos
  obtain ⟨R, hR, hRr, hRΩ, C₀, hC₀⟩ :=
    exists_holderOnWith_iteratedFDeriv_two_closedBall_half hα hα1 hΩ hx hr ha hell
  have hR1 : R ≤ 1 := hRr.trans (min_le_right _ _)
  have hBr : ball x R ⊆ ball x r := ball_subset_ball hRr
  have hrb' : r ≤ rb := (min_le_left _ _).trans (min_le_left _ _)
  have hrc' : r ≤ rc := (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨D, hD⟩ := exists_holderOnWith_fderiv_apply_add_mul_ball hα1.le hR1
    ((hLb.mono (hBr.trans (ball_subset_ball hrb'))).mono_const (le_max_left Lb Lc))
    ((hLc.mono (hBr.trans (ball_subset_ball hrc'))).mono_const (le_max_right Lb Lc))
  refine ⟨R, hR, hRΩ, C₀ * (D + 1),
    fun {u N M V} hu hN₀ hN₁ hN₂ hV hM => ?_⟩
  -- The principal part `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = L u - (Du·b + c u)` is Hölder with constant `M + D N`.
  set P : E → ℝ := fun y => ∑ i, ∑ j, a y i j • fderiv ℝ (fderiv ℝ u) y
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  set g : E → ℝ := fun y => fderiv ℝ u y (b y) + c y * u y
  have hg : HolderOnWith (D * N) α g (ball x R) := hD hu hN₀ hN₁ hN₂
  have hM₀ : HolderOnWith (M + D * N) α P (ball x R) := by
    have hPg : HolderOnWith M α (P + g) (ball x R) := by
      simpa only [P, g, Pi.add_def, add_assoc] using hM
    simpa only [add_sub_cancel_right] using hPg.sub hg
  refine (hC₀ hu hN₀ hN₁ hN₂ hV hM₀).mono_const ?_
  calc C₀ * (M + D * N + N) ≤ C₀ * ((D + 1) * (M + N)) := by
        gcongr
        calc M + D * N + N ≤ M + D * M + D * N + N := by gcongr; exact le_add_right le_rfl
          _ = (D + 1) * (M + N) := by ring
    _ = C₀ * (D + 1) * (M + N) := by ring

/-- **The interior Schauder estimate with lower-order terms.** Let `0 < α < 1`, let
`Ω ⊆ ℝ^{n+1}` be open and `K ⊆ Ω` compact, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + Du·b + c u` be an
operator whose coefficients `a` (entrywise), `b` and `c` are `α`-Hölder on a ball around each
`x ∈ K`, with `a x` elliptic at each `x ∈ K`, that is, `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`.
Then there is a constant `C`, depending on `a`, `b`, `c`, `K` and `Ω` but not on `u`, with the
following property. Let `u` be `C²` on `Ω`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded by `N` on `Ω`
and with `D²u` `α`-Hölder on every compact subset of `Ω` (with any constants). If `L u` is
`α`-Hölder on `Ω` with constant `M`, then `D²u` is `α`-Hölder on `K` with constant `C (M + N)`. -/
theorem exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_add_fderiv_add_mul
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Ω K : Set E} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {b : E → E} {c : E → ℝ}
    (ha : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j, HolderOnWith L α (fun y => a y i j) (ball x r))
    (hb : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α b (ball x r))
    (hc : ∀ x ∈ K, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α c (ball x r))
    (hell : ∀ x ∈ K, ∃ lam : ℝ, 0 < lam ∧ ∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ C : ℝ≥0, ∀ {u : E → ℝ} {N M : ℝ≥0}, ContDiffOn ℝ 2 u Ω →
      (∀ x ∈ Ω, |u x| ≤ N) → (∀ x ∈ Ω, ‖fderiv ℝ u x‖ ≤ N) →
      (∀ x ∈ Ω, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
      (∀ S ⊆ Ω, IsCompact S → ∃ V : ℝ≥0, HolderOnWith V α (iteratedFDeriv ℝ 2 u) S) →
      HolderOnWith M α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) + fderiv ℝ u x (b x) +
          c x * u x) Ω →
      HolderOnWith (C * (M + N)) α (iteratedFDeriv ℝ 2 u) K := by
  -- Around each point of `K`, a ball in `Ω` carrying the estimate on its concentric half ball.
  choose! R hR hRΩ C hC using fun x hx =>
    exists_holderOnWith_iteratedFDeriv_two_closedBall_half_of_add hα hα1 hΩ (hKΩ hx) (ha x hx)
      (hb x hx) (hc x hx) (hell x hx)
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (R x / 2)) fun x hx =>
      ball_mem_nhds x (half_pos (hR x hx))
  -- A Lebesgue number `δ` of the finite cover by the half balls.
  obtain ⟨δ, hδ, hδK⟩ := lebesgue_number_lemma_of_metric hK
    (c := fun z : t => ball (z : E) (R z / 2)) (fun _ => isOpen_ball) fun y hy => by
      obtain ⟨z, hzt, hyz⟩ := mem_iUnion₂.1 (hcover hy)
      exact mem_iUnion.2 ⟨⟨z, hzt⟩, hyz⟩
  set δ' : ℝ≥0 := ⟨δ, hδ.le⟩
  refine ⟨∑ z ∈ t, C z + 2 * δ' ^ (-(α : ℝ)), fun {u N M} hu hN₀ hN₁ hN₂ hV hM => ?_⟩
  -- Points of `K` at distance less than `δ` lie in one half ball.
  have hloc : ∀ x ∈ K, ∀ y ∈ K, dist x y < δ' → dist (iteratedFDeriv ℝ 2 u x)
      (iteratedFDeriv ℝ 2 u y) ≤ ((∑ z ∈ t, C z) * (M + N) : ℝ≥0) * dist x y ^ (α : ℝ) := by
    intro x hx y hy hxy
    obtain ⟨⟨z, hzt⟩, hz⟩ := hδK x hx
    have hzK := htK z hzt
    have hsub : ball z (R z) ⊆ Ω := ball_subset_closedBall.trans (hRΩ z hzK)
    obtain ⟨V, hV'⟩ := hV _ (hRΩ z hzK) (isCompact_closedBall z (R z))
    have key := hC z hzK (hu.mono hsub) (fun y hy => hN₀ y (hsub hy))
      (fun y hy => hN₁ y (hsub hy)) (fun y hy => hN₂ y (hsub hy))
      (hV'.mono ball_subset_closedBall) (hM.mono hsub)
    have hxz : x ∈ closedBall z (R z / 2) := ball_subset_closedBall (hz (mem_ball_self hδ))
    have hyz : y ∈ closedBall z (R z / 2) :=
      ball_subset_closedBall (hz (mem_ball.2 (by rw [dist_comm]; exact hxy)))
    refine (key.dist_le hxz hyz).trans ?_
    gcongr
    exact_mod_cast Finset.single_le_sum (fun _ _ => zero_le) hzt
  -- Points at larger distance are handled by the bound `‖D²u‖ ≤ N`.
  have hD : ∀ x ∈ K, ∀ y ∈ K,
      dist (iteratedFDeriv ℝ 2 u x) (iteratedFDeriv ℝ 2 u y) ≤ ((2 * N : ℝ≥0) : ℝ) := by
    intro x hx y hy
    refine (dist_le_norm_add_norm _ _).trans ?_
    push_cast
    linarith [hN₂ x (hKΩ hx), hN₂ y (hKΩ hy)]
  refine (HolderOnWith.of_dist_lt_of_dist_le (by exact_mod_cast hδ) hloc hD).mono_const ?_
  calc (∑ z ∈ t, C z) * (M + N) + 2 * N * δ' ^ (-(α : ℝ))
      ≤ (∑ z ∈ t, C z) * (M + N) + 2 * δ' ^ (-(α : ℝ)) * (M + N) := by
        rw [mul_right_comm]
        gcongr
        exact le_add_self
    _ = (∑ z ∈ t, C z + 2 * δ' ^ (-(α : ℝ))) * (M + N) := by ring

end TauCeti.PDE
