/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Interior
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure

/-!
# The interior Calderón–Zygmund estimate for continuous coefficients

Let `0 < n`, `1 < p < ∞`, and let `Ω ⊆ ℝⁿ` be open. This file proves the interior `W^{2,p}`
estimate for strong solutions of a non-divergence-form equation `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f` whose
coefficients are continuous on `Ω`
(`TauCeti.PDE.exists_lpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_continuousAt`). Let
`K ⊆ Ω` be compact, and let `a` be measurable on `Ω`, continuous at every point `x ∈ K`, with
`a x` elliptic there: `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. Coefficients continuous on `Ω`
are the main case. Then there is a constant `C` such that every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(Ω)` almost everywhere on `Ω` satisfies

`‖D²u‖_{Lᵖ(K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`.

The constant depends on `n`, `p`, `K`, `Ω` and the coefficient field `a`, but not on `u` or `f`.
No boundary condition is imposed on `u` and no regularity of `Ω` is used. Uniform ellipticity
on `K` with explicit constants is not needed as a hypothesis: ellipticity at each point of `K`
suffices, and the continuity of `a` at the points of `K` supplies the rest. Away from `K` the
coefficients need not be bounded, which is why `f` is assumed to lie in `Lᵖ(Ω)`.

## The argument

The interior estimate on balls
(`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_eq_of_abs_sub_le`)
gives constants `C₀` and `δ > 0`, depending only on `n` and `p`. By continuity of `a`, every
`x ∈ K` is the centre of a ball `B(x, 2rₓ) ⊆ Ω` on which `|aᵢⱼ - aᵢⱼ(x)| ≤ δ λₓ`, so the ball
estimate with the coefficients frozen at `A = a(x)` bounds `‖D²u‖_{Lᵖ(B(x, rₓ))}` by `f` and `u`.
By compactness finitely many of the balls `B(x, rₓ)` cover `K`, and the `Lᵖ` norm on `K` is at
most the sum of the `Lᵖ` norms on these balls
(`MeasureTheory.eLpNorm_restrict_biUnion_finset_le`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 9.11 and its proof (covering by balls on which the coefficients have small
  oscillation).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory TopologicalSpace Metric Filter
open scoped ENNReal NNReal InnerProductSpace Topology

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The interior Calderón–Zygmund estimate for continuous coefficients.** Let `0 < n` and
`1 < p < ∞`, let `Ω ⊆ ℝⁿ` be open and `K ⊆ Ω` compact, and let `a` be a matrix-valued coefficient,
measurable on `Ω` and continuous at each `x ∈ K`, such that `a x` is elliptic at each `x ∈ K`,
that is, `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. Then there is a constant `C`, depending on
`a`, `K` and `Ω` but not on `u` or `f`, such that every `u ∈ W^{2,p}(Ω)` with
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu = f ∈ Lᵖ(Ω)` almost everywhere on `Ω` satisfies

`‖D²u‖_{Lᵖ(K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u`. No boundary condition on `u`
and no regularity of `Ω` are assumed. -/
theorem exists_lpNorm_iteratedGradient_le_of_sum_mul_inner_eq_of_continuousAt (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ⊤) {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKΩ : K ⊆ Omega)
    {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))))
    (hcont : ∀ x ∈ K, ContinuousAt a x)
    (hell : ∀ x ∈ K, ∃ lam : ℝ, 0 < lam ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Omega)),
      (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))),
        ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict K) ≤
        C * (‖f‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hball⟩ :=
    exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_eq_of_abs_sub_le hn hp hp_top
  -- Around each point of `K`, a ball in `Ω` on which `a` oscillates by at most `δ λₓ`.
  have hloc : ∀ x ∈ K, ∃ lam : ℝ, 0 < lam ∧
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ) ∧
      ∃ r : ℝ, 0 < r ∧ ball x (2 * r) ⊆ Omega ∧
        ∀ y ∈ ball x (2 * r), ∀ i j, |a y i j - a x i j| ≤ δ * lam := by
    intro x hx
    obtain ⟨lam, hlam, hA⟩ := hell x hx
    have hΩx : (Omega : Set (EuclideanSpace ℝ (Fin n))) ∈ 𝓝 x :=
      Omega.isOpen.mem_nhds (hKΩ hx)
    have hev : ∀ᶠ y in 𝓝 x, y ∈ Omega ∧ ∀ i j, |a y i j - a x i j| ≤ δ * lam := by
      refine Eventually.and hΩx (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
      have hij : ContinuousAt (fun y => a y i j) x :=
        (continuous_id.matrix_elem i j).continuousAt.comp (hcont x hx)
      filter_upwards [Metric.tendsto_nhds.1 hij (δ * lam) (mul_pos hδ hlam)] with y hy
      exact (Real.dist_eq _ _ ▸ hy).le
    obtain ⟨ε, hε, hεx⟩ := Metric.eventually_nhds_iff_ball.1 hev
    refine ⟨lam, hlam, hA, ε / 2, half_pos hε, ?_, ?_⟩ <;> rw [mul_div_cancel₀ ε two_ne_zero]
    · exact fun y hy => (hεx y hy).1
    · exact fun y hy => (hεx y hy).2
  choose! lam hlam hA r hr hrΩ hosc using hloc
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (r x)) fun x hx => ball_mem_nhds x (hr x hx)
  -- A bound for the coefficients on `B(x, 2 rₓ)`.
  set Λ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i, ∑ j, |a x i j| + δ * lam x with hΛ
  set c : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    C₀ * (4 / lam x + (1 + Λ x / lam x) ^ 2 / r x ^ 2) with hc
  refine ⟨∑ x ∈ t, c x, fun u f heq => ?_⟩
  -- The `Lᵖ` norm of an `Lᵖ(Ω)` field on a subset of `Ω` is finite and at most its norm.
  have hsub : ∀ {G : Type} [NormedAddCommGroup G]
      (g : Lp G p (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))))
      {S : Set (EuclideanSpace ℝ (Fin n))}, S ⊆ Omega →
      eLpNorm g p (volume.restrict S) ≠ ⊤ ∧ lpNorm g p (volume.restrict S) ≤ ‖g‖ :=
    fun g S hS => ⟨((Lp.memLp g).mono_measure (Measure.restrict_mono hS le_rfl)).eLpNorm_ne_top,
      ENNReal.toReal_mono (Lp.eLpNorm_ne_top g)
        (eLpNorm_mono_measure _ (Measure.restrict_mono hS le_rfl))⟩
  set F := ‖f‖
  set U := ‖Wkp.value 2 u‖
  -- The ball estimate on each ball of the cover.
  have hlocal : ∀ x ∈ t,
      lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x (r x))) ≤ c x * (F + U) := by
    intro x hxt
    have hx := htK x hxt
    have hr0 := hr x hx
    have hl0 := hlam x hx
    have hR := hrΩ x hx
    have hΛ0 : 0 ≤ Λ x := by rw [hΛ]; positivity
    have haΛ : ∀ y ∈ ball x (2 * r x), ∀ i j, |a y i j| ≤ Λ x := fun y hy i j => by
      have h1 : |a x i j| ≤ ∑ i', ∑ j', |a x i' j'| :=
        (Finset.single_le_sum (f := fun j' => |a x i j'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i' => ∑ j', |a x i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
      have h2 := abs_sub_abs_le_abs_sub (a y i j) (a x i j)
      have h3 := hosc x hx y hy i j
      rw [hΛ]
      linarith
    -- The inner radius `rₓ` is below the outer radius `2 rₓ`, with gap exactly `rₓ`.
    have hlt : r x < 2 * r x := by linarith
    have hgap : 2 * r x - r x = r x := by ring
    have key := hball hl0 (hA x hx) hlt hR
      (ha.mono_measure (Measure.restrict_mono hR le_rfl)) le_rfl
      (Eventually.of_forall (hosc x hx)) hΛ0 (Eventually.of_forall haΛ) u f
      (ae_restrict_of_ae_restrict_of_subset hR heq)
    have hF := (hsub f hR).2
    have hU := (hsub (Wkp.value 2 u) hR).2
    have hF0 : 0 ≤ F := norm_nonneg _
    have hU0 : 0 ≤ U := norm_nonneg _
    rw [hgap] at key
    -- Divide by `rₓ²` and enlarge the norms on `B(x, 2 rₓ)` to the norms on `Ω`.
    have hbound : r x ^ 2 * lpNorm (Wkp.iteratedGradient 1 u) p
        (volume.restrict (ball x (r x))) ≤ r x ^ 2 * (c x * (F + U)) := by
      refine key.trans ?_
      have hsplit : r x ^ 2 * (c x * (F + U)) = C₀ * ((2 * r x) ^ 2 / lam x * F +
          (1 + Λ x / lam x) ^ 2 * U + (r x ^ 2 * (4 / lam x) * U +
            (1 + Λ x / lam x) ^ 2 * F)) := by
        rw [hc]
        field_simp
        ring
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ C₀.2
      have h1 : (2 * r x) ^ 2 / lam x *
          lpNorm f p (volume.restrict (ball x (2 * r x))) ≤ (2 * r x) ^ 2 / lam x * F := by
        gcongr
      have h2 : (1 + Λ x / lam x) ^ 2 * lpNorm (Wkp.value 2 u) p
          (volume.restrict (ball x (2 * r x))) ≤ (1 + Λ x / lam x) ^ 2 * U := by
        gcongr
      have h3 : 0 ≤ r x ^ 2 * (4 / lam x) * U + (1 + Λ x / lam x) ^ 2 * F := by positivity
      linarith
    exact le_of_mul_le_mul_left hbound (by positivity)
  -- Sum the local estimates over the cover.
  have hfin : ∀ x ∈ t, eLpNorm (Wkp.iteratedGradient 1 u) p
      (volume.restrict (ball x (r x))) ≠ ⊤ := fun x hxt =>
    (hsub (Wkp.iteratedGradient 1 u)
      ((ball_subset_ball (by linarith [hr x (htK x hxt)])).trans (hrΩ x (htK x hxt)))).1
  calc lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict K)
      ≤ ∑ x ∈ t, lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x (r x))) := by
        rw [← toReal_eLpNorm]
        simp_rw [← toReal_eLpNorm]
        rw [← ENNReal.toReal_sum hfin]
        exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin)
          ((eLpNorm_mono_measure _ (Measure.restrict_mono hcover le_rfl)).trans
            (eLpNorm_restrict_biUnion_finset_le _ hp.le t _))
    _ ≤ ∑ x ∈ t, c x * (F + U) := Finset.sum_le_sum hlocal
    _ = (∑ x ∈ t, c x) * (F + U) := (Finset.sum_mul _ _ _).symm

end PDE

end TauCeti
