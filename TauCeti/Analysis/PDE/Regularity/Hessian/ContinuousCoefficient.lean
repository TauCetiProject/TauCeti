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

/-- Around a point `x` of an open set `Ω` at which `a` is continuous, for every `ε > 0` there is
a ball `B(x, 2r) ⊆ Ω` on which every entry of `a` differs from its value at `x` by at most `ε`. -/
private theorem exists_ball_subset_forall_abs_sub_le {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hxΩ : x ∈ Omega) (hcont : ContinuousAt a x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball x (2 * r) ⊆ Omega ∧
      ∀ y ∈ ball x (2 * r), ∀ i j, |a y i j - a x i j| ≤ ε := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ Omega ∧ ∀ i j, |a y i j - a x i j| ≤ ε := by
    refine Eventually.and (Omega.isOpen.mem_nhds hxΩ)
      (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    have hij : ContinuousAt (fun y => a y i j) x :=
      (continuous_id.matrix_elem i j).continuousAt.comp hcont
    filter_upwards [Metric.tendsto_nhds.1 hij ε hε] with y hy
    exact (Real.dist_eq _ _ ▸ hy).le
  obtain ⟨ρ, hρ, hρx⟩ := Metric.eventually_nhds_iff_ball.1 hev
  refine ⟨ρ / 2, half_pos hρ, ?_, ?_⟩ <;> rw [mul_div_cancel₀ ρ two_ne_zero]
  · exact fun y hy => (hρx y hy).1
  · exact fun y hy => (hρx y hy).2

/-- **The ball estimate with norms on `Ω`.** On a ball `B(x₀, 2r) ⊆ Ω` on which `a` oscillates
around an elliptic matrix `A` by at most `δ λ`, the interior estimate on balls bounds `D²u` on
`B(x₀, r)` by the `Lᵖ(Ω)` norms of `f` and `u`, with the coefficient bound
`Λ = ∑ᵢⱼ |Aᵢⱼ| + δ λ` on `B(x₀, 2r)`. -/
private theorem exists_lpNorm_iteratedGradient_ball_le_mul_norm_add_norm (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C₀ : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin n))} {x₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ},
        0 < r → ball x₀ (2 * r) ⊆ Omega →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ},
        AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))) →
        (∀ y ∈ ball x₀ (2 * r), ∀ i j, |a y i j - A i j| ≤ δ * lam) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Omega)),
        (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ = f x) →
        lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ r)) ≤
          C₀ * (4 / lam + (1 + (∑ i, ∑ j, |A i j| + δ * lam) / lam) ^ 2 / r ^ 2) *
            (‖f‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hball⟩ :=
    exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_eq_of_abs_sub_le hn hp hp_top
  refine ⟨C₀, δ, hδ, fun {A lam} hl0 hA {Omega x₀ r} hr0 hR {a} ha hosc u f heq => ?_⟩
  set Λ := ∑ i, ∑ j, |A i j| + δ * lam with hΛ
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have haΛ : ∀ y ∈ ball x₀ (2 * r), ∀ i j, |a y i j| ≤ Λ := fun y hy i j => by
    have h1 : |A i j| ≤ ∑ i', ∑ j', |A i' j'| :=
      (Finset.single_le_sum (f := fun j' => |A i j'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun i' => ∑ j', |A i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
    have h2 := abs_sub_abs_le_abs_sub (a y i j) (A i j)
    have h3 := hosc y hy i j
    rw [hΛ]
    linarith
  -- The inner radius `r` is below the outer radius `2 r`, with gap exactly `r`.
  have hlt : r < 2 * r := by linarith
  have hgap : 2 * r - r = r := by ring
  have key := hball hl0 hA hlt hR (ha.mono_measure (Measure.restrict_mono hR le_rfl)) le_rfl
    (Eventually.of_forall hosc) hΛ0 (Eventually.of_forall haΛ) u f
    (ae_restrict_of_ae_restrict_of_subset hR heq)
  set F := ‖f‖
  set U := ‖Wkp.value 2 u‖
  have hF : lpNorm f p (volume.restrict (ball x₀ (2 * r))) ≤ F :=
    lpNorm_mono_measure (Lp.memLp f) (Measure.restrict_mono hR le_rfl)
  have hU : lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ (2 * r))) ≤ U :=
    lpNorm_mono_measure (Lp.memLp _) (Measure.restrict_mono hR le_rfl)
  have hF0 : 0 ≤ F := norm_nonneg _
  have hU0 : 0 ≤ U := norm_nonneg _
  rw [hgap] at key
  -- Divide by `r²` and enlarge the norms on `B(x₀, 2 r)` to the norms on `Ω`.
  have hbound : r ^ 2 * lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ r)) ≤
      r ^ 2 * (C₀ * (4 / lam + (1 + Λ / lam) ^ 2 / r ^ 2) * (F + U)) := by
    refine key.trans ?_
    have hsplit : r ^ 2 * (C₀ * (4 / lam + (1 + Λ / lam) ^ 2 / r ^ 2) * (F + U)) =
        C₀ * ((2 * r) ^ 2 / lam * F + (1 + Λ / lam) ^ 2 * U +
          (r ^ 2 * (4 / lam) * U + (1 + Λ / lam) ^ 2 * F)) := by
      field_simp
      ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ C₀.2
    have h1 : (2 * r) ^ 2 / lam * lpNorm f p (volume.restrict (ball x₀ (2 * r))) ≤
        (2 * r) ^ 2 / lam * F := by
      gcongr
    have h2 : (1 + Λ / lam) ^ 2 * lpNorm (Wkp.value 2 u) p (volume.restrict (ball x₀ (2 * r))) ≤
        (1 + Λ / lam) ^ 2 * U := by
      gcongr
    have h3 : 0 ≤ r ^ 2 * (4 / lam) * U + (1 + Λ / lam) ^ 2 * F := by positivity
    linarith
  exact le_of_mul_le_mul_left hbound (by positivity)

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
    exists_lpNorm_iteratedGradient_ball_le_mul_norm_add_norm hn hp hp_top
  -- Around each point of `K`, a ball in `Ω` on which `a` oscillates by at most `δ λₓ`.
  choose! lam hlam hA using hell
  choose! r hr hrΩ hosc using fun x hx =>
    exists_ball_subset_forall_abs_sub_le (hKΩ hx) (hcont x hx) (mul_pos hδ (hlam x hx))
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (r x)) fun x hx => ball_mem_nhds x (hr x hx)
  set c : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    C₀ * (4 / lam x + (1 + (∑ i, ∑ j, |a x i j| + δ * lam x) / lam x) ^ 2 / r x ^ 2)
  refine ⟨∑ x ∈ t, c x, fun u f heq => ?_⟩
  -- Sum the ball estimates over the cover.
  have hfin : ∀ x ∈ t, eLpNorm (Wkp.iteratedGradient 1 u) p
      (volume.restrict (ball x (r x))) ≠ ⊤ := fun x hxt =>
    ((Lp.memLp _).mono_measure (Measure.restrict_mono ((ball_subset_ball
      (by linarith [hr x (htK x hxt)])).trans (hrΩ x (htK x hxt))) le_rfl)).eLpNorm_ne_top
  calc lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict K)
      ≤ ∑ x ∈ t, lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x (r x))) := by
        rw [← toReal_eLpNorm]
        simp_rw [← toReal_eLpNorm]
        rw [← ENNReal.toReal_sum hfin]
        exact ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin)
          ((eLpNorm_mono_measure _ (Measure.restrict_mono hcover le_rfl)).trans
            (eLpNorm_restrict_biUnion_finset_le _ hp.le t _))
    _ ≤ ∑ x ∈ t, c x * (‖f‖ + ‖Wkp.value 2 u‖) := Finset.sum_le_sum fun x hxt =>
        hball (hlam x (htK x hxt)) (hA x (htK x hxt)) (hr x (htK x hxt)) (hrΩ x (htK x hxt)) ha
          (hosc x (htK x hxt)) u f heq
    _ = (∑ x ∈ t, c x) * (‖f‖ + ‖Wkp.value 2 u‖) := (Finset.sum_mul _ _ _).symm

end PDE

end TauCeti
