/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Interior
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.MeasureTheory.Function.LpSeminorm.AddMeasure
import TauCeti.Topology.Instances.Matrix

/-!
# The interior Calderón–Zygmund estimate for continuous coefficients

Let `0 < n`, `1 < p < ∞`, and let `Ω ⊆ ℝⁿ` be open. This file proves the interior `W^{2,p}`
estimate for strong solutions of a non-divergence-form equation
`∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ⟪b, ∇u⟫ + c u = f` whose principal coefficients are continuous on `Ω` and whose
lower-order coefficients are bounded, in
`PDE.exists_lpNorm_iteratedGradient_le_of_sum_mul_inner_add_inner_add_mul_eq_of_continuousAt`.
Let `K ⊆ Ω` be compact, and let `a` be measurable on `Ω`, continuous at every point `x ∈ K`, with
`a x` elliptic there: `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. Coefficients continuous on `Ω`
are the main case. Let `b` and `c` be measurable with `‖b‖ ≤ β` and `|c| ≤ γ` almost everywhere
on `Ω`. Then there is a constant `C` such that every `u ∈ W^{2,p}(Ω)` solving the equation with
`f ∈ Lᵖ(Ω)` almost everywhere on `Ω` satisfies

`‖D²u‖_{Lᵖ(K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`.

The constant depends on `n`, `p`, `K`, `Ω`, the coefficient field `a` and the bounds `β` and `γ`,
but not on `u` or `f`. No boundary condition is imposed on `u` and no regularity of `Ω` is used.
Uniform ellipticity on `K` with explicit constants is not needed as a hypothesis: ellipticity at
each point of `K` suffices, and the continuity of `a` at the points of `K` supplies the rest. Away
from `K` the principal coefficients need not be bounded, which is why `f` is assumed to lie in
`Lᵖ(Ω)`. The case `b = 0`, `c = 0` is the estimate for the principal part alone.

## The argument

The interior estimate on balls
(`TauCeti.PDE.exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_add_inner_add_mul_eq`)
gives constants `C₀` and `δ > 0`, depending only on `n` and `p`. By continuity of `a`, every
`x ∈ K` is the centre of a ball `B(x, 2rₓ) ⊆ Ω` on which `|aᵢⱼ - aᵢⱼ(x)| ≤ δ λₓ`
(`ContinuousAt.exists_ball_subset_forall_abs_sub_le`), so the ball
estimate with the coefficients frozen at `A = a(x)` bounds `‖D²u‖_{Lᵖ(B(x, rₓ))}` by `f` and `u`,
the bounds `β` and `γ` on `b` and `c` entering its constant.
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

/-- If every entry of `a` is within `ε` of the corresponding entry of `A`, then `|aᵢⱼ|` is at most
the sum of the absolute values of the entries of `A` plus `ε`. -/
theorem abs_le_sum_abs_add {m k : Type*} [Fintype m] [Fintype k] {A : Matrix m k ℝ} {i : m} {j : k}
    {x ε : ℝ} (h : |x - A i j| ≤ ε) : |x| ≤ ∑ i', ∑ j', |A i' j'| + ε := by
  have h1 : |A i j| ≤ ∑ i', ∑ j', |A i' j'| :=
    (Finset.single_le_sum (f := fun j' => |A i j'|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i' => ∑ j', |A i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  have h2 := abs_sub_abs_le_abs_sub x (A i j)
  linarith

/-- The arithmetic of the ball estimate: dividing `r² G ≤ C₀ ((2r)²/λ · Lf + T · Lu)` by `r²` and
enlarging the norms `Lf ≤ F`, `Lu ≤ U` gives `G ≤ C₀ (4/λ + T/r²)(F + U)`. -/
private theorem interior_bound_of_le_mul_add {C₀ : ℝ≥0} {lam r T F U G Lf Lu : ℝ} (hl0 : 0 < lam)
    (hr0 : 0 < r) (hT0 : 0 ≤ T) (hF0 : 0 ≤ F) (hU0 : 0 ≤ U) (hLf : Lf ≤ F) (hLu : Lu ≤ U)
    (key : r ^ 2 * G ≤ C₀ * ((2 * r) ^ 2 / lam * Lf + T * Lu)) :
    G ≤ C₀ * (4 / lam + T / r ^ 2) * (F + U) := by
  have hbound : r ^ 2 * G ≤ r ^ 2 * (C₀ * (4 / lam + T / r ^ 2) * (F + U)) := by
    refine key.trans ?_
    have hsplit : r ^ 2 * (C₀ * (4 / lam + T / r ^ 2) * (F + U)) =
        C₀ * ((2 * r) ^ 2 / lam * F + T * U + (r ^ 2 * (4 / lam) * U + T * F)) := by
      field_simp
      ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ C₀.2
    have h1 : (2 * r) ^ 2 / lam * Lf ≤ (2 * r) ^ 2 / lam * F := by gcongr
    have h2 : T * Lu ≤ T * U := mul_le_mul_of_nonneg_left hLu hT0
    have h3 : 0 ≤ r ^ 2 * (4 / lam) * U + T * F :=
      add_nonneg (by positivity) (mul_nonneg hT0 hF0)
    linarith
  exact le_of_mul_le_mul_left hbound (by positivity)

/-- **The ball estimate with norms on `Ω`.** On a ball `B(x₀, 2r) ⊆ Ω` on which `a` oscillates
around an elliptic matrix `A` by at most `δ λ`, the interior estimate on balls bounds `D²u` on
`B(x₀, r)` by the `Lᵖ(Ω)` norms of `f` and `u`, with the coefficient bound
`Λ = ∑ᵢⱼ |Aᵢⱼ| + δ λ` on `B(x₀, 2r)` and the bounds `β` and `γ` on the lower-order
coefficients. -/
private theorem exists_lpNorm_iteratedGradient_ball_le_mul_norm_add_norm (hn : 0 < n)
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    ∃ C₀ : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧ ∀ {A : Matrix (Fin n) (Fin n) ℝ} {lam : ℝ}, 0 < lam →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ) →
      ∀ {Omega : Opens (EuclideanSpace ℝ (Fin n))} {x₀ : EuclideanSpace ℝ (Fin n)} {r : ℝ},
        0 < r → ball x₀ (2 * r) ⊆ Omega →
      ∀ {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
        {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
        {c : EuclideanSpace ℝ (Fin n) → ℝ} {β γ : ℝ},
        AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))) →
        (∀ y ∈ ball x₀ (2 * r), ∀ i j, |a y i j - A i j| ≤ δ * lam) →
        AEStronglyMeasurable b (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))) →
        (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))), ‖b x‖ ≤ β) →
        AEStronglyMeasurable c (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))) →
        (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))), |c x| ≤ γ) →
      ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
        (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Omega)),
        (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))),
          ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
            EuclideanSpace.single j 1⟫_ℝ +
            ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ +
            c x * Wkp.value 2 u x = f x) →
        lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict (ball x₀ r)) ≤
          C₀ * (4 / lam + (1 + (∑ i, ∑ j, |A i j| + δ * lam + β * (2 * r) +
            γ * (2 * r) ^ 2) / lam) ^ 2 / r ^ 2) * (‖f‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hball⟩ :=
    exists_mul_lpNorm_iteratedGradient_ball_le_of_sum_mul_inner_add_inner_add_mul_eq hn hp hp_top
  refine ⟨C₀, δ, hδ, fun {A lam} hl0 hA {Omega x₀ r} hr0 hR {a b c β γ} ha hosc hb hbβ hc hcγ
    u f heq => ?_⟩
  set Λ := ∑ i, ∑ j, |A i j| + δ * lam with hΛ
  set T := (1 + (Λ + β * (2 * r) + γ * (2 * r) ^ 2) / lam) ^ 2 with hT
  have hT0 : 0 ≤ T := sq_nonneg _
  -- The bounds on `Ω` restrict to `B(x₀, 2 r)`.
  have hball_ae : ∀ {P : EuclideanSpace ℝ (Fin n) → Prop},
      (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))), P x) →
      ∀ᵐ x, x ∈ ball x₀ (2 * r) → P x := fun hP =>
    ((ae_restrict_iff' Omega.isOpen.measurableSet).1 hP).mono fun x hx hxb => hx (hR hxb)
  have haΛ : ∀ y ∈ ball x₀ (2 * r), ∀ i j, |a y i j| ≤ Λ := fun y hy i j =>
    abs_le_sum_abs_add (hosc y hy i j)
  -- The inner radius `r` is below the outer radius `2 r`, with gap exactly `r`.
  have hlt : r < 2 * r := by linarith
  have hgap : 2 * r - r = r := by ring
  have key := hball hl0 hA hlt hR (ha.mono_measure (Measure.restrict_mono hR le_rfl)) le_rfl
    (Eventually.of_forall hosc) (Eventually.of_forall haΛ)
    (hb.mono_measure (Measure.restrict_mono hR le_rfl)) (hball_ae hbβ)
    (hc.mono_measure (Measure.restrict_mono hR le_rfl)) (hball_ae hcγ) u f
    (ae_restrict_of_ae_restrict_of_subset hR heq)
  rw [hgap] at key
  exact interior_bound_of_le_mul_add hl0 hr0 hT0 (norm_nonneg f) (norm_nonneg (Wkp.value 2 u))
    (lpNorm_mono_measure (Lp.memLp f) (Measure.restrict_mono hR le_rfl))
    (lpNorm_mono_measure (Lp.memLp _) (Measure.restrict_mono hR le_rfl)) key

/-- **The interior Calderón–Zygmund estimate for continuous coefficients.** Let `0 < n` and
`1 < p < ∞`, let `Ω ⊆ ℝⁿ` be open and `K ⊆ Ω` compact, and let `a` be a matrix-valued coefficient,
measurable on `Ω` and continuous at each `x ∈ K`, such that `a x` is elliptic at each `x ∈ K`,
that is, `λₓ ‖ξ‖² ≤ ξᵀ a(x) ξ` for some `λₓ > 0`. Let `b` and `c` be measurable lower-order
coefficients with `‖b(x)‖ ≤ β` and `|c(x)| ≤ γ` for almost every `x ∈ Ω`. Then there is a
constant `C`, depending on `a`, `β`, `γ`, `K` and `Ω` but not on `u` or `f`, such that every
`u ∈ W^{2,p}(Ω)` with `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu + ⟪b, ∇u⟫ + c u = f ∈ Lᵖ(Ω)` almost everywhere on `Ω`
satisfies

`‖D²u‖_{Lᵖ(K)} ≤ C (‖f‖_{Lᵖ(Ω)} + ‖u‖_{Lᵖ(Ω)})`,

where `D²u` is the weak Hessian `TauCeti.Wkp.iteratedGradient 1 u` and `∇u` the weak gradient
`TauCeti.Wkp.iteratedGradient 0 (TauCeti.Wkp.lowerOrder 1 u)`. No boundary condition on `u`
and no regularity of `Ω` are assumed, and the gradient of `u` does not appear on the right. -/
theorem exists_lpNorm_iteratedGradient_le_of_sum_mul_inner_add_inner_add_mul_eq_of_continuousAt
    (hn : 0 < n) (hp : 1 < p) (hp_top : p ≠ ⊤) {Omega : Opens (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKΩ : K ⊆ Omega)
    {a : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    (ha : AEStronglyMeasurable a (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))))
    (hcont : ∀ x ∈ K, ContinuousAt a x)
    (hell : ∀ x ∈ K, ∃ lam : ℝ, 0 < lam ∧
      ∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {β : ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))))
    (hbβ : ∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))), ‖b x‖ ≤ β)
    {c : EuclideanSpace ℝ (Fin n) → ℝ} {γ : ℝ}
    (hc : AEStronglyMeasurable c (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))))
    (hcγ : ∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))), |c x| ≤ γ) :
    ∃ C : ℝ, ∀ (u : Wkp (volume : Measure (EuclideanSpace ℝ (Fin n))) Omega p 2)
      (f : Lp ℝ p ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Omega)),
      (∀ᵐ x ∂(volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin n)))),
        ∑ i, ∑ j, a x i j * ⟪Wkp.iteratedGradient 1 u x (EuclideanSpace.single i 1),
          EuclideanSpace.single j 1⟫_ℝ +
          ⟪b x, Wkp.iteratedGradient 0 (Wkp.lowerOrder 1 u) x⟫_ℝ +
          c x * Wkp.value 2 u x = f x) →
      lpNorm (Wkp.iteratedGradient 1 u) p (volume.restrict K) ≤
        C * (‖f‖ + ‖Wkp.value 2 u‖) := by
  obtain ⟨C₀, δ, hδ, hball⟩ :=
    exists_lpNorm_iteratedGradient_ball_le_mul_norm_add_norm hn hp hp_top
  -- Around each point of `K`, a ball in `Ω` on which `a` oscillates by at most `δ λₓ`.
  choose! lam hlam hA using hell
  have hsmall : ∀ x ∈ K, ∃ r : ℝ, 0 < r ∧ ball x (2 * r) ⊆ Omega ∧
      ∀ y ∈ ball x (2 * r), ∀ i j, |a y i j - a x i j| ≤ δ * lam x := fun x hx => by
    obtain ⟨ρ, hρ, hρΩ, hρa⟩ := (hcont x hx).exists_ball_subset_forall_abs_sub_le
      (Omega.isOpen.mem_nhds (hKΩ hx)) (mul_pos hδ (hlam x hx))
    rw [← mul_div_cancel₀ ρ two_ne_zero] at hρΩ hρa
    exact ⟨ρ / 2, half_pos hρ, hρΩ, hρa⟩
  choose! r hr hrΩ hosc using hsmall
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun x => ball x (r x)) fun x hx => ball_mem_nhds x (hr x hx)
  set C : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    C₀ * (4 / lam x + (1 + (∑ i, ∑ j, |a x i j| + δ * lam x + β * (2 * r x) +
      γ * (2 * r x) ^ 2) / lam x) ^ 2 / r x ^ 2)
  refine ⟨∑ x ∈ t, C x, fun u f heq => ?_⟩
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
    _ ≤ ∑ x ∈ t, C x * (‖f‖ + ‖Wkp.value 2 u‖) := Finset.sum_le_sum fun x hxt =>
        hball (hlam x (htK x hxt)) (hA x (htK x hxt)) (hr x (htK x hxt)) (hrΩ x (htK x hxt)) ha
          (hosc x (htK x hxt)) hb hbβ hc hcγ u f heq
    _ = (∑ x ∈ t, C x) * (‖f‖ + ‖Wkp.value 2 u‖) := (Finset.sum_mul _ _ _).symm

end PDE

end TauCeti
