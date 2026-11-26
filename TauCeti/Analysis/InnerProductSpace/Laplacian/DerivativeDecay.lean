/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.InnerProductSpace.Laplacian.Prod
import TauCeti.Analysis.Normed.Group.Prod
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Exp.Shift
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.Topology.Compactness.Normed

/-!
# Exponential decay of all derivatives of solutions of screened equations

Let `g` be a function on a finite-dimensional real inner product space `E`, with values in a real
normed space, solving

`Δ g = V • g + Φ`

outside a ball, where the potential satisfies `V ≥ a²` and has a bounded derivative. If `g` and the
derivative of the forcing `Φ` decay like `exp (-c ‖x‖)` for some `0 < c < a`, then so does the
derivative of `g` (`TauCeti.isBigO_fderiv_of_laplacian_eq_smul_add`). The proof compares
translates: `D = g (· + h) - g` solves the same equation up to a forcing of size
`‖h‖ exp (-c ‖x‖)`, so the forced exterior comparison principle for vector-valued functions
(`TauCeti.norm_le_mul_exp_add_div_mul_exp_of_norm_laplacian_sub_smul_le`) bounds `D` by `‖h‖`
times the same exponential. Dividing by `‖h‖` bounds the derivative.

Iterating this gives the regularity at infinity of the Liouville-type equation

`Δ ℓ = κ (exp ℓ - 1)`,

the scalar equation of the plane vortex: if `ℓ` is smooth near infinity and decays like
`exp (-c ‖x‖)` with `c² < κ`, then every iterated derivative of `ℓ` and of `exp ℓ - 1` decays like
`exp (-c ‖x‖)` (`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`,
`TauCeti.isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one`). The `n`-th derivative
`Dⁿℓ` solves `Δ Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ`, where the commutator `Cₙ = Dⁿ (exp ℓ) - exp ℓ • Dⁿℓ`
involves only derivatives of order below `n`, so each step of the induction is an instance of the
derivative estimate above. The rate is not lost along the induction.

Two solutions `ℓ₁`, `ℓ₂` of `Δ ℓ = κ (exp ℓ - 1)` outside a ball, tending to `0` at infinity,
approach each other at the rate `c` wherever `κ exp ℓᵢ ≥ c²`: their difference solves
`Δ u = V u` with `V` the difference quotient of `κ exp`, which is at least `c²`, so both `u` and
`-u` are subsolutions of `-Δ + V`, and `|u|` is at most its supremum on the boundary sphere times
`exp (-c (‖x‖ - R))` (`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`).

**Families.** The derivative estimate is proved for a family `g : P × E → G` of functions of
`z ∈ E` indexed by a parameter `p` in a finite-dimensional real normed space `P`, solving
`Δ_z g = V • g + Φ`, where `Δ_z` is the Laplacian in `z` at fixed `p`. With hypotheses uniform
for `‖p‖ ≤ r + δ`, the joint derivative of `g` in `(p, z)` decays like `exp (-c ‖z‖)` uniformly
for `‖p‖ ≤ r` (`TauCeti.exists_forall_norm_fderiv_le_mul_exp_of_laplacian_eq_smul_add`): the
translates `g (w + h) - g w` are now taken in both variables. A single function is the constant
family. Since `Δ_z` commutes with joint derivatives
(`ContDiff.laplacian_comp_prodMk_iteratedFDeriv`), a family of solutions of
`Δ_z ℓ = κ (exp ℓ - 1)` that is smooth and decays like `exp (-c ‖z‖)` uniformly on a region
`‖p‖ < r₁`, `‖z‖ > R₀` has all its joint derivatives decaying at the same rate, uniformly for
`‖p‖ ≤ r < r₁` (`TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_exp_sub_one`).
No bound on the derivative is assumed: at first order, the difference of two translates of the
family solves the unforced linear equation of the comparison above. These are the estimates for
the derivatives in the divisor and the point of families of plane vortices; the estimates for a
single solution of `Δ ℓ = κ (exp ℓ - 1)` are the case of the constant family.

## Main results

* `TauCeti.isBigO_fderiv_of_laplacian_eq_smul_add`: exponential decay of the derivative of a
  decaying solution of `Δ g = V • g + Φ`.
* `TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`: exponential decay of all iterated
  derivatives of a decaying solution of `Δ ℓ = κ (exp ℓ - 1)`.
* `TauCeti.isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one`: the same for
  `exp ℓ - 1`.
* `TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`: two solutions of
  `Δ ℓ = κ (exp ℓ - 1)` with `κ exp ℓᵢ ≥ c²` outside the ball of radius `R`, within `M` of each
  other on its boundary, are within `M exp (-c (‖x‖ - R))` of each other outside it.
* `TauCeti.exists_forall_norm_fderiv_le_mul_exp_of_laplacian_eq_smul_add`: uniform exponential
  decay of the joint derivative of a family of solutions of `Δ_z g = V • g + Φ`.
* `TauCeti.exists_forall_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_exp_sub_one`: uniform
  exponential decay of all joint derivatives of a family of solutions of `Δ_z ℓ = κ (exp ℓ - 1)`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (comparison with barriers) and §7.11 (difference quotients).
-/

public section

noncomputable section

namespace TauCeti

open Asymptotics Filter Metric Set Topology InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! ### Translates of families of forced screened solutions

The estimates of this file are proved for families `g : P × E → G` of functions of `z ∈ E`
indexed by a parameter `p` in a finite-dimensional real normed space `P`, with constants uniform
over a ball of parameters. A single function is the constant family. -/

/-- A step `0 < δ ≤ 1` with `s + δ < r`, for `s < r`. -/
private theorem exists_pos_le_one_add_lt {s r : ℝ} (hs : s < r) :
    ∃ δ, 0 < δ ∧ δ ≤ 1 ∧ s + δ < r :=
  ⟨min 1 ((r - s) / 2), lt_min one_pos (by linarith), min_le_left _ _,
    by linarith [min_le_right 1 ((r - s) / 2)]⟩

section Family

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

/-- A family that is `C¹` on the region `‖p‖ ≤ r + δ`, `‖z‖ ≥ R` is uniformly Lipschitz near a
bounded part of it: there is `M` with `‖f (w + h) - f w‖ ≤ M ‖h‖` for `‖w.1‖ ≤ r`,
`R + δ ≤ ‖w.2‖ ≤ R₁` and `‖h‖ ≤ δ`. -/
private theorem exists_norm_sub_le_mul_of_contDiffAt {F' : Type*}
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f : P × E → F'} {r δ R R₁ : ℝ}
    (hf : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ContDiffAt ℝ 1 f w) :
    ∃ M, 0 ≤ M ∧ ∀ w : P × E, ‖w.1‖ ≤ r → R + δ ≤ ‖w.2‖ → ‖w.2‖ ≤ R₁ → ∀ h : P × E,
      ‖h‖ ≤ δ → ‖f (w + h) - f w‖ ≤ M * ‖h‖ := by
  set A : Set (P × E) := {z | ‖z.1‖ ≤ r + δ ∧ R ≤ ‖z.2‖ ∧ ‖z.2‖ ≤ R₁ + δ}
  have hAc : IsCompact A := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
        ((isClosed_le continuous_const (continuous_norm.comp continuous_snd)).inter
          (isClosed_le (continuous_norm.comp continuous_snd) continuous_const))
    · refine (isBounded_iff_forall_norm_le.2 ⟨max (r + δ) (R₁ + δ), fun z hz ↦ ?_⟩)
      rw [Prod.norm_def]
      exact max_le_max hz.1 hz.2.2
  obtain ⟨M₀, hM₀⟩ := hAc.exists_bound_of_continuousOn (f := fderiv ℝ f) fun z hz ↦
    ((hf z hz.1 hz.2.1).continuousAt_fderiv (by norm_num)).continuousWithinAt
  refine ⟨max M₀ 0, le_max_right _ _, fun w hw₁ hw₂ hw₃ h hh ↦ ?_⟩
  have hsub : closedBall w ‖h‖ ⊆ A := fun z hz ↦ by
    obtain ⟨h₁, h₂⟩ := norm_fst_le_and_sub_le_norm_snd_of_mem_closedBall hz
    have h₃ : ‖z.2‖ ≤ ‖w.2‖ + ‖h‖ := by
      rw [mem_closedBall, dist_eq_norm] at hz
      have : ‖z.2 - w.2‖ ≤ ‖h‖ := (norm_snd_le (z - w)).trans hz
      linarith [norm_le_norm_add_norm_sub' z.2 w.2]
    exact ⟨by linarith, by linarith, by linarith⟩
  have hmem : w + h ∈ closedBall w ‖h‖ := by simp [mem_closedBall, dist_eq_norm]
  have h := (convex_closedBall w ‖h‖).norm_image_sub_le_of_norm_fderiv_le (f := f)
    (C := max M₀ 0) (fun z hz ↦ ((hf z (hsub hz).1 (hsub hz).2.1).differentiableAt (by norm_num)))
    (fun z hz ↦ (hM₀ z (hsub hz)).trans (le_max_left M₀ 0)) (mem_closedBall_self (norm_nonneg h))
    hmem
  simpa using h

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The points within `‖h‖ ≤ δ ≤ 1` of `(p, y)`, with `‖p‖ ≤ r` and `‖y‖ ≥ R + 1`, lie in the
region `‖p‖ ≤ r + δ`, `‖z‖ ≥ R`, and the weight `exp (-c ‖z‖)` there is at most `exp c` times
its value at `y`. -/
private theorem mem_region_of_mem_closedBall {r δ R c : ℝ} (hδ₁ : δ ≤ 1) (hc : 0 ≤ c) {p : P}
    (hp : ‖p‖ ≤ r) {h : P × E} (hh : ‖h‖ ≤ δ) {y : E} (hy : R + 1 ≤ ‖y‖) {z : P × E}
    (hz : z ∈ closedBall (p, y) ‖h‖) :
    ‖z.1‖ ≤ r + δ ∧ R ≤ ‖z.2‖ ∧
      Real.exp (-(c * ‖z.2‖)) ≤ Real.exp c * Real.exp (-(c * ‖y‖)) := by
  obtain ⟨h₁, h₂⟩ := norm_fst_le_and_sub_le_norm_snd_of_mem_closedBall hz
  simp only at h₁ h₂
  refine ⟨by linarith, by linarith, ?_⟩
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith

omit [FiniteDimensional ℝ P] in
/-- **The forcing of the equation for a translate.** Under the hypotheses of
`TauCeti.exists_norm_sub_le_mul_exp_of_laplacian_eq_smul_add`, the difference
`D = g ((p, ·) + h) - g (p, ·)` of two members of the family solves `Δ D = V (p, ·) • D` up to a
forcing of size `‖h‖ (L Kg + KΦ) exp c exp (-c ‖y‖)` outside the ball of radius `R + 1`. -/
private theorem norm_laplacian_sub_smul_translate_le {g Φ : P × E → G} {V : P × E → ℝ}
    {c r δ R L Kg KΦ : ℝ} (hc : 0 < c) (hδ₁ : δ ≤ 1) (hL : 0 ≤ L) (hKg : 0 ≤ Kg)
    (hKΦ : 0 ≤ KΦ) (hg : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ContDiffAt ℝ 2 g w)
    (hVd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → DifferentiableAt ℝ V w)
    (hVL : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ‖fderiv ℝ V w‖ ≤ L)
    (hΦd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → DifferentiableAt ℝ Φ w)
    (hΦ : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ →
      ‖fderiv ℝ Φ w‖ ≤ KΦ * Real.exp (-(c * ‖w.2‖)))
    (heq : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ →
      Δ (fun y ↦ g (w.1, y)) w.2 = V w • g w + Φ w)
    (hgd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ‖g w‖ ≤ Kg * Real.exp (-(c * ‖w.2‖)))
    {p : P} (hp : ‖p‖ ≤ r) {h : P × E} (hh : ‖h‖ ≤ δ) {y : E} (hy : R + 1 ≤ ‖y‖) :
    ‖Δ (fun t ↦ g ((p, t) + h) - g (p, t)) y - V (p, y) • (g ((p, y) + h) - g (p, y))‖ ≤
      ‖h‖ * ((L * Kg + KΦ) * Real.exp c) * Real.exp (-(c * ‖y‖)) := by
  have hreg := fun z (hz : z ∈ closedBall (p, y) ‖h‖) ↦
    mem_region_of_mem_closedBall hδ₁ hc.le hp hh hy hz
  have hyh : (p, y) + h ∈ closedBall (p, y) ‖h‖ := by simp [mem_closedBall, dist_eq_norm]
  have hpy : (p, y) ∈ closedBall (p, y) ‖h‖ := mem_closedBall_self (norm_nonneg h)
  have hpair : ∀ t : E, (p, t) + h = (p + h.1, t + h.2) := fun t ↦
    Prod.ext (Prod.fst_add _ _) (Prod.snd_add _ _)
  -- `Δ` of the difference is the difference of the values of `Δ_z g`.
  have hΔ : Δ (fun t : E ↦ g ((p, t) + h)) y =
      Δ (fun t ↦ g (((p, y) + h).1, t)) ((p, y) + h).2 := by
    simp only [hpair]
    exact congrFun (laplacian_comp_add_right (fun t ↦ g (p + h.1, t)) h.2) y
  have hgsh : ContDiffAt ℝ 2 (fun t ↦ g ((p, t) + h)) y :=
    (hg _ (hreg _ hyh).1 (hreg _ hyh).2.1).comp y
      ((contDiff_prodMk_right p).add contDiff_const).contDiffAt
  have hg₀ : ContDiffAt ℝ 2 (fun t ↦ g (p, t)) y :=
    (hg _ (hreg _ hpy).1 (hreg _ hpy).2.1).comp y (contDiff_prodMk_right p).contDiffAt
  have hsplit : Δ (fun t ↦ g ((p, t) + h) - g (p, t)) y - V (p, y) • (g ((p, y) + h) - g (p, y)) =
      (V ((p, y) + h) - V (p, y)) • g ((p, y) + h) + (Φ ((p, y) + h) - Φ (p, y)) := by
    rw [← Pi.sub_def, hgsh.laplacian_sub hg₀, hΔ, heq _ (hreg _ hyh).1 (hreg _ hyh).2.1,
      heq _ (hreg _ hpy).1 (hreg _ hpy).2.1]
    module
  -- Mean value bounds for `V` and `Φ` along the segment from `(p, y)` to `(p, y) + h`.
  have hVmv : ‖V ((p, y) + h) - V (p, y)‖ ≤ L * ‖(p, y) + h - (p, y)‖ :=
    (convex_closedBall (p, y) ‖h‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hVd z (hreg z hz).1 (hreg z hz).2.1)
      (fun z hz ↦ hVL z (hreg z hz).1 (hreg z hz).2.1) hpy hyh
  have hΦmv : ‖Φ ((p, y) + h) - Φ (p, y)‖ ≤
      (KΦ * (Real.exp c * Real.exp (-(c * ‖y‖)))) * ‖(p, y) + h - (p, y)‖ :=
    (convex_closedBall (p, y) ‖h‖).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hΦd z (hreg z hz).1 (hreg z hz).2.1)
      (fun z hz ↦ (hΦ z (hreg z hz).1 (hreg z hz).2.1).trans
        (mul_le_mul_of_nonneg_left (hreg z hz).2.2 hKΦ)) hpy hyh
  have hgyh : ‖g ((p, y) + h)‖ ≤ Kg * (Real.exp c * Real.exp (-(c * ‖y‖))) :=
    (hgd _ (hreg _ hyh).1 (hreg _ hyh).2.1).trans (mul_le_mul_of_nonneg_left (hreg _ hyh).2.2 hKg)
  rw [add_sub_cancel_left] at hVmv hΦmv
  rw [hsplit]
  calc ‖(V ((p, y) + h) - V (p, y)) • g ((p, y) + h) + (Φ ((p, y) + h) - Φ (p, y))‖
      ≤ ‖V ((p, y) + h) - V (p, y)‖ * ‖g ((p, y) + h)‖ + ‖Φ ((p, y) + h) - Φ (p, y)‖ :=
        (norm_add_le _ _).trans (by rw [norm_smul])
    _ ≤ (L * ‖h‖) * (Kg * (Real.exp c * Real.exp (-(c * ‖y‖)))) +
          (KΦ * (Real.exp c * Real.exp (-(c * ‖y‖)))) * ‖h‖ := by gcongr
    _ = ‖h‖ * ((L * Kg + KΦ) * Real.exp c) * Real.exp (-(c * ‖y‖)) := by ring

/-- **Translates of a family of forced screened solutions.** Let `g : P × E → G` solve
`Δ_z g = V • g + Φ` on the region `‖p‖ ≤ r + δ`, `‖z‖ ≥ R ≥ 1`, where `Δ_z` is the Laplacian in
`z`, `V ≥ a²` has derivative at most `L`, `g` is at most `Kg exp (-c ‖z‖)` and the derivative of
`Φ` at most `KΦ exp (-c ‖z‖)`, with `0 < c < a` and `0 < δ ≤ 1`. Then the differences
`g (w + h) - g w` with `‖h‖ ≤ δ` are at most `‖h‖` times a fixed multiple of `exp (-c ‖w.2‖)`
for `‖w.1‖ ≤ r` and `‖w.2‖ ≥ R + 1`. -/
private theorem exists_norm_sub_le_mul_exp_of_laplacian_eq_smul_add {g Φ : P × E → G}
    {V : P × E → ℝ} {a c r δ R L Kg KΦ : ℝ} (hc : 0 < c) (hca : c < a) (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1) (hR : 1 ≤ R) (hL : 0 ≤ L) (hKg : 0 ≤ Kg) (hKΦ : 0 ≤ KΦ)
    (hg : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ContDiffAt ℝ 2 g w)
    (hVd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → DifferentiableAt ℝ V w)
    (hVa : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → a ^ 2 ≤ V w)
    (hVL : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ‖fderiv ℝ V w‖ ≤ L)
    (hΦd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → DifferentiableAt ℝ Φ w)
    (hΦ : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ →
      ‖fderiv ℝ Φ w‖ ≤ KΦ * Real.exp (-(c * ‖w.2‖)))
    (heq : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ →
      Δ (fun y ↦ g (w.1, y)) w.2 = V w • g w + Φ w)
    (hgd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ‖g w‖ ≤ Kg * Real.exp (-(c * ‖w.2‖))) :
    ∃ K, 0 ≤ K ∧ ∀ w : P × E, ‖w.1‖ ≤ r → R + 1 ≤ ‖w.2‖ → ∀ h : P × E, ‖h‖ ≤ δ →
      ‖g (w + h) - g w‖ ≤ ‖h‖ * (K * Real.exp (-(c * ‖w.2‖))) := by
  -- On the sphere `‖z‖ = R + 1` the family is uniformly Lipschitz.
  obtain ⟨M, hM₀, hM⟩ := exists_norm_sub_le_mul_of_contDiffAt (R₁ := R + 1)
    fun w hw₁ hw₂ ↦ (hg w hw₁ hw₂).of_le (by norm_num)
  set B := (L * Kg + KΦ) * Real.exp c
  have hgap : 0 < a ^ 2 - c ^ 2 := by nlinarith
  refine ⟨M * Real.exp (c * (R + 1)) + B / (a ^ 2 - c ^ 2), by positivity,
    fun w hw₁ hw₂ h hh ↦ ?_⟩
  set p := w.1
  -- Each member of the family tends to zero at infinity, hence so does the difference `D`.
  have hlim : ∀ q : P, ‖q‖ ≤ r + δ → Tendsto (fun y ↦ g (q, y)) (cocompact E) (𝓝 0) :=
    fun q hq ↦ tendsto_cocompact_nhds_zero_of_norm_le_mul_exp hc fun y hy ↦ hgd (q, y) hq hy
  have hpair : ∀ y : E, (p, y) + h = (p + h.1, y + h.2) := fun y ↦
    Prod.ext (Prod.fst_add _ _) (Prod.snd_add _ _)
  have hDlim : Tendsto (fun y ↦ g ((p, y) + h) - g (p, y)) (cocompact E) (𝓝 0) := by
    have hsh := (hlim (p + h.1) (by linarith [norm_add_le p h.1, norm_fst_le h])).comp
      (Homeomorph.addRight h.2).isClosedEmbedding.tendsto_cocompact
    simp only [hpair]
    simpa [Function.comp_def] using hsh.sub (hlim p (by linarith))
  -- The forced comparison principle for `D` outside the ball of radius `R + 1`.
  have hcmp := norm_le_mul_exp_add_div_mul_exp_of_norm_laplacian_sub_smul_le
    (D := fun y ↦ g ((p, y) + h) - g (p, y)) (V := fun y ↦ V (p, y)) (M := M * ‖h‖)
    (B := ‖h‖ * B) (by linarith) hc hca (by positivity) (by positivity)
    (fun y hy ↦ by
      have hreg := fun z (hz : z ∈ closedBall (p, y) ‖h‖) ↦
        mem_region_of_mem_closedBall hδ₁ hc.le hw₁ hh hy hz
      exact ((hg _ (hreg _ (by simp [mem_closedBall, dist_eq_norm])).1
        (hreg _ (by simp [mem_closedBall, dist_eq_norm])).2.1).comp y
          ((contDiff_prodMk_right p).add contDiff_const).contDiffAt).sub
        ((hg _ (by simpa using (hreg _ (mem_closedBall_self (norm_nonneg h))).1)
          (by linarith)).comp y (contDiff_prodMk_right p).contDiffAt))
    (fun y hy ↦ hVa (p, y) (by simp only; linarith [(norm_nonneg h).trans hh]) (by
      simp only; linarith))
    (fun y hy ↦ norm_laplacian_sub_smul_translate_le hc hδ₁ hL hKg hKΦ hg hVd hVL hΦd hΦ heq hgd
      hw₁ hh hy.le)
    (fun y hy ↦ by
      simpa using hM (p, y) hw₁ (by simp only; linarith) (by simp only; linarith) h hh)
    hDlim hw₂
  have hwD : g (w + h) - g w = g ((p, w.2) + h) - g (p, w.2) := by simp [p]
  rw [hwD]
  refine hcmp.trans (le_of_eq ?_)
  rw [exp_neg_mul_sub]
  ring

/-- **Exponential decay of the derivatives of a family of forced screened solutions, uniformly in
the parameter.** Let `g : P × E → G` solve `Δ_z g = V • g + Φ` on the region `‖p‖ ≤ r + δ`,
`‖z‖ ≥ R ≥ 1`, where `Δ_z` is the Laplacian in `z ∈ E` at fixed `p`, `V ≥ a²` has derivative at
most `L`, `g` is at most `Kg exp (-c ‖z‖)` and the derivative of `Φ` at most
`KΦ exp (-c ‖z‖)`, with `0 < c < a` and `0 < δ ≤ 1`. Then the joint derivative of `g` in
`(p, z)` is at most `K exp (-c ‖z‖)` for `‖p‖ ≤ r` and `‖z‖ ≥ R + 1`. -/
theorem exists_forall_norm_fderiv_le_mul_exp_of_laplacian_eq_smul_add {g Φ : P × E → G}
    {V : P × E → ℝ} {a c r δ R L Kg KΦ : ℝ} (hc : 0 < c) (hca : c < a) (hδ : 0 < δ)
    (hδ₁ : δ ≤ 1) (hR : 1 ≤ R) (hL : 0 ≤ L) (hKg : 0 ≤ Kg) (hKΦ : 0 ≤ KΦ)
    (hg : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ContDiffAt ℝ 2 g w)
    (hVd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → DifferentiableAt ℝ V w)
    (hVa : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → a ^ 2 ≤ V w)
    (hVL : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ‖fderiv ℝ V w‖ ≤ L)
    (hΦd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → DifferentiableAt ℝ Φ w)
    (hΦ : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ →
      ‖fderiv ℝ Φ w‖ ≤ KΦ * Real.exp (-(c * ‖w.2‖)))
    (heq : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ →
      Δ (fun y ↦ g (w.1, y)) w.2 = V w • g w + Φ w)
    (hgd : ∀ w : P × E, ‖w.1‖ ≤ r + δ → R ≤ ‖w.2‖ → ‖g w‖ ≤ Kg * Real.exp (-(c * ‖w.2‖))) :
    ∃ K, 0 ≤ K ∧ ∀ w : P × E, ‖w.1‖ ≤ r → R + 1 ≤ ‖w.2‖ →
      ‖fderiv ℝ g w‖ ≤ K * Real.exp (-(c * ‖w.2‖)) := by
  obtain ⟨K, hK₀, hK⟩ := exists_norm_sub_le_mul_exp_of_laplacian_eq_smul_add hc hca hδ hδ₁ hR
    hL hKg hKΦ hg hVd hVa hVL hΦd hΦ heq hgd
  exact ⟨K, hK₀, fun w hw₁ hw₂ ↦
    norm_fderiv_le_of_forall_norm_sub_le hδ (by positivity) (hK w hw₁ hw₂)⟩

end Family

/-- **Exponential decay of the derivative of a forced screened solution.** Let `g : E → G` solve
`Δ g = V • g + Φ` outside a compact set, where `V ≥ a²` has a bounded derivative there. If `g`
and the derivative of the forcing `Φ` are `O(exp (-c ‖x‖))` at infinity with `0 < c < a`, then
so is the derivative of `g`. -/
theorem isBigO_fderiv_of_laplacian_eq_smul_add {g Φ : E → G} {V : E → ℝ} {a c : ℝ}
    (hc : 0 < c) (hca : c < a) (hg : ∀ᶠ x in cocompact E, ContDiffAt ℝ 2 g x)
    (hVd : ∀ᶠ x in cocompact E, DifferentiableAt ℝ V x)
    (hVa : ∀ᶠ x in cocompact E, a ^ 2 ≤ V x)
    (hVL : fderiv ℝ V =O[cocompact E] fun _ ↦ (1 : ℝ))
    (hΦd : ∀ᶠ x in cocompact E, DifferentiableAt ℝ Φ x)
    (hΦ : fderiv ℝ Φ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)))
    (heq : ∀ᶠ x in cocompact E, Δ g x = V x • g x + Φ x)
    (hgd : g =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) :
    fderiv ℝ g =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  obtain ⟨Kg, hKg⟩ := hgd.bound
  obtain ⟨L, hL⟩ := hVL.bound
  obtain ⟨KΦ, hKΦ⟩ := hΦ.bound
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸
      (hg.and (hVd.and (hVa.and (hL.and (hΦd.and (hKΦ.and (heq.and hKg))))))))
  set R := max R₀ 1
  -- Split the hypotheses, which hold outside the ball of radius `R`, into named statements.
  have hfar := fun (y : E) (hy : R ≤ ‖y‖) ↦
    hR₀ (Set.mem_ofPred.mpr ((le_max_left R₀ 1).trans hy))
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one, mul_one, forall_and] at hfar
  obtain ⟨hgR, hVdR, hVaR, hLR, hΦdR, hKΦR, heqR, hKgR⟩ := hfar
  -- Apply the estimate for families to the constant family `(t, z) ↦ g z` over `t ∈ ℝ`.
  obtain ⟨K, hK₀, hK⟩ := exists_norm_sub_le_mul_exp_of_laplacian_eq_smul_add (P := ℝ)
    (g := fun w ↦ g w.2) (V := fun w ↦ V w.2) (Φ := fun w ↦ Φ w.2) (r := 0)
    (L := max L 0) (Kg := max Kg 0) (KΦ := max KΦ 0) hc hca one_pos le_rfl
    (le_max_right R₀ 1) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
    (fun w _ hw ↦ (hgR w.2 hw).comp w contDiffAt_snd)
    (fun w _ hw ↦ (hVdR w.2 hw).comp w differentiableAt_snd)
    (fun w _ hw ↦ hVaR w.2 hw)
    (fun w _ hw ↦ (norm_fderiv_comp_snd_le V w).trans ((hLR w.2 hw).trans (le_max_left _ _)))
    (fun w _ hw ↦ (hΦdR w.2 hw).comp w differentiableAt_snd)
    (fun w _ hw ↦ (norm_fderiv_comp_snd_le Φ w).trans ((hKΦR w.2 hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)))
    (fun w _ hw ↦ heqR w.2 hw)
    (fun w _ hw ↦ (hKgR w.2 hw).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  refine IsBigO.of_bound K ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_ge_atTop (R + 1)] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  -- The difference bound makes `g` Lipschitz at `x` with constant `K exp (-c ‖x‖)`.
  refine norm_fderiv_le_of_forall_norm_sub_le one_pos (by positivity) fun y hy ↦ ?_
  have := hK ((0 : ℝ), x) (by simp) hx ((0 : ℝ), y) (by simpa [Prod.norm_def] using hy)
  simpa only [Prod.mk_add_mk, add_zero, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    using this

/-! ### All derivatives of solutions of `Δ ℓ = κ (exp ℓ - 1)` -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A rate strictly between `c > 0` and `√κ`, when `c² < κ`. -/
private theorem exists_lt_and_sq_lt {c κ : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) :
    ∃ a, c < a ∧ a ^ 2 < κ := by
  have ha2 : Real.sqrt ((c ^ 2 + κ) / 2) ^ 2 = (c ^ 2 + κ) / 2 := Real.sq_sqrt (by nlinarith)
  exact ⟨Real.sqrt ((c ^ 2 + κ) / 2), Real.lt_sqrt hc.le |>.mpr (by linarith),
    by rw [ha2]; linarith⟩

section Commutator

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The commutator `Dᵏ (exp ℓ) - exp ℓ • Dᵏ ℓ`. It involves only derivatives of `ℓ` of order
below `k` (`isBigO_iteratedFDeriv_expCommutator`). -/
private def expCommutator (ℓ : W → ℝ) (k : ℕ) (x : W) : W [×k]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ k (fun y ↦ Real.exp (ℓ y)) x - Real.exp (ℓ x) • iteratedFDeriv ℝ k ℓ x

private theorem contDiff_expCommutator {ℓ : W → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (k : ℕ) :
    ContDiff ℝ ∞ (expCommutator ℓ k) :=
  ((Real.contDiff_exp.comp hℓ).iteratedFDeriv_right (by simp)).sub
    ((Real.contDiff_exp.comp hℓ).smul (hℓ.iteratedFDeriv_right (by simp)))

private theorem expCommutator_one {ℓ : W → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) : expCommutator ℓ 1 = 0 := by
  funext x
  ext m
  simp [expCommutator, iteratedFDeriv_one_apply, fderiv_exp (hℓ.differentiable (by simp) x)]

/-- The recursion `Cₖ₊₁ = D Cₖ + D (exp ℓ) ⊗ Dᵏ ℓ`, up to the currying isometry. -/
private theorem expCommutator_succ {ℓ : W → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) (k : ℕ) :
    expCommutator ℓ (k + 1) = (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (k + 1) ↦ W) ℝ).symm ∘ fun y ↦ fderiv ℝ (expCommutator ℓ k) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y) := by
  funext y
  have he : ContDiff ℝ ∞ (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
  have hdC : DifferentiableAt ℝ (expCommutator ℓ k) y :=
    (contDiff_expCommutator hℓ k).differentiable (by simp) y
  have hdℓ : DifferentiableAt ℝ (iteratedFDeriv ℝ k ℓ) y :=
    (hℓ.iteratedFDeriv_right (m := 1) (by simp)).differentiable (by simp) y
  have hde : DifferentiableAt ℝ (fun y ↦ Real.exp (ℓ y)) y := he.differentiable (by simp) y
  -- Differentiate `Dᵏ (exp ℓ) = Cₖ + exp ℓ • Dᵏ ℓ`.
  have hDe : fderiv ℝ (iteratedFDeriv ℝ k fun y ↦ Real.exp (ℓ y)) y =
      fderiv ℝ (expCommutator ℓ k) y + (Real.exp (ℓ y) • fderiv ℝ (iteratedFDeriv ℝ k ℓ) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y)) := by
    have hsplit : (iteratedFDeriv ℝ k fun y ↦ Real.exp (ℓ y)) =
        fun x ↦ expCommutator ℓ k x + Real.exp (ℓ x) • iteratedFDeriv ℝ k ℓ x := by
      funext x
      simp [expCommutator]
    rw [hsplit]
    exact (hdC.hasFDerivAt.add (hde.hasFDerivAt.smul hdℓ.hasFDerivAt)).fderiv
  simp only [expCommutator, iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hDe, map_add,
    map_smul]
  abel

/-- Along any filter, the commutators `Cₖ` are `O(ρ)` with their derivatives, as long as the
derivatives of `ℓ` of order at most `n` are `O(ρ)` and those of `exp ℓ` are bounded, where
`j + k ≤ n + 1`. -/
private theorem isBigO_iteratedFDeriv_expCommutator {ℓ : W → ℝ} {l : Filter W} {ρ : W → ℝ}
    (hℓ : ContDiff ℝ ∞ ℓ) {n : ℕ} (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[l] ρ)
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun y ↦ Real.exp (ℓ y)) =O[l]
      fun _ ↦ (1 : ℝ))
    {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hjk : j + k ≤ n + 1) :
    iteratedFDeriv ℝ j (expCommutator ℓ k) =O[l] ρ := by
  have he : ContDiff ℝ ∞ (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
  induction k, hk using Nat.le_induction generalizing j with
  | base =>
    rw [expCommutator_one hℓ, iteratedFDeriv_zero]
    exact isBigO_zero _ _
  | succ k hk ih =>
    -- The term `D (exp ℓ) ⊗ Dᵏ ℓ`.
    have hT := (he.fderiv_right (m := ∞) le_rfl).isBigO_iteratedFDeriv_smulRight
      (hℓ.iteratedFDeriv_right (m := ∞) (i := k) le_rfl) (n := j) (mod_cast le_top)
      (fun i hi ↦ (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans
        (hen (i + 1) (by omega)))
      (fun i hi ↦ (isBigO_of_le _ fun y ↦ (norm_iteratedFDeriv_iteratedFDeriv ℓ i k y).le).trans
        (hℓn (i + k) (by omega)))
    simp only [one_mul] at hT
    have hF : iteratedFDeriv ℝ j (fderiv ℝ (expCommutator ℓ k)) =O[l] ρ :=
      (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_fderiv.le).trans (ih (j := j + 1) (by omega))
    have hsum : iteratedFDeriv ℝ j (fun y ↦ fderiv ℝ (expCommutator ℓ k) y +
        (fderiv ℝ (fun y ↦ Real.exp (ℓ y)) y).smulRight (iteratedFDeriv ℝ k ℓ y))
          =O[l] ρ := by
      refine (isBigO_of_le _ fun y ↦ (le_of_eq ?_)).trans (hF.add hT)
      rw [fun_iteratedFDeriv_add_apply
        (((contDiff_expCommutator hℓ k).fderiv_right (m := ∞) le_rfl).contDiffAt.of_le
          (by simp))
        (((he.fderiv_right (m := ∞) le_rfl).smulRight
          (hℓ.iteratedFDeriv_right (m := ∞) (i := k) le_rfl)).contDiffAt.of_le
            (by simp))]
    -- The spaces are given explicitly: unifying them against the instances carried by the
    -- currying isometry otherwise fails.
    have hiso : ∀ (f : W → W →L[ℝ] W [×k]→L[ℝ] ℝ) (y : W),
        ‖iteratedFDeriv ℝ j ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ W)
          ℝ).symm ∘ f) y‖ = ‖iteratedFDeriv ℝ j f y‖ := fun f y ↦
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := W)
        (F := W →L[ℝ] W [×k]→L[ℝ] ℝ) (G := W [×k + 1]→L[ℝ] ℝ) _ f y j
    rw [expCommutator_succ hℓ k]
    exact (isBigO_of_le _ fun y ↦ (hiso _ y).le).trans hsum

/-- A bound `‖D (exp ℓ)‖ ≤ L` bounds the derivative of the potential `κ exp ℓ` by
`|κ| max L 0`. -/
private theorem norm_fderiv_const_mul_exp_le {ℓ : W → ℝ} (hℓ : ContDiff ℝ ∞ ℓ) {κ L : ℝ} {y : W}
    (hL : ‖iteratedFDeriv ℝ 1 (fun y ↦ Real.exp (ℓ y)) y‖ ≤ L * ‖(1 : ℝ)‖) :
    ‖fderiv ℝ (fun y ↦ κ * Real.exp (ℓ y)) y‖ ≤ |κ| * max L 0 := by
  have he : ContDiff ℝ ∞ (fun y ↦ Real.exp (ℓ y)) := Real.contDiff_exp.comp hℓ
  rw [fderiv_const_mul (he.differentiable (by simp) y)]
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, ← norm_iteratedFDeriv_one]
  rw [norm_one, mul_one] at hL
  exact mul_le_mul_of_nonneg_left (hL.trans (le_max_left _ _)) (abs_nonneg κ)

/-- A bound `‖D Cₙ‖ ≤ K ρ` bounds the derivative of the forcing `κ Cₙ` by `|κ| max K 0 ρ`. -/
private theorem norm_fderiv_const_smul_expCommutator_le {ℓ : W → ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    {κ K ρ : ℝ} (hρ : 0 ≤ ρ) {n : ℕ} {y : W}
    (hK : ‖iteratedFDeriv ℝ 1 (expCommutator ℓ n) y‖ ≤ K * ‖ρ‖) :
    ‖fderiv ℝ (κ • expCommutator ℓ n) y‖ ≤ |κ| * max K 0 * ρ := by
  rw [fderiv_const_smul ((contDiff_expCommutator hℓ n).differentiable (by simp) y)]
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, ← norm_iteratedFDeriv_one, mul_assoc]
  rw [Real.norm_of_nonneg hρ] at hK
  exact mul_le_mul_of_nonneg_left (hK.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ))
    (abs_nonneg κ)

end Commutator

/-! ### Comparison of two solutions of `Δ ℓ = κ (exp ℓ - 1)` -/

/-- Where two `C²` functions solve `Δ ℓ = κ (exp ℓ - 1)`, their difference satisfies
`Δ (ℓ₁ - ℓ₂) = κ (exp ℓ₁ - exp ℓ₂)`. -/
theorem laplacian_sub_eq_of_laplacian_eq_exp_sub_one {ℓ₁ ℓ₂ : E → ℝ} {κ : ℝ} {x : E}
    (h₁ : ContDiffAt ℝ 2 ℓ₁ x) (h₂ : ContDiffAt ℝ 2 ℓ₂ x)
    (hΔ₁ : Δ ℓ₁ x = κ * (Real.exp (ℓ₁ x) - 1)) (hΔ₂ : Δ ℓ₂ x = κ * (Real.exp (ℓ₂ x) - 1)) :
    Δ (ℓ₁ - ℓ₂) x = κ * (Real.exp (ℓ₁ x) - Real.exp (ℓ₂ x)) := by
  rw [h₁.laplacian_sub h₂, hΔ₁, hΔ₂]
  ring

/-- One side of `TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`. -/
private theorem sub_le_mul_exp_of_laplacian_eq_exp_sub_one {ℓ₁ ℓ₂ : E → ℝ} {κ R c M : ℝ}
    (hR : 0 < R) (hc : 0 ≤ c) (hM : 0 ≤ M) (h₁ : ∀ x, R ≤ ‖x‖ → ContDiffAt ℝ 2 ℓ₁ x)
    (h₂ : ∀ x, R ≤ ‖x‖ → ContDiffAt ℝ 2 ℓ₂ x)
    (hΔ₁ : ∀ x, R ≤ ‖x‖ → Δ ℓ₁ x = κ * (Real.exp (ℓ₁ x) - 1))
    (hΔ₂ : ∀ x, R ≤ ‖x‖ → Δ ℓ₂ x = κ * (Real.exp (ℓ₂ x) - 1))
    (hc₁ : ∀ x, R ≤ ‖x‖ → c ^ 2 ≤ κ * Real.exp (ℓ₁ x))
    (hc₂ : ∀ x, R ≤ ‖x‖ → c ^ 2 ≤ κ * Real.exp (ℓ₂ x))
    (hlim₁ : Tendsto ℓ₁ (cocompact E) (𝓝 0)) (hlim₂ : Tendsto ℓ₂ (cocompact E) (𝓝 0))
    (hbd : ∀ x, ‖x‖ = R → ℓ₁ x - ℓ₂ x ≤ M) {x : E} (hx : R ≤ ‖x‖) :
    ℓ₁ x - ℓ₂ x ≤ M * Real.exp (-(c * (‖x‖ - R))) := by
  -- `Δ (ℓ₁ - ℓ₂) = V (ℓ₁ - ℓ₂)` for the difference quotient `V` of `κ exp`, and `V ≥ c²`.
  set V : E → ℝ := fun w ↦ if ℓ₁ w = ℓ₂ w then c ^ 2 else
    κ * ((Real.exp (ℓ₁ w) - Real.exp (ℓ₂ w)) / (ℓ₁ w - ℓ₂ w))
  have hV (w : E) (hw : R < ‖w‖) : c ^ 2 ≤ V w := by
    by_cases h : ℓ₁ w = ℓ₂ w
    · simp [V, h]
    · simp only [V, h, ↓reduceIte]
      have hκ : 0 ≤ κ :=
        nonneg_of_mul_nonneg_left ((sq_nonneg c).trans (hc₁ w hw.le)) (Real.exp_pos _)
      have hq := Real.le_sub_div_log_sub_log (Real.exp_pos _) (Real.exp_pos _)
        (min_le_left (Real.exp (ℓ₁ w)) (Real.exp (ℓ₂ w))) (min_le_right _ _)
        (by rwa [Real.log_exp, Real.log_exp, sub_ne_zero])
      rw [Real.log_exp, Real.log_exp] at hq
      calc c ^ 2 ≤ κ * min (Real.exp (ℓ₁ w)) (Real.exp (ℓ₂ w)) := by
            rw [mul_min_of_nonneg _ _ hκ]
            exact le_min (hc₁ w hw.le) (hc₂ w hw.le)
        _ ≤ _ := mul_le_mul_of_nonneg_left hq hκ
  have hsub (w : E) (hw : R < ‖w‖) : V w * (ℓ₁ - ℓ₂) w ≤ Δ (ℓ₁ - ℓ₂) w := by
    rw [laplacian_sub_eq_of_laplacian_eq_exp_sub_one (h₁ w hw.le) (h₂ w hw.le) (hΔ₁ w hw.le)
      (hΔ₂ w hw.le), Pi.sub_apply]
    by_cases h : ℓ₁ w = ℓ₂ w
    · simp [V, h]
    · simp only [V, h, ↓reduceIte]
      exact le_of_eq (by field_simp [sub_ne_zero.2 h])
  exact le_mul_exp_of_mul_le_laplacian hR hc hM
    (fun w hw ↦ ((h₁ w hw).sub (h₂ w hw)).continuousAt.continuousWithinAt)
    (fun w hw ↦ (h₁ w hw.le).sub (h₂ w hw.le)) hV hsub hbd (by simpa using hlim₁.sub hlim₂) hx

/-- **Comparison of two solutions of `Δ ℓ = κ (exp ℓ - 1)` outside a ball.** Let `ℓ₁` and `ℓ₂`
be `C²` solutions of `Δ ℓ = κ (exp ℓ - 1)` outside the ball of radius `R > 0`, tending to `0` at
infinity, with `κ exp ℓᵢ ≥ c²` there for a rate `c ≥ 0`. If `|ℓ₁ - ℓ₂| ≤ M` on the boundary
sphere, then for `‖x‖ ≥ R`,

`|ℓ₁ x - ℓ₂ x| ≤ M exp (-c (‖x‖ - R))`.

The difference solves `Δ u = V u` for the difference quotient `V` of `κ exp`, which is at least
`c²`, so `u` and `-u` are subsolutions of `-Δ + V`. -/
theorem abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one {ℓ₁ ℓ₂ : E → ℝ} {κ R c M : ℝ}
    (hR : 0 < R) (hc : 0 ≤ c) (h₁ : ∀ x, R ≤ ‖x‖ → ContDiffAt ℝ 2 ℓ₁ x)
    (h₂ : ∀ x, R ≤ ‖x‖ → ContDiffAt ℝ 2 ℓ₂ x)
    (hΔ₁ : ∀ x, R ≤ ‖x‖ → Δ ℓ₁ x = κ * (Real.exp (ℓ₁ x) - 1))
    (hΔ₂ : ∀ x, R ≤ ‖x‖ → Δ ℓ₂ x = κ * (Real.exp (ℓ₂ x) - 1))
    (hc₁ : ∀ x, R ≤ ‖x‖ → c ^ 2 ≤ κ * Real.exp (ℓ₁ x))
    (hc₂ : ∀ x, R ≤ ‖x‖ → c ^ 2 ≤ κ * Real.exp (ℓ₂ x))
    (hlim₁ : Tendsto ℓ₁ (cocompact E) (𝓝 0)) (hlim₂ : Tendsto ℓ₂ (cocompact E) (𝓝 0))
    (hbd : ∀ x, ‖x‖ = R → |ℓ₁ x - ℓ₂ x| ≤ M) {x : E} (hx : R ≤ ‖x‖) :
    |ℓ₁ x - ℓ₂ x| ≤ M * Real.exp (-(c * (‖x‖ - R))) := by
  have : Nontrivial E := ⟨⟨x, 0, norm_pos_iff.1 (hR.trans_le hx)⟩⟩
  have hM : 0 ≤ M := nonneg_of_forall_norm_eq_abs_le hR.le hbd
  refine abs_le.2 ⟨?_, sub_le_mul_exp_of_laplacian_eq_exp_sub_one hR hc hM h₁ h₂ hΔ₁ hΔ₂ hc₁ hc₂
    hlim₁ hlim₂ (fun w hw ↦ (le_abs_self _).trans (hbd w hw)) hx⟩
  have h := sub_le_mul_exp_of_laplacian_eq_exp_sub_one hR hc hM h₂ h₁ hΔ₂ hΔ₁ hc₂ hc₁ hlim₂ hlim₁
    (fun w hw ↦ (le_abs_self _).trans ((abs_sub_comm _ _).trans_le (hbd w hw))) hx
  linarith

/-! ### All derivatives of families of solutions of `Δ ℓ = κ (exp ℓ - 1)` -/

section FamilyExp

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- A family that is `O(exp (-c ‖z‖))` along `𝓟 (closedBall 0 s) ×ˢ cocompact E` tends to zero
there, so `κ exp ℓ` tends to `κ`. -/
private theorem tendsto_const_mul_exp_of_isBigO {ℓ : P × E → ℝ} {κ c s : ℝ} (hc : 0 < c)
    (hℓ : ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E] fun w ↦ Real.exp (-(c * ‖w.2‖))) :
    Tendsto (fun w ↦ κ * Real.exp (ℓ w)) (𝓟 (closedBall (0 : P) s) ×ˢ cocompact E) (𝓝 κ) := by
  simpa using ((Real.continuous_exp.tendsto 0).comp
    (hℓ.trans_tendsto ((tendsto_exp_neg_mul_norm_cocompact hc).comp tendsto_snd))).const_mul κ

/-- **Translates of a family of solutions of `Δ_z ℓ = κ (exp ℓ - 1)`.** If on the region
`‖p‖ ≤ s + δ`, `‖z‖ ≥ R ≥ 1` a smooth family solves `Δ_z ℓ = κ (exp ℓ - 1)`, is at most
`C exp (-c ‖z‖)` and has `κ exp ℓ ≥ c²`, then the differences `ℓ (w + h) - ℓ w` with `‖h‖ ≤ δ`
are at most `‖h‖` times a fixed multiple of `exp (-c ‖w.2‖)` for `‖w.1‖ ≤ s` and
`‖w.2‖ ≥ R + 1`: two translates solve the unforced comparison of
`TauCeti.abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one`. -/
private theorem exists_norm_sub_le_mul_exp_of_laplacian_eq_exp_sub_one_prod {ℓ : P × E → ℝ}
    {κ c s δ R C : ℝ} (hc : 0 < c) (hℓ : ContDiff ℝ ∞ ℓ) (hδ₁ : δ ≤ 1) (hR : 1 ≤ R)
    (hreg : ∀ (q : P) (y : E), ‖q‖ ≤ s + δ → R ≤ ‖y‖ →
      Δ (fun t ↦ ℓ (q, t)) y = κ * (Real.exp (ℓ (q, y)) - 1) ∧
      |ℓ (q, y)| ≤ C * Real.exp (-(c * ‖y‖)) ∧ c ^ 2 ≤ κ * Real.exp (ℓ (q, y))) :
    ∃ K, 0 ≤ K ∧ ∀ w : P × E, ‖w.1‖ ≤ s → R + 1 ≤ ‖w.2‖ → ∀ h : P × E, ‖h‖ ≤ δ →
      ‖ℓ (w + h) - ℓ w‖ ≤ ‖h‖ * (K * Real.exp (-(c * ‖w.2‖))) := by
  -- The translates are uniformly Lipschitz on the sphere of radius `R + 1`.
  obtain ⟨M, hM₀, hM⟩ := exists_norm_sub_le_mul_of_contDiffAt (f := ℓ) (r := s) (R := R)
    (R₁ := R + 1) fun w _ _ ↦ hℓ.contDiffAt.of_le (by simp)
  -- Each member of the family tends to zero at infinity.
  have hlim : ∀ q : P, ‖q‖ ≤ s + δ → Tendsto (fun y ↦ ℓ (q, y)) (cocompact E) (𝓝 0) :=
    fun q hq ↦ tendsto_cocompact_nhds_zero_of_norm_le_mul_exp hc fun y hy ↦ (hreg q y hq hy).2.1
  refine ⟨M * Real.exp (c * (R + 1)), by positivity, ?_⟩
  rintro ⟨p, z⟩ hw₁ hw₂ h hh
  dsimp only at hw₁ hw₂ ⊢
  have hpair : ∀ y : E, (p, y) + h = (p + h.1, y + h.2) := fun y ↦
    Prod.ext (Prod.fst_add _ _) (Prod.snd_add _ _)
  have hq : ‖p + h.1‖ ≤ s + δ := by linarith [norm_add_le p h.1, norm_fst_le h]
  have hw₁' : ‖p‖ ≤ s + δ := by linarith [(norm_nonneg h).trans hh]
  have hfar : ∀ y : E, R + 1 ≤ ‖y‖ → R ≤ ‖y + h.2‖ := fun y hy ↦ by
    have := norm_sub_le (y + h.2) h.2
    rw [add_sub_cancel_right] at this
    linarith [norm_snd_le h]
  have hlim₁ : Tendsto (fun y ↦ ℓ (p + h.1, y + h.2)) (cocompact E) (𝓝 0) := by
    have := (hlim _ hq).comp (Homeomorph.addRight h.2).isClosedEmbedding.tendsto_cocompact
    simpa [Function.comp_def] using this
  -- The two translates solve `Δ ℓ = κ (exp ℓ - 1)` outside the ball of radius `R + 1`.
  have hcmp := abs_sub_le_mul_exp_of_laplacian_eq_exp_sub_one
    (ℓ₁ := fun y ↦ ℓ (p + h.1, y + h.2)) (ℓ₂ := fun y ↦ ℓ (p, y)) (κ := κ) (R := R + 1)
    (M := M * ‖h‖) (by linarith) hc.le
    (fun y _ ↦ (hℓ.comp ((contDiff_prodMk_right _).comp (contDiff_id.add
      contDiff_const))).contDiffAt.of_le (by simp))
    (fun y _ ↦ (hℓ.comp (contDiff_prodMk_right _)).contDiffAt.of_le (by simp))
    (fun y hy ↦ by
      rw [congrFun (laplacian_comp_add_right (fun y ↦ ℓ (p + h.1, y)) h.2) y]
      exact (hreg _ _ hq (hfar y hy)).1)
    (fun y hy ↦ (hreg _ _ hw₁' (by linarith)).1)
    (fun y hy ↦ (hreg _ _ hq (hfar y hy)).2.2) (fun y hy ↦ (hreg _ _ hw₁' (by linarith)).2.2)
    hlim₁ (hlim _ hw₁')
    (fun y hy ↦ by
      have := hM (p, y) hw₁ (by simp only; linarith) (by simp only; linarith) h hh
      rw [hpair] at this
      simpa [Real.norm_eq_abs] using this) hw₂
  rw [hpair, Real.norm_eq_abs]
  refine hcmp.trans (le_of_eq ?_)
  rw [exp_neg_mul_sub]
  ring

/-- **The first derivative.** The difference of two translates of a family of solutions of
`Δ_z ℓ = κ (exp ℓ - 1)` solves a linear screened equation, so the first derivative of a decaying
family decays at the same rate, uniformly in the parameter. -/
private theorem isBigO_fderiv_of_laplacian_eq_exp_sub_one_prod {ℓ : P × E → ℝ}
    {κ c r₂ R₁ s : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ContDiff ℝ ∞ ℓ)
    (heq : ∀ w : P × E, ‖w.1‖ < r₂ → R₁ < ‖w.2‖ →
      Δ (fun y ↦ ℓ (w.1, y)) w.2 = κ * (Real.exp (ℓ w) - 1))
    (hdec : ∀ s < r₂, ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
      fun w ↦ Real.exp (-(c * ‖w.2‖)))
    (hs : s < r₂) :
    fderiv ℝ ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E] fun w ↦ Real.exp (-(c * ‖w.2‖)) := by
  obtain ⟨δ, hδ, hδ₁, hsδ⟩ := exists_pos_le_one_add_lt hs
  -- On a region `‖p‖ ≤ s + δ`, `‖z‖ ≥ R`, `ℓ` decays and `κ exp ℓ ≥ c²`.
  obtain ⟨C, hC⟩ := (hdec (s + δ) hsδ).bound
  obtain ⟨R₂, hR₂⟩ := eventually_principal_closedBall_prod_cocompact_iff.1
    (hC.and ((tendsto_const_mul_exp_of_isBigO hc (hdec (s + δ) hsδ)).eventually
      (le_mem_nhds hcκ)))
  set R := max (max R₂ 1) (R₁ + 1)
  obtain ⟨K, hK₀, hK⟩ := exists_norm_sub_le_mul_exp_of_laplacian_eq_exp_sub_one_prod (R := R)
    (C := C)
    hc hℓ hδ₁ ((le_max_right _ _).trans (le_max_left _ _)) fun q y hq hy ↦ by
      have hR := hR₂ (q, y) hq ((le_max_left _ _).trans ((le_max_left _ _).trans hy))
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hR
      exact ⟨heq (q, y) (by simp only; linarith)
        (by simp only; linarith [le_max_right (max R₂ 1) (R₁ + 1)]), hR.1, hR.2⟩
  -- The difference bound makes `ℓ` Lipschitz at `w` with constant `K exp (-c ‖w.2‖)`.
  rw [isBigO_iff]
  refine ⟨K, eventually_principal_closedBall_prod_cocompact_iff.2 ⟨R + 1, fun w hw₁ hw₂ ↦ ?_⟩⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact norm_fderiv_le_of_forall_norm_sub_le hδ (by positivity) (hK w hw₁ hw₂)

omit [FiniteDimensional ℝ P] in
/-- **The equation for the derivatives of a family.** Where a smooth family solves
`Δ_z ℓ = κ (exp ℓ - 1)` on an open region, its derivative of order `n ≥ 1` solves
`Δ_z Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ`, since `Δ_z` commutes with joint derivatives. -/
private theorem laplacian_iteratedFDeriv_eq_of_laplacian_eq_exp_sub_one_prod {ℓ : P × E → ℝ}
    {κ r₂ R₁ : ℝ} (hℓ : ContDiff ℝ ∞ ℓ)
    (heq : ∀ w : P × E, ‖w.1‖ < r₂ → R₁ < ‖w.2‖ →
      Δ (fun y ↦ ℓ (w.1, y)) w.2 = κ * (Real.exp (ℓ w) - 1))
    {n : ℕ} (hn : 1 ≤ n) {w : P × E} (hw₁ : ‖w.1‖ < r₂) (hw₂ : R₁ < ‖w.2‖) :
    Δ (fun y ↦ iteratedFDeriv ℝ n ℓ (w.1, y)) w.2 =
      (κ * Real.exp (ℓ w)) • iteratedFDeriv ℝ n ℓ w + (κ • expCommutator ℓ n) w := by
  set e : P × E → ℝ := fun w ↦ Real.exp (ℓ w) with he_def
  have he : ContDiff ℝ ∞ e := Real.contDiff_exp.comp hℓ
  have hloc : (fun w : P × E ↦ Δ (fun y ↦ ℓ (w.1, y)) w.2) =ᶠ[𝓝 w] κ • e - fun _ ↦ κ := by
    filter_upwards [(isOpen_setOf_norm_fst_lt_and_lt_norm_snd r₂ R₁).mem_nhds ⟨hw₁, hw₂⟩]
      with v hv
    rw [heq v hv.1 hv.2]
    simp [e, mul_sub]
  rw [congrFun ((hℓ.of_le (by simp)).laplacian_comp_prodMk_iteratedFDeriv (n := n)) w,
    (hloc.iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_sub_apply (f := κ • e) ((he.const_smul κ).contDiffAt.of_le (by simp))
      contDiffAt_const, iteratedFDeriv_const_of_ne (by omega),
    iteratedFDeriv_const_smul_apply (he.contDiffAt.of_le (by simp))]
  simp only [Pi.zero_apply, sub_zero, Pi.smul_apply, expCommutator, he_def]
  rw [smul_sub, mul_smul]
  abel

/-- **The inductive step.** For a smooth family solving `Δ_z ℓ = κ (exp ℓ - 1)` on the region
`‖p‖ < r₂`, `‖z‖ > R₁`, if the derivatives of `ℓ` of order at most `n ≥ 1` are
`O(exp (-c ‖z‖))` and those of `exp ℓ` bounded uniformly for `‖p‖ ≤ s + δ`, then so is the
derivative of order `n + 1` for `‖p‖ ≤ s`: `Dⁿℓ` solves
`Δ_z Dⁿℓ = κ exp ℓ • Dⁿℓ + κ Cₙ`. -/
private theorem isBigO_iteratedFDeriv_succ_of_laplacian_eq_exp_sub_one_prod {ℓ : P × E → ℝ}
    {κ c r₂ R₁ s δ : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ContDiff ℝ ∞ ℓ)
    (heq : ∀ w : P × E, ‖w.1‖ < r₂ → R₁ < ‖w.2‖ →
      Δ (fun y ↦ ℓ (w.1, y)) w.2 = κ * (Real.exp (ℓ w) - 1))
    (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hsδ : s + δ < r₂) {n : ℕ} (hn : 1 ≤ n)
    (hℓn : ∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[𝓟 (closedBall (0 : P) (s + δ)) ×ˢ cocompact E]
      fun w ↦ Real.exp (-(c * ‖w.2‖)))
    (hen : ∀ i ≤ n, iteratedFDeriv ℝ i (fun w ↦ Real.exp (ℓ w))
      =O[𝓟 (closedBall (0 : P) (s + δ)) ×ˢ cocompact E] fun _ ↦ (1 : ℝ)) :
    iteratedFDeriv ℝ (n + 1) ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
      fun w ↦ Real.exp (-(c * ‖w.2‖)) := by
  set e : P × E → ℝ := fun w ↦ Real.exp (ℓ w)
  have he : ContDiff ℝ ∞ e := Real.contDiff_exp.comp hℓ
  obtain ⟨a, hca, hκa⟩ := exists_lt_and_sq_lt hc hcκ
  -- Explicit bounds on the region `‖p‖ ≤ s + δ`, `‖z‖ ≥ R`.
  obtain ⟨Kg, hKg⟩ := (hℓn n le_rfl).bound
  obtain ⟨L, hL⟩ := (hen 1 hn).bound
  obtain ⟨KΦ, hKΦ⟩ := (isBigO_iteratedFDeriv_expCommutator hℓ hℓn hen hn (j := 1)
    (Nat.add_comm 1 n).le).bound
  have hVlim := tendsto_const_mul_exp_of_isBigO (κ := κ) hc
    ((isBigO_of_le _ fun w ↦ norm_iteratedFDeriv_zero.ge).trans (hℓn 0 (Nat.zero_le n)))
  obtain ⟨R₂, hR₂⟩ := eventually_principal_closedBall_prod_cocompact_iff.1
    (hKg.and (hL.and (hKΦ.and (hVlim.eventually (le_mem_nhds hκa)))))
  set R := max (max R₂ 1) (R₁ + 1)
  have hR : ∀ w : P × E, ‖w.1‖ ≤ s + δ → R ≤ ‖w.2‖ → _ := fun w hw₁ hw₂ ↦
    hR₂ w hw₁ ((le_max_left _ _).trans ((le_max_left _ _).trans hw₂))
  have hρ (w : P × E) : ‖Real.exp (-(c * ‖w.2‖))‖ = Real.exp (-(c * ‖w.2‖)) :=
    Real.norm_of_nonneg (Real.exp_pos _).le
  obtain ⟨K, -, hK⟩ := exists_forall_norm_fderiv_le_mul_exp_of_laplacian_eq_smul_add
    (g := iteratedFDeriv ℝ n ℓ) (V := fun w ↦ κ * e w) (Φ := κ • expCommutator ℓ n) (r := s)
    (L := |κ| * max L 0) (Kg := max Kg 0) (KΦ := |κ| * max KΦ 0) hc hca hδ hδ₁
    ((le_max_right _ _).trans (le_max_left _ _))
    (by positivity) (le_max_right _ _) (by positivity)
    (fun w _ _ ↦ (hℓ.iteratedFDeriv_right (m := 2) (by simp)).contDiffAt)
    (fun w _ _ ↦ (he.differentiable (by simp) w).const_mul κ)
    (fun w hw₁ hw₂ ↦ (hR w hw₁ hw₂).2.2.2)
    (fun w hw₁ hw₂ ↦ norm_fderiv_const_mul_exp_le hℓ (hR w hw₁ hw₂).2.1)
    (fun w _ _ ↦ ((contDiff_expCommutator hℓ n).differentiable (by simp) w).const_smul κ)
    (fun w hw₁ hw₂ ↦ norm_fderiv_const_smul_expCommutator_le hℓ (Real.exp_pos _).le
      (hR w hw₁ hw₂).2.2.1)
    (fun w hw₁ hw₂ ↦ laplacian_iteratedFDeriv_eq_of_laplacian_eq_exp_sub_one_prod hℓ heq hn
      (by linarith) (by linarith [le_max_right (max R₂ 1) (R₁ + 1)]))
    (fun w hw₁ hw₂ ↦ by
      have := (hR w hw₁ hw₂).1
      rw [hρ] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  rw [isBigO_iff]
  refine ⟨K, eventually_principal_closedBall_prod_cocompact_iff.2 ⟨R + 1, fun w hw₁ hw₂ ↦ ?_⟩⟩
  rw [← norm_fderiv_iteratedFDeriv, hρ]
  exact hK w hw₁ hw₂

/-- **All derivatives of a smooth family.** For a smooth family solving `Δ_z ℓ = κ (exp ℓ - 1)`
on the region `‖p‖ < r₂`, `‖z‖ > R₁` and decaying like `exp (-c ‖z‖)` uniformly for `‖p‖ ≤ s`,
every `s < r₂`, the derivatives of `ℓ` of order at most `n` are `O(exp (-c ‖z‖))` and those of
`exp ℓ` bounded, uniformly for `‖p‖ ≤ s`. -/
private theorem isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_prod {ℓ : P × E → ℝ}
    {κ c r₂ R₁ : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ContDiff ℝ ∞ ℓ)
    (heq : ∀ w : P × E, ‖w.1‖ < r₂ → R₁ < ‖w.2‖ →
      Δ (fun y ↦ ℓ (w.1, y)) w.2 = κ * (Real.exp (ℓ w) - 1))
    (hdec : ∀ s < r₂, ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
      fun w ↦ Real.exp (-(c * ‖w.2‖))) (n : ℕ) :
    ∀ s < r₂, (∀ i ≤ n, iteratedFDeriv ℝ i ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
      fun w ↦ Real.exp (-(c * ‖w.2‖))) ∧
      ∀ i ≤ n, iteratedFDeriv ℝ i (fun w ↦ Real.exp (ℓ w))
        =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E] fun _ ↦ (1 : ℝ) := by
  have hρ1 : ∀ s : ℝ, (fun w : P × E ↦ Real.exp (-(c * ‖w.2‖)))
      =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E] fun _ ↦ (1 : ℝ) := fun s ↦
    isBigO_of_le _ fun w ↦ by
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_one, Real.exp_le_one_iff,
        Left.neg_nonpos_iff]
      positivity
  induction n with
  | zero =>
    intro s hs
    have he0 : (fun w ↦ Real.exp (ℓ w)) =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
        fun _ ↦ (1 : ℝ) := by
      have hℓ1 := (hdec s hs).trans (hρ1 s)
      obtain ⟨C, hC⟩ := hℓ1.bound
      refine IsBigO.of_bound (Real.exp C) (hC.mono fun w hw ↦ ?_)
      simp only [Real.norm_eq_abs, norm_one, mul_one, abs_of_pos (Real.exp_pos _)] at hw ⊢
      exact Real.exp_le_exp.2 ((le_abs_self _).trans hw)
    refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩ <;> obtain rfl : i = 0 := by omega
    · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans (hdec s hs)
    · exact (isBigO_of_le _ fun y ↦ norm_iteratedFDeriv_zero.le).trans he0
  | succ n ih =>
    intro s hs
    obtain ⟨δ, hδ, hδ₁, hsδ⟩ := exists_pos_le_one_add_lt hs
    have hmono : 𝓟 (closedBall (0 : P) s) ×ˢ cocompact E ≤
        𝓟 (closedBall (0 : P) (s + δ)) ×ˢ cocompact E :=
      Filter.prod_mono (principal_mono.2 (closedBall_subset_closedBall (by linarith))) le_rfl
    obtain ⟨ihℓ, ihe⟩ := ih (s + δ) hsδ
    have hnext : iteratedFDeriv ℝ (n + 1) ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
        fun w ↦ Real.exp (-(c * ‖w.2‖)) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact (isBigO_of_le _ fun y ↦ (norm_iteratedFDeriv_one ℓ).le).trans
          (isBigO_fderiv_of_laplacian_eq_exp_sub_one_prod hc hcκ hℓ heq hdec hs)
      · exact isBigO_iteratedFDeriv_succ_of_laplacian_eq_exp_sub_one_prod hc hcκ hℓ heq hδ hδ₁
          hsδ hn ihℓ ihe
    have hℓall : ∀ i ≤ n + 1, iteratedFDeriv ℝ i ℓ =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
        fun w ↦ Real.exp (-(c * ‖w.2‖)) := fun i hi ↦ by
      rcases Nat.lt_or_eq_of_le hi with h | rfl
      · exact (ihℓ i (by omega)).mono hmono
      · exact hnext
    refine ⟨hℓall, fun i hi ↦ ?_⟩
    rcases Nat.lt_or_eq_of_le hi with h | rfl
    · exact (ihe i (by omega)).mono hmono
    · exact ((hℓ.of_le (by simp)).isBigO_iteratedFDeriv_succ_exp (fun i _ hi ↦ hℓall i hi)
        fun i hi ↦ (ihe i hi).mono hmono).trans (hρ1 s)

/-- **Uniform exponential decay of all derivatives of a family of solutions of
`Δ ℓ = κ (exp ℓ - 1)`.** Let `ℓ : P × E → ℝ` be a family of functions of `z ∈ E` indexed by a
parameter `p` in a finite-dimensional real normed space `P`. Suppose that on the region
`‖p‖ < r₁`, `‖z‖ > R₀` it is smooth, solves `Δ_z ℓ = κ (exp ℓ - 1)`, where `Δ_z` is the Laplacian
in `z` at fixed `p`, and is at most `K exp (-c ‖z‖)` in absolute value, with `0 < c` and
`c² < κ`. Then for every `r < r₁` and every order `n` there are `C` and `R` such that the
joint derivatives of `ℓ` in `(p, z)` of order at most `n` are at most `C exp (-c ‖z‖)` for
`‖p‖ ≤ r` and `‖z‖ ≥ R`. -/
theorem exists_forall_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_exp_sub_one
    {ℓ : P × E → ℝ} {κ c r r₁ R₀ K : ℝ} (hc : 0 < c) (hcκ : c ^ 2 < κ) (hr : r < r₁)
    (hℓ : ∀ w : P × E, ‖w.1‖ < r₁ → R₀ < ‖w.2‖ → ContDiffAt ℝ ∞ ℓ w)
    (heq : ∀ w : P × E, ‖w.1‖ < r₁ → R₀ < ‖w.2‖ →
      Δ (fun y ↦ ℓ (w.1, y)) w.2 = κ * (Real.exp (ℓ w) - 1))
    (hdec : ∀ w : P × E, ‖w.1‖ < r₁ → R₀ < ‖w.2‖ → |ℓ w| ≤ K * Real.exp (-(c * ‖w.2‖)))
    (n : ℕ) :
    ∃ C R, ∀ w : P × E, ‖w.1‖ ≤ r → R ≤ ‖w.2‖ → ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j ℓ w‖ ≤ C * Real.exp (-(c * ‖w.2‖)) := by
  -- For `r < 0` there is nothing to prove.
  rcases lt_or_ge r 0 with hr₀ | hr₀
  · exact ⟨0, 0, fun w hw₁ ↦ absurd ((norm_nonneg _).trans hw₁) (not_le.2 hr₀)⟩
  obtain ⟨ℓ', hℓ', r₂, R₁, hr₂, hr₂₁, hR₀₁, hagree⟩ :=
    exists_contDiff_forall_eventuallyEq_prod hr₀ hr hℓ
  have hR₀ : ∀ w : P × E, ‖w.1‖ < r₂ → R₁ < ‖w.2‖ → ‖w.1‖ < r₁ ∧ R₀ < ‖w.2‖ :=
    fun w hw₁ hw₂ ↦ ⟨by linarith, by linarith⟩
  -- `ℓ'` solves the equation and decays on the region.
  have heq' : ∀ w : P × E, ‖w.1‖ < r₂ → R₁ < ‖w.2‖ →
      Δ (fun y ↦ ℓ' (w.1, y)) w.2 = κ * (Real.exp (ℓ' w) - 1) := fun w hw₁ hw₂ ↦ by
    have ht : Tendsto (fun y : E ↦ (w.1, y)) (𝓝 w.2) (𝓝 w) := by
      simpa using (continuous_const.prodMk continuous_id).tendsto w.2
    have hnear : (fun y ↦ ℓ' (w.1, y)) =ᶠ[𝓝 w.2] fun y ↦ ℓ (w.1, y) :=
      ht.eventually (hagree w hw₁ hw₂)
    rw [(laplacian_congr_nhds hnear).eq_of_nhds, (hagree w hw₁ hw₂).eq_of_nhds]
    exact heq w (hR₀ w hw₁ hw₂).1 (hR₀ w hw₁ hw₂).2
  have hdec' : ∀ s < r₂, ℓ' =O[𝓟 (closedBall (0 : P) s) ×ˢ cocompact E]
      fun w ↦ Real.exp (-(c * ‖w.2‖)) := fun s hs ↦ by
    refine IsBigO.of_bound K (eventually_principal_closedBall_prod_cocompact_iff.2
      ⟨R₁ + 1, fun w hw₁ hw₂ ↦ ?_⟩)
    have hw : ‖w.1‖ < r₂ ∧ R₁ < ‖w.2‖ := ⟨by linarith, by linarith⟩
    rw [(hagree w hw.1 hw.2).eq_of_nhds, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact hdec w (hR₀ w hw.1 hw.2).1 (hR₀ w hw.1 hw.2).2
  have hO := (isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one_prod hc hcκ hℓ' heq' hdec' n r
    hr₂).1
  -- One constant for the finitely many orders `j ≤ n`.
  obtain ⟨C, hC⟩ := (isBigO_pi (f := fun w (j : Fin (n + 1)) ↦ ‖iteratedFDeriv ℝ j ℓ' w‖).2
    fun j ↦ (hO j (Nat.lt_succ_iff.1 j.isLt)).norm_left).bound
  obtain ⟨R, hR⟩ := eventually_principal_closedBall_prod_cocompact_iff.1 hC
  refine ⟨C, max R (R₁ + 1), fun w hw₁ hw₂ j hj ↦ ?_⟩
  have hw : ‖w.1‖ < r₂ ∧ R₁ < ‖w.2‖ :=
    ⟨by linarith, by linarith [le_max_right R (R₁ + 1)]⟩
  have h := (norm_le_pi_norm (fun j : Fin (n + 1) ↦ ‖iteratedFDeriv ℝ j ℓ' w‖)
    ⟨j, Nat.lt_succ_of_le hj⟩).trans (hR w hw₁ ((le_max_left _ _).trans hw₂))
  rw [((hagree w hw.1 hw.2).iteratedFDeriv ℝ j).eq_of_nhds, norm_norm,
    Real.norm_of_nonneg (Real.exp_pos _).le] at h
  exact h

end FamilyExp

/-! ### All derivatives of a single solution of `Δ ℓ = κ (exp ℓ - 1)`

A single function is the constant family over `ℝ`. -/

/-- **Exponential decay of all derivatives of solutions of `Δ ℓ = κ (exp ℓ - 1)`.** Let `ℓ` be
smooth outside a compact set and solve `Δ ℓ = κ (exp ℓ - 1)` there. If `ℓ` is `O(exp (-c ‖x‖))`
at infinity with `0 < c` and `c² < κ`, then every iterated derivative of `ℓ` is
`O(exp (-c ‖x‖))`. -/
theorem isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ} (hc : 0 < c)
    (hcκ : c ^ 2 < κ) (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ ∞ ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) (n : ℕ) :
    iteratedFDeriv ℝ n ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) := by
  obtain ⟨K, hK⟩ := hℓd.bound
  obtain ⟨R₀, -, hR₀⟩ := hasBasis_cobounded_norm.eventually_iff.mp
    (cobounded_eq_cocompact (α := E) ▸ (hℓ.and (heq.and hK)))
  have hfar := fun (y : E) (hy : R₀ < ‖y‖) ↦ hR₀ (Set.mem_ofPred.mpr hy.le)
  -- Apply the estimate for families to the constant family `(t, z) ↦ ℓ z` over `t ∈ ℝ`.
  obtain ⟨C, R, hCR⟩ := exists_forall_norm_iteratedFDeriv_le_mul_exp_of_laplacian_eq_exp_sub_one
    (P := ℝ) (ℓ := ℓ ∘ Prod.snd) (r := 0) (r₁ := 1) (K := K) hc hcκ one_pos
    (fun w _ hw ↦ (hfar w.2 hw).1.comp w contDiffAt_snd) (fun w _ hw ↦ (hfar w.2 hw).2.1)
    (fun w _ hw ↦ by simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using (hfar w.2 hw).2.2)
    n
  refine IsBigO.of_bound C ?_
  filter_upwards [(tendsto_norm_cocompact_atTop (E := E)).eventually_ge_atTop R] with x hx
  have h := hCR ((0 : ℝ), x) (by simp) hx n le_rfl
  rwa [Prod.norm_iteratedFDeriv_comp_snd, ← Real.norm_of_nonneg (Real.exp_pos _).le] at h

/-- **Exponential decay of all derivatives of `exp ℓ - 1`** for a solution of
`Δ ℓ = κ (exp ℓ - 1)`, under the hypotheses of
`TauCeti.isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one`. -/
theorem isBigO_iteratedFDeriv_exp_sub_one_of_laplacian_eq_exp_sub_one {ℓ : E → ℝ} {κ c : ℝ}
    (hc : 0 < c) (hcκ : c ^ 2 < κ) (hℓ : ∀ᶠ x in cocompact E, ContDiffAt ℝ ∞ ℓ x)
    (heq : ∀ᶠ x in cocompact E, Δ ℓ x = κ * (Real.exp (ℓ x) - 1))
    (hℓd : ℓ =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖))) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ Real.exp (ℓ x) - 1) =O[cocompact E]
      fun x ↦ Real.exp (-(c * ‖x‖)) := by
  -- Pass to a globally smooth `ℓ'` agreeing with `ℓ` near every point outside a compact set.
  obtain ⟨ℓ', hℓ'c, hagree⟩ := exists_contDiff_eventually_eventuallyEq hℓ
  have heq' : ∀ᶠ x in cocompact E, Δ ℓ' x = κ * (Real.exp (ℓ' x) - 1) := by
    filter_upwards [hagree, heq] with x hx hx'
    rw [(laplacian_congr_nhds hx).eq_of_nhds, hx', hx.eq_of_nhds]
  have hℓd' : ℓ' =O[cocompact E] fun x ↦ Real.exp (-(c * ‖x‖)) :=
    hℓd.congr' (hagree.mono fun x hx ↦ hx.eq_of_nhds.symm) EventuallyEq.rfl
  have h : iteratedFDeriv ℝ n (fun x ↦ Real.exp (ℓ' x) - 1) =O[cocompact E]
      fun x ↦ Real.exp (-(c * ‖x‖)) :=
    (hℓ'c.of_le (by simp)).isBigO_iteratedFDeriv_exp_sub_one
      (by simpa using isBigO_exp_neg_mul_norm_of_le hc.le (cocompact E)) fun i _ ↦
        isBigO_iteratedFDeriv_of_laplacian_eq_exp_sub_one hc hcκ
          (Eventually.of_forall fun x ↦ hℓ'c.contDiffAt) heq' hℓd' i
  refine h.congr' (hagree.mono fun x hx ↦ ?_) EventuallyEq.rfl
  exact (((hx.fun_comp Real.exp).sub EventuallyEq.rfl).iteratedFDeriv ℝ n).eq_of_nhds

end TauCeti
