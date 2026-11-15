/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Semigroup
public import TauCeti.Analysis.GradientFlow.MoreauYosida.Convex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Analysis.GradientFlow.EVI.Stability
import TauCeti.Analysis.GradientFlow.MinimizingMovement
import TauCeti.Analysis.ODE.Gronwall

/-!
# Convergence of minimizing movements to `EVI_λ` gradient flows

Let `φ : X → EReal` be a lower semicontinuous coercive energy on a complete pseudometric space `X`
satisfying Assumption 4.0.1 of Ambrosio–Gigli–Savaré (`TauCeti.PenalizedConvex lam τ φ`) for all
sufficiently small time steps `τ > 0`. This file proves Theorem 4.0.4 of Ambrosio–Gigli–Savaré:

* From every `x₀` in the effective domain `{x | φ x ≠ ⊤}` there starts an `EVI_λ` solution `u` with
  `u 0 = x₀`, and the piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of *every* family of
  minimizing movement sequences from `x₀` with time steps `τ j → 0` converge to `u` uniformly on
  bounded intervals `[0, T]`
  (`TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent_of_penalizedConvex`).
* The set of initial points of `EVI_λ` solutions is the closure of the effective domain,
  `eviDomain lam φ = closure {x | φ x ≠ ⊤}` (`TauCeti.eviDomain_eq_closure_of_penalizedConvex`),
  closing the existence question left open in `TauCeti.Analysis.GradientFlow.EVI.Semigroup`.
* On a complete CAT(0) space, both conclusions hold for every lower semicontinuous `λ`-geodesically
  convex energy that never takes the value `⊥`
  (`TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent` and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`).

## Proof outline

No compactness of energy sublevels is assumed. Instead, two minimizing movement sequences `U` and
`V` from `x₀` with small time steps `τ` and `σ` are compared directly in the metric of `X`.
Restricting the bilinear interpolant of `(m, n) ↦ d(U m, V n)² / 2` on `[0, ∞)²` to the diagonal
gives a continuous function `δ` on `[0, ∞)` that is smooth on each grid subinterval and has an
explicit right derivative everywhere. Combining the four discrete variational inequalities of
`TauCeti.PenalizedConvex.apply_add_le_of_mem_moreauYosidaResolvent` at `(⌊s / τ⌋₊, ⌊s / σ⌋₊)` with
the bilinear weights decouples the energies into telescoping step decreases, up to a `λ`-error
controlled by the step lengths. Integrating with `e^{2λs}` via Grönwall's inequality and bounding
the accumulated step lengths by Cauchy–Schwarz and the discrete energy inequality yields a linear
rate `d(U ⌈t / τ⌉₊, V ⌈t / σ⌉₊)² ≤ K (τ + σ)` on `[0, T]`.

Completeness of `X` produces a uniform limit curve `u` along a canonical sequence of time steps
(whose resolvent chains exist by `TauCeti.PenalizedConvex.exists_forall_mem_moreauYosidaResolvent`),
and the same two-chain estimate forces every other family of minimizing movement sequences from
`x₀` to converge uniformly to `u`. Passing the discrete Hölder estimate
`TauCeti.edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent` and the discrete energy
regularization estimate `TauCeti.PenalizedConvex.apply_le` to the limit shows that `u` satisfies
the endpoint characterization `TauCeti.isEVISolution_iff_apply_le` of `EVI_λ` solutions. Initial
points in `closure {x | φ x ≠ ⊤}` are then reached by `λ`-contraction of `EVI_λ` solutions and the
stability theorem `TauCeti.TendstoGamma.isEVISolution_of_tendsto`.

## Main results

* `TauCeti.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent_of_penalizedConvex`:
  uniform convergence of minimizing movements from `x₀` with `φ x₀ ≠ ⊤` to an `EVI_λ` solution.
* `TauCeti.eviDomain_eq_closure_of_penalizedConvex`: `eviDomain lam φ = closure {x | φ x ≠ ⊤}`.
* `TauCeti.GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent` and
  `TauCeti.GeodesicallyConvex.eviDomain_eq_closure`: specialization to `λ`-geodesically convex
  energies on complete CAT(0) spaces.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Theorem 4.0.4 and Section 4.2.
-/

public section

open Filter Finset Set Topology Real
open scoped NNReal ENNReal

namespace TauCeti

/-! ### Piecewise linear and diagonal bilinear interpolation -/

section Interpolant

/-- Piecewise linear interpolation of `f : ℕ → ℝ` with step `τ` at time `t`. -/
private noncomputable def linInterp (τ : ℝ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  (1 - (t / τ - ⌊t / τ⌋₊)) * f ⌊t / τ⌋₊ + (t / τ - ⌊t / τ⌋₊) * f (⌊t / τ⌋₊ + 1)

/-- Diagonal evaluation at `(t, t)` of the bilinear interpolation of `G : ℕ → ℕ → ℝ` on the grid
`(m τ, n σ)`. -/
private noncomputable def bilinInterp (τ σ : ℝ) (G : ℕ → ℕ → ℝ) (t : ℝ) : ℝ :=
  linInterp τ (fun m ↦ linInterp σ (G m) t) t

private lemma linInterp_zero (τ : ℝ) (f : ℕ → ℝ) : linInterp τ f 0 = f 0 := by
  simp [linInterp]

private lemma bilinInterp_zero (τ σ : ℝ) (G : ℕ → ℕ → ℝ) : bilinInterp τ σ G 0 = G 0 0 := by
  simp [bilinInterp, linInterp_zero]

private lemma bilinInterp_const_right (τ σ : ℝ) (f : ℕ → ℝ) :
    bilinInterp τ σ (fun m _ ↦ f m) = linInterp τ f := by
  ext t
  have hconst (m : ℕ) : linInterp σ (fun _ ↦ f m) t = f m := by
    simp only [linInterp]
    ring
  simp only [bilinInterp, hconst]

/-- On the closed grid interval `[j τ, (j + 1) τ]`, `linInterp τ f` agrees with the affine
interpolant between `f j` and `f (j + 1)`, including at the right endpoint `(j + 1) τ`. -/
private lemma linInterp_eq_on_Icc {τ : ℝ} (hτ : 0 < τ) (f : ℕ → ℝ) (j : ℕ) {t : ℝ}
    (ht : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) :
    linInterp τ f t = ((j : ℝ) + 1 - t / τ) * f j + (t / τ - j) * f (j + 1) := by
  have h1 : (j : ℝ) ≤ t / τ := (le_div_iff₀ hτ).2 ht.1
  have h2 : t / τ ≤ (j : ℝ) + 1 := (div_le_iff₀ hτ).2 ht.2
  rcases h2.eq_or_lt with heq | hlt
  · have hfl : ⌊t / τ⌋₊ = j + 1 := by
      rw [heq, ← Nat.cast_add_one]
      exact Nat.floor_natCast (j + 1)
    rw [linInterp, hfl, heq]
    push_cast
    ring
  · have hfl : ⌊t / τ⌋₊ = j :=
      (Nat.floor_eq_iff ((Nat.cast_nonneg j).trans h1)).2 ⟨h1, hlt⟩
    rw [linInterp, hfl]
    ring

private lemma bilinInterp_eq_on_Icc {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (G : ℕ → ℕ → ℝ)
    (j k : ℕ) {t : ℝ} (htτ : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ))
    (htσ : t ∈ Icc ((k : ℝ) * σ) (((k : ℝ) + 1) * σ)) :
    bilinInterp τ σ G t =
      ((j : ℝ) + 1 - t / τ) * (((k : ℝ) + 1 - t / σ) * G j k + (t / σ - k) * G j (k + 1)) +
        (t / τ - j) *
          (((k : ℝ) + 1 - t / σ) * G (j + 1) k + (t / σ - k) * G (j + 1) (k + 1)) := by
  simp only [bilinInterp, linInterp_eq_on_Icc hτ _ j htτ, linInterp_eq_on_Icc hσ _ k htσ]

/-- Exact right derivative of `bilinInterp τ σ G` at every nonnegative time `s`. -/
private lemma hasDerivWithinAt_bilinInterp_Ici {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ)
    (G : ℕ → ℕ → ℝ) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivWithinAt (bilinInterp τ σ G)
      ((1 - (s / σ - ⌊s / σ⌋₊)) * (G (⌊s / τ⌋₊ + 1) ⌊s / σ⌋₊ - G ⌊s / τ⌋₊ ⌊s / σ⌋₊) / τ +
        (s / σ - ⌊s / σ⌋₊) * (G (⌊s / τ⌋₊ + 1) (⌊s / σ⌋₊ + 1) - G ⌊s / τ⌋₊ (⌊s / σ⌋₊ + 1)) / τ +
        (1 - (s / τ - ⌊s / τ⌋₊)) * (G ⌊s / τ⌋₊ (⌊s / σ⌋₊ + 1) - G ⌊s / τ⌋₊ ⌊s / σ⌋₊) / σ +
        (s / τ - ⌊s / τ⌋₊) * (G (⌊s / τ⌋₊ + 1) (⌊s / σ⌋₊ + 1) - G (⌊s / τ⌋₊ + 1) ⌊s / σ⌋₊) / σ)
      (Ici s) s := by
  set j := ⌊s / τ⌋₊
  set k := ⌊s / σ⌋₊
  set b := min (((j : ℝ) + 1) * τ) (((k : ℝ) + 1) * σ)
  have hsτ : (j : ℝ) * τ ≤ s ∧ s < ((j : ℝ) + 1) * τ :=
    ⟨(le_div_iff₀ hτ).1 (Nat.floor_le (div_nonneg hs hτ.le)),
      (div_lt_iff₀ hτ).1 (Nat.lt_floor_add_one _)⟩
  have hsσ : (k : ℝ) * σ ≤ s ∧ s < ((k : ℝ) + 1) * σ :=
    ⟨(le_div_iff₀ hσ).1 (Nat.floor_le (div_nonneg hs hσ.le)),
      (div_lt_iff₀ hσ).1 (Nat.lt_floor_add_one _)⟩
  let P : ℝ → ℝ := fun t ↦
    ((j : ℝ) + 1 - t / τ) * (((k : ℝ) + 1 - t / σ) * G j k + (t / σ - k) * G j (k + 1)) +
      (t / τ - j) * (((k : ℝ) + 1 - t / σ) * G (j + 1) k + (t / σ - k) * G (j + 1) (k + 1))
  have hA : HasDerivAt (fun t ↦ (j : ℝ) + 1 - t / τ) (-(1 / τ)) s := by
    simpa using ((hasDerivAt_id s).div_const τ).const_sub ((j : ℝ) + 1)
  have hA' : HasDerivAt (fun t ↦ t / τ - (j : ℝ)) (1 / τ) s := by
    simpa using ((hasDerivAt_id s).div_const τ).sub_const (j : ℝ)
  have hB : HasDerivAt (fun t ↦ (k : ℝ) + 1 - t / σ) (-(1 / σ)) s := by
    simpa using ((hasDerivAt_id s).div_const σ).const_sub ((k : ℝ) + 1)
  have hB' : HasDerivAt (fun t ↦ t / σ - (k : ℝ)) (1 / σ) s := by
    simpa using ((hasDerivAt_id s).div_const σ).sub_const (k : ℝ)
  have hP : HasDerivAt P
      ((1 - (s / σ - k)) * (G (j + 1) k - G j k) / τ +
        (s / σ - k) * (G (j + 1) (k + 1) - G j (k + 1)) / τ +
        (1 - (s / τ - j)) * (G j (k + 1) - G j k) / σ +
        (s / τ - j) * (G (j + 1) (k + 1) - G (j + 1) k) / σ) s :=
    ((hA.fun_mul ((hB.mul_const (G j k)).fun_add (hB'.mul_const (G j (k + 1))))).fun_add
      (hA'.fun_mul ((hB.mul_const (G (j + 1) k)).fun_add
        (hB'.mul_const (G (j + 1) (k + 1)))))).congr_deriv (by ring)
  have heq : ∀ t ∈ Icc s b, bilinInterp τ σ G t = P t := fun t ht ↦
    bilinInterp_eq_on_Icc hτ hσ G j k ⟨hsτ.1.trans ht.1, ht.2.trans (min_le_left _ _)⟩
      ⟨hsσ.1.trans ht.1, ht.2.trans (min_le_right _ _)⟩
  have hsb : s < b := lt_min hsτ.2 hsσ.2
  exact hP.hasDerivWithinAt.congr_of_eventuallyEq
    (mem_of_superset (Icc_mem_nhdsGE hsb) heq) (heq s ⟨le_rfl, hsb.le⟩)

private lemma continuousOn_bilinInterp {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 < σ) (G : ℕ → ℕ → ℝ) :
    ContinuousOn (bilinInterp τ σ G) (Ici 0) := by
  intro s (hs : 0 ≤ s)
  have hright := (hasDerivWithinAt_bilinInterp_Ici hτ hσ G hs).continuousWithinAt
  rcases hs.eq_or_lt with rfl | hs_pos
  · exact hright
  · refine (continuousAt_iff_continuous_left_right.2 ⟨?_, hright⟩).continuousWithinAt
    set j := ⌈s / τ⌉₊ - 1
    set k := ⌈s / σ⌉₊ - 1
    have hj1 : j + 1 = ⌈s / τ⌉₊ := Nat.sub_add_cancel (Nat.ceil_pos.2 (div_pos hs_pos hτ))
    have hk1 : k + 1 = ⌈s / σ⌉₊ := Nat.sub_add_cancel (Nat.ceil_pos.2 (div_pos hs_pos hσ))
    have hsτ : (j : ℝ) * τ < s ∧ s ≤ ((j : ℝ) + 1) * τ :=
      ⟨(lt_div_iff₀ hτ).1 (Nat.lt_ceil.1 (hj1 ▸ Nat.lt_add_one j)),
        (div_le_iff₀ hτ).1 (by exact_mod_cast hj1 ▸ Nat.le_ceil (s / τ))⟩
    have hsσ : (k : ℝ) * σ < s ∧ s ≤ ((k : ℝ) + 1) * σ :=
      ⟨(lt_div_iff₀ hσ).1 (Nat.lt_ceil.1 (hk1 ▸ Nat.lt_add_one k)),
        (div_le_iff₀ hσ).1 (by exact_mod_cast hk1 ▸ Nat.le_ceil (s / σ))⟩
    set a := max ((j : ℝ) * τ) ((k : ℝ) * σ)
    let P : ℝ → ℝ := fun t ↦
      ((j : ℝ) + 1 - t / τ) * (((k : ℝ) + 1 - t / σ) * G j k + (t / σ - k) * G j (k + 1)) +
        (t / τ - j) * (((k : ℝ) + 1 - t / σ) * G (j + 1) k + (t / σ - k) * G (j + 1) (k + 1))
    have hP : Continuous P := by fun_prop
    have has : a < s := max_lt hsτ.1 hsσ.1
    have heq : ∀ t ∈ Icc a s, bilinInterp τ σ G t = P t := fun t ht ↦
      bilinInterp_eq_on_Icc hτ hσ G j k ⟨(le_max_left _ _).trans ht.1, ht.2.trans hsτ.2⟩
        ⟨(le_max_right _ _).trans ht.1, ht.2.trans hsσ.2⟩
    exact hP.continuousWithinAt.congr_of_eventuallyEq
      (mem_of_superset (Icc_mem_nhdsLE has) heq) (heq s ⟨has.le, le_rfl⟩)

private lemma hasDerivWithinAt_linInterp_Ici {τ : ℝ} (hτ : 0 < τ) (f : ℕ → ℝ) {s : ℝ}
    (hs : 0 ≤ s) :
    HasDerivWithinAt (linInterp τ f) ((f (⌊s / τ⌋₊ + 1) - f ⌊s / τ⌋₊) / τ) (Ici s) s := by
  have h := hasDerivWithinAt_bilinInterp_Ici hτ one_pos (fun m _ ↦ f m) hs
  rw [bilinInterp_const_right] at h
  exact h.congr_deriv (by ring)

private lemma continuousOn_linInterp {τ : ℝ} (hτ : 0 < τ) (f : ℕ → ℝ) :
    ContinuousOn (linInterp τ f) (Ici 0) := by
  rw [← bilinInterp_const_right τ 1 f]
  exact continuousOn_bilinInterp hτ one_pos (fun m _ ↦ f m)

end Interpolant

/-! ### Uniform metric comparison of two minimizing movement sequences -/

section TwoChainComparison

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}

/-- Real one-step discrete variational inequality for half-squared distances. -/
private lemma div_add_mul_dist_sq_le_sub {τ : ℝ≥0} (hconv : PenalizedConvex lam τ φ) (hτ : 0 < τ)
    {x y v : X} (hy : y ∈ moreauYosidaResolvent φ τ x) {ey ev : ℝ} (hey : φ y = ey)
    (hev : φ v = ev) :
    (dist y v ^ 2 / 2 - dist x v ^ 2 / 2) / τ + lam * (dist y v ^ 2 / 2) ≤ ev - ey := by
  have hvi := hconv.apply_add_le_of_mem_moreauYosidaResolvent hτ hy (hev ▸ EReal.coe_ne_top ev)
  rw [hey, hev, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at hvi
  have hτ' : (τ : ℝ) ≠ 0 := (NNReal.coe_pos.2 hτ).ne'
  have hrew : (dist y v ^ 2 / 2 - dist x v ^ 2 / 2) / τ + lam * (dist y v ^ 2 / 2) =
      dist y v ^ 2 / (2 * τ) + lam / 2 * dist y v ^ 2 - dist x v ^ 2 / (2 * τ) := by
    field_simp
    ring
  have hnn : 0 ≤ dist x y ^ 2 / (2 * τ) := by positivity
  linarith

/-- Perturbation bound between `2 * δ(s)` and the `λ`-weighted terms from the four discrete
variational inequalities on a grid cell `[j, j + 1] × [k, k + 1]`. -/
private lemma mul_two_bilin_sub_le {x₀ u₀ u₁ v₀ v₁ : X} {R α β : ℝ}
    (hu₀ : dist x₀ u₀ ≤ R) (hu₁ : dist x₀ u₁ ≤ R) (hv₀ : dist x₀ v₀ ≤ R) (hv₁ : dist x₀ v₁ ≤ R)
    (hα : α ∈ Icc (0 : ℝ) 1) (hβ : β ∈ Icc (0 : ℝ) 1) :
    lam * (2 * ((1 - α) * ((1 - β) * (dist u₀ v₀ ^ 2 / 2) + β * (dist u₀ v₁ ^ 2 / 2)) +
        α * ((1 - β) * (dist u₁ v₀ ^ 2 / 2) + β * (dist u₁ v₁ ^ 2 / 2))) -
      ((1 - β) * (dist u₁ v₀ ^ 2 / 2) + β * (dist u₁ v₁ ^ 2 / 2) +
        (1 - α) * (dist u₀ v₁ ^ 2 / 2) + α * (dist u₁ v₁ ^ 2 / 2))) ≤
      8 * |lam| * R * (dist u₀ u₁ + dist v₀ v₁) := by
  have hcell (u v : X) (hu : dist x₀ u ≤ R) (hv : dist x₀ v ≤ R)
      (hdu : dist u u₁ ≤ dist u₀ u₁) (hdv : dist v v₁ ≤ dist v₀ v₁) :
      |dist u v ^ 2 / 2 - dist u₁ v₁ ^ 2 / 2| ≤ 2 * R * (dist u₀ u₁ + dist v₀ v₁) := by
    have hsum : dist u v + dist u₁ v₁ ≤ 4 * R := by
      linarith [dist_triangle_left u v x₀, dist_triangle_left u₁ v₁ x₀]
    have hdiff : |dist u v - dist u₁ v₁| ≤ dist u₀ u₁ + dist v₀ v₁ := by
      rw [abs_le]
      refine ⟨by linarith [dist_triangle u₁ u v₁, dist_triangle u v v₁, dist_comm u₁ u],
        by linarith [dist_triangle u u₁ v, dist_triangle u₁ v₁ v, dist_comm v₁ v]⟩
    calc |dist u v ^ 2 / 2 - dist u₁ v₁ ^ 2 / 2|
        = |dist u v - dist u₁ v₁| * ((dist u v + dist u₁ v₁) / 2) := by
          rw [← abs_of_nonneg (by positivity : 0 ≤ (dist u v + dist u₁ v₁) / 2), ← abs_mul]
          congr 1; ring
      _ ≤ (dist u₀ u₁ + dist v₀ v₁) * (2 * R) :=
          mul_le_mul hdiff (by linarith) (by positivity) (by positivity)
      _ = 2 * R * (dist u₀ u₁ + dist v₀ v₁) := by ring
  set M := 2 * R * (dist u₀ u₁ + dist v₀ v₁)
  have h00 := hcell u₀ v₀ hu₀ hv₀ le_rfl le_rfl
  have h01 := hcell u₀ v₁ hu₀ hv₁ le_rfl (by simp)
  have h10 := hcell u₁ v₀ hu₁ hv₀ (by simp) le_rfl
  set D := 2 * ((1 - α) * ((1 - β) * (dist u₀ v₀ ^ 2 / 2) + β * (dist u₀ v₁ ^ 2 / 2)) +
      α * ((1 - β) * (dist u₁ v₀ ^ 2 / 2) + β * (dist u₁ v₁ ^ 2 / 2))) -
    ((1 - β) * (dist u₁ v₀ ^ 2 / 2) + β * (dist u₁ v₁ ^ 2 / 2) +
      (1 - α) * (dist u₀ v₁ ^ 2 / 2) + α * (dist u₁ v₁ ^ 2 / 2))
  have hD : D = 2 * (1 - α) * (1 - β) * (dist u₀ v₀ ^ 2 / 2 - dist u₁ v₁ ^ 2 / 2) +
      (1 - α) * (2 * β - 1) * (dist u₀ v₁ ^ 2 / 2 - dist u₁ v₁ ^ 2 / 2) +
      (1 - β) * (2 * α - 1) * (dist u₁ v₀ ^ 2 / 2 - dist u₁ v₁ ^ 2 / 2) := by ring
  have hD_abs : |D| ≤ 4 * M := by
    rw [hD]
    have hc1 : |2 * (1 - α) * (1 - β)| ≤ 2 := by
      rw [abs_of_nonneg (by nlinarith [hα.1, hα.2, hβ.1, hβ.2])]
      nlinarith [hα.1, hα.2, hβ.1, hβ.2]
    have hc2 : |(1 - α) * (2 * β - 1)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hα.1, hα.2, hβ.1, hβ.2]
    have hc3 : |(1 - β) * (2 * α - 1)| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [hα.1, hα.2, hβ.1, hβ.2]
    refine ((abs_add_three _ _ _).trans ?_).trans (by linarith : 2 * M + 1 * M + 1 * M ≤ 4 * M)
    rw [abs_mul (2 * (1 - α) * (1 - β)), abs_mul ((1 - α) * (2 * β - 1)),
      abs_mul ((1 - β) * (2 * α - 1))]
    gcongr
  calc lam * D ≤ |lam * D| := le_abs_self _
    _ = |lam| * |D| := abs_mul lam D
    _ ≤ |lam| * (4 * M) := mul_le_mul_of_nonneg_left hD_abs (abs_nonneg lam)
    _ = 8 * |lam| * R * (dist u₀ u₁ + dist v₀ v₁) := by dsimp [M]; ring

/-- One-cell differential inequality for the diagonal bilinear interpolant of half-squared
distances between two minimizing movement sequences. -/
private lemma deriv_bilinInterp_add_mul_le {τ σ : ℝ≥0} (hτ_conv : PenalizedConvex lam τ φ)
    (hσ_conv : PenalizedConvex lam σ φ) (hτ : 0 < τ) (hσ : 0 < σ) {x₀ : X} {U V : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ n, V (n + 1) ∈ moreauYosidaResolvent φ σ (V n)) {R : ℝ} {j k : ℕ}
    {eU0 eU1 eV0 eV1 : ℝ} (heU0 : φ (U j) = eU0) (heU1 : φ (U (j + 1)) = eU1)
    (heV0 : φ (V k) = eV0) (heV1 : φ (V (k + 1)) = eV1) (hdU0 : dist x₀ (U j) ≤ R)
    (hdU1 : dist x₀ (U (j + 1)) ≤ R) (hdV0 : dist x₀ (V k) ≤ R) (hdV1 : dist x₀ (V (k + 1)) ≤ R)
    {s : ℝ} (hsτ : ⌊s / τ⌋₊ = j) (hsσ : ⌊s / σ⌋₊ = k) (hs : 0 ≤ s) :
    let G := fun m n ↦ dist (U m) (V n) ^ 2 / 2
    ((1 - (s / σ - k)) * (G (j + 1) k - G j k) / τ +
        (s / σ - k) * (G (j + 1) (k + 1) - G j (k + 1)) / τ +
        (1 - (s / τ - j)) * (G j (k + 1) - G j k) / σ +
        (s / τ - j) * (G (j + 1) (k + 1) - G (j + 1) k) / σ) +
      2 * lam * bilinInterp τ σ G s ≤
      (eU0 - eU1 + 8 * |lam| * R * dist (U j) (U (j + 1))) +
        (eV0 - eV1 + 8 * |lam| * R * dist (V k) (V (k + 1))) := by
  intro G
  set α := s / τ - (j : ℝ)
  set β := s / σ - (k : ℝ)
  have hα : α ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.2 (hsτ ▸ Nat.floor_le (div_nonneg hs (NNReal.coe_nonneg τ))),
      sub_le_iff_le_add'.2 (hsτ ▸ (Nat.lt_floor_add_one (s / τ)).le)⟩
  have hβ : β ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.2 (hsσ ▸ Nat.floor_le (div_nonneg hs (NNReal.coe_nonneg σ))),
      sub_le_iff_le_add'.2 (hsσ ▸ (Nat.lt_floor_add_one (s / σ)).le)⟩
  have h1 := div_add_mul_dist_sq_le_sub hτ_conv hτ (hU j) heU1 heV0
  have h2 := div_add_mul_dist_sq_le_sub hτ_conv hτ (hU j) heU1 heV1
  have h3 := div_add_mul_dist_sq_le_sub hσ_conv hσ (hV k) heV1 heU0
  have h4 := div_add_mul_dist_sq_le_sub hσ_conv hσ (hV k) heV1 heU1
  simp only [dist_comm (V _) (U _)] at h3 h4
  have heU_dec : eU1 ≤ eU0 := by
    exact_mod_cast heU1 ▸ heU0 ▸ apply_le_of_mem_moreauYosidaResolvent (hU j)
  have heV_dec : eV1 ≤ eV0 := by
    exact_mod_cast heV1 ▸ heV0 ▸ apply_le_of_mem_moreauYosidaResolvent (hV k)
  have hbilin : bilinInterp τ σ G s =
      (1 - α) * ((1 - β) * G j k + β * G j (k + 1)) +
        α * ((1 - β) * G (j + 1) k + β * G (j + 1) (k + 1)) := by
    simp only [bilinInterp, linInterp, hsτ, hsσ, α, β]
  have herr := mul_two_bilin_sub_le (lam := lam) hdU0 hdU1 hdV0 hdV1 hα hβ
  have hsum := add_le_add
    (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hβ.2))
        (mul_le_mul_of_nonneg_left h2 hβ.1))
      (add_le_add (mul_le_mul_of_nonneg_left h3 (sub_nonneg.2 hα.2))
        (mul_le_mul_of_nonneg_left h4 hα.1)))
    herr
  rw [hbilin]
  dsimp only [G]
  refine (le_of_eq_of_le (by ring) hsum).trans ?_
  nlinarith [hα.1, hβ.1, heU_dec, heV_dec]

private lemma apply_le_apply_zero {τ : ℝ≥0} {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) (m : ℕ) :
    φ (U m) ≤ φ (U 0) :=
  antitone_comp_of_forall_mem_moreauYosidaResolvent hU (Nat.zero_le m)

private lemma floor_div_add_one_le_ceil {τ : ℝ≥0} (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1) {t T : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ⌊t / (τ : ℝ)⌋₊ + 1 ≤ ⌈(T + 1) / (τ : ℝ)⌉₊ := by
  refine (Nat.cast_le (α := ℝ)).1 ?_
  calc ((⌊t / (τ : ℝ)⌋₊ + 1 : ℕ) : ℝ)
      = (⌊t / (τ : ℝ)⌋₊ : ℝ) + 1 := by push_cast; ring
    _ ≤ t / τ + 1 / τ := add_le_add (Nat.floor_le (div_nonneg ht0 (NNReal.coe_nonneg τ)))
        ((one_le_div (NNReal.coe_pos.2 hτ)).2 hτ1)
    _ ≤ (T + 1) / τ := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) (NNReal.coe_nonneg τ)
    _ ≤ (⌈(T + 1) / (τ : ℝ)⌉₊ : ℝ) := Nat.le_ceil _

/-- Total discrete path length of `U` up to step `⌈(T + 1) / τ⌉₊`, bounded via Cauchy–Schwarz and
the discrete energy inequality. -/
private lemma sum_dist_step_le_sqrt {τ : ℝ≥0} (hτ : 0 < τ) {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) {E L T : ℝ} (hT : 0 ≤ T)
    (hE : φ (U 0) = E) (hLN : (L : EReal) ≤ φ (U ⌈(T + 1) / (τ : ℝ)⌉₊)) :
    ∑ i ∈ range ⌈(T + 1) / (τ : ℝ)⌉₊, dist (U i) (U (i + 1)) ≤
      Real.sqrt (2 * (T + 1 + τ) * (E - L)) := by
  set N := ⌈(T + 1) / (τ : ℝ)⌉₊
  have he (m : ℕ) (hm : m ≤ N) : φ (U m) = ((φ (U m)).toReal : EReal) := by
    have hlow : (L : EReal) ≤ φ (U m) :=
      hLN.trans (antitone_comp_of_forall_mem_moreauYosidaResolvent hU hm)
    exact (EReal.coe_toReal
      (ne_top_of_le_ne_top (hE ▸ EReal.coe_ne_top E) (apply_le_apply_zero hU m))
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) hlow)).symm
  have hEL : L ≤ E := EReal.coe_le_coe_iff.1 (hLN.trans (hE ▸ apply_le_apply_zero hU N))
  have hsum_sq : ∑ i ∈ range N, dist (U i) (U (i + 1)) ^ 2 ≤ 2 * τ * (E - L) := by
    have hstep (i : ℕ) (hi : i ∈ range N) :
        dist (U i) (U (i + 1)) ^ 2 / (2 * τ) ≤ (φ (U i)).toReal - (φ (U (i + 1))).toReal := by
      have hiN : i + 1 ≤ N := Nat.succ_le_of_lt (mem_range.1 hi)
      have h1 := apply_add_le_of_mem_moreauYosidaResolvent (hU i)
      rw [he (i + 1) hiN, he i (Nat.le_of_succ_le hiN), coe_edist_sq_div_eq_coe_dist_sq_div hτ,
        ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      linarith
    have htele := (sum_div (range N) (fun i ↦ dist (U i) (U (i + 1)) ^ 2) (2 * (τ : ℝ))).trans_le
      ((sum_le_sum hstep).trans_eq (sum_range_sub' (fun i ↦ (φ (U i)).toReal) N))
    have he0 : (φ (U 0)).toReal = E := by rw [hE]; rfl
    have heNL : L ≤ (φ (U N)).toReal := EReal.coe_le_coe_iff.1 (he N le_rfl ▸ hLN)
    rw [← div_le_iff₀' (mul_pos two_pos (NNReal.coe_pos.2 hτ))]
    linarith
  have hNτ : (N : ℝ) * τ ≤ T + 1 + τ := by
    calc (N : ℝ) * τ ≤ ((T + 1) / τ + 1) * τ := mul_le_mul_of_nonneg_right
          (Nat.ceil_lt_add_one (div_nonneg (by linarith) (NNReal.coe_nonneg τ))).le
          (NNReal.coe_nonneg τ)
      _ = T + 1 + τ := by field_simp
  refine Real.le_sqrt_of_sq_le ?_
  calc (∑ i ∈ range N, dist (U i) (U (i + 1))) ^ 2
      ≤ N * ∑ i ∈ range N, dist (U i) (U (i + 1)) ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := range N) (f := fun i ↦ dist (U i) (U (i + 1)))
    _ ≤ N * (2 * τ * (E - L)) := mul_le_mul_of_nonneg_left hsum_sq (Nat.cast_nonneg N)
    _ = 2 * ((N : ℝ) * τ) * (E - L) := by ring
    _ ≤ 2 * (T + 1 + τ) * (E - L) := mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.2 hEL)

/-- Nonnegativity and upper bound of the piecewise linear primitive of the discrete forcing
sequence along a minimizing movement chain up to horizon `T`. -/
private lemma linInterp_sum_bounds {τ : ℝ≥0} (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1) {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) {E L R T : ℝ} (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hE : φ (U 0) = E) (hL : ∀ m ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U m))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    let N := ⌈(T + 1) / (τ : ℝ)⌉₊
    let a := fun m ↦ if m + 1 ≤ N then
      (φ (U m)).toReal - (φ (U (m + 1))).toReal + 8 * |lam| * R * dist (U m) (U (m + 1)) else 0
    0 ≤ linInterp τ (fun n ↦ (τ : ℝ) * ∑ i ∈ range n, a i) t ∧
      linInterp τ (fun n ↦ (τ : ℝ) * ∑ i ∈ range n, a i) t ≤
        τ * ((E - L) + 8 * |lam| * R * Real.sqrt (2 * (T + 2) * (E - L))) := by
  intro N a
  have he (m : ℕ) (hm : m ≤ N) : φ (U m) = ((φ (U m)).toReal : EReal) :=
    (EReal.coe_toReal (ne_top_of_le_ne_top (hE ▸ EReal.coe_ne_top E) (apply_le_apply_zero hU m))
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (hL m hm))).symm
  have ha_nn (m : ℕ) : 0 ≤ a m := by
    dsimp only [a]; split_ifs with hm
    · have : (φ (U (m + 1))).toReal ≤ (φ (U m)).toReal := EReal.coe_le_coe_iff.1
        (he (m + 1) hm ▸ he m (Nat.le_of_succ_le hm) ▸ apply_le_of_mem_moreauYosidaResolvent (hU m))
      linarith [show 0 ≤ 8 * |lam| * R * dist (U m) (U (m + 1)) by positivity]
    · exact le_rfl
  set j := ⌊t / (τ : ℝ)⌋₊
  have hjN : j + 1 ≤ N := floor_div_add_one_le_ceil hτ hτ1 ht.1 ht.2
  set u := t / τ - (j : ℝ)
  have hu0 : 0 ≤ u := sub_nonneg.2 (Nat.floor_le (div_nonneg ht.1 (NNReal.coe_nonneg τ)))
  have hu1 : 0 ≤ 1 - u := sub_nonneg.2 (sub_le_iff_le_add'.2 (Nat.lt_floor_add_one _).le)
  have hs0 : 0 ≤ ∑ i ∈ range j, a i := sum_nonneg fun i _ ↦ ha_nn i
  have hs1 : 0 ≤ ∑ i ∈ range (j + 1), a i := sum_nonneg fun i _ ↦ ha_nn i
  refine ⟨by change 0 ≤ (1 - u) * _ + u * _; positivity, ?_⟩
  have hmono {p q : ℕ} (hpq : p ≤ q) : ∑ i ∈ range p, a i ≤ ∑ i ∈ range q, a i :=
    sum_le_sum_of_subset_of_nonneg (range_mono hpq) fun i _ _ ↦ ha_nn i
  have hinterp : linInterp τ (fun n ↦ (τ : ℝ) * ∑ i ∈ range n, a i) t ≤
      (τ : ℝ) * ∑ i ∈ range N, a i := by
    change (1 - u) * ((τ : ℝ) * ∑ i ∈ range j, a i) +
      u * ((τ : ℝ) * ∑ i ∈ range (j + 1), a i) ≤ (τ : ℝ) * ∑ i ∈ range N, a i
    calc (1 - u) * ((τ : ℝ) * ∑ i ∈ range j, a i) + u * ((τ : ℝ) * ∑ i ∈ range (j + 1), a i)
        ≤ (1 - u) * ((τ : ℝ) * ∑ i ∈ range N, a i) + u * ((τ : ℝ) * ∑ i ∈ range N, a i) :=
          add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (hmono (Nat.le_of_succ_le hjN)) (NNReal.coe_nonneg τ)) hu1)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hmono hjN)
              (NNReal.coe_nonneg τ)) hu0)
      _ = (τ : ℝ) * ∑ i ∈ range N, a i := by ring
  have hsum_eq : ∑ i ∈ range N, a i = ((φ (U 0)).toReal - (φ (U N)).toReal) +
      8 * |lam| * R * ∑ i ∈ range N, dist (U i) (U (i + 1)) := by
    have ha_eq : ∀ i ∈ range N, a i = (φ (U i)).toReal - (φ (U (i + 1))).toReal +
        8 * |lam| * R * dist (U i) (U (i + 1)) :=
      fun i hi ↦ ite_eq_left (Nat.succ_le_of_lt (mem_range.1 hi))
    rw [sum_congr rfl ha_eq, sum_add_distrib, sum_range_sub', ← mul_sum]
  have hEL : L ≤ E := EReal.coe_le_coe_iff.1 ((hL N le_rfl).trans (hE ▸ apply_le_apply_zero hU N))
  have hlen : ∑ i ∈ range N, dist (U i) (U (i + 1)) ≤ Real.sqrt (2 * (T + 2) * (E - L)) :=
    (sum_dist_step_le_sqrt hτ hU hT hE (hL N le_rfl)).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.2 hEL)))
  have he0 : (φ (U 0)).toReal = E := by rw [hE]; rfl
  have hLN : L ≤ (φ (U N)).toReal := EReal.coe_le_coe_iff.1 (he N le_rfl ▸ hL N le_rfl)
  refine hinterp.trans (mul_le_mul_of_nonneg_left ?_ (NNReal.coe_nonneg τ))
  rw [hsum_eq, he0]
  linarith [mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ 8 * |lam| * R)]

/-- Right-derivative nonpositivity of the integrating-factor functional on `[0, T)`. -/
private lemma exists_hasDerivWithinAt_nonpos_bilinInterp {τ σ : ℝ≥0}
    (hτ_conv : PenalizedConvex lam τ φ) (hσ_conv : PenalizedConvex lam σ φ) (hτ : 0 < τ)
    (hτ1 : (τ : ℝ) ≤ 1) (hσ : 0 < σ) (hσ1 : (σ : ℝ) ≤ 1) {x₀ : X} {U V : ℕ → X}
    (hU0 : U 0 = x₀) (hV0 : V 0 = x₀) (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ n, V (n + 1) ∈ moreauYosidaResolvent φ σ (V n)) {E L R T : ℝ} (hR : 0 ≤ R)
    (hE : φ x₀ = E)
    (hLU : ∀ m ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U m) ∧ dist x₀ (U m) ≤ R)
    (hLV : ∀ n ≤ ⌈(T + 1) / (σ : ℝ)⌉₊, (L : EReal) ≤ φ (V n) ∧ dist x₀ (V n) ≤ R)
    {s : ℝ} (hs : s ∈ Ico 0 T) :
    let aU := fun m ↦ if m + 1 ≤ ⌈(T + 1) / (τ : ℝ)⌉₊ then
      (φ (U m)).toReal - (φ (U (m + 1))).toReal + 8 * |lam| * R * dist (U m) (U (m + 1)) else 0
    let aV := fun n ↦ if n + 1 ≤ ⌈(T + 1) / (σ : ℝ)⌉₊ then
      (φ (V n)).toReal - (φ (V (n + 1))).toReal + 8 * |lam| * R * dist (V n) (V (n + 1)) else 0
    ∃ f', HasDerivWithinAt
      (fun r ↦ exp (2 * lam * r) * bilinInterp τ σ (fun m n ↦ dist (U m) (V n) ^ 2 / 2) r -
        exp (2 * |lam| * T) * (linInterp τ (fun n ↦ (τ : ℝ) * ∑ i ∈ range n, aU i) r +
          linInterp σ (fun n ↦ (σ : ℝ) * ∑ i ∈ range n, aV i) r)) f' (Ici s) s ∧ f' ≤ 0 := by
  intro aU aV
  set j := ⌊s / (τ : ℝ)⌋₊
  set k := ⌊s / (σ : ℝ)⌋₊
  have hj : j + 1 ≤ ⌈(T + 1) / (τ : ℝ)⌉₊ := floor_div_add_one_le_ceil hτ hτ1 hs.1 hs.2.le
  have hk : k + 1 ≤ ⌈(T + 1) / (σ : ℝ)⌉₊ := floor_div_add_one_le_ceil hσ hσ1 hs.1 hs.2.le
  have heU (m : ℕ) (hm : m ≤ ⌈(T + 1) / (τ : ℝ)⌉₊) : φ (U m) = ((φ (U m)).toReal : EReal) :=
    (EReal.coe_toReal
      (ne_top_of_le_ne_top (hU0 ▸ hE ▸ EReal.coe_ne_top E) (apply_le_apply_zero hU m))
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (hLU m hm).1)).symm
  have heV (n : ℕ) (hn : n ≤ ⌈(T + 1) / (σ : ℝ)⌉₊) : φ (V n) = ((φ (V n)).toReal : EReal) :=
    (EReal.coe_toReal
      (ne_top_of_le_ne_top (hV0 ▸ hE ▸ EReal.coe_ne_top E) (apply_le_apply_zero hV n))
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot L) (hLV n hn).1)).symm
  have hdδ := hasDerivWithinAt_bilinInterp_Ici (NNReal.coe_pos.2 hτ) (NNReal.coe_pos.2 hσ)
    (fun m n ↦ dist (U m) (V n) ^ 2 / 2) hs.1
  have hdU := (hasDerivWithinAt_linInterp_Ici (NNReal.coe_pos.2 hτ)
    (fun n ↦ (τ : ℝ) * ∑ i ∈ range n, aU i) hs.1).congr_deriv (by
      rw [sum_range_succ, ← mul_sub, add_sub_cancel_left,
        mul_div_cancel_left₀ _ (NNReal.coe_pos.2 hτ).ne'])
  have hdV := (hasDerivWithinAt_linInterp_Ici (NNReal.coe_pos.2 hσ)
    (fun n ↦ (σ : ℝ) * ∑ i ∈ range n, aV i) hs.1).congr_deriv (by
      rw [sum_range_succ, ← mul_sub, add_sub_cancel_left,
        mul_div_cancel_left₀ _ (NNReal.coe_pos.2 hσ).ne'])
  have hexp : HasDerivWithinAt (fun r ↦ exp (2 * lam * r)) (2 * lam * exp (2 * lam * s))
      (Ici s) s := by
    simpa [mul_comm] using (((hasDerivAt_id s).const_mul (2 * lam)).exp).hasDerivWithinAt
  refine ⟨_, (hexp.fun_mul hdδ).fun_sub ((hdU.fun_add hdV).const_mul (exp (2 * |lam| * T))), ?_⟩
  have hcell := deriv_bilinInterp_add_mul_le hτ_conv hσ_conv hτ hσ hU hV
    (heU j (Nat.le_of_succ_le hj)) (heU (j + 1) hj) (heV k (Nat.le_of_succ_le hk))
    (heV (k + 1) hk) (hLU j (Nat.le_of_succ_le hj)).2 (hLU (j + 1) hj).2
    (hLV k (Nat.le_of_succ_le hk)).2 (hLV (k + 1) hk).2 rfl rfl hs.1
  have haU_eq : aU j = (φ (U j)).toReal - (φ (U (j + 1))).toReal +
      8 * |lam| * R * dist (U j) (U (j + 1)) := ite_eq_left hj
  have haV_eq : aV k = (φ (V k)).toReal - (φ (V (k + 1))).toReal +
      8 * |lam| * R * dist (V k) (V (k + 1)) := ite_eq_left hk
  have haU0 : 0 ≤ aU j := by
    have := EReal.coe_le_coe_iff.1
      (heU (j + 1) hj ▸ heU j (Nat.le_of_succ_le hj) ▸ apply_le_of_mem_moreauYosidaResolvent (hU j))
    linarith [haU_eq, show 0 ≤ 8 * |lam| * R * dist (U j) (U (j + 1)) by positivity]
  have haV0 : 0 ≤ aV k := by
    have := EReal.coe_le_coe_iff.1
      (heV (k + 1) hk ▸ heV k (Nat.le_of_succ_le hk) ▸ apply_le_of_mem_moreauYosidaResolvent (hV k))
    linarith [haV_eq, show 0 ≤ 8 * |lam| * R * dist (V k) (V (k + 1)) by positivity]
  have hexp_le : exp (2 * lam * s) ≤ exp (2 * |lam| * T) :=
    exp_le_exp.2 (by nlinarith [le_abs_self lam, abs_nonneg lam, hs.1, hs.2.le])
  nlinarith [mul_le_mul_of_nonneg_left (haU_eq ▸ haV_eq ▸ hcell) (exp_pos (2 * lam * s)).le,
    mul_le_mul_of_nonneg_right hexp_le (add_nonneg haU0 haV0)]

/-- Grönwall integration of the diagonal bilinear interpolant inequality on `[0, T]`. -/
private lemma bilinInterp_dist_sq_le {τ σ : ℝ≥0} (hτ_conv : PenalizedConvex lam τ φ)
    (hσ_conv : PenalizedConvex lam σ φ) (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1) (hσ : 0 < σ)
    (hσ1 : (σ : ℝ) ≤ 1) {x₀ : X} {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ n, V (n + 1) ∈ moreauYosidaResolvent φ σ (V n)) {E L R T : ℝ} (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hE : φ x₀ = E)
    (hLU : ∀ m ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U m) ∧ dist x₀ (U m) ≤ R)
    (hLV : ∀ n ≤ ⌈(T + 1) / (σ : ℝ)⌉₊, (L : EReal) ≤ φ (V n) ∧ dist x₀ (V n) ≤ R)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    bilinInterp τ σ (fun m n ↦ dist (U m) (V n) ^ 2 / 2) t ≤
      exp (4 * |lam| * T) *
        ((E - L) + 8 * |lam| * R * Real.sqrt (2 * (T + 2) * (E - L))) * (τ + σ) := by
  set G := fun m n ↦ dist (U m) (V n) ^ 2 / 2
  let aU := fun m ↦ if m + 1 ≤ ⌈(T + 1) / (τ : ℝ)⌉₊ then
    (φ (U m)).toReal - (φ (U (m + 1))).toReal + 8 * |lam| * R * dist (U m) (U (m + 1)) else 0
  let aV := fun n ↦ if n + 1 ≤ ⌈(T + 1) / (σ : ℝ)⌉₊ then
    (φ (V n)).toReal - (φ (V (n + 1))).toReal + 8 * |lam| * R * dist (V n) (V (n + 1)) else 0
  let ΦU := linInterp τ fun n ↦ (τ : ℝ) * ∑ i ∈ range n, aU i
  let ΦV := linInterp σ fun n ↦ (σ : ℝ) * ∑ i ∈ range n, aV i
  let F : ℝ → ℝ := fun s ↦ exp (2 * lam * s) * bilinInterp τ σ G s -
    exp (2 * |lam| * T) * (ΦU s + ΦV s)
  have hsub : Icc 0 T ⊆ Ici 0 := Icc_subset_Ici_self
  have hF_cont : ContinuousOn F (Icc 0 T) :=
    ((((by fun_prop : Continuous fun s ↦ exp (2 * lam * s)).continuousOn).mul
      ((continuousOn_bilinInterp (NNReal.coe_pos.2 hτ) (NNReal.coe_pos.2 hσ) G).mono hsub)).sub
      (continuousOn_const.mul (((continuousOn_linInterp (NNReal.coe_pos.2 hτ) _).mono hsub).add
        ((continuousOn_linInterp (NNReal.coe_pos.2 hσ) _).mono hsub))))
  have hF0 : F 0 ≤ 0 := by simp [F, ΦU, ΦV, bilinInterp_zero, linInterp_zero, G, hU0, hV0]
  choose f' hf' hf'0 using fun s (hs : s ∈ Ico 0 T) ↦
    exists_hasDerivWithinAt_nonpos_bilinInterp hτ_conv hσ_conv hτ hτ1 hσ hσ1 hU0 hV0 hU hV hR hE
      hLU hLV hs
  have hFt : F t ≤ 0 := by
    have := le_gronwallBound_of_liminf_deriv_right_le (f := F)
      (f' := fun s ↦ if hs : s ∈ Ico 0 T then f' s hs else 0) (δ := 0) (K := 0) (ε := 0) hF_cont
      (fun s hs r hr ↦ (hf' s hs).liminf_right_slope_le (by rwa [dite_eq_left hs] at hr)) hF0
      (fun s hs ↦ by rw [dite_eq_left hs, zero_mul, zero_add]; exact hf'0 s hs) t ht
    simpa only [gronwallBound_ε0_δ0] using this
  obtain ⟨hΦU0, hΦU⟩ := linInterp_sum_bounds (lam := lam) hτ hτ1 hU hT hR (hU0 ▸ hE)
    (fun m hm ↦ (hLU m hm).1) ht
  obtain ⟨hΦV0, hΦV⟩ := linInterp_sum_bounds (lam := lam) hσ hσ1 hV hT hR (hV0 ▸ hE)
    (fun n hn ↦ (hLV n hn).1) ht
  have hexp_neg : exp (-(2 * lam * t)) ≤ exp (2 * |lam| * T) :=
    exp_le_exp.2 (by nlinarith [neg_abs_le lam, abs_nonneg lam, ht.1, ht.2])
  have hmul := mul_le_mul_of_nonneg_left (sub_nonpos.1 hFt) (exp_pos (-(2 * lam * t))).le
  rw [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul] at hmul
  calc bilinInterp τ σ G t ≤ exp (-(2 * lam * t)) * (exp (2 * |lam| * T) * (ΦU t + ΦV t)) := hmul
    _ ≤ exp (2 * |lam| * T) * (exp (2 * |lam| * T) * (ΦU t + ΦV t)) :=
        mul_le_mul_of_nonneg_right hexp_neg (mul_nonneg (exp_pos _).le (add_nonneg hΦU0 hΦV0))
    _ = exp (4 * |lam| * T) * (ΦU t + ΦV t) := by rw [← mul_assoc, ← exp_add]; congr 2; ring
    _ ≤ exp (4 * |lam| * T) *
          ((E - L) + 8 * |lam| * R * Real.sqrt (2 * (T + 2) * (E - L))) * (τ + σ) := by
        have := add_le_add hΦU hΦV
        nlinarith [exp_pos (4 * |lam| * T)]

/-- Single-step squared-distance bound `d(U j, U (j + 1))² ≤ 2 τ (E - L)` from energy decrease. -/
private lemma dist_step_sq_le_mul_sub {τ : ℝ≥0} (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1) {U : ℕ → X}
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n)) {E L T : ℝ} (hE : φ (U 0) = E)
    (hL : ∀ m ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U m)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (U ⌊t / (τ : ℝ)⌋₊) (U (⌊t / (τ : ℝ)⌋₊ + 1)) ^ 2 ≤ 2 * τ * (E - L) := by
  set j := ⌊t / (τ : ℝ)⌋₊
  have hj : j + 1 ≤ ⌈(T + 1) / (τ : ℝ)⌉₊ := floor_div_add_one_le_ceil hτ hτ1 ht.1 ht.2
  have h1 := (apply_add_le_of_mem_moreauYosidaResolvent (hU j)).trans (apply_le_apply_zero hU j)
  rw [hE, coe_edist_sq_div_eq_coe_dist_sq_div hτ] at h1
  have h2 := (add_le_add_left (hL (j + 1) hj) _).trans h1
  rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h2
  rw [← div_le_iff₀' (by positivity : (0 : ℝ) < 2 * τ)]
  linarith

/-- For `0 ≤ x`, the ceiling `⌈x⌉₊` equals either `⌊x⌋₊` or `⌊x⌋₊ + 1`. -/
private lemma ceil_eq_floor_or_add_one {x : ℝ} (hx : 0 ≤ x) :
    ⌈x⌉₊ = ⌊x⌋₊ ∨ ⌈x⌉₊ = ⌊x⌋₊ + 1 := by
  have h1 : ⌊x⌋₊ ≤ ⌈x⌉₊ := Nat.cast_le.1 ((Nat.floor_le hx).trans (Nat.le_ceil x))
  have h2 : ⌈x⌉₊ ≤ ⌊x⌋₊ + 1 := Nat.ceil_le.2 (by exact_mod_cast (Nat.lt_floor_add_one x).le)
  omega

/-- Uniform squared-distance comparison of the piecewise constant interpolants of two minimizing
movement sequences on `[0, T]`. -/
private lemma dist_ceil_sq_le_of_penalizedConvex {τ σ : ℝ≥0} (hτ_conv : PenalizedConvex lam τ φ)
    (hσ_conv : PenalizedConvex lam σ φ) (hτ : 0 < τ) (hτ1 : (τ : ℝ) ≤ 1) (hσ : 0 < σ)
    (hσ1 : (σ : ℝ) ≤ 1) {x₀ : X} {U V : ℕ → X} (hU0 : U 0 = x₀) (hV0 : V 0 = x₀)
    (hU : ∀ n, U (n + 1) ∈ moreauYosidaResolvent φ τ (U n))
    (hV : ∀ n, V (n + 1) ∈ moreauYosidaResolvent φ σ (V n)) {E L R T : ℝ} (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hE : φ x₀ = E)
    (hLU : ∀ m ≤ ⌈(T + 1) / (τ : ℝ)⌉₊, (L : EReal) ≤ φ (U m) ∧ dist x₀ (U m) ≤ R)
    (hLV : ∀ n ≤ ⌈(T + 1) / (σ : ℝ)⌉₊, (L : EReal) ≤ φ (V n) ∧ dist x₀ (V n) ≤ R)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    dist (U ⌈t / (τ : ℝ)⌉₊) (V ⌈t / (σ : ℝ)⌉₊) ^ 2 ≤
      (6 * exp (4 * |lam| * T) *
          ((E - L) + 8 * |lam| * R * Real.sqrt (2 * (T + 2) * (E - L))) +
        6 * (E - L)) * (τ + σ) := by
  have hδ := bilinInterp_dist_sq_le hτ_conv hσ_conv hτ hτ1 hσ hσ1 hU0 hV0 hU hV hT hR hE hLU hLV ht
  set j := ⌊t / (τ : ℝ)⌋₊
  set k := ⌊t / (σ : ℝ)⌋₊
  set p := ⌈t / (τ : ℝ)⌉₊
  set q := ⌈t / (σ : ℝ)⌉₊
  have hp_mem : p = j ∨ p = j + 1 :=
    ceil_eq_floor_or_add_one (div_nonneg ht.1 (NNReal.coe_nonneg τ))
  have hq_mem : q = k ∨ q = k + 1 :=
    ceil_eq_floor_or_add_one (div_nonneg ht.1 (NNReal.coe_nonneg σ))
  have hcorner (m n : ℕ) (hm : m = j ∨ m = j + 1) (hn : n = k ∨ n = k + 1) :
      dist (U p) (V q) ^ 2 ≤ 6 * (dist (U m) (V n) ^ 2 / 2) +
        3 * dist (U j) (U (j + 1)) ^ 2 + 3 * dist (V k) (V (k + 1)) ^ 2 := by
    have hdU : dist (U p) (U m) ≤ dist (U j) (U (j + 1)) := by
      rcases hp_mem with hp | hp <;> rcases hm with rfl | rfl <;> simp [hp, dist_comm]
    have hdV : dist (V n) (V q) ≤ dist (V k) (V (k + 1)) := by
      rcases hq_mem with hq | hq <;> rcases hn with rfl | rfl <;> simp [hq, dist_comm]
    have htri : dist (U p) (V q) ≤ dist (U m) (V n) + dist (U j) (U (j + 1)) +
        dist (V k) (V (k + 1)) := by
      linarith [dist_triangle (U p) (U m) (V q), dist_triangle (U m) (V n) (V q)]
    nlinarith [dist_nonneg (x := U p) (y := V q),
      sq_nonneg (dist (U m) (V n) - dist (U j) (U (j + 1))),
      sq_nonneg (dist (U m) (V n) - dist (V k) (V (k + 1))),
      sq_nonneg (dist (U j) (U (j + 1)) - dist (V k) (V (k + 1)))]
  have hstepU := dist_step_sq_le_mul_sub hτ hτ1 hU (hU0 ▸ hE) (fun m hm ↦ (hLU m hm).1) ht
  have hstepV := dist_step_sq_le_mul_sub hσ hσ1 hV (hV0 ▸ hE) (fun n hn ↦ (hLV n hn).1) ht
  set α := t / τ - (j : ℝ)
  set β := t / σ - (k : ℝ)
  have hα0 : 0 ≤ α := sub_nonneg.2 (Nat.floor_le (div_nonneg ht.1 (NNReal.coe_nonneg τ)))
  have hα1 : 0 ≤ 1 - α := sub_nonneg.2 (sub_le_iff_le_add'.2 (Nat.lt_floor_add_one _).le)
  have hβ0 : 0 ≤ β := sub_nonneg.2 (Nat.floor_le (div_nonneg ht.1 (NNReal.coe_nonneg σ)))
  have hβ1 : 0 ≤ 1 - β := sub_nonneg.2 (sub_le_iff_le_add'.2 (Nat.lt_floor_add_one _).le)
  have hbilin : bilinInterp τ σ (fun m n ↦ dist (U m) (V n) ^ 2 / 2) t =
      (1 - α) * (1 - β) * (dist (U j) (V k) ^ 2 / 2) +
        (1 - α) * β * (dist (U j) (V (k + 1)) ^ 2 / 2) +
        α * (1 - β) * (dist (U (j + 1)) (V k) ^ 2 / 2) +
        α * β * (dist (U (j + 1)) (V (k + 1)) ^ 2 / 2) := by
    simp only [bilinInterp, linInterp, j, k, α, β]; ring
  have hcomb : dist (U p) (V q) ^ 2 ≤
      6 * bilinInterp τ σ (fun m n ↦ dist (U m) (V n) ^ 2 / 2) t +
        3 * dist (U j) (U (j + 1)) ^ 2 + 3 * dist (V k) (V (k + 1)) ^ 2 := by
    rw [hbilin]
    nlinarith [mul_le_mul_of_nonneg_left (hcorner j k (.inl rfl) (.inl rfl)) (mul_nonneg hα1 hβ1),
      mul_le_mul_of_nonneg_left (hcorner j (k + 1) (.inl rfl) (.inr rfl)) (mul_nonneg hα1 hβ0),
      mul_le_mul_of_nonneg_left (hcorner (j + 1) k (.inr rfl) (.inl rfl)) (mul_nonneg hα0 hβ1),
      mul_le_mul_of_nonneg_left (hcorner (j + 1) (k + 1) (.inr rfl) (.inr rfl))
        (mul_nonneg hα0 hβ0)]
  nlinarith

end TwoChainComparison

/-! ### Discrete-to-continuous exponential limits -/

section DiscreteExponentialLimits

private lemma tendsto_ceil_div_mul {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k)
    (hσ0 : Tendsto σ atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun k ↦ (⌈t / (σ k : ℝ)⌉₊ : ℝ) * σ k) atTop (𝓝 t) := by
  have hσr : Tendsto (fun k ↦ (σ k : ℝ)) atTop (𝓝 0) :=
    (NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hσ0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hσr.const_add t) (fun k ↦ ?_) (fun k ↦ ?_)
  · exact (div_le_iff₀ (NNReal.coe_pos.2 (hσ k))).1 (Nat.le_ceil _)
  · calc (⌈t / (σ k : ℝ)⌉₊ : ℝ) * (σ k : ℝ)
        ≤ (t / (σ k : ℝ) + 1) * (σ k : ℝ) :=
          mul_le_mul_of_nonneg_right
            (Nat.ceil_lt_add_one (div_nonneg ht (NNReal.coe_nonneg (σ k)))).le
            (NNReal.coe_nonneg (σ k))
      _ = t + (σ k : ℝ) := by
          have := (NNReal.coe_pos.2 (hσ k)).ne'
          field_simp

private lemma tendsto_one_add_mul_pow {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k)
    (hσ0 : Tendsto σ atTop (𝓝 0)) {N : ℕ → ℕ} {d : ℝ}
    (hN : Tendsto (fun k ↦ (N k : ℝ) * σ k) atTop (𝓝 d)) (lam : ℝ) :
    Tendsto (fun k ↦ (1 + lam * σ k) ^ N k) atTop (𝓝 (exp (lam * d))) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simp
  have hσr : Tendsto (fun k ↦ (σ k : ℝ)) atTop (𝓝 0) :=
    (NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hσ0
  have hne : ∀ k, lam * (σ k : ℝ) ≠ 0 :=
    fun k ↦ mul_ne_zero hlam (NNReal.coe_pos.2 (hσ k)).ne'
  have hu : Tendsto (fun k ↦ lam * (σ k : ℝ)) atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using hσr.const_mul lam) (Eventually.of_forall hne)
  have hslope : Tendsto (fun x : ℝ ↦ x⁻¹ * Real.log (1 + x)) (𝓝[≠] 0) (𝓝 1) := by
    simpa using (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero
  have hprod : Tendsto (fun k ↦ (lam * ((N k : ℝ) * σ k)) *
      ((lam * σ k)⁻¹ * Real.log (1 + lam * σ k))) atTop (𝓝 ((lam * d) * 1)) :=
    (hN.const_mul lam).mul (hslope.comp hu)
  rw [mul_one] at hprod
  have hprod' : Tendsto (fun k ↦ (N k : ℝ) * Real.log (1 + lam * σ k)) atTop (𝓝 (lam * d)) :=
    hprod.congr fun k ↦ by
      have := (NNReal.coe_pos.2 (hσ k)).ne'
      field_simp
  refine ((Real.continuous_exp.tendsto (lam * d)).comp hprod').congr' ?_
  filter_upwards [(by simpa using (hσr.const_mul lam).const_add 1 :
      Tendsto (fun k ↦ 1 + lam * (σ k : ℝ)) atTop (𝓝 1)).eventually
      (Ioi_mem_nhds (one_pos : (0 : ℝ) < 1))]
    with k hk
  dsimp only [Function.comp_apply]
  rw [Real.exp_nat_mul, Real.exp_log hk]

private lemma tendsto_mul_sum_one_add_mul_pow {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k)
    (hσ0 : Tendsto σ atTop (𝓝 0)) {N : ℕ → ℕ} {d : ℝ}
    (hN : Tendsto (fun k ↦ (N k : ℝ) * σ k) atTop (𝓝 d)) (lam : ℝ) :
    Tendsto (fun k ↦ (σ k : ℝ) * ∑ n ∈ range (N k), (1 + lam * σ k) ^ n) atTop
      (𝓝 (∫ r in 0..d, exp (lam * r))) := by
  rcases eq_or_ne lam 0 with rfl | hlam
  · simpa [mul_comm] using hN
  have hpow := tendsto_one_add_mul_pow hσ hσ0 hN lam
  have hint : ∫ r in 0..d, exp (lam * r) = (exp (lam * d) - 1) / lam := by
    rw [intervalIntegral.integral_comp_mul_left (fun r ↦ exp r) hlam, integral_exp]
    simp [div_eq_inv_mul]
  rw [hint]
  refine ((hpow.sub_const 1).div_const lam).congr fun k ↦ ?_
  have hσk : (σ k : ℝ) ≠ 0 := (NNReal.coe_pos.2 (hσ k)).ne'
  have h1 : (1 : ℝ) + lam * σ k ≠ 1 := fun h ↦ mul_ne_zero hlam hσk (by linarith)
  have hsub : (1 : ℝ) + lam * σ k - 1 = lam * σ k := by ring
  rw [geom_sum_eq h1, hsub]
  field_simp

end DiscreteExponentialLimits

/-! ### Passage to the `EVI_λ` limit and domain identification -/

section Convergence

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal}

/-- On a pseudometric space, coercivity `φ_{τ₀}(x₁) > -∞` rules out the value `⊥` everywhere. -/
private lemma apply_ne_bot_of_moreauYosida_ne_bot {τ₀ : ℝ≥0} {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (z : X) : φ z ≠ ⊥ := fun hz ↦
  h₀ <| le_bot_iff.1 <| by simpa [hz] using moreauYosida_le φ τ₀ (edist_ne_top x₁ z)

/-- Passing the discrete Hölder estimate to a pointwise limit of minimizing movements gives a
local `1/2`-Hölder bound on `[0, ∞)`. -/
private lemma dist_sq_le_of_tendsto_ceil {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ x₀ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤) {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k)
    (hσ0 : Tendsto σ atTop (𝓝 0)) {V : ℕ → ℕ → X} (hV0 : ∀ k, V k 0 = x₀)
    (hV : ∀ k n, V k (n + 1) ∈ moreauYosidaResolvent φ (σ k) (V k n)) {u : ℝ → X}
    (hlim : ∀ t ≥ 0, Tendsto (fun k ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (𝓝 (u t))) :
    ∃ K ≥ 0, ∀ ⦃s t : ℝ⦄, 0 ≤ s → s ≤ t →
      dist (u s) (u t) ^ 2 ≤ (t - s) * K * (1 + exp (8 * t / (τ₀ / 2 : ℝ≥0))) := by
  set τ' : ℝ≥0 := τ₀ / 2
  have hbot := apply_ne_bot_of_moreauYosida_ne_bot h₀
  have hAbot : moreauYosida φ τ' x₀ ≠ ⊥ :=
    moreauYosida_ne_bot_of_lt (half_lt_self hτ₀) (edist_ne_top x₀ x₁) h₀
  have hAtop : moreauYosida φ τ' x₀ ≠ ⊤ :=
    ne_top_of_le_ne_top hx₀ (moreauYosida_le_self φ τ' x₀)
  set A := (moreauYosida φ τ' x₀).toReal
  set E := (φ x₀).toReal
  have hA : moreauYosida φ τ' x₀ = A := (EReal.coe_toReal hAtop hAbot).symm
  have hE : φ x₀ = E := (EReal.coe_toReal hx₀ (hbot x₀)).symm
  have hAE : 0 ≤ E - A := sub_nonneg.2 (EReal.coe_le_coe_iff.1
    (hA ▸ hE ▸ moreauYosida_le_self φ τ' x₀))
  refine ⟨2 * (E - A), by positivity, fun s t hs hst ↦ ?_⟩
  have hσr : Tendsto (fun k ↦ (σ k : ℝ)) atTop (𝓝 0) :=
    (NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hσ0
  have hrhs : Tendsto (fun k ↦ (t - s + (σ k : ℝ)) * (2 * (E - A)) *
      (1 + exp (8 * (t + (σ k : ℝ)) / (τ' : ℝ)))) atTop
      (𝓝 ((t - s) * (2 * (E - A)) * (1 + exp (8 * t / (τ₀ / 2 : ℝ≥0))))) := by
    simpa only [add_zero, Function.comp_def, τ'] using
      (((hσr.const_add (t - s)).mul_const (2 * (E - A))).mul
        (tendsto_const_nhds.add
          ((Real.continuous_exp.tendsto _).comp (((hσr.const_add t).const_mul 8).div_const τ'))))
  refine le_of_tendsto_of_tendsto (((hlim s hs).dist (hlim t (hs.trans hst))).pow 2) hrhs ?_
  filter_upwards [hσ0.eventually (Iic_mem_nhds (by positivity : (0 : ℝ≥0) < τ' / 4))] with k hk
  have hed := edist_ceil_sq_le_of_forall_mem_moreauYosidaResolvent (hV k) (hσ k)
    (by exact_mod_cast (le_div_iff₀' (by norm_num : (0 : ℝ≥0) < 4)).1 hk)
    (hV0 k ▸ hA) (hV0 k ▸ hE) hs hst
  rw [edist_dist, ← ENNReal.ofReal_pow dist_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hed
  exact hed.trans_eq (by ring)

/-- Passing the discrete Hölder estimate to a pointwise limit of minimizing movements gives
continuity of the limit curve on `[0, ∞)`. -/
private lemma continuousOn_of_tendsto_ceil {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ x₀ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤) {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k)
    (hσ0 : Tendsto σ atTop (𝓝 0)) {V : ℕ → ℕ → X} (hV0 : ∀ k, V k 0 = x₀)
    (hV : ∀ k n, V k (n + 1) ∈ moreauYosidaResolvent φ (σ k) (V k n)) {u : ℝ → X}
    (hlim : ∀ t ≥ 0, Tendsto (fun k ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (𝓝 (u t))) :
    ContinuousOn u (Ici 0) := by
  obtain ⟨K, hK0, hholder⟩ := dist_sq_le_of_tendsto_ceil hτ₀ h₀ hx₀ hσ hσ0 hV0 hV hlim
  set τ' : ℝ≥0 := τ₀ / 2
  refine Metric.continuousOn_iff.2 fun t₀ (ht₀ : 0 ≤ t₀) ε hε ↦ ?_
  set C := K * (1 + exp (8 * (t₀ + 1) / τ')) + 1
  have hC : 0 < C := by positivity
  refine ⟨min 1 (ε ^ 2 / C), by positivity, fun t (ht : 0 ≤ t) hdist ↦ ?_⟩
  have hd1 : |t - t₀| < 1 := (Real.dist_eq t t₀ ▸ hdist).trans_le (min_le_left _ _)
  have hdC : |t - t₀| < ε ^ 2 / C := (Real.dist_eq t t₀ ▸ hdist).trans_le (min_le_right _ _)
  have hsq : dist (u t) (u t₀) ^ 2 < ε ^ 2 := by
    rcases le_total t t₀ with htt₀ | ht₀t
    · have hexp : exp (8 * t₀ / τ') ≤ exp (8 * (t₀ + 1) / τ') :=
        exp_le_exp.2 (by gcongr; linarith)
      have habs : |t - t₀| = t₀ - t := by rw [abs_of_nonpos (by linarith)]; ring
      calc dist (u t) (u t₀) ^ 2 ≤ (t₀ - t) * K * (1 + exp (8 * t₀ / τ')) := hholder ht htt₀
        _ ≤ |t - t₀| * C := by
            rw [habs]; dsimp [C]
            nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg (sub_nonneg.2 htt₀) hK0)]
        _ < ε ^ 2 := (lt_div_iff₀ hC).1 hdC
    · have hexp : exp (8 * t / τ') ≤ exp (8 * (t₀ + 1) / τ') :=
        exp_le_exp.2 (by gcongr; linarith [(abs_lt.1 hd1).2])
      have habs : |t - t₀| = t - t₀ := abs_of_nonneg (by linarith)
      rw [dist_comm]
      calc dist (u t₀) (u t) ^ 2 ≤ (t - t₀) * K * (1 + exp (8 * t / τ')) := hholder ht₀ ht₀t
        _ ≤ |t - t₀| * C := by
            rw [habs]; dsimp [C]
            nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg (sub_nonneg.2 ht₀t) hK0)]
        _ < ε ^ 2 := (lt_div_iff₀ hC).1 hdC
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hsq

/-- Integrated regularization estimate passed to the limit along minimizing movements. -/
private lemma apply_le_of_tendsto_ceil
    (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ) (hφ : LowerSemicontinuous φ)
    (hbot : ∀ x, φ x ≠ ⊥) {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k) (hσ0 : Tendsto σ atTop (𝓝 0))
    {V : ℕ → ℕ → X} (hV : ∀ k n, V k (n + 1) ∈ moreauYosidaResolvent φ (σ k) (V k n))
    {u : ℝ → X} (hlim : ∀ t ≥ 0, Tendsto (fun k ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (𝓝 (u t)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal) := by
  have hσ_gt : Tendsto σ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσ0 (Eventually.of_forall hσ)
  have hσr : Tendsto (fun k ↦ (σ k : ℝ)) atTop (𝓝 0) :=
    (NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hσ0
  lift φ y to ℝ using ⟨hy, hbot y⟩ with q hq
  set N : ℕ → ℕ := fun k ↦ ⌈t / (σ k : ℝ)⌉₊ - ⌈s / (σ k : ℝ)⌉₊
  have hN_lim : Tendsto (fun k ↦ (N k : ℝ) * σ k) atTop (𝓝 (t - s)) :=
    ((tendsto_ceil_div_mul hσ hσ0 (hs.trans hst.le)).sub (tendsto_ceil_div_mul hσ hσ0 hs)).congr
      fun k ↦ by
        rw [← sub_mul, ← Nat.cast_sub
          (Nat.ceil_mono (div_le_div_of_nonneg_right hst.le (NNReal.coe_nonneg (σ k))))]
  have hpow := tendsto_one_add_mul_pow hσ hσ0 hN_lim lam
  have hsum := tendsto_mul_sum_one_add_mul_pow hσ hσ0 hN_lim lam
  have hEpos := integral_exp_mul_pos lam (sub_pos.2 hst)
  let c : ℕ → ℝ := fun k ↦
    (dist (V k ⌈s / (σ k : ℝ)⌉₊) y ^ 2 -
      (1 + lam * σ k) ^ N k * dist (V k ⌈t / (σ k : ℝ)⌉₊) y ^ 2) /
      (2 * ((σ k : ℝ) * ∑ n ∈ range (N k), (1 + lam * σ k) ^ n))
  have hc_lim : Tendsto (fun k ↦ ((q + c k : ℝ) : EReal)) atTop (𝓝 (((q +
      (dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
        (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 <| tendsto_const_nhds.add <|
      ((((hlim s hs).dist tendsto_const_nhds).pow 2).sub
        (hpow.mul (((hlim t (hs.trans hst.le)).dist tendsto_const_nhds).pow 2))).div
        (hsum.const_mul 2) (by positivity)
  rw [← EReal.coe_add, ← hc_lim.liminf_eq]
  refine ((hφ.le_liminf (u t)).trans
    ((hlim t (hs.trans hst.le)).liminf_le_liminf_comp (u := φ))).trans (liminf_le_liminf ?_)
  filter_upwards [hσ_gt.eventually hconv,
    ((by simpa using (hσr.const_mul lam).const_add 1 :
      Tendsto (fun k ↦ 1 + lam * (σ k : ℝ)) atTop (𝓝 1))).eventually
      (Ioi_mem_nhds (one_pos : (0 : ℝ) < 1)),
    hN_lim.eventually (Ioi_mem_nhds (sub_pos.2 hst))] with k hk_conv hlamk hNk
  have hN_pos : 0 < N k := by
    by_contra h0; simp [Nat.eq_zero_of_not_pos h0] at hNk
  have hle := Nat.ceil_mono (div_le_div_of_nonneg_right hst.le (NNReal.coe_nonneg (σ k)))
  have hWk : ∀ n, V k (⌈s / (σ k : ℝ)⌉₊ + (n + 1)) ∈
      moreauYosidaResolvent φ (σ k) (V k (⌈s / (σ k : ℝ)⌉₊ + n)) :=
    fun n ↦ by simpa only [add_assoc] using hV k (⌈s / (σ k : ℝ)⌉₊ + n)
  have hd := hk_conv.apply_le (hσ k) (le_of_lt hlamk) hWk (hq ▸ EReal.coe_ne_top q) hN_pos
  simpa only [Function.comp_apply, add_zero, N, Nat.add_sub_of_le hle, ← hq, EReal.coe_add, c,
    mul_assoc] using hd

/-- A pointwise limit of minimizing movements under penalized convexity is an `EVI_λ` solution. -/
private lemma isEVISolution_of_tendsto_ceil
    (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤)
    {σ : ℕ → ℝ≥0} (hσ : ∀ k, 0 < σ k) (hσ0 : Tendsto σ atTop (𝓝 0)) {V : ℕ → ℕ → X}
    (hV0 : ∀ k, V k 0 = x₀)
    (hV : ∀ k n, V k (n + 1) ∈ moreauYosidaResolvent φ (σ k) (V k n)) {u : ℝ → X}
    (hlim : ∀ t ≥ 0, Tendsto (fun k ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (𝓝 (u t))) :
    IsEVISolution lam φ u := by
  have hbot := apply_ne_bot_of_moreauYosida_ne_bot h₀
  have hu_cont := continuousOn_of_tendsto_ceil hτ₀ h₀ hx₀ hσ hσ0 hV0 hV hlim
  have hreg : ∀ y, φ y ≠ ⊤ → ∀ s t : ℝ, 0 ≤ s → s < t →
      φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
        (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal) :=
    fun _ hy _ _ hs hst ↦ apply_le_of_tendsto_ceil hconv hφ hbot hσ hσ0 hV hlim hy hs hst
  have htop : ∀ t > 0, φ (u t) ≠ ⊤ := fun t ht ↦
    ne_top_of_le_ne_top (EReal.add_ne_top hx₀ (EReal.coe_ne_top _)) (hreg x₀ hx₀ 0 t le_rfl ht)
  exact (isEVISolution_iff_apply_le hφ).2 ⟨hu_cont, htop, fun t _ ↦ hbot (u t), hreg⟩

/-- Uniform Cauchy property on `[0, T]` of a minimizing movement family along time steps tending
to `0`. -/
private lemma uniformCauchySeqOn_ceil_of_penalizedConvex
    (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀)
    {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤) {σ : ℕ → ℝ≥0}
    (hσ : ∀ k, 0 < σ k) (hσ0 : Tendsto σ atTop (𝓝 0)) {V : ℕ → ℕ → X} (hV0 : ∀ k, V k 0 = x₀)
    (hV : ∀ k n, V k (n + 1) ∈ moreauYosidaResolvent φ (σ k) (V k n)) {T : ℝ} (hT : 0 ≤ T) :
    UniformCauchySeqOn (fun k (t : ℝ) ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (Icc 0 T) := by
  have hbot := apply_ne_bot_of_moreauYosida_ne_bot h₀
  set E := (φ x₀).toReal
  have hE : φ x₀ = E := (EReal.coe_toReal hx₀ (hbot x₀)).symm
  obtain ⟨L, R', hR'top, hev⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hτ₀ h₀
      (edist_ne_top x₀ x₁) hσ hσ0 hV (by simpa only [hV0] using tendsto_const_nhds)
      (S := E) (fun k ↦ by rw [hV0 k, hE]) (by linarith : 0 ≤ T + 1)
  set R := R'.toReal
  have hL : ∀ᶠ k in atTop, ∀ n ≤ ⌈(T + 1) / (σ k : ℝ)⌉₊,
      (L : EReal) ≤ φ (V k n) ∧ dist x₀ (V k n) ≤ R := by
    filter_upwards [hev] with k hk n hn
    exact ⟨(hk n hn).1, dist_edist x₀ (V k n) ▸
      (ENNReal.toReal_le_toReal (edist_ne_top _ _) hR'top).2 (hk n hn).2⟩
  set K := 6 * exp (4 * |lam| * T) *
      ((E - L) + 8 * |lam| * R * Real.sqrt (2 * (T + 2) * (E - L))) + 6 * (E - L)
  have hσ_gt : Tendsto σ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσ0 (Eventually.of_forall hσ)
  have hσr : Tendsto (fun k ↦ (σ k : ℝ)) atTop (𝓝 0) :=
    (NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hσ0
  refine Metric.uniformCauchySeqOn_iff.2 fun ε hε ↦ ?_
  have hδ : 0 < ε ^ 2 / (2 * (|K| + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((hσ_gt.eventually hconv).and <| (hσ0.eventually (Iio_mem_nhds (one_pos : (0 : ℝ≥0) < 1))).and
      <| hL.and (hσr.eventually (Iio_mem_nhds hδ)))
  refine ⟨N, fun j hj k hk t ht ↦ ?_⟩
  obtain ⟨hj_conv, hj1, hjL, hjδ⟩ := hN j hj
  obtain ⟨hk_conv, hk1, hkL, hkδ⟩ := hN k hk
  have hsq := dist_ceil_sq_le_of_penalizedConvex hj_conv hk_conv (hσ j)
    (NNReal.coe_le_one.2 (le_of_lt hj1)) (hσ k) (NNReal.coe_le_one.2 (le_of_lt hk1)) (hV0 j)
    (hV0 k) (hV j) (hV k) hT ENNReal.toReal_nonneg hE hjL hkL ht
  have hlt : dist (V j ⌈t / (σ j : ℝ)⌉₊) (V k ⌈t / (σ k : ℝ)⌉₊) ^ 2 < ε ^ 2 := by
    have hK : K * ((σ j : ℝ) + σ k) ≤ (|K| + 1) * ((σ j : ℝ) + σ k) :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self K]) (by positivity)
    have hsum : (|K| + 1) * ((σ j : ℝ) + σ k) < ε ^ 2 := by
      have := mul_lt_mul_of_pos_left (add_lt_add (show (σ j : ℝ) < _ from hjδ) hkδ)
        (by positivity : 0 < |K| + 1)
      field_simp at this
      linarith
    exact (hsq.trans hK).trans_lt hsum
  exact (pow_lt_pow_iff_left₀ dist_nonneg hε.le two_ne_zero).1 hlt

/-- Any family of minimizing movement chains from `x₀` tracks the canonical family uniformly on
`[0, T]`. -/
private lemma tendstoUniformlyOn_of_tendstoUniformlyOn_canonical
    (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀)
    {x₁ x₀ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (hx₀ : φ x₀ ≠ ⊤) {σ τ : ℕ → ℝ≥0}
    (hσ : ∀ j, 0 < σ j) (hσ0 : Tendsto σ atTop (𝓝 0)) (hτ : ∀ j, 0 < τ j)
    (hτ0 : Tendsto τ atTop (𝓝 0)) {V J : ℕ → ℕ → X} (hV0 : ∀ j, V j 0 = x₀)
    (hV : ∀ j k, V j (k + 1) ∈ moreauYosidaResolvent φ (σ j) (V j k)) (hJ0 : ∀ j, J j 0 = x₀)
    (hJ : ∀ j k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) {u : ℝ → X} (T : ℝ)
    (hu : TendstoUniformlyOn (fun j (t : ℝ) ↦ V j ⌈t / (σ j : ℝ)⌉₊) u atTop (Icc 0 T)) :
    TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Icc_eq_empty_of_lt hT, Metric.tendstoUniformlyOn_iff]
  have hbot := apply_ne_bot_of_moreauYosida_ne_bot h₀
  set E := (φ x₀).toReal
  have hE : φ x₀ = E := (EReal.coe_toReal hx₀ (hbot x₀)).symm
  obtain ⟨LU, RU', hRU'top, hevU⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hτ₀ h₀
      (edist_ne_top x₀ x₁) hτ hτ0 hJ (by simpa only [hJ0] using tendsto_const_nhds)
      (S := E) (fun j ↦ by rw [hJ0 j, hE]) (by linarith : 0 ≤ T + 1)
  obtain ⟨LV, RV', hRV'top, hevV⟩ :=
    exists_eventually_forall_le_apply_and_edist_le_of_forall_mem_moreauYosidaResolvent hτ₀ h₀
      (edist_ne_top x₀ x₁) hσ hσ0 hV (by simpa only [hV0] using tendsto_const_nhds)
      (S := E) (fun j ↦ by rw [hV0 j, hE]) (by linarith : 0 ≤ T + 1)
  set L := min LU LV
  set R := max RU'.toReal RV'.toReal
  have hR : 0 ≤ R := ENNReal.toReal_nonneg.trans (le_max_left _ _)
  set K := 6 * exp (4 * |lam| * T) *
      ((E - L) + 8 * |lam| * R * Real.sqrt (2 * (T + 2) * (E - L))) + 6 * (E - L)
  have hτ_gt : Tendsto τ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hτ0 (Eventually.of_forall hτ)
  have hσ_gt : Tendsto σ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hσ0 (Eventually.of_forall hσ)
  have hsum0 : Tendsto (fun j ↦ (τ j : ℝ) + σ j) atTop (𝓝 0) := by
    simpa using (((NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hτ0).add
      ((NNReal.continuous_coe.tendsto' 0 0 NNReal.coe_zero).comp hσ0))
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu (ε / 2) (half_pos hε),
    hτ_gt.eventually hconv, hσ_gt.eventually hconv,
    hτ0.eventually (Iio_mem_nhds (one_pos : (0 : ℝ≥0) < 1)),
    hσ0.eventually (Iio_mem_nhds (one_pos : (0 : ℝ≥0) < 1)), hevU, hevV,
    hsum0.eventually (Iio_mem_nhds (by positivity : 0 < (ε / 2) ^ 2 / (|K| + 1)))]
    with j huj hjτ_conv hjσ_conv hjτ1 hjσ1 hjU hjV hjδ t ht
  have hjLU : ∀ m ≤ ⌈(T + 1) / (τ j : ℝ)⌉₊, (L : EReal) ≤ φ (J j m) ∧ dist x₀ (J j m) ≤ R :=
    fun m hm ↦ ⟨(EReal.coe_le_coe_iff.2 (min_le_left _ _)).trans (hjU m hm).1,
      (dist_edist x₀ (J j m) ▸ (ENNReal.toReal_le_toReal (edist_ne_top _ _) hRU'top).2
        (hjU m hm).2).trans (le_max_left _ _)⟩
  have hjLV : ∀ n ≤ ⌈(T + 1) / (σ j : ℝ)⌉₊, (L : EReal) ≤ φ (V j n) ∧ dist x₀ (V j n) ≤ R :=
    fun n hn ↦ ⟨(EReal.coe_le_coe_iff.2 (min_le_right _ _)).trans (hjV n hn).1,
      (dist_edist x₀ (V j n) ▸ (ENNReal.toReal_le_toReal (edist_ne_top _ _) hRV'top).2
        (hjV n hn).2).trans (le_max_right _ _)⟩
  have hsq := dist_ceil_sq_le_of_penalizedConvex hjτ_conv hjσ_conv (hτ j)
    (NNReal.coe_le_one.2 (le_of_lt hjτ1)) (hσ j) (NNReal.coe_le_one.2 (le_of_lt hjσ1)) (hJ0 j)
    (hV0 j) (hJ j) (hV j) hT hR hE hjLU hjLV ht
  have hJV : dist (J j ⌈t / (τ j : ℝ)⌉₊) (V j ⌈t / (σ j : ℝ)⌉₊) < ε / 2 :=
    (pow_lt_pow_iff_left₀ dist_nonneg (half_pos hε).le two_ne_zero).1 <|
      (hsq.trans (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K])
        (by positivity))).trans_lt ((lt_div_iff₀' (by positivity : 0 < |K| + 1)).1 hjδ)
  linarith [dist_triangle (u t) (V j ⌈t / (σ j : ℝ)⌉₊) (J j ⌈t / (τ j : ℝ)⌉₊),
    dist_comm (J j ⌈t / (τ j : ℝ)⌉₊) (V j ⌈t / (σ j : ℝ)⌉₊), huj t ht]

private lemma one_add_mul_pos_of_le (lam : ℝ) {τ : ℝ≥0} (hτ : τ ≤ 1 / (2 * (⌈|lam|⌉₊ + 1))) :
    0 < 1 + lam * τ := by
  have h1 : (τ : ℝ) ≤ 1 / (2 * ((⌈|lam|⌉₊ : ℝ) + 1)) := by exact_mod_cast hτ
  have h2 : |lam * (τ : ℝ)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg τ)]
    calc |lam| * (τ : ℝ) ≤ ((⌈|lam|⌉₊ : ℝ) + 1) * (τ : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith [Nat.le_ceil |lam|]) (NNReal.coe_nonneg τ)
      _ ≤ ((⌈|lam|⌉₊ : ℝ) + 1) * (1 / (2 * ((⌈|lam|⌉₊ : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 / 2 := by field_simp
  linarith [neg_abs_le (lam * (τ : ℝ))]

/-- Existence of a canonical sequence of time steps `σ k → 0` and minimizing movement sequences
from `x₀` under penalized convexity and coercivity. -/
private lemma exists_canonical_moreauYosidaResolvent [CompleteSpace X]
    (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) (x₀ : X) :
    ∃ (σ : ℕ → ℝ≥0) (V : ℕ → ℕ → X), (∀ k, 0 < σ k) ∧ Tendsto σ atTop (𝓝 0) ∧
      (∀ k, V k 0 = x₀) ∧ ∀ k n, V k (n + 1) ∈ moreauYosidaResolvent φ (σ k) (V k n) := by
  obtain ⟨s, hs0, hs_conv⟩ := Metric.mem_nhdsWithin_iff.1 hconv
  set r : ℝ≥0 := min (τ₀ / 2) (min (Real.toNNReal (s / 2)) (1 / (2 * (⌈|lam|⌉₊ + 1))))
  have hr : 0 < r := lt_min (half_pos hτ₀)
    (lt_min (Real.toNNReal_pos.2 (half_pos hs0)) (by positivity))
  let σ : ℕ → ℝ≥0 := fun k ↦ r / (k + 1)
  have hσ : ∀ k, 0 < σ k := fun k ↦ div_pos hr (by positivity)
  have hσ0 : Tendsto σ atTop (𝓝 0) := NNReal.tendsto_coe.1 <| by
    simpa [σ, div_eq_mul_inv] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r : ℝ)
  have hσ_le_r : ∀ k, σ k ≤ r :=
    fun k ↦ div_le_self (NNReal.coe_nonneg r) (by exact_mod_cast Nat.succ_pos k)
  have hσ_conv : ∀ k, PenalizedConvex lam (σ k) φ := fun k ↦ hs_conv ⟨by
    rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg (σ k))]
    have h1 : (σ k : ℝ) ≤ Real.toNNReal (s / 2) := NNReal.coe_le_coe.2
      ((hσ_le_r k).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [Real.coe_toNNReal _ (half_pos hs0).le] at h1
    linarith, hσ k⟩
  have hσ_lam : ∀ k, 0 < 1 + lam * σ k := fun k ↦
    one_add_mul_pos_of_le lam ((hσ_le_r k).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hσ_coer : ∀ k z, moreauYosida φ (σ k) z ≠ ⊥ := fun k z ↦
    moreauYosida_ne_bot_of_lt
      ((hσ_le_r k).trans_lt ((min_le_left _ _).trans_lt (half_lt_self hτ₀)))
      (edist_ne_top z x₁) h₀
  choose V hV0 hV using fun k ↦
    (hσ_conv k).exists_forall_mem_moreauYosidaResolvent hφ (hσ_lam k) (hσ_coer k) x₀
  exact ⟨σ, V, hσ, hσ0, hV0, hV⟩

/-- **Convergence of minimizing movements to the `EVI_λ` flow** (Ambrosio–Gigli–Savaré, Theorem
4.0.4). Let `φ` be a lower semicontinuous energy on a complete pseudometric space `X` satisfying
`TauCeti.PenalizedConvex lam τ φ` for all sufficiently small `τ > 0` and `φ_{τ₀}(x₁) > -∞` for some
`τ₀ > 0` and `x₁ : X`. Then from every `x₀` with `φ x₀ ≠ ⊤` there starts an `EVI_λ` solution `u`
with `u 0 = x₀`, and the piecewise constant interpolants `t ↦ J j ⌈t / τ j⌉₊` of every family of
minimizing movement sequences from `x₀` with time steps `τ j → 0` converge to `u` uniformly on
every interval `[0, T]`. -/
theorem exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent_of_penalizedConvex
    [CompleteSpace X] (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ)
    (hφ : LowerSemicontinuous φ) {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X}
    (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) → (∀ j, J j 0 = x₀) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  obtain ⟨σ, V, hσ, hσ0, hV0, hV⟩ :=
    exists_canonical_moreauYosidaResolvent hconv hφ hτ₀ h₀ x₀
  have hCauchy : ∀ T ≥ 0,
      UniformCauchySeqOn (fun k (t : ℝ) ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (Icc 0 T) := fun T hT ↦
    uniformCauchySeqOn_ceil_of_penalizedConvex hconv hτ₀ h₀ hx₀ hσ hσ0 hV0 hV hT
  classical
  let u : ℝ → X := fun t ↦ if ht : 0 < t then
    (cauchySeq_tendsto_of_complete ((hCauchy t ht.le).cauchySeq ⟨ht.le, le_rfl⟩)).choose else x₀
  have hu0 : u 0 = x₀ := dite_eq_right (lt_irrefl 0)
  have hlim : ∀ t ≥ 0, Tendsto (fun k ↦ V k ⌈t / (σ k : ℝ)⌉₊) atTop (𝓝 (u t)) := fun t ht ↦ by
    rcases ht.eq_or_lt with rfl | ht_pos
    · simpa only [zero_div, Nat.ceil_zero, hV0, hu0] using tendsto_const_nhds
    · dsimp only [u]
      rw [dite_eq_left ht_pos]
      exact (cauchySeq_tendsto_of_complete
        ((hCauchy t ht_pos.le).cauchySeq ⟨ht_pos.le, le_rfl⟩)).choose_spec
  have huV : ∀ T : ℝ,
      TendstoUniformlyOn (fun k (t : ℝ) ↦ V k ⌈t / (σ k : ℝ)⌉₊) u atTop (Icc 0 T) := fun T ↦ by
    rcases lt_or_ge T 0 with hT | hT
    · simp [Icc_eq_empty_of_lt hT, Metric.tendstoUniformlyOn_iff]
    · exact (hCauchy T hT).tendstoUniformlyOn_of_tendsto fun t ht ↦ hlim t ht.1
  refine ⟨u, hu0, isEVISolution_of_tendsto_ceil hconv hφ hτ₀ h₀ hx₀ hσ hσ0 hV0 hV hlim,
    fun τ J hτ hτ0 hJ0 hJ T ↦ ?_⟩
  exact tendstoUniformlyOn_of_tendstoUniformlyOn_canonical hconv hτ₀ h₀ hx₀ hσ hσ0
    (fun j ↦ pos_iff_ne_zero.2 (hτ j)) hτ0 hV0 hV hJ0 hJ T (huV T)

/-- **Domain of the `EVI_λ` flow under penalized convexity** (Ambrosio–Gigli–Savaré, Theorem
4.0.4). On a complete pseudometric space, if `φ` is lower semicontinuous, satisfies
`TauCeti.PenalizedConvex lam τ φ` for all sufficiently small `τ > 0`, and satisfies
`φ_{τ₀}(x₁) > -∞` for some `τ₀ > 0` and `x₁ : X`, then the set of initial points of `EVI_λ`
solutions is the closure of the effective domain `{x | φ x ≠ ⊤}`. -/
theorem eviDomain_eq_closure_of_penalizedConvex [CompleteSpace X]
    (hconv : ∀ᶠ τ : ℝ≥0 in 𝓝[>] 0, PenalizedConvex lam τ φ) (hφ : LowerSemicontinuous φ)
    {τ₀ : ℝ≥0} (hτ₀ : 0 < τ₀) {x₁ : X} (h₀ : moreauYosida φ τ₀ x₁ ≠ ⊥) :
    eviDomain lam φ = closure {x | φ x ≠ ⊤} := by
  refine Subset.antisymm eviDomain_subset_closure fun x₀ hx₀ ↦ ?_
  obtain ⟨x, hx_dom, hx_lim⟩ := mem_closure_iff_seq_limit.1 hx₀
  choose U hU0 hU_evi _ using fun n ↦
    exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent_of_penalizedConvex
      hconv hφ hτ₀ h₀ (hx_dom n)
  have hCauchy : ∀ T ≥ 0, UniformCauchySeqOn U atTop (Icc 0 T) := fun T _ ↦ by
    refine Metric.uniformCauchySeqOn_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hx_lim.cauchySeq
      (ε / exp (|lam| * T)) (div_pos hε (exp_pos _))
    refine ⟨N, fun j hj k hk t ht ↦ ?_⟩
    have hexp : exp (-(lam * t)) ≤ exp (|lam| * T) :=
      exp_le_exp.2 (by nlinarith [neg_abs_le lam, abs_nonneg lam, ht.1, ht.2])
    calc dist (U j t) (U k t) ≤ exp (-(lam * t)) * dist (U j 0) (U k 0) :=
          (hU_evi j).dist_le (hU_evi k) hφ ht.1
      _ ≤ exp (|lam| * T) * dist (x j) (x k) := by
          rw [hU0 j, hU0 k]; exact mul_le_mul_of_nonneg_right hexp dist_nonneg
      _ < ε := by rw [mul_comm]; exact (lt_div_iff₀ (exp_pos _)).1 (hN j hj k hk)
  classical
  let u : ℝ → X := fun t ↦ if ht : 0 < t then
    (cauchySeq_tendsto_of_complete ((hCauchy t ht.le).cauchySeq ⟨ht.le, le_rfl⟩)).choose else x₀
  have hu0 : u 0 = x₀ := dite_eq_right (lt_irrefl 0)
  have hlim : ∀ t ≥ 0, Tendsto (fun n ↦ U n t) atTop (𝓝 (u t)) := fun t ht ↦ by
    rcases ht.eq_or_lt with rfl | ht_pos
    · simpa only [hU0, hu0] using hx_lim
    · dsimp only [u]
      rw [dite_eq_left ht_pos]
      exact (cauchySeq_tendsto_of_complete
        ((hCauchy t ht_pos.le).cauchySeq ⟨ht_pos.le, le_rfl⟩)).choose_spec
  have hu_cont : ContinuousOn u (Ici 0) := fun t₀ (ht₀ : 0 ≤ t₀) ↦ by
    have hunif : TendstoUniformlyOn U u atTop (Icc 0 (t₀ + 1)) :=
      (hCauchy (t₀ + 1) (by linarith)).tendstoUniformlyOn_of_tendsto fun t ht ↦ hlim t ht.1
    have hcont_ev : ∀ᶠ n in atTop, ContinuousOn (U n) (Icc 0 (t₀ + 1)) :=
      Eventually.of_forall fun n ↦ (hU_evi n).continuousOn.mono Icc_subset_Ici_self
    refine (hunif.continuousOn hcont_ev.frequently t₀ ⟨ht₀, by linarith⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio (t₀ + 1), isOpen_Iio, lt_add_one t₀,
      fun r ⟨hr1, hr2⟩ ↦ ⟨hr2, le_of_lt hr1⟩⟩
  have hbot := apply_ne_bot_of_moreauYosida_ne_bot h₀
  exact mem_eviDomain.2 ⟨u, hφ.tendstoGamma_const.isEVISolution_of_tendsto (fun _ ↦ hφ) hU_evi
    hlim hu_cont ⟨x 0, hx_dom 0⟩ (fun t _ ↦ hbot (u t)), hu0⟩

/-- **Convergence of minimizing movements on a complete CAT(0) space.** If `φ` is `λ`-geodesically
convex, lower semicontinuous, and never takes the value `⊥`, then from every `x₀` with `φ x₀ ≠ ⊤`
there starts an `EVI_λ` solution `u` with `u 0 = x₀`, to which all minimizing movement sequences
from `x₀` with time steps tending to `0` converge uniformly on bounded intervals `[0, T]`. -/
theorem GeodesicallyConvex.exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent
    [IsCATZeroSpace X] [CompleteSpace X] (h : GeodesicallyConvex lam φ)
    (hφ : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥) {x₀ : X} (hx₀ : φ x₀ ≠ ⊤) :
    ∃ u : ℝ → X, u 0 = x₀ ∧ IsEVISolution lam φ u ∧
      ∀ (τ : ℕ → ℝ≥0) (J : ℕ → ℕ → X),
        (∀ j, τ j ≠ 0) → Tendsto τ atTop (𝓝 0) → (∀ j, J j 0 = x₀) →
        (∀ j k, J j (k + 1) ∈ moreauYosidaResolvent φ (τ j) (J j k)) →
        ∀ T : ℝ, TendstoUniformlyOn (fun j (t : ℝ) ↦ J j ⌈t / (τ j : ℝ)⌉₊) u atTop (Icc 0 T) := by
  set τ₀ : ℝ≥0 := 1 / (2 * (⌈|lam|⌉₊ + 1))
  exact exists_isEVISolution_tendstoUniformlyOn_moreauYosidaResolvent_of_penalizedConvex
    (Eventually.of_forall fun _ ↦ h.penalizedConvex) hφ (by positivity : 0 < τ₀)
    (h.moreauYosida_ne_bot hφ hbot (one_add_mul_pos_of_le lam le_rfl) x₀) hx₀

/-- **Domain of the `EVI_λ` flow on a complete CAT(0) space.** If `φ` is `λ`-geodesically convex,
lower semicontinuous, and never takes the value `⊥`, then `eviDomain lam φ = closure {x | φ x ≠ ⊤}`.
-/
theorem GeodesicallyConvex.eviDomain_eq_closure [IsCATZeroSpace X] [CompleteSpace X]
    (h : GeodesicallyConvex lam φ) (hφ : LowerSemicontinuous φ) (hbot : ∀ x, φ x ≠ ⊥) :
    eviDomain lam φ = closure {x | φ x ≠ ⊤} := by
  rcases Set.eq_empty_or_nonempty {x : X | φ x ≠ ⊤} with hemp | ⟨x₁, _⟩
  · refine Subset.antisymm ?_ (by rw [hemp, closure_empty]; exact empty_subset _)
    simpa only [hemp, closure_empty] using eviDomain_subset_closure (lam := lam) (φ := φ)
  set τ₀ : ℝ≥0 := 1 / (2 * (⌈|lam|⌉₊ + 1))
  exact eviDomain_eq_closure_of_penalizedConvex (Eventually.of_forall fun _ ↦ h.penalizedConvex)
    hφ (by positivity : 0 < τ₀)
    (h.moreauYosida_ne_bot hφ hbot (one_add_mul_pos_of_le lam le_rfl) x₁)

end Convergence

end TauCeti
