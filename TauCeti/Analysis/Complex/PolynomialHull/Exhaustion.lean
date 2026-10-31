/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.Analysis.Complex.PolynomialHull.Basic
public import TauCeti.Analysis.Complex.Pseudoconvex
import Mathlib.Analysis.Analytic.Polynomial
import TauCeti.Analysis.Complex.NegLogOneSubNormSq
import TauCeti.Analysis.Complex.PiBall
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

/-!
# The plurisubharmonic exhaustion of a polynomial polyhedron

For a radius `R` and a finite set `s` of polynomials on `ℂⁿ`, the open set
`D = ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}` is cut out by the strict inequalities defining the
polynomial polyhedron `TauCeti.polynomialPolyhedron R s`; it is the interior of the polyhedron
when `R ≠ 0` and the polynomials are nonconstant (`TauCeti.interior_polynomialPolyhedron`). Since
the norm on `ι → ℂ` is the sup norm, `ball 0 R` is the open polydisc `{|zᵢ| < R for all i}`.

This file shows that

`ψ(z) = ∑ᵢ -log (1 - |zᵢ / R|²) + ∑_{p ∈ s} -log (1 - |p(z)|²)`

(`TauCeti.polynomialPolyhedronExhaustion R s`) is a smooth strictly plurisubharmonic exhaustion
function of `D`: it is smooth on `D`, its Levi form is positive definite at every point of `D`,
and each sublevel set `{z ∈ D | ψ(z) ≤ c}` is compact. A smooth strictly plurisubharmonic
exhaustion is the input of the `L²` criterion for a domain to be Stein (Hörmander, Chapters IV and
V), which is how the interiors of polynomial polyhedra serve as Stein neighbourhoods of
polynomially convex compact sets; that criterion is not proved here.

The basic input is the Levi form of `-log (1 - ‖g‖²)` for a holomorphic map `g` with `‖g‖ < 1`,
whose diagonal at `v` is at least `‖Dg(v)‖²`
(`TauCeti.norm_fderiv_apply_sq_le_re_leviForm_neg_log_one_sub_norm_sq`). The
polynomial terms of `ψ` are therefore plurisubharmonic, while the coordinate terms together
contribute `∑ᵢ |vᵢ / R|²`, which is positive for `v ≠ 0`. Every term of `ψ` is nonnegative on `D`,
so `ψ(z) ≤ c` bounds each `|zᵢ / R|²` and each `|p(z)|²` by `1 - exp (-c) < 1`; these bounds cut
out a compact subset of `D`.

## Main declarations

* `TauCeti.polynomialPolyhedronExhaustion R s`: the exhaustion function `ψ`.
* `TauCeti.contDiffOn_polynomialPolyhedronExhaustion`: `ψ` is smooth on `D`.
* `TauCeti.isStrictlyPlurisubharmonicAt_polynomialPolyhedronExhaustion`: `ψ` is strictly
  plurisubharmonic at every point of `D`.
* `TauCeti.isCompact_inter_setOf_polynomialPolyhedronExhaustion_le`: the sublevel sets of `ψ` in
  `D` are compact.

## References

* L. Hörmander, *An introduction to complex analysis in several variables*, 3rd ed.,
  North-Holland, 1990, §2.6, §2.7 and Chapters IV and V.
-/

public section

open MvPolynomial Metric Set

namespace TauCeti

section polynomialPolyhedron

variable {ι : Type*} [Fintype ι] {R : ℝ} {s : Finset (MvPolynomial ι ℂ)} {z : ι → ℂ}

/-- The plurisubharmonic exhaustion function
`ψ(z) = ∑ᵢ -log (1 - |zᵢ / R|²) + ∑_{p ∈ s} -log (1 - |p(z)|²)` of the open set
`ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}`, the interior of the polynomial polyhedron
`TauCeti.polynomialPolyhedron R s` when `R ≠ 0` and the polynomials of `s` are nonconstant. -/
noncomputable def polynomialPolyhedronExhaustion (R : ℝ) (s : Finset (MvPolynomial ι ℂ))
    (z : ι → ℂ) : ℝ :=
  ∑ i, -Real.log (1 - ‖z i / R‖ ^ 2) + ∑ p ∈ s, -Real.log (1 - ‖eval z p‖ ^ 2)

theorem polynomialPolyhedronExhaustion_def (R : ℝ) (s : Finset (MvPolynomial ι ℂ))
    (z : ι → ℂ) :
    polynomialPolyhedronExhaustion R s z =
      ∑ i, -Real.log (1 - ‖z i / R‖ ^ 2) + ∑ p ∈ s, -Real.log (1 - ‖eval z p‖ ^ 2) :=
  (rfl)

/-- The exhaustion function is smooth on `ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}`. -/
theorem contDiffOn_polynomialPolyhedronExhaustion {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (polynomialPolyhedronExhaustion R s)
      (ball 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ < 1}) := fun z hz ↦ by
  refine ContDiffAt.contDiffWithinAt ?_
  have hp : ∀ p ∈ s, ‖eval z p‖ < 1 := fun p hp ↦ mem_iInter₂.1 hz.2 p hp
  exact (ContDiffAt.sum fun i _ ↦ contDiffAt_neg_log_one_sub_norm_sq
      (((contDiff_apply ℂ (fun _ : ι ↦ ℂ) i).div_const (R : ℂ)).contDiffAt.restrict_scalars ℝ)
      (Complex.pi_norm_div_lt_one_of_mem_ball hz.1 i)).add
    (ContDiffAt.sum fun p hps ↦ contDiffAt_neg_log_one_sub_norm_sq
      ((AnalyticOnNhd.eval_mvPolynomial p z (mem_univ z)).contDiffAt.restrict_scalars ℝ)
        (hp p hps))

/-- The exhaustion function is **strictly plurisubharmonic** at every point of
`ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}`. -/
theorem isStrictlyPlurisubharmonicAt_polynomialPolyhedronExhaustion
    (hz : z ∈ ball 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ < 1}) :
    IsStrictlyPlurisubharmonicAt (polynomialPolyhedronExhaustion R s) z := by
  rw [isStrictlyPlurisubharmonicAt_iff]
  intro v hv
  have hR : 0 < R := pos_of_mem_ball hz.1
  have hp : ∀ p ∈ s, ‖eval z p‖ < 1 := fun p hp ↦ mem_iInter₂.1 hz.2 p hp
  have hcoord (i : ι) : ContDiffAt ℝ 2 (fun z : ι → ℂ ↦ -Real.log (1 - ‖z i / R‖ ^ 2)) z :=
    contDiffAt_neg_log_one_sub_norm_sq
      (((contDiff_apply ℂ (fun _ : ι ↦ ℂ) i).div_const (R : ℂ)).contDiffAt.restrict_scalars ℝ)
      (Complex.pi_norm_div_lt_one_of_mem_ball hz.1 i)
  have hpoly : ∀ p ∈ s, ContDiffAt ℝ 2 (fun z : ι → ℂ ↦ -Real.log (1 - ‖eval z p‖ ^ 2)) z :=
    fun p hps ↦ contDiffAt_neg_log_one_sub_norm_sq
      ((AnalyticOnNhd.eval_mvPolynomial p z (mem_univ z)).contDiffAt.restrict_scalars ℝ)
        (hp p hps)
  have hψ : polynomialPolyhedronExhaustion R s =
      (∑ i, fun z : ι → ℂ ↦ -Real.log (1 - ‖z i / R‖ ^ 2)) +
        ∑ p ∈ s, fun z : ι → ℂ ↦ -Real.log (1 - ‖eval z p‖ ^ 2) := by
    ext z
    simp [polynomialPolyhedronExhaustion_def]
  have hsum₁ : ContDiffAt ℝ 2 (∑ i, fun z : ι → ℂ ↦ -Real.log (1 - ‖z i / R‖ ^ 2)) z := by
    simpa only [Finset.sum_fn] using ContDiffAt.sum fun i _ ↦ hcoord i
  have hsum₂ : ContDiffAt ℝ 2 (∑ p ∈ s, fun z : ι → ℂ ↦ -Real.log (1 - ‖eval z p‖ ^ 2)) z := by
    simpa only [Finset.sum_fn] using ContDiffAt.sum hpoly
  rw [hψ, leviForm_add hsum₁ hsum₂, leviForm_sum _ fun i _ ↦ hcoord i, leviForm_sum _ hpoly]
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Complex.add_re,
    Complex.re_sum]
  -- The coordinate terms contribute `∑ᵢ |vᵢ / R|² > 0`; the polynomial terms are nonnegative.
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have hderiv (j : ι) : fderiv ℂ (fun z : ι → ℂ ↦ z j / R) z v = v j / R := by
    have hfun : (fun z : ι → ℂ ↦ z j / R) =
        ⇑((R : ℂ)⁻¹ • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) j) := by
      ext z
      simp [div_eq_inv_mul]
    rw [hfun, ContinuousLinearMap.fderiv]
    simp [div_eq_inv_mul]
  have hlow (j : ι) : ‖v j / R‖ ^ 2 ≤
      (leviForm (fun z : ι → ℂ ↦ -Real.log (1 - ‖z j / R‖ ^ 2)) z v v).re := by
    simpa [hderiv j] using norm_fderiv_apply_sq_le_re_leviForm_neg_log_one_sub_norm_sq
      ((contDiff_apply ℂ (fun _ : ι ↦ ℂ) j).div_const (R : ℂ)).contDiffAt
      (Complex.pi_norm_div_lt_one_of_mem_ball hz.1 j) v
  have hpos₁ : 0 < ∑ j, (leviForm (fun z : ι → ℂ ↦ -Real.log (1 - ‖z j / R‖ ^ 2)) z v v).re := by
    refine Finset.sum_pos' (fun j _ ↦ (sq_nonneg _).trans (hlow j)) ⟨i, Finset.mem_univ i, ?_⟩
    refine lt_of_lt_of_le ?_ (hlow i)
    have : v i / (R : ℂ) ≠ 0 := div_ne_zero hi (Complex.ofReal_ne_zero.2 hR.ne')
    positivity
  have hnonneg₂ : 0 ≤ ∑ p ∈ s,
      (leviForm (fun z : ι → ℂ ↦ -Real.log (1 - ‖eval z p‖ ^ 2)) z v v).re :=
    Finset.sum_nonneg fun p hps ↦ (sq_nonneg _).trans
      (norm_fderiv_apply_sq_le_re_leviForm_neg_log_one_sub_norm_sq
        ((AnalyticOnNhd.eval_mvPolynomial p z (mem_univ z)).contDiffAt) (hp p hps) v)
  linarith

/-- **The exhaustion property.** Every sublevel set of the exhaustion function in
`ball 0 R ∩ ⋂_{p ∈ s} {|p| < 1}` is compact. -/
theorem isCompact_inter_setOf_polynomialPolyhedronExhaustion_le (c : ℝ) :
    IsCompact ((ball 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ < 1}) ∩
      {z | polynomialPolyhedronExhaustion R s z ≤ c}) := by
  set D := ball 0 R ∩ ⋂ p ∈ s, {w | ‖eval w p‖ < 1}
  set t := 1 - Real.exp (-c)
  have ht : t < 1 := by simp only [t]; linarith [Real.exp_pos (-c)]
  -- The closed set `K` cut out by the bounds `|zᵢ / R|² ≤ t` and `|p(z)|² ≤ t` lies in `D`.
  set K := {z : ι → ℂ | (∀ i, ‖z i / R‖ ^ 2 ≤ t) ∧ ∀ p ∈ s, ‖eval z p‖ ^ 2 ≤ t}
  rcases le_or_gt R 0 with hR | hR
  · simp [D, ball_eq_empty.2 hR]
  have hKD : K ⊆ D := by
    intro z hz
    have hlt {a : ℝ} (ha : a ^ 2 ≤ t) (ha₀ : 0 ≤ a) : a < 1 := by nlinarith
    refine ⟨mem_ball_zero_iff.2 ((pi_norm_lt_iff hR).2 fun i ↦ ?_), mem_iInter₂.2 fun p hp ↦
      hlt (hz.2 p hp) (norm_nonneg _)⟩
    have := hlt (hz.1 i) (norm_nonneg _)
    rwa [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_lt_one hR] at this
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0 : ι → ℂ) R).of_isClosed_subset ?_ fun z hz ↦ ?_
    · have hK : K = (⋂ i, {z : ι → ℂ | ‖z i / R‖ ^ 2 ≤ t}) ∩
          ⋂ p ∈ s, {z | ‖eval z p‖ ^ 2 ≤ t} := by
        ext z
        simp [K]
      rw [hK]
      exact (isClosed_iInter fun i ↦ isClosed_le (by fun_prop) continuous_const).inter
        (isClosed_biInter fun p _ ↦ isClosed_le ((continuous_eval p).norm.pow 2) continuous_const)
    · exact ball_subset_closedBall (hKD hz).1
  -- On `D`, every term of the exhaustion is nonnegative, so a sublevel set of `D` lies in `K`.
  have hDK : D ∩ {z | polynomialPolyhedronExhaustion R s z ≤ c} =
      K ∩ polynomialPolyhedronExhaustion R s ⁻¹' Iic c := by
    refine Subset.antisymm (fun z ⟨hz, hzc⟩ ↦ ⟨?_, hzc⟩) fun z ⟨hz, hzc⟩ ↦ ⟨hKD hz, hzc⟩
    have hcoord (i : ι) : ‖z i / R‖ ^ 2 < 1 := by
      have := Complex.pi_norm_div_lt_one_of_mem_ball hz.1 i
      nlinarith [norm_nonneg (z i / R)]
    have hpoly (p) (hp : p ∈ s) : ‖eval z p‖ ^ 2 < 1 := by
      have : ‖eval z p‖ < 1 := mem_iInter₂.1 hz.2 p hp
      nlinarith [norm_nonneg (eval z p)]
    have h₁ : 0 ≤ ∑ i, -Real.log (1 - ‖z i / R‖ ^ 2) :=
      Finset.sum_nonneg fun i _ ↦ Real.neg_log_one_sub_nonneg (sq_nonneg _) (hcoord i).le
    have h₂ : 0 ≤ ∑ p ∈ s, -Real.log (1 - ‖eval z p‖ ^ 2) :=
      Finset.sum_nonneg fun p hp ↦ Real.neg_log_one_sub_nonneg (sq_nonneg _) (hpoly p hp).le
    have hzc' : polynomialPolyhedronExhaustion R s z ≤ c := hzc
    rw [polynomialPolyhedronExhaustion_def] at hzc'
    refine ⟨fun i ↦ (Real.neg_log_one_sub_le_iff (hcoord i)).1 ?_, fun p hp ↦
      (Real.neg_log_one_sub_le_iff (hpoly p hp)).1 ?_⟩
    · have := Finset.single_le_sum
        (fun j _ ↦ Real.neg_log_one_sub_nonneg (sq_nonneg _) (hcoord j).le) (Finset.mem_univ i)
      linarith
    · have := Finset.single_le_sum
        (fun q hq ↦ Real.neg_log_one_sub_nonneg (sq_nonneg _) (hpoly q hq).le) hp
      linarith
  rw [hDK]
  exact hKc.of_isClosed_subset (((contDiffOn_polynomialPolyhedronExhaustion (n := 0)).mono
    hKD).continuousOn.preimage_isClosed_of_isClosed hKc.isClosed isClosed_Iic) inter_subset_left

end polynomialPolyhedron

end TauCeti
