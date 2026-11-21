/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.PartialDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Lagrange
import TauCeti.Analysis.Calculus.DSlope.Basic
import TauCeti.Analysis.Calculus.DSlope.Integral
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Topology.MetricSpace.Pseudo.Pi

/-!
# Coordinate divided differences of entire functions on `ℂⁿ`

For a function `f : (ι → ℂ) → E` of several complex variables, a coordinate `i : ι` and a base
point `ζ : ℂ`, the coordinate divided difference `TauCeti.partialDslope i ζ f` applies the
one-variable divided difference `dslope · ζ` along the line parallel to the `i`-th coordinate axis:

  `partialDslope i ζ f z = dslope (fun w ↦ f (update z i w)) ζ (z i)`.

Away from the hyperplane `z i = ζ` it equals `(z i - ζ)⁻¹ • (f z - f (update z i ζ))`, and on
`z i = ζ` it takes the value `partialDeriv i f z` when `f` is complex differentiable there. At
every point `z` it satisfies the exact decomposition

  `f z = f (update z i ζ) + (z i - ζ) • partialDslope i ζ f z`.

When `f` is entire on `ι → ℂ` (with `ι` finite and `E` complete), the fundamental theorem of
calculus represents `partialDslope i ζ f z` as `∫ t in 0..1, ∂ᵢ f (update z i (ζ + t • (z i - ζ)))`,
and differentiation under the integral sign makes `partialDslope i ζ f` entire. For any `f` that is
complex differentiable on a closed polydisc `closedBall c R` (with no completeness assumption on
`E`), applying Hahn–Banach and the one-variable maximum modulus principle along the `i`-th
coordinate bounds `partialDslope i ζ f` by `2 M / (R - r)` on `closedBall c R` whenever `ζ` lies
within `r < R` of `c i` and `f` is bounded by `M` on the polydisc. Finally, `partialDslope i ζ`
agrees with Euclidean division by `X - C ζ` along polynomial coordinate lines, lowers polynomial
degree in `z i` by one, and preserves polynomial degree bounds in every coordinate.

## Main definitions and results

* `TauCeti.partialDslope`: the coordinate divided difference along coordinate `i` at `ζ`.
* `TauCeti.sub_smul_partialDslope`, `TauCeti.eq_update_add_sub_mul_partialDslope`: the coordinate
  division identity `f z = f (update z i ζ) + (z i - ζ) * partialDslope i ζ f z`.
* `TauCeti.partialDslope_eq_integral_partialDeriv`: the integral representation over `[0, 1]`.
* `TauCeti.differentiable_partialDslope`: `partialDslope i ζ f` is entire when `f` is entire.
* `TauCeti.norm_partialDslope_le`: polydisc supremum estimate `2 * M / (R - r)` for functions
  complex differentiable on `closedBall c R`.
* `TauCeti.partialDslope_update_eq_eval_divByMonic`: exact polynomial division formula
  `partialDslope i ζ f (update z i w) = (P /ₘ (X - C ζ)).eval w`.
* `TauCeti.exists_degree_lt_and_update_eq_eval`, `TauCeti.exists_natDegree_le_and_update_eq_eval`,
  `TauCeti.exists_natDegree_le_sub_one_and_partialDslope_eq_eval_self`,
  `TauCeti.exists_degree_lt_and_partialDslope_eq_eval`,
  `TauCeti.exists_natDegree_le_and_partialDslope_eq_eval`,
  `TauCeti.exists_degree_lt_and_partialDeriv_eq_eval`,
  `TauCeti.exists_degree_lt_and_iterate_partialDeriv_eq_eval`: coordinate polynomial degree control.

## References

* [M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer, 2000]:
  §4.3, proof of Lemma 4.8, Step 2, pp. 124–125.
-/

public section

open Function Metric Polynomial Set

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coordinate divided difference of `f : (ι → ℂ) → E` along coordinate `i` across `z i = ζ`:
`dslope (fun w ↦ f (update z i w)) ζ (z i)`. -/
noncomputable def partialDslope (i : ι) (ζ : ℂ) (f : (ι → ℂ) → E) : (ι → ℂ) → E :=
  fun z ↦ dslope (fun w ↦ f (update z i w)) ζ (z i)

theorem partialDslope_def (i : ι) (ζ : ℂ) (f : (ι → ℂ) → E) :
    partialDslope i ζ f = fun z ↦ dslope (fun w ↦ f (update z i w)) ζ (z i) := (rfl)

theorem partialDslope_apply (i : ι) (ζ : ℂ) (f : (ι → ℂ) → E) (z : ι → ℂ) :
    partialDslope i ζ f z = dslope (fun w ↦ f (update z i w)) ζ (z i) := (rfl)

/-- The coordinate divided difference of a constant function is zero. -/
@[simp]
theorem partialDslope_const (i : ι) (ζ : ℂ) (c : E) :
    partialDslope i ζ (fun _ : ι → ℂ ↦ c) = 0 := by
  ext z
  simp [partialDslope_apply]

/-- The coordinate divided difference of the zero function is zero. -/
@[simp]
theorem partialDslope_zero_fun (i : ι) (ζ : ℂ) :
    partialDslope i ζ (0 : (ι → ℂ) → E) = 0 :=
  partialDslope_const i ζ 0

/-- Away from the hyperplane `z i = ζ`, `partialDslope i ζ f z` is the difference quotient
`(z i - ζ)⁻¹ • (f z - f (update z i ζ))`. -/
theorem partialDslope_of_ne (i : ι) {ζ : ℂ} (f : (ι → ℂ) → E) {z : ι → ℂ} (hz : z i ≠ ζ) :
    partialDslope i ζ f z = (z i - ζ)⁻¹ • (f z - f (update z i ζ)) := by
  rw [partialDslope_apply, dslope_of_ne _ hz, slope_def_module, update_eq_self]

/-- On the hyperplane `z i = ζ`, `partialDslope i ζ f z` equals `partialDeriv i f z` whenever `f`
is complex differentiable at `z`. -/
theorem partialDslope_of_eq [Finite ι] {f : (ι → ℂ) → E} {z : ι → ℂ}
    (hf : DifferentiableAt ℂ f z) (i : ι) {ζ : ℂ} (hz : z i = ζ) :
    partialDslope i ζ f z = partialDeriv i f z := by
  subst hz
  rw [partialDslope_apply, dslope_same, partialDeriv_eq_deriv_update hf i]

/-- Evaluating `partialDslope i ζ f` at `update z i ζ` gives `partialDeriv i f (update z i ζ)`. -/
@[simp]
theorem partialDslope_update_self [Finite ι] {f : (ι → ℂ) → E} {z : ι → ℂ} {i : ι} {ζ : ℂ}
    (hf : DifferentiableAt ℂ f (update z i ζ)) :
    partialDslope i ζ f (update z i ζ) = partialDeriv i f (update z i ζ) :=
  partialDslope_of_eq hf i (update_self i ζ z)

/-- Exact coordinate division identity in vector form:
`(z i - ζ) • partialDslope i ζ f z = f z - f (update z i ζ)`. -/
@[simp]
theorem sub_smul_partialDslope (i : ι) (ζ : ℂ) (f : (ι → ℂ) → E) (z : ι → ℂ) :
    (z i - ζ) • partialDslope i ζ f z = f z - f (update z i ζ) := by
  rw [partialDslope_apply, sub_smul_dslope, update_eq_self]

/-- Exact coordinate division identity for complex-valued functions:
`f z = f (update z i ζ) + (z i - ζ) * partialDslope i ζ f z`. -/
theorem eq_update_add_sub_mul_partialDslope (i : ι) (ζ : ℂ) (f : (ι → ℂ) → ℂ) (z : ι → ℂ) :
    f z = f (update z i ζ) + (z i - ζ) * partialDslope i ζ f z := by
  have h := sub_smul_partialDslope i ζ f z
  rw [smul_eq_mul] at h
  linear_combination -h

/-- `partialDslope i ζ` commutes with scalar multiplication by a constant. -/
@[simp]
theorem partialDslope_const_smul (c : ℂ) (i : ι) (ζ : ℂ) (f : (ι → ℂ) → E) :
    partialDslope i ζ (c • f) = c • partialDslope i ζ f := by
  ext z
  rw [Pi.smul_apply, partialDslope_apply, partialDslope_apply, ← Pi.smul_apply]
  exact congrFun (dslope_const_smul c (fun w ↦ f (update z i w)) ζ) (z i)

/-- `partialDslope i ζ` commutes with left multiplication by a constant. -/
@[simp]
theorem partialDslope_const_mul (c : ℂ) (i : ι) (ζ : ℂ) (f : (ι → ℂ) → ℂ) :
    partialDslope i ζ (fun z ↦ c * f z) = fun z ↦ c * partialDslope i ζ f z := by
  simpa only [Pi.smul_def, smul_eq_mul] using partialDslope_const_smul c i ζ f

/-- `partialDslope i ζ` is additive on entire functions. -/
theorem partialDslope_add [Finite ι] {f g : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (i : ι) (ζ : ℂ) :
    partialDslope i ζ (f + g) = partialDslope i ζ f + partialDslope i ζ g := by
  have := Fintype.ofFinite ι
  ext z
  have hfu : DifferentiableAt ℂ (fun w ↦ f (update z i w)) ζ :=
    (hf (update z i ζ)).comp ζ (hasFDerivAt_update z ζ).differentiableAt
  have hgu : DifferentiableAt ℂ (fun w ↦ g (update z i w)) ζ :=
    (hg (update z i ζ)).comp ζ (hasFDerivAt_update z ζ).differentiableAt
  exact congrFun (dslope_add hfu hgu) (z i)

/-! ### Integral representation and entireness -/

section Entire

variable [Finite ι] [CompleteSpace E]

/-- **Integral representation of the coordinate divided difference.** For an entire function
`f : (ι → ℂ) → E`, `partialDslope i ζ f z` equals the average of `∂ᵢ f` along the segment from `ζ`
to `z i` in the `i`-th coordinate. -/
theorem partialDslope_eq_integral_partialDeriv {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) (z : ι → ℂ) :
    partialDslope i ζ f z =
      ∫ t in (0 : ℝ)..1, partialDeriv i f (update z i (ζ + t • (z i - ζ))) := by
  have := Fintype.ofFinite ι
  have hline : Differentiable ℂ (fun w ↦ f (update z i w)) :=
    fun w ↦ (hf (update z i w)).comp w (hasFDerivAt_update z w).differentiableAt
  rw [partialDslope_apply,
    dslope_eq_integral_deriv isOpen_univ (hline.contDiff (n := 1)).contDiffOn (subset_univ _)]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [partialDeriv_eq_deriv_update (hf _) i]
  simp only [update_idem, update_self]

/-- **Entireness of the coordinate divided difference.** If `f : (ι → ℂ) → E` is entire, then
`partialDslope i ζ f` is entire. -/
theorem differentiable_partialDslope {f : (ι → ℂ) → E} (hf : Differentiable ℂ f) (i : ι) (ζ : ℂ) :
    Differentiable ℂ (partialDslope i ζ f) := by
  have := Fintype.ofFinite ι
  let K : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  let φ : ℝ → ℂ := fun t ↦ ((projIcc (0 : ℝ) 1 zero_le_one t : ℝ) : ℂ)
  have hφ : Continuous φ :=
    Complex.continuous_ofReal.comp (continuous_subtypeVal.comp continuous_projIcc)
  have hφK : ∀ t, φ t ∈ K :=
    fun t ↦ ⟨projIcc 0 1 zero_le_one t, (projIcc 0 1 zero_le_one t).property, rfl⟩
  let F : ((ι → ℂ) × ℂ) → E := fun p ↦ partialDeriv i f (update p.1 i (ζ + p.2 * (p.1 i - ζ)))
  have hFd : Differentiable ℂ F := by
    refine (differentiable_partialDeriv hf i).comp (differentiable_pi.mpr fun j ↦ ?_)
    by_cases hj : j = i
    · subst hj
      simp only [update_self]
      fun_prop
    · simp only [update_of_ne hj]
      fun_prop
  have hg : MeasureTheory.Integrable (fun _ : ℝ ↦ (1 : ℂ))
      (MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)) :=
    continuous_const.integrableOn_Ioc
  intro z
  have han : AnalyticAt ℂ
      (fun q ↦ ∫ t in Ioc (0 : ℝ) 1, (1 : ℂ) • F (q, φ t)) z :=
    analyticAt_integral_smul hK hφ hφK
      (fun y _ ↦ hFd.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem) hg
  refine han.differentiableAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ ?_)
  rw [partialDslope_eq_integral_partialDeriv hf i ζ q,
    intervalIntegral.integral_of_le zero_le_one]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  simp only [one_smul, F, φ, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self ht),
    Complex.real_smul]

end Entire

/-! ### Polydisc supremum bounds -/

section NormBounds

variable [Fintype ι]

/-- **Polydisc maximum modulus bound for `partialDslope`.** If `f : (ι → ℂ) → E` is complex
differentiable and bounded by `M` on `closedBall c R`, and `ζ ∈ closedBall (c i) r` with `r < R`,
then `‖partialDslope i ζ f z‖ ≤ 2 * M / (R - r)` for every `z ∈ closedBall c R`. -/
theorem norm_partialDslope_le {f : (ι → ℂ) → E} {c : ι → ℂ} {r R M : ℝ} {i : ι}
    {ζ : ℂ} (hf : DifferentiableOn ℂ f (closedBall c R)) (hζ : ζ ∈ closedBall (c i) r)
    (hrR : r < R) (hM : ∀ w ∈ closedBall c R, ‖f w‖ ≤ M) {z : ι → ℂ} (hz : z ∈ closedBall c R) :
    ‖partialDslope i ζ f z‖ ≤ 2 * M / (R - r) := by
  have hr : 0 ≤ r := dist_nonneg.trans (mem_closedBall.mp hζ)
  have hR : 0 < R := hr.trans_lt hrR
  have hRr : 0 < R - r := sub_pos.mpr hrR
  have hζ_ball : ζ ∈ ball (c i) R := mem_ball.mpr ((mem_closedBall.mp hζ).trans_lt hrR)
  have hζM : ‖f (update z i ζ)‖ ≤ M :=
    hM _ (update_mem_closedBall (closedBall_subset_closedBall hrR.le hζ) hz)
  set h : ℂ → E := fun u ↦ f (update z i u)
  have hh_diff : DifferentiableOn ℂ h (closedBall (c i) R) :=
    hf.comp (fun u _ ↦ (hasFDerivAt_update z u).differentiableAt.differentiableWithinAt)
      fun u hu ↦ update_mem_closedBall hu hz
  have hh_at : DifferentiableAt ℂ h ζ :=
    (hh_diff.mono ball_subset_closedBall).differentiableAt (isOpen_ball.mem_nhds hζ_ball)
  obtain ⟨φ, hφ_norm, hφ_val⟩ := exists_dual_vector'' ℂ (partialDslope i ζ f z)
  set g : ℂ → ℂ := dslope (φ ∘ h) ζ
  have hg_diff : DifferentiableOn ℂ g (ball (c i) R) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds hζ_ball)).mpr
      (φ.differentiable.comp_differentiableOn (hh_diff.mono ball_subset_closedBall))
  have hg_cont : ContinuousOn g (closure (ball (c i) R)) := by
    rw [closure_ball (c i) hR.ne', continuousOn_dslope (closedBall_mem_nhds_of_mem hζ_ball)]
    exact ⟨φ.continuous.comp_continuousOn hh_diff.continuousOn, φ.differentiableAt.comp ζ hh_at⟩
  -- On the boundary circle `sphere (c i) R`, `‖u - ζ‖ ≥ R - r` and `‖φ(h u - h ζ)‖ ≤ 2 * M`.
  have hg_fr (u : ℂ) (hu : u ∈ frontier (ball (c i) R)) : ‖g u‖ ≤ 2 * M / (R - r) := by
    rw [frontier_ball (c i) hR.ne'] at hu
    have huR : ‖u - c i‖ = R := by simpa [dist_eq_norm] using mem_sphere.mp hu
    have hζr : ‖ζ - c i‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hζ
    have huζ : R - r ≤ ‖u - ζ‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub u ζ (c i)]
    have hfuM : ‖f (update z i u)‖ ≤ M :=
      hM _ (update_mem_closedBall (sphere_subset_closedBall hu) hz)
    rw [le_div_iff₀ hRr, mul_comm]
    calc (R - r) * ‖g u‖
        ≤ ‖u - ζ‖ * ‖g u‖ := mul_le_mul_of_nonneg_right huζ (norm_nonneg _)
      _ = ‖(u - ζ) • g u‖ := (norm_smul (u - ζ) (g u)).symm
      _ = ‖φ (h u - h ζ)‖ := by
          rw [sub_smul_dslope, Function.comp_apply, Function.comp_apply, ← map_sub]
      _ ≤ ‖φ‖ * ‖h u - h ζ‖ := φ.le_opNorm _
      _ ≤ 1 * (‖h u‖ + ‖h ζ‖) :=
          mul_le_mul hφ_norm (norm_sub_le _ _) (norm_nonneg _) zero_le_one
      _ ≤ 2 * M := by linarith
  have hzi : z i ∈ closure (ball (c i) R) := by
    rw [closure_ball (c i) hR.ne']
    exact mem_closedBall.mpr ((dist_le_pi_dist z c i).trans (mem_closedBall.mp hz))
  have hgz := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball ⟨hg_diff, hg_cont⟩
    hg_fr hzi
  have hφ_eq : g (z i) = (‖partialDslope i ζ f z‖ : ℂ) :=
    (φ.dslope_comp h ζ (z i) fun _ ↦ hh_at).trans hφ_val
  simpa [hφ_eq] using hgz

end NormBounds

/-! ### Coordinate polynomial degree control -/

section Degree

/-- If `f` agrees with a polynomial `P` along the `i`-th coordinate line through `z`, then
`partialDslope i ζ f` agrees with `P /ₘ (X - C ζ)` along that line. -/
theorem partialDslope_update_eq_eval_divByMonic {f : (ι → ℂ) → ℂ} {i : ι} {ζ : ℂ}
    {z : ι → ℂ} {P : ℂ[X]} (hP : ∀ w, f (update z i w) = P.eval w) (w : ℂ) :
    partialDslope i ζ f (update z i w) = (P /ₘ (X - C ζ)).eval w := by
  have hPdiv : P = C (P.eval ζ) + (X - C ζ) * (P /ₘ (X - C ζ)) := by
    conv_lhs => rw [← modByMonic_add_div P (X - C ζ), modByMonic_X_sub_C_eq_C_eval]
  have hfun : (fun u ↦ f (update (update z i w) i u)) =
      (fun _ ↦ P.eval ζ) + ((fun u ↦ u - ζ) * fun u ↦ (P /ₘ (X - C ζ)).eval u) := by
    ext u
    simp only [update_idem, hP, Pi.add_apply, Pi.mul_apply]
    conv_lhs => rw [hPdiv]
    simp
  rw [partialDslope_apply, update_self, hfun,
    dslope_add (differentiableAt_const _) (by fun_prop), Pi.add_apply, dslope_const,
    Pi.zero_apply, zero_add, dslope_mul (by fun_prop) (by fun_prop)]
  have hderiv : dslope (fun u : ℂ ↦ u - ζ) ζ w = 1 := by
    rcases eq_or_ne w ζ with rfl | hw
    · simp
    · simp [dslope_of_ne _ hw, slope_def_field, sub_ne_zero.mpr hw]
  simp [hderiv]

/-- Fixing the `i`-th coordinate at `ζ` preserves a strict polynomial degree bound `< d` in any
coordinate `j` (becoming constant in coordinate `i` itself). -/
theorem exists_degree_lt_and_update_eq_eval {f : (ι → ℂ) → ℂ} (i j : ι) (ζ : ℂ)
    {d : WithBot ℕ} (hf : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w)
    (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update (update z j w) i ζ) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨Q, hQdeg, hQ⟩ := hf z
    refine ⟨C (Q.eval ζ), ?_, fun w ↦ by simp [hQ ζ]⟩
    rcases eq_or_ne Q 0 with rfl | hQ0
    · simpa using hQdeg
    · exact degree_C_le.trans_lt ((zero_le_degree_iff.mpr hQ0).trans_lt hQdeg)
  · obtain ⟨Q, hQdeg, hQ⟩ := hf (update z i ζ)
    exact ⟨Q, hQdeg, fun w ↦ by rw [update_comm hij, hQ]⟩

/-- Fixing the `i`-th coordinate at `ζ` preserves a polynomial degree bound `≤ e` in any
coordinate `j` (becoming constant in coordinate `i` itself). -/
theorem exists_natDegree_le_and_update_eq_eval {f : (ι → ℂ) → ℂ} (i j : ι) (ζ : ℂ) {e : ℕ}
    (hf : ∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update (update z j w) i ζ) = Q.eval w := by
  simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using
    exists_degree_lt_and_update_eq_eval i j ζ (d := Order.succ (e : WithBot ℕ))
      (fun y ↦ by simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using hf y) z

/-- **Degree reduction in the divided coordinate.** If `f` is a polynomial of degree at most `e` in
`z i` along the `i`-th coordinate line through `z`, then `partialDslope i ζ f` is a polynomial of
degree at most `e - 1` along that line. -/
theorem exists_natDegree_le_sub_one_and_partialDslope_eq_eval_self {f : (ι → ℂ) → ℂ} (i : ι)
    (ζ : ℂ) {e : ℕ} {z : ι → ℂ}
    (hf : ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update z i w) = Q.eval w) :
    ∃ Q : ℂ[X], Q.natDegree ≤ e - 1 ∧ ∀ w, partialDslope i ζ f (update z i w) = Q.eval w := by
  obtain ⟨P, hPdeg, hP⟩ := hf
  refine ⟨P /ₘ (X - C ζ), ?_, partialDslope_update_eq_eval_divByMonic hP⟩
  calc (P /ₘ (X - C ζ)).natDegree
      = P.natDegree - (X - C ζ).natDegree := natDegree_divByMonic P (monic_X_sub_C ζ)
    _ ≤ e - 1 := by rw [natDegree_X_sub_C]; omega

/-- **Coordinate degree preservation under `partialDslope`.** If `f` is entire and a polynomial of
degree strictly less than `d` in coordinate `j`, then so is `partialDslope i ζ f`. -/
theorem exists_degree_lt_and_partialDslope_eq_eval [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (i j : ι) (ζ : ℂ) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialDslope i ζ f (update z j w) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨P, hPdeg, hP⟩ := hdeg z
    exact ⟨P /ₘ (X - C ζ), (degree_divByMonic_le P _).trans_lt hPdeg,
      partialDslope_update_eq_eval_divByMonic hP⟩
  cases d with
  | bot =>
    obtain ⟨Q, hQ, _⟩ := hdeg z
    exact (not_lt_bot hQ).elim
  | coe d =>
    have := Fintype.ofFinite ι
    let s : Finset ℕ := Finset.range d
    let v : ℕ → ℂ := fun m ↦ (m : ℂ)
    have hv : InjOn v s := Nat.cast_injective.injOn
    refine ⟨Lagrange.interpolate s v (fun m ↦ partialDslope i ζ f (update z j (v m))), ?_,
      fun w ↦ ?_⟩
    · simpa only [s, Finset.card_range, Nat.cast_withBot] using
        Lagrange.degree_interpolate_lt (fun m ↦ partialDslope i ζ f (update z j (v m))) hv
    · -- Express `f` along coordinate `j` in the Lagrange basis at `0, …, d - 1`, then apply
      -- `dslope · ζ` along coordinate `i` term-by-term.
      have hfun : (fun u ↦ f (update (update z j w) i u)) =
          fun u ↦ ∑ m ∈ s, (Lagrange.basis s v m).eval w * f (update (update z j (v m)) i u) := by
        ext u
        obtain ⟨Qu, hQu_deg, hQu⟩ := hdeg (update z i u)
        have hQu_eq : Qu = Lagrange.interpolate s v (fun m ↦ f (update (update z i u) j (v m))) :=
          Lagrange.eq_interpolate_of_eval_eq _ hv
            (by simpa only [s, Finset.card_range, Nat.cast_withBot] using hQu_deg)
            fun m _ ↦ (hQu (v m)).symm
        rw [update_comm hij, hQu w, hQu_eq, Lagrange.interpolate_apply, eval_finsetSum]
        refine Finset.sum_congr rfl fun m _ ↦ ?_
        rw [eval_mul, eval_C, mul_comm, update_comm (Ne.symm hij)]
      have hdiff (m : ℕ) (_ : m ∈ s) : DifferentiableAt ℂ
          (fun u ↦ (Lagrange.basis s v m).eval w * f (update (update z j (v m)) i u)) ζ :=
        ((hf _).comp ζ (hasFDerivAt_update (update z j (v m)) ζ).differentiableAt).const_mul _
      rw [partialDslope_apply, update_of_ne (Ne.symm hij), hfun,
        congrFun (dslope_sum s hdiff) (z i), Lagrange.interpolate_apply, eval_finsetSum]
      refine Finset.sum_congr rfl fun m _ ↦ ?_
      rw [congrFun (dslope_const_mul _ _ ζ) (z i), eval_mul, eval_C, mul_comm, partialDslope_apply,
        update_of_ne (Ne.symm hij)]

/-- If `f` is entire and a polynomial of degree at most `e` in coordinate `j`, then so is
`partialDslope i ζ f`. -/
theorem exists_natDegree_le_and_partialDslope_eq_eval [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (i j : ι) (ζ : ℂ) {e : ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.natDegree ≤ e ∧ ∀ w, partialDslope i ζ f (update z j w) = Q.eval w := by
  simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using
    exists_degree_lt_and_partialDslope_eq_eval hf i j ζ (d := Order.succ (e : WithBot ℕ))
      (fun y ↦ by simpa only [Order.lt_succ_iff, ← natDegree_le_iff_degree_le] using hdeg y) z

/-- Differentiating an entire function along coordinate `i` preserves a strict polynomial degree
bound `< d` in every coordinate `j`. -/
theorem exists_degree_lt_and_partialDeriv_eq_eval [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (i j : ι) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (z : ι → ℂ) :
    ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, partialDeriv i f (update z j w) = Q.eval w := by
  by_cases hij : j = i
  · subst hij
    obtain ⟨Q, hQdeg, hQ⟩ := hdeg z
    refine ⟨Q.derivative, degree_derivative_le.trans_lt hQdeg, fun w ↦ ?_⟩
    rw [partialDeriv_eq_deriv_update (hf _) j, update_self]
    have hfun : (fun s ↦ f (update (update z j w) j s)) = fun s ↦ Q.eval s :=
      funext fun s ↦ by simp [hQ]
    rw [hfun, Polynomial.deriv]
  · obtain ⟨Q, hQ, hQz⟩ := exists_degree_lt_and_partialDslope_eq_eval hf i j (z i) hdeg z
    exact ⟨Q, hQ, fun w ↦ by
      rw [← partialDslope_of_eq (hf _) i (update_of_ne (Ne.symm hij) w z), hQz]⟩

/-- Iterated differentiation of an entire function along coordinate `i` preserves a strict
polynomial degree bound `< d` in every coordinate `j`. -/
theorem exists_degree_lt_and_iterate_partialDeriv_eq_eval [Finite ι] {f : (ι → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (i j : ι) {d : WithBot ℕ}
    (hdeg : ∀ y, ∃ Q : ℂ[X], Q.degree < d ∧ ∀ w, f (update y j w) = Q.eval w) (m : ℕ) :
    ∀ z, ∃ Q : ℂ[X], Q.degree < d ∧
      ∀ w, (partialDeriv i)^[m] f (update z j w) = Q.eval w := by
  induction m with
  | zero => exact hdeg
  | succ m ih =>
    simp_rw [iterate_succ_apply']
    exact exists_degree_lt_and_partialDeriv_eq_eval (differentiable_iterate_partialDeriv hf i m)
      i j ih

end Degree

end TauCeti
