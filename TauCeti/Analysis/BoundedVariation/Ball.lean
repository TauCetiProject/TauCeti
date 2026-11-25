/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.BoundedVariation.MinkowskiContent
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The perimeter of balls, annuli and separated balls

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E` of
dimension `n`, and write `ω = μ (ball 0 1)`. A ball of radius `r > 0` has perimeter

`P(ball c r) = n ω r^(n-1) = (n / r) μ (ball c r)`

in the whole space (`TauCeti.perimeter_ball`, `TauCeti.perimeter_ball_eq_ofReal_div_mul`). For
`μ` the volume of `EuclideanSpace ℝ (Fin n)` this is the classical surface area `n ω_n r^(n-1)`
of the sphere of radius `r`, where `ω_n` is the volume of the unit ball. The perimeter only sees a
set up to null sets, so the closed ball has the same perimeter (`TauCeti.perimeter_closedBall`).
In dimension `n ≥ 1` balls satisfy `P(ball c r)^n = n^n ω μ (ball c r)^(n-1)`
(`TauCeti.perimeter_ball_pow`): they attain equality in the isoperimetric inequality
`P(E)^n ≥ n^n ω μ E^(n-1)`, whose constant is fixed by this identity.

Sets assembled from balls test the inequality and its equality case. Perimeter adds up over sets
with disjoint closures (`TauCeti.perimeter_union_of_disjoint_closure`), so for `0 < r < R` the open
annulus `ball c R \ closedBall c r`, whose complement is `closedBall c r ∪ (ball c R)ᶜ`, has
perimeter `n (R^(n-1) + r^(n-1)) ω` (`TauCeti.perimeter_ball_sdiff_closedBall_of_pos`), and two
balls of radii `r₁, r₂ > 0` with centres more than `r₁ + r₂` apart have a union of perimeter
`n (r₁^(n-1) + r₂^(n-1)) ω` (`TauCeti.perimeter_ball_union_ball`). Both satisfy the isoperimetric
inequality strictly. The punctured ball `ball c r \ {c}` agrees with `ball c r` up to a null set,
so it attains equality (`TauCeti.perimeter_ball_sdiff_singleton_pow`), although it is not a ball
(`TauCeti.ball_sdiff_singleton_ne_ball`): equality only determines a set up to null sets.

The perimeter is computed from its definition by duality. The test vector field
`x ↦ θ x • (x - c) / (r + δ)`, for a smooth bump `θ` equal to one on the ball and supported in
the ball of radius `r + δ`, has norm at most one and constant divergence `n / (r + δ)` on the
ball, which gives the lower bound as `δ → 0`. For the upper bound, the perimeter of the closed
ball is at most its lower outer Minkowski content
(`TauCeti.perimeter_closure_le_liminf_measure_thickening_sdiff_div`). The `ε`-neighbourhood of the
closed ball is the open ball of radius `r + ε`, so this content is the derivative `n r^(n-1) ω`
of `r ↦ r^n ω`.

## Main results

* `TauCeti.perimeter_ball`: `P(ball c r) = n r^(n-1) μ (ball 0 1)` for `r > 0`.
* `TauCeti.perimeter_ball_eq_ofReal_div_mul`: `P(ball c r) = (n / r) μ (ball c r)`.
* `TauCeti.perimeter_closedBall`: the same formula for closed balls.
* `TauCeti.perimeter_ball_pow`: `P(ball c r)^n = n^n μ (ball 0 1) μ (ball c r)^(n-1)`.
* `TauCeti.perimeter_ball_sdiff_closedBall`, `TauCeti.perimeter_ball_sdiff_closedBall_of_pos`: the
  perimeter of an annulus.
* `TauCeti.finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_ball_sdiff_closedBall_pow`:
  annuli satisfy the isoperimetric inequality strictly.
* `TauCeti.perimeter_ball_union_ball` and
  `TauCeti.finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_ball_union_ball_pow`: the
  perimeter of two separated balls, and the strict isoperimetric inequality for them.
* `TauCeti.perimeter_ball_sdiff_singleton_pow`: punctured balls attain equality.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Chapter 12.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set Filter TopologicalSpace TestFunction
open scoped ENNReal NNReal Distributions Topology

variable {E : Type*} [NormedAddCommGroup E] {c : E} {r : ℝ}
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E}

/-- **Lower bound for the perimeter of a ball.** For `r > 0` and `δ > 0`, in dimension `n` the
ball of radius `r` has perimeter at least `(n / (r + δ)) * μ.real (ball c r)`. -/
private theorem ofReal_le_perimeter_ball (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r)) ≤ perimeter μ ⊤ (ball c r) := by
  -- The test field is `x ↦ θ x • (x - c) / (r + δ)`, where the bump `θ` is one on the ball of
  -- radius `r` and supported in the ball of radius `r + δ`; it is admissible and has divergence
  -- `n / (r + δ)` on the ball.
  let θ : ContDiffBump c := ⟨r, r + δ, hr, by linarith⟩
  have hrδ : 0 < r + δ := by linarith
  let φ : 𝓓(⊤, E) :=
    ⟨fun x => ((r + δ)⁻¹ * θ x) • (x - c),
      (contDiff_const.mul θ.contDiff).smul (contDiff_id.sub contDiff_const),
      θ.hasCompactSupport.mul_left.smul_right, by simp⟩
  have hφ (x : E) : ‖φ x‖ ≤ 1 := by
    simp only [φ, coe_mk]
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 hrδ.le) θ.nonneg)]
    by_cases hx : θ x = 0
    · simp [hx]
    have hxc : ‖x - c‖ < r + δ := by
      rw [← dist_eq_norm, ← mem_ball]
      exact θ.support_eq ▸ hx
    calc (r + δ)⁻¹ * θ x * ‖x - c‖ ≤ (r + δ)⁻¹ * 1 * (r + δ) := by
          gcongr
          · exact θ.le_one
    _ = 1 := by field_simp
  -- On the ball the bump is locally one, so the field is locally `x ↦ (x - c) / (r + δ)`.
  have hdiv : ∀ x ∈ ball c r, divergenceCLM φ x = finrank ℝ E / (r + δ) := by
    intro x hx
    have hloc : (φ : E → E) =ᶠ[𝓝 x] fun y => (r + δ)⁻¹ • (y - c) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp only [φ, coe_mk]
      rw [θ.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]
    have hd : HasFDerivAt (fun y => (r + δ)⁻¹ • (y - c))
        ((r + δ)⁻¹ • ContinuousLinearMap.id ℝ E) x :=
      ((hasFDerivAt_id x).sub_const c).const_smul _
    rw [divergenceCLM_apply, hloc.fderiv_eq, hd.fderiv]
    simp [div_eq_inv_mul]
  calc ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r))
      = ENNReal.ofReal (∫ x in ball c r, divergenceCLM φ x ∂μ) := by
        rw [setIntegral_congr_fun measurableSet_ball hdiv, setIntegral_const, smul_eq_mul,
          mul_comm]
    _ ≤ perimeter μ ⊤ (ball c r) := by
        rw [perimeter_eq_iSup measurableSet_ball.nullMeasurableSet]
        exact le_iSup₂_of_le (f := fun (φ : 𝓓(⊤, E)) (_ : ∀ x, ‖φ x‖ ≤ 1) =>
          ENNReal.ofReal (∫ x in ball c r, divergenceCLM φ x ∂μ)) φ hφ le_rfl

variable [μ.IsAddHaarMeasure]

/-- **Upper bound for the perimeter of a ball.** For `r > 0`, in dimension `n` the ball of
radius `r` has perimeter at most `n * r ^ (n - 1) * μ.real (ball 0 1)`. -/
private theorem perimeter_ball_le (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) ≤ ENNReal.ofReal
      (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  -- The closed ball has the same perimeter, and its outer Minkowski content is the derivative
  -- `n r^(n-1) ω` of `r ↦ r^n ω`.
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hshell : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      μ ((thickening ε (closedBall c r) \ closure (closedBall c r)) ∩ (⊤ : Opens E)) /
        ENNReal.ofReal ε = ENNReal.ofReal (ε⁻¹ * (((r + ε) ^ n - r ^ n) * ω)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    rw [thickening_closedBall hε hr.le, closure_closedBall, Opens.coe_top, inter_univ,
      ← ofReal_measureReal (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne),
      measureReal_sdiff (closedBall_subset_ball (by linarith)) measurableSet_closedBall
        measure_ball_lt_top.ne, μ.addHaar_real_ball_of_pos c (by linarith),
      μ.addHaar_real_closedBall c hr.le, ← ENNReal.ofReal_div_of_pos hε]
    congr 1
    ring
  have hslope : Tendsto (fun ε : ℝ => ENNReal.ofReal (ε⁻¹ * (((r + ε) ^ n - r ^ n) * ω)))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (n * r ^ (n - 1) * ω))) := by
    refine ENNReal.tendsto_ofReal ?_
    simp_rw [← mul_assoc]
    exact ((hasDerivAt_pow n r).tendsto_slope_zero_right.mul_const ω).congr fun ε => by
      rw [smul_eq_mul]
  calc perimeter μ ⊤ (ball c r)
      = perimeter μ ⊤ (closure (closedBall c r)) := by
        rw [closure_closedBall, perimeter_congr_ae (ae_restrict_of_ae
          (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c r hr.ne'))]
    _ ≤ liminf (fun ε => μ ((thickening ε (closedBall c r) \ closure (closedBall c r)) ∩
          (⊤ : Opens E)) / ENNReal.ofReal ε) (𝓝[>] 0) :=
        perimeter_closure_le_liminf_measure_thickening_sdiff_div ⊤ _
    _ = ENNReal.ofReal (n * r ^ (n - 1) * ω) := by
        rw [liminf_congr hshell, hslope.liminf_eq]

/-- For `r > 0`, in dimension `n` the ball of radius `r` has perimeter
`n * r ^ (n - 1) * μ.real (ball 0 1)`, as a real number cast to `ℝ≥0∞`. -/
private theorem perimeter_ball_eq_ofReal (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) =
      ENNReal.ofReal (finrank ℝ E * r ^ (finrank ℝ E - 1) * μ.real (ball 0 1)) := by
  refine le_antisymm (perimeter_ball_le hr) (le_of_tendsto (x := 𝓝[>] (0 : ℝ))
    (f := fun δ => ENNReal.ofReal (finrank ℝ E / (r + δ) * μ.real (ball c r))) ?_ ?_)
  · rw [← μ.finrank_div_mul_addHaar_real_ball c hr]
    refine ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds ?_)
    have : ContinuousAt (fun δ : ℝ => (finrank ℝ E : ℝ) / (r + δ) * μ.real (ball c r)) 0 := by
      fun_prop (disch := simpa using hr.ne')
    simpa using this.tendsto
  · filter_upwards [self_mem_nhdsWithin] with δ hδ using ofReal_le_perimeter_ball hr hδ

/-- **The perimeter of a ball.** Against an additive Haar measure `μ` on a space of dimension `n`,
a ball of radius `r > 0` has perimeter `n r^(n-1) μ (ball 0 1)` in the whole space. For the volume
of `EuclideanSpace ℝ (Fin n)` this is the surface area `n ω_n r^(n-1)` of the sphere of
radius `r`. -/
theorem perimeter_ball (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_ball_eq_ofReal hr, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
    ofReal_measureReal measure_ball_lt_top.ne]

/-- **The perimeter of a ball, normalized by its volume.** A ball of radius `r` has perimeter
`(n / r) μ (ball c r)`, where `n` is the dimension. For `r ≤ 0` the ball is empty and both sides
are `0`. -/
theorem perimeter_ball_eq_ofReal_div_mul :
    perimeter μ ⊤ (ball c r) = ENNReal.ofReal (finrank ℝ E / r) * μ (ball c r) := by
  by_cases hr : 0 < r
  swap
  · rw [ball_eq_empty.2 (not_lt.1 hr), perimeter_empty, measure_empty, mul_zero]
  rw [perimeter_ball_eq_ofReal hr, ← μ.finrank_div_mul_addHaar_real_ball c hr,
    ENNReal.ofReal_mul (by positivity), ofReal_measureReal measure_ball_lt_top.ne]

/-- **The perimeter of a closed ball.** A closed ball of radius `r > 0` has the same perimeter
`n r^(n-1) μ (ball 0 1)` as the open ball, since they differ by a null set. -/
theorem perimeter_closedBall (hr : 0 < r) :
    perimeter μ ⊤ (closedBall c r) =
      finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero c r
    hr.ne')), perimeter_ball hr]

/-- **Balls are isoperimetric equality cases.** In dimension `n ≥ 1`, a ball of radius `r > 0`
satisfies `P(ball c r)^n = n^n μ (ball 0 1) μ (ball c r)^(n-1)`, equality in the isoperimetric
inequality `P(E)^n ≥ n^n μ (ball 0 1) μ E^(n-1)`. -/
theorem perimeter_ball_pow (hn : finrank ℝ E ≠ 0) (hr : 0 < r) :
    perimeter μ ⊤ (ball c r) ^ finrank ℝ E =
      finrank ℝ E ^ finrank ℝ E * μ (ball 0 1) * μ (ball c r) ^ (finrank ℝ E - 1) := by
  rw [perimeter_ball hr, μ.addHaar_ball_of_pos c hr]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h : ENNReal.ofReal (r ^ k) ^ (k + 1) = ENNReal.ofReal (r ^ (k + 1)) ^ k := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity), ← pow_mul,
      ← pow_mul, mul_comm]
  rw [hk, Nat.succ_sub_one, Nat.succ_eq_add_one, mul_pow, mul_pow, h]
  ring

/-! ### Annuli, separated balls and punctured balls -/

omit [BorelSpace E] in
/-- A set whose perimeter and measure are `n a μ (ball 0 1)` and `v μ (ball 0 1)`, with
`v^(n-1) < a^n`, satisfies the isoperimetric inequality strictly. Here `n ≥ 1` is the dimension. -/
private theorem finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_pow_of_lt
    (hn : finrank ℝ E ≠ 0) {A : Set E} {a v : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v)
    (hP : perimeter μ ⊤ A = finrank ℝ E * ENNReal.ofReal a * μ (ball 0 1))
    (hA : μ A = ENNReal.ofReal v * μ (ball 0 1)) (h : v ^ (finrank ℝ E - 1) < a ^ finrank ℝ E) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * μ (ball 0 1) * μ A ^ (finrank ℝ E - 1) <
      perimeter μ ⊤ A ^ finrank ℝ E := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  -- Both sides are `n ^ n μ (ball 0 1) ^ n` times a real number.
  set C := (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * μ (ball 0 1) ^ finrank ℝ E
  have hC : C ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn))
    (pow_ne_zero _ (measure_ball_pos μ 0 one_pos).ne')
  have hC' : C ≠ ∞ := ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
    (ENNReal.pow_ne_top measure_ball_lt_top.ne)
  calc (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * μ (ball 0 1) * μ A ^ (finrank ℝ E - 1) =
        C * ENNReal.ofReal (v ^ (finrank ℝ E - 1)) := by
        rw [hA, mul_pow, ENNReal.ofReal_pow hv]
        simp only [C, hk, Nat.add_sub_cancel]
        ring
    _ < C * ENNReal.ofReal (a ^ finrank ℝ E) := (ENNReal.mul_lt_mul_iff_right hC hC').2
        ((ENNReal.ofReal_lt_ofReal_iff ((by positivity : (0 : ℝ) ≤ _).trans_lt h)).2 h)
    _ = perimeter μ ⊤ A ^ finrank ℝ E := by
        rw [hP, mul_pow, mul_pow, ENNReal.ofReal_pow ha]
        ring

/-- **The perimeter of an annulus.** For `r < R`, the open annulus `ball c R \ closedBall c r` has
the perimeter of the outer ball plus that of the inner closed ball: its complement is the union of
`closedBall c r` and `(ball c R)ᶜ`, which are closed and disjoint. -/
theorem perimeter_ball_sdiff_closedBall {R : ℝ} (h : r < R) :
    perimeter μ ⊤ (ball c R \ closedBall c r) =
      perimeter μ ⊤ (ball c R) + perimeter μ ⊤ (closedBall c r) := by
  rw [← perimeter_compl, compl_sdiff, perimeter_union_of_disjoint_closure
    measurableSet_closedBall.nullMeasurableSet measurableSet_ball.compl.nullMeasurableSet,
    perimeter_compl, add_comm]
  rw [isClosed_closedBall.closure_eq, isOpen_ball.isClosed_compl.closure_eq]
  exact disjoint_compl_right_iff_subset.2 (closedBall_subset_ball h)

/-- **The perimeter of an annulus, explicitly.** For `0 < r < R`, in dimension `n` the open annulus
`ball c R \ closedBall c r` has perimeter `n (R^(n-1) + r^(n-1)) μ (ball 0 1)`. -/
theorem perimeter_ball_sdiff_closedBall_of_pos {R : ℝ} (hr : 0 < r) (h : r < R) :
    perimeter μ ⊤ (ball c R \ closedBall c r) = finrank ℝ E *
      ENNReal.ofReal (R ^ (finrank ℝ E - 1) + r ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_ball_sdiff_closedBall h, perimeter_ball (hr.trans h), perimeter_closedBall hr,
    ENNReal.ofReal_add (pow_pos (hr.trans h) _).le (pow_pos hr _).le]
  ring

/-- **Annuli are strict isoperimetric examples.** In dimension `n ≥ 1`, for `0 < r < R` the open
annulus `A = ball c R \ closedBall c r` satisfies `n^n μ (ball 0 1) μ A^(n-1) < P(A)^n`. -/
theorem finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_ball_sdiff_closedBall_pow
    (hn : finrank ℝ E ≠ 0) {R : ℝ} (hr : 0 < r) (h : r < R) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * μ (ball 0 1) *
        μ (ball c R \ closedBall c r) ^ (finrank ℝ E - 1) <
      perimeter μ ⊤ (ball c R \ closedBall c r) ^ finrank ℝ E := by
  have hv : 0 ≤ R ^ finrank ℝ E - r ^ finrank ℝ E :=
    sub_nonneg.2 (pow_le_pow_left₀ hr.le h.le _)
  refine finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_pow_of_lt hn
    (add_nonneg (pow_pos (hr.trans h) _).le (pow_pos hr _).le) hv
    (perimeter_ball_sdiff_closedBall_of_pos hr h) ?_ ?_
  · rw [← ofReal_measureReal (measure_ne_top_of_subset sdiff_subset measure_ball_lt_top.ne),
      μ.addHaar_real_ball_sdiff_closedBall c hr.le h.le, ENNReal.ofReal_mul hv,
      ofReal_measureReal measure_ball_lt_top.ne]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    rw [hk, Nat.add_sub_cancel]
    calc (R ^ (k + 1) - r ^ (k + 1)) ^ k ≤ (R ^ (k + 1)) ^ k :=
          pow_le_pow_left₀ (hk ▸ hv) (sub_le_self _ (by positivity)) _
      _ = (R ^ k) ^ (k + 1) := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ < (R ^ k + r ^ k) ^ (k + 1) :=
          pow_lt_pow_left₀ (lt_add_of_pos_right _ (pow_pos hr k)) (pow_pos (hr.trans h) k).le
            k.succ_ne_zero

/-- **The perimeter of two separated balls.** Balls of radii `r₁, r₂ > 0` whose centres are at
distance more than `r₁ + r₂` have disjoint closures, so in dimension `n` their union
has perimeter `n (r₁^(n-1) + r₂^(n-1)) μ (ball 0 1)`. -/
theorem perimeter_ball_union_ball {c₁ c₂ : E} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h : r₁ + r₂ < dist c₁ c₂) :
    perimeter μ ⊤ (ball c₁ r₁ ∪ ball c₂ r₂) = finrank ℝ E *
      ENNReal.ofReal (r₁ ^ (finrank ℝ E - 1) + r₂ ^ (finrank ℝ E - 1)) * μ (ball 0 1) := by
  rw [perimeter_union_of_disjoint_closure measurableSet_ball.nullMeasurableSet
      measurableSet_ball.nullMeasurableSet ((closedBall_disjoint_closedBall h).mono
        closure_ball_subset_closedBall closure_ball_subset_closedBall),
    perimeter_ball hr₁, perimeter_ball hr₂, ENNReal.ofReal_add (by positivity) (by positivity)]
  ring

/-- **Two separated balls are a strict isoperimetric example.** In dimension `n ≥ 1`, balls of radii
`r₁, r₂ > 0` whose centres are at distance more than `r₁ + r₂` have a union `B` with
`n^n μ (ball 0 1) μ B^(n-1) < P(B)^n`. -/
theorem finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_ball_union_ball_pow
    (hn : finrank ℝ E ≠ 0) {c₁ c₂ : E} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h : r₁ + r₂ < dist c₁ c₂) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * μ (ball 0 1) *
        μ (ball c₁ r₁ ∪ ball c₂ r₂) ^ (finrank ℝ E - 1) <
      perimeter μ ⊤ (ball c₁ r₁ ∪ ball c₂ r₂) ^ finrank ℝ E := by
  refine finrank_pow_mul_measure_ball_mul_measure_pow_lt_perimeter_pow_of_lt hn
    (v := r₁ ^ finrank ℝ E + r₂ ^ finrank ℝ E) (by positivity) (by positivity)
    (perimeter_ball_union_ball hr₁ hr₂ h) ?_ ?_
  · rw [measure_union (ball_disjoint_ball h.le) measurableSet_ball, μ.addHaar_ball_of_pos _ hr₁,
      μ.addHaar_ball_of_pos _ hr₂, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_one_of_ne_zero hn
    rw [hk, Nat.add_sub_cancel]
    -- Both sides compare with `max r₁ r₂ ^ k * (r₁ ^ k + r₂ ^ k) ^ k`.
    have h₁ : r₁ ^ (k + 1) + r₂ ^ (k + 1) ≤ max r₁ r₂ * (r₁ ^ k + r₂ ^ k) := by
      rw [pow_succ', pow_succ', mul_add]
      gcongr
      exacts [le_max_left r₁ r₂, le_max_right r₁ r₂]
    have h₂ : max r₁ r₂ ^ k < r₁ ^ k + r₂ ^ k := by
      rcases max_choice r₁ r₂ with hmax | hmax <;> rw [hmax]
      · exact lt_add_of_pos_right _ (pow_pos hr₂ k)
      · exact lt_add_of_pos_left _ (pow_pos hr₁ k)
    calc (r₁ ^ (k + 1) + r₂ ^ (k + 1)) ^ k ≤ (max r₁ r₂ * (r₁ ^ k + r₂ ^ k)) ^ k :=
          pow_le_pow_left₀ (by positivity) h₁ _
      _ = max r₁ r₂ ^ k * (r₁ ^ k + r₂ ^ k) ^ k := mul_pow _ _ _
      _ < (r₁ ^ k + r₂ ^ k) * (r₁ ^ k + r₂ ^ k) ^ k :=
          mul_lt_mul_of_pos_right h₂ (by positivity)
      _ = (r₁ ^ k + r₂ ^ k) ^ (k + 1) := (pow_succ' _ _).symm

/-- **The punctured ball is an isoperimetric equality case.** In a nontrivial space of dimension
`n`, the punctured ball `ball c r \ {c}`, `r > 0`, satisfies
`P(ball c r \ {c})^n = n^n μ (ball 0 1) μ (ball c r \ {c})^(n-1)`, since it agrees with
`ball c r` up to a null set. It is nevertheless not a ball
(`TauCeti.ball_sdiff_singleton_ne_ball`, `TauCeti.ball_sdiff_singleton_ne_closedBall`): equality
in the isoperimetric inequality only determines a set up to null sets. -/
theorem perimeter_ball_sdiff_singleton_pow [Nontrivial E] (hr : 0 < r) :
    perimeter μ ⊤ (ball c r \ {c}) ^ finrank ℝ E =
      finrank ℝ E ^ finrank ℝ E * μ (ball 0 1) * μ (ball c r \ {c}) ^ (finrank ℝ E - 1) := by
  rw [perimeter_congr_ae (ae_restrict_of_ae (sdiff_null_ae_eq_self (measure_singleton c))),
    measure_congr (sdiff_null_ae_eq_self (measure_singleton c)),
    perimeter_ball_pow finrank_pos.ne' hr]

end TauCeti
