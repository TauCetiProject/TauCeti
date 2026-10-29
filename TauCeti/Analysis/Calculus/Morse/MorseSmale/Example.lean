/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.MorseSmale.Manifold

/-!
# A Morse–Smale function on the plane

The function `f(x, y) = cos x + y² / 2` on `ℝ²` has globally Lipschitz gradient
`∇f(x, y) = (-sin x, y)`. Its critical points are the points `(kπ, 0)`, `k ∈ ℤ`, all nondegenerate:
saddles of Morse index `1` for even `k` and minima of Morse index `0` for odd `k`. Its
negative-gradient flow is Morse–Smale. Along an orbit the second coordinate is `y₀ e^{-t}`, so an
unstable set lies on the `x`-axis; the first coordinate solves `x' = sin x`, for which the saddle
values `2πm` are repelling, so the stable set of a saddle is the vertical line through it. Hence
the unstable set of a saddle `p` and the stable set of a saddle `q` meet only if `p = q`, and then
only at that saddle. There the unstable set is tangent to the horizontal direction and the stable
set is the vertical line, so the tangent spaces are the horizontal and vertical directions. The
stable set of a minimum has two-dimensional tangent spaces at each of its points.

For a saddle `p` and a minimum `q` (for instance `(0, 0)` and `(π, 0)`), the set of points on
trajectories from `p` to `q` is a manifold of dimension `1`, and its level slices are manifolds of
dimension `0`.

## Main results

* `TauCeti.lipschitzWith_gradient_cosAddHalfSq`: the gradient is `1`-Lipschitz.
* `TauCeti.fderiv_cosAddHalfSq_eq_zero_iff`, `TauCeti.isNondegenerateCriticalPoint_cosAddHalfSq`,
  `TauCeti.hasNondegenerateCriticalPointsOn_cosAddHalfSq`,
  `TauCeti.morseIndex_cosAddHalfSq_of_cos_eq_one`,
  `TauCeti.morseIndex_cosAddHalfSq_of_cos_eq_neg_one`: the critical points, their nondegeneracy
  and their Morse indices.
* `TauCeti.isMorseSmale_cosAddHalfSq`: the negative-gradient flow of `cosAddHalfSq` is
  Morse–Smale.
* `TauCeti.exists_isManifold_cosAddHalfSq_saddle_min` and
  `TauCeti.exists_isManifold_cosAddHalfSq_saddle_min_level`: the dimension formulas for a saddle
  and a minimum.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014.
-/

public section

open Set Filter Topology InnerProductSpace
open scoped Gradient NNReal RealInnerProductSpace Manifold

namespace TauCeti

/-- The function `cos x + y² / 2` on the Euclidean plane. -/
noncomputable def cosAddHalfSq (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.cos (z 0) + z 1 ^ 2 / 2

@[simp]
theorem cosAddHalfSq_apply (z : EuclideanSpace ℝ (Fin 2)) :
    cosAddHalfSq z = Real.cos (z 0) + z 1 ^ 2 / 2 :=
  (rfl)

/-- The gradient field `(-sin x, y)`. -/
private noncomputable def gradField (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-Real.sin (z 0), z 1]

@[simp]
private theorem gradField_apply_zero (z : EuclideanSpace ℝ (Fin 2)) :
    gradField z 0 = -Real.sin (z 0) := rfl

@[simp]
private theorem gradField_apply_one (z : EuclideanSpace ℝ (Fin 2)) : gradField z 1 = z 1 := rfl

/-- The function `cos x + y² / 2` is smooth: it is `C^n` for every differentiability order `n`. -/
theorem contDiff_cosAddHalfSq {n : WithTop ℕ∞} : ContDiff ℝ n cosAddHalfSq :=
  (Real.contDiff_cos.comp (EuclideanSpace.proj (0 : Fin 2)).contDiff).add
    (((EuclideanSpace.proj (1 : Fin 2)).contDiff.pow 2).div_const 2)

private theorem hasGradientAt_cosAddHalfSq (z : EuclideanSpace ℝ (Fin 2)) :
    HasGradientAt cosAddHalfSq (gradField z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 := (Real.hasDerivAt_cos (z 0)).comp_hasFDerivAt z
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt
  have h1 := (((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt
    (x := z)).pow 2).const_smul (1 / 2 : ℝ)
  have e : cosAddHalfSq = fun w ↦ (Real.cos ∘ (EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) → ℝ)) w + (1 / 2 : ℝ) • ((EuclideanSpace.proj (1 : Fin 2) :
        EuclideanSpace ℝ (Fin 2) → ℝ) w ^ 2) := by
    funext w
    simp [cosAddHalfSq]
    ring
  rw [e]
  convert h0.add h1 using 1
  ext w
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The gradient of `cos x + y² / 2` is `(-sin x, y)`. -/
private theorem gradient_cosAddHalfSq : ∇ cosAddHalfSq = gradField :=
  funext fun z ↦ (hasGradientAt_cosAddHalfSq z).gradient

/-- The first coordinate of the gradient is `-sin x`. -/
@[simp]
theorem gradient_cosAddHalfSq_apply_zero (z : EuclideanSpace ℝ (Fin 2)) :
    ∇ cosAddHalfSq z 0 = -Real.sin (z 0) := by
  rw [gradient_cosAddHalfSq, gradField_apply_zero]

/-- The second coordinate of the gradient is `y`. -/
@[simp]
theorem gradient_cosAddHalfSq_apply_one (z : EuclideanSpace ℝ (Fin 2)) :
    ∇ cosAddHalfSq z 1 = z 1 := by
  rw [gradient_cosAddHalfSq, gradField_apply_one]

/-- **The gradient is `1`-Lipschitz.** -/
theorem lipschitzWith_gradient_cosAddHalfSq : LipschitzWith 1 (∇ cosAddHalfSq) := by
  rw [gradient_cosAddHalfSq]
  refine LipschitzWith.of_dist_le_mul fun z w ↦ ?_
  rw [NNReal.coe_one, one_mul, EuclideanSpace.dist_eq, EuclideanSpace.dist_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.sum_univ_two, gradField_apply_zero, gradField_apply_one, Real.dist_eq]
  have := Real.abs_sin_sub_sin_le (z 0) (w 0)
  have h0 : |-Real.sin (z 0) - -Real.sin (w 0)| ^ 2 ≤ |z 0 - w 0| ^ 2 := by
    rw [neg_sub_neg, abs_sub_comm]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  linarith

/-- The basis vectors of the plane. -/
private noncomputable abbrev e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

private noncomputable abbrev e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1

private theorem gradField_eq (w : EuclideanSpace ℝ (Fin 2)) :
    gradField w = (-Real.sin (w 0)) • e₀ + w 1 • e₁ := by
  ext i
  fin_cases i <;> simp

/-- The derivative of the gradient field: `(u₀, u₁) ↦ (-cos x · u₀, u₁)`. -/
private noncomputable def hessField (z : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((-Real.cos (z 0)) • (EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)).smulRight e₀ +
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).smulRight e₁

private theorem hessField_apply (z u : EuclideanSpace ℝ (Fin 2)) :
    hessField z u = (-Real.cos (z 0) * u 0) • e₀ + u 1 • e₁ := by
  simp [hessField]

/-- The Hessian operator of `cos x + y² / 2`. -/
private theorem hessianOperator_cosAddHalfSq (z : EuclideanSpace ℝ (Fin 2)) :
    hessianOperator cosAddHalfSq z = hessField z := by
  rw [← fderiv_gradient, gradient_cosAddHalfSq]
  have h0 := ((Real.hasDerivAt_sin (z 0)).comp_hasFDerivAt z
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt).neg.smul_const
      e₀
  have h1 := (EuclideanSpace.proj (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt (x := z) |>.smul_const e₁
  have hG : HasFDerivAt gradField (hessField z) z := by
    convert h0.add h1 using 1
    · funext w
      simp [gradField_eq]
    · ext u i
      fin_cases i <;> simp [hessField]
  exact hG.fderiv

/-- The value of the Hessian quadratic form: `-cos x · u₀² + u₁²`. -/
theorem hessianQuadraticForm_cosAddHalfSq (z u : EuclideanSpace ℝ (Fin 2)) :
    hessianQuadraticForm cosAddHalfSq z u = -Real.cos (z 0) * u 0 ^ 2 + u 1 ^ 2 := by
  rw [hessianQuadraticForm_apply, ← inner_hessianOperator_left, hessianOperator_cosAddHalfSq,
    hessField_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The critical points of `cos x + y² / 2` are the points with `sin x = 0` and `y = 0`. -/
@[simp]
theorem fderiv_cosAddHalfSq_eq_zero_iff {z : EuclideanSpace ℝ (Fin 2)} :
    fderiv ℝ cosAddHalfSq z = 0 ↔ Real.sin (z 0) = 0 ∧ z 1 = 0 := by
  have h : fderiv ℝ cosAddHalfSq z = 0 ↔ ∇ cosAddHalfSq z = 0 := by
    simp [gradient]
  rw [h, gradient_cosAddHalfSq, gradField_eq]
  constructor
  · intro h0
    have h0' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h0
    have h1' := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) h0
    exact ⟨by simpa using h0', by simpa using h1'⟩
  · rintro ⟨h0, h1⟩
    simp [h0, h1]

/-- **The critical points are nondegenerate.** -/
theorem isNondegenerateCriticalPoint_cosAddHalfSq {z : EuclideanSpace ℝ (Fin 2)}
    (hz : fderiv ℝ cosAddHalfSq z = 0) : IsNondegenerateCriticalPoint cosAddHalfSq z := by
  have hc : Real.cos (z 0) ≠ 0 := by
    rcases Real.sin_eq_zero_iff_cos_eq.1 (fderiv_cosAddHalfSq_eq_zero_iff.1 hz).1 with h | h <;>
      rw [h] <;> norm_num
  refine isNondegenerateCriticalPoint_iff_separatingLeft.2
    ⟨contDiff_cosAddHalfSq.contDiffAt, hz,
      (ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective _).2 fun v w hvw ↦ ?_⟩
  -- The Hessian bilinear form is `⟪hessField z v, w⟫`, and `hessField z` is injective.
  rw [← sub_eq_zero]
  have hB : fderiv ℝ (fderiv ℝ cosAddHalfSq) z (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hD : hessField z (v - w) = 0 := by
    have h2 : fderiv ℝ (fderiv ℝ cosAddHalfSq) z (v - w) (hessField z (v - w)) = 0 := by
      simp [hB]
    rw [← inner_hessianOperator_left, hessianOperator_cosAddHalfSq] at h2
    exact inner_self_eq_zero.1 h2
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hD
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hD
  simp only [hessField_apply] at h0 h1
  ext i
  fin_cases i
  · simpa [hc] using h0
  · simpa using h1

/-- **`cos x + y² / 2` is a Morse function**: every critical point is nondegenerate. -/
theorem hasNondegenerateCriticalPointsOn_cosAddHalfSq :
    HasNondegenerateCriticalPointsOn cosAddHalfSq univ :=
  hasNondegenerateCriticalPointsOn_iff.2 fun _ _ hz ↦ isNondegenerateCriticalPoint_cosAddHalfSq hz

/-- At a critical point with `cos x = -1`, the Morse index is `0`. -/
private theorem morseIndex_cosAddHalfSq_of_isCritical_of_cos_eq_neg_one
    {z : EuclideanSpace ℝ (Fin 2)} (hz : fderiv ℝ cosAddHalfSq z = 0) (hc : Real.cos (z 0) = -1) :
    morseIndex cosAddHalfSq z = 0 := by
  have hnd := isNondegenerateCriticalPoint_cosAddHalfSq hz
  refine hnd.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero.1 fun u hu ↦ ?_
  rw [hessianQuadraticForm_cosAddHalfSq, hc]
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    apply hu
    ext i
    fin_cases i
    · simpa using h.1
    · simpa using h.2
  rcases hne with h | h
  · nlinarith [pow_pos (abs_pos.2 h) 2, sq_abs (u 0), sq_nonneg (u 1)]
  · nlinarith [pow_pos (abs_pos.2 h) 2, sq_abs (u 1), sq_nonneg (u 0)]

/-- At a critical point with `cos x = 1`, the Morse index is `1`. -/
private theorem morseIndex_cosAddHalfSq_of_isCritical_of_cos_eq_one {z : EuclideanSpace ℝ (Fin 2)}
    (hz : fderiv ℝ cosAddHalfSq z = 0) (hc : Real.cos (z 0) = 1) :
    morseIndex cosAddHalfSq z = 1 := by
  have hnd := isNondegenerateCriticalPoint_cosAddHalfSq hz
  have h0 : morseIndex cosAddHalfSq z ≠ 0 := fun h ↦ by
    have := (hnd.hessianQuadraticForm_posDef_iff_morseIndex_eq_zero.2 h) e₀ (by simp)
    rw [hessianQuadraticForm_cosAddHalfSq, hc] at this
    norm_num at this
  have h2 : morseIndex cosAddHalfSq z ≠ 2 := fun h ↦ by
    have := (hnd.neg_hessianQuadraticForm_posDef_iff_morseIndex_eq_finrank.2
      (by rw [h, finrank_euclideanSpace_fin])) e₁ (by simp)
    rw [neg_apply, hessianQuadraticForm_cosAddHalfSq, hc] at this
    norm_num at this
  have hle : morseIndex cosAddHalfSq z ≤ 2 := by
    simpa using morseIndex_le_finrank (f := cosAddHalfSq) (x := z)
  omega

/-- The Morse index of `cos x + y² / 2` at a point depends only on `cos` of its first coordinate,
because so does the Hessian quadratic form; criticality in the second coordinate plays no role. -/
private theorem morseIndex_cosAddHalfSq_congr {z w : EuclideanSpace ℝ (Fin 2)}
    (h : Real.cos (z 0) = Real.cos (w 0)) :
    morseIndex cosAddHalfSq z = morseIndex cosAddHalfSq w := by
  rw [morseIndex_def, morseIndex_def]
  congr 1
  exact QuadraticMap.ext fun u ↦ by
    rw [hessianQuadraticForm_cosAddHalfSq, hessianQuadraticForm_cosAddHalfSq, h]

/-- The projection `(z 0, 0)` of `z` to the `x`-axis; it is critical when `sin (z 0) = 0`. -/
private noncomputable abbrev onAxis (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 0 (z 0)

private theorem fderiv_cosAddHalfSq_onAxis {z : EuclideanSpace ℝ (Fin 2)}
    (h : Real.cos (z 0) = 1 ∨ Real.cos (z 0) = -1) : fderiv ℝ cosAddHalfSq (onAxis z) = 0 := by
  refine fderiv_cosAddHalfSq_eq_zero_iff.2 ⟨?_, by simp⟩
  simpa using Real.sin_eq_zero_iff_cos_eq.2 h

/-- At a point with `cos x = -1`, a minimum when it is critical, the Morse index is `0`. -/
theorem morseIndex_cosAddHalfSq_of_cos_eq_neg_one {z : EuclideanSpace ℝ (Fin 2)}
    (hc : Real.cos (z 0) = -1) : morseIndex cosAddHalfSq z = 0 := by
  have hw : Real.cos (onAxis z 0) = -1 := by simpa using hc
  rw [morseIndex_cosAddHalfSq_congr (w := onAxis z) (by rw [hc, hw]),
    morseIndex_cosAddHalfSq_of_isCritical_of_cos_eq_neg_one
      (fderiv_cosAddHalfSq_onAxis (Or.inr hc)) hw]

/-- At a point with `cos x = 1`, a saddle when it is critical, the Morse index is `1`. -/
theorem morseIndex_cosAddHalfSq_of_cos_eq_one {z : EuclideanSpace ℝ (Fin 2)}
    (hc : Real.cos (z 0) = 1) : morseIndex cosAddHalfSq z = 1 := by
  have hw : Real.cos (onAxis z 0) = 1 := by simpa using hc
  rw [morseIndex_cosAddHalfSq_congr (w := onAxis z) (by rw [hc, hw]),
    morseIndex_cosAddHalfSq_of_isCritical_of_cos_eq_one
      (fderiv_cosAddHalfSq_onAxis (Or.inl hc)) hw]

/-- The negative-gradient flow of `cos x + y² / 2`. -/
local notation "Φ" => negativeGradientFlow cosAddHalfSq lipschitzWith_gradient_cosAddHalfSq

private theorem hasDerivAt_orbit (z : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    HasDerivAt (fun t ↦ Φ t z) (-gradField (Φ t z)) t := by
  have := (isNegativeGradient_negativeGradientFlow cosAddHalfSq
    lipschitzWith_gradient_cosAddHalfSq).isIntegralCurve z t
  beta_reduce at this
  rwa [gradient_cosAddHalfSq] at this

private theorem hasDerivAt_orbit_coord (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) (t : ℝ) :
    HasDerivAt (fun t ↦ Φ t z i) (-gradField (Φ t z) i) t := by
  exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
    t (hasDerivAt_orbit z t)

/-- Along an orbit, the second coordinate is `y₀ e^{-t}`. -/
private theorem orbit_apply_one (z : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    Φ t z 1 = z 1 * Real.exp (-t) := by
  have hd : ∀ s, HasDerivAt (fun s ↦ Real.exp s * Φ s z 1) 0 s := fun s ↦ by
    refine ((Real.hasDerivAt_exp s).mul (hasDerivAt_orbit_coord z 1 s)).congr_deriv ?_
    simp only [gradField_apply_one]
    ring
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt) (fun s ↦ (hd s).deriv)
    t 0
  simp only [Real.exp_zero, one_mul, Flow.map_zero_apply] at hc
  rw [← hc, mul_comm (Real.exp t), mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
    mul_one]

/-- A point of an unstable set of a critical point lies on the `x`-axis. -/
private theorem apply_one_eq_zero_of_mem_unstableSet {p z : EuclideanSpace ℝ (Fin 2)}
    (hp : p 1 = 0) (hz : z ∈ Flow.unstableSet Φ p) : z 1 = 0 := by
  rw [Flow.mem_unstableSet] at hz
  have h0 : (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) → ℝ) p = 0 := by
    simpa using hp
  have h1 := ((EuclideanSpace.proj (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.tendsto p).comp hz
  rw [h0] at h1
  have hlim : Tendsto (fun t ↦ |z 1 * Real.exp (-t)|) atBot (𝓝 0) := by
    have h2 := h1.abs
    rw [abs_zero] at h2
    refine h2.congr fun t ↦ ?_
    simp [orbit_apply_one]
  have hge : ∀ᶠ t in atBot, |z 1| ≤ |z 1 * Real.exp (-t)| := by
    filter_upwards [eventually_le_atBot 0] with t ht
    rw [abs_mul, Real.abs_exp]
    exact le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (by linarith))
  have := ge_of_tendsto hlim hge
  exact abs_nonpos_iff.1 this

/-- The vertical line `{x = a}` through a zero of `sin` is invariant, with explicit orbits. -/
private theorem orbit_vertical {a : ℝ} (ha : Real.sin a = 0) (y s : ℝ) :
    Φ s (a • e₀ + y • e₁) = a • e₀ + (y * Real.exp (-s)) • e₁ := by
  set c : ℝ → EuclideanSpace ℝ (Fin 2) := fun s ↦ a • e₀ + (y * Real.exp (-s)) • e₁
  have hc : IsIntegralCurve c fun _ w ↦ -∇ cosAddHalfSq w := fun s ↦ by
    rw [gradient_cosAddHalfSq]
    have hy := (((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s)).const_mul y).smul_const e₁
    have h0 : HasDerivAt c (0 + (y * (Real.exp (-s) * -1)) • e₁) s :=
      (hasDerivAt_const s (a • e₀)).add hy
    refine h0.congr_deriv ?_
    beta_reduce
    ext i
    fin_cases i <;> simp [c, gradField_eq, ha]
  have := eq_negativeGradientFlow cosAddHalfSq lipschitzWith_gradient_cosAddHalfSq hc s
  simpa [c] using this.symm

/-- **The stable set of a saddle lies on a vertical line.** A point of the stable set of a critical
point `q` with `cos (q 0) = 1` has first coordinate `q 0`: for `x' = sin x` the value `q 0` is
repelling. -/
private theorem apply_zero_eq_of_mem_stableSet {q z : EuclideanSpace ℝ (Fin 2)}
    (hs : Real.sin (q 0) = 0) (hc : Real.cos (q 0) = 1) (hz : z ∈ Flow.stableSet Φ q) :
    z 0 = q 0 := by
  rw [Flow.mem_stableSet] at hz
  set D : ℝ → ℝ := fun t ↦ Φ t z 0 - q 0 with hDdef
  have hD' : ∀ t, HasDerivAt D (Real.sin (D t)) t := fun t ↦ by
    refine ((hasDerivAt_orbit_coord z 0 t).sub_const (q 0)).congr_deriv ?_
    simp only [gradField_apply_zero, neg_neg, hDdef, Real.sin_sub, hs, hc]
    ring
  have hD : Tendsto D atTop (𝓝 0) := by
    have h1 := ((EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.tendsto q).comp hz
    have h2 : Tendsto D atTop
        (𝓝 ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) → ℝ) q - q 0)) :=
      h1.sub_const (q 0)
    simpa using h2
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 (hD.eventually (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1)))
  -- `D²` is nondecreasing on `[T₀, ∞)`, since `D sin D ≥ 0` for `|D| < 1`.
  have hmono : MonotoneOn (fun t ↦ D t ^ 2) (Ici T₀) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t ↦ 2 * D t * Real.sin (D t))
      (convex_Ici T₀) ((continuous_iff_continuousAt.2 fun t ↦ (hD' t).continuousAt).pow 2
        |>.continuousOn) (fun t _ ↦ ?_) fun t ht ↦ ?_
    · have := ((hD' t).pow 2).hasDerivWithinAt (s := interior (Ici T₀))
      convert this using 1
      ring
    · rw [interior_Ici] at ht
      obtain ⟨h1, h2⟩ := hT₀ t (le_of_lt ht)
      have hπ := Real.two_le_pi
      rcases le_total 0 (D t) with h | h
      · exact mul_nonneg (by linarith) (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))
      · exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith))
  have hT : D T₀ ^ 2 ≤ 0 := by
    have hlim : Tendsto (fun t ↦ D t ^ 2) atTop (𝓝 0) := by simpa using hD.pow 2
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop T₀] with t ht
    exact hmono (Set.mem_Ici.2 le_rfl) ht ht
  have hDT : D T₀ = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hT (sq_nonneg _))
  -- From time `T₀` on, the orbit runs along the vertical line through `q`.
  have hw : Φ T₀ z = q 0 • e₀ + Φ T₀ z 1 • e₁ := by
    have h0 : Φ T₀ z 0 = q 0 := by simpa [hDdef, sub_eq_zero] using hDT
    ext i
    fin_cases i <;> simp [h0]
  have hv := orbit_vertical hs (Φ T₀ z 1) (-T₀)
  rw [← hw, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply] at hv
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hv

/-- A critical point is fixed by the flow. -/
private theorem orbit_eq_self {z : EuclideanSpace ℝ (Fin 2)} (hz : fderiv ℝ cosAddHalfSq z = 0)
    (t : ℝ) : Φ t z = z := by
  refine (forall_negativeGradientFlow_eq_self_iff _ _ z).2 ?_ t
  simp [gradient, hz]

/-- **Transversality at a saddle.** At a critical point `q` with `cos (q 0) = 1`, the span of the
tangent cone of the unstable set lies in the `x`-axis (and is a line), and the tangent cone of the
stable set contains the vertical direction, so together the two spans are the whole plane. -/
private theorem span_sup_span_eq_top_of_saddle {q : EuclideanSpace ℝ (Fin 2)}
    (hq : fderiv ℝ cosAddHalfSq q = 0) (hc : Real.cos (q 0) = 1) :
    Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet Φ q) q) ⊔
      Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet Φ q) q) = ⊤ := by
  have hqc := fderiv_cosAddHalfSq_eq_zero_iff.1 hq
  have hnd := isNondegenerateCriticalPoint_cosAddHalfSq hq
  set U := Submodule.span ℝ (tangentConeAt ℝ (Flow.unstableSet Φ q) q)
  set K := LinearMap.ker (EuclideanSpace.proj (1 : Fin 2) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).toLinearMap
  have hqu : q ∈ Flow.unstableSet Φ q := Flow.self_mem_unstableSet_iff.2 (orbit_eq_self hq)
  -- The unstable set lies on the `x`-axis `K`, so `U ≤ K`, and `U` is a line.
  have hUK : U ≤ K := by
    refine Submodule.span_le.2 ?_
    have hsub : Flow.unstableSet Φ q ⊆ (K : Set (EuclideanSpace ℝ (Fin 2))) := fun z hz ↦ by
      simpa [K] using apply_one_eq_zero_of_mem_unstableSet hqc.2 hz
    have hKc : IsClosed (K : Set (EuclideanSpace ℝ (Fin 2))) :=
      (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).isClosed_ker
    have hqK : q ∈ K := by simpa [K] using hqc.2
    calc tangentConeAt ℝ (Flow.unstableSet Φ q) q
        ⊆ tangentConeAt ℝ (K : Set (EuclideanSpace ℝ (Fin 2))) q := tangentConeAt_mono hsub
      _ = K := Submodule.tangentConeAt_eq K hKc hqK
  have hUdim : Module.finrank ℝ U = 1 := by
    rw [hnd.finrank_span_tangentConeAt_unstableSet contDiff_cosAddHalfSq
      lipschitzWith_gradient_cosAddHalfSq hqu, morseIndex_cosAddHalfSq_of_cos_eq_one hc]
  -- The vertical direction is tangent to the stable set.
  have he₁ : e₁ ∈ Submodule.span ℝ (tangentConeAt ℝ (Flow.stableSet Φ q) q) := by
    have hq' : q = q 0 • e₀ + (0 : ℝ) • e₁ := by
      ext i
      fin_cases i <;> simp [hqc.2]
    have hmem : ∀ s : ℝ, q 0 • e₀ + s • e₁ ∈ Flow.stableSet Φ q := fun s ↦ by
      rw [Flow.mem_stableSet]
      simp only [orbit_vertical hqc.1]
      have h := (tendsto_const_nhds (x := q 0 • e₀)).add
        ((Real.tendsto_exp_neg_atTop_nhds_zero.const_mul s).smul_const e₁)
      rwa [mul_zero, ← hq'] at h
    have hγ : HasDerivAt (fun s : ℝ ↦ q 0 • e₀ + s • e₁) e₁ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e₁).const_add (q 0 • e₀)
    have := hγ.mem_tangentConeAt (S := Flow.stableSet Φ q) (Eventually.of_forall hmem)
    beta_reduce at this
    rw [← hq'] at this
    exact Submodule.subset_span this
  -- `U` and the vertical line together span the plane.
  have hinf : U ⊓ ℝ ∙ e₁ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun v ⟨hvU, hv₁⟩ ↦ ?_
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv₁
    have := hUK hvU
    simp [K] at this
    simp [this]
  have hsup : U ⊔ ℝ ∙ e₁ = ⊤ :=
    Submodule.eq_top_of_disjoint U (ℝ ∙ e₁)
      (by rw [hUdim, finrank_span_singleton (by simp), finrank_euclideanSpace_fin])
      (disjoint_iff.2 hinf)
  exact top_unique (hsup ▸ sup_le_sup_left (Submodule.span_le.2 (by simpa using he₁)) U)

/-- **`cos x + y² / 2` is Morse–Smale.** For all critical points `p` and `q`, the unstable set of
`p` and the stable set of `q` of its negative-gradient flow are transverse at every common
point. -/
theorem isMorseSmale_cosAddHalfSq :
    IsMorseSmale cosAddHalfSq lipschitzWith_gradient_cosAddHalfSq := by
  refine IsMorseSmale.of_forall fun p q y hp hq ⟨hyu, hys⟩ ↦ ?_
  replace hp := hp.fderiv_eq_zero
  replace hq := hq.fderiv_eq_zero
  have hpc := fderiv_cosAddHalfSq_eq_zero_iff.1 hp
  have hqc := fderiv_cosAddHalfSq_eq_zero_iff.1 hq
  have hcos : Real.cos (q 0) = 1 ∨ Real.cos (q 0) = -1 := Real.sin_eq_zero_iff_cos_eq.1 hqc.1
  rcases hcos with hc | hc
  · -- `q` is a saddle: then `y = q`, and `p = q`.
    have hy0 := apply_zero_eq_of_mem_stableSet hqc.1 hc hys
    have hy1 := apply_one_eq_zero_of_mem_unstableSet hpc.2 hyu
    have hyq : y = q := by
      ext i
      fin_cases i
      · exact hy0
      · simpa [hqc.2] using hy1
    subst hyq
    have hpy : p = y := by
      rw [Flow.mem_unstableSet] at hyu
      simp only [orbit_eq_self hq] at hyu
      exact (tendsto_nhds_unique tendsto_const_nhds hyu).symm
    subst hpy
    exact span_sup_span_eq_top_of_saddle hp hc
  · -- `q` is a minimum: its stable set has full-dimensional tangent spaces.
    have hnd := isNondegenerateCriticalPoint_cosAddHalfSq hq
    have h := hnd.finrank_span_tangentConeAt_stableSet_add_morseIndex contDiff_cosAddHalfSq
      lipschitzWith_gradient_cosAddHalfSq hys
    rw [morseIndex_cosAddHalfSq_of_cos_eq_neg_one hc, add_zero] at h
    rw [Submodule.eq_top_of_finrank_eq h, sup_top_eq]

variable {p q : EuclideanSpace ℝ (Fin 2)}

/-- **The connecting locus from a saddle to a minimum is a manifold of dimension `1`.** For a
saddle `p` (`cos (p 0) = 1`) and a minimum `q` (`cos (q 0) = -1`), the set
`W^u(p) ∩ W^s(q)` of points on trajectories from `p` to `q` is a `C¹` manifold of dimension
`1 = morseIndex p - morseIndex q`, modelled on any one-dimensional subspace, with `C¹` inclusion
into the plane; for example `p = (0, 0)` and `q = (π, 0)`. -/
theorem exists_isManifold_cosAddHalfSq_saddle_min (hp : fderiv ℝ cosAddHalfSq p = 0)
    (hpc : Real.cos (p 0) = 1) (hq : fderiv ℝ cosAddHalfSq q = 0) (hqc : Real.cos (q 0) = -1)
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin 2))} (hL : Module.finrank ℝ L = 1) :
    ∃ C : ChartedSpace L ↥(Flow.unstableSet Φ p ∩ Flow.stableSet Φ q), letI := C
      IsManifold 𝓘(ℝ, L) 1 ↥(Flow.unstableSet Φ p ∩ Flow.stableSet Φ q) ∧
      ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 1
        (Subtype.val : ↥(Flow.unstableSet Φ p ∩ Flow.stableSet Φ q) →
          EuclideanSpace ℝ (Fin 2)) := by
  refine isMorseSmale_cosAddHalfSq.exists_isManifold_unstableSet_inter_stableSet
    contDiff_cosAddHalfSq (isNondegenerateCriticalPoint_cosAddHalfSq hp)
    (isNondegenerateCriticalPoint_cosAddHalfSq hq) ?_
  rw [hL, morseIndex_cosAddHalfSq_of_cos_eq_one hpc,
    morseIndex_cosAddHalfSq_of_cos_eq_neg_one hqc]

/-- **Level slices of the connecting locus from a saddle to a minimum are manifolds of dimension
`0`.** For a saddle `p` and a minimum `q`, each level slice `W^u(p) ∩ W^s(q) ∩ {f = c}` is a
`C¹` manifold of dimension `0`, modelled on any subspace of dimension `0`, and its inclusion into
the plane is `C¹`. -/
theorem exists_isManifold_cosAddHalfSq_saddle_min_level (hp : fderiv ℝ cosAddHalfSq p = 0)
    (hpc : Real.cos (p 0) = 1) (hq : fderiv ℝ cosAddHalfSq q = 0) (hqc : Real.cos (q 0) = -1)
    {L : Submodule ℝ (EuclideanSpace ℝ (Fin 2))} (hL : Module.finrank ℝ L = 0) (c : ℝ) :
    ∃ C : ChartedSpace L ↥(Flow.unstableSet Φ p ∩ Flow.stableSet Φ q ∩
        {x | cosAddHalfSq x = c}), letI := C
      IsManifold 𝓘(ℝ, L) 1 ↥(Flow.unstableSet Φ p ∩ Flow.stableSet Φ q ∩
        {x | cosAddHalfSq x = c}) ∧
      ContMDiff 𝓘(ℝ, L) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 1
        (Subtype.val : ↥(Flow.unstableSet Φ p ∩ Flow.stableSet Φ q ∩
          {x | cosAddHalfSq x = c}) → EuclideanSpace ℝ (Fin 2)) := by
  refine isMorseSmale_cosAddHalfSq.exists_isManifold_unstableSet_inter_stableSet_level
    contDiff_cosAddHalfSq (isNondegenerateCriticalPoint_cosAddHalfSq hp)
    (isNondegenerateCriticalPoint_cosAddHalfSq hq) ?_
  rw [hL, morseIndex_cosAddHalfSq_of_cos_eq_one hpc,
    morseIndex_cosAddHalfSq_of_cos_eq_neg_one hqc]

end TauCeti
