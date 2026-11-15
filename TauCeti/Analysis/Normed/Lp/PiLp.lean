/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Comparisons of finite product norms and distances

The finite `Lᵖ` norm is nonnegative for every exponent and respects coordinatewise bounds on
norms, including when the two families have different target spaces. This compares scalar
evaluations of a vector family with the vector family's `Lᵖ` norm. For constant fibres we
deduce the bound for the image of a family under a map of bounded growth, the norm of a family
of multiples of one vector, and the invariance of the norm under reindexing.

For `p ≥ 1`, the `Lᵖ` distance dominates the sup distance. In the other direction, the `L²`
distance is at most the square root of the number of coordinates times the sup distance.
These estimates give inclusions between balls in the two metrics. The corresponding
Cauchy–Schwarz estimate bounds the sum of coordinate norms by `√(card ι)` times the `L²` norm.
The coordinate spaces may be different seminormed groups, or pseudometric spaces for the
distance comparisons.

Extending a vector of `Lᵖ(ι, E)` by zero along an embedding `f : ι ↪ ι'` places its coordinate `i`
in the slot `f i`, and the vectors so obtained are those whose coordinates outside the range of
`f` vanish. In particular, extending a vector of `Lᵖ(Fin k, E)` by zero onto the first `k`
coordinates of `Lᵖ(Fin n, E)`, for `k ≤ n`, places its coordinates in the slots `j < k`; the
vectors so obtained are those whose coordinates `j ≥ k` vanish.
The finite sum against a zero-extended vector reduces to the sum over its original coordinates.
Over an index type with at most one element, the `Lᵖ` norm is the norm of the coordinate.

A family of coordinatewise linear isometries induces a linear isometry between finite `Lᵖ`
products (`LinearIsometry.piLpCongrRight`), the non-surjective counterpart of
`LinearIsometryEquiv.piLpCongrRight`. Finally, over any nontrivially normed field `𝕜`, summing
coordinate evaluations identifies `PiLp ∞ (fun i ↦ StrongDual 𝕜 (E i))` isometrically with the
continuous dual of `PiLp 1 E` (`PiLp.oneDualEquiv`).

## Source

The coordinate-norm estimate is adapted from
`ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} {E F : ι → Type*}

/-- Coordinatewise domination of norms implies domination of finite `Lᵖ` norms.
The dominating family only needs a norm: the coordinate bounds ensure its nonnegativity. -/
theorem norm_mono [∀ i, SeminormedAddGroup (E i)] [∀ i, Norm (F i)]
    {x : PiLp p E} {y : PiLp p F}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [norm_eq_card, norm_eq_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    apply Set.Finite.toFinset_mono
    intro i hi hzero
    exact hi (le_antisymm (by simpa only [hzero] using h i) (norm_nonneg _))
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [norm_eq_ciSup, norm_eq_ciSup]
    exact ciSup_mono (Set.finite_range _).bddAbove h
  · simp only [norm_eq_sum (ENNReal.toReal_pos hp0 hp)]
    gcongr
    · exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    · exact h _

/-- The finite `Lᵖ` norm is nonnegative for every exponent, including `p < 1`, where `PiLp p E`
carries a norm but no seminormed group structure. -/
protected theorem norm_nonneg' [∀ i, SeminormedAddGroup (E i)] (x : PiLp p E) : 0 ≤ ‖x‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · rw [norm_eq_card]
    positivity
  · rw [norm_eq_ciSup]
    exact Real.iSup_nonneg fun i ↦ norm_nonneg _
  · rw [norm_eq_sum hp]
    exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

variable [∀ i, SeminormedAddCommGroup (E i)]

/-- Taking coordinate norms preserves the finite `Lᵖ` norm. -/
@[simp]
theorem norm_norm (x : PiLp p E) :
    ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ = ‖x‖ :=
  le_antisymm (norm_mono fun i ↦ by simp) (norm_mono fun i ↦ by simp)

/-- The sum of coordinate norms of a vector is at most `√(card ι)` times its `L²` norm. -/
theorem sum_norm_le_sqrt_card_mul_norm (x : PiLp 2 E) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  simpa [PiLp.norm_eq_of_L2] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι ↦ 1) (fun i ↦ ‖x i‖)

/-- Reindexing a finite family along an equivalence preserves its `Lᵖ` norm, for every
exponent. -/
theorem norm_toLp_comp_equiv {E : Type*} [SeminormedAddCommGroup E] {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (x : ι → E) : ‖WithLp.toLp p (x ∘ e)‖ = ‖WithLp.toLp p x‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · simp only [norm_eq_card, Set.toFinite_toFinset, Set.toFinset_card]
    exact congrArg Nat.cast (Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl))
  · simp only [norm_eq_ciSup]
    exact e.iSup_congr fun _ ↦ rfl
  · simp only [norm_eq_sum hp]
    exact congrArg (· ^ _) (Fintype.sum_equiv e _ _ fun _ ↦ rfl)

/-- Over an index type with at most one element, a vector of `Lᵖ`, `p ≥ 1`, has the norm of
each of its coordinates. -/
theorem norm_apply_eq_norm [Fact (1 ≤ p)] [Subsingleton ι] (x : PiLp p E) (i : ι) :
    ‖x i‖ = ‖x‖ := by
  classical
  have hx : PiLp.single p i (x i) = x :=
    PiLp.ext fun j ↦ by obtain rfl := Subsingleton.elim i j; simp
  rw [← hx, norm_single, hx]

section Constant

variable [Fact (1 ≤ p)] {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- Applying a map with `‖g v‖ ≤ C * ‖v‖` to each member of a finite family multiplies its
`Lᵖ` norm by at most `C`. -/
theorem norm_toLp_comp_le {g : E → F} {C : ℝ} (hg : ∀ v, ‖g v‖ ≤ C * ‖v‖)
    (x : ι → E) : ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ C * ‖WithLp.toLp p x‖ := by
  by_cases hC : 0 ≤ C
  · calc
      ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ ‖C • WithLp.toLp p (fun i ↦ ‖x i‖)‖ :=
        norm_mono fun i ↦ by simpa [abs_of_nonneg hC] using hg (x i)
      _ = C * ‖WithLp.toLp p x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_norm (WithLp.toLp p x)]
  · -- A negative constant forces every norm to vanish.
    have hv (v : E) : ‖v‖ = 0 :=
      le_antisymm (by nlinarith [norm_nonneg (g v), norm_nonneg v, hg v]) (norm_nonneg v)
    have hx : ‖WithLp.toLp p x‖ = 0 := le_antisymm
      (by simpa using norm_mono (y := (0 : PiLp p fun _ : ι ↦ E)) fun i ↦ by simp [hv])
      (norm_nonneg _)
    rw [hx, mul_zero]
    simpa using norm_mono (y := (0 : PiLp p fun _ : ι ↦ F))
      fun i ↦ by simpa [hv] using hg (x i)

/-- A finite family of multiples of one vector has `Lᵖ` norm equal to the `Lᵖ` norm of the
coefficients times the norm of the vector. -/
theorem norm_toLp_smul_const {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] (a : ι → 𝕜) (y : F) :
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖WithLp.toLp p a‖ * ‖y‖ := by
  calc
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖‖y‖ • WithLp.toLp p (fun i ↦ ‖a i‖)‖ :=
      le_antisymm (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
        (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
    _ = ‖WithLp.toLp p a‖ * ‖y‖ := by
      rw [norm_smul, _root_.norm_norm, norm_norm (WithLp.toLp p a), mul_comm]

end Constant

section PseudoMetricSpace

variable [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]

/-- The sup distance of the coordinate vectors is at most the `Lᵖ` distance, `p ≥ 1`. -/
theorem dist_ofLp_le (x y : PiLp p β) : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ dist x y := by
  simpa only [NNReal.coe_one, one_mul] using (lipschitzWith_ofLp p β).dist_le_mul x y

/-- The closed ball of radius `r` about `x` lies in the closed sup-metric ball of radius `r`
about `ofLp x`. -/
theorem closedBall_subset_preimage_ofLp_closedBall (x : PiLp p β) (r : ℝ) :
    Metric.closedBall x r ⊆ WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r := fun y hy ↦
  (dist_ofLp_le y x).trans hy

/-- The open ball of radius `r` about `x` lies in the open sup-metric ball of radius `r`
about `ofLp x`. -/
theorem ball_subset_preimage_ofLp_ball (x : PiLp p β) (r : ℝ) :
    Metric.ball x r ⊆ WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r := fun y hy ↦
  (dist_ofLp_le y x).trans_lt hy

/-- The `L²` distance is at most the square root of the coordinate count times the sup distance
between the coordinate vectors. -/
theorem dist_le_sqrt_card_mul_dist_ofLp (x y : PiLp 2 β) :
    dist x y ≤ Real.sqrt (Fintype.card ι) * dist (WithLp.ofLp x) (WithLp.ofLp y) := by
  simpa [NNReal.coe_rpow, Real.sqrt_eq_rpow] using
    (lipschitzWith_toLp 2 β).dist_le_mul (WithLp.ofLp x) (WithLp.ofLp y)

/-- A sup-metric closed ball of radius `r` pulls back into the `L²` closed ball of radius
`√(card ι) * r`. -/
theorem preimage_ofLp_closedBall_subset_closedBall (x : PiLp 2 β) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r ⊆
      Metric.closedBall x (Real.sqrt (Fintype.card ι) * r) := fun y hy ↦
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans
    (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))

/-- A sup-metric open ball of radius `r` pulls back into the `L²` open ball of radius
`√(card ι) * r`. The index type must be nonempty so that this scale factor is positive. -/
theorem preimage_ofLp_ball_subset_ball [Nonempty ι] (x : PiLp 2 β) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r ⊆
      Metric.ball x (Real.sqrt (Fintype.card ι) * r) := fun y hy ↦
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans_lt
    (mul_lt_mul_of_pos_left hy (Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)))

end PseudoMetricSpace

end PiLp

namespace PiLp

section OneDual

variable (𝕜 : Type*) {ι : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  (E : ι → Type*) [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- For a finite index type `ι`, the supremum-normed product
`PiLp ∞ (fun i ↦ StrongDual 𝕜 (E i))` is isometrically isomorphic to the continuous dual of the
sum-normed product `PiLp 1 E` via `φ ↦ (v ↦ ∑ i, φ i (v i))`. -/
noncomputable def oneDualEquiv :
    PiLp ∞ (fun i ↦ StrongDual 𝕜 (E i)) ≃ₗᵢ[𝕜] StrongDual 𝕜 (PiLp 1 E) where
  toFun φ := ∑ i, (φ i).comp
    ((ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 1 𝕜 E).toContinuousLinearMap)
  invFun :=
    letI := Classical.decEq ι
    fun Λ ↦ WithLp.toLp ∞ fun i ↦ Λ.comp
      ((PiLp.continuousLinearEquiv 1 𝕜 E).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single 𝕜 E i))
  map_add' _ _ := by
    ext v
    simp [Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext v
    simp [Finset.mul_sum]
  left_inv φ := by
    classical
    ext i u
    simp only [ContinuousLinearMap.comp_apply, sum_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  right_inv Λ := by
    classical
    ext v
    have hv : ∑ i, PiLp.single 1 i (v i) = v := by
      ext j
      simp [Finset.sum_apply]
    conv_rhs => rw [← hv, map_sum]
    simp
  norm_map' φ := by
    classical
    let Φ : StrongDual 𝕜 (PiLp 1 E) := ∑ i, (φ i).comp
      ((ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 1 𝕜 E).toContinuousLinearMap)
    have hΦ_single (i : ι) (u : E i) : Φ (PiLp.single 1 i u) = φ i u := by
      simp only [Φ, sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound Φ (norm_nonneg φ) fun v ↦ ?_
      simp only [Φ, sum_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
      calc ‖∑ i, φ i (v i)‖
          ≤ ∑ i, ‖φ i (v i)‖ := norm_sum_le _ _
        _ ≤ ∑ i, ‖φ i‖ * ‖v i‖ := Finset.sum_le_sum fun i _ ↦ (φ i).le_opNorm (v i)
        _ ≤ ∑ i, ‖φ‖ * ‖v i‖ :=
          Finset.sum_le_sum fun i _ ↦
            mul_le_mul_of_nonneg_right (PiLp.norm_apply_le φ i) (norm_nonneg _)
        _ = ‖φ‖ * ‖v‖ := by rw [← Finset.mul_sum, PiLp.norm_eq_of_L1]
    · rw [PiLp.norm_eq_ciSup]
      refine Real.iSup_le (fun i ↦ ?_) (norm_nonneg Φ)
      refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg Φ) fun u ↦ ?_
      rw [← hΦ_single i u]
      simpa using Φ.le_opNorm (PiLp.single 1 i u)

variable {𝕜 E}

/-- `PiLp.oneDualEquiv` acts by summing the coordinate evaluations `φ i (v i)`. -/
theorem oneDualEquiv_apply (φ : PiLp ∞ (fun i ↦ StrongDual 𝕜 (E i))) (v : PiLp 1 E) :
    oneDualEquiv 𝕜 E φ v = ∑ i, φ i (v i) := by
  simp [oneDualEquiv]

/-- On a single-coordinate vector `PiLp.single 1 i u`, `PiLp.oneDualEquiv φ` evaluates `φ i` at
`u`. -/
@[simp]
theorem oneDualEquiv_apply_single [DecidableEq ι] (φ : PiLp ∞ (fun i ↦ StrongDual 𝕜 (E i)))
    (i : ι) (u : E i) :
    oneDualEquiv 𝕜 E φ (PiLp.single 1 i u) = φ i u := by
  rw [oneDualEquiv_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- The `i`-th coordinate functional of `(PiLp.oneDualEquiv 𝕜 E).symm Λ` evaluates at `u` to
`Λ (PiLp.single 1 i u)`. -/
@[simp]
theorem oneDualEquiv_symm_apply [DecidableEq ι] (Λ : StrongDual 𝕜 (PiLp 1 E)) (i : ι) (u : E i) :
    (oneDualEquiv 𝕜 E).symm Λ i u = Λ (PiLp.single 1 i u) := by
  have h := congrArg (fun ψ : StrongDual 𝕜 (PiLp 1 E) ↦ ψ (PiLp.single 1 i u))
    ((oneDualEquiv 𝕜 E).apply_symm_apply Λ)
  simpa only [oneDualEquiv_apply_single] using h

/-- Each coordinate functional of `(PiLp.oneDualEquiv 𝕜 E).symm Λ` has norm at most `‖Λ‖`. -/
theorem norm_oneDualEquiv_symm_apply_le (Λ : StrongDual 𝕜 (PiLp 1 E)) (i : ι) :
    ‖(oneDualEquiv 𝕜 E).symm Λ i‖ ≤ ‖Λ‖ :=
  (PiLp.norm_apply_le ((oneDualEquiv 𝕜 E).symm Λ) i).trans_eq
    ((oneDualEquiv 𝕜 E).symm.norm_map Λ)

end OneDual

end PiLp

namespace LinearIsometry

section piLpCongrRight

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {𝕜 : Type*} [Semiring 𝕜] {ι : Type*} [Fintype ι]
  {α β γ : ι → Type*} [∀ i, SeminormedAddCommGroup (α i)] [∀ i, SeminormedAddCommGroup (β i)]
  [∀ i, SeminormedAddCommGroup (γ i)] [∀ i, Module 𝕜 (α i)] [∀ i, Module 𝕜 (β i)]
  [∀ i, Module 𝕜 (γ i)]

/-- A family of coordinatewise linear isometries induces a linear isometry between finite `Lᵖ`
products. This is the `LinearIsometry` counterpart of `LinearIsometryEquiv.piLpCongrRight`. -/
protected noncomputable def piLpCongrRight (f : ∀ i, α i →ₗᵢ[𝕜] β i) :
    PiLp p α →ₗᵢ[𝕜] PiLp p β where
  toLinearMap :=
    (WithLp.linearEquiv p 𝕜 (∀ i, β i)).symm.toLinearMap.comp
      ((LinearMap.pi fun i ↦ (f i).toLinearMap.comp (LinearMap.proj i)).comp
        (WithLp.linearEquiv p 𝕜 (∀ i, α i)).toLinearMap)
  norm_map' _ :=
    le_antisymm (PiLp.norm_mono fun i ↦ by simp) (PiLp.norm_mono fun i ↦ by simp)

variable {p}

@[simp]
theorem piLpCongrRight_apply (f : ∀ i, α i →ₗᵢ[𝕜] β i) (x : PiLp p α) (i : ι) :
    LinearIsometry.piLpCongrRight p f x i = f i (x i) :=
  (rfl)

theorem piLpCongrRight_eq_toLp (f : ∀ i, α i →ₗᵢ[𝕜] β i) (x : PiLp p α) :
    LinearIsometry.piLpCongrRight p f x = WithLp.toLp p fun i ↦ f i (x i) :=
  (rfl)

@[simp]
theorem piLpCongrRight_id :
    LinearIsometry.piLpCongrRight p (fun i ↦ (LinearIsometry.id : α i →ₗᵢ[𝕜] α i)) =
      LinearIsometry.id :=
  LinearIsometry.ext fun x ↦ PiLp.ext fun i ↦ by simp

theorem piLpCongrRight_comp (g : ∀ i, β i →ₗᵢ[𝕜] γ i) (f : ∀ i, α i →ₗᵢ[𝕜] β i) :
    LinearIsometry.piLpCongrRight p (fun i ↦ (g i).comp (f i)) =
      (LinearIsometry.piLpCongrRight p g).comp (LinearIsometry.piLpCongrRight p f) :=
  LinearIsometry.ext fun x ↦ PiLp.ext fun i ↦ by simp

@[simp]
theorem piLpCongrRight_single [DecidableEq ι] (f : ∀ i, α i →ₗᵢ[𝕜] β i) (i : ι) (v : α i) :
    LinearIsometry.piLpCongrRight p f (PiLp.single p i v) = PiLp.single p i (f i v) := by
  ext j
  rw [piLpCongrRight_apply]
  exact Pi.apply_single (f ·) (fun _ ↦ map_zero _) i v j

@[simp]
theorem _root_.LinearIsometryEquiv.piLpCongrRight_toLinearIsometry (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) :
    (LinearIsometryEquiv.piLpCongrRight p e).toLinearIsometry =
      LinearIsometry.piLpCongrRight p fun i ↦ (e i).toLinearIsometry :=
  LinearIsometry.ext fun x ↦ PiLp.ext fun i ↦ by simp

end piLpCongrRight

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E : Type*} [Semiring 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] {ι ι' : Type*} [Fintype ι] [Fintype ι'] {k n : ℕ}

/-- Extending a vector of `Lᵖ(ι, E)` by zero along an embedding `f : ι ↪ ι'` puts its coordinate
`i` in the slot `f i`. -/
theorem piLpExtendByZero_apply_apply (f : ι ↪ ι') (v : PiLp p fun _ : ι ↦ E) (i : ι) :
    piLpExtendByZero p 𝕜 E f v (f i) = v i := by
  simpa using f.injective.extend_apply (fun i ↦ v i) 0 i

/-- The vectors of `Lᵖ(ι', E)` obtained by extending a vector of `Lᵖ(ι, E)` by zero along an
embedding `f : ι ↪ ι'` are those whose coordinates outside the range of `f` vanish. -/
theorem range_piLpExtendByZero (f : ι ↪ ι') :
    Set.range (piLpExtendByZero p 𝕜 E f) =
      {y : PiLp p fun _ : ι' ↦ E | ∀ j ∉ Set.range f, y j = 0} := by
  refine Set.ext fun y ↦ ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨w, rfl⟩ j hj
    exact piLpExtendByZero_apply_eq_zero hj w
  · refine ⟨WithLp.toLp p fun i ↦ y (f i), PiLp.ext fun j ↦ ?_⟩
    by_cases hj : j ∈ Set.range f
    · obtain ⟨i, rfl⟩ := hj
      rw [piLpExtendByZero_apply_apply, PiLp.toLp_apply]
    · rw [piLpExtendByZero_apply_eq_zero hj, hy j hj]

/-- Extending a vector of `Lᵖ(Fin k, E)` by zero onto the first `k` coordinates of
`Lᵖ(Fin n, E)` puts its coordinates in the slots `j < k` and zeros elsewhere. -/
theorem piLpExtendByZero_castLEEmb_apply (hk : k ≤ n) (w : PiLp p fun _ : Fin k ↦ E)
    (j : Fin n) :
    piLpExtendByZero p 𝕜 E (Fin.castLEEmb hk) w j = if h : j.val < k then w ⟨j, h⟩ else 0 := by
  split_ifs with h
  · have hj : Fin.castLEEmb hk ⟨j, h⟩ = j := Fin.ext rfl
    conv_lhs => rw [← hj]
    exact piLpExtendByZero_apply_apply _ w _
  · exact piLpExtendByZero_apply_eq_zero (by simpa [Fin.range_castLE] using h) w

/-- The vectors of `Lᵖ(Fin n, E)` obtained by extending a vector of `Lᵖ(Fin k, E)` by zero are
those whose coordinates `j ≥ k` vanish. -/
theorem range_piLpExtendByZero_castLEEmb (hk : k ≤ n) :
    Set.range (piLpExtendByZero p 𝕜 E (Fin.castLEEmb hk)) =
      {y : PiLp p fun _ : Fin n ↦ E | ∀ j : Fin n, k ≤ j.val → y j = 0} := by
  simp [range_piLpExtendByZero, Fin.range_castLE]

end LinearIsometry

namespace LinearIsometry

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 : Type*} [NormedRing 𝕜]
  {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- A finite sum paired with a vector extended by zero along an embedding reduces to the sum over
the original coordinates. -/
theorem sum_mul_piLpExtendByZero (f : ι ↪ ι') (x : PiLp p fun _ : ι ↦ 𝕜) (h : ι' → 𝕜) :
    ∑ b, h b * piLpExtendByZero p 𝕜 𝕜 f x b = ∑ a, h (f a) * x a := by
  rw [← Finset.sum_extend_zero_of_injective (t := Finset.univ) (fun a ↦ h (f a) * x a)
    f.injective fun _ => Finset.mem_univ _]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hb
    simp [f.injective.extend_apply]
  · simp [Function.extend_apply' _ _ _ (by simpa using hb),
      piLpExtendByZero_apply_eq_zero hb]

end LinearIsometry
