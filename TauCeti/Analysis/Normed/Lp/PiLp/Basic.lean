/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Comparisons of finite product norms and distances

The finite `Lᵖ` norm is nonnegative for every exponent and respects coordinatewise bounds on
norms, including when the two families have different target spaces. This compares scalar
evaluations of a vector family with the vector family's `Lᵖ` norm. For constant fibres we
deduce the bound for the image of a family under a map of bounded growth, the norm of a family
of multiples of one vector (for `p ≠ 0`), and the invariance of the norm under reindexing. For
`p ≥ 1`, a linear combination `∑ i, s i • v i` with the coordinates of `s` as coefficients has
norm at most `‖s‖ * ∑ i, ‖v i‖`. For `p ≥ 1`, a real family with a positive coordinate has
positive `Lᵖ` norm (`PiLp.norm_toLp_pos`), and for `1 ≤ q < ∞` rescaling a positive family `c` to
`(‖c‖_q (c i / ‖c‖_q) ^ (q / p))_i` moves it from `ℓ^q` to `ℓ^p` without changing its norm
(`PiLp.norm_toLp_mul_div_rpow`).

For `p ≥ 1`, the `Lᵖ` distance dominates the sup distance. In the other direction, the `L²`
distance is at most the square root of the number of coordinates times the sup distance.
These estimates give inclusions between balls in the two metrics. The corresponding
Cauchy–Schwarz estimate bounds the sum of coordinate norms by `√(card ι)` times the `L²` norm.
The coordinate spaces may be different seminormed groups, or pseudometric spaces for the
distance comparisons. A squared-norm bound of `(k + 1) * t²` for a vector of `L²`
also bounds the number of coordinates with norm exceeding a nonnegative `t` by `k`
(`PiLp.card_filter_lt_norm_le`). For `0 < p < ∞`, bounds `‖x i‖ ^ p F ≤ G i` on the coordinate
shares of `‖x‖ ^ p F` add up to `‖x‖ ^ p F ≤ ∑ i, G i` (`PiLp.norm_rpow_mul_le_sum`).

Extending a vector of `Lᵖ(ι, E)` by zero along an embedding `f : ι ↪ ι'` places its coordinate `i`
in the slot `f i`, and the vectors so obtained are those whose coordinates outside the range of
`f` vanish. In particular, extending a vector of `Lᵖ(Fin k, E)` by zero onto the first `k`
coordinates of `Lᵖ(Fin n, E)`, for `k ≤ n`, places its coordinates in the slots `j < k`; the
vectors so obtained are those whose coordinates `j ≥ k` vanish.
The finite sum against a zero-extended vector reduces to the sum over its original coordinates.
Over an index type with at most one element and for `p ≠ 0`, the `Lᵖ` norm is the norm of the
coordinate.
Reindexing the coordinates along the identity bijection is the identity.
Maps into `PiLp p β` converge uniformly exactly when each coordinate does.

We also record `PiLp.univ_sum_single`, the coordinate isometry `PiLp.singleLI` (and the
continuous coordinate inclusion `PiLp.singleCLM`), the power identity `PiLp.norm_rpow_eq_sum`,
coordinatewise decomposition `ContinuousLinearMap.sum_comp_piLpSingleCLM`,
and coordinatewise submodule restriction `LinearIsometryEquiv.submodulePiLp`.

For a family of operators `T i : E i →L[𝕜] F i`, the block-diagonal operator
`PiLp.piMap p T : PiLp p E →L[𝕜] PiLp p F` acts coordinatewise; it is
`ContinuousLinearMap.piMap T` transported along `PiLp.continuousLinearEquiv`. For `p = 2` and
Hilbert spaces this is the orthogonal direct sum of the `T i` on a finite Hilbert sum. Its
coordinates and its action on coordinate inclusions are computed blockwise
(`PiLp.proj_comp_piMap`, `PiLp.piMap_comp_singleCLM`).

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

/-- Every finite `PiLp` vector is the sum of its coordinate `PiLp.single` vectors; compare
`Finset.univ_sum_single`. -/
theorem univ_sum_single [DecidableEq ι] [∀ i, AddCommGroup (E i)] (x : PiLp p E) :
    ∑ i, single p i (x i) = x :=
  WithLp.ofLp_injective p <| by simp [WithLp.ofLp_sum, Finset.univ_sum_single]

/-- Coordinatewise domination of norms implies domination of finite `Lᵖ` norms.
The dominating family only needs a norm: the coordinate bounds ensure its nonnegativity. -/
theorem norm_mono [∀ i, SeminormedAddGroup (E i)] [∀ i, Norm (F i)]
    {x : PiLp p E} {y : PiLp p F}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [norm_eq_card, norm_eq_card]
    exact Nat.cast_le.mpr <| Finset.card_le_card <| Set.Finite.toFinset_mono fun i hi hzero ↦
      hi (le_antisymm (by simpa only [hzero] using h i) (norm_nonneg _))
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

/-- For `0 < p < ∞`, the `p`-th power of the finite `PiLp` norm equals the sum of the `p`-th powers
of the coordinate norms. -/
theorem norm_rpow_eq_sum [∀ i, SeminormedAddGroup (E i)] (hp : 0 < p.toReal) (x : PiLp p E) :
    ‖x‖ ^ p.toReal = ∑ i, ‖x i‖ ^ p.toReal := by
  rw [norm_eq_sum hp, ← Real.rpow_mul (Finset.sum_nonneg fun _ _ ↦ by positivity),
    one_div_mul_cancel hp.ne', Real.rpow_one]

/-- For `0 < p < ∞`, bounds `‖x i‖ ^ p * F ≤ G i` on the coordinate shares of `‖x‖ ^ p * F` add
up to `‖x‖ ^ p * F ≤ ∑ i, G i`. -/
theorem norm_rpow_mul_le_sum [∀ i, SeminormedAddGroup (E i)] (x : PiLp p E) (hp : 0 < p.toReal)
    {F : ℝ} {G : ι → ℝ} (h : ∀ i, ‖x i‖ ^ p.toReal * F ≤ G i) :
    ‖x‖ ^ p.toReal * F ≤ ∑ i, G i := by
  rw [norm_rpow_eq_sum hp, Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ ↦ h i

/-- Taking coordinate norms preserves the finite `Lᵖ` norm. -/
@[simp]
theorem norm_norm [∀ i, SeminormedAddGroup (E i)] (x : PiLp p E) :
    ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ = ‖x‖ :=
  le_antisymm (norm_mono fun i ↦ by simp) (norm_mono fun i ↦ by simp)

/-- Over an index type with at most one element, a vector of `Lᵖ`, `p ≠ 0`, has the norm of each of
its coordinates. For `p = 0` the norm instead counts the coordinates of nonzero norm. -/
theorem norm_apply_eq_norm [∀ i, SeminormedAddGroup (E i)] [Subsingleton ι] (hp : p ≠ 0)
    (x : PiLp p E) (i : ι) : ‖x i‖ = ‖x‖ := by
  have : Unique ι := uniqueOfSubsingleton i
  rcases eq_or_ne p ∞ with rfl | hp'
  · rw [norm_eq_ciSup, ciSup_unique, Subsingleton.elim i default]
  · have hp_pos := ENNReal.toReal_pos hp hp'
    rw [← Real.rpow_left_inj (norm_nonneg _) (PiLp.norm_nonneg' x) hp_pos.ne',
      norm_rpow_eq_sum hp_pos, Fintype.sum_subsingleton _ i]

variable [∀ i, SeminormedAddCommGroup (E i)]

/-- At most `k` coordinates have norm exceeding a nonnegative threshold `t` when the squared
norm is at most `(k + 1) * t²`. -/
theorem card_filter_lt_norm_le {x : PiLp 2 E} {k : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (hxt : ‖x‖ ^ 2 ≤ (k + 1 : ℝ) * t ^ 2) :
    (Finset.univ.filter fun i ↦ t < ‖x i‖).card ≤ k := by
  classical
  by_contra h
  let s := Finset.univ.filter fun i ↦ t < ‖x i‖
  have hcard : k + 1 ≤ s.card := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
  have hsum : (s.card : ℝ) * t ^ 2 < ∑ i ∈ s, ‖x i‖ ^ 2 := by
    calc
      _ = ∑ _i ∈ s, t ^ 2 := by simp
      _ < _ := Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega)) fun i hi ↦
        pow_lt_pow_left₀ ((Finset.mem_filter.mp hi).2) ht (by norm_num : 2 ≠ 0)
  have htotal : ∑ i ∈ s, ‖x i‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have hcard' : (k + 1 : ℝ) ≤ s.card := by exact_mod_cast hcard
  exact (mul_le_mul_of_nonneg_right hcard' (sq_nonneg t)).not_gt
    (hsum.trans_le (htotal.trans hxt))

section SingleLI

variable (p E) [Fact (1 ≤ p)] [DecidableEq ι] {𝕜 : Type*} [Semiring 𝕜] [∀ i, Module 𝕜 (E i)]

/-- Coordinate inclusion `v ↦ PiLp.single p i v` into `PiLp p E` as a linear isometry. -/
noncomputable def singleLI (i : ι) : E i →ₗᵢ[𝕜] PiLp p E where
  toLinearMap := (WithLp.linearEquiv p 𝕜 (∀ j, E j)).symm.toLinearMap ∘ₗ LinearMap.single 𝕜 E i
  norm_map' v := by simp

variable {p E}

/-- `PiLp.singleLI` evaluates as `PiLp.single`. -/
@[simp] theorem singleLI_apply (i : ι) (v : E i) :
    singleLI (𝕜 := 𝕜) p E i v = single p i v := by simp [singleLI]

end SingleLI

/-- The sum of coordinate norms of a vector is at most `√(card ι)` times its `L²` norm. -/
theorem sum_norm_le_sqrt_card_mul_norm (x : PiLp 2 E) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  simpa [PiLp.norm_eq_of_L2] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι ↦ 1) (fun i ↦ ‖x i‖)

/-- Reindexing a finite family along an equivalence preserves its `Lᵖ` norm, for every
exponent. -/
theorem norm_toLp_comp_equiv {E : Type*} [Norm E] {κ : Type*} [Fintype κ]
    (e : κ ≃ ι) (x : ι → E) : ‖WithLp.toLp p (x ∘ e)‖ = ‖WithLp.toLp p x‖ := by
  rcases p.trichotomy with rfl | rfl | hp
  · simp only [norm_eq_card, Set.toFinite_toFinset, Set.toFinset_card]
    exact congrArg Nat.cast (Fintype.card_congr (e.subtypeEquiv fun _ ↦ Iff.rfl))
  · simp only [norm_eq_ciSup]
    exact e.iSup_congr fun _ ↦ rfl
  · simp only [norm_eq_sum hp]
    exact congrArg (· ^ _) (Fintype.sum_equiv e _ _ fun _ ↦ rfl)

/-- For `p ≠ 0`, a finite family of multiples of one vector has `Lᵖ` norm equal to the `Lᵖ` norm
of the coefficients times the norm of the vector. -/
theorem norm_toLp_smul_const {F 𝕜 : Type*} [SeminormedAddGroup F] [SeminormedAddGroup 𝕜]
    [SMul 𝕜 F] [NormSMulClass 𝕜 F] (hp : p ≠ 0) (a : ι → 𝕜) (y : F) :
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖WithLp.toLp p a‖ * ‖y‖ := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp only [norm_eq_ciSup, norm_smul]
    exact (Real.iSup_mul_of_nonneg (norm_nonneg y) _).symm
  · have hp_pos := ENNReal.toReal_pos hp hp'
    rw [← Real.rpow_left_inj (PiLp.norm_nonneg' _)
      (mul_nonneg (PiLp.norm_nonneg' _) (norm_nonneg y)) hp_pos.ne',
      Real.mul_rpow (PiLp.norm_nonneg' _) (norm_nonneg y), norm_rpow_eq_sum hp_pos,
      norm_rpow_eq_sum hp_pos, Finset.sum_mul]
    simp only [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg y)]

/-- A real family with a positive coordinate has positive `Lᵖ` norm. -/
theorem norm_toLp_pos [Fact (1 ≤ p)] {c : ι → ℝ} {i : ι} (hi : 0 < c i) : 0 < ‖WithLp.toLp p c‖ :=
  hi.trans_le ((Real.le_norm_self _).trans (norm_apply_le (WithLp.toLp p c) i))

/-- Rescaling a positive family `c` with `N = ‖c‖_{ℓ^q}`, `1 ≤ q < ∞`, to
`(N (c i / N) ^ (q / p))_i` preserves its norm in `ℓ^p` for every `p ≠ 0`. -/
theorem norm_toLp_mul_div_rpow [Nonempty ι] {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ∞) (hp : p ≠ 0)
    {c : ι → ℝ} (hc : ∀ i, 0 < c i) :
    ‖WithLp.toLp p fun i ↦ ‖WithLp.toLp q c‖ * (c i / ‖WithLp.toLp q c‖) ^ (q.toReal / p.toReal)‖
      = ‖WithLp.toLp q c‖ := by
  set N := ‖WithLp.toLp q c‖
  have hN : 0 < N := norm_toLp_pos (hc (Classical.arbitrary ι))
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp [abs_of_pos hN]
  have hp₀ := ENNReal.toReal_pos hp hp'
  -- `∑ᵢ (c i / N) ^ q = 1`
  have hsum : ∑ i, (c i / N) ^ q.toReal = 1 := by
    have h := norm_rpow_eq_sum ((ENNReal.toReal_pos_iff_ne_top q).2 hq) (WithLp.toLp q c)
    simp only [Real.norm_eq_abs, abs_of_pos (hc _)] at h
    simp_rw [Real.div_rpow (hc _).le hN.le, ← Finset.sum_div, ← h]
    exact div_self (by positivity)
  rw [← Real.rpow_left_inj (PiLp.norm_nonneg' _) hN.le hp₀.ne', norm_rpow_eq_sum hp₀]
  have hterm (i : ι) : ‖(WithLp.toLp p fun i ↦ N * (c i / N) ^ (q.toReal / p.toReal)) i‖ ^
      p.toReal = N ^ p.toReal * (c i / N) ^ q.toReal := by
    have hb : 0 ≤ c i / N := (div_pos (hc i) hN).le
    rw [toLp_apply, Real.norm_of_nonneg (by positivity), Real.mul_rpow hN.le (by positivity),
      ← Real.rpow_mul hb, div_mul_cancel₀ _ hp₀.ne']
  simp_rw [hterm, ← Finset.mul_sum, hsum, mul_one]

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

/-- A linear combination `∑ i, s i • v i` whose coefficients are the coordinates of a vector `s`
of `Lᵖ`, `p ≥ 1`, has norm at most `‖s‖ * ∑ i, ‖v i‖`. -/
theorem norm_sum_smul_le {𝕜 : Type*} [SeminormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 F]
    [IsBoundedSMul 𝕜 F] (s : PiLp p fun _ : ι ↦ 𝕜) (v : ι → F) :
    ‖∑ i, s i • v i‖ ≤ ‖s‖ * ∑ i, ‖v i‖ := by
  rw [Finset.mul_sum]
  exact (norm_sum_le _ _).trans <| Finset.sum_le_sum fun i _ ↦
    (norm_smul_le _ _).trans <| mul_le_mul_of_nonneg_right (norm_apply_le s i) (norm_nonneg _)

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

section UniformSpace

variable {β : ι → Type*} [∀ i, UniformSpace (β i)]

omit [Fintype ι] in
/-- Maps into `PiLp p β` converge uniformly exactly when each coordinate does. -/
theorem tendstoUniformly_iff {κ α : Type*} {l : Filter κ} {F : κ → α → PiLp p β}
    {g : α → PiLp p β} :
    TendstoUniformly F g l ↔ ∀ i, TendstoUniformly (fun k z ↦ F k z i) (fun z ↦ g z i) l := by
  refine ⟨fun h i ↦ ((Pi.uniformContinuous_proj β i).comp (uniformContinuous_ofLp p β))
    |>.comp_tendstoUniformly h, fun h ↦ ?_⟩
  have hpi : TendstoUniformly (fun k z ↦ WithLp.ofLp (F k z)) (fun z ↦ WithLp.ofLp (g z)) l := by
    have hi : Filter.Tendsto (fun k (i : ι) ↦ UniformFun.ofFun fun z ↦ F k z i) l
        (nhds fun i ↦ UniformFun.ofFun fun z ↦ g z i) :=
      tendsto_pi_nhds.2 fun i ↦ UniformFun.tendsto_iff_tendstoUniformly.2 (h i)
    exact UniformFun.tendsto_iff_tendstoUniformly.1
      ((UniformFun.uniformEquivPiComm α β).symm.continuous.tendsto _ |>.comp hi)
  exact (uniformContinuous_toLp p β).comp_tendstoUniformly hpi

end UniformSpace

section Single

variable [DecidableEq ι]

omit [Fintype ι] in
/-- Scalar multiplication commutes with `PiLp.single`. -/
@[simp]
theorem single_smul {𝕜 : Type*} {β : ι → Type*} [∀ i, Zero (β i)] [∀ i, SMulZeroClass 𝕜 (β i)]
    (p : ℝ≥0∞) (i : ι) (c : 𝕜) (a : β i) :
    single p i (c • a) = c • single p i a := by
  simp_rw [← toLp_single, ← WithLp.toLp_smul]
  exact congrArg (WithLp.toLp p)
    (Pi.single_op (fun i ↦ (c • · : β i → β i)) (fun _ ↦ smul_zero _) i a)

omit [Fintype ι] in
/-- Inclusion of the `i`-th coordinate into `PiLp p β` as a continuous linear map. -/
def singleCLM (p : ℝ≥0∞) (𝕜 : Type*) [Semiring 𝕜] (β : ι → Type*)
    [∀ i, TopologicalSpace (β i)] [∀ i, AddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] (i : ι) :
    β i →L[𝕜] PiLp p β :=
  (continuousLinearEquiv p 𝕜 β).symm.toContinuousLinearMap.comp (.single 𝕜 β i)

omit [Fintype ι] in
@[simp]
theorem singleCLM_apply {𝕜 : Type*} [Semiring 𝕜] {β : ι → Type*}
    [∀ i, TopologicalSpace (β i)] [∀ i, AddCommGroup (β i)] [∀ i, Module 𝕜 (β i)]
    (i : ι) (a : β i) :
    singleCLM p 𝕜 β i a = single p i a := by
  simp [singleCLM]

@[simp]
theorem toContinuousLinearMap_singleLI [Fact (1 ≤ p)] {𝕜 : Type*} [Semiring 𝕜]
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] (i : ι) :
    (singleLI (𝕜 := 𝕜) p β i).toContinuousLinearMap = singleCLM p 𝕜 β i := by
  ext a
  simp

/-- The coordinate projections and inclusions decompose the identity on `PiLp p β`. -/
theorem sum_singleCLM_comp_proj [Fact (1 ≤ p)] {𝕜 : Type*} [Semiring 𝕜] {β : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] :
    ∑ i, (singleCLM p 𝕜 β i).comp (proj p β i) = ContinuousLinearMap.id 𝕜 (PiLp p β) := by
  ext x j
  simp

/-- The operator norm of `PiLp.singleCLM` is at most `1`. -/
theorem norm_singleCLM_le [Fact (1 ≤ p)] {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {β : ι → Type*} [∀ i, SeminormedAddCommGroup (β i)] [∀ i, NormedSpace 𝕜 (β i)] (i : ι) :
    ‖singleCLM p 𝕜 β i‖ ≤ 1 := by
  rw [← toContinuousLinearMap_singleLI]
  exact (singleLI (𝕜 := 𝕜) p β i).norm_toContinuousLinearMap_le

end Single

end PiLp

namespace ContinuousLinearMap

/-- Decomposing a continuous linear map on a finite `PiLp` product along the coordinate
inclusions `PiLp.singleCLM`. -/
theorem sum_comp_piLpSingleCLM {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ≥0∞}
    {𝕜 M : Type*} [Semiring 𝕜] {β : ι → Type*}
    [∀ i, TopologicalSpace (β i)] [∀ i, AddCommGroup (β i)] [∀ i, Module 𝕜 (β i)]
    [TopologicalSpace M] [AddCommMonoid M] [Module 𝕜 M]
    (L : PiLp p β →L[𝕜] M) (v : PiLp p β) :
    ∑ i, L.comp (PiLp.singleCLM p 𝕜 β i) (v i) = L v := by
  simp only [ContinuousLinearMap.comp_apply, PiLp.singleCLM_apply]
  rw [← map_sum, PiLp.univ_sum_single]

end ContinuousLinearMap

namespace LinearIsometry

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
  · simpa only [Fin.castLEEmb_apply, Fin.castLE_mk, Fin.eta] using
      piLpExtendByZero_apply_apply (Fin.castLEEmb hk) w ⟨j, h⟩
  · exact piLpExtendByZero_apply_eq_zero (by simpa [Fin.range_castLE] using h) w

/-- The vectors of `Lᵖ(Fin n, E)` obtained by extending a vector of `Lᵖ(Fin k, E)` by zero are
those whose coordinates `j ≥ k` vanish. -/
theorem range_piLpExtendByZero_castLEEmb (hk : k ≤ n) :
    Set.range (piLpExtendByZero p 𝕜 E (Fin.castLEEmb hk)) =
      {y : PiLp p fun _ : Fin n ↦ E | ∀ j : Fin n, k ≤ j.val → y j = 0} := by
  simp [range_piLpExtendByZero, Fin.range_castLE]

end LinearIsometry

namespace LinearIsometry

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 : Type*} [SeminormedRing 𝕜]
  {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- A finite sum paired with a vector extended by zero along an embedding reduces to the sum over
the original coordinates. -/
theorem sum_mul_piLpExtendByZero (f : ι ↪ ι') (x : PiLp p fun _ : ι ↦ 𝕜) (h : ι' → 𝕜) :
    ∑ b, h b * piLpExtendByZero p 𝕜 𝕜 f x b = ∑ a, h (f a) * x a :=
  (Fintype.sum_of_injective f f.injective _ _
    (fun b hb ↦ by rw [piLpExtendByZero_apply_eq_zero hb, mul_zero])
    fun a ↦ by rw [piLpExtendByZero_apply_apply]).symm

end LinearIsometry

namespace PiLp

variable {𝕜 ι : Type*} {E F G : ι → Type*} (p : ℝ≥0∞) [Semiring 𝕜]
variable [∀ i, AddCommGroup (E i)] [∀ i, TopologicalSpace (E i)] [∀ i, Module 𝕜 (E i)]
variable [∀ i, AddCommGroup (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, Module 𝕜 (F i)]
variable [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, Module 𝕜 (G i)]

/-- The block-diagonal operator `x ↦ (T i (x i))ᵢ` between the `Lᵖ` products of two families of
topological modules. For `p = 2` and Hilbert spaces this is the orthogonal direct sum of the
operators `T i` on finite Hilbert sums. -/
noncomputable def piMap (T : ∀ i, E i →L[𝕜] F i) : PiLp p E →L[𝕜] PiLp p F :=
  (PiLp.continuousLinearEquiv p 𝕜 E).symm.arrowCongrEquiv (PiLp.continuousLinearEquiv p 𝕜 F).symm
    (ContinuousLinearMap.piMap T)

@[simp]
theorem piMap_apply (T : ∀ i, E i →L[𝕜] F i) (x : PiLp p E) (i : ι) :
    piMap p T x i = T i (x i) :=
  (rfl)

/-- Under the identification `PiLp.continuousLinearEquiv` of `Lᵖ` products with plain products,
the block-diagonal operator `PiLp.piMap p T` is `ContinuousLinearMap.piMap T`. -/
theorem continuousLinearEquiv_comp_piMap (T : ∀ i, E i →L[𝕜] F i) :
    (PiLp.continuousLinearEquiv p 𝕜 F : PiLp p F →L[𝕜] ∀ i, F i) ∘L piMap p T =
      ContinuousLinearMap.piMap T ∘L
        (PiLp.continuousLinearEquiv p 𝕜 E : PiLp p E →L[𝕜] ∀ i, E i) :=
  (rfl)

/-- The block-diagonal operator with identity blocks is the identity. -/
@[simp]
theorem piMap_id : piMap p (fun i ↦ ContinuousLinearMap.id 𝕜 (E i)) = .id 𝕜 (PiLp p E) :=
  (rfl)

/-- Block-diagonal operators compose blockwise. -/
@[simp]
theorem piMap_comp (S : ∀ i, F i →L[𝕜] G i) (T : ∀ i, E i →L[𝕜] F i) :
    piMap p (fun i ↦ S i ∘L T i) = piMap p S ∘L piMap p T :=
  (rfl)

/-- A block-diagonal operator maps the `i`-th coordinate inclusion through its `i`-th block. -/
@[simp]
theorem piMap_comp_singleCLM [DecidableEq ι] (T : ∀ i, E i →L[𝕜] F i) (i : ι) :
    piMap p T ∘L singleCLM p 𝕜 E i = singleCLM p 𝕜 F i ∘L T i := by
  ext x j
  by_cases h : j = i
  · subst h
    simp
  · simp [h]

end PiLp

namespace PiLp

variable {𝕜 ι : Type*} {E F : ι → Type*} (p : ℝ≥0∞) [Semiring 𝕜]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
variable [∀ i, NormedAddCommGroup (F i)] [∀ i, Module 𝕜 (F i)]

/-- The `i`-th coordinate of a block-diagonal operator is its `i`-th block applied to the `i`-th
coordinate. -/
@[simp]
theorem proj_comp_piMap (T : ∀ i, E i →L[𝕜] F i) (i : ι) :
    proj p F i ∘L piMap p T = T i ∘L proj p E i :=
  (rfl)

end PiLp

namespace LinearIsometryEquiv

section CongrLeft

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {𝕜 E : Type*} [Semiring 𝕜] [SeminormedAddCommGroup E]
  [Module 𝕜 E] {ι : Type*} [Fintype ι]

/-- Reindexing the coordinates of `Lᵖ(ι, E)` along the identity of `ι` is the identity. -/
@[simp]
theorem piLpCongrLeft_refl :
    piLpCongrLeft p 𝕜 E (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 (PiLp p fun _ : ι ↦ E) := by
  ext x i
  simp [piLpCongrLeft_apply, Equiv.piCongrLeft'_refl]

end CongrLeft

section SubmodulePiLp
variable {ι 𝕜 X : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)] [Ring 𝕜]
  [SeminormedAddCommGroup X] [Module 𝕜 X] {F : ι → Type*} [∀ i, SeminormedAddCommGroup (F i)]
  [∀ i, Module 𝕜 (F i)] (e : X ≃ₗᵢ[𝕜] PiLp p F) (M : Submodule 𝕜 X)
  (N : ∀ i, Submodule 𝕜 (F i)) (hMN : ∀ x, x ∈ M ↔ ∀ i, e x i ∈ N i)

/-- Restrict a linear isometry equivalence `e : X ≃ₗᵢ[𝕜] PiLp p F` to a submodule `M` of `X`
characterized coordinatewise by `x ∈ M ↔ ∀ i, e x i ∈ N i`. -/
noncomputable def submodulePiLp : ↥M ≃ₗᵢ[𝕜] PiLp p (fun i ↦ ↥(N i)) where
  toFun x := WithLp.toLp p fun i ↦ ⟨e x.val i, (hMN x.val).mp x.property i⟩
  invFun g := ⟨e.symm (WithLp.toLp p fun i ↦ (g i : F i)),
    (hMN _).mpr fun i ↦ by rw [e.apply_symm_apply, PiLp.toLp_apply]; exact (g i).property⟩
  map_add' _ _ := by ext i : 2; simp [map_add]
  map_smul' _ _ := by ext i : 2; simp
  left_inv x := Subtype.ext <| by have hx := WithLp.toLp_ofLp p (e x.val); simp [hx]
  right_inv _ := by ext i : 2; simp
  norm_map' x := (le_antisymm (PiLp.norm_mono fun _ ↦ by simp [PiLp.toLp_apply])
    (PiLp.norm_mono fun _ ↦ by simp [PiLp.toLp_apply])).trans
      ((e.norm_map x.val).trans (Submodule.norm_coe x))

/-- Coordinatewise evaluation of `e.submodulePiLp M N hMN` in `F i`. -/
@[simp] theorem coe_submodulePiLp_apply (x : ↥M) (i : ι) :
    (e.submodulePiLp M N hMN x i : F i) = e x.val i := (rfl)

/-- Coordinatewise evaluation of `(e.submodulePiLp M N hMN).symm` under `e`. -/
@[simp] theorem apply_coe_submodulePiLp_symm (g : PiLp p (fun i ↦ ↥(N i))) (i : ι) :
    e ((e.submodulePiLp M N hMN).symm g : X) i = (g i : F i) := by
  rw [← e.coe_submodulePiLp_apply M N hMN, LinearIsometryEquiv.apply_symm_apply]

/-- On `PiLp.single`, `(e.submodulePiLp M N hMN).symm` embeds via `e.symm`. -/
theorem coe_submodulePiLp_symm_single [DecidableEq ι] (j : ι) (h : ↥(N j)) :
    ((e.submodulePiLp M N hMN).symm (PiLp.single p j h) : X) =
      e.symm (PiLp.single p j (h : F j)) :=
  e.injective <| by
    rw [e.apply_symm_apply]; ext k : 1; rw [e.apply_coe_submodulePiLp_symm M N hMN]
    rcases eq_or_ne k j with rfl | hkj <;> simp [*]
end SubmodulePiLp

end LinearIsometryEquiv
