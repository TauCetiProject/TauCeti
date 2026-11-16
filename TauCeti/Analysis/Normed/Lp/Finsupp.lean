/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.Analysis.Normed.Lp.BoundedContinuous

/-!
# Finitely supported functions and finite-support probabilities in `ℓᵖ`

Every finitely supported function `a : α →₀ E` into a normed group belongs to `lp (fun _ : α ↦ E) p`
for every exponent `p : ℝ≥0∞`. This gives an injective inclusion `Finsupp.toLp p`, bundled as a
linear map `Finsupp.toLpLinearMap 𝕜 p`. It sends `Finsupp.single x v` to `lp.single p x v`,
intertwines `Finsupp.mapDomain` along bijections and group actions with
`LinearIsometryEquiv.lpCongrLeft` and `lp.leftTranslation`, and reduces the `ℓ¹` norm, `tsum`, and
the pairing `lp.pairingBCF` with bounded continuous functions to finite sums over `a.support`.

Composing with `Convexity.StdSimplex.weights` embeds Mathlib's finite-support probability simplex
`Convexity.StdSimplex R α` into `lp (fun _ : α ↦ R) p` via `Convexity.StdSimplex.toLp p`. It
sends point masses `Convexity.StdSimplex.single x` to `lp.single p x 1`, intertwines pushforward
`Convexity.StdSimplex.map` along bijections and group actions with `lpCongrLeft` and
`lp.leftTranslation`, has convex range equal to the convex hull of the unit point masses
`lp.single p x 1`, and over `ℝ` lands on the unit sphere of `ℓ¹`.

## Main definitions

* `Finsupp.toLp`: inclusion `(α →₀ E) → lp (fun _ : α ↦ E) p`.
* `Finsupp.toLpLinearMap`: the same inclusion as a `𝕜`-linear map.
* `Convexity.StdSimplex.toLp`: inclusion `Convexity.StdSimplex R α → lp (fun _ : α ↦ R) p`.

## Main results

* `Finsupp.toLp_single`, `Finsupp.toLp_eq_sum_single`: compatibility with point masses and finite
  coordinate expansions.
* `Finsupp.norm_toLp_one`, `Finsupp.norm_toLp_one_of_nonneg`: the `ℓ¹` norm of `a.toLp 1` is the
  finite sum of coordinate norms.
* `Finsupp.lpCongrLeft_toLp`, `Finsupp.leftTranslation_toLp`: equivariance with reindexing and
  left translation.
* `Finsupp.pairingBCF_toLp`: pairing `a.toLp 1` with a bounded continuous function `f` is
  `a.sum fun x c ↦ c * f x`.
* `Convexity.StdSimplex.norm_toLp_one`, `Convexity.StdSimplex.leftTranslation_toLp`,
  `Convexity.StdSimplex.norm_leftTranslation_sub_toLp_one`: `ℓ¹` norm and left-translation
  identities for finite-support probabilities.
* `Convexity.StdSimplex.convex_range_toLp`, `Convexity.StdSimplex.range_toLp_eq_convexHull`: the
  image of `Convexity.StdSimplex R α` in `ℓᵖ` is convex and equals the convex hull of the unit
  point masses `lp.single p x 1`.
-/

public section

noncomputable section

open scoped ENNReal BoundedContinuousFunction

namespace Finsupp

section ToLp

variable {α β E : Type*} [NormedAddCommGroup E]

/-- Every finitely supported function lies in `ℓᵖ` for every exponent `p : ℝ≥0∞`. -/
theorem memℓp (a : α →₀ E) (p : ℝ≥0∞) : Memℓp (a : α → E) p :=
  (memℓp_zero a.hasFiniteSupport).of_exponent_ge zero_le

/-- The inclusion of finitely supported functions `α →₀ E` into `lp (fun _ : α ↦ E) p`. -/
def toLp (p : ℝ≥0∞) (a : α →₀ E) : lp (fun _ : α ↦ E) p :=
  ⟨⇑a, a.memℓp p⟩

/-- Evaluating `a.toLp p` at `x` returns `a x`. -/
@[simp]
theorem toLp_apply (p : ℝ≥0∞) (a : α →₀ E) (x : α) : a.toLp p x = a x :=
  (rfl)

/-- The function underlying `a.toLp p` is `a`. -/
theorem coeFn_toLp (p : ℝ≥0∞) (a : α →₀ E) : ⇑(a.toLp p) = ⇑a := by
  ext x
  rfl

/-- The inclusion `Finsupp.toLp p` is injective. -/
theorem toLp_injective (p : ℝ≥0∞) :
    Function.Injective (toLp p : (α →₀ E) → lp (fun _ : α ↦ E) p) := fun a b h ↦ by
  ext x
  simpa only [toLp_apply] using congrArg (fun f : lp (fun _ : α ↦ E) p ↦ f x) h

@[simp]
theorem toLp_zero (p : ℝ≥0∞) : (0 : α →₀ E).toLp p = 0 := by
  ext x
  simp

@[simp]
theorem toLp_add (p : ℝ≥0∞) (a b : α →₀ E) : (a + b).toLp p = a.toLp p + b.toLp p := by
  ext x
  simp

@[simp]
theorem toLp_neg (p : ℝ≥0∞) (a : α →₀ E) : (-a).toLp p = -a.toLp p := by
  ext x
  simp

@[simp]
theorem toLp_sub (p : ℝ≥0∞) (a b : α →₀ E) : (a - b).toLp p = a.toLp p - b.toLp p := by
  ext x
  simp

@[simp]
theorem toLp_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (p : ℝ≥0∞) (c : 𝕜) (a : α →₀ E) : (c • a).toLp p = c • a.toLp p := by
  ext x
  simp

/-- The inclusion of `Finsupp.single x v` into `ℓᵖ` is the point mass `lp.single p x v`. -/
@[simp]
theorem toLp_single [DecidableEq α] (p : ℝ≥0∞) (x : α) (v : E) :
    (single x v).toLp p = lp.single p x v := by
  ext y
  simp [single_apply, lp.single_apply, Pi.single_apply, eq_comm]

/-- The inclusion `(α →₀ E) →ₗ[𝕜] lp (fun _ : α ↦ E) p`, as a `𝕜`-linear map. -/
def toLpLinearMap (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞) :
    (α →₀ E) →ₗ[𝕜] lp (fun _ : α ↦ E) p where
  toFun := toLp p
  map_add' := toLp_add p
  map_smul' := toLp_smul p

@[simp]
theorem toLpLinearMap_apply {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (p : ℝ≥0∞) (a : α →₀ E) : toLpLinearMap 𝕜 p a = a.toLp p := by
  simp [toLpLinearMap]

/-- Every finitely supported element of `ℓᵖ` is the finite sum of its coordinate point masses. -/
theorem toLp_eq_sum_single [DecidableEq α] (p : ℝ≥0∞) (a : α →₀ E) :
    a.toLp p = a.sum fun x v ↦ lp.single p x v := by
  ext y
  rw [toLp_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  by_cases hy : y ∈ a.support
  · simp [lp.single_apply, Pi.single_apply, hy]
  · simp [lp.single_apply, Pi.single_apply, hy, notMem_support_iff.mp hy]

/-- The unconditional sum of coordinates of `a.toLp p` is the finite sum `a.sum fun _ v ↦ v`. -/
theorem tsum_toLp (p : ℝ≥0∞) (a : α →₀ E) : ∑' x, a.toLp p x = a.sum fun _ v ↦ v := by
  rw [Finsupp.sum]
  exact tsum_eq_sum fun x hx ↦ notMem_support_iff.mp hx

/-- The `ℓ¹` norm of a finitely supported function is the finite sum of its coordinate norms. -/
theorem norm_toLp_one (a : α →₀ E) : ‖a.toLp 1‖ = a.sum fun _ v ↦ ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp), Finsupp.sum]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, toLp_apply]
  exact tsum_eq_sum fun x hx ↦ by simp [notMem_support_iff.mp hx]

/-- The `ℓ¹` norm of a nonnegative real finitely supported function is the finite sum of its
values. -/
theorem norm_toLp_one_of_nonneg {a : α →₀ ℝ} (ha : ∀ x, 0 ≤ a x) :
    ‖a.toLp 1‖ = a.sum fun _ r ↦ r := by
  rw [norm_toLp_one]
  exact Finset.sum_congr rfl fun x _ ↦ Real.norm_of_nonneg (ha x)

/-- Reindexing `a.toLp p` along a bijection `e : α ≃ β` corresponds to `Finsupp.mapDomain e`. -/
theorem lpCongrLeft_toLp {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : α ≃ β) (a : α →₀ E) :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 E e (a.toLp p) = (a.mapDomain e).toLp p := by
  ext y
  simp [mapDomain_equiv_apply]

/-- Left translation of `a.toLp p` by `g` under a group action corresponds to
`Finsupp.mapDomain (g • ·)`. -/
theorem leftTranslation_toLp {G 𝕜 : Type*} [Group G] [MulAction G α] [NormedRing 𝕜]
    [Module 𝕜 E] [IsBoundedSMul 𝕜 E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : G) (a : α →₀ E) :
    lp.leftTranslation p 𝕜 g (a.toLp p) = (a.mapDomain (g • ·)).toLp p := by
  rw [lp.leftTranslation_eq_lpCongrLeft]
  exact lpCongrLeft_toLp (MulAction.toPerm g) a

/-- The `ℓ¹` translation distance `‖L_g a - a‖` of a finitely supported real function is
`∑' x, |a (g⁻¹ • x) - a x|`. -/
theorem norm_leftTranslation_sub_toLp_one {G : Type*} [Group G] [MulAction G α]
    (g : G) (a : α →₀ ℝ) :
    ‖lp.leftTranslation 1 ℝ g (a.toLp 1) - a.toLp 1‖ = ∑' x, |a (g⁻¹ • x) - a x| := by
  rw [lp.norm_eq_tsum_rpow (by simp)]
  simp only [ENNReal.toReal_one, Real.rpow_one, div_one, lp.coeFn_sub, Pi.sub_apply,
    lp.leftTranslation_apply, toLp_apply, Real.norm_eq_abs]

/-- Pairing `a.toLp 1` with a bounded continuous function `f` reduces to the finite sum
`a.sum fun x c ↦ c * f x`. -/
theorem pairingBCF_toLp {𝕜 : Type*} [TopologicalSpace α] [RCLike 𝕜] (a : α →₀ 𝕜) (f : α →ᵇ 𝕜) :
    lp.pairingBCF 𝕜 (a.toLp 1) f = a.sum fun x c ↦ c * f x := by
  rw [lp.pairingBCF_apply, Finsupp.sum]
  exact tsum_eq_sum fun x hx ↦ by simp [notMem_support_iff.mp hx]

end ToLp

end Finsupp

namespace Convexity.StdSimplex

section ToLp

variable {R α β : Type*}

/-- The unconditional sum of the weights of a finite-support probability is `1`. -/
theorem tsum_weights [AddCommMonoid R] [LE R] [One R] [TopologicalSpace R]
    (μ : StdSimplex R α) : ∑' x, μ.weights x = 1 := by
  rw [tsum_eq_sum fun x hx ↦ Finsupp.notMem_support_iff.mp hx]
  exact μ.total

/-- The inclusion of the finite-support probability simplex `Convexity.StdSimplex R α` into
`lp (fun _ : α ↦ R) p`. -/
def toLp [NormedAddCommGroup R] [LE R] [One R] (p : ℝ≥0∞) (μ : StdSimplex R α) :
    lp (fun _ : α ↦ R) p :=
  μ.weights.toLp p

/-- Evaluating `μ.toLp p` at `x` returns `μ.weights x`. -/
@[simp]
theorem toLp_apply [NormedAddCommGroup R] [LE R] [One R] (p : ℝ≥0∞) (μ : StdSimplex R α)
    (x : α) : μ.toLp p x = μ.weights x :=
  (rfl)

/-- The inclusion `Convexity.StdSimplex.toLp p` is injective. -/
theorem toLp_injective [NormedAddCommGroup R] [LE R] [One R] (p : ℝ≥0∞) :
    Function.Injective (toLp p : StdSimplex R α → lp (fun _ : α ↦ R) p) := by
  intro μ ν h
  have hw := Finsupp.toLp_injective p h
  cases μ
  cases ν
  congr

/-- The inclusion of a point mass `Convexity.StdSimplex.single x` into `ℓᵖ` is
`lp.single p x 1`. -/
@[simp]
theorem toLp_single [NormedRing R] [PartialOrder R] [IsStrictOrderedRing R] [DecidableEq α]
    (p : ℝ≥0∞) (x : α) : (single x : StdSimplex R α).toLp p = lp.single p x 1 := by
  simp [toLp]

/-- The unconditional coordinate sum of `μ.toLp p` is `1`. -/
theorem tsum_toLp [NormedAddCommGroup R] [LE R] [One R] (p : ℝ≥0∞) (μ : StdSimplex R α) :
    ∑' x, μ.toLp p x = 1 :=
  μ.tsum_weights

/-- Every finite-support real probability has `ℓ¹` norm equal to `1`. -/
theorem norm_toLp_one (μ : StdSimplex ℝ α) : ‖μ.toLp 1‖ = 1 := by
  rw [toLp, Finsupp.norm_toLp_one_of_nonneg μ.weights_nonneg, μ.total]

/-- Reindexing `μ.toLp p` along a bijection `e : α ≃ β` corresponds to
`Convexity.StdSimplex.map e`. -/
theorem lpCongrLeft_toLp {𝕜 : Type*} [NormedRing R] [PartialOrder R] [IsStrictOrderedRing R]
    [NormedRing 𝕜] [Module 𝕜 R] [IsBoundedSMul 𝕜 R] {p : ℝ≥0∞} [Fact (1 ≤ p)] (e : α ≃ β)
    (μ : StdSimplex R α) :
    LinearIsometryEquiv.lpCongrLeft p 𝕜 R e (μ.toLp p) = (μ.map e).toLp p := by
  rw [toLp, toLp, weights_map, Finsupp.lpCongrLeft_toLp]

/-- Left translation of `μ.toLp p` by `g` under a group action corresponds to
`Convexity.StdSimplex.map (g • ·)`. -/
theorem leftTranslation_toLp {G 𝕜 : Type*} [Group G] [MulAction G α] [NormedRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [NormedRing 𝕜] [Module 𝕜 R] [IsBoundedSMul 𝕜 R]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (g : G) (μ : StdSimplex R α) :
    lp.leftTranslation p 𝕜 g (μ.toLp p) = (μ.map (g • ·)).toLp p := by
  rw [toLp, toLp, weights_map, Finsupp.leftTranslation_toLp]

/-- The `ℓ¹` translation distance `‖L_g μ - μ‖` of a finite-support real probability is
`∑' x, |μ.weights (g⁻¹ • x) - μ.weights x|`. -/
theorem norm_leftTranslation_sub_toLp_one {G : Type*} [Group G] [MulAction G α] (g : G)
    (μ : StdSimplex ℝ α) :
    ‖lp.leftTranslation 1 ℝ g (μ.toLp 1) - μ.toLp 1‖ =
      ∑' x, |μ.weights (g⁻¹ • x) - μ.weights x| :=
  Finsupp.norm_leftTranslation_sub_toLp_one g μ.weights

/-- Pairing `μ.toLp 1` with a bounded continuous function `f` is the finite expectation
`μ.weights.sum fun x c ↦ c * f x`. -/
theorem pairingBCF_toLp [TopologicalSpace α] (μ : StdSimplex ℝ α) (f : α →ᵇ ℝ) :
    lp.pairingBCF ℝ (μ.toLp 1) f = μ.weights.sum fun x c ↦ c * f x :=
  Finsupp.pairingBCF_toLp μ.weights f

/-- The image of `Convexity.StdSimplex R α` in `ℓᵖ` is convex. -/
theorem convex_range_toLp [NormedRing R] [PartialOrder R] [IsStrictOrderedRing R] (p : ℝ≥0∞) :
    Convex R (Set.range (toLp p : StdSimplex R α → lp (fun _ : α ↦ R) p)) := by
  rintro _ ⟨μ, rfl⟩ _ ⟨ν, rfl⟩ a b ha hb hab
  exact ⟨Convexity.convexCombPair a b ha hb hab μ ν, by simp [toLp]⟩

/-- The image of `Convexity.StdSimplex R α` in `ℓᵖ` is the convex hull of the unit point masses
`lp.single p x 1`. -/
theorem range_toLp_eq_convexHull [NormedField R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq α] (p : ℝ≥0∞) :
    Set.range (toLp p : StdSimplex R α → lp (fun _ : α ↦ R) p) =
      convexHull R (Set.range fun x : α ↦ lp.single p x (1 : R)) := by
  refine le_antisymm ?_
    (convexHull_min (Set.range_subset_iff.2 fun x ↦ ⟨.single x, by simp⟩) (convex_range_toLp p))
  rintro _ ⟨μ, rfl⟩
  have hsum : ∑ x ∈ μ.weights.support, μ.weights x • lp.single p x (1 : R) = μ.toLp p := by
    rw [toLp, Finsupp.toLp_eq_sum_single, Finsupp.sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [← lp.single_smul, smul_eq_mul, mul_one]
  rw [← hsum]
  exact (convex_convexHull R _).sum_mem (fun x _ ↦ μ.weights_nonneg x) μ.total
    fun x _ ↦ subset_convexHull R _ ⟨x, rfl⟩

end ToLp

end Convexity.StdSimplex
