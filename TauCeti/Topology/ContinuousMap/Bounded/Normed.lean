/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Norm bounds and pointwise operators on bounded continuous functions

This file records norm estimates for operations on bounded continuous functions, and the operator
of pointwise application of a bounded continuous family of continuous linear maps.

The main estimate, `TauCeti.norm_boundedContinuousFunction_comp_le`, bounds the sup norm of the
postcomposition `N ∘ f` of a bounded continuous function `f` by an `ε`-Lipschitz map `N` by
`‖N 0‖ + ε * ‖f‖`. Thus a globally Lipschitz nonlinearity maps bounded continuous functions to
bounded ones with an explicit affine norm bound. In `TauCeti.Analysis.ODE.LyapunovPerron.Basic` it
supplies the uniform bound on the forcing term `s ↦ N (γ s)` that makes the Lyapunov–Perron
integral converge and defines the Lyapunov–Perron operator on bounded continuous curves.

`BoundedContinuousFunction.applyCLM` applies a bounded continuous family `φ` of continuous linear
maps pointwise, `(φ, h) ↦ (t ↦ φ t (h t))`, as a continuous bilinear map, and
`BoundedContinuousFunction.norm_applyCLM_apply_le` bounds the operator norm of `applyCLM φ`
by `‖φ‖`.
The derivative of a superposition operator `f ↦ G ∘ f` at `f` is `applyCLM` of the family
`t ↦ G' (f t)` of derivatives of `G`; see
`TauCeti.Analysis.Calculus.FDeriv.BoundedContinuousFunction`.

`BoundedContinuousFunction.continuousAt_of_forall_apply_eq` says that an operator that is given
near `f₀` by `Θ f t = G (f t)`, with `G` uniformly continuous on a set containing a tube around the
range of `f₀`, is continuous at `f₀` (`BoundedContinuousFunction.apply_mem_of_mem_ball` and
`BoundedContinuousFunction.ball_half_subset_of_mem_ball` are the facts about the tube).

`BoundedContinuousFunction.compContinuousₗᵢ` is precomposition with a homeomorphism, as a linear
isometry equivalence of a submodule of `α →ᵇ β` that it preserves, and
`ContinuousLinearMap.compLeftContinuousBounded_compContinuous` says that postcomposition with a
continuous linear map commutes with precomposition.

`BoundedContinuousFunction.exists_finite_range_dist_lt` says that on a discrete space every bounded
real function is a uniform limit of finite-valued bounded functions.

`BoundedContinuousFunction.norm_norm_smul_one_sub_le_of_nonneg` says that a nonnegative real
bounded continuous function `f` lies within `‖f‖` of the constant `‖f‖`.

`BoundedContinuousFunction.dilate` is the dilation `n ↦ f (n / k)` of a bounded sequence, with
natural-number division; dilations compose multiplicatively and commute with the pointwise
operations. They are the operators under which Dixmier's generalized limits are invariant, see
`TauCeti.Analysis.Normed.Order.GeneralizedLimit`.

`BoundedContinuousFunction.eventually_forall_compact_norm_lt_add` and
`BoundedContinuousFunction.eventually_forall_compact_norm_lt` upgrade pointwise eventual norm
estimates along a filter `l` to compact-uniform eventual norm estimates for a family
`F : X → (α →ᵇ E)` continuous in the sup norm on a compact set `K ⊆ X`.
-/

public section

open Metric
open scoped NNReal BoundedContinuousFunction

namespace TauCeti

variable {T X Y : Type*} [TopologicalSpace T] [SeminormedAddCommGroup X]
  [SeminormedAddCommGroup Y]
  {N : X → Y} {ε : ℝ≥0}

/-- Postcomposition by an `ε`-Lipschitz map `N` has norm at most
`‖N 0‖ + ε * ‖f‖`. -/
theorem norm_boundedContinuousFunction_comp_le (hN : LipschitzWith ε N) (f : T →ᵇ X) :
    ‖f.comp N hN‖ ≤ ‖N 0‖ + ε * ‖f‖ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun t ↦ ?_
  have h := hN.dist_le_mul (f t) 0
  rw [dist_eq_norm, dist_zero_right] at h
  have ht := f.norm_coe_le_norm t
  have := norm_sub_norm_le (N (f t)) (N 0)
  simp only [BoundedContinuousFunction.comp_apply]
  nlinarith [ε.coe_nonneg]

end TauCeti

namespace BoundedContinuousFunction

variable {α 𝕜 X Y : Type*} [TopologicalSpace α] [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- Pointwise application `(φ, h) ↦ (t ↦ φ t (h t))` of a bounded continuous family `φ` of
continuous linear maps to a bounded continuous function `h`, as a continuous bilinear map. -/
noncomputable def applyCLM : (α →ᵇ (X →L[𝕜] Y)) →L[𝕜] (α →ᵇ X) →L[𝕜] α →ᵇ Y :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ 𝕜
      (fun (φ : α →ᵇ (X →L[𝕜] Y)) (h : α →ᵇ X) ↦
        ofNormedAddCommGroup (fun t ↦ φ t (h t)) (φ.continuous.clm_apply h.continuous)
        (‖φ‖ * ‖h‖) fun t ↦
          (φ t).le_of_opNorm_le_of_le (φ.norm_coe_le_norm t) (h.norm_coe_le_norm t))
      (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
      (fun _ _ _ ↦ by ext; simp))
    1 fun φ h ↦ by
      rw [LinearMap.mk₂_apply, one_mul]
      exact norm_ofNormedAddCommGroup_le _ (by positivity) _

@[simp]
theorem applyCLM_apply (φ : α →ᵇ (X →L[𝕜] Y)) (h : α →ᵇ X) (t : α) :
    applyCLM φ h t = φ t (h t) :=
  (rfl)

/-- Pointwise application of `φ` has operator norm at most the sup norm of `φ`. -/
theorem norm_applyCLM_apply_le (φ : α →ᵇ (X →L[𝕜] Y)) : ‖applyCLM φ‖ ≤ ‖φ‖ :=
  (applyCLM φ).opNorm_le_bound (norm_nonneg φ) fun h ↦ (norm_le (by positivity)).2 fun t ↦
    (φ t).le_of_opNorm_le_of_le (φ.norm_coe_le_norm t) (h.norm_coe_le_norm t)


section PseudoMetricSpace

variable {α X Y : Type*} [TopologicalSpace α] [PseudoMetricSpace X] [PseudoMetricSpace Y]
  {s : Set X} {f₀ : α →ᵇ X} {δ : ℝ} {G : X → Y} {Θ : (α →ᵇ X) → α →ᵇ Y}

/-- If the values of `f₀` stay `δ > 0` inside `s`, then every function in the `δ`-ball about `f₀`
has its values in `s`. -/
theorem apply_mem_of_mem_ball {f : α →ᵇ X} (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hf : f ∈ ball f₀ δ) (t : α) : f t ∈ s :=
  hf₀ t (mem_ball.2 ((dist_coe_le_dist t).trans_lt (mem_ball.1 hf)))

/-- If the values of `f₀` stay `δ > 0` inside `s`, then so do the values of every function
uniformly within `δ / 2` of `f₀`, with the margin `δ / 2`. -/
theorem ball_half_subset_of_mem_ball {f : α →ᵇ X} (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s)
    (hf : f ∈ ball f₀ (δ / 2)) (t : α) : ball (f t) (δ / 2) ⊆ s :=
  (ball_subset_ball' (by linarith [dist_coe_le_dist (f := f) (g := f₀) t, mem_ball.1 hf])).trans
    (hf₀ t)

/-- If `G` is uniformly continuous on `s`, the values of `f₀` stay a distance `δ > 0` inside `s`,
and `Θ f t = G (f t)` on the ball of radius `δ` about `f₀`, then `Θ` is continuous at `f₀`. -/
theorem continuousAt_of_forall_apply_eq (hG : UniformContinuousOn G s) (hδ : 0 < δ)
    (hf₀ : ∀ t, ball (f₀ t) δ ⊆ s) (hΘ : ∀ f ∈ ball f₀ δ, ∀ t, Θ f t = G (f t)) :
    ContinuousAt Θ f₀ := by
  refine Metric.continuousAt_iff.2 fun ε hε ↦ ?_
  obtain ⟨η, hη, hGη⟩ := Metric.uniformContinuousOn_iff_le.1 hG (ε / 2) (half_pos hε)
  refine ⟨min δ η, lt_min hδ hη, fun f hf ↦ ?_⟩
  have hfδ : f ∈ ball f₀ δ := mem_ball.2 (hf.trans_le (min_le_left _ _))
  refine lt_of_le_of_lt ((dist_le (half_pos hε).le).2 fun t ↦ ?_) (half_lt_self hε)
  rw [hΘ f hfδ, hΘ f₀ (mem_ball_self hδ)]
  exact hGη _ (apply_mem_of_mem_ball hf₀ hfδ t) _
    (hf₀ t (mem_ball_self hδ)) ((dist_coe_le_dist t).trans (hf.le.trans (min_le_right _ _)))

end PseudoMetricSpace

end BoundedContinuousFunction

/-- Postcomposition with a continuous linear map commutes with precomposition with a continuous
map. -/
theorem ContinuousLinearMap.compLeftContinuousBounded_compContinuous {α δ 𝕜 β γ : Type*}
    [TopologicalSpace α] [TopologicalSpace δ] [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup β] [NormedSpace 𝕜 β] [SeminormedAddCommGroup γ] [NormedSpace 𝕜 γ]
    (g : β →L[𝕜] γ) (f : α →ᵇ β) (a : C(δ, α)) :
    g.compLeftContinuousBounded δ (f.compContinuous a) =
      (g.compLeftContinuousBounded α f).compContinuous a :=
  (rfl)

namespace BoundedContinuousFunction

variable {α 𝕜 β S : Type*} [TopologicalSpace α] [NormedField 𝕜] [SeminormedAddCommGroup β]
  [NormedSpace 𝕜 β] [SetLike S (α →ᵇ β)] [AddSubgroupClass S (α →ᵇ β)]
  [SMulMemClass S 𝕜 (α →ᵇ β)]

/-- Precomposition with a continuous map `a` of `α` that has a continuous inverse `b`, as a linear
isometry equivalence of a submodule `s` of `α →ᵇ β`, such as a `Submodule` or a `Subalgebra`,
preserved by both `a` and `b`. -/
def compContinuousₗᵢ (s : S) (a b : C(α, α)) (hab : ∀ x, a (b x) = x) (hba : ∀ x, b (a x) = x)
    (ha : ∀ f ∈ s, f.compContinuous a ∈ s) (hb : ∀ f ∈ s, f.compContinuous b ∈ s) :
    s ≃ₗᵢ[𝕜] s where
  toFun f := ⟨(f : α →ᵇ β).compContinuous a, ha _ f.2⟩
  invFun f := ⟨(f : α →ᵇ β).compContinuous b, hb _ f.2⟩
  map_add' _ _ := Subtype.ext <| ext fun _ => by simp
  map_smul' _ _ := Subtype.ext <| ext fun _ => by simp
  left_inv f := Subtype.ext <| ext fun x => congrArg (f : α →ᵇ β) (hab x)
  right_inv f := Subtype.ext <| ext fun x => congrArg (f : α →ᵇ β) (hba x)
  norm_map' f := by
    rw [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_norm]
    refine le_antisymm ((f : α →ᵇ β).norm_compContinuous_le a) ?_
    calc ‖(f : α →ᵇ β)‖ = ‖((f : α →ᵇ β).compContinuous a).compContinuous b‖ := by
          congr 1
          ext x
          exact congrArg (f : α →ᵇ β) (hab x).symm
      _ ≤ ‖(f : α →ᵇ β).compContinuous a‖ := norm_compContinuous_le _ _

/-- `compContinuousₗᵢ s a b … f` is the precomposition of `f` with `a`. -/
@[simp]
theorem compContinuousₗᵢ_apply (s : S) (a b : C(α, α)) (hab : ∀ x, a (b x) = x)
    (hba : ∀ x, b (a x) = x) (ha : ∀ f ∈ s, f.compContinuous a ∈ s)
    (hb : ∀ f ∈ s, f.compContinuous b ∈ s) (f : s) :
    (compContinuousₗᵢ (𝕜 := 𝕜) s a b hab hba ha hb f : α →ᵇ β) =
      (f : α →ᵇ β).compContinuous a :=
  (rfl)

/-- The inverse of `compContinuousₗᵢ s a b …` is precomposition with `b`. -/
@[simp]
theorem compContinuousₗᵢ_symm_apply (s : S) (a b : C(α, α)) (hab : ∀ x, a (b x) = x)
    (hba : ∀ x, b (a x) = x) (ha : ∀ f ∈ s, f.compContinuous a ∈ s)
    (hb : ∀ f ∈ s, f.compContinuous b ∈ s) (f : s) :
    ((compContinuousₗᵢ (𝕜 := 𝕜) s a b hab hba ha hb).symm f : α →ᵇ β) =
      (f : α →ᵇ β).compContinuous b :=
  (rfl)

/-- On a discrete space, every bounded real function is a uniform limit of finite-valued
bounded functions: `δ * ⌊f / δ⌋` is within `δ` of `f`. -/
theorem exists_finite_range_dist_lt {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (f : X →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ g : X →ᵇ ℝ, (Set.range g).Finite ∧ dist f g < ε := by
  set δ := ε / 2 with hδ_def
  have hδ : 0 < δ := half_pos hε
  have hrange : (Set.range fun x => δ * ⌊f x / δ⌋).Finite := by
    refine ((Set.finite_Icc ⌊-‖f‖ / δ⌋ ⌊‖f‖ / δ⌋).image fun n : ℤ => δ * n).subset
      (Set.range_subset_iff.2 fun x => Set.mem_image_of_mem _ ?_)
    have hx := abs_le.1 (Real.norm_eq_abs (f x) ▸ f.norm_coe_le_norm x)
    exact ⟨Int.floor_mono (div_le_div_of_nonneg_right hx.1 hδ.le),
      Int.floor_mono (div_le_div_of_nonneg_right hx.2 hδ.le)⟩
  refine ⟨mkOfDiscrete _ _ fun x y =>
      dist_le_diam_of_mem hrange.isBounded (Set.mem_range_self x) (Set.mem_range_self y),
    hrange, lt_of_le_of_lt ((f.dist_le hδ.le).2 fun x => ?_) (by linarith)⟩
  have h : f x - δ * ⌊f x / δ⌋ = δ * Int.fract (f x / δ) := by
    rw [Int.fract, mul_sub, mul_div_cancel₀ _ hδ.ne']
  rw [mkOfDiscrete_apply, Real.dist_eq, h, abs_of_nonneg (mul_nonneg hδ.le (Int.fract_nonneg _))]
  exact mul_le_of_le_one_right hδ.le (Int.fract_lt_one _).le

/-- A nonnegative real bounded continuous function `f` lies within `‖f‖` of the constant `‖f‖`. -/
theorem norm_norm_smul_one_sub_le_of_nonneg {X : Type*} [TopologicalSpace X] {f : X →ᵇ ℝ}
    (hf : 0 ≤ f) : ‖‖f‖ • (1 : X →ᵇ ℝ) - f‖ ≤ ‖f‖ :=
  (norm_le (norm_nonneg f)).2 fun x => by
    have h₁ := f.apply_le_norm x
    have h₀ : 0 ≤ f x := hf x
    simp only [FunLike.coe_sub, FunLike.coe_smul, FunLike.coe_one, Pi.sub_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_one,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith

section Dilate

variable {β : Type*} [PseudoMetricSpace β]

/-- The dilation of a bounded sequence `f` by `k`: the sequence `n ↦ f (n / k)`, with
natural-number division. For `k ≥ 1` it repeats every entry of `f` exactly `k` times. -/
def dilate (f : ℕ →ᵇ β) (k : ℕ) : ℕ →ᵇ β :=
  f.compContinuous ⟨(· / k), continuous_of_discreteTopology⟩

@[simp]
theorem dilate_apply (f : ℕ →ᵇ β) (k n : ℕ) : f.dilate k n = f (n / k) :=
  (rfl)

@[simp]
theorem dilate_one (f : ℕ →ᵇ β) : f.dilate 1 = f := by
  ext n
  simp

/-- Dilations compose multiplicatively, since `n / l / k = n / (k * l)`. -/
@[simp]
theorem dilate_dilate (f : ℕ →ᵇ β) (k l : ℕ) : (f.dilate k).dilate l = f.dilate (k * l) := by
  ext n
  simp [Nat.div_div_eq_div_mul, mul_comm]

@[simp]
theorem zero_dilate [Zero β] (k : ℕ) : (0 : ℕ →ᵇ β).dilate k = 0 := by
  ext n
  simp

@[simp]
theorem smul_dilate {𝕜 : Type*} [PseudoMetricSpace 𝕜] [Zero 𝕜] [Zero β] [SMul 𝕜 β]
    [IsBoundedSMul 𝕜 β] (c : 𝕜) (f : ℕ →ᵇ β) (k : ℕ) : (c • f).dilate k = c • f.dilate k := by
  ext n
  simp

@[simp]
theorem add_dilate [Add β] [BoundedAdd β] [ContinuousAdd β] (f g : ℕ →ᵇ β) (k : ℕ) :
    (f + g).dilate k = f.dilate k + g.dilate k :=
  (rfl)

@[simp]
theorem sub_dilate [Sub β] [BoundedSub β] [ContinuousSub β] (f g : ℕ →ᵇ β) (k : ℕ) :
    (f - g).dilate k = f.dilate k - g.dilate k :=
  (rfl)

end Dilate

/-- Dilations commute with negation. This is stated for a `SeminormedAddCommGroup` codomain, the
setting of Mathlib's `Neg` instance on bounded continuous functions. -/
@[simp]
theorem neg_dilate {β : Type*} [SeminormedAddCommGroup β] (f : ℕ →ᵇ β) (k : ℕ) :
    (-f).dilate k = -f.dilate k := by
  ext n
  simp

section CompactUniform

open Filter Set Topology

/-- Finite-subcover upgrade from pointwise eventual bounds along `l : Filter α` to a
compact-uniform eventual bound for a family `F : X → (α →ᵇ E)` continuous on a compact set `K`. -/
theorem eventually_forall_compact_norm_lt_add
    {α X E : Type*} [TopologicalSpace α] [TopologicalSpace X] [SeminormedAddCommGroup E]
    {l : Filter α} {F : X → (α →ᵇ E)} {g : X → ℝ} {K : Set X}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hg : ContinuousOn g K)
    (hlim : ∀ x ∈ K, ∀ {δ : ℝ}, 0 < δ → ∀ᶠ t in l, ‖F x t‖ < g x + δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, ∀ x ∈ K, ‖F x t‖ < g x + ε := by
  have hε3 : 0 < ε / 3 := by linarith
  have hnhds : ∀ x : K, ∃ U : Set X, IsOpen U ∧ (x : X) ∈ U ∧
      ∀ y ∈ K, y ∈ U → ‖F y - F x‖ < ε / 3 ∧ g x < g y + ε / 3 := by
    intro ⟨x, hxK⟩
    have hFx : ∀ᶠ y in 𝓝[K] x, dist (F y) (F x) < ε / 3 :=
      (hF x hxK).eventually (ball_mem_nhds (F x) hε3)
    have hgx : ∀ᶠ y in 𝓝[K] x, dist (g y) (g x) < ε / 3 :=
      (hg x hxK).eventually (ball_mem_nhds (g x) hε3)
    obtain ⟨U, hU_nhds, hU_sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (hFx.and hgx)
    obtain ⟨V, hV_sub, hV_open, hxV⟩ := mem_nhds_iff.mp hU_nhds
    refine ⟨V, hV_open, hxV, fun y hyK hyV ↦ ?_⟩
    obtain ⟨hdF, hdg⟩ := hU_sub ⟨hV_sub hyV, hyK⟩
    rw [dist_eq_norm] at hdF
    rw [Real.dist_eq] at hdg
    exact ⟨hdF, by linarith [(abs_lt.mp hdg).1]⟩
  choose U hU_open hxU hU_est using hnhds
  obtain ⟨s, hs_cover⟩ :=
    hK.elim_finite_subcover (fun i : K ↦ U i) (fun i ↦ hU_open i) fun x hx ↦
      mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  have hev_all : ∀ᶠ t in l, ∀ i ∈ s, ‖F i t‖ < g i + ε / 3 :=
    (eventually_all_finset s).mpr fun i _ ↦ hlim i.1 i.2 hε3
  filter_upwards [hev_all] with t ht x hxK
  obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs_cover hxK)
  obtain ⟨hFi, hgi⟩ := hU_est i x hxK hxi
  have hti := ht i his
  have hdiff_t : ‖F x t - F i t‖ ≤ ‖F x - F i‖ :=
    (F x - F i).norm_coe_le_norm t
  have htri : ‖F x t‖ ≤ ‖F x - F i‖ + ‖F i t‖ :=
    calc
      ‖F x t‖ = ‖(F x t - F i t) + F i t‖ := by rw [sub_add_cancel]
      _ ≤ ‖F x t - F i t‖ + ‖F i t‖ := norm_add_le _ _
      _ ≤ ‖F x - F i‖ + ‖F i t‖ := add_le_add_left hdiff_t _
  linarith

/-- Finite-subcover upgrade from pointwise convergence to `0` along `l : Filter α` to a
compact-uniform eventual norm bound for a family `F : X → (α →ᵇ E)` continuous on a compact set
`K`. -/
theorem eventually_forall_compact_norm_lt
    {α X E : Type*} [TopologicalSpace α] [TopologicalSpace X] [SeminormedAddCommGroup E]
    {l : Filter α} {F : X → (α →ᵇ E)} {K : Set X}
    (hK : IsCompact K) (hF : ContinuousOn F K)
    (hlim : ∀ x ∈ K, Tendsto (fun t ↦ F x t) l (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in l, ∀ x ∈ K, ‖F x t‖ < ε := by
  have h := eventually_forall_compact_norm_lt_add (g := fun _ ↦ 0) hK hF continuousOn_const
    (fun x hx {δ} hδ ↦ by
      simpa only [zero_add] using
        (tendsto_order.mp (tendsto_zero_iff_norm_tendsto_zero.mp (hlim x hx))).2 δ hδ) hε
  simpa only [zero_add] using h

end CompactUniform

end BoundedContinuousFunction
