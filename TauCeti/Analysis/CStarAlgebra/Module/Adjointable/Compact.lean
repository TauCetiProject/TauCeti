/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Rank-one and module-compact operators on Hilbert C⋆-modules

For vectors `x : F` and `y : E` in Hilbert C⋆-modules over `A`, the rank-one operator
`θ_{x,y} : E → F` is `z ↦ ⟪y, z⟫_A • x`. It is adjointable with adjoint `θ_{y,x}`, and these
operators are closed under composition with arbitrary adjointable maps on either side. The
module-compact operators `K_A(E, F)` are the norm closure of the linear span of the rank-one
operators inside the adjointable operators `L_A(E, F)`. They are generally *not* the compact
operators of Banach-space theory: for a unital C⋆-algebra `A`, the identity of the right
self-module `A` is the rank-one operator `θ_{1,1}`.

For right Hilbert `B`-modules (`A = Bᵐᵒᵖ`), `θ_{x,y}` is the usual `z ↦ x ⟨y, z⟩_B`, and the
composition law `θ_{x,y} θ_{u,v} = θ_{⟪y, u⟫_A • x, v}` reads `θ_{x,y} θ_{u,v} = θ_{x ⟨y, u⟩_B, v}`.

The module-compact operators are the analytic input for the multiplier description
`L_A(E) ≅ M(K_A(E))`, for frames and finitely generated projective modules, and for imprimitivity
bimodules.

## Main declarations

* `TauCeti.AdjointableMap.rankOne A x y`: the rank-one operator `θ_{x,y}`, with
  `adjoint_rankOne`, `norm_rankOne_le`, `comp_rankOne`, `rankOne_comp`, `rankOne_comp_rankOne`
  (and `star_rankOne`, `mul_rankOne`, `rankOne_mul`, `rankOne_mul_rankOne` in
  `AdjointableMap A E E`), sesquilinearity, the coefficient laws `rankOne_smul_coeff_left` and
  `rankOne_smul_coeff_right`, and positivity of `θ_{x,x}` (`rankOne_self_nonneg`).
* `TauCeti.AdjointableMap.compactOperator A E F`: the closed subspace `K_A(E, F)` of
  `AdjointableMap A E F`, characterized as the smallest closed subspace containing every rank-one
  operator (`compactOperator_le_iff`) and by finite-sum approximation
  (`mem_compactOperator_iff_forall_exists_sum`).
* `TauCeti.AdjointableMap.map_mem_compactOperator`: a continuous (semi)linear map sending
  rank-one operators into `K_A` preserves `K_A`.
* `TauCeti.AdjointableMap.comp_mem_compactOperator_left`,
  `TauCeti.AdjointableMap.comp_mem_compactOperator_right`, and
  `TauCeti.AdjointableMap.adjoint_mem_compactOperator_iff`: `K_A` absorbs composition with
  adjointable operators on both sides and is closed under adjoints.
* `TauCeti.AdjointableMap.compactOperatorIdeal A E`: `K_A(E)` as a closed two-sided ideal of
  `AdjointableMap A E E`. For complete `E` it is therefore a nonunital C⋆-algebra, by
  `TwoSidedIdeal.nonUnitalCStarAlgebra` in `TauCeti.Analysis.CStarAlgebra.Ideal`.
* `TauCeti.AdjointableMap.eq_of_forall_compactOperator_apply_eq`,
  `TauCeti.AdjointableMap.eq_of_forall_compactOperator_comp_eq`, and
  `TauCeti.AdjointableMap.eq_of_forall_comp_compactOperator_eq`: module-compact operators separate
  vectors and adjointable operators on both sides.
* `TauCeti.AdjointableMap.tendsto_comp_of_mem_compactOperator_of_eventually_norm_le` and
  `TauCeti.AdjointableMap.tendsto_compactOperator_comp_of_eventually_norm_le`: bounded strongly
  convergent (respectively adjoint-strongly convergent) nets converge in operator norm after
  composing with a module-compact operator.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Section 2.2.
-/

public section

open CStarModule Filter Topology

namespace TauCeti

namespace AdjointableMap

variable {A E F G : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul A G] [CStarModule A G]

/-! ### Rank-one operators -/

section RankOne

variable (A) in
/-- The bounded complex-linear map `z ↦ ⟪y, z⟫_A • x` underlying `rankOne A x y`. -/
private noncomputable def rankOneCLM (x : F) (y : E) : E →L[ℂ] F :=
  LinearMap.mkContinuous
    { toFun z := inner A y z • x
      map_add' z w := by rw [CStarModule.inner_add_right, CStarModule.add_smul]
      map_smul' c z := by
        rw [inner_smul_right_complex, (CStarModule.isScalarTower A F).smul_assoc,
          RingHom.id_apply] }
    (‖x‖ * ‖y‖) (CStarModule.norm_inner_smul_le A x y)

private theorem rankOneCLM_apply (x : F) (y z : E) :
    rankOneCLM A x y z = inner A y z • x :=
  (rfl)

variable (A) in
/-- The rank-one operator `θ_{x,y} : E → F`, `z ↦ ⟪y, z⟫_A • x`, an adjointable operator with
adjoint `θ_{y,x}`. For right Hilbert `B`-modules (`A = Bᵐᵒᵖ`) it is `z ↦ x ⟨y, z⟩_B`. -/
noncomputable def rankOne (x : F) (y : E) : AdjointableMap A E F where
  toContinuousLinearMap := rankOneCLM A x y
  adjoint' := rankOneCLM A y x
  inner_map_eq' z w := by
    rw [rankOneCLM_apply, rankOneCLM_apply, inner_op_smul_left, inner_op_smul_right, star_inner]

@[simp]
theorem rankOne_apply (x : F) (y z : E) : rankOne A x y z = inner A y z • x :=
  (rfl)

/-- The adjoint of `θ_{x,y}` is `θ_{y,x}`. -/
@[simp]
theorem adjoint_rankOne (x : F) (y : E) : (rankOne A x y).adjoint = rankOne A y x :=
  -- The adjoint field of `rankOne A x y` is by construction the map underlying `rankOne A y x`.
  ext fun z ↦ adjoint_mk_apply _ _ _ z

/-- The norm bound `‖θ_{x,y}‖ ≤ ‖x‖ ‖y‖`. -/
theorem norm_rankOne_le (x : F) (y : E) : ‖rankOne A x y‖ ≤ ‖x‖ * ‖y‖ :=
  opNorm_le_bound _ (by positivity) (CStarModule.norm_inner_smul_le A x y)

/-- Composing on the left with an adjointable operator: `T θ_{x,y} = θ_{T x, y}`. -/
@[simp]
theorem comp_rankOne (T : AdjointableMap A F G) (x : F) (y : E) :
    T.comp (rankOne A x y) = rankOne A (T x) y :=
  ext fun z ↦ by simp

/-- Composing on the right with an adjointable operator: `θ_{x,y} T = θ_{x, T* y}`. -/
theorem rankOne_comp (x : F) (y : E) (T : AdjointableMap A G E) :
    (rankOne A x y).comp T = rankOne A x (T.adjoint y) :=
  ext fun z ↦ by simp [adjoint_inner_left]

/-- The composition law `θ_{x,y} θ_{u,v} = θ_{⟪y, u⟫_A • x, v}`; for right Hilbert `B`-modules
this is `θ_{x,y} θ_{u,v} = θ_{x ⟨y, u⟩_B, v}`. -/
theorem rankOne_comp_rankOne (x : G) (y u : F) (v : E) :
    (rankOne A x y).comp (rankOne A u v) = rankOne A (inner A y u • x) v := by
  rw [comp_rankOne, rankOne_apply]

/-- The adjoint of `θ_{x,y}` in the C⋆-algebra `AdjointableMap A E E` is `θ_{y,x}`. -/
@[simp]
theorem star_rankOne (x y : E) : star (rankOne A x y) = rankOne A y x :=
  adjoint_rankOne x y

/-- Multiplying on the left in `AdjointableMap A E E`: `T θ_{x,y} = θ_{T x, y}`. -/
@[simp]
theorem mul_rankOne (T : AdjointableMap A E E) (x y : E) :
    T * rankOne A x y = rankOne A (T x) y :=
  comp_rankOne T x y

/-- Multiplying on the right in `AdjointableMap A E E`: `θ_{x,y} T = θ_{x, T⋆ y}`. -/
theorem rankOne_mul (x y : E) (T : AdjointableMap A E E) :
    rankOne A x y * T = rankOne A x (star T y) :=
  rankOne_comp x y T

/-- The product law `θ_{x,y} θ_{u,v} = θ_{⟪y, u⟫_A • x, v}` in `AdjointableMap A E E`. -/
theorem rankOne_mul_rankOne (x y u v : E) :
    rankOne A x y * rankOne A u v = rankOne A (inner A y u • x) v :=
  rankOne_comp_rankOne x y u v

/-- Moving a coefficient across a rank-one operator: `θ_{a • x, y} = θ_{x, a⋆ • y}`; for right
Hilbert `B`-modules this is `θ_{x b, y} = θ_{x, y b⋆}`. -/
theorem rankOne_smul_coeff_left (a : A) (x : F) (y : E) :
    rankOne A (a • x) y = rankOne A x (star a • y) :=
  ext fun z ↦ by
    rw [rankOne_apply, rankOne_apply, inner_op_smul_left, star_star,
      (semigroupAction A F).mul_smul]

/-- Moving a coefficient across a rank-one operator: `θ_{x, a • y} = θ_{a⋆ • x, y}`; for right
Hilbert `B`-modules this is `θ_{x, y b} = θ_{x b⋆, y}`. -/
theorem rankOne_smul_coeff_right (a : A) (x : F) (y : E) :
    rankOne A x (a • y) = rankOne A (star a • x) y := by
  rw [rankOne_smul_coeff_left, star_star]

@[simp]
theorem rankOne_zero_left (y : E) : rankOne A (0 : F) y = 0 :=
  ext fun z ↦ by rw [rankOne_apply, (distribSMul A F).smul_zero, zero_apply]

@[simp]
theorem rankOne_zero_right (x : F) : rankOne A x (0 : E) = 0 :=
  ext fun z ↦ by
    rw [rankOne_apply, CStarModule.inner_zero_left, (smulWithZero A F).zero_smul, zero_apply]

@[simp]
theorem rankOne_add_left (x₁ x₂ : F) (y : E) :
    rankOne A (x₁ + x₂) y = rankOne A x₁ y + rankOne A x₂ y :=
  ext fun z ↦ by
    rw [add_apply, rankOne_apply, rankOne_apply, rankOne_apply, (distribSMul A F).smul_add]

@[simp]
theorem rankOne_add_right (x : F) (y₁ y₂ : E) :
    rankOne A x (y₁ + y₂) = rankOne A x y₁ + rankOne A x y₂ :=
  ext fun z ↦ by
    rw [add_apply, rankOne_apply, rankOne_apply, rankOne_apply, CStarModule.inner_add_left,
      CStarModule.add_smul]

@[simp]
theorem rankOne_smul_left (c : ℂ) (x : F) (y : E) :
    rankOne A (c • x) y = c • rankOne A x y :=
  ext fun z ↦ by
    rw [smul_apply, rankOne_apply, rankOne_apply, (CStarModule.smulCommClass A F).smul_comm]

@[simp]
theorem rankOne_smul_right (c : ℂ) (x : F) (y : E) :
    rankOne A x (c • y) = star c • rankOne A x y :=
  ext fun z ↦ by
    rw [smul_apply, rankOne_apply, rankOne_apply, inner_smul_left_complex,
      (CStarModule.isScalarTower A F).smul_assoc]

@[simp]
theorem rankOne_neg_left (x : F) (y : E) : rankOne A (-x) y = -rankOne A x y :=
  eq_neg_of_add_eq_zero_left <| by rw [← rankOne_add_left, neg_add_cancel, rankOne_zero_left]

@[simp]
theorem rankOne_neg_right (x : F) (y : E) : rankOne A x (-y) = -rankOne A x y :=
  eq_neg_of_add_eq_zero_left <| by rw [← rankOne_add_right, neg_add_cancel, rankOne_zero_right]

@[simp]
theorem rankOne_sub_left (x₁ x₂ : F) (y : E) :
    rankOne A (x₁ - x₂) y = rankOne A x₁ y - rankOne A x₂ y := by
  rw [sub_eq_add_neg, rankOne_add_left, rankOne_neg_left, ← sub_eq_add_neg]

@[simp]
theorem rankOne_sub_right (x : F) (y₁ y₂ : E) :
    rankOne A x (y₁ - y₂) = rankOne A x y₁ - rankOne A x y₂ := by
  rw [sub_eq_add_neg, rankOne_add_right, rankOne_neg_right, ← sub_eq_add_neg]

/-- The rank-one operator `θ_{x,x}` is self-adjoint. -/
theorem isSelfAdjoint_rankOne_self (x : E) : IsSelfAdjoint (rankOne A x x) :=
  isSelfAdjoint_iff_adjoint_eq.mpr (adjoint_rankOne x x)

/-- The rank-one operator `θ_{x,x}` is positive in the C⋆-algebra `AdjointableMap A E E`:
`⟪z, θ_{x,x} z⟫_A = ⟪x, z⟫_A ⟪x, z⟫_A⋆`. -/
theorem rankOne_self_nonneg [CompleteSpace E] (x : E) : 0 ≤ rankOne A x x :=
  nonneg_iff_forall_inner_nonneg.mpr fun z ↦ by
    rw [rankOne_apply, inner_op_smul_right, ← star_inner x z]
    exact mul_star_self_nonneg _

end RankOne

/-! ### Module-compact operators -/

section Compact

variable (A E F) in
/-- The module-compact operators `K_A(E, F)`: the norm closure of the linear span of the rank-one
operators `θ_{x,y}` in `AdjointableMap A E F`. These need not be compact operators in the sense of
Banach spaces. -/
noncomputable def compactOperator : Submodule ℂ (AdjointableMap A E F) :=
  (Submodule.span ℂ {T | ∃ (x : F) (y : E), rankOne A x y = T}).topologicalClosure

theorem compactOperator_def :
    compactOperator A E F =
      (Submodule.span ℂ {T | ∃ (x : F) (y : E), rankOne A x y = T}).topologicalClosure :=
  (rfl)

@[simp]
theorem rankOne_mem_compactOperator (x : F) (y : E) : rankOne A x y ∈ compactOperator A E F :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨x, y, rfl⟩)

theorem isClosed_compactOperator : IsClosed (compactOperator A E F : Set (AdjointableMap A E F)) :=
  Submodule.isClosed_topologicalClosure _

/-- `K_A(E, F)` is the smallest closed subspace of `AdjointableMap A E F` containing every
rank-one operator. -/
theorem compactOperator_le_iff {p : Submodule ℂ (AdjointableMap A E F)}
    (hp : IsClosed (p : Set (AdjointableMap A E F))) :
    compactOperator A E F ≤ p ↔ ∀ (x : F) (y : E), rankOne A x y ∈ p := by
  refine ⟨fun h x y ↦ h (rankOne_mem_compactOperator x y), fun h ↦ ?_⟩
  refine Submodule.topologicalClosure_minimal _ ?_ hp
  rw [Submodule.span_le]
  rintro _ ⟨x, y, rfl⟩
  exact h x y

/-- The linear span of the rank-one operators consists of the finite sums of rank-one
operators. -/
theorem mem_span_rankOne_iff {T : AdjointableMap A E F} :
    T ∈ Submodule.span ℂ {T | ∃ (x : F) (y : E), rankOne A x y = T} ↔
      ∃ (n : ℕ) (x : Fin n → F) (y : Fin n → E), ∑ i, rankOne A (x i) (y i) = T := by
  refine ⟨fun hT ↦ ?_, ?_⟩
  · obtain ⟨n, c, S, rfl⟩ := Submodule.mem_span_set'.mp hT
    choose x y hxy using fun i ↦ (S i).property
    exact ⟨n, fun i ↦ c i • x i, y, Finset.sum_congr rfl fun i _ ↦ by
      rw [rankOne_smul_left, hxy]⟩
  · rintro ⟨n, x, y, rfl⟩
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ⟨x i, y i, rfl⟩

/-- Finite-sum approximation: an adjointable operator is module-compact if and only if it is a
norm limit of finite sums of rank-one operators. -/
theorem mem_compactOperator_iff_forall_exists_sum {T : AdjointableMap A E F} :
    T ∈ compactOperator A E F ↔ ∀ ε > 0, ∃ (n : ℕ) (x : Fin n → F) (y : Fin n → E),
      ‖T - ∑ i, rankOne A (x i) (y i)‖ < ε := by
  rw [compactOperator_def, ← SetLike.mem_coe, Submodule.topologicalClosure_coe,
    Metric.mem_closure_iff]
  refine forall₂_congr fun ε _ ↦ ⟨?_, ?_⟩
  · rintro ⟨S, hS, hTS⟩
    obtain ⟨n, x, y, rfl⟩ := mem_span_rankOne_iff.mp hS
    exact ⟨n, x, y, by rwa [← dist_eq_norm]⟩
  · rintro ⟨n, x, y, h⟩
    exact ⟨_, mem_span_rankOne_iff.mpr ⟨n, x, y, rfl⟩, by rwa [dist_eq_norm]⟩

/-- A continuous (semi)linear map between spaces of adjointable operators that sends every
rank-one operator into `K_A` sends all of `K_A` into `K_A`. -/
theorem map_mem_compactOperator {E' F' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [SMul A E'] [CStarModule A E'] [NormedAddCommGroup F'] [NormedSpace ℂ F'] [SMul A F']
    [CStarModule A F'] {σ : ℂ →+* ℂ}
    (L : AdjointableMap A E F →ₛₗ[σ] AdjointableMap A E' F') (hL : Continuous L)
    (h : ∀ (x : F) (y : E), L (rankOne A x y) ∈ compactOperator A E' F')
    {T : AdjointableMap A E F} (hT : T ∈ compactOperator A E F) :
    L T ∈ compactOperator A E' F' :=
  (compactOperator_le_iff (p := (compactOperator A E' F').comap L)
    (isClosed_compactOperator.preimage hL)).mpr h hT

/-- `K_A` absorbs composition on the left: `S T ∈ K_A(E, G)` for `T ∈ K_A(E, F)`. -/
theorem comp_mem_compactOperator_left (S : AdjointableMap A F G) {T : AdjointableMap A E F}
    (hT : T ∈ compactOperator A E F) : S.comp T ∈ compactOperator A E G := by
  simpa using map_mem_compactOperator (compL S).toLinearMap (compL S).continuous
    (fun x y ↦ by simp) hT

/-- `K_A` absorbs composition on the right: `S T ∈ K_A(E, G)` for `S ∈ K_A(F, G)`. -/
theorem comp_mem_compactOperator_right {S : AdjointableMap A F G}
    (hS : S ∈ compactOperator A F G) (T : AdjointableMap A E F) :
    S.comp T ∈ compactOperator A E G := by
  simpa using map_mem_compactOperator ((compL (A := A)).flip T).toLinearMap
    ((compL (A := A)).flip T).continuous (fun x y ↦ by simp [rankOne_comp]) hS

/-- The adjoint of a module-compact operator is module-compact. -/
theorem adjoint_mem_compactOperator {T : AdjointableMap A E F}
    (hT : T ∈ compactOperator A E F) : T.adjoint ∈ compactOperator A F E := by
  simpa using map_mem_compactOperator adjointₗᵢ.toLinearEquiv.toLinearMap
    adjointₗᵢ.continuous (fun x y ↦ by simp) hT

@[simp]
theorem adjoint_mem_compactOperator_iff {T : AdjointableMap A E F} :
    T.adjoint ∈ compactOperator A F E ↔ T ∈ compactOperator A E F :=
  ⟨fun h ↦ adjoint_adjoint T ▸ adjoint_mem_compactOperator h, adjoint_mem_compactOperator⟩

/-- If `θ_{x, x} x = 0`, then `x = 0`. -/
theorem eq_zero_of_rankOne_self_apply_eq_zero {x : E} (h : rankOne A x x x = 0) : x = 0 := by
  refine (CStarModule.inner_self (A := A)).mp (mul_star_self_eq_zero.mp ?_)
  have hinner : inner A x (rankOne A x x x) = 0 := by rw [h, CStarModule.inner_zero_right]
  rw [rankOne_apply, CStarModule.inner_op_smul_right] at hinner
  nth_rw 2 [← CStarModule.isSelfAdjoint_inner_self.star_eq] at hinner
  exact hinner

/-- A vector annihilated by every module-compact operator vanishes. -/
theorem eq_zero_of_forall_compactOperator_apply_eq_zero {x : E}
    (h : ∀ k ∈ compactOperator A E E, k x = 0) : x = 0 :=
  eq_zero_of_rankOne_self_apply_eq_zero (h _ (rankOne_mem_compactOperator x x))

/-- Vectors on which all module-compact operators agree are equal. -/
theorem eq_of_forall_compactOperator_apply_eq {x y : E}
    (h : ∀ k ∈ compactOperator A E E, k x = k y) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_forall_compactOperator_apply_eq_zero fun k hk ↦ by
    rw [map_sub, h k hk, sub_self]

/-- An adjointable operator `T : L_A(E, F)` whose composition with every module-compact
operator vanishes on the right is zero. -/
theorem eq_zero_of_forall_compactOperator_comp_eq_zero {T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A E E, T.comp k = 0) : T = 0 := by
  refine ext fun x ↦ eq_zero_of_rankOne_self_apply_eq_zero (A := A) ?_
  have happ : (T.comp (rankOne A x (T.adjoint (T x)))) x = 0 := by
    rw [h _ (rankOne_mem_compactOperator _ _), zero_apply]
  simpa [comp_rankOne, rankOne_apply, T.adjoint_inner_left] using happ

/-- Two adjointable operators `S, T : L_A(E, F)` satisfying `S ∘ k = T ∘ k` for all
`k ∈ K_A(E)` are equal. -/
theorem eq_of_forall_compactOperator_comp_eq {S T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A E E, S.comp k = T.comp k) : S = T :=
  sub_eq_zero.mp <| eq_zero_of_forall_compactOperator_comp_eq_zero fun k hk ↦ by
    rw [sub_comp, h k hk, sub_self]

/-- An adjointable operator `T : L_A(E, F)` whose composition with every module-compact
operator vanishes on the left is zero. -/
theorem eq_zero_of_forall_comp_compactOperator_eq_zero {T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A F F, k.comp T = 0) : T = 0 := by
  rw [← adjoint_eq_zero_iff]
  refine eq_zero_of_forall_compactOperator_comp_eq_zero fun k hk ↦ ?_
  have hkT := congrArg adjoint (h k.adjoint (adjoint_mem_compactOperator hk))
  simpa [adjoint_comp] using hkT

/-- Two adjointable operators `S, T : L_A(E, F)` satisfying `k ∘ S = k ∘ T` for all
`k ∈ K_A(F)` are equal. -/
theorem eq_of_forall_comp_compactOperator_eq {S T : AdjointableMap A E F}
    (h : ∀ k ∈ compactOperator A F F, k.comp S = k.comp T) : S = T :=
  sub_eq_zero.mp <| eq_zero_of_forall_comp_compactOperator_eq_zero fun k hk ↦ by
    rw [comp_sub, h k hk, sub_self]

variable (A E) in
/-- The module-compact operators `K_A(E)` as a two-sided ideal of `AdjointableMap A E E`. It is
closed (`isClosed_compactOperatorIdeal`) and, for complete `E`, a nonunital C⋆-algebra. -/
noncomputable def compactOperatorIdeal : TwoSidedIdeal (AdjointableMap A E E) :=
  .mk' (compactOperator A E E) (zero_mem _) add_mem neg_mem
    (fun {S _} hT ↦ comp_mem_compactOperator_left S hT)
    (fun {_ T} hS ↦ comp_mem_compactOperator_right hS T)

@[simp]
theorem mem_compactOperatorIdeal {T : AdjointableMap A E E} :
    T ∈ compactOperatorIdeal A E ↔ T ∈ compactOperator A E E :=
  TwoSidedIdeal.mem_mk' _ _ _ _ _ _ T

@[simp]
theorem coe_compactOperatorIdeal :
    (compactOperatorIdeal A E : Set (AdjointableMap A E E)) = compactOperator A E E :=
  TwoSidedIdeal.coe_mk' _ _ _ _ _ _

instance isClosed_compactOperatorIdeal :
    IsClosed (compactOperatorIdeal A E : Set (AdjointableMap A E E)) := by
  rw [coe_compactOperatorIdeal]
  exact isClosed_compactOperator

end Compact

/-! ### Strong-to-norm convergence on composition with module-compact operators -/

section StrongToNorm

/-- Along any filter of adjointable operators converging strongly on `E`, composition on the right
with a finite sum of rank-one operators converges in operator norm. -/
theorem tendsto_comp_sum_rankOne_of_tendsto
    {ι : Type*} {l : Filter ι} {f : ι → AdjointableMap A E F} {T : AdjointableMap A E F}
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    {n : ℕ} (x : Fin n → E) (y : Fin n → G) :
    Tendsto (fun i ↦ (f i).comp (∑ j, rankOne A (x j) (y j))) l
      (𝓝 (T.comp (∑ j, rankOne A (x j) (y j)))) := by
  have hrank (u : E) (v : G) :
      Tendsto (fun i ↦ (f i).comp (rankOne A u v)) l (𝓝 (T.comp (rankOne A u v))) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero (fun _ ↦ norm_nonneg _)
      (fun i ↦ ?_) (by simpa only [zero_mul] using
        (tendsto_iff_norm_sub_tendsto_zero.mp (hf u)).mul_const ‖v‖)
    rw [comp_rankOne, comp_rankOne, ← rankOne_sub_left]
    exact norm_rankOne_le (f i u - T u) v
  have hcomp (S : AdjointableMap A E F) :
      S.comp (∑ j, rankOne A (x j) (y j)) = ∑ j, S.comp (rankOne A (x j) (y j)) := by
    ext z; simp
  simp_rw [hcomp]
  exact tendsto_finsetSum Finset.univ fun j _ ↦ hrank (x j) (y j)

/-- Along any norm-bounded filter of adjointable operators converging strongly on `E`,
composition on the right with any module-compact operator `k ∈ K_A(G, E)` converges in operator
norm. -/
theorem tendsto_comp_of_mem_compactOperator_of_eventually_norm_le
    {ι : Type*} {l : Filter ι} {f : ι → AdjointableMap A E F} {T : AdjointableMap A E F}
    {C : ℝ} (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf : ∀ x : E, Tendsto (fun i ↦ f i x) l (𝓝 (T x)))
    {k : AdjointableMap A G E} (hk : k ∈ compactOperator A G E) :
    Tendsto (fun i ↦ (f i).comp k) l (𝓝 (T.comp k)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M : ℝ := max C 0 + ‖T‖ + 1
  have hM : 0 < M := by positivity
  obtain ⟨n, x, y, hkS⟩ :=
    mem_compactOperator_iff_forall_exists_sum.mp hk (ε / (2 * M)) (by positivity)
  set S : AdjointableMap A G E := ∑ j, rankOne A (x j) (y j)
  have hS_lim : ∀ᶠ i in l, dist ((f i).comp S) (T.comp S) < ε / 2 :=
    Metric.tendsto_nhds.mp (tendsto_comp_sum_rankOne_of_tendsto hf x y) (ε / 2) (by positivity)
  filter_upwards [hC, hS_lim] with i hiC hiS
  rw [dist_eq_norm] at hiS ⊢
  have hsplit : (f i).comp k - T.comp k =
      ((f i).comp (k - S) - T.comp (k - S)) + ((f i).comp S - T.comp S) := by
    rw [comp_sub, comp_sub]; abel
  have hdiff_norm : ‖(f i).comp (k - S) - T.comp (k - S)‖ ≤ M * ‖k - S‖ := by
    calc ‖(f i).comp (k - S) - T.comp (k - S)‖
        ≤ ‖(f i).comp (k - S)‖ + ‖T.comp (k - S)‖ := norm_sub_le _ _
      _ ≤ ‖f i‖ * ‖k - S‖ + ‖T‖ * ‖k - S‖ :=
          add_le_add (opNorm_comp_le (f i) (k - S)) (opNorm_comp_le T (k - S))
      _ = (‖f i‖ + ‖T‖) * ‖k - S‖ := by ring
      _ ≤ M * ‖k - S‖ := by gcongr; linarith [le_max_left C 0]
  have hterm1 : ‖(f i).comp (k - S) - T.comp (k - S)‖ ≤ ε / 2 :=
    hdiff_norm.trans <| (mul_le_mul_of_nonneg_left hkS.le hM.le).trans_eq <| by
      field_simp
  calc ‖(f i).comp k - T.comp k‖
      ≤ ‖(f i).comp (k - S) - T.comp (k - S)‖ + ‖(f i).comp S - T.comp S‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt hterm1 hiS
    _ = ε := add_halves ε

/-- Along any norm-bounded filter of adjointable operators whose adjoints converge strongly on
`F`, composition on the left with any module-compact operator `k ∈ K_A(F, G)` converges in
operator norm. -/
theorem tendsto_compactOperator_comp_of_eventually_norm_le
    {ι : Type*} {l : Filter ι} {f : ι → AdjointableMap A E F} {T : AdjointableMap A E F}
    {C : ℝ} (hC : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hf_adj : ∀ y : F, Tendsto (fun i ↦ (f i).adjoint y) l (𝓝 (T.adjoint y)))
    {k : AdjointableMap A F G} (hk : k ∈ compactOperator A F G) :
    Tendsto (fun i ↦ k.comp (f i)) l (𝓝 (k.comp T)) := by
  have hC_adj : ∀ᶠ i in l, ‖(f i).adjoint‖ ≤ C := by
    filter_upwards [hC] with i hi
    simpa [norm_adjoint] using hi
  have hcomp := tendsto_comp_of_mem_compactOperator_of_eventually_norm_le hC_adj hf_adj
    (adjoint_mem_compactOperator hk)
  have hadj := continuous_adjoint.continuousAt.tendsto.comp hcomp
  simpa [Function.comp_def, ← adjoint_comp] using hadj

end StrongToNorm

end AdjointableMap

end TauCeti
