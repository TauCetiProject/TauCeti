/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

import TauCeti.Analysis.InnerProductSpace.LinearPMap.GraphProjection
import TauCeti.Analysis.InnerProductSpace.LinearPMap.SubmoduleAdjoint
import TauCeti.LinearAlgebra.LinearPMap.Basic
import TauCeti.Topology.Algebra.Module.LinearPMap.GraphCore

/-!
# The operators `T†T` and `T T†` for a closed densely defined operator

For a partially defined operator `T`, the domain of `LinearPMap.adjointComp T` consists
of the vectors `x` in the domain of `T` for which `T x` belongs to the domain of `T†`,
and dually `LinearPMap.compAdjoint T` is `T T†` on `{y ∈ D(T†) | T† y ∈ D(T)}`.
If `T` is closed and densely defined between real or complex Hilbert spaces, then both
`T†T` and `T T†` are densely defined, nonnegative and self-adjoint, `D(T†T)` is a graph
core for `T`, and `D(T T†)` is a graph core for `T†`.

Projecting `(z, 0)` onto the closed graph of `T` gives a solution of
`x + T†T x = z`. This surjectivity and the form identity give density of the
composition domain, equality with the adjoint, and density of the restricted graph in
the graph of `T`. By `T†† = T`, the dual statements for `T T†` follow from `T.compAdjoint =
(T†).adjointComp`.

## References

* J. von Neumann, *Über adjungierte Funktionaloperatoren*, Ann. of Math. (2) **33** (1932),
  294–310.
* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), Theorem V.3.24.
* Joachim Weidmann, *Linear Operators in Hilbert Spaces*, Chapter 5.
* Adapted from the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/tree/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Analysis/Semigroup),
  which gives the real Hilbert space argument.
-/

public section

noncomputable section

open InnerProductSpace
open scoped LinearPMap

namespace LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The composition `T†T` on its maximal domain. -/
def adjointComp (T : E →ₗ.[𝕜] F) : E →ₗ.[𝕜] E :=
  let D := (Submodule.comap T.toFun T†.domain).map T.domain.subtype
  T†.comp (T.domRestrict D) fun x ↦ by
    obtain ⟨⟨y, hy⟩, hy', hxy⟩ := x.property.1
    have h : T.domRestrict D x = T ⟨y, hy⟩ := domRestrict_apply hxy.symm
    rw [h]
    exact hy'

/-- The domain of `adjointComp T` is precisely the maximal composition domain. -/
theorem mem_adjointComp_domain {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ T.adjointComp.domain ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T†.domain := by
  rw [adjointComp, comp_domain, domRestrict_domain]
  constructor
  · rintro ⟨⟨⟨y, hy⟩, h, rfl⟩, _⟩
    exact ⟨hy, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨⟨x, hx⟩, h, rfl⟩, hx⟩

/-- Every vector in the domain of `T†T` belongs to the domain of `T`. -/
theorem adjointComp_domain_le (T : E →ₗ.[𝕜] F) : T.adjointComp.domain ≤ T.domain :=
  fun _ hx ↦ (mem_adjointComp_domain.mp hx).choose

/-- Evaluating `adjointComp T` at `x` applies `T†` to `T x`. -/
@[simp]
theorem adjointComp_apply (T : E →ₗ.[𝕜] F) (x : (adjointComp T).domain) :
    adjointComp T x = T† ⟨T ⟨x, adjointComp_domain_le T x.property⟩,
      (mem_adjointComp_domain.mp x.property).choose_spec⟩ :=
  -- Unfolding composition and domain restriction gives the same arguments of `T` and `T†`
  -- by proof irrelevance of the membership witnesses.
  (rfl)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The form identity for `T†T` needs density of the domain of `T`, but not closedness. -/
theorem inner_adjointComp {T : E →ₗ.[𝕜] F} (hd : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) {y : E} (hy : y ∈ T.domain) :
    ⟪adjointComp T x, y⟫ =
      ⟪T ⟨x, adjointComp_domain_le T x.property⟩, T ⟨y, hy⟩⟫ := by
  rw [adjointComp_apply]
  exact adjoint_isFormalAdjoint hd _ ⟨y, hy⟩

/-- The quadratic form of `T†T` is nonnegative. No density assumption is required: when `T.domain`
is not dense, `T†` takes the value `0`. -/
theorem re_inner_adjointComp_nonneg (T : E →ₗ.[𝕜] F) (x : T.adjointComp.domain) :
    0 ≤ RCLike.re ⟪T.adjointComp x, (x : E)⟫ := by
  by_cases hd : Dense (T.domain : Set E)
  · rw [inner_adjointComp hd x (T.adjointComp_domain_le x.property)]
    exact inner_self_nonneg
  · rw [adjointComp_apply, adjoint_apply_of_not_dense hd, inner_zero_left, _root_.map_zero]

/-- The maximal-domain operator `T†T` is a formal adjoint of itself. -/
private theorem adjointComp_isFormalAdjoint {T : E →ₗ.[𝕜] F}
    (hd : Dense (T.domain : Set E)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  rw [inner_adjointComp hd x (adjointComp_domain_le T y.property), adjointComp_apply]
  exact (adjoint_isFormalAdjoint hd (T := T)).symm
    ⟨x, adjointComp_domain_le T x.property⟩
    ⟨T ⟨y, adjointComp_domain_le T y.property⟩, (mem_adjointComp_domain.mp y.property).choose_spec⟩

/-- The composition `T T†` on its maximal domain `{y ∈ D(T†) | T† y ∈ D(T)}`. -/
def compAdjoint (T : E →ₗ.[𝕜] F) : F →ₗ.[𝕜] F :=
  let D := (Submodule.comap T†.toFun T.domain).map T†.domain.subtype
  T.comp (T†.domRestrict D) fun y ↦ by
    obtain ⟨⟨z, hz⟩, hz', hzy⟩ := y.property.1
    have h : T†.domRestrict D y = T† ⟨z, hz⟩ := domRestrict_apply hzy.symm
    rwa [h]

/-- The domain of `compAdjoint T` is precisely `{y ∈ D(T†) | T† y ∈ D(T)}`. -/
theorem mem_compAdjoint_domain {T : E →ₗ.[𝕜] F} {y : F} :
    y ∈ T.compAdjoint.domain ↔ ∃ hy : y ∈ T†.domain, T† ⟨y, hy⟩ ∈ T.domain := by
  rw [compAdjoint, comp_domain, domRestrict_domain]
  constructor
  · rintro ⟨⟨⟨z, hz⟩, h, rfl⟩, _⟩
    exact ⟨hz, h⟩
  · rintro ⟨hy, h⟩
    exact ⟨⟨⟨y, hy⟩, h, rfl⟩, hy⟩

/-- Every vector in the domain of `T T†` belongs to the domain of `T†`. -/
theorem compAdjoint_domain_le (T : E →ₗ.[𝕜] F) : T.compAdjoint.domain ≤ T†.domain :=
  fun _ hy ↦ (mem_compAdjoint_domain.mp hy).choose

/-- When `T.domain` is not dense, `T†` vanishes on its domain, so `D(T T†) = D(T†)`. -/
theorem compAdjoint_domain_of_not_dense {T : E →ₗ.[𝕜] F} (hd : ¬Dense (T.domain : Set E)) :
    T.compAdjoint.domain = T†.domain :=
  le_antisymm (compAdjoint_domain_le T) fun _ hy ↦ mem_compAdjoint_domain.mpr
    ⟨hy, by rw [adjoint_apply_of_not_dense hd]; exact zero_mem _⟩

/-- Evaluating `compAdjoint T` at `y` applies `T` to `T† y`. -/
@[simp]
theorem compAdjoint_apply (T : E →ₗ.[𝕜] F) (y : T.compAdjoint.domain) :
    T.compAdjoint y = T ⟨T† ⟨y, compAdjoint_domain_le T y.property⟩,
      (mem_compAdjoint_domain.mp y.property).choose_spec⟩ :=
  -- Unfolding composition and domain restriction gives the same arguments of `T†` and `T`
  -- by proof irrelevance of the membership witnesses.
  (rfl)

/-- When `T.domain` is not dense, `T†` vanishes on its domain, so `T T†` also vanishes on its
domain. -/
theorem compAdjoint_apply_of_not_dense {T : E →ₗ.[𝕜] F} (hd : ¬Dense (T.domain : Set E))
    (y : T.compAdjoint.domain) : T.compAdjoint y = 0 :=
  (compAdjoint_apply T y).trans <|
    (congrArg T (Subtype.ext (adjoint_apply_of_not_dense hd _))).trans T.map_zero

/-- The form identity for `T T†` needs only density of the domain of `T`. -/
theorem inner_compAdjoint {T : E →ₗ.[𝕜] F} (hd : Dense (T.domain : Set E))
    (x : T.compAdjoint.domain) {y : F} (hy : y ∈ T†.domain) :
    ⟪T.compAdjoint x, y⟫ =
      ⟪T† ⟨x, compAdjoint_domain_le T x.property⟩, T† ⟨y, hy⟩⟫ := by
  rw [compAdjoint_apply]
  exact (adjoint_isFormalAdjoint hd).symm _ ⟨y, hy⟩

/-- The quadratic form of `T T†` is nonnegative. No density assumption is required: when `T.domain`
is not dense, `T†` takes the value `0`. -/
theorem re_inner_compAdjoint_nonneg (T : E →ₗ.[𝕜] F) (x : T.compAdjoint.domain) :
    0 ≤ RCLike.re ⟪T.compAdjoint x, (x : F)⟫ := by
  by_cases hd : Dense (T.domain : Set E)
  · rw [inner_compAdjoint hd x (T.compAdjoint_domain_le x.property)]
    exact inner_self_nonneg
  · rw [compAdjoint_apply_of_not_dense hd, inner_zero_left, _root_.map_zero]

variable [CompleteSpace F]

/-- For a closed densely defined `T`, every vector is `x + T†T x` for a point in the maximal
composition domain. -/
theorem surjective_add_adjointComp (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    Function.Surjective (fun x : (adjointComp T).domain ↦ (x : E) + adjointComp T x) := by
  intro z
  obtain ⟨u, hu⟩ := hT.exists_inner_sub_eq_inner_map z
  have hTu : T u ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨z - (u : E), hu⟩
  refine ⟨⟨u, mem_adjointComp_domain.mpr ⟨u.property, hTu⟩⟩, ?_⟩
  dsimp only
  rw [adjointComp_apply]
  -- Both subtype arguments of `T†` have value `T u`; only their membership proofs differ.
  change (u : E) + T† ⟨T u, hTu⟩ = z
  rw [adjoint_apply_eq hd _ hu]
  abel

/-- The maximal domain of `T†T` is dense for a closed densely defined operator `T`. -/
theorem dense_adjointComp_domain (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Dense ((adjointComp T).domain : Set E) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x, hx⟩ := surjective_add_adjointComp T hT hd z
  dsimp only at hx
  have hzero : ⟪(x : E), z⟫ = 0 := hz (x : E) x.property
  have hsum : RCLike.re ⟪(x : E), (x : E)⟫ +
      RCLike.re ⟪T ⟨x, adjointComp_domain_le T x.property⟩,
        T ⟨x, adjointComp_domain_le T x.property⟩⟫ = 0 := by
    have h := congrArg RCLike.re hzero
    rw [← hx, inner_add_right, _root_.map_add RCLike.re,
      inner_re_symm (x : E) (adjointComp T x),
      inner_adjointComp hd x (adjointComp_domain_le T x.property)] at h
    simpa only [_root_.map_zero] using h
  have hx0 : (x : E) = 0 := re_inner_self_nonpos.mp <| by
    have hn : 0 ≤ RCLike.re ⟪T ⟨x, adjointComp_domain_le T x.property⟩,
        T ⟨x, adjointComp_domain_le T x.property⟩⟫ := inner_self_nonneg
    linarith
  have hx' : x = 0 := Subtype.ext hx0
  rw [← hx, hx']
  simp

/-- **Von Neumann's theorem:** `T†T` on its maximal domain is self-adjoint when `T` is closed
and densely defined. -/
theorem isSelfAdjoint_adjointComp (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : IsSelfAdjoint (adjointComp T) := by
  have hdA := dense_adjointComp_domain T hT hd
  have hsym := adjointComp_isFormalAdjoint hd
  have hle : adjointComp T ≤ (adjointComp T)† := hsym.le_adjoint hdA
  have hfa := (adjoint_isFormalAdjoint hdA (T := adjointComp T)).symm
  have key : ∀ y : ((adjointComp T)†).domain,
      ∃ hm : (y : E) ∈ (adjointComp T).domain,
        adjointComp T ⟨(y : E), hm⟩ = (adjointComp T)† y := by
    intro y
    obtain ⟨u, hueq⟩ :=
      surjective_add_adjointComp T hT hd ((y : E) + (adjointComp T)† y)
    dsimp only at hueq
    have hperp : ∀ z : E, ⟪z, (y : E) - (u : E)⟫ = 0 := by
      intro z
      obtain ⟨x, hxeq⟩ := surjective_add_adjointComp T hT hd z
      dsimp only at hxeq
      have ea : ⟪(x : E) + adjointComp T x, (y : E)⟫ =
          ⟪(x : E), (y : E) + (adjointComp T)† y⟫ := by
        rw [inner_add_left, inner_add_right, hfa x y]
      have eb : ⟪(x : E) + adjointComp T x, (u : E)⟫ =
          ⟪(x : E), (y : E) + (adjointComp T)† y⟫ := by
        rw [inner_add_left, hsym x u, ← inner_add_right, hueq]
      rw [← hxeq, inner_sub_right, ea, eb, sub_self]
    have hyu : (y : E) = (u : E) :=
      sub_eq_zero.mp (inner_self_eq_zero.mp (hperp ((y : E) - (u : E))))
    refine ⟨hyu ▸ u.property, ?_⟩
    have hAu : adjointComp T ⟨(y : E), hyu ▸ u.property⟩ = adjointComp T u := by
      congr 1
      exact Subtype.ext hyu
    rw [hAu]
    have h := hueq
    rw [hyu] at h
    exact add_left_cancel h
  have hge : (adjointComp T)† ≤ adjointComp T := by
    refine ⟨fun y hy ↦ (key ⟨y, hy⟩).choose, ?_⟩
    intro a b hab
    obtain ⟨hm, hval⟩ := key a
    have hb : b = ⟨(a : E), hm⟩ := Subtype.ext hab.symm
    rw [hb, hval]
  rw [isSelfAdjoint_def]
  exact eq_of_le_of_domain_eq hge (le_antisymm hge.1 hle.1)

/-- **Von Neumann's core theorem:** for a closed operator `T`, the domain of `T†T` is a graph core
for `T`. No density assumption on `T.domain` is required. -/
theorem IsClosed.hasCore_adjointComp_domain {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    T.HasCore T.adjointComp.domain := by
  rw [hT.hasCore_iff_graph_subset_closure (adjointComp_domain_le T)]
  let L := WithLp.prodContinuousLinearEquiv 2 𝕜 E F
  let K : Submodule 𝕜 (WithLp 2 (E × F)) := T.graph.comap L.toLinearMap
  have hK : _root_.IsClosed (K : Set (WithLp 2 (E × F))) := hT.preimage L.continuous
  let : CompleteSpace K := hK.completeSpace_coe
  let G : Submodule 𝕜 K :=
    ((T.domRestrict T.adjointComp.domain).graph.comap L.toLinearMap).comap K.subtype
  have hdG : Dense (G : Set K) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    obtain ⟨x₀, hx₀1, hx₀2⟩ := T.mem_graph_iff.mp (Submodule.mem_comap.mp w.property)
    obtain ⟨u, hu⟩ := hT.exists_inner_sub_eq_inner_map (x₀ : E)
    have hu_mem : (u : E) ∈ T.adjointComp.domain :=
      mem_adjointComp_domain.mpr
        ⟨u.property, mem_adjoint_domain_of_exists _ ⟨(x₀ : E) - (u : E), hu⟩⟩
    have huK : WithLp.toLp 2 ((u : E), T u) ∈ K := by
      rw [Submodule.mem_comap]
      simpa only [L, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
        WithLp.prodContinuousLinearEquiv_apply, WithLp.ofLp_toLp] using T.mem_graph u
    have huG : (⟨WithLp.toLp 2 ((u : E), T u), huK⟩ : K) ∈ G := by
      rw [Submodule.mem_comap, Submodule.mem_comap]
      exact (T.domRestrict T.adjointComp.domain).mem_graph_iff.mpr
        ⟨⟨u, hu_mem, u.property⟩, rfl, domRestrict_apply rfl⟩
    have h0 : ⟪(u : E), (x₀ : E)⟫ + ⟪T u, T x₀⟫ = 0 := by
      have h := (Submodule.mem_orthogonal G w).mp hw ⟨_, huK⟩ huG
      rw [Submodule.coe_inner, WithLp.prod_inner_apply] at h
      have hw1 : (WithLp.ofLp (w : WithLp 2 (E × F))).1 = (x₀ : E) := hx₀1.symm
      have hw2 : (WithLp.ofLp (w : WithLp 2 (E × F))).2 = T x₀ := hx₀2.symm
      simpa only [WithLp.ofLp_toLp, hw1, hw2] using h
    have hx₀_inner : ⟪(x₀ : E), (x₀ : E)⟫ = 0 := calc
      ⟪(x₀ : E), (x₀ : E)⟫ =
          ⟪(u : E), (x₀ : E)⟫ + (⟪(x₀ : E), (x₀ : E)⟫ - ⟪(u : E), (x₀ : E)⟫) := by abel
      _ = 0 := by rwa [← inner_sub_left, hu x₀]
    have hx₀0 : x₀ = 0 := Subtype.ext (inner_self_eq_zero.mp hx₀_inner)
    refine Subtype.ext (L.injective ?_)
    rw [ZeroMemClass.coe_zero, _root_.map_zero]
    exact Prod.ext (hx₀1.symm.trans (by simp [hx₀0])) (hx₀2.symm.trans (by simp [hx₀0]))
  intro p hp
  have hpK : L.symm p ∈ K := by
    rw [Submodule.mem_comap]
    simpa [L] using hp
  have hmem := (L.continuous.comp continuous_subtypeVal).range_subset_closure_image_dense hdG
    ⟨⟨L.symm p, hpK⟩, L.apply_symm_apply p⟩
  exact closure_mono (by rintro _ ⟨q, hq, rfl⟩; exact hq) hmem

/-- When `T.domain` is not dense, `T†` vanishes on its domain, so `D((T†)† T†) = D(T†)`. -/
theorem adjointComp_adjoint_domain_of_not_dense {T : E →ₗ.[𝕜] F}
    (hd : ¬Dense (T.domain : Set E)) : (T†).adjointComp.domain = T†.domain :=
  le_antisymm (adjointComp_domain_le (T†)) fun _ hy ↦ mem_adjointComp_domain.mpr
    ⟨hy, by rw [adjoint_apply_of_not_dense hd]; exact zero_mem _⟩

/-- When `T.domain` is not dense, `T†` vanishes on its domain, so `(T†)† T†` also vanishes on its
domain. -/
theorem adjointComp_adjoint_apply_of_not_dense {T : E →ₗ.[𝕜] F}
    (hd : ¬Dense (T.domain : Set E)) (y : (T†).adjointComp.domain) :
    (T†).adjointComp y = 0 :=
  (adjointComp_apply (T†) y).trans <|
    (congrArg (T††) (Subtype.ext (adjoint_apply_of_not_dense hd _))).trans (T††).map_zero

/-- For a closed operator `T`, `T.compAdjoint` coincides with `(T†).adjointComp`. No density
assumption on `T.domain` is needed: when `T.domain` is not dense, `T†` is `0` on its domain, so
both operators are `0` on `T†.domain`. -/
theorem IsClosed.compAdjoint_eq_adjoint_adjointComp {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    T.compAdjoint = (T†).adjointComp := by
  by_cases hd : Dense (T.domain : Set E)
  · have hdd := adjoint_adjoint hT hd
    have hdom : T.compAdjoint.domain = (T†).adjointComp.domain := by
      ext y
      simp only [mem_compAdjoint_domain, mem_adjointComp_domain, hdd]
    refine LinearPMap.ext hdom fun y hy₁ hy₂ ↦ ?_
    rw [compAdjoint_apply, adjointComp_apply]
    exact (LinearPMap.congr_fun hdd _ _).symm
  · refine LinearPMap.ext
        ((compAdjoint_domain_of_not_dense hd).trans
          (adjointComp_adjoint_domain_of_not_dense hd).symm)
        fun y hy₁ hy₂ ↦ ?_
    rw [compAdjoint_apply_of_not_dense hd ⟨y, hy₁⟩,
      adjointComp_adjoint_apply_of_not_dense hd ⟨y, hy₂⟩]

/-- For a closed operator `T`, the domain of `T T†` is dense in the target space. -/
theorem IsClosed.dense_compAdjoint_domain {T : E →ₗ.[𝕜] F} (hT : T.IsClosed) :
    Dense (T.compAdjoint.domain : Set F) := by
  by_cases hd : Dense (T.domain : Set E)
  · rw [hT.compAdjoint_eq_adjoint_adjointComp]
    exact dense_adjointComp_domain (T†) (adjoint_isClosed hd) (dense_adjoint_domain hT.isClosable)
  · rw [compAdjoint_domain_of_not_dense hd]
    exact dense_adjoint_domain hT.isClosable

/-- For a closed densely defined `T`, every vector of `F` is `y + T T† y` for a vector in the
domain of `T T†`. -/
theorem surjective_add_compAdjoint (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    Function.Surjective (fun y : T.compAdjoint.domain ↦ (y : F) + T.compAdjoint y) := by
  rw [hT.compAdjoint_eq_adjoint_adjointComp]
  exact surjective_add_adjointComp (T†) (adjoint_isClosed hd) (dense_adjoint_domain hT.isClosable)

/-- **Von Neumann's theorem (target Gram operator):** `T T†` on its maximal domain is
self-adjoint when `T` is closed and densely defined. -/
theorem isSelfAdjoint_compAdjoint (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : IsSelfAdjoint T.compAdjoint := by
  rw [hT.compAdjoint_eq_adjoint_adjointComp]
  exact isSelfAdjoint_adjointComp (T†) (adjoint_isClosed hd) (dense_adjoint_domain hT.isClosable)

/-- For a closed densely defined operator `T`, the domain of `T T†` is a graph core for `T†`. -/
theorem IsClosed.adjoint_hasCore_compAdjoint_domain {T : E →ₗ.[𝕜] F} (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : (T†).HasCore T.compAdjoint.domain := by
  rw [hT.compAdjoint_eq_adjoint_adjointComp]
  exact (adjoint_isClosed hd).hasCore_adjointComp_domain

end LinearPMap

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Viewing a bounded operator `B` as a partial linear map on `⊤`, its unbounded source Gram
operator `adjointComp` coincides with `B† ∘L B` on `⊤`. -/
@[simp]
theorem toPMap_top_adjointComp (B : E →L[𝕜] F) :
    ((B : E →ₗ[𝕜] F).toPMap ⊤).adjointComp =
      ((B.adjoint ∘L B : E →L[𝕜] E) : E →ₗ[𝕜] E).toPMap ⊤ := by
  have hd : Dense (((⊤ : Submodule 𝕜 E) : Set E)) := by rw [Submodule.top_coe]; exact dense_univ
  have hadj := B.toPMap_adjoint_eq_adjoint_toPMap_of_dense hd
  have hdom : ((B : E →ₗ[𝕜] F).toPMap ⊤).adjointComp.domain = ⊤ := by
    ext x
    simp [LinearPMap.mem_adjointComp_domain, hadj]
  refine LinearPMap.ext hdom fun x hx _ ↦ ?_
  rw [LinearPMap.adjointComp_apply]
  exact LinearPMap.congr_fun hadj _ Submodule.mem_top

end ContinuousLinearMap

