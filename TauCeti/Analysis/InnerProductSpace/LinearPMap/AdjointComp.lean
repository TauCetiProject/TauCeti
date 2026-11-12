/-
Copyright (c) 2026 Lyu Yuwei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lyu Yuwei
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap

import TauCeti.Analysis.InnerProductSpace.LinearPMap.GraphProjection

/-!
# The operator `T†T` for a closed densely defined operator

For a partially defined operator `T`, the domain of `LinearPMap.adjointComp T` consists
of the vectors `x` in the domain of `T` for which `T x` belongs to the domain of `T†`.
If `T` is closed and densely defined between real or complex Hilbert spaces, then
`T†T` is densely defined, nonnegative and self-adjoint.

Projecting `(z, 0)` onto the closed graph of `T` gives a solution of
`x + T†T x = z`. This surjectivity and the form identity give density of the
composition domain, then equality with the adjoint.

## References

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
    obtain ⟨⟨y, hy⟩, hy', hxy⟩ := x.2.1
    have h : T.domRestrict D x = T ⟨y, hy⟩ := domRestrict_apply hxy.symm
    rw [h]
    exact hy'

/-- The domain of `adjointComp T` is precisely the maximal composition domain. -/
theorem mem_adjointComp_domain {T : E →ₗ.[𝕜] F} {x : E} :
    x ∈ T.adjointComp.domain ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T†.domain := by
  -- Composition preserves the restricted domain; `domRestrict` intersects it with `T.domain`.
  change x ∈ (Submodule.comap T.toFun T†.domain).map T.domain.subtype ⊓ T.domain ↔ _
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
    adjointComp T x = T† ⟨T ⟨x, adjointComp_domain_le T x.2⟩,
      (mem_adjointComp_domain.mp x.2).choose_spec⟩ :=
  -- Unfolding composition and domain restriction gives the same arguments of `T` and `T†`
  -- by proof irrelevance of the membership witnesses.
  (rfl)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The form identity for `T†T` needs density of the domain of `T`, but not closedness. -/
theorem inner_adjointComp {T : E →ₗ.[𝕜] F} (hd : Dense (T.domain : Set E))
    (x : (adjointComp T).domain) {y : E} (hy : y ∈ T.domain) :
    ⟪adjointComp T x, y⟫ =
      ⟪T ⟨x, adjointComp_domain_le T x.2⟩, T ⟨y, hy⟩⟫ := by
  rw [adjointComp_apply]
  exact adjoint_isFormalAdjoint hd _ ⟨y, hy⟩

/-- The quadratic form of `T†T` is nonnegative when `T` is densely defined. -/
theorem re_inner_adjointComp_nonneg {T : E →ₗ.[𝕜] F} (hd : Dense (T.domain : Set E))
    (x : T.adjointComp.domain) : 0 ≤ RCLike.re ⟪T.adjointComp x, (x : E)⟫ := by
  rw [inner_adjointComp hd x (T.adjointComp_domain_le x.2)]
  exact inner_self_nonneg

/-- The maximal-domain operator `T†T` is a formal adjoint of itself. -/
private theorem adjointComp_isFormalAdjoint {T : E →ₗ.[𝕜] F}
    (hd : Dense (T.domain : Set E)) :
    (adjointComp T).IsFormalAdjoint (adjointComp T) := by
  intro x y
  rw [inner_adjointComp hd x (adjointComp_domain_le T y.2), adjointComp_apply]
  exact (adjoint_isFormalAdjoint hd (T := T)).symm
    ⟨x, adjointComp_domain_le T x.2⟩
    ⟨T ⟨y, adjointComp_domain_le T y.2⟩, (mem_adjointComp_domain.mp y.2).choose_spec⟩

variable [CompleteSpace F]

/-- For a closed densely defined `T`, every vector is `x + T†T x` for a point in the maximal
composition domain. -/
theorem surjective_add_adjointComp (T : E →ₗ.[𝕜] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) :
    Function.Surjective (fun x : (adjointComp T).domain ↦ (x : E) + adjointComp T x) := by
  intro z
  obtain ⟨u, hu⟩ := hT.exists_inner_sub_eq_inner_map z
  have hTu : T u ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨z - (u : E), hu⟩
  refine ⟨⟨u, mem_adjointComp_domain.mpr ⟨u.2, hTu⟩⟩, ?_⟩
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
  have hzero : ⟪(x : E), z⟫ = 0 := hz (x : E) x.2
  have hsum : RCLike.re ⟪(x : E), (x : E)⟫ +
      RCLike.re ⟪T ⟨x, adjointComp_domain_le T x.2⟩,
        T ⟨x, adjointComp_domain_le T x.2⟩⟫ = 0 := by
    have h := congrArg RCLike.re hzero
    rw [← hx, inner_add_right, _root_.map_add RCLike.re,
      inner_re_symm (x : E) (adjointComp T x),
      inner_adjointComp hd x (adjointComp_domain_le T x.2)] at h
    simpa only [_root_.map_zero] using h
  have hx0 : (x : E) = 0 := re_inner_self_nonpos.mp <| by
    have hn : 0 ≤ RCLike.re ⟪T ⟨x, adjointComp_domain_le T x.2⟩,
        T ⟨x, adjointComp_domain_le T x.2⟩⟫ := inner_self_nonneg
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
    refine ⟨hyu ▸ u.2, ?_⟩
    have hAu : adjointComp T ⟨(y : E), hyu ▸ u.2⟩ = adjointComp T u := by
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

end LinearPMap
