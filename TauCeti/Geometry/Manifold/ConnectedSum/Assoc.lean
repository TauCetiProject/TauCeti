/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Map

import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Associativity of the connected sum

The connected sum `TauCeti.ConnectedSum e₁ e₂` of `M` and `N` removes the centres of the balls
`e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. To form an
iterated connected sum `(M # N) # P`, the middle summand `N` needs two balls, one for each of its
neighbours. This file shows that the result does not depend on the bracketing.

* **Balls in a summand.** A ball `f : E → M` of a summand whose image avoids the centre of the
  ball `e₁` of the connected sum stays a ball of the connected sum, through the punctured summand:
  `TauCeti.ConnectedSum.inlBall` and `TauCeti.ConnectedSum.inrBall`, from
  `TauCeti.Geometry.Manifold.ConnectedSum.Basic`. They are open embeddings, and `C^n` local
  diffeomorphisms for the charts of the connected sum when `f` is one
  (`TauCeti.ConnectedSum.isLocalDiffeomorph_inlBall`, in
  `TauCeti.Geometry.Manifold.ConnectedSum.Smooth`).
* **Associativity.** Let `a : E → M`, `b, b' : E → N` and `c : E → P` be balls, where `b` is used
  to glue `N` to `M` and `b'` to glue `N` to `P`, and assume that neither of `b` and `b'` meets the
  centre of the other. Then `(M # N) # P`, formed along `a`, `b` and then along `b'` (as a ball of
  `M # N`) and `c`, is homeomorphic to `M # (N # P)`, formed along `b'`, `c` and then along `a` and
  `b` (as a ball of `N # P`) (`TauCeti.ConnectedSum.assocHomeomorph`). The homeomorphism is the
  identity on the three summands with their centres removed: `M ∖ {a 0}`, `N ∖ {b 0, b' 0}` and
  `P ∖ {c 0}`. For balls which are `C^n` local diffeomorphisms it is a `C^n` diffeomorphism for the
  charts of the connected sums (`TauCeti.ConnectedSum.assocDiffeomorph`).

The proof identifies the punctured summand `(M # N) ∖ {b' 0}` of the outer connected sum with the
connected sum of `M` and `N ∖ {b' 0}`, along `a` and the ball `b` read in `N ∖ {b' 0}`, through
the map of connected sums induced by the inclusion `N ∖ {b' 0} → N`
(`TauCeti.ConnectedSum.map`). The hypothesis on the centres makes `b' 0` a point of the second
summand only, and `b 0` a point of the first summand of `N # P` only. Together with the
commutativity of the connected sum (`TauCeti.ConnectedSum.commHomeomorph`) and the connected sum
with a sphere (`TauCeti.connectedSumSphereDiffeomorph`), this gives the laws of a commutative monoid
with unit the sphere, for connected sums along explicit balls.

## Main definitions

* `TauCeti.ConnectedSum.assocHomeomorph`: the homeomorphism `(M # N) # P ≃ M # (N # P)`.
* `TauCeti.ConnectedSum.assocDiffeomorph`: the same map, as a `C^n` diffeomorphism.

## Main results

* `TauCeti.ConnectedSum.assocHomeomorph_inl_inl`, `TauCeti.ConnectedSum.assocHomeomorph_inl_inr`,
  `TauCeti.ConnectedSum.assocHomeomorph_inr`: the associativity homeomorphism is the identity on
  each of the three punctured summands.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
-/

public section

noncomputable section

open Set Function Topology TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {N : Type*} [TopologicalSpace N] [T1Space N]
  {P : Type*} [TopologicalSpace P] [T1Space P]

/-! ### Associativity -/

section Assoc

variable [InnerProductSpace ℝ E] {a : E → M} {b b' : E → N} {c : E → P}
  (hbb' : b' 0 ∉ range b) (hb'b : b 0 ∉ range b')

/-! The outer ball of `M # N` is `inrBall a b b' hb'b`, the ball `b'` read in the second summand,
and the outer ball of `N # P` is `inlBall b' c b hbb'`, the ball `b` read in the first summand. The
punctured summand of `M # N` along its outer ball is the connected sum of `M` and `N ∖ {b' 0}`,
and that of `N # P` is the connected sum of `N ∖ {b 0}` and `P`. -/

/-- The connected sum of `M` and `N ∖ {b' 0}`, included in that of `M` and `N`. -/
private def leftIncl : ConnectedSum a (punctureBall b' b hbb') → ConnectedSum a b :=
  map id Subtype.val injective_id Subtype.val_injective (id_comp a)
    (subtypeVal_comp_punctureBall hbb')

/-- The connected sum of `N ∖ {b 0}` and `P`, included in that of `N` and `P`. -/
private def rightIncl : ConnectedSum (punctureBall b b' hb'b) c → ConnectedSum b' c :=
  map Subtype.val id Subtype.val_injective injective_id (subtypeVal_comp_punctureBall hb'b)
    (id_comp c)

private theorem leftIncl_inl (x : puncture a) :
    leftIncl hbb' (inl a (punctureBall b' b hbb') x) = inl a b x := by
  simp [leftIncl]

private theorem leftIncl_inr (y : puncture (punctureBall b' b hbb')) :
    leftIncl hbb' (a := a) (inr a _ y) = inr a b ⟨y.1.1, mem_puncture.2 fun h ↦
      mem_puncture.1 y.2 (Subtype.ext (by simpa using h))⟩ := by
  simp only [leftIncl, map_inr]
  exact congrArg _ (Subtype.ext (coe_punctureMap _ _ _))

private theorem rightIncl_inl (x : puncture (punctureBall b b' hb'b)) :
    rightIncl hb'b (c := c) (inl _ c x) = inl b' c ⟨x.1.1, mem_puncture.2 fun h ↦
      mem_puncture.1 x.2 (Subtype.ext (by simpa using h))⟩ := by
  simp only [rightIncl, map_inl]
  exact congrArg _ (Subtype.ext (coe_punctureMap _ _ _))

private theorem rightIncl_inr (y : puncture c) :
    rightIncl hb'b (inr (punctureBall b b' hb'b) c y) = inr b' c y := by
  simp [rightIncl]

/-- A point of `N ∖ {b 0, b' 0}`, read in the punctured second summand of `M # (N ∖ {b' 0})`,
as a point of the punctured first summand of `(N ∖ {b 0}) # P`. -/
private def leftToRight (y : puncture (punctureBall b' b hbb')) :
    puncture (punctureBall b b' hb'b) :=
  ⟨⟨y.1.1, mem_puncture.2 fun h ↦ mem_puncture.1 y.2 (Subtype.ext (by rwa [coe_punctureBall]))⟩,
    mem_puncture.2 fun h ↦ mem_puncture.1 y.1.2 (by simpa using congrArg Subtype.val h)⟩

/-- A point of `N ∖ {b 0, b' 0}`, read in the punctured first summand of `(N ∖ {b 0}) # P`, as a
point of the punctured second summand of `M # (N ∖ {b' 0})`. -/
private def rightToLeft (x : puncture (punctureBall b b' hb'b)) :
    puncture (punctureBall b' b hbb') :=
  ⟨⟨x.1.1, mem_puncture.2 fun h ↦ mem_puncture.1 x.2 (Subtype.ext (by rwa [coe_punctureBall]))⟩,
    mem_puncture.2 fun h ↦ mem_puncture.1 x.1.2 (by simpa using congrArg Subtype.val h)⟩

variable (ha : IsOpenEmbedding a) (hb : IsOpenEmbedding b) (hb' : IsOpenEmbedding b')
  (hc : IsOpenEmbedding c)

include ha hb hbb' in
private theorem range_leftIncl :
    range (leftIncl hbb' (a := a)) =
      haveI := t1Space ha hb
      (puncture (inrBall a b b' hb'b) : Set (ConnectedSum a b)) := by
  have := t1Space ha hb
  rw [leftIncl, range_map, coe_puncture]
  ext p
  simp only [range_id, mem_univ, ofPred_true, image_univ, Subtype.range_coe_subtype, mem_union,
    mem_image, mem_ofPred_eq, mem_compl_singleton_iff]
  constructor
  · rintro (⟨x, rfl⟩ | ⟨y, hy, rfl⟩) h
    · rw [inrBall_apply, inl_eq_inr_iff ha.injective hb.injective] at h
      obtain ⟨v, -, -, hv⟩ := h
      exact hbb' ⟨_, by simpa using hv⟩
    · rw [inrBall_apply] at h
      have h' := congrArg Subtype.val (inr_injective ha.injective hb.injective h)
      exact (mem_puncture.1 hy) (by simpa using h')
  · intro hp
    obtain ⟨x | y, rfl⟩ := mk_surjective a b p
    · exact Or.inl ⟨x, (mk_inl a b x).symm⟩
    · refine Or.inr ⟨y, mem_puncture.2 fun hy ↦ hp ?_, (mk_inr a b y).symm⟩
      rw [mk_inr, inrBall_apply]
      exact congrArg _ (Subtype.ext (by simpa using hy))

include hb' hc hb'b in
private theorem range_rightIncl :
    range (rightIncl hb'b (c := c)) =
      haveI := t1Space hb' hc
      (puncture (inlBall b' c b hbb') : Set (ConnectedSum b' c)) := by
  have := t1Space hb' hc
  rw [rightIncl, range_map, coe_puncture]
  ext p
  simp only [range_id, mem_univ, ofPred_true, image_univ, Subtype.range_coe_subtype, mem_union,
    mem_image, mem_ofPred_eq, mem_compl_singleton_iff]
  constructor
  · rintro (⟨x, hx, rfl⟩ | ⟨y, rfl⟩) h
    · rw [inlBall_apply] at h
      have h' := congrArg Subtype.val (inl_injective hb'.injective hc.injective h)
      exact (mem_puncture.1 hx) (by simpa using h')
    · rw [inlBall_apply, eq_comm, inl_eq_inr_iff hb'.injective hc.injective] at h
      obtain ⟨v, -, hv, -⟩ := h
      exact hb'b ⟨_, by simpa using hv⟩
  · intro hp
    obtain ⟨x | y, rfl⟩ := mk_surjective b' c p
    · refine Or.inl ⟨x, mem_puncture.2 fun hx ↦ hp ?_, (mk_inl b' c x).symm⟩
      rw [mk_inl, inlBall_apply]
      exact congrArg _ (Subtype.ext (by simpa using hx))
    · exact Or.inr ⟨y, (mk_inr b' c y).symm⟩

include ha hb in
private theorem isOpenEmbedding_leftIncl : IsOpenEmbedding (leftIncl hbb' (a := a)) :=
  isOpenEmbedding_map injective_id Subtype.val_injective (id_comp a)
    (subtypeVal_comp_punctureBall hbb') .id (puncture b').isOpen.isOpenEmbedding_subtypeVal ha
    (isOpenEmbedding_punctureBall hbb' hb)

include hb' hc in
private theorem isOpenEmbedding_rightIncl : IsOpenEmbedding (rightIncl hb'b (c := c)) :=
  isOpenEmbedding_map Subtype.val_injective injective_id (subtypeVal_comp_punctureBall hb'b)
    (id_comp c) (puncture b).isOpen.isOpenEmbedding_subtypeVal .id
    (isOpenEmbedding_punctureBall hb'b hb') hc

/-- `M # (N ∖ {b' 0})` is the punctured summand of `M # N` along its outer ball. -/
private def leftHomeomorph :
    haveI := t1Space ha hb
    ConnectedSum a (punctureBall b' b hbb') ≃ₜ puncture (inrBall a b b' hb'b) :=
  haveI := t1Space ha hb
  (isOpenEmbedding_leftIncl hbb' ha hb).toIsEmbedding.toHomeomorph.trans
    (.setCongr (range_leftIncl hbb' hb'b ha hb))

/-- `(N ∖ {b 0}) # P` is the punctured summand of `N # P` along its outer ball. -/
private def rightHomeomorph :
    haveI := t1Space hb' hc
    ConnectedSum (punctureBall b b' hb'b) c ≃ₜ puncture (inlBall b' c b hbb') :=
  haveI := t1Space hb' hc
  (isOpenEmbedding_rightIncl hb'b hb' hc).toIsEmbedding.toHomeomorph.trans
    (.setCongr (range_rightIncl hbb' hb'b hb' hc))

private theorem coe_leftHomeomorph (z : ConnectedSum a (punctureBall b' b hbb')) :
    haveI := t1Space ha hb
    (leftHomeomorph hbb' hb'b ha hb z : ConnectedSum a b) = leftIncl hbb' z :=
  (rfl)

private theorem coe_rightHomeomorph (z : ConnectedSum (punctureBall b b' hb'b) c) :
    haveI := t1Space hb' hc
    (rightHomeomorph hbb' hb'b hb' hc z : ConnectedSum b' c) = rightIncl hb'b z :=
  (rfl)

private theorem leftHomeomorph_symm_apply (z : ConnectedSum a (punctureBall b' b hbb'))
    (x : haveI := t1Space ha hb; puncture (inrBall a b b' hb'b))
    (hx : (x : ConnectedSum a b) = leftIncl hbb' z) :
    (leftHomeomorph hbb' hb'b ha hb).symm x = z := by
  have := t1Space ha hb
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (hx.trans (coe_leftHomeomorph hbb' hb'b ha hb z).symm)

private theorem rightHomeomorph_symm_apply (z : ConnectedSum (punctureBall b b' hb'b) c)
    (x : haveI := t1Space hb' hc; puncture (inlBall b' c b hbb'))
    (hx : (x : ConnectedSum b' c) = rightIncl hb'b z) :
    (rightHomeomorph hbb' hb'b hb' hc).symm x = z := by
  have := t1Space hb' hc
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (hx.trans (coe_rightHomeomorph hbb' hb'b hb' hc z).symm)

/-- The third summand `P ∖ {c 0}`, as a subspace of the punctured summand of `N # P`. -/
private def assocInr (y : puncture c) :
    haveI := t1Space hb' hc
    puncture (inlBall b' c b hbb') :=
  haveI := t1Space hb' hc
  ⟨inr b' c y, mem_puncture.2 (inr_ne_inlBall_zero hb'.injective hc.injective hbb' hb'b y)⟩

/-- The first summand `M ∖ {a 0}`, as a subspace of the punctured summand of `M # N`. -/
private def assocInl (x : puncture a) :
    haveI := t1Space ha hb
    puncture (inrBall a b b' hb'b) :=
  haveI := t1Space ha hb
  ⟨inl a b x, mem_puncture.2 (inl_ne_inrBall_zero ha.injective hb.injective hb'b hbb' x)⟩

/-- `M # (N ∖ {b' 0})` maps to `M # (N # P)`, by the identity on `M ∖ {a 0}` and on
`N ∖ {b 0, b' 0}`. -/
private def leftMap :
    haveI := t1Space hb' hc
    ConnectedSum a (punctureBall b' b hbb') → ConnectedSum a (inlBall b' c b hbb') :=
  haveI := t1Space hb' hc
  map id (inl b' c) injective_id (inl_injective hb'.injective hc.injective) (id_comp a)
    (inl_comp_punctureBall b' c hbb')

/-- `(N ∖ {b 0}) # P` maps to `(M # N) # P`, by the identity on `N ∖ {b 0, b' 0}` and on
`P ∖ {c 0}`. -/
private def rightMap :
    haveI := t1Space ha hb
    ConnectedSum (punctureBall b b' hb'b) c → ConnectedSum (inrBall a b b' hb'b) c :=
  haveI := t1Space ha hb
  map (inr a b) id (inr_injective ha.injective hb.injective) injective_id
    (inr_comp_punctureBall a b hb'b) (id_comp c)

private theorem leftMap_inl (x : puncture a) :
    haveI := t1Space hb' hc
    leftMap hbb' hb' hc (inl a _ x) = inl a (inlBall b' c b hbb') x := by
  have := t1Space hb' hc
  simp [leftMap]

private theorem leftMap_inr (y : puncture (punctureBall b' b hbb')) :
    haveI := t1Space hb' hc
    leftMap hbb' hb' hc (inr a _ y) =
      inr a (inlBall b' c b hbb') ⟨inl b' c y, by
        rw [← coe_punctureMap (inl_injective hb'.injective hc.injective)
          (congrFun (inl_comp_punctureBall b' c hbb') 0) y]
        exact Subtype.prop _⟩ := by
  have := t1Space hb' hc
  simp only [leftMap, map_inr]
  exact congrArg _ (Subtype.ext (coe_punctureMap _ _ _))

private theorem rightMap_inl (x : puncture (punctureBall b b' hb'b)) :
    haveI := t1Space ha hb
    rightMap hb'b ha hb (inl _ c x) =
      inl (inrBall a b b' hb'b) c ⟨inr a b x, by
        rw [← coe_punctureMap (inr_injective ha.injective hb.injective)
          (congrFun (inr_comp_punctureBall a b hb'b) 0) x]
        exact Subtype.prop _⟩ := by
  have := t1Space ha hb
  simp only [rightMap, map_inl]
  exact congrArg _ (Subtype.ext (coe_punctureMap _ _ _))

private theorem rightMap_inr (y : puncture c) :
    haveI := t1Space ha hb
    rightMap hb'b ha hb (inr _ c y) = inr (inrBall a b b' hb'b) c y := by
  have := t1Space ha hb
  simp [rightMap]

/-- The point `b' v` of the punctured second summand of `M # N`, read in `M # (N ∖ {b' 0})`. -/
private theorem leftHomeomorph_symm_inrBall {v : E} (hv : v ≠ 0)
    (hx : haveI := t1Space ha hb; inrBall a b b' hb'b v ∈ puncture (inrBall a b b' hb'b)) :
    (leftHomeomorph hbb' hb'b ha hb).symm ⟨_, hx⟩ =
      inr a _ ⟨⟨b' v, mem_puncture.2 fun h ↦ hv (hb'.injective.eq_iff.1 h)⟩,
        mem_puncture.2 fun h ↦ hb'b ⟨v, by simpa using congrArg Subtype.val h⟩⟩ := by
  refine leftHomeomorph_symm_apply hbb' hb'b ha hb _ _ ?_
  rw [leftIncl_inr]
  exact (inrBall_apply a b hb'b v).trans
    (congrArg _ (Subtype.ext (coe_punctureBall _ _)))

/-- The point `b w` of the punctured first summand of `N # P`, read in `(N ∖ {b 0}) # P`. -/
private theorem rightHomeomorph_symm_inlBall {w : E} (hw : w ≠ 0)
    (hx : haveI := t1Space hb' hc; inlBall b' c b hbb' w ∈ puncture (inlBall b' c b hbb')) :
    (rightHomeomorph hbb' hb'b hb' hc).symm ⟨_, hx⟩ =
      inl _ c ⟨⟨b w, mem_puncture.2 fun h ↦ hw (hb.injective.eq_iff.1 h)⟩,
        mem_puncture.2 fun h ↦ hbb' ⟨w, by simpa using congrArg Subtype.val h⟩⟩ := by
  refine rightHomeomorph_symm_apply hbb' hb'b hb' hc _ _ ?_
  rw [rightIncl_inl]
  exact (inlBall_apply b' c hbb' w).trans
    (congrArg _ (Subtype.ext (coe_punctureBall _ _)))

/-- The map `(M # N) # P → M # (N # P)`: the identity on `M ∖ {a 0}`, `N ∖ {b 0, b' 0}` and
`P ∖ {c 0}`. -/
private def assocFun :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    ConnectedSum (inrBall a b b' hb'b) c → ConnectedSum a (inlBall b' c b hbb') :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  lift (leftMap hbb' hb' hc ∘ (leftHomeomorph hbb' hb'b ha hb).symm)
    (inr a (inlBall b' c b hbb') ∘ assocInr hbb' hb'b hb' hc) fun v hv hx hy ↦ by
      simp only [comp_apply, leftHomeomorph_symm_inrBall hbb' hb'b ha hb hb' hv hx, leftMap_inr,
        assocInr]
      exact congrArg _ (Subtype.ext (inl_eq_inr v hv _ hy))

/-- The map `M # (N # P) → (M # N) # P`: the identity on `M ∖ {a 0}`, `N ∖ {b 0, b' 0}` and
`P ∖ {c 0}`. -/
private def assocInvFun :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    ConnectedSum a (inlBall b' c b hbb') → ConnectedSum (inrBall a b b' hb'b) c :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  lift (inl (inrBall a b b' hb'b) c ∘ assocInl hbb' hb'b ha hb)
    (rightMap hb'b ha hb ∘ (rightHomeomorph hbb' hb'b hb' hc).symm) fun v hv hx hy ↦ by
      simp only [comp_apply, rightHomeomorph_symm_inlBall hbb' hb'b hb hb' hc
        (by simpa [inversion_eq_center one_ne_zero] using hv) hy, rightMap_inl, assocInl]
      exact congrArg _ (Subtype.ext (inl_eq_inr v hv hx _))

private theorem assocFun_inl (x : haveI := t1Space ha hb; puncture (inrBall a b b' hb'b)) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocFun hbb' hb'b ha hb hb' hc (inl _ c x) =
      leftMap hbb' hb' hc ((leftHomeomorph hbb' hb'b ha hb).symm x) :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  lift_inl _ _ _ x

private theorem assocFun_inr (y : puncture c) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocFun hbb' hb'b ha hb hb' hc (inr _ c y) = inr a _ (assocInr hbb' hb'b hb' hc y) :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  lift_inr _ _ _ y

private theorem assocInvFun_inl (x : puncture a) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocInvFun hbb' hb'b ha hb hb' hc (inl a _ x) = inl _ c (assocInl hbb' hb'b ha hb x) :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  lift_inl _ _ _ x

private theorem assocInvFun_inr (y : haveI := t1Space hb' hc; puncture (inlBall b' c b hbb')) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocInvFun hbb' hb'b ha hb hb' hc (inr a _ y) =
      rightMap hb'b ha hb ((rightHomeomorph hbb' hb'b hb' hc).symm y) :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  lift_inr _ _ _ y

private theorem assocInvFun_assocFun (p) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocInvFun hbb' hb'b ha hb hb' hc (assocFun hbb' hb'b ha hb hb' hc p) = p := by
  have := t1Space ha hb
  have := t1Space hb' hc
  obtain ⟨x | y, rfl⟩ := mk_surjective _ c p
  · obtain ⟨z, rfl⟩ := (leftHomeomorph hbb' hb'b ha hb).surjective x
    rw [mk_inl, assocFun_inl, Homeomorph.symm_apply_apply]
    obtain ⟨x | y, rfl⟩ := mk_surjective a _ z
    · rw [mk_inl, leftMap_inl, assocInvFun_inl]
      exact congrArg _ (Subtype.ext (leftIncl_inl hbb' x).symm)
    · rw [mk_inr, leftMap_inr, assocInvFun_inr, rightHomeomorph_symm_apply hbb' hb'b hb' hc
        (inl _ c (leftToRight hbb' hb'b y)) _ (by rw [rightIncl_inl]; rfl), rightMap_inl]
      exact congrArg _ (Subtype.ext (leftIncl_inr hbb' y).symm)
  · rw [mk_inr, assocFun_inr, assocInvFun_inr, rightHomeomorph_symm_apply hbb' hb'b hb' hc
      (inr _ c y) _ (rightIncl_inr hb'b y).symm, rightMap_inr]

private theorem assocFun_assocInvFun (q) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocFun hbb' hb'b ha hb hb' hc (assocInvFun hbb' hb'b ha hb hb' hc q) = q := by
  have := t1Space ha hb
  have := t1Space hb' hc
  obtain ⟨x | y, rfl⟩ := mk_surjective a _ q
  · rw [mk_inl, assocInvFun_inl, assocFun_inl, leftHomeomorph_symm_apply hbb' hb'b ha hb
      (inl a _ x) _ (leftIncl_inl hbb' x).symm, leftMap_inl]
  · obtain ⟨z, rfl⟩ := (rightHomeomorph hbb' hb'b hb' hc).surjective y
    rw [mk_inr, assocInvFun_inr, Homeomorph.symm_apply_apply]
    obtain ⟨x | y, rfl⟩ := mk_surjective _ c z
    · rw [mk_inl, rightMap_inl, assocFun_inl, leftHomeomorph_symm_apply hbb' hb'b ha hb
        (inr a _ (rightToLeft hbb' hb'b x)) _ (by rw [leftIncl_inr]; rfl), leftMap_inr]
      exact congrArg _ (Subtype.ext (rightIncl_inl hb'b x).symm)
    · rw [mk_inr, rightMap_inr, assocFun_inr]
      exact congrArg _ (Subtype.ext (rightIncl_inr hb'b y).symm)

private theorem continuous_assocFun :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    Continuous (assocFun hbb' hb'b ha hb hb' hc) := by
  have := t1Space ha hb
  have := t1Space hb' hc
  refine continuous_lift _ _ _ ?_
    ((continuous_inr a _).comp ((continuous_inr b' c).subtype_mk _))
  exact (continuous_map _ _ _ _ continuous_id (continuous_inl b' c)).comp
    (leftHomeomorph hbb' hb'b ha hb).symm.continuous

private theorem continuous_assocInvFun :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    Continuous (assocInvFun hbb' hb'b ha hb hb' hc) := by
  have := t1Space ha hb
  have := t1Space hb' hc
  refine continuous_lift _ _ _
    ((continuous_inl _ c).comp ((continuous_inl a b).subtype_mk _)) ?_
  exact (continuous_map _ _ _ _ (continuous_inr a b) continuous_id).comp
    (rightHomeomorph hbb' hb'b hb' hc).symm.continuous

/-- **The connected sum is associative.** Let `a : E → M`, `b, b' : E → N` and `c : E → P` be
balls which are open embeddings, such that neither of `b` and `b'` meets the centre of the other.
Then the connected sum of `M # N` (along `a` and `b`) and `P`, along the ball `b'` of `M # N` and
`c`, is homeomorphic to the connected sum of `M` and `N # P` (along `b'` and `c`), along `a` and the
ball `b` of `N # P`. The homeomorphism is the identity on `M ∖ {a 0}`, on `N ∖ {b 0, b' 0}` and on
`P ∖ {c 0}`. -/
def assocHomeomorph :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    ConnectedSum (inrBall a b b' hb'b) c ≃ₜ ConnectedSum a (inlBall b' c b hbb') :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  { toFun := assocFun hbb' hb'b ha hb hb' hc
    invFun := assocInvFun hbb' hb'b ha hb hb' hc
    left_inv := assocInvFun_assocFun hbb' hb'b ha hb hb' hc
    right_inv := assocFun_assocInvFun hbb' hb'b ha hb hb' hc
    continuous_toFun := continuous_assocFun hbb' hb'b ha hb hb' hc
    continuous_invFun := continuous_assocInvFun hbb' hb'b ha hb hb' hc }

private theorem coe_assocHomeomorph :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    ⇑(assocHomeomorph hbb' hb'b ha hb hb' hc) = assocFun hbb' hb'b ha hb hb' hc :=
  (rfl)

/-- On the first summand `M ∖ {a 0}`, the associativity homeomorphism is the identity. -/
@[simp]
theorem assocHomeomorph_inl_inl (x : puncture a)
    (hx : haveI := t1Space ha hb; inl a b x ∈ puncture (inrBall a b b' hb'b)) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocHomeomorph hbb' hb'b ha hb hb' hc (inl _ c ⟨inl a b x, hx⟩) = inl a _ x := by
  have := t1Space ha hb
  have := t1Space hb' hc
  rw [coe_assocHomeomorph, assocFun_inl, leftHomeomorph_symm_apply hbb' hb'b ha hb (inl a _ x) _
    (leftIncl_inl hbb' x).symm, leftMap_inl]

/-- On the middle summand `N ∖ {b 0, b' 0}`, the associativity homeomorphism is the identity. -/
@[simp]
theorem assocHomeomorph_inl_inr (y : puncture b)
    (hy : haveI := t1Space ha hb; inr a b y ∈ puncture (inrBall a b b' hb'b)) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocHomeomorph hbb' hb'b ha hb hb' hc (inl _ c ⟨inr a b y, hy⟩) =
      inr a _ ⟨inl b' c ⟨y, mem_puncture.2 fun h ↦ mem_puncture.1 hy
        (by rw [inrBall_apply]; exact congrArg _ (Subtype.ext (by rwa [coe_punctureBall])))⟩,
        mem_puncture.2 fun h ↦ mem_puncture.1 y.2 (by
          simpa using congrArg Subtype.val
            (inl_injective hb'.injective hc.injective (h.trans (inlBall_apply b' c hbb' 0))))⟩ := by
  have := t1Space ha hb
  have := t1Space hb' hc
  rw [coe_assocHomeomorph]
  have hy' : (y : N) ∈ puncture b' := mem_puncture.2 fun h ↦ mem_puncture.1 hy
    (by rw [inrBall_apply]; exact congrArg _ (Subtype.ext (by rwa [coe_punctureBall])))
  rw [assocFun_inl, leftHomeomorph_symm_apply hbb' hb'b ha hb
    (inr a _ ⟨⟨y, hy'⟩, mem_puncture.2 fun h ↦ mem_puncture.1 y.2 (by
      simpa using congrArg Subtype.val h)⟩) _ (by rw [leftIncl_inr]), leftMap_inr]

/-- On the third summand `P ∖ {c 0}`, the associativity homeomorphism is the identity. -/
@[simp]
theorem assocHomeomorph_inr (y : puncture c) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    assocHomeomorph hbb' hb'b ha hb hb' hc (inr _ c y) =
      inr a _ ⟨inr b' c y,
        mem_puncture.2 (inr_ne_inlBall_zero hb'.injective hc.injective hbb' hb'b y)⟩ :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  assocFun_inr hbb' hb'b ha hb hb' hc y

@[simp]
theorem assocHomeomorph_symm_inl (x : puncture a) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    (assocHomeomorph hbb' hb'b ha hb hb' hc).symm (inl a _ x) =
      inl _ c ⟨inl a b x,
        mem_puncture.2 (inl_ne_inrBall_zero ha.injective hb.injective hb'b hbb' x)⟩ := by
  have := t1Space ha hb
  have := t1Space hb' hc
  rw [Homeomorph.symm_apply_eq, assocHomeomorph_inl_inl]

@[simp]
theorem assocHomeomorph_symm_inr_inl (x : puncture b')
    (hx : haveI := t1Space hb' hc; inl b' c x ∈ puncture (inlBall b' c b hbb')) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    (assocHomeomorph hbb' hb'b ha hb hb' hc).symm (inr a _ ⟨inl b' c x, hx⟩) =
      inl _ c ⟨inr a b ⟨x, mem_puncture.2 fun h ↦ mem_puncture.1 hx
        (by rw [inlBall_apply]; exact congrArg _ (Subtype.ext (by rwa [coe_punctureBall])))⟩,
        mem_puncture.2 fun h ↦ mem_puncture.1 x.2 (by
          simpa using congrArg Subtype.val
            (inr_injective ha.injective hb.injective (h.trans (inrBall_apply a b hb'b 0))))⟩ := by
  have := t1Space ha hb
  have := t1Space hb' hc
  rw [Homeomorph.symm_apply_eq, assocHomeomorph_inl_inr]

@[simp]
theorem assocHomeomorph_symm_inr_inr (y : puncture c)
    (hy : haveI := t1Space hb' hc; inr b' c y ∈ puncture (inlBall b' c b hbb')) :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    (assocHomeomorph hbb' hb'b ha hb hb' hc).symm (inr a _ ⟨inr b' c y, hy⟩) = inr _ c y := by
  have := t1Space ha hb
  have := t1Space hb' hc
  rw [Homeomorph.symm_apply_eq, assocHomeomorph_inr]

section Smooth

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
  [ChartedSpace H M] [ChartedSpace H N] [ChartedSpace H P]
  [IsManifold I n M] [IsManifold I n N] [IsManifold I n P]
  (da : IsLocalDiffeomorph 𝓘(ℝ, E) I n a) (db : IsLocalDiffeomorph 𝓘(ℝ, E) I n b)
  (db' : IsLocalDiffeomorph 𝓘(ℝ, E) I n b') (dc : IsLocalDiffeomorph 𝓘(ℝ, E) I n c)

include da db db' dc in
/-- The associativity map is a `C^n` local diffeomorphism, for the charts of the connected sums:
on each of the three punctured summands it is the composite of inclusions of open subsets. -/
private theorem isLocalDiffeomorph_assocFun :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    letI := chartedSpace (H := H) ha hb
    letI := chartedSpace (H := H) hb' hc
    letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
    letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
    IsLocalDiffeomorph I I n (assocFun hbb' hb'b ha hb hb' hc) := by
  have := t1Space ha hb
  have := t1Space hb' hc
  let := chartedSpace (H := H) ha hb
  let := chartedSpace (H := H) hb' hc
  have := isManifold ha hb da db
  have := isManifold hb' hc db' dc
  have hlB := isOpenEmbedding_inrBall ha hb hb'b hb'
  have dlB := isLocalDiffeomorph_inrBall ha hb da db hb'b db'
  have hrB := isOpenEmbedding_inlBall hb' hc hbb' hb
  have drB := isLocalDiffeomorph_inlBall hb' hc db' dc hbb' db
  let := chartedSpace (H := H) hlB hc
  let := chartedSpace (H := H) ha hrB
  have hβ := isOpenEmbedding_punctureBall hbb' hb
  have dβ := isLocalDiffeomorph_punctureBall hbb' db
  let := chartedSpace (H := H) ha hβ
  -- `M # (N ∖ {b' 0})` maps by local diffeomorphisms to `M # N` and to `M # (N # P)`.
  have dIncl : IsLocalDiffeomorph I I n (leftIncl hbb' (a := a)) :=
    isLocalDiffeomorph_map _ _ _ _ (Diffeomorph.refl I M n).isLocalDiffeomorph
      isLocalDiffeomorph_subtype_val ha hβ ha hb da dβ
  have dMap : IsLocalDiffeomorph I I n (leftMap hbb' hb' hc (a := a)) :=
    isLocalDiffeomorph_map _ _ _ _ (Diffeomorph.refl I M n).isLocalDiffeomorph
      (isLocalDiffeomorph_inl hb' hc db' dc) ha hβ ha hrB da dβ
  -- So does its homeomorphism onto the punctured summand of `M # N`.
  have dHom : IsLocalDiffeomorph I I n (leftHomeomorph hbb' hb'b ha hb) := fun z ↦
    IsLocalDiffeomorphAt.of_comp_left (dIncl z) (isLocalDiffeomorph_subtype_val _)
      (leftHomeomorph hbb' hb'b ha hb).continuous.continuousAt
  have dInr : IsLocalDiffeomorph I I n (assocInr hbb' hb'b hb' hc) := fun y ↦
    IsLocalDiffeomorphAt.of_comp_left (isLocalDiffeomorph_inr hb' hc db' dc y)
      (isLocalDiffeomorph_subtype_val _) ((continuous_inr b' c).subtype_mk _).continuousAt
  intro p
  obtain ⟨x | y, rfl⟩ := mk_surjective _ c p
  · obtain ⟨z, rfl⟩ := (leftHomeomorph hbb' hb'b ha hb).surjective x
    rw [mk_inl]
    refine IsLocalDiffeomorphAt.of_comp_right
      (e := inl (inrBall a b b' hb'b) c ∘ leftHomeomorph hbb' hb'b ha hb) (x := z) ?_
      ((dHom z).comp (hg := isLocalDiffeomorph_inl hlB hc dlB dc _))
    have : assocFun hbb' hb'b ha hb hb' hc ∘ inl _ c ∘ leftHomeomorph hbb' hb'b ha hb =
        leftMap hbb' hb' hc := by
      ext z
      simp [assocFun_inl]
    rw [← comp_assoc, comp_assoc _ (inl _ c), this]
    exact dMap z
  · rw [mk_inr]
    refine IsLocalDiffeomorphAt.of_comp_right ?_ (isLocalDiffeomorph_inr hlB hc dlB dc y)
    have : assocFun hbb' hb'b ha hb hb' hc ∘ inr _ c = inr a _ ∘ assocInr hbb' hb'b hb' hc := by
      ext y
      exact assocFun_inr hbb' hb'b ha hb hb' hc y
    rw [this]
    exact (dInr y).comp (hg := isLocalDiffeomorph_inr ha hrB da drB _)

/-- **The connected sum of manifolds is associative.** For balls which are open embeddings and
`C^n` local diffeomorphisms, such that neither of `b` and `b'` meets the centre of the other, the
homeomorphism `TauCeti.ConnectedSum.assocHomeomorph` from `(M # N) # P` to `M # (N # P)` is a `C^n`
diffeomorphism for the charts of the connected sums (`TauCeti.ConnectedSum.chartedSpace`). -/
def assocDiffeomorph :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    letI := chartedSpace (H := H) ha hb
    letI := chartedSpace (H := H) hb' hc
    letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
    letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
    ConnectedSum (inrBall a b b' hb'b) c ≃ₘ^n⟮I, I⟯ ConnectedSum a (inlBall b' c b hbb') :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  letI := chartedSpace (H := H) ha hb
  letI := chartedSpace (H := H) hb' hc
  letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
  letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
  (isLocalDiffeomorph_assocFun hbb' hb'b ha hb hb' hc da db db' dc).diffeomorphOfBijective
    (assocHomeomorph hbb' hb'b ha hb hb' hc).bijective

@[simp]
theorem coe_assocDiffeomorph :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    letI := chartedSpace (H := H) ha hb
    letI := chartedSpace (H := H) hb' hc
    letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
    letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
    ⇑(assocDiffeomorph hbb' hb'b ha hb hb' hc da db db' dc) =
      assocHomeomorph hbb' hb'b ha hb hb' hc :=
  haveI := t1Space ha hb
  haveI := t1Space hb' hc
  letI := chartedSpace (H := H) ha hb
  letI := chartedSpace (H := H) hb' hc
  letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
  letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
  coe_diffeomorphOfBijective

@[simp]
theorem coe_assocDiffeomorph_symm :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    letI := chartedSpace (H := H) ha hb
    letI := chartedSpace (H := H) hb' hc
    letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
    letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
    ⇑(assocDiffeomorph hbb' hb'b ha hb hb' hc da db db' dc).symm =
      (assocHomeomorph hbb' hb'b ha hb hb' hc).symm := by
  have := t1Space ha hb
  have := t1Space hb' hc
  let := chartedSpace (H := H) ha hb
  let := chartedSpace (H := H) hb' hc
  let := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
  let := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
  ext q
  rw [Homeomorph.eq_symm_apply, ← coe_assocDiffeomorph hbb' hb'b ha hb hb' hc da db db' dc,
    Diffeomorph.apply_symm_apply]

/-- The diffeomorphism `TauCeti.ConnectedSum.assocDiffeomorph` is the homeomorphism
`TauCeti.ConnectedSum.assocHomeomorph`. -/
@[simp]
theorem toHomeomorph_assocDiffeomorph :
    haveI := t1Space ha hb
    haveI := t1Space hb' hc
    letI := chartedSpace (H := H) ha hb
    letI := chartedSpace (H := H) hb' hc
    letI := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
    letI := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
    (assocDiffeomorph hbb' hb'b ha hb hb' hc da db db' dc).toHomeomorph =
      assocHomeomorph hbb' hb'b ha hb hb' hc := by
  have := t1Space ha hb
  have := t1Space hb' hc
  let := chartedSpace (H := H) ha hb
  let := chartedSpace (H := H) hb' hc
  let := chartedSpace (H := H) (isOpenEmbedding_inrBall ha hb hb'b hb') hc
  let := chartedSpace (H := H) ha (isOpenEmbedding_inlBall hb' hc hbb' hb)
  ext p
  simp

end Smooth

end Assoc

end TauCeti.ConnectedSum
