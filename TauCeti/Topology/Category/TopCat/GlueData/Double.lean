/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.GlueData

/-!
# Doubling a space along an open subset

Gluing two copies of a topological space `X` along an open subset `U` by the identity gives the
gluing data `TauCeti.doubleGlueData X U`. Two points of the glued space coming from the charts
are equal exactly when they are images of the same point of `X`, lying in `U` if the charts
differ (`TauCeti.doubleGlueData_ι_eq_iff`).

Each chart of the double is an open copy of `X`, but the double is Hausdorff only when `X` is
Hausdorff and `U` is closed (`TauCeti.t2Space_doubleGlueData_iff`). The failure happens at the
points `x` in the closure of `U` but not in `U`: such a point has two distinct images in the
double that have no disjoint neighbourhoods (`TauCeti.not_disjoint_nhds_doubleGlueData_ι`), and
the pair `(x, x)` lies in the closure of the relation between the two charts without belonging
to it (`TauCeti.mk_mem_closure_diff_doubleGlueData_chartRel`), so that relation is not closed
(`TauCeti.not_isClosed_doubleGlueData_chartRel`). This makes the double the basic test
case for the Hausdorff criterion `TopCat.GlueData.t2Space_iff_isClosed_chartRel`: the standard
example is the plane with a doubled origin, the double of `ℂ` along `ℂ \ {0}`, which is locally
homeomorphic to `ℂ` but not Hausdorff.

## Main declarations

* `TauCeti.doubleGlueData`: two copies of `X` glued along `U` by the identity.
* `TauCeti.doubleGlueData_ι_eq_iff`, `TauCeti.mem_doubleGlueData_chartRel_iff`: the gluing
  relation.
* `TauCeti.t2Space_doubleGlueData_iff`: the double is Hausdorff exactly when `X` is Hausdorff and
  `U` is closed.
* `TauCeti.not_isClosed_doubleGlueData_chartRel`: a point of `closure U` outside `U` makes the
  relation between the two charts not closed.
* `TauCeti.not_disjoint_nhds_doubleGlueData_ι`: the two images of a point of `closure U` cannot
  be separated by open sets.

## References

* Nicolas Bourbaki, *General Topology*, Chapter I, §8.3 (Hausdorff quotient spaces).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the line with two origins).
-/

public section

open CategoryTheory TopologicalSpace Set Topology Filter

universe u

namespace TauCeti

variable (X : Type u) [TopologicalSpace X] (U : Opens X)

/-- The double of `X` along an open subset `U`: two copies of `X`, indexed by `ULift Bool`, glued
along `U` by the identity. The overlap of distinct copies is `U`, and the transition maps are the
identity. -/
@[expose] noncomputable def doubleGlueData : TopCat.GlueData.{u} :=
  TopCat.GlueData.mk'
    { J := ULift.{u} Bool
      U := fun _ ↦ TopCat.of X
      V := fun i j ↦ ⟨{x | i = j ∨ x ∈ U}, by
        by_cases h : i = j
        · simp [h]
        · simpa [h] using U.isOpen⟩
      t := fun _ _ ↦ TopCat.ofHom ⟨fun x ↦ ⟨x.1, x.2.imp Eq.symm id⟩, by fun_prop⟩
      V_id := fun _ ↦ eq_top_iff.2 fun _ _ ↦ Or.inl rfl
      t_id := fun _ ↦ rfl
      t_inter := fun _ _ _ x hx ↦ x.2.elim (fun h ↦ hx.imp (h ▸ id) id) Or.inr
      cocycle := fun _ _ _ _ _ ↦ rfl }

/-- The double is indexed by `ULift Bool`, one index for each copy of `X`. -/
@[simp] theorem doubleGlueData_J : (doubleGlueData X U).J = ULift.{u} Bool := (rfl)

/-- Each piece of the double is a copy of `X`. -/
@[simp] theorem doubleGlueData_U (i : (doubleGlueData X U).J) :
    (doubleGlueData X U).U i = TopCat.of X := (rfl)

/-- The overlap of the charts `i` and `j` of the double is the subspace of points of `X` lying in
`U` if `i ≠ j`. -/
@[simp] theorem doubleGlueData_V (i j : (doubleGlueData X U).J) :
    (doubleGlueData X U).V (i, j) = TopCat.of {x : X // i = j ∨ x ∈ U} := (rfl)

/-- The overlap of the charts `i` and `j` of the double includes into the chart `i` as a subspace
of `X`. -/
@[simp] theorem doubleGlueData_f (i j : (doubleGlueData X U).J) :
    (doubleGlueData X U).f i j =
      TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // i = j ∨ x ∈ U}, X)) :=
  (rfl)

/-- The transition maps of the double are the identity on underlying points of `X`. -/
@[simp] theorem doubleGlueData_t (i j : (doubleGlueData X U).J) :
    (doubleGlueData X U).t i j =
      TopCat.ofHom (⟨fun x ↦ ⟨x.1, x.2.imp Eq.symm id⟩, by fun_prop⟩ :
        C({x : X // i = j ∨ x ∈ U}, {x : X // j = i ∨ x ∈ U})) :=
  (rfl)

variable {X U}

/-- The two copies of `X` in the double are indexed by different charts. -/
theorem doubleGlueData_false_ne_true : (⟨false⟩ : (doubleGlueData X U).J) ≠ ⟨true⟩ :=
  ULift.up_injective.ne Bool.false_ne_true

/-- Two points of the double coming from the charts `i` and `j` are equal exactly when they come
from the same point of `X`, which lies in `U` if `i ≠ j`. -/
@[simp, grind =]
theorem doubleGlueData_ι_eq_iff {i j : (doubleGlueData X U).J} {x y : X} :
    (doubleGlueData X U).toGlueData.ι i x = (doubleGlueData X U).toGlueData.ι j y ↔
      x = y ∧ (i = j ∨ x ∈ U) := by
  -- `TopCat.GlueData.ι_eq_iff_rel` is stated for points of `(doubleGlueData X U).U i`, which is
  -- `X` only after unfolding `doubleGlueData`; apply it rather than rewriting with it.
  refine ((doubleGlueData X U).ι_eq_iff_rel i j x y).trans ⟨?_, ?_⟩
  · rintro ⟨⟨z, hz⟩, hx, hy⟩
    simp only [doubleGlueData_f, doubleGlueData_t] at hx hy
    exact ⟨hx.symm.trans hy, hx ▸ hz⟩
  · rintro ⟨rfl, h⟩
    exact ⟨⟨x, h⟩, rfl, rfl⟩

/-- A point of the relation between the charts `i` and `j` of the double is a point of the
diagonal of `X`, lying in `U` if `i ≠ j`. -/
@[simp, grind =]
theorem mem_doubleGlueData_chartRel_iff {i j : (doubleGlueData X U).J} {p : X × X} :
    p ∈ (doubleGlueData X U).chartRel i j ↔ p.1 = p.2 ∧ (i = j ∨ p.1 ∈ U) :=
  ((doubleGlueData X U).mem_chartRel_iff).trans doubleGlueData_ι_eq_iff

/-- For a point `x` in the closure of `U`, the pair `(x, x)` lies in the closure of the relation
between any two charts of the double. -/
theorem mk_mem_closure_doubleGlueData_chartRel {x : X} (hx : x ∈ closure (U : Set X))
    (i j : (doubleGlueData X U).J) :
    ((x, x) : X × X) ∈ closure ((doubleGlueData X U).chartRel i j) :=
  map_mem_closure (f := fun y : X ↦ (y, y)) (continuous_id.prodMk continuous_id) hx fun _ hy ↦
    mem_doubleGlueData_chartRel_iff.2 ⟨rfl, Or.inr hy⟩

/-- For a point `x` in the closure of `U` but not in `U`, the pair `(x, x)` lies in the closure of
the relation between two different charts of the double but not in that relation. -/
theorem mk_mem_closure_diff_doubleGlueData_chartRel {x : X} (hx : x ∈ closure (U : Set X))
    (hxU : x ∉ U) {i j : (doubleGlueData X U).J} (hij : i ≠ j) :
    ((x, x) : X × X) ∈
      closure ((doubleGlueData X U).chartRel i j) \ (doubleGlueData X U).chartRel i j :=
  ⟨mk_mem_closure_doubleGlueData_chartRel hx i j, fun h ↦
    (mem_doubleGlueData_chartRel_iff.1 h).2.elim hij hxU⟩

/-- If some point of the closure of `U` is not in `U`, then the relation between two different
charts of the double is not closed. -/
theorem not_isClosed_doubleGlueData_chartRel {x : X} (hx : x ∈ closure (U : Set X)) (hxU : x ∉ U)
    {i j : (doubleGlueData X U).J} (hij : i ≠ j) :
    ¬ IsClosed ((doubleGlueData X U).chartRel i j) := fun h ↦
  (mk_mem_closure_diff_doubleGlueData_chartRel hx hxU hij).2
    (h.closure_subset (mk_mem_closure_doubleGlueData_chartRel hx i j))

/-- The double of `X` along `U` is Hausdorff exactly when `X` is Hausdorff and `U` is closed. -/
theorem t2Space_doubleGlueData_iff :
    T2Space (doubleGlueData X U).toGlueData.glued ↔ T2Space X ∧ IsClosed (U : Set X) := by
  refine (doubleGlueData X U).t2Space_iff_isClosed_chartRel.trans ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · -- The relation of a chart with itself is the diagonal.
    have hdiag : (doubleGlueData X U).chartRel ⟨false⟩ ⟨false⟩ = diagonal X :=
      Set.ext fun p ↦ mem_doubleGlueData_chartRel_iff.trans (and_iff_left (Or.inl rfl))
    exact t2_iff_isClosed_diagonal.2 (hdiag ▸ h ⟨false⟩ ⟨false⟩)
  · -- A point of `closure U` outside `U` would make the relation between the two charts
    -- not closed.
    exact isClosed_of_closure_subset fun x hx ↦ of_not_not fun hxU ↦
      not_isClosed_doubleGlueData_chartRel (i := ⟨false⟩) (j := ⟨true⟩) hx hxU
        doubleGlueData_false_ne_true (h _ _)
  · rintro ⟨hX, hU⟩ i j
    have hrel : (doubleGlueData X U).chartRel i j =
        diagonal X ∩ Prod.fst ⁻¹' {x | i = j ∨ x ∈ U} :=
      Set.ext fun p ↦ mem_doubleGlueData_chartRel_iff
    rw [hrel]
    refine (t2_iff_isClosed_diagonal.1 hX).inter (IsClosed.preimage continuous_fst ?_)
    by_cases hij : i = j
    · simp [hij]
    · simpa [hij] using hU

/-- The images of a point `x` in the closure of `U` under any two chart inclusions of the double
have no disjoint neighbourhoods. When `i ≠ j` and `x ∉ U` these images are distinct points, by
`TauCeti.doubleGlueData_ι_eq_iff`, so the double is not Hausdorff. -/
theorem not_disjoint_nhds_doubleGlueData_ι {x : X} (hx : x ∈ closure (U : Set X))
    (i j : (doubleGlueData X U).J) :
    ¬ Disjoint (𝓝 ((doubleGlueData X U).toGlueData.ι i x))
      (𝓝 ((doubleGlueData X U).toGlueData.ι j x)) := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  intro h
  -- On `U` the two chart inclusions agree, so they push `𝓝[U] x` forward to the same filter.
  have heq : map ((doubleGlueData X U).toGlueData.ι i) (𝓝[(U : Set X)] x : Filter X) =
      map ((doubleGlueData X U).toGlueData.ι j) (𝓝[(U : Set X)] x : Filter X) :=
    map_congr (eventually_nhdsWithin_of_forall fun y hy ↦
      doubleGlueData_ι_eq_iff.2 ⟨rfl, Or.inr hy⟩)
  -- Each chart inclusion is an open embedding, so it maps `𝓝[U] x ≤ 𝓝 x` below the
  -- neighbourhoods of the image of `x`.
  have h' : Disjoint (map ((doubleGlueData X U).toGlueData.ι i) (𝓝[(U : Set X)] x : Filter X))
      (map ((doubleGlueData X U).toGlueData.ι j) (𝓝[(U : Set X)] x : Filter X)) :=
    h.mono ((map_mono nhdsWithin_le_nhds).trans ((doubleGlueData X U).ι_isOpenEmbedding i
        |>.map_nhds_eq x).le)
      ((map_mono nhdsWithin_le_nhds).trans ((doubleGlueData X U).ι_isOpenEmbedding j
        |>.map_nhds_eq x).le)
  exact (map_neBot (hf := this)).ne (disjoint_self.1 (h'.mono_right heq.le))

end TauCeti
