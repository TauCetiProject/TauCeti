/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.CategoryTheory.Elements.Basic

/-!
# Base change of topological equivariant families

For a functor `F : C ⥤ Type*`, its category of elements is the action category of the family
with total space `F.Elements`. Precomposition along `K : D ⥤ C` pulls this family back.
The total space `(K ⋙ F).Elements` is topologized as the actual fiber product of `K.obj`
and the anchor of `F.Elements`, not as a disjoint union of fibers.

The homeomorphism `CategoryTheory.Functor.Elements.precompHomeomorph` identifies this fiber
product. Both projections are continuous, and the new anchor is continuous. If `D` has
continuous target, `K` is continuous on total arrows, and the original action is continuous,
the pulled-back action is continuous. This gives base change along chart-refinement functors
for arbitrary topological equivariant families, without smoothness or transversality hypotheses
and without discarding any arrow labels.

## References

* I. Moerdijk and J. Mrčun, *Introduction to foliations and Lie groupoids*, Section 5.3.
-/

public section

open CategoryTheory Topology

namespace CategoryTheory.Functor.Elements

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ Type*) (K : D ⥤ C)
  [TopologicalSpace D] [TopologicalSpace F.Elements]

/-- The total space of a pulled-back family has the fiber-product topology of the object map
and the original anchor. -/
instance instTopologicalSpacePrecomp : TopologicalSpace (K ⋙ F).Elements :=
  .induced (precompEquiv F K) inferInstance

/-- The total space of a pulled-back family is homeomorphic to the fiber product of the
object map and the original anchor. -/
def precompHomeomorph : (K ⋙ F).Elements ≃ₜ
    K.obj.Pullback (Functor.Elements.obj (F := F)) :=
  (precompEquiv F K).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The fiber-product coordinates of a point of the pulled-back family. -/
@[simp]
theorem precompHomeomorph_apply (z : (K ⋙ F).Elements) :
    precompHomeomorph F K z = ⟨(z.obj, (precomp K F).obj z), rfl⟩ :=
  precompEquiv_apply F K z

/-- The new anchor is the first fiber-product coordinate. -/
@[simp]
theorem precompHomeomorph_symm_apply_obj
    (q : K.obj.Pullback (Functor.Elements.obj (F := F))) :
    ((precompHomeomorph F K).symm q).obj = q.1.1 :=
  precompEquiv_symm_apply_obj F K q

/-- Forgetting the new base coordinate recovers the original point. -/
@[simp]
theorem precomp_obj_precompHomeomorph_symm
    (q : K.obj.Pullback (Functor.Elements.obj (F := F))) :
    (precomp K F).obj ((precompHomeomorph F K).symm q) = q.1.2 :=
  precomp_obj_precompEquiv_symm F K q

/-- The new anchor and the map to the original total space jointly embed the pulled-back
family in the product. -/
theorem isEmbedding_precomp :
    IsEmbedding fun z : (K ⋙ F).Elements ↦ (z.obj, (precomp K F).obj z) := by
  simpa only [Function.comp_def, precompHomeomorph_apply] using
    IsEmbedding.subtypeVal.comp (precompHomeomorph F K).isEmbedding

/-- Continuity into a pulled-back family is equivalent to continuity of its two projections. -/
theorem continuous_precomp_iff {X : Type*} [TopologicalSpace X]
    {f : X → (K ⋙ F).Elements} :
    Continuous f ↔ Continuous (fun x ↦ (f x).obj) ∧
      Continuous (fun x ↦ (precomp K F).obj (f x)) := by
  exact (isEmbedding_precomp F K).isInducing.continuous_iff.trans continuous_prodMk

/-- The anchor of a pulled-back family is continuous. -/
@[fun_prop]
theorem continuous_precomp_anchor :
    Continuous (Functor.Elements.obj : (K ⋙ F).Elements → D) :=
  continuous_fst.comp (isEmbedding_precomp F K).continuous

/-- The projection of a pulled-back family to the original total space is continuous. -/
@[fun_prop]
theorem continuous_precomp_obj : Continuous (precomp K F).obj :=
  continuous_snd.comp (isEmbedding_precomp F K).continuous

variable [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]

/-- Precomposition is continuous on total arrows when the underlying functor is continuous
on total arrows. -/
theorem continuous_total_precomp
    (hK : Continuous fun a : Quiver.Total D ↦
      (⟨K.obj a.left, K.obj a.right, K.map a.hom⟩ : Quiver.Total C)) :
    Continuous fun a : Quiver.Total (K ⋙ F).Elements ↦
      (⟨(precomp K F).obj a.left, (precomp K F).obj a.right,
        (precomp K F).map a.hom⟩ : Quiver.Total F.Elements) := by
  exact isEmbedding_total.continuous_iff.mpr
    ((hK.comp continuous_total_π).prodMk
      ((continuous_precomp_obj F K).comp continuous_source))

/-- The action of the pulled-back family is continuous when the original action, the
functor on total arrows, and the target in `D` are continuous. No separation or smoothness
assumption is needed. -/
theorem continuous_act_precomp
    (hK : Continuous fun a : Quiver.Total D ↦
      (⟨K.obj a.left, K.obj a.right, K.map a.hom⟩ : Quiver.Total C))
    (ht : Continuous (act F))
    (htD : Continuous (Quiver.Total.right : Quiver.Total D → D)) :
    Continuous (act (K ⋙ F)) := by
  apply continuous_target_iff.mp
  apply (continuous_precomp_iff F K).mpr
  exact ⟨htD.comp continuous_total_π,
    (continuous_target_iff.mpr ht).comp (continuous_total_precomp F K hK)⟩

end CategoryTheory.Functor.Elements
