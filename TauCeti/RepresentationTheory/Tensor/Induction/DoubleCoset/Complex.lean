/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Discrete
public import TauCeti.RepresentationTheory.Tensor.Induction.DoubleCoset.Differential
public import TauCeti.RepresentationTheory.Tensor.Induction.Resolution

/-!
# The Mackey decomposition of the tensor-induced resolution

The Mackey comparison for tensor induction is an isomorphism of complexes, not just of total
modules. This file constructs the complex on the tensor product of the double-coset orbit
factors and its comparison with the restricted tensor-induced total coinduced resolution.
The grading sums degrees first within each orbit and then over the double cosets. Its
differential is the corresponding iterated slot sum.

The orbit factors are restrictions along `mackeyToH` of the original coinduced resolution,
not the coinduced resolutions of the conjugated coefficient modules. This comparison feeds the
double-coset formula for the Evens norm. Its augmentation applies the original augmentation in
every factor, as recorded by `smoothTensorInducedMackeyIso_resolutionAugmentation`.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*, Trans. Amer.
  Math. Soc. **108** (1963), §6, Proposition 2.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

variable {R : Type u} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (U V : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex] [CompactSpace U]
  (r : DoubleCoset.Quotient (V : Set G) (U : Set G) → G)
  (hr : ∀ D, DoubleCoset.mk V U (r D) = D)
  (t : ∀ D, ((mackeySubgroup (r D) U V).subgroupOf V).LeftTransversal)
  (s : U.LeftTransversal) (A : SmoothDiscreteTopRep.{u, v, max v w} R U)

/-- The tensor product of the orbitwise tensor inductions of the restrictions of the original
coinduced resolution. Its factors are indexed by double cosets. -/
noncomputable abbrev smoothTensorInducedMackeyResolutionModule :=
  (toSmoothDiscrete R V).obj (DiscreteRep.piTensorProduct fun D ↦
    (ofSmoothDiscrete R V).obj
      ((toSmoothDiscrete R V).obj
        (DiscreteRep.tensorInduced _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D)) (t D)
          ((ofSmoothDiscrete R _).obj
            ((toSmoothDiscrete R _).obj
              (DiscreteRep.res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D))
                ((ofSmoothDiscrete R U).obj (smoothGradedResolutionFunctor.obj A))))))))

variable [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [Fintype (G ⧸ U)]

/-- The grading of the Mackey-decomposed resolution sums degrees within each orbit and then
over the double cosets. -/
noncomputable abbrev smoothTensorInducedMackeyResolutionPiece :
    ℤ → Submodule R (smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.V :=
  PiTensorProduct.totalDegreePiece _ (fun D ↦
    PiTensorProduct.totalDegreePiece (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)
      (fun _ ↦ A.obj.gradedResolutionPiece))

/-- The smooth Mackey comparison on total resolutions preserves and detects total degree. -/
theorem smoothTensorInducedMackeyIso_mem_resolutionPiece_iff (n : ℤ)
    (z : (smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.V) :
    (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).hom.hom.hom z ∈
      smoothTensorInducedGradedResolutionPiece U hU s A n ↔
        z ∈ smoothTensorInducedMackeyResolutionPiece U V hU r t A n := by
  let B := (ofSmoothDiscrete R U).obj (smoothGradedResolutionFunctor.obj A)
  have hB : B.ρ = A.obj.gradedResolutionRepresentation := by
    ext g x
    exact (ofSmoothDiscrete_obj_ρ_apply R U _ g x).trans
      ((smoothGradedResolutionFunctor_obj_obj_ρ_apply A g x).trans
        (A.obj.gradedResolutionTopRep_ρ_apply g x))
  have hρ (g : U) : LinearMap.IsHomogeneous (B.ρ g)
      A.obj.gradedResolutionPiece A.obj.gradedResolutionPiece 0 := by
    rw [hB]
    exact A.obj.isHomogeneous_gradedResolutionRepresentation g
  exact (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A n)
    (smoothTensorInducedMackeyIso_hom_apply U V hU r hr t s
      (smoothGradedResolutionFunctor.obj A) z)).to_iff.trans
        (Subgroup.tensorInducedMackey_mem_totalDegreePiece_iff U V r hr t B.ρ s hρ n z)

/- We obtain the equivariant differential by conjugating the ambient differential along the smooth
Mackey isomorphism, then identify it with the iterated slot sum by the algebraic chain identity.
This avoids constructing a second equivariance proof for the same slot operator. -/

/-- The differential on the orbitwise tensor product, transported along the Mackey comparison.
Its iterated slot-sum formula is `smoothTensorInducedMackeyResolutionDifferential_apply`. -/
noncomputable def smoothTensorInducedMackeyResolutionDifferential :
    smoothTensorInducedMackeyResolutionModule U V hU r t A ⟶
      smoothTensorInducedMackeyResolutionModule U V hU r t A :=
  (smoothTensorInducedMackeyIso U V hU r hr t s
    (smoothGradedResolutionFunctor.obj A)).hom ≫
      (smoothResFunctor R V.subtype continuous_subtype_val).map
        (smoothTensorInducedGradedResolutionDifferential U hU s A) ≫
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).inv

/-- The Mackey differential applies the original differential in one factor of one orbit at a
time. In particular the transported differential is the actual tensor-complex differential. -/
theorem smoothTensorInducedMackeyResolutionDifferential_apply
    [DecidableEq (DoubleCoset.Quotient (V : Set G) (U : Set G))]
    [∀ D, DecidableEq (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)]
    (z : (smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.V) :
    (smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A).hom.hom z =
      PiTensorProduct.slotSum _ (fun D ↦
        PiTensorProduct.slotSum (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)
          (fun _ ↦ A.obj.gradedResolutionDifferential)) z := by
  classical
  let B := (ofSmoothDiscrete R U).obj (smoothGradedResolutionFunctor.obj A)
  have hd (g : U) : A.obj.gradedResolutionDifferential ∘ₗ B.ρ g =
      B.ρ g ∘ₗ A.obj.gradedResolutionDifferential := by
    let f := (ofSmoothDiscrete R U).map (smoothGradedResolutionDifferential A)
    have hf : f.toLinearMap = A.obj.gradedResolutionDifferential :=
      (ofSmoothDiscrete_map_toLinearMap R U _).trans
        (LinearMap.ext (smoothGradedResolutionDifferential_hom_apply A))
    rw [← hf]
    exact f.isIntertwining' g
  let e := smoothTensorInducedMackeyIso U V hU r hr t s
    (smoothGradedResolutionFunctor.obj A)
  let dz := PiTensorProduct.slotSum _ (fun D ↦
    PiTensorProduct.slotSum (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)
      (fun _ ↦ A.obj.gradedResolutionDifferential)) z
  have hk : (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom
      (e.hom.hom.hom z) = e.hom.hom.hom dz := by
    dsimp only [dz]
    -- The smooth/discrete presentations agree at semireducible transparency.
    erw [smoothTensorInducedGradedResolutionDifferential_apply,
      smoothTensorInducedMackeyIso_hom_apply, smoothTensorInducedMackeyIso_hom_apply]
    exact (Subgroup.tensorInducedMackey_slotSum U V r hr t B.ρ s hd z).symm
  -- Fix the carrier presentation of the transported composite before rewriting.
  suffices e.inv.hom.hom
      ((smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom
        (e.hom.hom.hom z)) = dz by exact this
  rw [hk]
  exact congrArg (fun f ↦ f.hom.hom dz) e.hom_inv_id

omit [Fintype (G ⧸ U)] in
/-- The orbitwise action preserves the sum of the orbitwise total degrees. -/
theorem smoothTensorInducedMackeyResolutionPiece_ρ_mem (n : ℤ) (g : V)
    (z : (smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.V)
    (hz : z ∈ smoothTensorInducedMackeyResolutionPiece U V hU r t A n) :
    ((smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.ρ g) z ∈
      smoothTensorInducedMackeyResolutionPiece U V hU r t A n := by
  let B := (ofSmoothDiscrete R U).obj (smoothGradedResolutionFunctor.obj A)
  let M D := DiscreteRep.tensorInduced _ (U.isOpen_mackeySubgroup_subgroupOf V hU (r D))
    (t D) (DiscreteRep.res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D)) B)
  have hB : B.ρ = A.obj.gradedResolutionRepresentation := by
    ext u x
    exact (ofSmoothDiscrete_obj_ρ_apply R U _ u x).trans
      ((smoothGradedResolutionFunctor_obj_obj_ρ_apply A u x).trans
        (A.obj.gradedResolutionTopRep_ρ_apply u x))
  have hM D : LinearMap.IsHomogeneous ((M D).ρ g)
      (PiTensorProduct.totalDegreePiece _ (fun _ ↦ A.obj.gradedResolutionPiece))
      (PiTensorProduct.totalDegreePiece _ (fun _ ↦ A.obj.gradedResolutionPiece)) 0 := by
    have hρ u : LinearMap.IsHomogeneous
        ((DiscreteRep.res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D)) B).ρ u)
        A.obj.gradedResolutionPiece A.obj.gradedResolutionPiece 0 := by
      have he :
          (DiscreteRep.res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D)) B).ρ u =
            B.ρ (mackeyToH (r D) U V u) :=
        LinearMap.ext (DiscreteRep.res_ρ_apply _ _ B u)
      rw [he, hB]
      exact A.obj.isHomogeneous_gradedResolutionRepresentation _
    have he : (M D).ρ g =
        (DiscreteRep.res (mackeyToH (r D) U V) (U.continuous_mackeyToH V (r D)) B).ρ.wreathTensor
          _ (((mackeySubgroup (r D) U V).subgroupOf V).monomialHom (t D) g) := by
      ext x
      exact (DiscreteRep.tensorInduced_ρ_apply _ _ _ _ g x).trans
        (Subgroup.tensorInducedRepresentation_apply _ _ _ g x)
    rw [he]
    exact Representation.isHomogeneous_wreathTensor _ hρ _
  have he : ((smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.ρ g) z =
      PiTensorProduct.map (fun D ↦ (M D).ρ g) z :=
    (DiscreteRep.piTensorProduct_ρ_apply M g z).trans
      (LinearMap.congr_fun (Representation.piTensorProduct_apply _ g) z)
  have h := (PiTensorProduct.isHomogeneous_map hM).map_mem hz
  rw [Finset.sum_const_zero, add_zero] at h
  exact he.symm ▸ h

omit [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] in
/-- The Mackey differential intertwines the comparison with the ambient differential. -/
private theorem mackeyResolutionDifferential_comp_hom :
    smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A ≫
        (smoothTensorInducedMackeyIso U V hU r hr t s
          (smoothGradedResolutionFunctor.obj A)).hom =
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).hom ≫
          (smoothResFunctor R V.subtype continuous_subtype_val).map
            (smoothTensorInducedGradedResolutionDifferential U hU s A) := by
  -- Fix the codomain presentation before categorical simplification across the coefficient
  -- dictionaries; their underlying objects agree, but not at reducible transparency.
  let e : smoothTensorInducedMackeyResolutionModule U V hU r t A ≅
      (smoothResFunctor R V.subtype continuous_subtype_val).obj
        ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A) :=
    smoothTensorInducedMackeyIso U V hU r hr t s (smoothGradedResolutionFunctor.obj A)
  let δ := (smoothResFunctor R V.subtype continuous_subtype_val).map
    (smoothTensorInducedGradedResolutionDifferential U hU s A)
  have key : (e.hom ≫ δ ≫ e.inv) ≫ e.hom = e.hom ≫ δ := by simp [Category.assoc]
  exact key

/-- The orbitwise differential raises the sum of degrees by one. -/
theorem isHomogeneous_smoothTensorInducedMackeyResolutionDifferential :
    LinearMap.IsHomogeneous
      (smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A).hom.hom.toLinearMap
      (smoothTensorInducedMackeyResolutionPiece U V hU r t A)
      (smoothTensorInducedMackeyResolutionPiece U V hU r t A) 1 := by
  refine LinearMap.isHomogeneous_def.2 fun n z hz ↦ ?_
  have he := congrArg (fun f ↦ f.hom.hom z)
    (mackeyResolutionDifferential_comp_hom U V hU r hr t s A)
  exact (smoothTensorInducedMackeyIso_mem_resolutionPiece_iff U V hU r hr t s A (n + 1) _).1
    ((congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A (n + 1)) he).mpr
      ((isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A).map_mem
        ((smoothTensorInducedMackeyIso_mem_resolutionPiece_iff U V hU r hr t s A n z).2 hz)))

omit [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] in
/-- The orbitwise tensor differential squares to zero in characteristic two. -/
theorem smoothTensorInducedMackeyResolutionDifferential_sq (hA : ∀ a : A.obj.V, a + a = 0) :
    (smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A).hom ≫
      (smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A).hom = 0 := by
  let e : smoothTensorInducedMackeyResolutionModule U V hU r t A ≅
      (smoothResFunctor R V.subtype continuous_subtype_val).obj
        ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A) :=
    smoothTensorInducedMackeyIso U V hU r hr t s (smoothGradedResolutionFunctor.obj A)
  let δ := (smoothResFunctor R V.subtype continuous_subtype_val).map
    (smoothTensorInducedGradedResolutionDifferential U hU s A)
  have hδ : δ ≫ δ = 0 := by
    apply ObjectProperty.hom_ext
    refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
    exact ConcreteCategory.congr_hom
      (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA) z
  have he : (e.hom ≫ δ ≫ e.inv) ≫ (e.hom ≫ δ ≫ e.inv) = 0 := by
    simp only [Category.assoc, e.inv_hom_id_assoc]
    rw [← Category.assoc δ δ, hδ]
    simp
  exact congrArg (fun f ↦ f.hom) he

/-- The cochain complex on the orbitwise tensor product of restrictions of the original total
resolution. Its grading and differential are the iterated total grading and iterated slot sum.
The body is exposed so that each degree has its native subtype carrier, as for
`TopRep.gradedCochainComplex`. -/
@[expose] noncomputable def smoothTensorInducedMackeyResolution (hA : ∀ a : A.obj.V, a + a = 0) :
    CochainComplex (TopRep.{max u v w} R V) ℕ :=
  (smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.gradedCochainComplex
    (smoothTensorInducedMackeyResolutionPiece U V hU r t A)
    (smoothTensorInducedMackeyResolutionPiece_ρ_mem U V hU r t A)
    (smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A).hom
    (isHomogeneous_smoothTensorInducedMackeyResolutionDifferential U V hU r hr t s A)
    (smoothTensorInducedMackeyResolutionDifferential_sq U V hU r hr t s A hA)

/-- The Mackey comparison identifies the orbitwise tensor complex with the complex of the
restricted ambient tensor-induced resolution, in every degree. -/
noncomputable def smoothTensorInducedMackeyResolutionIso (hA : ∀ a : A.obj.V, a + a = 0) :
    let M := ((smoothResFunctor R V.subtype continuous_subtype_val).obj
      ((smoothTensorInducedGradedResolutionFunctor U hU s).obj A)).obj
    let d := ((smoothResFunctor R V.subtype continuous_subtype_val).map
      (smoothTensorInducedGradedResolutionDifferential U hU s A)).hom
    smoothTensorInducedMackeyResolution U V hU r hr t s A hA ≅
      M.gradedCochainComplex (smoothTensorInducedGradedResolutionPiece U hU s A)
        (fun n g z hz ↦ smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A n g z hz) d
        (isHomogeneous_smoothTensorInducedGradedResolutionDifferential U hU s A)
        (by
          refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
          exact ConcreteCategory.congr_hom
            (smoothTensorInducedGradedResolutionDifferential_sq U hU s A hA) z) := by
  let e := (smoothDiscreteι R V).mapIso
    (smoothTensorInducedMackeyIso U V hU r hr t s (smoothGradedResolutionFunctor.obj A))
  exact TopRep.gradedCochainComplexIso e
    (smoothTensorInducedMackeyIso_mem_resolutionPiece_iff U V hU r hr t s A)
    (congrArg (fun f ↦ f.hom) (mackeyResolutionDifferential_comp_hom U V hU r hr t s A))

/-- In each degree the chain comparison applies the original smooth Mackey comparison. -/
@[simp]
theorem smoothTensorInducedMackeyResolutionIso_hom_f_apply
    (hA : ∀ a : A.obj.V, a + a = 0) (n : ℕ)
    (z : ((smoothTensorInducedMackeyResolution U V hU r hr t s A hA).X n).V) :
    (((smoothTensorInducedMackeyResolutionIso U V hU r hr t s A hA).hom.f n).hom z).1 =
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).hom.hom.hom z.1 := by
  unfold smoothTensorInducedMackeyResolutionIso
  exact TopRep.gradedCochainComplexIso_hom_f_apply _ _ _ _ _

/-- In each degree the inverse chain comparison applies the inverse smooth Mackey comparison. -/
@[simp]
theorem smoothTensorInducedMackeyResolutionIso_inv_f_apply
    (hA : ∀ a : A.obj.V, a + a = 0) (n : ℕ)
    (z) :
    (((smoothTensorInducedMackeyResolutionIso U V hU r hr t s A hA).inv.f n).hom z).1 =
      (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).inv.hom.hom z.1 := by
  unfold smoothTensorInducedMackeyResolutionIso
  exact TopRep.gradedCochainComplexIso_inv_f_apply _ _ _ _ _

omit [Fintype (DoubleCoset.Quotient (V : Set G) (U : Set G))]
  [∀ D, Fintype (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)] [Fintype (G ⧸ U)] in
/-- The Mackey chain comparison is augmented: applying the coefficient augmentation in every
factor before the resolution comparison equals first the coefficient Mackey comparison and then
the ambient tensor augmentation. This is an identity on arbitrary tensors. -/
theorem smoothTensorInducedMackeyIso_resolutionAugmentation
    (z : ⨂[R] D : DoubleCoset.Quotient (V : Set G) (U : Set G),
      ⨂[R] _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V, A.obj.V) :
    (smoothTensorInducedMackeyIso U V hU r hr t s
        (smoothGradedResolutionFunctor.obj A)).hom.hom.hom
        (PiTensorProduct.map (fun _ ↦ PiTensorProduct.map
          (fun _ ↦ A.obj.gradedResolutionAugmentation)) z) =
      PiTensorProduct.map (fun _ ↦ A.obj.gradedResolutionAugmentation)
        ((smoothTensorInducedMackeyIso U V hU r hr t s A).hom.hom.hom z) := by
  have hf : (smoothGradedResolutionAugmentationApp A).hom.hom.toLinearMap =
      A.obj.gradedResolutionAugmentation :=
    LinearMap.ext (smoothGradedResolutionAugmentationApp_hom_apply A)
  have h := smoothTensorInducedMackeyIso_hom_naturality_apply U V hU r hr t s
    (smoothGradedResolutionAugmentationApp A) z
  rw [hf] at h
  exact h

end TauCeti
