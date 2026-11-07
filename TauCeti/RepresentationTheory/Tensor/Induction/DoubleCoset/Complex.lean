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

The orbit factors here use restrictions of the original coinduced resolution. They are not yet
the coinduced resolutions of the conjugated coefficient modules. The augmented chain comparison
constructed here is the first comparison needed to express the restricted norm as a product of
orbitwise norms. In particular its augmentation applies the original augmentation in every
factor, as recorded by `smoothTensorInducedMackeyIso_resolutionAugmentation`.

We obtain the equivariant differential by conjugating the ambient differential along the smooth
Mackey isomorphism, then identify it with the iterated slot sum by the algebraic chain identity.
This avoids constructing a second equivariance proof for the same slot operator.

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
  have hρ (g : U) : LinearMap.IsHomogeneous (B.ρ g)
      A.obj.gradedResolutionPiece A.obj.gradedResolutionPiece 0 :=
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      rw [add_zero]
      exact (congrArg (· ∈ A.obj.gradedResolutionPiece p)
        ((ofSmoothDiscrete_obj_ρ_apply R U _ g x).trans
          (smoothGradedResolutionFunctor_obj_obj_ρ_apply A g x))).mpr
            (A.obj.gradedResolutionTopRep_ρ_mem p g x hx)
  exact (congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A n)
    (smoothTensorInducedMackeyIso_hom_apply U V hU r hr t s
      (smoothGradedResolutionFunctor.obj A) z)).to_iff.trans
        (Subgroup.tensorInducedMackey_mem_totalDegreePiece_iff U V r hr t B.ρ s hρ n z)

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
    exact (congrArg (· ∘ₗ B.ρ g) hf.symm).trans
      ((f.isIntertwining' g).trans (congrArg (B.ρ g ∘ₗ ·) hf))
  let e := smoothTensorInducedMackeyIso U V hU r hr t s
    (smoothGradedResolutionFunctor.obj A)
  let dz := PiTensorProduct.slotSum _ (fun D ↦
    PiTensorProduct.slotSum (V ⧸ (mackeySubgroup (r D) U V).subgroupOf V)
      (fun _ ↦ A.obj.gradedResolutionDifferential)) z
  have he (x) := smoothTensorInducedMackeyIso_hom_apply U V hU r hr t s
    (smoothGradedResolutionFunctor.obj A) x
  have hc : e.inv.hom.hom (e.hom.hom.hom dz) = dz :=
    congrArg (fun f ↦ f.hom.hom dz) e.hom_inv_id
  have hk : (smoothTensorInducedGradedResolutionDifferential U hU s A).hom.hom
      (e.hom.hom.hom z) = e.hom.hom.hom dz :=
    (smoothTensorInducedGradedResolutionDifferential_apply U hU s A _).trans
      ((congrArg (PiTensorProduct.slotSum (G ⧸ U)
        (fun _ ↦ A.obj.gradedResolutionDifferential)) (he z)).trans
          ((Subgroup.tensorInducedMackey_slotSum U V r hr t B.ρ s hd z).symm.trans
            (he dz).symm))
  exact (congrArg e.inv.hom.hom hk).trans hc

omit [Fintype (G ⧸ U)] in
include hr s in
/-- The orbitwise action preserves the sum of the orbitwise total degrees. -/
theorem smoothTensorInducedMackeyResolutionPiece_ρ_mem (n : ℤ) (g : V)
    (z : (smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.V)
    (hz : z ∈ smoothTensorInducedMackeyResolutionPiece U V hU r t A n) :
    ((smoothTensorInducedMackeyResolutionModule U V hU r t A).obj.ρ g) z ∈
      smoothTensorInducedMackeyResolutionPiece U V hU r t A n := by
  let : Fintype (G ⧸ U) := Fintype.ofFinite _
  let e := smoothTensorInducedMackeyIso U V hU r hr t s
    (smoothGradedResolutionFunctor.obj A)
  exact (smoothTensorInducedMackeyIso_mem_resolutionPiece_iff U V hU r hr t s A n _).1
    ((congrArg (· ∈ smoothTensorInducedGradedResolutionPiece U hU s A n)
      (e.hom.hom.hom.isIntertwining g z)).mpr
        (smoothTensorInducedGradedResolutionPiece_ρ_mem U hU s A n g _
          ((smoothTensorInducedMackeyIso_mem_resolutionPiece_iff U V hU r hr t s A n z).2 hz)))

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
    (smoothTensorInducedMackeyResolutionPiece_ρ_mem U V hU r hr t s A)
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
  let f := (ofSmoothDiscrete R U).map (smoothGradedResolutionAugmentationApp A)
  have hf : f.toLinearMap = A.obj.gradedResolutionAugmentation :=
    (ofSmoothDiscrete_map_toLinearMap R U _).trans
      (LinearMap.ext (smoothGradedResolutionAugmentationApp_hom_apply A))
  have h := Subgroup.tensorInducedMackey_naturality U V r hr t
    ((ofSmoothDiscrete R U).obj A).ρ f s z
  have hmap : PiTensorProduct.map (fun _ : G ⧸ U ↦ f.toLinearMap) =
      PiTensorProduct.map (fun _ : G ⧸ U ↦ A.obj.gradedResolutionAugmentation) :=
    congrArg (fun f ↦ PiTensorProduct.map (fun _ : G ⧸ U ↦ f)) hf
  have hinner : PiTensorProduct.map (fun D : DoubleCoset.Quotient (V : Set G) (U : Set G) ↦
        PiTensorProduct.map (fun _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V ↦ f.toLinearMap)) =
      PiTensorProduct.map (fun D : DoubleCoset.Quotient (V : Set G) (U : Set G) ↦
        PiTensorProduct.map (fun _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V ↦
          A.obj.gradedResolutionAugmentation)) :=
    congrArg (fun f ↦ PiTensorProduct.map (fun D : DoubleCoset.Quotient (V : Set G) (U : Set G) ↦
      PiTensorProduct.map (fun _ : V ⧸ (mackeySubgroup (r D) U V).subgroupOf V ↦ f))) hf
  exact (smoothTensorInducedMackeyIso_hom_apply U V hU r hr t s
    (smoothGradedResolutionFunctor.obj A) _).trans
      ((congrArg _ (LinearMap.congr_fun hinner.symm z)).trans
        (h.trans ((LinearMap.congr_fun
          (Representation.IntertwiningMap.tensorInduced_toLinearMap f s) _).trans
            ((LinearMap.congr_fun hmap _).trans
              (congrArg _ (smoothTensorInducedMackeyIso_hom_apply U V hU r hr t s A z).symm)))))

end TauCeti
