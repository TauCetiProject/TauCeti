/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
public import TauCeti.Algebra.Module.GradedModule.Trivial
public import TauCeti.CategoryTheory.Groupoid.ConnectedFunctor

/-!
# Classical local systems as DG local systems in degree zero

A classical local system on a pointed space `(B, b)` is a functor from the fundamental groupoid to
`R`-modules.  Its fiber at `b` is a representation of `π₁(B, b)`, hence a module over the group
ring `R[π₁(B, b)]`, and the chain algebra `C_*(Ω_b B; R)` acts on it from the right through the
ring homomorphism `loopChainToGroupAlgebra`, which keeps the degree-zero
component and sends it to the group ring by `loopZeroChainToGroupAlgebra`.  With the trivial
grading and the zero differential, the fiber is a DG local system concentrated in degree zero (the
source's Definition 1.8 in degree zero).

## Main definitions

* `TauCeti.classicalAction`: the resulting action of the chain algebra on the fiber of a local
  system.
* `TauCeti.classicalDGLocalSystem`: the DG local system of a classical local system.
* `TauCeti.classicalDGLocalSystemFunctor`: the functor from classical local systems.

## Main results

* `TauCeti.isDGRightModule_fiber`: the fiber is a DG right module, with the trivial grading and
  zero differential.
* `TauCeti.classicalDGLocalSystemMap_injective`: on a path-connected space, a morphism of local
  systems is determined by the induced morphism of DG local systems.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definition 1.8.
-/

public section

noncomputable section

open MulOpposite DirectSum

namespace TauCeti

universe u w

section Action

open CategoryTheory

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {x : X}

/-- **The action of the chain algebra on the fiber of a local system**: the algebra map from the
opposite of `C_*(Ω_x X; R)` to the endomorphisms of the fiber at `x`, through the degree-zero ring
map and the monodromy representation.  A Moore loop acts by the monodromy of its class. -/
def classicalAction (L : LocalCoefficientSystem.{u, u, w} R X) :
    (loopChainAlgebra X x R)ᵐᵒᵖ →ₐ[R] Module.End R (L.obj (FundamentalGroupoid.mk x)) :=
  ((AlgEquiv.opOp R (Module.End R (L.obj (FundamentalGroupoid.mk x)))).symm :
      _ ≃ₐ[R] _).toAlgHom.comp
    ((MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
      (FundamentalGroup X x) (LocalCoefficientSystem.fiberRightAction L)).comp
      (loopChainToGroupAlgebra X x R)).op

theorem classicalAction_op_apply (L : LocalCoefficientSystem.{u, u, w} R X)
    (a : loopChainAlgebra X x R) :
    classicalAction L (op a) =
      (MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
        (FundamentalGroup X x) (LocalCoefficientSystem.fiberRightAction L)
        (loopChainToGroupAlgebra X x R a)).unop := by
  simp [classicalAction]

theorem classicalAction_eq_zero (L : LocalCoefficientSystem.{u, u, w} R X)
    {a : loopChainAlgebra X x R} (ha : loopChainToGroupAlgebra X x R a = 0) :
    classicalAction L (op a) = 0 := by
  rw [classicalAction_op_apply, ha, map_zero, unop_zero]

/-- The right action of the chain algebra on the fiber of a classical local system. -/
instance instModuleOpFiber (L : LocalCoefficientSystem.{u, u, w} R X) :
    Module (loopChainAlgebra X x R)ᵐᵒᵖ (L.obj (FundamentalGroupoid.mk x)) :=
  Module.compHom _ (classicalAction L).toRingHom

@[simp]
theorem op_smul_eq_classicalAction (L : LocalCoefficientSystem.{u, u, w} R X)
    (a : loopChainAlgebra X x R)
    (m : L.obj (FundamentalGroupoid.mk x)) : op a • m = classicalAction L (op a) m :=
  rfl

/-- The action of the chain algebra on the fiber is compatible with the `R`-module structure:
the scalars `R` act through the algebra map, as the DG right-module structure requires. -/
instance (L : LocalCoefficientSystem.{u, u, w} R X) :
    IsScalarTower R (loopChainAlgebra X x R)ᵐᵒᵖ (L.obj (FundamentalGroupoid.mk x)) where
  smul_assoc r a m := congrArg (fun f ↦ f m) (map_smul (classicalAction L) r a)

/-- The chain algebra acts on the fiber, concentrated in degree zero, compatibly with the
gradings: every homogeneous element of nonzero degree acts by zero. -/
instance (L : LocalCoefficientSystem.{u, u, w} R X) :
    SetLike.GradedSMul (InternalGrading.ofDecomposition
      (cubicalChainGrading (MooreLoopSpace X x) R)).opposite.piece
      (trivialGrading R (L.obj (FundamentalGroupoid.mk x)))
    where
  smul_mem {i j a m} ha hm := by
    rw [InternalGrading.mem_opposite_piece_iff, InternalGrading.ofDecomposition_piece] at ha
    rw [mem_trivialGrading_iff] at hm ⊢
    rcases hm with rfl | rfl
    · by_cases hi : i = 0
      · left
        simp [hi]
      · right
        rw [← op_unop a, op_smul_eq_classicalAction,
          classicalAction_eq_zero L (loopChainToGroupAlgebra_eq_zero_of_mem hi ha)]
        exact LinearMap.zero_apply m
    · right
      simp

/-- **The fiber of a classical local system is a DG right module over `C_*(Ω_x X; R)`**, with the
trivial grading and the zero differential. -/
theorem isDGRightModule_fiber (L : LocalCoefficientSystem.{u, u, w} R X) :
    IsDGRightModule (loopChain_isDGAlgebra X x R)
      (trivialGrading R (L.obj (FundamentalGroupoid.mk x)))
      (0 : L.obj (FundamentalGroupoid.mk x) →ₗ[R] L.obj (FundamentalGroupoid.mk x)) where
  isHomogeneous := LinearMap.isHomogeneous_zero _ _ _
  sq_zero _ := LinearMap.zero_apply _
  leibniz {_ _} _ a := by
    rw [op_smul_eq_classicalAction _ (cubicalChainDifferential _ R a),
      classicalAction_eq_zero L (loopChainToGroupAlgebra_differential a)]
    simp

variable (x) in
/-- **The DG local system of a classical local system**: the fiber at the basepoint, concentrated
in degree zero. -/
-- Exposed because the types of `classicalDGLocalSystem_grading` and `classicalDGLocalSystemMap`
-- mention its carrier and `DGRightModuleHom` between the underlying fiber modules.
@[expose] def classicalDGLocalSystem (L : LocalCoefficientSystem.{u, u, w} R X) :
    DGLocalSystem X x R :=
  DGRightModuleCat.of (isDGRightModule_fiber L)

@[simp]
theorem classicalDGLocalSystem_carrier (L : LocalCoefficientSystem.{u, u, w} R X) :
    (classicalDGLocalSystem x L).carrier = L.obj (FundamentalGroupoid.mk x) :=
  (rfl)

@[simp]
theorem classicalDGLocalSystem_grading (L : LocalCoefficientSystem.{u, u, w} R X) :
    (classicalDGLocalSystem x L).grading = trivialGrading R (L.obj (FundamentalGroupoid.mk x)) :=
  (rfl)

@[simp]
theorem classicalDGLocalSystem_differential (L : LocalCoefficientSystem.{u, u, w} R X) :
    (classicalDGLocalSystem x L).differential = 0 :=
  (rfl)

/-- A Moore loop acts on the fiber by the monodromy of its class: the point chain of a loop `γ`
acts by the monodromy of the inverse of `fundamentalGroupHom γ`, that is of the class of `γ`. -/
@[simp]
theorem classicalAction_lof_ofCube (L : LocalCoefficientSystem.{u, u, w} R X)
    (c : SingularCube (MooreLoopSpace X x) 0) :
    classicalAction L (op (cubicalChainLof (MooreLoopSpace X x) R 0
        (NormalizedCubicalChain.ofCube (MooreLoopSpace X x) R c))) =
      LocalCoefficientSystem.monodromyRepresentation L x
        (MooreLoopSpace.fundamentalGroupHom x (c 0))⁻¹ := by
  simp only [classicalAction_op_apply, loopChainToGroupAlgebra_lof_zero,
    loopZeroChainToGroupAlgebra_ofCube]
  simp

theorem classicalAction_naturality {L L' : LocalCoefficientSystem.{u, u, w} R X} (φ : L ⟶ L')
    (a : (loopChainAlgebra X x R)ᵐᵒᵖ) (m : L.obj (FundamentalGroupoid.mk x)) :
    (φ.app (FundamentalGroupoid.mk x)).hom (classicalAction L a m) =
      classicalAction L' a ((φ.app (FundamentalGroupoid.mk x)).hom m) := by
  rw [← op_unop a, classicalAction_op_apply, classicalAction_op_apply]
  exact LocalCoefficientSystem.fiberRightAction_lift_naturality φ _ m

/-- **A morphism of classical local systems induces a morphism of DG local systems.** -/
def classicalDGLocalSystemMap {L L' : LocalCoefficientSystem.{u, u, w} R X} (φ : L ⟶ L') :
    DGRightModuleHom (isDGRightModule_fiber (x := x) L) (isDGRightModule_fiber (x := x) L') where
  toLinearMap :=
    { toFun := fun m ↦ (φ.app (FundamentalGroupoid.mk x)).hom m
      map_add' := fun m n ↦ map_add _ m n
      map_smul' := fun a m ↦ classicalAction_naturality φ a m }
  map_mem' := fun {q m} hm ↦ by
    rw [mem_trivialGrading_iff] at hm ⊢
    rcases hm with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (map_zero _)
  map_d' := fun m ↦ by simp

@[simp]
theorem classicalDGLocalSystemMap_apply {L L' : LocalCoefficientSystem.{u, u, w} R X} (φ : L ⟶ L')
    (m : L.obj (FundamentalGroupoid.mk x)) :
    classicalDGLocalSystemMap (x := x) φ m = (φ.app (FundamentalGroupoid.mk x)).hom m :=
  (rfl)

theorem classicalDGLocalSystemMap_comp_apply {L L' L'' : LocalCoefficientSystem.{u, u, w} R X}
    (φ : L ⟶ L') (ψ : L' ⟶ L'') (m : L.obj (FundamentalGroupoid.mk x)) :
    classicalDGLocalSystemMap (x := x) (φ ≫ ψ) m =
      classicalDGLocalSystemMap (x := x) ψ (classicalDGLocalSystemMap (x := x) φ m) :=
  (rfl)

variable (x R) in
/-- **The functor from classical local systems to DG local systems**: a classical local system
goes to its fiber at the basepoint, concentrated in degree zero. -/
-- Exposed because the type of `classicalDGLocalSystemFunctor_map` needs `obj` to unfold to
-- `classicalDGLocalSystem` for `classicalDGLocalSystemMap φ` to be a morphism.
@[expose] def classicalDGLocalSystemFunctor :
    LocalCoefficientSystem.{u, u, w} R X ⥤ DGLocalSystem X x R where
  obj L := classicalDGLocalSystem x L
  map φ := classicalDGLocalSystemMap φ
  -- `ext` finds no extensionality lemma for these goals, so `hom_ext` is applied with the
  -- objects named explicitly, which unblocks the stuck `GradedAlgebra` instance problem.
  map_id L := by
    refine DGRightModuleCat.hom_ext (M := classicalDGLocalSystem x L)
      (N := classicalDGLocalSystem x L) fun m ↦ ?_
    rw [DGRightModuleCat.id_apply]
    exact classicalDGLocalSystemMap_apply (𝟙 L) m
  map_comp φ ψ := by
    refine DGRightModuleCat.hom_ext (M := classicalDGLocalSystem x _)
      (N := classicalDGLocalSystem x _) fun m ↦ ?_
    exact (classicalDGLocalSystemMap_comp_apply φ ψ m).trans
      (DGRightModuleCat.comp_apply (M := classicalDGLocalSystem x _)
        (N := classicalDGLocalSystem x _) (P := classicalDGLocalSystem x _)
        (classicalDGLocalSystemMap φ) (classicalDGLocalSystemMap ψ) m).symm

@[simp]
theorem classicalDGLocalSystemFunctor_obj (L : LocalCoefficientSystem.{u, u, w} R X) :
    (classicalDGLocalSystemFunctor R x).obj L = classicalDGLocalSystem x L :=
  (rfl)

@[simp]
theorem classicalDGLocalSystemFunctor_map {L L' : LocalCoefficientSystem.{u, u, w} R X}
    (φ : L ⟶ L') :
    (classicalDGLocalSystemFunctor R x).map φ = classicalDGLocalSystemMap φ :=
  (rfl)

/-- **A morphism of local systems on a path-connected space is determined by the induced morphism of
DG local systems**: it is determined by its component at the basepoint, by transport along
paths. -/
theorem classicalDGLocalSystemMap_injective [PathConnectedSpace X]
    {L L' : LocalCoefficientSystem.{u, u, w} R X} :
    Function.Injective (classicalDGLocalSystemMap (x := x) (L := L) (L' := L')) := by
  intro φ ψ h
  have hx : φ.app (FundamentalGroupoid.mk x) = ψ.app (FundamentalGroupoid.mk x) :=
    ModuleCat.hom_ext (LinearMap.ext fun m ↦ congrArg (fun f ↦ f.toLinearMap m) h)
  exact Groupoid.natTrans_ext (x₀ := FundamentalGroupoid.mk x)
    (FundamentalGroupoid.nonempty_hom _) hx

/-- On a path-connected space, the functor from classical to DG local systems is faithful. -/
instance [PathConnectedSpace X] : (classicalDGLocalSystemFunctor R x).Faithful where
  map_injective h := by
    rw [classicalDGLocalSystemFunctor_map, classicalDGLocalSystemFunctor_map] at h
    exact classicalDGLocalSystemMap_injective h

end Action

end TauCeti
