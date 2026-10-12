/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.ZerothHomology
public import TauCeti.AlgebraicTopology.DGLocalSystem.Basic
public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.RingTheory.GradedAlgebra.Trivial
public import TauCeti.CategoryTheory.Groupoid.ConnectedFunctor

/-!
# Classical local systems as DG local systems in degree zero

A classical local system on a pointed space `(B, b)` is a functor from the fundamental groupoid to
`R`-modules.  Its fiber at `b` is a representation of `π₁(B, b)`, hence a module over the group
ring `R[π₁(B, b)ᵐᵒᵖ]` on which the chain algebra `C_*(Ω_b B; R)` acts through the ring homomorphism
`loopChainDegreeZero` which keeps the degree-zero component and sends it to the group ring by
`zerothClass`.  With the trivial grading and the zero differential, the fiber is a DG local system
concentrated in degree zero (the source's Definition 1.8 in degree zero).

## Main definitions

* `TauCeti.loopChainDegreeZero`: the algebra map `C_*(Ω_b B; R) → R[π₁(B, b)ᵐᵒᵖ]`.
* `TauCeti.classicalAction`: the resulting action of the chain algebra on the fiber of a local
  system.
* `TauCeti.classicalDGLocalSystem`: the DG local system of a classical local system.
* `TauCeti.classicalDGLocalSystemFunctor`: the functor from classical local systems.

## Main results

* `TauCeti.loopChainDegreeZero_lof`, `TauCeti.loopChainDegreeZero_differential`: the values on
  homogeneous chains, and compatibility with the differential.
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

section DegreeZero

variable (B : Type*) [TopologicalSpace B] (b : B) (R : Type*) [CommRing R]

/-- The component of `loopChainDegreeZero` in dimension `n`: the class map in dimension zero and
zero in positive dimensions. -/
def zerothComponent :
    (n : ℕ) → NormalizedCubicalChain (MooreLoopSpace B b) R n →ₗ[R]
      MonoidAlgebra R (FundamentalGroup B b)ᵐᵒᵖ
  | 0 => zerothClass B b R
  | _ + 1 => 0

variable {B b R}

@[simp]
theorem zerothComponent_zero : zerothComponent B b R 0 = zerothClass B b R :=
  (rfl)

theorem zerothComponent_eq_zero {n : ℕ} (h : n ≠ 0)
    (x : NormalizedCubicalChain (MooreLoopSpace B b) R n) : zerothComponent B b R n x = 0 := by
  cases n with
  | zero => exact absurd rfl h
  | succ n => rfl

variable (B b R)

/-- **The degree-zero ring map**: the algebra map from the chains on the Moore loop space to the
group ring of the opposite fundamental group, which is the class map on `0`-chains and zero on
chains of positive dimension. -/
def loopChainDegreeZero : loopChainAlgebra B b R →ₐ[R] MonoidAlgebra R (FundamentalGroup B b)ᵐᵒᵖ :=
  DirectSum.toAlgebra R _ (zerothComponent B b R)
    (by simp [zerothComponent])
    (fun {i j} x y ↦ by
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · subst hi hj
          simp [zerothComponent]
        · rw [zerothComponent_eq_zero (by omega), zerothComponent_eq_zero hj, mul_zero]
      · rw [zerothComponent_eq_zero (by omega), zerothComponent_eq_zero hi, zero_mul])

variable {B b R}

/-- The degree-zero ring map on a homogeneous chain. -/
theorem loopChainDegreeZero_lof (n : ℕ) (y : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainDegreeZero B b R (cubicalChainLof (MooreLoopSpace B b) R n y) =
      zerothComponent B b R n y := by
  rw [loopChainDegreeZero, DirectSum.toAlgebra_apply, cubicalChainLof, DirectSum.lof_eq_of]
  exact DirectSum.toSemiring_of _ _ _ n y

/-- The degree-zero ring map kills boundaries. -/
theorem loopChainDegreeZero_differential (a : loopChainAlgebra B b R) :
    loopChainDegreeZero B b R (cubicalChainDifferential (MooreLoopSpace B b) R a) = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    cases n with
    | zero =>
      rw [← DirectSum.lof_eq_of R, cubicalChainDifferential_lof_zero, map_zero]
    | succ k =>
      rw [← DirectSum.lof_eq_of R, cubicalChainDifferential_lof_succ]
      cases k with
      | zero =>
        rw [loopChainDegreeZero_lof]
        exact zerothClass_boundary y
      | succ k =>
        rw [loopChainDegreeZero_lof]
        exact zerothComponent_eq_zero (by omega) _
  | add x y hx hy => simp [hx, hy]

/-- The degree-zero ring map kills homogeneous elements of nonzero cohomological degree. -/
theorem loopChainDegreeZero_eq_zero_of_mem {i : ℤ} (hi : i ≠ 0) {a : loopChainAlgebra B b R}
    (ha : a ∈ cubicalChainGrading (MooreLoopSpace B b) R i) :
    loopChainDegreeZero B b R a = 0 := by
  rcases (mem_cubicalChainGrading_iff _ _).1 ha with rfl | ⟨n, y, hn, rfl⟩
  · exact map_zero _
  · rw [loopChainDegreeZero_lof]
    exact zerothComponent_eq_zero (by omega) _

end DegreeZero

section Action

open CategoryTheory

universe u v w

variable {R : Type u} [CommRing R] {X : TopCat.{v}} {x : X}

/-- **The action of the chain algebra on the fiber of a local system**: the algebra map from the
opposite of `C_*(Ω_x X; R)` to the endomorphisms of the fiber at `x`, through the degree-zero ring
map and the monodromy representation. -/
def classicalAction (L : LocalCoefficientSystem.{u, v, w} R X) :
    (loopChainAlgebra X x R)ᵐᵒᵖ →ₐ[R] Module.End R (L.obj (FundamentalGroupoid.mk x)) :=
  ((AlgEquiv.opOp R (Module.End R (L.obj (FundamentalGroupoid.mk x)))).symm :
      _ ≃ₐ[R] _).toAlgHom.comp
    ((MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
      (FundamentalGroup X x)ᵐᵒᵖ
      (LocalCoefficientSystem.monodromyRepresentation L x).op).comp
        (loopChainDegreeZero X x R)).op

theorem classicalAction_eq_zero (L : LocalCoefficientSystem.{u, v, w} R X)
    {a : loopChainAlgebra X x R} (ha : loopChainDegreeZero X x R a = 0) :
    classicalAction L (op a) = 0 := by
  simp [classicalAction, ha]

/-- The right action of the chain algebra on the fiber of a classical local system. -/
instance instModuleOpFiber (L : LocalCoefficientSystem.{u, v, w} R X) :
    Module (loopChainAlgebra X x R)ᵐᵒᵖ (L.obj (FundamentalGroupoid.mk x)) :=
  Module.compHom _ (classicalAction L).toRingHom

theorem op_smul_fiber (L : LocalCoefficientSystem.{u, v, w} R X) (a : loopChainAlgebra X x R)
    (m : L.obj (FundamentalGroupoid.mk x)) : op a • m = classicalAction L (op a) m :=
  rfl

/-- The action of the chain algebra on the fiber is compatible with the `R`-module structure:
the scalars `R` act through the algebra map, as the DG right-module structure requires. -/
instance (L : LocalCoefficientSystem.{u, v, w} R X) :
    IsScalarTower R (loopChainAlgebra X x R)ᵐᵒᵖ (L.obj (FundamentalGroupoid.mk x)) where
  smul_assoc r a m := congrArg (fun f ↦ f m) (map_smul (classicalAction L) r a)

/-- The chain algebra acts on the fiber, concentrated in degree zero, compatibly with the
gradings: every homogeneous element of nonzero degree acts by zero. -/
instance (L : LocalCoefficientSystem.{u, v, w} R X) :
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
        rw [← op_unop a, op_smul_fiber,
          classicalAction_eq_zero L (loopChainDegreeZero_eq_zero_of_mem hi ha)]
        rfl
    · right
      simp

/-- **The fiber of a classical local system is a DG right module over `C_*(Ω_x X; R)`**, with the
trivial grading and the zero differential. -/
theorem isDGRightModule_fiber (L : LocalCoefficientSystem.{u, v, w} R X) :
    IsDGRightModule (loopChain_isDGAlgebra X x R)
      (trivialGrading R (L.obj (FundamentalGroupoid.mk x)))
      (0 : L.obj (FundamentalGroupoid.mk x) →ₗ[R] L.obj (FundamentalGroupoid.mk x)) where
  isHomogeneous := LinearMap.isHomogeneous_zero _ _ _
  sq_zero _ := rfl
  leibniz {_ _} _ a := by
    rw [op_smul_fiber _ (cubicalChainDifferential _ R a),
      classicalAction_eq_zero L (loopChainDegreeZero_differential a)]
    simp

variable (x) in
/-- **The DG local system of a classical local system**: the fiber at the basepoint, concentrated
in degree zero. -/
@[expose] def classicalDGLocalSystem (L : LocalCoefficientSystem.{u, v, w} R X) :
    DGLocalSystem X x R :=
  DGRightModuleCat.of (isDGRightModule_fiber L)

theorem classicalAction_op_apply (L : LocalCoefficientSystem.{u, v, w} R X)
    (a : loopChainAlgebra X x R) :
    classicalAction L (op a) =
      (MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
        (FundamentalGroup X x)ᵐᵒᵖ
        (LocalCoefficientSystem.monodromyRepresentation L x).op
        (loopChainDegreeZero X x R a)).unop := by
  simp [classicalAction]

theorem fiberAct_naturality {L L' : LocalCoefficientSystem.{u, v, w} R X} (φ : L ⟶ L')
    (y : MonoidAlgebra R (FundamentalGroup X x)ᵐᵒᵖ) (m : L.obj (FundamentalGroupoid.mk x)) :
    (φ.app (FundamentalGroupoid.mk x)).hom
        ((MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
          (FundamentalGroup X x)ᵐᵒᵖ
          (LocalCoefficientSystem.monodromyRepresentation L x).op y).unop m) =
      (MonoidAlgebra.lift R (Module.End R (L'.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
        (FundamentalGroup X x)ᵐᵒᵖ
        (LocalCoefficientSystem.monodromyRepresentation L' x).op y).unop
        ((φ.app (FundamentalGroupoid.mk x)).hom m) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add y z hy hz => simp [hy, hz]
  | single g r =>
    simp [MonoidAlgebra.lift_single]

theorem classicalAction_naturality {L L' : LocalCoefficientSystem.{u, v, w} R X} (φ : L ⟶ L')
    (a : (loopChainAlgebra X x R)ᵐᵒᵖ) (m : L.obj (FundamentalGroupoid.mk x)) :
    (φ.app (FundamentalGroupoid.mk x)).hom (classicalAction L a m) =
      classicalAction L' a ((φ.app (FundamentalGroupoid.mk x)).hom m) := by
  rw [← op_unop a, classicalAction_op_apply, classicalAction_op_apply]
  exact fiberAct_naturality φ _ m

/-- **A morphism of classical local systems induces a morphism of DG local systems.** -/
def classicalDGLocalSystemMap {L L' : LocalCoefficientSystem.{u, v, w} R X} (φ : L ⟶ L') :
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
theorem classicalDGLocalSystemMap_apply {L L' : LocalCoefficientSystem.{u, v, w} R X} (φ : L ⟶ L')
    (m : L.obj (FundamentalGroupoid.mk x)) :
    classicalDGLocalSystemMap (x := x) φ m = (φ.app (FundamentalGroupoid.mk x)).hom m :=
  (rfl)

variable (x R) in
/-- **The functor from classical local systems to DG local systems**: a classical local system
goes to its fiber at the basepoint, concentrated in degree zero. -/
def classicalDGLocalSystemFunctor : LocalCoefficientSystem.{u, v, w} R X ⥤ DGLocalSystem X x R where
  obj L := classicalDGLocalSystem x L
  map φ := classicalDGLocalSystemMap φ
  map_id L := DGRightModuleHom.toLinearMap_injective
    (LinearMap.ext fun m ↦ (DGRightModuleCat.id_apply (classicalDGLocalSystem x L) m).symm)
  map_comp φ ψ := DGRightModuleHom.toLinearMap_injective
    (LinearMap.ext fun m ↦ (DGRightModuleCat.comp_apply (M := classicalDGLocalSystem x _)
      (N := classicalDGLocalSystem x _) (P := classicalDGLocalSystem x _)
      (classicalDGLocalSystemMap φ) (classicalDGLocalSystemMap ψ) m).symm)

@[simp]
theorem classicalDGLocalSystemFunctor_obj (L : LocalCoefficientSystem.{u, v, w} R X) :
    (classicalDGLocalSystemFunctor R x).obj L = classicalDGLocalSystem x L :=
  (rfl)

/-- **A morphism of local systems on a path-connected space is determined by the induced morphism of
DG local systems**: it is determined by its component at the basepoint, by transport along
paths. -/
theorem classicalDGLocalSystemMap_injective [PathConnectedSpace X]
    {L L' : LocalCoefficientSystem.{u, v, w} R X} {φ ψ : L ⟶ L'}
    (h : classicalDGLocalSystemMap (x := x) φ = classicalDGLocalSystemMap (x := x) ψ) : φ = ψ := by
  have hx : φ.app (FundamentalGroupoid.mk x) = ψ.app (FundamentalGroupoid.mk x) :=
    ModuleCat.hom_ext (LinearMap.ext fun m ↦ congrArg (fun f ↦ f.toLinearMap m) h)
  exact Groupoid.natTrans_ext (x₀ := FundamentalGroupoid.mk x)
    (fun y ↦ ⟨(⟦PathConnectedSpace.somePath x y.as⟧ : Path.Homotopic.Quotient x y.as)⟩) hx

end Action

end TauCeti
