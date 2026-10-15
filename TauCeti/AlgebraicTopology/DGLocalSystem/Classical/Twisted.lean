/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne
public import TauCeti.RingTheory.GradedAlgebra.Trivial

/-!
# Twisted complexes of classical local systems

Let `L` be a classical local system on a pointed space `(X, x)` and `L_x` its fiber.  The DG
local system `classicalDGLocalSystem x L` is `L_x` in degree zero with the zero differential, and
a chain of `C_*(Ω_x X; R)` acts on it through its degree-zero part in the group ring
`R[π₁(X, x)]`.  This file records that its twisted complexes only see this degree-zero
truncation.

The truncation `loopChainToGroupAlgebra` is a morphism of DG algebras from `C_*(Ω_x X; R)` to the
group ring, trivially graded with the zero differential
(`TauCeti.loopChainToGroupAlgebraDGAlgHom`).  The fiber `L_x` is a right module over the group
ring, a class acting by the monodromy of its inverse (`TauCeti.classicalGroupAlgebraAction`), and
the action of a chain is the action of its truncation (`TauCeti.op_loopChainToGroupAlgebra_smul`).
So for a twisting cocycle `m` with values in `C_*(Ω_x X; R)`, the twisted complex of
`classicalDGLocalSystem x L` with `m` is the twisted complex of `L_x` over `R[π₁(X, x)]` with the
truncated cocycle (`TauCeti.classicalTwistedCochainComplexIso`), through the identity of the
underlying modules, and likewise for their homology (`TauCeti.classicalTwistedHomologyIso`).
When the twisting cocycle comes from Morse or Floer trajectory data, as in the source, the
complex over the group ring is the Morse or Floer complex with coefficients in `L`. This file
works with an arbitrary twisting cocycle and does not construct that data. It also does not
compare these complexes with cubical chains with local coefficients.

## Main definitions

* `TauCeti.loopChainToGroupAlgebraDGAlgHom`: the degree-zero truncation as a morphism of DG
  algebras.
* `TauCeti.classicalGroupAlgebraAction`: the right action of the group ring on the fiber.
* `TauCeti.classicalTwistedCochainComplexIso`: the twisted complex of a classical local system is
  isomorphic to the twisted complex of its fiber over the group ring with the truncated cocycle.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4 and §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer,
  1978, Chapter VI, §1.
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w

section DGAlgHom

variable (X : Type u) [TopologicalSpace X] (x : X) (R : Type u) [CommRing R]

/-- **The degree-zero truncation as a morphism of DG algebras**: `loopChainToGroupAlgebra` from
`C_*(Ω_x X; R)` to the group ring `R[π₁(X, x)]`, trivially graded with the zero differential.  It
kills the chains of positive dimension and the boundaries. -/
def loopChainToGroupAlgebraDGAlgHom :
    DGAlgHom (loopChain_isDGAlgebra X x R)
      (isDGAlgebra_zero (trivialGrading R (MonoidAlgebra R (FundamentalGroup X x)))) where
  toAlgHom := loopChainToGroupAlgebra X x R
  map_mem {i a} ha := by
    by_cases hi : i = 0
    · rw [hi, trivialGrading_zero]
      exact Submodule.mem_top
    · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, loopChainToGroupAlgebra_eq_zero_of_mem hi ha]
      exact zero_mem _
  map_d' a := (LinearMap.zero_apply _).trans (loopChainToGroupAlgebra_differential a).symm

@[simp]
theorem loopChainToGroupAlgebraDGAlgHom_apply (a : loopChainAlgebra X x R) :
    loopChainToGroupAlgebraDGAlgHom X x R a = loopChainToGroupAlgebra X x R a :=
  (rfl)

end DGAlgHom

section Action

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {x : X}

/-- **The action of the group ring on the fiber of a local system**: the algebra map from the
opposite of `R[π₁(X, x)]` to the endomorphisms of the fiber at `x`, a class acting by the
monodromy of its inverse.  The action of the chain algebra, `classicalAction`, factors through
it. -/
def classicalGroupAlgebraAction (L : LocalCoefficientSystem.{u, u, w} R X) :
    (MonoidAlgebra R (FundamentalGroup X x))ᵐᵒᵖ →ₐ[R]
      Module.End R (L.obj (FundamentalGroupoid.mk x)) :=
  ((AlgEquiv.opOp R (Module.End R (L.obj (FundamentalGroupoid.mk x)))).symm :
      _ ≃ₐ[R] _).toAlgHom.comp
    (MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
      (FundamentalGroup X x) (LocalCoefficientSystem.fiberRightAction L)).op

theorem classicalGroupAlgebraAction_op_apply (L : LocalCoefficientSystem.{u, u, w} R X)
    (y : MonoidAlgebra R (FundamentalGroup X x)) :
    classicalGroupAlgebraAction L (op y) =
      (MonoidAlgebra.lift R (Module.End R (L.obj (FundamentalGroupoid.mk x)))ᵐᵒᵖ
        (FundamentalGroup X x) (LocalCoefficientSystem.fiberRightAction L) y).unop := by
  simp [classicalGroupAlgebraAction]

/-- The action of a chain on the fiber is the action of its degree-zero truncation. -/
theorem classicalAction_op_eq (L : LocalCoefficientSystem.{u, u, w} R X)
    (a : loopChainAlgebra X x R) :
    classicalAction L (op a) =
      classicalGroupAlgebraAction L (op (loopChainToGroupAlgebra X x R a)) := by
  rw [classicalAction_op_apply, classicalGroupAlgebraAction_op_apply]

/-- The right action of the group ring on the fiber of a classical local system. -/
instance instModuleGroupAlgebraOpFiber (L : LocalCoefficientSystem.{u, u, w} R X) :
    Module (MonoidAlgebra R (FundamentalGroup X x))ᵐᵒᵖ (L.obj (FundamentalGroupoid.mk x)) :=
  Module.compHom _ (classicalGroupAlgebraAction L).toRingHom

@[simp]
theorem op_smul_eq_classicalGroupAlgebraAction (L : LocalCoefficientSystem.{u, u, w} R X)
    (y : MonoidAlgebra R (FundamentalGroup X x)) (v : L.obj (FundamentalGroupoid.mk x)) :
    op y • v = classicalGroupAlgebraAction L (op y) v :=
  (rfl)

/-- The action of the group ring on the fiber is compatible with the `R`-module structure. -/
instance (L : LocalCoefficientSystem.{u, u, w} R X) :
    IsScalarTower R (MonoidAlgebra R (FundamentalGroup X x))ᵐᵒᵖ
      (L.obj (FundamentalGroupoid.mk x)) where
  smul_assoc r y v := congrArg (fun f ↦ f v) (map_smul (classicalGroupAlgebraAction L) r y)

/-- **A chain acts on the fiber as its degree-zero truncation.** -/
theorem op_loopChainToGroupAlgebra_smul (L : LocalCoefficientSystem.{u, u, w} R X)
    (a : loopChainAlgebra X x R) (v : L.obj (FundamentalGroupoid.mk x)) :
    op (loopChainToGroupAlgebra X x R a) • v = op a • v := by
  rw [op_smul_eq_classicalAction, classicalAction_op_eq, op_smul_eq_classicalGroupAlgebraAction]

/-- The fiber of a classical local system is a DG right module over the group ring, trivially
graded with the zero differential. -/
theorem isDGRightModule_fiber_groupAlgebra (L : LocalCoefficientSystem.{u, u, w} R X) :
    IsDGRightModule (isDGAlgebra_zero (trivialGrading R (MonoidAlgebra R (FundamentalGroup X x))))
      (trivialGrading R (L.obj (FundamentalGroupoid.mk x)))
      (0 : L.obj (FundamentalGroupoid.mk x) →ₗ[R] L.obj (FundamentalGroupoid.mk x)) :=
  isDGRightModule_zero _

/-- On the fiber, the twisted differential of a matrix of chains is the twisted differential of
its degree-zero truncation. -/
theorem twistedDifferential_loopChainToGroupAlgebra (L : LocalCoefficientSystem.{u, u, w} R X)
    {P : Type*} [Fintype P] (m : P → P → loopChainAlgebra X x R)
    (f : P → L.obj (FundamentalGroupoid.mk x)) :
    twistedDifferential (fun p q ↦ loopChainToGroupAlgebra X x R (m p q))
        (trivialGrading R (L.obj (FundamentalGroupoid.mk x))) 0 f =
      twistedDifferential m (trivialGrading R (L.obj (FundamentalGroupoid.mk x))) 0 f := by
  funext q
  simp only [twistedDifferential_apply, op_loopChainToGroupAlgebra_smul]

end Action

section Twisted

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {x : X}
  (L : LocalCoefficientSystem.{u, u, w} R X) {P : Type*} [Fintype P] {ind : P → ℤ}
  (m : LoopTwistingCocycle X x R P ind)

/-- The degree-`n` part of `classicalTwistedCochainComplexIso`. -/
def classicalTwistedCochainComplexXEquiv (n : ℤ) :
    (m.twistedCochainComplex 0 (isDGRightModule_fiber L)).X n ≃ₗ[R]
      ((m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twistedCochainComplex 0
        (isDGRightModule_fiber_groupAlgebra L)).X n :=
  (twistedCochainComplexXEquiv m.mem_graded m.twisting (isDGRightModule_fiber L) n).trans
    (twistedCochainComplexXEquiv (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).mem_graded
      (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twisting
      (isDGRightModule_fiber_groupAlgebra L) n).symm

/-- The degree-`n` identification is the identity of the underlying elements of `P → L_x`. -/
@[simp]
theorem twistedCochainComplexXEquiv_classicalTwistedCochainComplexXEquiv (n : ℤ)
    (g : (m.twistedCochainComplex 0 (isDGRightModule_fiber L)).X n) :
    (twistedCochainComplexXEquiv (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).mem_graded
        (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twisting
        (isDGRightModule_fiber_groupAlgebra L) n
        (classicalTwistedCochainComplexXEquiv L m n g) : P → L.obj (FundamentalGroupoid.mk x)) =
      twistedCochainComplexXEquiv m.mem_graded m.twisting (isDGRightModule_fiber L) n g := by
  simp [classicalTwistedCochainComplexXEquiv]

/-- **The twisted complex of a classical local system**: for a twisting cocycle `m` with values
in `C_*(Ω_x X; R)`, the twisted complex of `classicalDGLocalSystem x L` with `m` is the twisted
complex of the fiber `L_x`, as a module over `R[π₁(X, x)]`, with the cocycle truncated to degree
zero, through the identity of the underlying modules. -/
def classicalTwistedCochainComplexIso :
    m.twistedCochainComplex 0 (isDGRightModule_fiber L) ≅
      (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twistedCochainComplex 0
        (isDGRightModule_fiber_groupAlgebra L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (classicalTwistedCochainComplexXEquiv L m n).toModuleIso) fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      have hm : (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).m =
          fun p q ↦ loopChainToGroupAlgebra X x R (m.m p q) := by
        funext p q
        rw [TwistingCocycle.map_m, loopChainToGroupAlgebraDGAlgHom_apply]
      ext g
      apply (twistedCochainComplexXEquiv (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).mem_graded
        (m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twisting
        (isDGRightModule_fiber_groupAlgebra L) (i + 1)).injective
      apply Subtype.ext
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_hom,
        ModuleCat.hom_ofHom, LinearEquiv.coe_coe]
      rw [twistedCochainComplexXEquiv_classicalTwistedCochainComplexXEquiv,
        twistedCochainComplexXEquiv_d, twistedCochainComplexXEquiv_d,
        twistedCochainComplexXEquiv_classicalTwistedCochainComplexXEquiv, hm,
        twistedDifferential_loopChainToGroupAlgebra]

/-- The isomorphism of twisted complexes is the degreewise identification. -/
@[simp]
theorem classicalTwistedCochainComplexIso_hom_f_apply (n : ℤ)
    (g : (m.twistedCochainComplex 0 (isDGRightModule_fiber L)).X n) :
    ((classicalTwistedCochainComplexIso L m).hom.f n).hom g =
      classicalTwistedCochainComplexXEquiv L m n g := by
  simp only [classicalTwistedCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

/-- The inverse isomorphism of twisted complexes is the inverse degreewise identification. -/
@[simp]
theorem classicalTwistedCochainComplexIso_inv_f_apply (n : ℤ)
    (g : ((m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twistedCochainComplex 0
      (isDGRightModule_fiber_groupAlgebra L)).X n) :
    ((classicalTwistedCochainComplexIso L m).inv.f n).hom g =
      (classicalTwistedCochainComplexXEquiv L m n).symm g := by
  simp only [classicalTwistedCochainComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    LinearEquiv.toModuleIso_inv, ModuleCat.hom_ofHom, LinearEquiv.coe_coe]

/-- The homology of the twisted complex of a classical local system is the homology of the
twisted complex of its fiber over the group ring with the truncated cocycle. -/
def classicalTwistedHomologyIso (q : ℤ) :
    (m.twistedCochainComplex 0 (isDGRightModule_fiber L)).homology q ≅
      ((m.map (loopChainToGroupAlgebraDGAlgHom X x R)).twistedCochainComplex 0
        (isDGRightModule_fiber_groupAlgebra L)).homology q :=
  (HomologicalComplex.homologyFunctor _ _ q).mapIso (classicalTwistedCochainComplexIso L m)

end Twisted

end TauCeti
