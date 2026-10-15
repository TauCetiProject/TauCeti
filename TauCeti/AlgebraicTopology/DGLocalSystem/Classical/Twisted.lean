/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.AlgebraicTopology.DGLocalSystem.RankOne

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

The truncation `loopChainToGroupAlgebraDGAlgHom` lives in `DGLocalSystem/LoopAlgebra.lean`, and
the action `classicalGroupAlgebraAction` in `DGLocalSystem/Classical/Basic.lean`.

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

section Action

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {x : X}

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
