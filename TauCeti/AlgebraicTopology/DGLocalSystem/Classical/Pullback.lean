/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.Classical.Basic
public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.Algebra.MonoidAlgebra.MapDomain

/-!
# Pullback of classical local systems as DG local systems

For a based map `f : (X, x) → (Y, f x)` and a classical local system `L` on `Y`, the DG local
system of the pullback `f^* L` is the pullback of the DG local system of `L`, that is, the
restriction of scalars of the fiber `L_{f x}` along `C_*(Ωf) : C_*(Ω_x X) → C_*(Ω_{f x} Y)`.
Both have the fiber `(f^* L)_x = L_{f x}` as carrier, in degree zero with the zero differential,
and the two actions of `C_*(Ω_x X; R)` agree: a chain acts on `(f^* L)_x` through its degree-zero
part in `R[π₁(X, x)]` and the monodromy of `f^* L`, which is the monodromy of `L` along `π₁(f)`,
while it acts on the restriction through `C_*(Ωf)`, whose degree-zero part is the image under
`π₁(f)` (`loopChainToGroupAlgebra_loopChainMap`).

## Main definitions

* `TauCeti.classicalDGLocalSystemPullbackEquiv`: the identity of the fiber `(f^* L)_x = L_{f x}`,
  as a linear equivalence over `C_*(Ω_x X; R)ᵐᵒᵖ` onto the restricted fiber.
* `TauCeti.classicalDGLocalSystemPullbackIso`: the isomorphism
  `classicalDGLocalSystem x (f^* L) ≅ (DGLocalSystem.pullback R f rfl).obj
  (classicalDGLocalSystem (f x) L)`, the identity on the underlying fiber.
* `TauCeti.classicalDGLocalSystemPullbackIsoOfEq`: the same for a basepoint equation `f x = y`.
* `TauCeti.classicalDGLocalSystemFunctorPullbackIso`: the naturality of
  `classicalDGLocalSystemPullbackIso` in `L`, as an isomorphism
  of functors `f^* ⋙ classicalDGLocalSystemFunctor R x ≅
  classicalDGLocalSystemFunctor R (f x) ⋙ DGLocalSystem.pullback R f rfl`.

## Main results

* `TauCeti.classicalAction_pullback`: the action of a chain on the fiber of `f^* L` is the action
  of its image under `C_*(Ωf)` on the fiber of `L`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 2 and 7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definition 1.8.
* G. W. Whitehead, *Elements of Homotopy Theory*, Graduate Texts in Mathematics 61, Springer,
  1978, Chapter VI, Section 1 ("Bundles of Groups": local systems and their pullbacks).
-/

public section

noncomputable section

open CategoryTheory MulOpposite

namespace TauCeti

universe u w

variable {R : Type u} [CommRing R] {X Y : TopCat.{u}}

/-- **The action on the fiber of a pullback**: a chain of `C_*(Ω_x X; R)` acts on the fiber of
`f^* L` as its image under `C_*(Ωf)` acts on the fiber of `L` at `f x`. -/
theorem classicalAction_pullback (f : C(X, Y)) {x : X} (L : LocalCoefficientSystem.{u, u, w} R Y)
    (a : loopChainAlgebra X x R) :
    classicalAction (x := x) ((LocalCoefficientSystem.pullback (R := R) f).obj L) (op a) =
      classicalAction (x := f x) L (op (loopChainMap R f rfl a)) := by
  rw [classicalAction_op_apply, classicalAction_op_apply, loopChainToGroupAlgebra_loopChainMap,
    FundamentalGroup.mapOfEq_rfl, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.lift_mapDomain]
  -- The fibers `(f^* L)_x` and `L_{f x}` agree only up to unfolding, so the two right actions are
  -- compared as a term rather than by rewriting.
  refine congrArg (fun F ↦ unop (MonoidAlgebra.lift R
    (Module.End R (L.obj (FundamentalGroupoid.mk (f x))))ᵐᵒᵖ (FundamentalGroup X x) F
      (loopChainToGroupAlgebra X x R a))) (MonoidHom.ext fun g ↦ ?_)
  exact (LocalCoefficientSystem.fiberRightAction_apply _ g).trans
    ((congrArg op (congrArg (LocalCoefficientSystem.monodromyRepresentation L (f x))
      (map_inv (FundamentalGroup.map f x) g))).trans
        (LocalCoefficientSystem.fiberRightAction_apply L _).symm)

variable (R) in
/-- The identity of the fiber `(f^* L)_x = L_{f x}`, as a linear equivalence over the opposite of
`C_*(Ω_x X; R)` onto the restriction of scalars of the fiber of `L` along `C_*(Ωf)`. -/
def classicalDGLocalSystemPullbackEquiv (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y) :
    classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L) ≃ₗ[
      (loopChainAlgebra X x R)ᵐᵒᵖ]
      (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L) where
  toFun := (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
    (classicalDGLocalSystem (f x) L)).symm
  invFun := DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
    (classicalDGLocalSystem (f x) L)
  map_add' := map_add _
  map_smul' a m := (DGRightModuleCat.restrictScalarsEquiv _ _).injective (by
    rw [DGRightModuleCat.restrictScalarsEquiv_smul, RingHom.id_apply]
    -- The fibers `(f^* L)_x` and `L_{f x}` agree only up to unfolding, so the equation is
    -- assembled as a term rather than by rewriting.
    exact ((DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
      (classicalDGLocalSystem (f x) L)).apply_symm_apply _).trans
        ((LinearMap.congr_fun (classicalAction_pullback f L a.unop) m).trans
          (congrArg (op (loopChainMap R f rfl a.unop) • ·)
            ((DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
              (classicalDGLocalSystem (f x) L)).apply_symm_apply m).symm)))
  left_inv := (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
    (classicalDGLocalSystem (f x) L)).apply_symm_apply
  right_inv := (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
    (classicalDGLocalSystem (f x) L)).symm_apply_apply

/-- The underlying element of the image of `m` under `classicalDGLocalSystemPullbackEquiv` is
`m` itself. -/
@[simp]
theorem restrictScalarsEquiv_classicalDGLocalSystemPullbackEquiv (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y)
    (m : classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L)) :
    DGRightModuleCat.restrictScalarsEquiv _ _ (classicalDGLocalSystemPullbackEquiv R f x L m) = m :=
  (DGRightModuleCat.restrictScalarsEquiv (loopChainMap R f rfl)
    (classicalDGLocalSystem (f x) L)).apply_symm_apply m

/-- The inverse of `classicalDGLocalSystemPullbackEquiv` takes the underlying element. -/
@[simp]
theorem classicalDGLocalSystemPullbackEquiv_symm_apply (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y)
    (m : (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L)) :
    (classicalDGLocalSystemPullbackEquiv R f x L).symm m =
      DGRightModuleCat.restrictScalarsEquiv _ _ m :=
  (rfl)

variable (R) in
/-- **The DG local system of a pullback is the pullback of the DG local system**: for a based map
`f : (X, x) → (Y, f x)` and a local system `L` on `Y`, the identity of the fiber
`(f^* L)_x = L_{f x}` is an isomorphism from the DG local system of `f^* L` to the restriction of
scalars of that of `L` along `C_*(Ωf)`. -/
def classicalDGLocalSystemPullbackIso (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y) :
    classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L) ≅
      (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L) :=
  DGRightModuleCat.isoMk
    (M := classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L))
    (N := (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L))
    (classicalDGLocalSystemPullbackEquiv R f x L)
    (fun q m ↦ by
      rw [DGRightModuleCat.mem_restrictScalars_obj_grading,
        restrictScalarsEquiv_classicalDGLocalSystemPullbackEquiv, classicalDGLocalSystem_grading,
        classicalDGLocalSystem_grading]
      exact Iff.rfl)
    (fun m ↦ (DGRightModuleCat.restrictScalarsEquiv _ _).injective (by
      rw [DGRightModuleCat.restrictScalarsEquiv_differential,
        restrictScalarsEquiv_classicalDGLocalSystemPullbackEquiv,
        restrictScalarsEquiv_classicalDGLocalSystemPullbackEquiv,
        classicalDGLocalSystem_differential, classicalDGLocalSystem_differential,
        LinearMap.zero_apply]
      rfl))

/-- The isomorphism `classicalDGLocalSystemPullbackIso` acts by
`classicalDGLocalSystemPullbackEquiv`. -/
@[simp]
theorem classicalDGLocalSystemPullbackIso_hom_apply (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y)
    (m : classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L)) :
    (classicalDGLocalSystemPullbackIso R f x L).hom m =
      classicalDGLocalSystemPullbackEquiv R f x L m := by
  rw [classicalDGLocalSystemPullbackIso, DGRightModuleCat.isoMk_hom_apply]

/-- The inverse of `classicalDGLocalSystemPullbackIso` acts by the inverse of
`classicalDGLocalSystemPullbackEquiv`. -/
@[simp]
theorem classicalDGLocalSystemPullbackIso_inv_apply (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y)
    (m : (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L)) :
    (classicalDGLocalSystemPullbackIso R f x L).inv m =
      (classicalDGLocalSystemPullbackEquiv R f x L).symm m := by
  rw [classicalDGLocalSystemPullbackIso, DGRightModuleCat.isoMk_inv_apply]

variable (R) in
/-- `classicalDGLocalSystemPullbackIso` for a based map `f : (X, x) → (Y, y)` with an arbitrary
basepoint equation `f x = y`. -/
def classicalDGLocalSystemPullbackIsoOfEq (f : C(X, Y)) {x : X} {y : Y} (hf : f x = y)
    (L : LocalCoefficientSystem.{u, u, w} R Y) :
    classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L) ≅
      (DGLocalSystem.pullback R f hf).obj (classicalDGLocalSystem y L) := by
  subst hf
  exact classicalDGLocalSystemPullbackIso R f x L

/-- Along the reflexivity proof, `classicalDGLocalSystemPullbackIsoOfEq` is
`classicalDGLocalSystemPullbackIso`. -/
@[simp]
theorem classicalDGLocalSystemPullbackIsoOfEq_rfl (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y) :
    classicalDGLocalSystemPullbackIsoOfEq R f (rfl : f x = f x) L =
      classicalDGLocalSystemPullbackIso R f x L :=
  (rfl)

/-- Naturality of `classicalDGLocalSystemPullbackIso` in the local system. -/
theorem classicalDGLocalSystemPullbackIso_hom_naturality (f : C(X, Y)) (x : X)
    {L L' : LocalCoefficientSystem.{u, u, w} R Y} (φ : L ⟶ L') :
    classicalDGLocalSystemMap (x := x) ((LocalCoefficientSystem.pullback (R := R) f).map φ) ≫
        (classicalDGLocalSystemPullbackIso R f x L').hom =
      (classicalDGLocalSystemPullbackIso R f x L).hom ≫
        (DGLocalSystem.pullback R f rfl).map (classicalDGLocalSystemMap φ) := by
  -- `ext` finds no extensionality lemma here (as in `classicalDGLocalSystemFunctor`), so the
  -- objects are named explicitly.
  refine DGRightModuleCat.hom_ext
    (M := classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L))
    (N := (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L')) fun m ↦ ?_
  rw [DGRightModuleCat.comp_apply]
  refine (DGRightModuleCat.comp_apply
    (M := classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L))
    (N := classicalDGLocalSystem x ((LocalCoefficientSystem.pullback (R := R) f).obj L'))
    (P := (DGLocalSystem.pullback R f rfl).obj (classicalDGLocalSystem (f x) L'))
    (classicalDGLocalSystemMap _) _ m).trans
      ((DGRightModuleCat.restrictScalarsEquiv _ _).injective ?_)
  -- The fibers of `f^* L` and `L` agree only up to unfolding, so the equation is assembled as a
  -- term rather than by rewriting.
  have hL := (congrArg _ (classicalDGLocalSystemPullbackIso_hom_apply f x L m)).trans
    (restrictScalarsEquiv_classicalDGLocalSystemPullbackEquiv f x L m)
  have hL' := (congrArg _ (classicalDGLocalSystemPullbackIso_hom_apply f x L'
    (classicalDGLocalSystemMap ((LocalCoefficientSystem.pullback (R := R) f).map φ) m))).trans
      (restrictScalarsEquiv_classicalDGLocalSystemPullbackEquiv f x L' _)
  exact hL'.trans ((classicalDGLocalSystemMap_apply _ m).trans
    ((classicalDGLocalSystemMap_apply φ m).symm.trans
      ((DGRightModuleCat.restrictScalars_map_apply (loopChainMap R f rfl)
        (M := classicalDGLocalSystem (f x) L) (N := classicalDGLocalSystem (f x) L')
        (classicalDGLocalSystemMap φ) ((classicalDGLocalSystemPullbackIso R f x L).hom m)).trans
          (congrArg (classicalDGLocalSystemMap φ) hL)).symm))

variable (R) in
/-- **Naturality of `classicalDGLocalSystemPullbackIso` in the local system**: for a based map
`f : (X, x) → (Y, f x)`, taking DG local systems commutes with pulling back along `f`, up to the
identity of the fibers. -/
def classicalDGLocalSystemFunctorPullbackIso (f : C(X, Y)) (x : X) :
    LocalCoefficientSystem.pullback (R := R) f ⋙ classicalDGLocalSystemFunctor.{u, w} R x ≅
      classicalDGLocalSystemFunctor R (f x) ⋙ DGLocalSystem.pullback R f rfl :=
  NatIso.ofComponents (classicalDGLocalSystemPullbackIso R f x) fun φ ↦
    classicalDGLocalSystemPullbackIso_hom_naturality f x φ

/-- The component of `classicalDGLocalSystemFunctorPullbackIso` at `L`. -/
@[simp]
theorem classicalDGLocalSystemFunctorPullbackIso_app (f : C(X, Y)) (x : X)
    (L : LocalCoefficientSystem.{u, u, w} R Y) :
    (classicalDGLocalSystemFunctorPullbackIso R f x).app L =
      classicalDGLocalSystemPullbackIso R f x L :=
  (rfl)

end TauCeti
