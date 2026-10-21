/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.GraphAutomorphism
public import TauCeti.Algebra.AlgebraicGroup.SpecialLinear.DiagonalTorus.Basic
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Relabel

/-!
# The type-A graph automorphism on the standard torus

The signed reverse inverse transpose automorphism of `SL_{r+1}` preserves its chosen
diagonal torus. In fundamental-weight coordinates it reverses the `r` coordinates.
Together with the existing equations on the numbered simple-root subgroups, this
gives the torus and root-subgroup parts of the standard pinning calculation.

The calculation works over every commutative base ring, including nonreduced rings.
It uses the matrix identity `TauCeti.typeAGraphAutomorphism_diagGL` and the standard
weights of `TauCeti.SlStd`.

## References

* R. W. Carter, *Finite Groups of Lie Type*, §1.15.
* R. Steinberg, *Lectures on Chevalley Groups*, §10.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.SpecialLinear

universe u w

variable (r : ℕ) (R : Type u) [CommRing R]

/-- Reversal of the fundamental-weight indices, transported to the lifted index type
used by the split torus. -/
def diagonalTorusRevPerm : Equiv.Perm (ULift.{u} (Fin r)) :=
  (Equiv.ulift.trans Fin.revPerm).trans Equiv.ulift.symm

@[simp]
theorem diagonalTorusRevPerm_apply (i : ULift.{u} (Fin r)) :
    diagonalTorusRevPerm r i = ULift.up i.down.rev := by
  simp [diagonalTorusRevPerm]

@[simp]
theorem diagonalTorusRevPerm_symm_apply (i : ULift.{u} (Fin r)) :
    (diagonalTorusRevPerm r).symm i = ULift.up i.down.rev := by
  simp [diagonalTorusRevPerm, Fin.revPerm_symm]

/-- The graph automorphism acts on the standard diagonal torus by reversing its
fundamental-weight coordinates. This equality holds on points over every `R`-algebra. -/
@[simp]
theorem typeAGraphAutomorphism_diagonalTorusPoints
    (A : Type w) [CommRing A] [Algebra R A]
    (p : WithConv (MonoidAlgebra R
      (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) →ₐ[R] A)) :
    Matrix.SpecialLinearGroup.typeAGraphAutomorphism r A
        (pointsMulEquiv (R := R) (A := A) (r + 1) (diagonalTorusPoints r R A p)) =
      pointsMulEquiv (R := R) (A := A) (r + 1)
        (diagonalTorusPoints r R A
          ((SplitTorus.pointsMulEquiv (R := R) (A := CommAlgCat.of R A)).symm
            (fun i : ULift.{u} (Fin r) =>
              SplitTorus.pointsMulEquiv p (ULift.up i.down.rev)))) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [Matrix.SpecialLinearGroup.toGL_typeAGraphAutomorphism,
    toGL_pointsMulEquiv_diagonalTorusPoints,
    TauCeti.typeAGraphAutomorphism_diagGL,
    toGL_pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext k
  let s := SplitTorus.pointsMulEquiv p
  have hs : (fun i : ULift.{u} (Fin r) => s (ULift.up i.down.rev)) =
      MulEquiv.arrowCongr (diagonalTorusRevPerm r) (MulEquiv.refl Aˣ) s := by
    funext i
    simp
  rw [MulEquiv.apply_symm_apply, hs, torusCharacter_mulEquivArrowCongr,
    ← torusCharacter_neg]
  congr 1
  funext i
  simpa only [Pi.neg_apply, Function.comp_apply, diagonalTorusRevPerm_apply,
    diagonalTorusWeight_apply, Fin.rev_rev] using (SlStd.weight_rev_rev r k.rev i.down).symm

/-- The coordinate graph automorphism restricts to reversal of the standard
diagonal torus. This is an equality of Hopf-algebra maps over the base ring. -/
@[reassoc (attr := simp)]
theorem typeAGraphCoordinateIso_hom_comp_diagonalTorusCoordinateMap :
    (typeAGraphCoordinateIso R r).hom ≫ diagonalTorusCoordinateMap r R =
      diagonalTorusCoordinateMap r R ≫
        SplitTorus.relabelCoordinateMap R (diagonalTorusRevPerm r) := by
  apply Quiver.Hom.op_inj
  apply (CommHopfAlgCat.pointsFunctor (R := R)).map_injective
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  ext A p
  -- The represented point-functor maps are precomposition by coordinate morphisms.
  -- `ext` exposes a point through the `WithConv` wrapper, while the point API is
  -- stated using the underlying algebra homomorphism. There is no named extensionality
  -- bridge for this coercion; the following `change` only unfolds that wrapper.
  change WithConv (MonoidAlgebra R
    (Multiplicative (ULift.{u} (Fin r) →₀ ℤ)) →ₐ[R] A) at p
  apply (pointsMulEquiv (R := R) (A := A) (r + 1)).injective
  let q := BialgHom.mapDomain (SplitTorus.relabelCoordinateMap R
    (diagonalTorusRevPerm r)).hom p
  have hq : q = (SplitTorus.pointsMulEquiv (R := R) (A := A)).symm
      (fun i : ULift.{u} (Fin r) =>
        SplitTorus.pointsMulEquiv p (ULift.up i.down.rev)) := by
    apply (SplitTorus.pointsMulEquiv (R := R) (A := A)).injective
    funext i
    simpa only [q, BialgHom.mapDomain_apply, WithConv.ofConv_toConv,
      diagonalTorusRevPerm_apply, MulEquiv.apply_symm_apply] using
      SplitTorus.pointsMulEquiv_mapDomain_relabelCoordinateMap
        (R := R) (A := A) (τ := diagonalTorusRevPerm r) p i
  -- After the functorial composites are read as precomposition, the claim is
  -- exactly the point-level diagonal-torus calculation above.
  rw [NatTrans.comp_app, NatTrans.comp_app]
  erw [GrpCat.comp_apply, GrpCat.comp_apply]
  -- `CommHopfAlgCat.Hom.mapPointsFunctor_app_apply` is the interface lemma for each map
  -- separately, but
  -- does not normalize their composite through `GrpCat`'s coercions. State that
  -- composite in the point API's form so the four applications below can use the
  -- interface lemma explicitly.
  change pointsMulEquiv (R := R) (A := A) (r + 1)
      ((CommHopfAlgCat.Hom.mapPointsFunctor (typeAGraphCoordinateIso R r).hom).app A
        ((CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app A p)) =
    pointsMulEquiv (R := R) (A := A) (r + 1)
      ((CommHopfAlgCat.Hom.mapPointsFunctor (diagonalTorusCoordinateMap r R)).app A
        ((CommHopfAlgCat.Hom.mapPointsFunctor
          (SplitTorus.relabelCoordinateMap R (diagonalTorusRevPerm r))).app A p))
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
    CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  rw [pointsMulEquiv_comp_typeAGraphCoordinateIso]
  have hleft : toConv (p.ofConv.comp (diagonalTorusCoordinateMap r R).hom.toAlgHom) =
      diagonalTorusPoints r R A p :=
    (CommHopfAlgCat.Hom.mapPointsFunctor_app_apply (diagonalTorusCoordinateMap r R) A p).symm.trans
      (diagonalTorusPoints_apply r R A p).symm
  have hright :
      toConv ((p.ofConv.comp (SplitTorus.relabelCoordinateMap R
        (diagonalTorusRevPerm r)).hom.toAlgHom).comp
          (diagonalTorusCoordinateMap r R).hom.toAlgHom) =
        diagonalTorusPoints r R A q := by
    rw [diagonalTorusPoints_apply,
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
    simp only [q, BialgHom.mapDomain_apply, ofConv_toConv]
  rw [hleft, hright, hq]
  exact typeAGraphAutomorphism_diagonalTorusPoints r R A p

end TauCeti.SpecialLinear
