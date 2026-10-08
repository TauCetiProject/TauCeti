/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Basic
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.CoordinateBaseChange

/-!
# Base change of symplectic root subgroups

The canonical coordinate-Hopf-algebra identifications for `Sp₂ₘ` and `𝔾ₐ` carry
scalar extension of every normalized symplectic root map to the root map constructed
over the new base. This includes both long-root families and all three short-root
families. In particular, the integral root maps retain their parameter and signs in
positive characteristic and over nonreduced rings. No flatness assumption is needed.

This supplies the root-map compatibility used when transporting symplectic pinnings
between bases. The calculation uses `rootSubgroupCoordinateMap_apply_X` and
`RootSubgroupIndex.map_tangentMatrix`, so there is no new presentation of the root maps.
It follows the quotient-cancellation construction in
`SpecialLinear.RootSubgroup.BaseChange` and the coordinate calculation in
`GeneralLinear.Root.BaseChange`.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §§21 and 24.6.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.Symplectic

universe u v

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable {m : ℕ}

/-- Every normalized symplectic root map commutes with arbitrary base extension,
under the canonical coordinate-algebra identifications of `Sp₂ₘ` and `𝔾ₐ`. -/
-- Instantiate the ring arguments when rewriting: the extension ring has a `max` universe.
@[reassoc]
theorem baseChangeMap_rootSubgroupCoordinateMap_comp_baseChangeIso_hom
    (root : GLSymplecticFin.RootSubgroupIndex m) :
    CommHopfAlgCat.baseChangeMap (K := K) (rootSubgroupCoordinateMap (R := R) root) ≫
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso R K).hom =
      (coordinateHopfAlgebraBaseChangeIso R K m).hom ≫
        rootSubgroupCoordinateMap (R := K) root := by
  let q := CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R m)
  let : Epi q := ConcreteCategory.epi_of_surjective q
    (CommHopfAlgCat.baseChangeMap_surjective (coordinateMap R m)
      (by
        rw [coordinateMap_def]
        exact CommHopfAlgCat.mkQuotient_surjective _ _))
  apply (cancel_epi q).mp
  dsimp only [q]
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (k := R) (K := K)).map_comp,
    ← Category.assoc (CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R m)),
    baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom,
    Category.assoc]
  apply (cancel_epi (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K (m + m)).inv).mp
  apply _root_.CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext K (m + m)
  intro a b
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
  simp only [BialgHom.coe_toAlgHom, Iso.inv_hom_id_assoc]
  rw [GeneralLinear.coordinateHopfAlgebraBaseChangeMap_X]
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp, Function.comp_apply]
  rw [rootSubgroupCoordinateMap_apply_X, rootSubgroupCoordinateMap_apply_X]
  let f : AdditiveGroup.coordinateHopfAlgebra R →+* AdditiveGroup.coordinateHopfAlgebra K :=
    RingHom.comp
      (AlgHom.restrictScalars R
        (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso R K).hom.hom.toAlgHom).toRingHom
      Algebra.TensorProduct.includeRight.toRingHom
  have hf (x : AdditiveGroup.coordinateHopfAlgebra R) :
      f x = (AdditiveGroup.coordinateHopfAlgebraBaseChangeIso R K).hom.hom (1 ⊗ₜ[R] x) := rfl
  have hcoord : f (SymmetricAlgebra.ι R R 1) = SymmetricAlgebra.ι K K 1 := by
    simp [f, AdditiveGroup.coordinateHopfAlgebraBaseChangeIso, _root_.CommHopfAlgCat.isoMk_hom]
  have hmatrix : (1 + root.tangentMatrix (SymmetricAlgebra.ι R R 1)).map f =
      1 + root.tangentMatrix (SymmetricAlgebra.ι K K 1) := by
    rw [Matrix.map_add f f.map_add, Matrix.map_one f f.map_zero f.map_one]
    exact congrArg (1 + ·) ((root.map_tangentMatrix f.toAddMonoidHom
      (SymmetricAlgebra.ι R R 1)).trans (congrArg root.tangentMatrix hcoord))
  exact (hf _).symm.trans (congrFun (congrFun hmatrix a) b)

end TauCeti.Symplectic
