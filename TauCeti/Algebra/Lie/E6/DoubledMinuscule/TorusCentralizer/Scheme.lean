/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.MaximalTorus
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.StandardComodule
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer
import TauCeti.Algebra.Lie.E6.DoubledMinuscule.PointsFunctor

/-!
# Schematic self-centralization of the doubled E₆ weight torus

The rank-six weight torus of the integral doubled minuscule carrier is its own schematic
centralizer, after specialization to any commutative base ring. The point statement tests every
commutative value algebra, not just rational points over infinite fields. Equality of the defining
ideals therefore includes infinitesimal structure, even in characteristics two and three.

Distinct weight characters force a centralizing matrix to be diagonal. The all-ring diagonal
criterion of `TauCeti.E6DoubledMinuscule.mem_range_weightTorusPoints_iff_isDiag`, obtained from the
invariant cross product, then recovers its torus parameter. This supplies schematic torus
recognition for the explicit carrier, not an identification with the pinned simply connected
group scheme of type E₆. Constructions transfer to that pinned group only along such an
identification once proved. No equality with the separately ground-ring-generated carrier is
asserted.

## Main results

* `centralizerPointsSubgroup_eq_range_weightTorus`: the centralizer is the torus on all value
  algebras, including finite and nonreduced ones.
* `centralizerHopfIdeal_weightTorus_toIdeal_eq_ker`: the centralizer's defining ideal is the
  kernel of restriction to the weight torus.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§16 and 26.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 3 and 17.
* The schematic diagonalization uses the method of
  `TauCeti.Algebra.Lie.E7.Minuscule.Generated.TorusCentralizer`; the diagonal-intersection
  calculation is the doubled carrier's existing invariant-cross-product construction.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.E6DoubledMinuscule

universe u v

variable (R : Type u) [CommRing R]

private theorem torus_comp_coordinateMap :
    (weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom =
      GeneralLinear.weightTorusCoordinateBialgHom (S := R) matrixWeight := by
  rw [← CommHopfAlgCat.hom_comp, coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

private theorem centralizer_iff_isDiag (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := coordinateHopfAlgebra R) A) :
    g ∈ BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap R).hom A ↔
      (GeneralLinear.pointsMulEquiv 54 (BialgHom.mapDomain (coordinateMap R).hom g) :
        Matrix (Fin 54) (Fin 54) A).IsDiag := by
  have hwt : Function.Injective matrixWeight := by
    intro a b h
    apply minusculeCharacter_injective
    exact congrArg SplitTorus.weightCharacter h
  have h := BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (coordinateMap R).hom (coordinateMap_surjective R)
    (weightTorusToBaseChangeCoordinateMap R).hom g
  rw [torus_comp_coordinateMap,
    GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag _ hwt] at h
  rw [BialgHom.centralizerPointsSubgroup, CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  simpa only [IsConcreteLE.le_iff, RingHom.mem_ker, HopfIdeal.mem_toIdeal] using h.symm

-- The matrix formula uses the direct bialgebra presentation, allowing independent universes
-- for the coefficient ring, value algebra and finite weight indices.
private theorem torus_matrix (A : CommAlgCat.{v} R)
    (q : HopfAlgebra.points (R := R)
      (H := (DiagonalizableGroup.coordinateRing R
        (SplitTorus.characterGroup (Fin 6))).obj) A) :
    GeneralLinear.pointsMulEquiv 54
        (BialgHom.mapDomain (coordinateMap R).hom
          (BialgHom.mapDomain (weightTorusToBaseChangeCoordinateMap R).hom q)) =
      (weightTorusPoints A (SplitTorus.pointsMulEquiv q) :
        Matrix.GeneralLinearGroup (Fin 54) A) := by
  have he : BialgHom.mapDomain (coordinateMap R).hom
        (BialgHom.mapDomain (weightTorusToBaseChangeCoordinateMap R).hom q) =
      BialgHom.mapDomain
        ((weightTorusToBaseChangeCoordinateMap R).hom.comp (coordinateMap R).hom) q := by
    simp only [BialgHom.mapDomain_apply, BialgHom.comp_toAlgHom, AlgHom.comp_assoc]
  rw [he, torus_comp_coordinateMap]
  apply Units.ext
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe,
    GeneralLinear.pointsMulEquiv_apply, BialgHom.mapDomain_apply,
    GeneralLinear.weightTorusCoordinateBialgHom_def,
    DiagonalizableGroup.pointToGeneralLinear_comp_diagonalCoordinateMap]
  congr 1
  funext i
  exact congrArg (fun s : Aˣ ↦ (s : A))
    (SplitTorus.charOfPoint_weightCharacter q (matrixWeight i))

/-- Over every value algebra, the schematic centralizer of the doubled E₆ weight torus is
exactly the image of that torus. This tests extensions of the value algebra, rather than only
commutation with its rational torus points. -/
theorem centralizerPointsSubgroup_eq_range_weightTorus (A : CommAlgCat.{v} R) :
    BialgHom.centralizerPointsSubgroup (weightTorusToBaseChangeCoordinateMap R).hom A =
      (BialgHom.mapDomain (weightTorusToBaseChangeCoordinateMap R).hom).range := by
  ext g
  rw [centralizer_iff_isDiag, MonoidHom.mem_range]
  constructor
  · intro hg
    let p := (pointsPresentation A).mulEquiv
      (CommHopfAlgCat.baseChangeIsoPointsMulEquiv (baseChangeCoordinateIso R) A g)
    have hp : (p : Matrix.GeneralLinearGroup (Fin 54) A) =
        GeneralLinear.pointsMulEquiv 54 (BialgHom.mapDomain (coordinateMap R).hom g) := by
      rw [GeneralLinear.IntegralPointsPresentation.coe_mulEquiv_apply,
        BialgHom.mapDomain_apply, ← CommHopfAlgCat.Hom.mapPointsFunctor_app_apply,
        mapPointsFunctor_coordinateMap_app]
      exact GeneralLinear.pointsMulEquiv_quotientPointsHom_baseChangeIsoPointsMulEquiv
        54 definingIdeal (baseChangeDefiningIdeal R) (baseChangeCoordinateIso R)
        (mkQuotient_comp_baseChangeCoordinateIso_hom R) A g
    have hpdiag : ((p : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A).IsDiag := by
      rw [hp]
      exact hg
    obtain ⟨s, hs⟩ := (mem_range_weightTorusPoints_iff_isDiag p).mpr hpdiag
    refine ⟨(SplitTorus.pointsMulEquiv (R := R) (A := A)).symm s, ?_⟩
    apply BialgHom.mapDomain_injective_of_surjective _ (coordinateMap_surjective R)
    apply (GeneralLinear.pointsMulEquiv 54).injective
    rw [torus_matrix, MulEquiv.apply_symm_apply, ← hp]
    exact congrArg Subtype.val hs
  · rintro ⟨q, rfl⟩
    rw [torus_matrix, coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply,
      diagGL_coe]
    exact Matrix.isDiag_diagonal _

/-- The schematic centralizer of the doubled E₆ weight torus is cut out by the kernel of
restriction to the torus. This is equality of ideals, not merely equality of geometric points;
no reducedness, flatness or field hypothesis is required. -/
theorem centralizerHopfIdeal_weightTorus_toIdeal_eq_ker :
    (BialgHom.centralizerHopfIdeal (weightTorusToBaseChangeCoordinateMap R).hom).toIdeal =
      RingHom.ker (weightTorusToBaseChangeCoordinateMap R).hom := by
  let π := (weightTorusToBaseChangeCoordinateMap R).hom
  let I := BialgHom.centralizerHopfIdeal π
  apply le_antisymm
  · have hmem : toConv π.toAlgHom ∈ BialgHom.centralizerPointsSubgroup π
        (CommAlgCat.of R (DiagonalizableGroup.coordinateRing R
          (SplitTorus.characterGroup (Fin 6))).obj) := by
      rw [centralizerPointsSubgroup_eq_range_weightTorus]
      refine ⟨toConv (AlgHom.id R _), ?_⟩
      simp only [BialgHom.mapDomain_apply, AlgHom.id_comp, π]
    exact (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp hmem
  -- Test the universal centralizer point to recover the actual ideal, not just its radical.
  · let A := CommAlgCat.of R (CommHopfAlgCat.quotient (coordinateHopfAlgebra R) I)
    let g := CommHopfAlgCat.quotientPointsHom (coordinateHopfAlgebra R) I A
      (toConv (AlgHom.id R _))
    have hg : g ∈ BialgHom.centralizerPointsSubgroup π A :=
      CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup _ I A _
    rw [centralizerPointsSubgroup_eq_range_weightTorus] at hg
    obtain ⟨q, hq⟩ := hg
    intro x hx
    have hz : g.ofConv x = 0 := by
      rw [← hq, BialgHom.mapDomain_apply]
      exact (congrArg q.ofConv hx).trans (map_zero _)
    dsimp [A] at hz
    have hz' : (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R) I).hom x = 0 := by
      simpa only [g, CommHopfAlgCat.quotientPointsHom_apply,
        ofConv_toConv, AlgHom.comp_apply, AlgHom.id_apply, BialgHom.coe_toAlgHom] using hz
    rw [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk] at hz'
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz'

end TauCeti.E6DoubledMinuscule
