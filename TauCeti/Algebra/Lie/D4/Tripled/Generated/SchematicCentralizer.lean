/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Generated.WeightTorus
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Basic
import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Centralizer.Functorial
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.Centralizer
import TauCeti.Algebra.Lie.D4.Tripled.MaximalTorus

/-!
# The schematic torus centralizer of the generated tripled D₄ carrier

The rank-four weight torus is its own scheme-theoretic centralizer in the subgroup of
`GL₂₄` generated over any commutative ground ring by the tripled root subgroups and torus.
The calculation tests all value algebras, not just field-valued points: the distinct
characters of the vector and two half-spin representations force a centralizing matrix
to be diagonal. The invariant triality product then identifies those diagonal carrier
points with the weight torus.
In particular the equality retains all infinitesimal centralizer structure, including
in characteristic two.

This concerns the generated carrier, without identifying it with the specialization of the
integral toral closure or with an independently pinned simply connected group.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.1.
* SGA 3, Exposé XI, for centralizers of diagonalizable subgroups.
* The matrix centralizer calculation is
  `TauCeti.GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag`;
  the triality-product calculation is
  `TauCeti.D4Tripled.mem_range_weightTorusPoints_iff_isDiag`.
-/

public section

open CategoryTheory WithConv
open TauCeti.DynkinType

namespace TauCeti.D4Tripled.Generated

universe u v

noncomputable section

variable (R : Type u) [CommRing R]

/-- Over every value algebra, a generated-carrier point lies in the closed weight torus
exactly when its matrix is diagonal. This includes nonreduced value algebras. -/
@[simp↓]
theorem mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag
    (A : CommAlgCat.{v} R)
    (g : HopfAlgebra.points (R := R) (H := generatedCoordinateHopfAlgebra R) A) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
        (weightTorusDefiningIdeal R) A ↔
      (GeneralLinear.pointsMulEquiv 24
        (BialgHom.mapDomain (generatedCoordinateMap R).hom g) :
          Matrix (Fin 24) (Fin 24) A).IsDiag := by
  let f := (GeneralLinear.pointsMulEquiv (R := R) 24).toMonoidHom.comp
    ((CommHopfAlgCat.Hom.mapPointsFunctor (generatedCoordinateMap R)).app A).hom
  have hf : Function.Injective f :=
    (GeneralLinear.pointsMulEquiv 24).injective.comp
      (CommHopfAlgCat.Hom.mapPointsFunctor_app_injective_of_surjective
        (generatedCoordinateMap R) (generatedCoordinateMap_surjective R) A)
  have hfg : f g = GeneralLinear.pointsMulEquiv 24
      (BialgHom.mapDomain (generatedCoordinateMap R).hom g) := by
    dsimp only [f]
    -- The categorical source and the explicit convolution-point type use different wrappers.
    erw [BialgHom.mapDomain_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply]
  have hmem := Subgroup.mem_map_iff_mem hf
    (K := CommHopfAlgCat.quotientPointsSubgroup (generatedCoordinateHopfAlgebra R)
      (weightTorusDefiningIdeal R) A) (x := g)
  rw [map_quotientPointsSubgroup_weightTorusDefiningIdeal R A] at hmem
  let p : points A :=
    ⟨f g, coe_carrierPointsHom R A g ▸ (carrierPointsHom R A g).property⟩
  refine hmem.symm.trans ?_
  have hp : f g ∈ ((weightTorusPoints A).range).map (points A).subtype ↔
      p ∈ (weightTorusPoints A).range :=
    Subgroup.mem_map_iff_mem (points A).subtype_injective
      (K := (weightTorusPoints A).range) (x := p)
  refine hp.trans ((mem_range_weightTorusPoints_iff_isDiag p).trans ?_)
  exact Iff.of_eq (congrArg (fun m : Matrix.GeneralLinearGroup (Fin 24) A ↦
    (m : Matrix (Fin 24) (Fin 24) A).IsDiag) hfg)

/-- The schematic centralizer of the generated tripled D₄ weight torus is the torus itself,
over every commutative ground ring, including its infinitesimal structure. -/
@[simp↓]
theorem centralizerHopfIdeal_generatedWeightTorusCoordinateMap :
    BialgHom.centralizerHopfIdeal (generatedWeightTorusCoordinateMap R).hom =
      weightTorusDefiningIdeal R := by
  apply HopfIdeal.eq_of_forall_quotientPointsSubgroup_eq
  intro A
  ext g
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff,
    mem_quotientPointsSubgroup_weightTorusDefiningIdeal_iff_isDiag]
  -- Vanishing on the Hopf ideal is containment of its underlying ideal in the point's kernel.
  simp only [← HopfIdeal.mem_toIdeal, ← RingHom.mem_ker, ← IsConcreteLE.le_iff]
  rw [← BialgHom.centralizerHopfIdeal_comp_le_ker_iff
    (generatedCoordinateMap R).hom (generatedCoordinateMap_surjective R),
    hom_generatedWeightTorusCoordinateMap_comp_generatedCoordinateMap]
  exact GeneralLinear.centralizerHopfIdeal_weightTorus_le_ker_iff_isDiag
    d4TripledWeight d4TripledWeight_injective _

end

end TauCeti.D4Tripled.Generated
