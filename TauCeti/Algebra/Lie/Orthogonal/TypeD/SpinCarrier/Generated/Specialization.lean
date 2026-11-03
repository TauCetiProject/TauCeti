/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Generated.Basic

/-!
# Specialization of the generated type-D spin group

For any extension of commutative rings, the subgroup generated after extension by the numbered
spin root subgroups and weight torus lies in the scalar extension of the generated subgroup.
The resulting coordinate map is surjective and is characterized by its ambient general-linear
coordinate square. It preserves every generating map, and agrees with the existing comparison
isomorphism for free extensions.

In particular the comparison applies to reduction modulo a prime, where freeness of the
extension is unavailable. It does not assert equality of the two generated models at non-flat
specialization, or identify either model with an independently pinned simply connected group.

## References

* B. Conrad, *Reductive Group Schemes*, §1.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.

The generator compatibility argument follows the existing tripled-D₄ comparison in
`TauCeti.Algebra.Lie.D4.Tripled.Generated.BaseChange`. The construction uses the common-kernel
base-change inclusion and the quotient base-change isomorphism, not a flatness assumption.
-/

public section

open CategoryTheory

namespace TauCeti.TypeDSpinCarrier

universe v w

variable (n : ℕ) (hn : 4 ≤ n)
variable (k : Type v) (K : Type max v w) [CommRing k] [CommRing K] [Algebra k K]

/-- The extended defining equations vanish on every root and torus generator over the extension
ring. Additional equations after specialization are allowed. -/
theorem map_baseChangeHopfIdeal_generatedDefiningIdeal_le :
    (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n hn k)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom ≤
      generatedDefiningIdeal n hn K := by
  rw [generatedDefiningIdeal_def, generatedDefiningIdeal_def]
  calc
    _ ≤ (CommHopfAlgCat.commonKernelHopfIdeal fun j ↦
          CommHopfAlgCat.baseChangeMap (K := K) (generatorCoordinateMap n hn k j)).map
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom :=
      HopfIdeal.map_mono _ (CommHopfAlgCat.baseChangeHopfIdeal_commonKernelHopfIdeal_le _)
    _ = _ := by
      rw [CommHopfAlgCat.map_commonKernelHopfIdeal,
        ← funext (generatorCoordinateMap_baseChange n hn k K),
        CommHopfAlgCat.commonKernelHopfIdeal_comp_of_injective _ _ fun j ↦
          (ConcreteCategory.bijective_of_isIso
            (generatorCoordinateAlgebraBaseChangeIso n k K j).hom).1]

/-- The coordinate map from scalar extension of the generated type-D spin group to the group
generated over the extension ring. On group schemes it represents the reverse closed immersion.
No freeness or flatness assumption is made. -/
noncomputable def generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n hn k) ⟶
      generatedCoordinateHopfAlgebra n hn K :=
  (CommHopfAlgCat.baseChangeIsoOfEqQuotient (generatedDefiningIdeal n hn k)
    ((CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n hn k)).map
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom)
    (generatedCoordinateHopfAlgebra_def n hn k) rfl
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)) rfl).hom ≫
    CommHopfAlgCat.quotientMapOfLe _
      (map_baseChangeHopfIdeal_generatedDefiningIdeal_le n hn k K) ≫
    (eqToIso (generatedCoordinateHopfAlgebra_def n hn K)).inv

/-- The specialization comparison preserves the ambient general-linear coordinates. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap :
    CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k) ≫
        generatedCoordinateHopfAlgebraBaseChangeMap n hn k K =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n hn K := by
  rw [generatedCoordinateHopfAlgebraBaseChangeMap, ← Category.assoc,
    ← Category.assoc,
    CommHopfAlgCat.baseChangeMap_comp_baseChangeIsoOfEqQuotient_hom _ _ _ _ _ _ _
      (CommHopfAlgCat.mkQuotient _
        ((CommHopfAlgCat.baseChangeHopfIdeal (K := K) (generatedDefiningIdeal n hn k)).map
          (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom.hom))
      (generatedCoordinateMap_comp_eqToHom n hn k) (by simp)]
  simp only [Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe_assoc]
  rw [← generatedCoordinateMap_comp_eqToHom]
  simp only [Category.assoc, eqToIso.inv, eqToHom_trans, eqToHom_refl, Category.comp_id]

private noncomputable instance baseChangeGeneratedCoordinateMap_epi :
    Epi (CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k)) :=
  ConcreteCategory.epi_of_surjective _ (CommHopfAlgCat.baseChangeMap_surjective
    (generatedCoordinateMap n hn k) (generatedCoordinateMap_surjective n hn k))

/-- The ambient coordinate square uniquely determines the specialization comparison. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_unique
    (f : CommHopfAlgCat.baseChange (K := K) (generatedCoordinateHopfAlgebra n hn k) ⟶
      generatedCoordinateHopfAlgebra n hn K)
    (hf : CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateMap n hn k) ≫ f =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom ≫
        generatedCoordinateMap n hn K) :
    f = generatedCoordinateHopfAlgebraBaseChangeMap n hn k K := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (generatedCoordinateMap n hn k))).mp
  rw [hf, baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap]

/-- The specialization comparison is surjective on coordinate algebras, so the group generated
after extension is a closed subgroup of the extended group. -/
theorem generatedCoordinateHopfAlgebraBaseChangeMap_surjective :
    Function.Surjective (generatedCoordinateHopfAlgebraBaseChangeMap n hn k K).hom := by
  have h := (generatedCoordinateMap_surjective n hn K).comp
    (ConcreteCategory.bijective_of_isIso
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n)).hom).2
  rw [← BialgHom.coe_comp, ← _root_.CommHopfAlgCat.hom_comp,
    ← baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap] at h
  exact Function.Surjective.of_comp h

/-- Specialization preserves every numbered root-subgroup and weight-torus coordinate lift. -/
@[reassoc (attr := simp)]
theorem generatedCoordinateHopfAlgebraBaseChangeMap_comp_generatedCoordinateLift
    (j : Sum (Fin n ⊕ Fin n) Unit) :
    generatedCoordinateHopfAlgebraBaseChangeMap n hn k K ≫ generatedCoordinateLift n hn K j =
      CommHopfAlgCat.baseChangeMap (K := K) (generatedCoordinateLift n hn k j) ≫
        (generatorCoordinateAlgebraBaseChangeIso n k K j).hom := by
  apply (cancel_epi (CommHopfAlgCat.baseChangeMap (K := K)
    (generatedCoordinateMap n hn k))).mp
  rw [← Category.assoc,
    baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeMap,
    Category.assoc, generatedCoordinateMap_comp_generatedCoordinateLift]
  rw [← Category.assoc, ← (CommHopfAlgCat.baseChangeFunctor (K := K)).map_comp,
    generatedCoordinateMap_comp_generatedCoordinateLift]
  exact ((Iso.inv_comp_eq
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso k K (dimension n))).mp
      (generatorCoordinateMap_baseChange n hn k K j)).symm

/-- For a free extension the specialization comparison is the existing base-change isomorphism.
-/
theorem
    generatedCoordinateHopfAlgebraBaseChangeMap_eq_generatedCoordinateHopfAlgebraBaseChangeIso_hom
    [Module.Free k K] :
    generatedCoordinateHopfAlgebraBaseChangeMap n hn k K =
      (generatedCoordinateHopfAlgebraBaseChangeIso n hn k K).hom := by
  symm
  apply generatedCoordinateHopfAlgebraBaseChangeMap_unique
  exact baseChangeMap_generatedCoordinateMap_comp_generatedCoordinateHopfAlgebraBaseChangeIso_hom
    n hn k K

end TauCeti.TypeDSpinCarrier
