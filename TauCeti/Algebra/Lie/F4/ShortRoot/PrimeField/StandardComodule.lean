/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# The standard representation of the short-root F₄ prime-field carrier

The scalar extension of the short-root carrier over `𝔽₂` has a faithful representation on
column vectors of length twenty-six. Restriction to its weight torus has twenty-four distinct
nonzero weights and a two-dimensional zero-weight space. Every invariant submodule is stable
under the corresponding weight projections, including over finite fields: characters, rather
than rational torus points, separate the weights.

The zero-weight projection retains both coordinates together. There is no assertion that either
zero-weight coordinate line is invariant, nor that the standard representation is simple.
These projections and the numbered root actions provide the invariant-subspace calculations
needed to study simplicity and the unipotent radical.

Here the coordinate algebra is the scalar extension of the prime-field carrier itself, not the
possibly smaller subgroup generated after scalar extension. The carrier is not identified with
the pinned simply connected group scheme of type `F₄`; transfer to that group requires such an
identification.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.

The corestriction construction follows
`TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.StandardComodule`; the coefficient and
matrix-point interface follows `TauCeti.Algebra.Lie.E6.DoubledMinuscule.StandardComodule`.
-/

public section

open CategoryTheory WithConv
open scoped Matrix TensorProduct

namespace TauCeti.F4ShortRoot.PrimeField

open DynkinType

universe u

noncomputable section

variable (k : Type u) [CommRing k] [Algebra (ZMod 2) k]

/-- The coordinate Hopf algebra of the scalar extension of the short-root prime-field carrier. -/
abbrev coordinateHopfAlgebra : CommHopfAlgCat k :=
  CommHopfAlgCat.baseChange (K := k)
    (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) definingIdeal)

/-- The coordinate morphism of the carrier's inclusion in `GL₂₆` after scalar extension. -/
def coordinateMap : GeneralLinear.coordinateHopfAlgebra k 26 ⟶ coordinateHopfAlgebra k :=
  (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv ≫
    CommHopfAlgCat.baseChangeMap (K := k)
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) definingIdeal)

/-- The carrier coordinate morphism is the scalar extension of its quotient morphism,
transported along the general-linear coordinate identification. -/
theorem coordinateMap_def :
    coordinateMap k =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv ≫
        CommHopfAlgCat.baseChangeMap (K := k)
          (CommHopfAlgCat.mkQuotient
            (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26) definingIdeal) := by
  rw [coordinateMap]

/-- The standard coordinate morphism is surjective, so the represented inclusion is closed. -/
theorem coordinateMap_surjective : Function.Surjective (coordinateMap k).hom := by
  rw [coordinateMap_def, _root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp]
  exact (CommHopfAlgCat.baseChangeMap_surjective _
    (CommHopfAlgCat.mkQuotient_surjective _ _)).comp
      (ConcreteCategory.bijective_of_isIso
        (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv).2

/-- A reduced generator factored through the carrier, then extended to `k`. -/
def generatorCoordinateMap (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    coordinateHopfAlgebra k ⟶ CommHopfAlgCat.baseChange (K := k) (generatorCodomain j) :=
  CommHopfAlgCat.baseChangeMap (K := k)
    (CommHopfAlgCat.liftQuotient definingIdeal (generator j) (by
      rw [definingIdeal_def]
      exact CommHopfAlgCat.commonKernelHopfIdeal_toIdeal_le_ker generator j))

/-- Factoring a generator through the carrier does not alter its ambient coordinate map. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_generatorCoordinateMap (j : (Fin 4 ⊕ Fin 4) ⊕ Unit) :
    coordinateMap k ≫ generatorCoordinateMap k j =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso (ZMod 2) k 26).inv ≫
        CommHopfAlgCat.baseChangeMap (K := k) (generator j) := by
  rw [coordinateMap_def, generatorCoordinateMap, Category.assoc]
  simp only [← (CommHopfAlgCat.baseChangeFunctor (K := k)).map_comp,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient]

/-- Restriction of functions on the carrier to its scalar-extended weight torus. -/
def weightTorusCoordinateMap : coordinateHopfAlgebra k ⟶
    (DiagonalizableGroup.coordinateRing k (SplitTorus.characterGroup (Fin 4))).obj :=
  generatorCoordinateMap k (.inr ()) ≫
    (DiagonalizableGroup.baseChangeCoordinateHopfAlgebraIso (ZMod 2) k
      (SplitTorus.characterGroup (Fin 4))).hom

/-- The carrier weight torus recovers the prescribed twenty-six weights in the ambient group. -/
@[reassoc (attr := simp)]
theorem coordinateMap_comp_weightTorusCoordinateMap :
    coordinateMap k ≫ weightTorusCoordinateMap k =
      GeneralLinear.weightTorusBaseChangeCoordinateMap (ZMod 2) k f4ShortRootWeight := by
  simp only [weightTorusCoordinateMap,
    coordinateMap_comp_generatorCoordinateMap_assoc, generator_inr,
    GeneralLinear.weightTorusBaseChangeCoordinateMap_eq ℤ (ZMod 2),
    GeneralLinear.weightTorusBaseChangeCoordinateMap_def]

/-- The standard right comodule of the scalar-extended short-root carrier on `k²⁶`. -/
@[instance_reducible]
def standardComodule : Comodule k (coordinateHopfAlgebra k) (Fin 26 → k) :=
  GeneralLinear.corestrictStandardComodule k 26 (coordinateMap k).hom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- The standard representation is faithful in the scheme-theoretic sense. -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := k) (H := coordinateHopfAlgebra k) (V := Fin 26 → k) :=
  GeneralLinear.isFaithful_corestrictStandardComodule k 26 (coordinateMap k).hom
    (coordinateMap_surjective k)

/-- The coefficient matrix consists of the ambient matrix coordinates restricted to the
carrier. -/
theorem coefficientMatrix_basisFun (a b : Fin 26) :
    Comodule.coefficientMatrix (C := coordinateHopfAlgebra k) (Pi.basisFun k (Fin 26)) a b =
      (coordinateMap k).hom (GeneralLinear.coordinateHopfAlgebraAlgEquiv k 26
        (GeneralLinear.coordinateRingMap k 26 (MvPolynomial.X (a, b)))) := by
  simp only [Comodule.coefficientMatrix_corestrict, Matrix.map_apply,
    GeneralLinear.coefficientMatrix_basisFun, BialgHom.toCoalgHom_apply,
    GeneralLinear.genericMatrix_apply]

/-- Base-valued points of the scalar-extended coordinate algebra are the existing matrix-valued
points of the prime-field carrier. -/
def specializedPointsMulEquiv :
    HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k) (CommAlgCat.of k k) ≃*
      points k :=
  (AlgHom.baseChangePointsMulEquiv (k := ZMod 2) (K := k) (R := k)
    (A := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra (ZMod 2) 26)
      definingIdeal)).symm.trans
    ((GeneralLinear.hopfIdealPointsSubgroupMulEquiv 26 definingIdeal
      (CommAlgCat.of (ZMod 2) k)).trans
        (MulEquiv.subgroupCongr (points_eq_hopfIdealPointsSubgroup k).symm))

/-- The point equivalence evaluates the same matrix coordinates as the carrier's standard
representation. -/
@[simp]
theorem pointToGeneralLinear_specializedPointsMulEquiv
    (q : HopfAlgebra.points (R := k) (H := coordinateHopfAlgebra k) (CommAlgCat.of k k)) :
    GeneralLinear.pointToGeneralLinear 26
        (toConv (q.ofConv.comp (coordinateMap k).hom.toAlgHom)) =
      (specializedPointsMulEquiv k q : Matrix.GeneralLinearGroup (Fin 26) k) := by
  rw [coordinateMap_def, GeneralLinear.pointToGeneralLinear_baseChangeMap]
  simp only [specializedPointsMulEquiv, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply]
  rw [GeneralLinear.coe_hopfIdealPointsSubgroupMulEquiv_apply,
    CommHopfAlgCat.quotientPointsHom_apply, GeneralLinear.pointsMulEquiv_apply]

/-- Every subcomodule of the standard representation is stable under the carrier's concrete
matrix-valued points, in particular under its positive and negative simple root subgroups. -/
theorem points_mulVec_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    (g : points k) {v : Fin 26 → k} (hv : v ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin 26) k) : Matrix (Fin 26) (Fin 26) k) *ᵥ v ∈ N := by
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem k 26 (coordinateMap k).hom
    N ((specializedPointsMulEquiv k).symm g) hv
  rwa [AlgHom.mapDomain_apply, pointToGeneralLinear_specializedPointsMulEquiv,
    MulEquiv.apply_symm_apply] at h

/-- On the weight torus the standard comodule is diagonal with the short-root weight table.
The two occurrences of zero remain two independent basis vectors of the same weight. -/
theorem torusCorestrict_eq_ofWeights :
    Comodule.Corestrict (weightTorusCoordinateMap k).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun k (Fin 26))
        (fun a ↦ SplitTorus.weightCharacter (f4ShortRootWeight a)) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (coordinateMap k).hom (weightTorusCoordinateMap k).hom f4ShortRootWeight
  rw [← _root_.CommHopfAlgCat.hom_comp, coordinateMap_comp_weightTorusCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-- A subcomodule is stable under the projection to any torus weight, with all its
multiplicities retained. -/
theorem weightComponent_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    {v : Fin 26 → k} (hv : v ∈ N) (w : Fin 4 → ℤ) :
    (fun a ↦ if f4ShortRootWeight a = w then v a else 0) ∈ N := by
  have hchar (a : Fin 26) :
      SplitTorus.weightCharacter (f4ShortRootWeight a) = SplitTorus.weightCharacter w ↔
        f4ShortRootWeight a = w := by
    constructor
    · intro h
      funext i
      simpa using congrArg
        (fun χ : Multiplicative (Fin 4 →₀ ℤ) ↦ Multiplicative.toAdd χ i) h
    · rintro rfl
      rfl
  simpa only [hchar] using Subcomodule.weightComponent_mem_of_corestrict_eq_ofWeights
    (weightTorusCoordinateMap k).hom.toCoalgHom _ (torusCorestrict_eq_ofWeights k)
    N hv (SplitTorus.weightCharacter w)

/-- Every nonzero-weight coordinate can be extracted from an invariant submodule vector. -/
theorem single_smul_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    {v : Fin 26 → k} (hv : v ∈ N) (a : Fin 26) (ha : f4ShortRootWeight a ≠ 0) :
    v a • Pi.single a 1 ∈ N := by
  have hp := weightComponent_mem k N hv (f4ShortRootWeight a)
  have heq : (fun b ↦ if f4ShortRootWeight b = f4ShortRootWeight a then v b else 0) =
      v a • Pi.single a 1 := by
    ext b
    have hba : f4ShortRootWeight b = f4ShortRootWeight a ↔ b = a := by
      constructor
      · intro h
        exact f4ShortRootWeight_injOn (by simpa [h] using ha) ha h
      · rintro rfl
        rfl
    by_cases hb : b = a
    · subst b
      simp
    · simp [hba, hb]
  rwa [heq] at hp

/-- The zero-weight part of an invariant vector retains both zero-weight coordinates together. -/
theorem zeroWeightComponent_mem
    (N : Subcomodule k (coordinateHopfAlgebra k) (Fin 26 → k))
    {v : Fin 26 → k} (hv : v ∈ N) :
    v 12 • Pi.single 12 1 + v 13 • Pi.single 13 1 ∈ N := by
  have hp := weightComponent_mem k N hv 0
  have heq : (fun a ↦ if f4ShortRootWeight a = 0 then v a else 0) =
      v 12 • Pi.single 12 1 + v 13 • Pi.single 13 1 := by
    ext a
    simp only [f4ShortRootWeight_eq_zero_iff, Pi.add_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
    by_cases h12 : a = 12 <;> by_cases h13 : a = 13 <;> simp_all
  rwa [heq] at hp

end

end TauCeti.F4ShortRoot.PrimeField
