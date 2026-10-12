/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.StandardComodule
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.BaseChange
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
import TauCeti.Algebra.Coalgebra.Comodule.GroupLike
import TauCeti.Algebra.Coalgebra.Subcomodule.Corestrict

/-!
# The standard representation of the type-B spin carrier

The full-weight type-`Bₙ₊₁` spin carrier is a closed subgroup of `GL_(2^(n+1))`. After base
change to a commutative ring `R`, its standard representation is therefore the corestriction of
the standard general-linear comodule along the quotient coordinate morphism.

This file proves that the resulting representation, the spin representation of the carrier, is
faithful over every commutative ring and simple over every field. For simplicity, restriction to
the spin weight torus separates a nonzero invariant vector into its one-dimensional weight
components, since the spin weights are pairwise distinct. A numbered simple root generator acts
on an exterior basis vector by creating and contracting coordinates, so whenever the corresponding
spin weight pairs to `∓1` with the simple coroot, the positive or negative simple-root element at
parameter one has image equal to the original basis vector plus its simple reflection, up to
sign. Subtracting the original vector therefore gives the reflected vector up to sign. The spin
weights form a single orbit of the simple reflections, so a coordinate vector reaches every
other one.

## Main declarations

* `TauCeti.TypeBSpinCarrier.standardComodule`: the standard comodule on `R^(2^(n+1))`.
* `TauCeti.TypeBSpinCarrier.isFaithful_standardComodule`: faithfulness of the standard comodule.
* `TauCeti.TypeBSpinCarrier.mulVec_mem` and `TauCeti.TypeBSpinCarrier.points_mulVec_mem`:
  subcomodules are stable under carrier-valued points and under concrete carrier points.
* `TauCeti.TypeBSpinCarrier.torusCorestrict_eq_ofWeights`: restricted to the weight torus, the
  standard comodule is the direct sum of the spin weight lines.
* `TauCeti.TypeBSpinCarrier.isSimpleOrder_of_spinWeights_of_rootSubgroupPoints`: a comodule with
  the spin weight decomposition whose subcomodules are stable under the numbered simple-root
  matrices is simple over a field.
* `TauCeti.TypeBSpinCarrier.instIsSimpleOrderSubcomodule`: simplicity over a field.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2 and II.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.

The corestriction, faithfulness, and point-action arguments, and the shape of the simplicity
proof, follow the type-`E₆` minuscule carrier in
`TauCeti.Algebra.Lie.E6.Minuscule.StandardComodule`.
-/

public section

open CategoryTheory Module WithConv
open TauCeti.UniversalEnvelopingAlgebra
open scoped Matrix TensorProduct

namespace TauCeti.TypeBSpinCarrier

universe u

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The standard right comodule of the specialized type-`Bₙ₊₁` spin carrier. -/
@[instance_reducible]
noncomputable def standardComodule :
    Comodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R) :=
  GeneralLinear.corestrictStandardComodule R (dimension n) (coordinateMap n R).hom

attribute [local instance] GeneralLinear.standardComodule standardComodule

/-- **The standard comodule of the specialized type-`Bₙ₊₁` spin carrier is faithful.** -/
theorem isFaithful_standardComodule :
    Comodule.IsFaithful (k := R) (H := coordinateHopfAlgebra n R)
      (V := Fin (dimension n) → R) :=
  GeneralLinear.isFaithful_corestrictStandardComodule R (dimension n)
    (coordinateMap n R).hom (coordinateMap_surjective n R)

/-- **A subcomodule of the standard carrier comodule is stable under every carrier-valued
point.** -/
theorem mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (g : WithConv (coordinateHopfAlgebra n R →ₐ[R] R)) {w : Fin (dimension n) → R}
    (hw : w ∈ N) :
    (GeneralLinear.pointToGeneralLinear (dimension n)
        (CommHopfAlgCat.quotientPointsHom
          (GeneralLinear.coordinateHopfAlgebra R (dimension n)) (baseChangeDefiningIdeal n R)
          (CommAlgCat.of R R) g) : Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈
      N := by
  have h := GeneralLinear.corestrictStandardComodule_mulVec_mem R (dimension n)
    (coordinateMap n R).hom N g hw
  have hpoint : AlgHom.mapDomain (coordinateMap n R).hom g = _ :=
    mapPointsFunctor_coordinateMap_app n R g
  rwa [hpoint] at h

/-- A subcomodule of the standard carrier comodule is stable under every concrete carrier
point. -/
theorem points_mulVec_mem
    (N : Subcomodule R (coordinateHopfAlgebra n R) (Fin (dimension n) → R))
    (g : points n R) {w : Fin (dimension n) → R} (hw : w ∈ N) :
    ((g : Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ w ∈ N := by
  have h := mulVec_mem n R N ((baseChangePointsMulEquiv n R (CommAlgCat.of R R)).symm g) hw
  rw [quotientPointsHom_baseChangePointsMulEquiv_symm,
    ← GeneralLinear.pointsMulEquiv_apply, MulEquiv.apply_symm_apply] at h
  exact h

/-! ## The numbered simple root generators on the coordinate basis -/

/-- At parameter one, a numbered simple-root point moves a coordinate vector by the signed
coordinate vector its root generator produces. -/
private theorem rootSubgroupPoints_mulVec_single_sub (j : Fin (n + 1) ⊕ Fin (n + 1))
    {a a' : Fin (dimension n)} {c : ℤˣ}
    (h : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W)) :
    ((rootSubgroupPoints n j R (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) R) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) R) *ᵥ Pi.single a 1 -
        Pi.single a 1 =
      ((c : ℤ) : R) • Pi.single a' 1 := by
  rw [coe_rootSubgroupPoints_eq_one_add_smul]
  rw [toAdd_ofAdd, one_smul, Matrix.add_mulVec, Matrix.one_mulVec,
    add_sub_cancel_left, Matrix.mulVec_single_one]
  funext r
  simp [rootIntMatrix_apply_of_eq n j h, Pi.single_apply]

/-- The character of the spin weight torus attached to a spin-basis index. -/
noncomputable abbrev basisCharacter (a : Fin (dimension n)) :
    Multiplicative (Fin (n + 1) →₀ ℤ) :=
  SplitTorus.weightCharacter (basisWeight n a)

/-- Distinct spin-basis indices give distinct characters of the weight torus. -/
theorem basisCharacter_injective : Function.Injective (basisCharacter n) := by
  intro a b h
  have hw : basisWeight n a = basisWeight n b := by
    funext i
    simpa only [basisCharacter, SplitTorus.toAdd_weightCharacter] using
      congrArg (fun χ : Multiplicative (Fin (n + 1) →₀ ℤ) ↦ Multiplicative.toAdd χ i) h
  exact (Fintype.equivFin (Finset (Fin (n + 1)))).symm.injective
    (DynkinType.typeBSpinWeight_injective hw)

/-- **Restricting the standard carrier comodule to the spin weight torus gives the direct sum of
the distinct spin weight lines.** Corestricting along `weightTorusToBaseChangeCoordinateMap`
turns the standard comodule on `Fin (dimension n) → R` into the comodule in which the coordinate
basis vector at `a` spans the weight line of the torus character `basisCharacter n a`. -/
theorem torusCorestrict_eq_ofWeights :
    let _ := standardComodule n R
    Comodule.Corestrict (weightTorusToBaseChangeCoordinateMap n R).hom.toCoalgHom =
      Comodule.ofWeights (Pi.basisFun R (Fin (dimension n))) (basisCharacter n) := by
  apply GeneralLinear.corestrict_corestrict_standardComodule_eq_ofWeights
    (coordinateMap n R).hom (weightTorusToBaseChangeCoordinateMap n R).hom
    (basisWeight n)
  rw [← _root_.CommHopfAlgCat.hom_comp,
    coordinateMap_comp_weightTorusToBaseChangeCoordinateMap,
    GeneralLinear.hom_weightTorusBaseChangeCoordinateMap]

/-! ## Simplicity over a field -/

section Simple

variable (k : Type u) [Field k]

/-- If a numbered simple root generator sends one lattice basis vector to a signed second one,
then a subspace stable under the corresponding root matrix at parameter one and containing the
first coordinate vector contains the second. -/
private theorem single_mem_of_rep_rootGenerator_eq
    (N : Submodule k (Fin (dimension n) → k))
    (j : Fin (n + 1) ⊕ Fin (n + 1)) {a a' : Fin (dimension n)} {c : ℤˣ}
    (hroot : ∀ w ∈ N, ((rootSubgroupPoints n j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) k) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) k) *ᵥ w ∈ N)
    (h : rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.typeBSimpleRootGeneratorFamily j))
        (latticeBasis n a : ExteriorAlgebra ℚ (polarization n).W) =
      c • (latticeBasis n a' : ExteriorAlgebra ℚ (polarization n).W))
    (ha : Pi.single a 1 ∈ N) : Pi.single a' 1 ∈ N := by
  have hsub := N.sub_mem (hroot _ ha) ha
  rw [rootSubgroupPoints_mulVec_single_sub n k j h] at hsub
  have hc : ((c : ℤ) : k) ≠ 0 := by
    rcases Int.units_eq_one_or c with rfl | rfl <;> simp
  exact (Submodule.smul_mem_iff _ hc).1 hsub

/-- Invariance under the two simple-root points makes membership of coordinate basis vectors
stable under every simple reflection. -/
private theorem single_basisReflection_mem
    (N : Submodule k (Fin (dimension n) → k))
    (hroot : ∀ (j : Fin (n + 1) ⊕ Fin (n + 1)), ∀ w ∈ N,
      ((rootSubgroupPoints n j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) k) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) k) *ᵥ w ∈ N)
    (a : Fin (dimension n)) (i : Fin (n + 1)) (ha : Pi.single a 1 ∈ N) :
    Pi.single (basisReflection n i a) 1 ∈ N := by
  rcases DynkinType.typeBSpinWeight_apply_eq_neg_one_or_eq_zero_or_eq_one (signSet n a) i with
    hneg | hzero | hpos
  · obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inl_exteriorBasis n i _ _ hneg
      (signSet_basisReflection n i a).symm
    refine single_mem_of_rep_rootGenerator_eq n k N (.inl i) (c := c) (hroot _) ?_ ha
    rw [coe_latticeBasis n a, coe_latticeBasis n (basisReflection n i a)]
    exact hc
  · rwa [(basisReflection_eq_self_iff n i a).2 hzero]
  · obtain ⟨c, hc⟩ := exists_rep_rootGenerator_inr_exteriorBasis n i _ _ hpos
      (signSet_basisReflection n i a).symm
    refine single_mem_of_rep_rootGenerator_eq n k N (.inr i) (c := c) (hroot _) ?_ ha
    rw [coe_latticeBasis n a, coe_latticeBasis n (basisReflection n i a)]
    exact hc

/-- A comodule on `k^(2^(n+1))` with the type-`Bₙ₊₁` spin weight decomposition is simple if its
subcomodules are stable under the numbered positive and negative simple-root matrices at parameter
one. This applies both to the specialization of the integral carrier and to the subgroup generated
directly over the field. -/
theorem isSimpleOrder_of_spinWeights_of_rootSubgroupPoints
    {H : Type*} [AddCommGroup H] [Module k H] [Coalgebra k H]
    [Comodule k H (Fin (dimension n) → k)]
    (f : H →ₗc[k] MonoidAlgebra k (Multiplicative (Fin (n + 1) →₀ ℤ)))
    (hweights : Comodule.Corestrict f =
      Comodule.ofWeights (Pi.basisFun k (Fin (dimension n))) (basisCharacter n))
    (hroot : ∀ (N : Subcomodule k H (Fin (dimension n) → k)) (j : Fin (n + 1) ⊕ Fin (n + 1)),
      ∀ w ∈ N, ((rootSubgroupPoints n j k (Multiplicative.ofAdd 1) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) k) :
          Matrix (Fin (dimension n)) (Fin (dimension n)) k) *ᵥ w ∈ N) :
    IsSimpleOrder (Subcomodule k H (Fin (dimension n) → k)) :=
  Subcomodule.isSimpleOrder_of_corestrict_eq_ofWeights f (basisCharacter n)
    (basisCharacter_injective n) hweights
    (basisReflection n) (basisReflection_involutive n)
    (fun N a i ↦ single_basisReflection_mem n k N.toSubmodule (hroot N) a i)
    (Fintype.equivFin (Finset (Fin (n + 1))) ∅) fun a ↦ by
      obtain ⟨l, hl⟩ := DynkinType.exists_typeBSpinReflections_eq (signSet n a)
      exact ⟨l, by rw [foldl_basisReflection, hl]; simp [signSet]⟩

/-- **The standard comodule of the specialized type-`Bₙ₊₁` spin carrier is simple over every
field.** -/
instance instIsSimpleOrderSubcomodule :
    IsSimpleOrder (Subcomodule k (coordinateHopfAlgebra n k) (Fin (dimension n) → k)) :=
  isSimpleOrder_of_spinWeights_of_rootSubgroupPoints n k
    (weightTorusToBaseChangeCoordinateMap n k).hom.toCoalgHom (torusCorestrict_eq_ofWeights n k)
    fun N j _ hw ↦ points_mulVec_mem n k N (rootSubgroupPoints n j k (Multiplicative.ofAdd 1)) hw

end Simple

end TauCeti.TypeBSpinCarrier
