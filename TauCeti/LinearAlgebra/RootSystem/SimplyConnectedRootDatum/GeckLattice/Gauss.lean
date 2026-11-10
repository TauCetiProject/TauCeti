/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
import TauCeti.Algebra.Group.OneParameterGauss
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Gauss
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Gauss

/-!
# Opposite-simple-root Gauss factorization in the Geck carrier

For a valid Dynkin type `t`, the numbered simple raising and lowering generators at each Bourbaki
node `i : Fin t.rank` form an `sl₂` pair in the defining matrix representation of Geck's Lie
algebra. Unlike minuscule or standard classical representations, Geck's representation is modeled on
the adjoint module, where root operators do not square to zero (root strings have length three for
simply laced or long roots and four in type `G₂`).

This file specializes the general Kostant opposite-root Gauss factorizations to the pinned Geck
lattice and its toral-closure group scheme. Over any commutative ring `A` and for any `a, b ∈ A`
such that `u = 1 + a b` is a unit of `A`, the opposite simple-root elements at Bourbaki node `i`
factor in both multiplication orders through the `i`-th coordinate of the represented split weight
torus (which corresponds to the simple coroot `αᵢ^∨`):

```text
xᵢ(a) x₋ᵢ(b) = x₋ᵢ(b u⁻¹) t(Pi.mulSingle i u) xᵢ(a u⁻¹),
x₋ᵢ(b) xᵢ(a) = xᵢ(a u⁻¹) t(Pi.mulSingle i u⁻¹) x₋ᵢ(b u⁻¹).
```

Weyl-word transport of these factorizations to every root of the simply connected root datum is
developed in `TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.Weyl.Gauss`.

## Main results

* `TauCeti.DynkinType.geckRootSubgroupParam_inl_mul_inr` and
  `TauCeti.DynkinType.geckRootSubgroupParam_inr_mul_inl`: opposite-simple-root Gauss factorizations
  on base-changed Geck lattice automorphisms.
* `TauCeti.DynkinType.geckRootSubgroupPoints_inl_mul_inr` and
  `TauCeti.DynkinType.geckRootSubgroupPoints_inr_mul_inl`: opposite-simple-root Gauss factorizations
  inside the matrix point group `TauCeti.DynkinType.geckPoints`.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
-/

public section

namespace TauCeti.DynkinType

universe v

noncomputable section

-- Matrices form a Lie ring through their commutator in the defining Geck representation.
attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-! ## Lattice-automorphism Gauss factorizations -/

/-- **Opposite-simple-root Gauss factorization on Geck lattice automorphisms (raising times
lowering).** Whenever `u = 1 + a b` is a unit of `A`, the product `xᵢ(a) x₋ᵢ(b)` at Bourbaki node
`i` factors through the `i`-th coordinate of `geckTorusPoints`. -/
theorem geckRootSubgroupParam_inl_mul_inr (i : Fin t.rank) (A : CommAlgCat.{v} ℤ)
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd a) *
        t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd b) =
      t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        t.geckTorusPoints ht A (Pi.mulSingle i u) *
        t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have h :=
    UniversalEnvelopingAlgebra.kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f
      (i := Sum.inl i) (j := Sum.inr i) (c := i) (α := t.rootGeneratorWeight ht (.inl i))
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
      (t.isNilpotent_geckRepresentation_rootGenerator ht (.inr i))
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
      (t.isCartanWeightVector_geckCoordinateBasisFin ht)
      (t.isSl2Triple_geckRepresentation ht i)
      (fun q => t.lie_lieBasis_h_rootGenerator ht (.inl i) q)
      (fun q => t.lie_lieBasis_h_rootGenerator_inr_neg ht i q)
      A a b u hu
  rwa [UniversalEnvelopingAlgebra.kostantCoordinateCocharacter_apply] at h

/-- **Opposite-simple-root Gauss factorization on Geck lattice automorphisms (lowering times
raising).** Whenever `u = 1 + a b` is a unit of `A`, the product `x₋ᵢ(b) xᵢ(a)` at Bourbaki node
`i` factors through the inverse of the `i`-th coordinate of `geckTorusPoints`. -/
theorem geckRootSubgroupParam_inr_mul_inl (i : Fin t.rank) (A : CommAlgCat.{v} ℤ)
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd b) *
        t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd a) =
      t.geckRootSubgroupParam ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        t.geckTorusPoints ht A (Pi.mulSingle i u⁻¹) *
        t.geckRootSubgroupParam ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  simpa only [Pi.mulSingle_inv] using
    map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq
      (t.geckRootSubgroupParam_inl_mul_inr ht i A (-a) (-b) u (by rwa [neg_mul_neg]))

/-! ## Point-group Gauss factorizations -/

/-- **Opposite-simple-root Gauss factorization in the Geck carrier point group (raising times
lowering).** Over every commutative ring `A` and whenever `u = 1 + a b` is a unit of `A`, the
product `xᵢ(a) x₋ᵢ(b)` in `t.geckPoints ht A` factors through the represented weight-torus point
`Pi.mulSingle i u`. -/
theorem geckRootSubgroupPoints_inl_mul_inr (i : Fin t.rank) (A : Type v) [CommRing A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a) *
        t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd b) =
      t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) *
        t.geckWeightTorusPoints ht A (Pi.mulSingle i u) *
        t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) := by
  have h :=
    UniversalEnvelopingAlgebra.kostantToralRootSubgroupPoints_mul_kostantToralRootSubgroupPoints_e_f
      (i := Sum.inl i) (j := Sum.inr i) (c := i) (α := t.rootGeneratorWeight ht (.inl i))
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
      (t.isCartanWeightVector_geckCoordinateBasisFin ht)
      (t.isSl2Triple_geckRepresentation ht i)
      (fun q => t.lie_lieBasis_h_rootGenerator ht (.inl i) q)
      (fun q => t.lie_lieBasis_h_rootGenerator_inr_neg ht i q)
      A a b u hu
  rw [geckRootSubgroupPoints_def, geckRootSubgroupPoints_def, geckWeightTorusPoints_def]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
  exact congrArg
    (MulEquiv.subgroupCongr (t.geckPoints_eq_kostantToralPointsSubgroup ht A).symm) h

/-- **Opposite-simple-root Gauss factorization in the Geck carrier point group (lowering times
raising).** Over every commutative ring `A` and whenever `u = 1 + a b` is a unit of `A`, the
product `x₋ᵢ(b) xᵢ(a)` in `t.geckPoints ht A` factors through the represented weight-torus point
`Pi.mulSingle i u⁻¹`. -/
theorem geckRootSubgroupPoints_inr_mul_inl (i : Fin t.rank) (A : Type v) [CommRing A]
    (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd b) *
        t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a) =
      t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * ↑u⁻¹)) *
        t.geckWeightTorusPoints ht A (Pi.mulSingle i u⁻¹) *
        t.geckRootSubgroupPoints ht (.inr i) A (Multiplicative.ofAdd (b * ↑u⁻¹)) := by
  simpa only [Pi.mulSingle_inv] using
    map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq
      (t.geckRootSubgroupPoints_inl_mul_inr ht i A (-a) (-b) u (by rwa [neg_mul_neg]))

end

end TauCeti.DynkinType
