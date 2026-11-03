/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Weyl squares in the type-B spin carrier

For each numbered simple root of the full-weight type-`Bₙ₊₁` spin carrier, the pinned word
`xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` squares to the simple-coroot value at `-1`. This fixes the torus
factor lost on passing from normalizer representatives to Weyl-group elements. In particular,
the word's fourth power is one. No assertion of exact order is made: the square can become
one in characteristic two.

The identities hold over arbitrary commutative value rings, including nonreduced rings, and
also at `n = 0`, where the carrier is the rank-one spin construction. They do not identify
the carrier with an independently constructed pinned simply connected group scheme.

The proof specializes `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_sq` using the
represented simple-root triples and the integral exterior weight basis, then transports the
identity to the carrier's matrix coordinates.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe v

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (A : Type v) [CommRing A]

/-- The pinned simple Weyl word squares to the corresponding simple-coroot value at `-1`,
independently of its unit parameter. -/
@[simp↓]
theorem rootSubgroupPoints_weylWord_sq (i : Fin (n + 1)) (u : Aˣ) :
    (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A)) *
      rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 2 =
        weightTorusPoints n A (Pi.mulSingle i (-1)) := by
  have hpos : ∀ j, ⁅typeBSimpleCorootGenerator (K := ℚ) j,
      typeBSimpleRootGeneratorFamily (K := ℚ) (.inl i)⁆ =
        ((rootGeneratorWeight n (.inl i) j : ℤ) : ℚ) •
          typeBSimpleRootGeneratorFamily (K := ℚ) (.inl i) :=
    lie_coroot_rootGenerator n (.inl i)
  have hneg : ∀ j, ⁅typeBSimpleCorootGenerator (K := ℚ) j,
      typeBSimpleRootGeneratorFamily (K := ℚ) (.inr i)⁆ =
        -(((rootGeneratorWeight n (.inl i) j : ℤ) : ℚ) •
          typeBSimpleRootGeneratorFamily (K := ℚ) (.inr i)) := by
    intro j
    simpa only [rootGeneratorWeight_inl, rootGeneratorWeight_inr, Pi.neg_apply,
      Int.cast_neg, neg_smul] using lie_coroot_rootGenerator n (.inr i) j
  have h := kostantWeylParam_sq
    (typeBSimpleRootGeneratorFamily (K := ℚ)) (typeBSimpleCorootGenerator (K := ℚ))
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n)
    (isNilpotent_rep_rootGenerator n (.inl i)) (isNilpotent_rep_rootGenerator n (.inr i))
    (latticeBasis n) (basisWeight n) (isCartanWeightVector_latticeBasis n)
    (isSl2Triple_rep_rootGenerator n i) hpos hneg (CommAlgCat.of ℤ A) u
  have hmatrix := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv ((latticeBasis n).baseChange A)).toMonoidHom) h
  simp only [kostantWeylParam_def, kostantCoordinateCocharacter_apply, map_pow, map_mul,
    MulEquiv.toMonoidHom_eq_coe,
    basisMatrix_kostantRootSubgroupParam _ _ _ _ _ (isNilpotent_rep_rootGenerator n),
    basisMatrix_kostantTorusPoints] at hmatrix
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, coe_rootSubgroupPoints,
    coe_weightTorusPoints] using hmatrix

/-- Every pinned simple Weyl word in the spin carrier has fourth power one. -/
@[simp↓]
theorem rootSubgroupPoints_weylWord_pow_four (i : Fin (n + 1)) (u : Aˣ) :
    (rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A)) *
      rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
      rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 4 = 1 := by
  have hfour : 4 = 2 * 2 := rfl
  rw [hfour, pow_mul, rootSubgroupPoints_weylWord_sq, ← map_pow, ← Pi.mulSingle_pow]
  simp

end TauCeti.TypeBSpinCarrier
