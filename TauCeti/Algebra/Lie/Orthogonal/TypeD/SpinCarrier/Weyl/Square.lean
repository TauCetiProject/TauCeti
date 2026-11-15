/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.SpinCarrier.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Weyl squares in the full-weight type-D spin carrier

For each Bourbaki node and every unit `u` of a commutative value ring, the pinned word
`xᵢ(u) x₋ᵢ(-u⁻¹) xᵢ(u)` squares to the simple-coroot value at `-1` in the spin weight torus.
Consequently its fourth power is the identity. These are relations in the actual carrier,
including in characteristic two and over nonreduced rings; no exact order is asserted.

The square relation identifies the coroot normalization of the opposite-root word. The carrier
is not identified with an independently pinned simply connected group scheme of type `Dₙ`;
constructions transfer to that group only along such an identification.

## Main declarations

* `rootSubgroupPoints_mul_mul_sq`: the unit-parameter Weyl word squares to its coroot at `-1`.
* `rootSubgroupPoints_mul_mul_pow_four`: the same word has fourth power one.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.

The proof transports `TauCeti.UniversalEnvelopingAlgebra.kostantWeylParam_sq` through the
existing spin lattice basis, using the represented type-D `sl₂` triples and integral weights.
-/

public section

namespace TauCeti.TypeDSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

noncomputable section

universe v

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (hn : 4 ≤ n) (A : Type v) [CommRing A]

/-- The pinned opposite-root word at any unit parameter squares to the numbered simple-coroot
value at `-1` in the full-spin weight torus. -/
@[simp↓]
theorem rootSubgroupPoints_mul_mul_sq (i : Fin n) (u : Aˣ) :
    (rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 2 =
      weightTorusPoints n hn A (Pi.mulSingle i (-1)) := by
  have hneg (j : Fin n) :
      ⁅serreH ℚ (CartanMatrix.D n) j, serreRootGenerator (CartanMatrix.D n) (.inr i)⁆ =
        -((TypeDStd.rootGeneratorWeight n (.inl i) j : ℚ) •
          serreRootGenerator (CartanMatrix.D n) (.inr i)) := by
    simpa using TypeDStd.lie_serreH_serreRootGenerator n (.inr i) j
  have h := kostantWeylParam_sq
    (serreRootGenerator (CartanMatrix.D n)) (serreH ℚ (CartanMatrix.D n))
    (rep n hn) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn (.inl i))
    (isNilpotent_rep_rootGenerator n hn (.inr i))
    (latticeBasis n) (basisWeight n) (isCartanWeightVector_latticeBasis n hn)
    (isSl2Triple_rep_rootGenerator n hn i)
    (TypeDStd.lie_serreH_serreRootGenerator n (.inl i)) hneg (CommAlgCat.of ℤ A) u
  -- Pass from automorphisms of the base-changed lattice to their matrices in its named basis.
  have hm := congrArg
    (Units.map (LinearMap.toMatrixAlgEquiv ((latticeBasis n).baseChange A)).toMonoidHom) h
  simp only [kostantWeylParam_def, kostantCoordinateCocharacter_apply, map_pow, map_mul,
    MulEquiv.toMonoidHom_eq_coe,
    basisMatrix_kostantRootSubgroupParam
      (serreRootGenerator (CartanMatrix.D n)) (serreH ℚ (CartanMatrix.D n))
      (rep n hn) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n)] at hm
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints,
    basisMatrix_kostantTorusPoints, MulEquiv.toMonoidHom_eq_coe] using hm

/-- Every unit-parameter pinned Weyl word in the spin carrier has fourth power one. This does
not assert exact order four, which can fail in characteristic two. -/
@[simp↓]
theorem rootSubgroupPoints_mul_mul_pow_four (i : Fin n) (u : Aˣ) :
    (rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A)) *
        rootSubgroupPoints n hn (.inr i) A (Multiplicative.ofAdd (-((u⁻¹ : Aˣ) : A))) *
        rootSubgroupPoints n hn (.inl i) A (Multiplicative.ofAdd (u : A))) ^ 4 = 1 := by
  have hfour : (4 : ℕ) = 2 * 2 := rfl
  rw [hfour, pow_mul, rootSubgroupPoints_mul_mul_sq, ← map_pow, ← Pi.mulSingle_pow]
  simp

end

end TauCeti.TypeDSpinCarrier
