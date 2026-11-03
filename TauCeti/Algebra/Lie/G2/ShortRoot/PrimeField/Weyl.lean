/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Weyl
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Simple Weyl representatives in the characteristic-three G₂ carrier

The short-root G₂ subgroup generated over `𝔽₃` contains the pinned words
`nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)`. They normalize its represented weight torus and act on it by the
numbered simple reflections of the simply connected root datum. They also exchange each positive
simple root subgroup with its opposite, with the sign fixed by that word.

The equations are obtained from the integral seven-dimensional representation by equality of
matrices, not by identifying the generated carrier with the specialization of the integral toral
closure. They hold over arbitrary commutative `𝔽₃`-algebras, including nonreduced ones. They give
normalizer representatives for the root datum and for transporting the numbered root subgroups.
No identification with an independently constructed pinned simply connected group scheme is
asserted.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX.

The root-parameter and torus-action proofs reuse the integral Kostant Weyl equations in
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Weyl`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open DynkinType

universe v w

noncomputable section

local notation "node" => G2.simpleIndex valid_G2

/-- The pinned simple Weyl representative in the carrier generated over `𝔽₃`. -/
def simpleWeylPoint (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The representative is the word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` in the actual generated carrier. -/
theorem simpleWeylPoint_def (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

/-- The generated carrier's representative and the integral carrier's representative are the
same invertible matrix. This asserts no equality of their group schemes. -/
@[simp]
theorem coe_simpleWeylPoint (i : Fin 2) (A : Type v) [CommRing A] [Algebra (ZMod 3) A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) =
      (IntegralToralClosure.simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) := by
  simp only [simpleWeylPoint_def, IntegralToralClosure.simpleWeylPoint_def,
    Subgroup.coe_mul, coe_rootSubgroupPoints]

/-- Simple Weyl representatives are natural in the value algebra. -/
@[simp]
theorem pointsMap_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 3) A] [Algebra (ZMod 3) B] (f : A →ₐ[ZMod 3] B) (i : Fin 2) :
    pointsMap f (simpleWeylPoint i A) = simpleWeylPoint i B := by
  simp only [simpleWeylPoint_def, map_mul, pointsMap_rootSubgroupPoints,
    toAdd_ofAdd, map_one, map_neg]

/-- The simple representative carries its positive simple root subgroup to the negative one,
with parameter negated, over every commutative `𝔽₃`-algebra. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (IntegralToralClosure.simpleWeylPoint_conj_rootSubgroupPoints i A u)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints] using h

/-- Conjugation by the simple representative reflects the weight-torus parameter at the named
simple root and its simple-coroot coordinate. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 2) (A : Type v) [CommRing A]
    [Algebra (ZMod 3) A] (s : Fin 2 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A
        (weylReflectTorusPoint (κ := Fin 2)
          ((G2.simplyConnectedRootDatum valid_G2).root (node i)) i s) := by
  apply Subtype.ext
  have h := congrArg Subtype.val
    (IntegralToralClosure.simpleWeylPoint_conj_weightTorusPoints i A s)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints] using h

/-- Each simple Weyl representative is in the normalizer of the weight torus of the
characteristic-three carrier, with no field or reducedness hypothesis on the value algebra. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 2) (A : Type v)
    [CommRing A] [Algebra (ZMod 3) A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range := by
  -- Conjugation maps the torus onto itself because the reflection is an involution.
  exact (weightTorusPoints A).mem_normalizer_range_of_surjective
    (IntegralToralClosure.weylReflectTorusPoint_root_simpleIndex_involutive i A).surjective
    (simpleWeylPoint_conj_weightTorusPoints i A)

end

end TauCeti.G2ShortRoot.PrimeField
