/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic
public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.PointsFunctor

/-!
# Simple Weyl representatives in the F₄ carrier generated over 𝔽₂

The word `xᵢ(1) x₋ᵢ(-1) xᵢ(1)` belongs to the carrier generated over the prime
field because each factor is a named root-subgroup point. Its matrix agrees with the
integral Weyl representative, so the integral conjugation equations give the simple
reflection on the weight torus and the map from the positive simple-root subgroup to its opposite.

These statements hold over all commutative 𝔽₂-algebras. They supply explicit normalizing
points for transporting the numbered simple-root subgroups to other roots; no equality
between the prime-field carrier and the scalar extension of the integral carrier is used.

The formal inputs are `TauCeti.F4ShortRoot.simpleWeylPoint_conj_weightTorusPoints`
and the matrix comparison for the named prime-field root subgroups.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

universe v w

noncomputable section

/-- The pinned simple Weyl word in the carrier generated over 𝔽₂. -/
def simpleWeylPoint (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

/-- The prime-field representative is the specified word in its own pinned generators. -/
theorem simpleWeylPoint_def (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    simpleWeylPoint i A =
      rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) :=
  (rfl)

/-- The Weyl word over 𝔽₂ has the matrix of the corresponding integral Weyl word. -/
@[simp]
theorem coe_simpleWeylPoint (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    (simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 26) A) =
      (F4ShortRoot.simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 26) A) := by
  simp only [simpleWeylPoint_def, Subgroup.coe_mul, coe_rootSubgroupPoints,
    F4ShortRoot.simpleWeylPoint_def]

/-- The representative commutes with every change of 𝔽₂-algebra. -/
@[simp]
theorem pointsMap_simpleWeylPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 2) A] [Algebra (ZMod 2) B] (f : A →ₐ[ZMod 2] B) (i : Fin 4) :
    pointsMap f (simpleWeylPoint i A) = simpleWeylPoint i B := by
  simp [simpleWeylPoint_def]

/-- The pinned representative sends the positive simple-root subgroup to its opposite,
with the integral sign convention retained in characteristic two. -/
@[simp]
theorem simpleWeylPoint_conj_rootSubgroupPoints (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        (simpleWeylPoint i A)⁻¹ =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_rootSubgroupPoints] using
    congrArg Subtype.val (F4ShortRoot.simpleWeylPoint_conj_rootSubgroupPoints i A u)

/-- The prime-field representative acts on the weight torus by the simple reflection of
the simply connected type-F₄ datum. -/
@[simp]
theorem simpleWeylPoint_conj_weightTorusPoints (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (s : Fin 4 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * (simpleWeylPoint i A)⁻¹ =
      weightTorusPoints A
        (DynkinType.F4.geckSimpleReflectionTorusPoint DynkinType.valid_F4 i A s) := by
  apply Subtype.ext
  simpa (config := { instances := true }) only [DynkinType.rank,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_simpleWeylPoint,
    coe_weightTorusPoints] using
    congrArg Subtype.val (F4ShortRoot.simpleWeylPoint_conj_weightTorusPoints i A s)

/-- Each prime-field pinned Weyl representative normalizes the weight torus. -/
theorem simpleWeylPoint_mem_normalizer_weightTorusPoints (i : Fin 4) (A : Type v)
    [CommRing A] [Algebra (ZMod 2) A] :
    simpleWeylPoint i A ∈ Subgroup.normalizer (weightTorusPoints A).range :=
  (weightTorusPoints A).mem_normalizer_range_of_surjective
    (Function.Involutive.surjective
      (DynkinType.F4.geckSimpleReflectionTorusPoint_geckSimpleReflectionTorusPoint
        DynkinType.valid_F4 i A))
    (simpleWeylPoint_conj_weightTorusPoints i A)

end

end TauCeti.F4ShortRoot.PrimeField
