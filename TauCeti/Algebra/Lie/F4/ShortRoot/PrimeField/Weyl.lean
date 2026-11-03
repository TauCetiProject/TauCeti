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
points for transporting the numbered simple-root subgroups to other roots. Their products
`weylWordPoint` along words agree with the integral Weyl words and commute with change of
coefficient algebra. No equality between the prime-field carrier and the scalar extension
of the integral carrier is used.

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

/-- The product of the pinned Weyl representatives along a word. -/
def weylWordPoint (l : List (Fin 4)) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    points A :=
  (l.map fun i ↦ simpleWeylPoint i A).prod

/-- The empty Weyl word represents the identity. -/
@[simp]
theorem weylWordPoint_nil (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    weylWordPoint [] A = 1 := by
  simp [weylWordPoint]

/-- Prepending a node multiplies its representative on the left. -/
@[simp]
theorem weylWordPoint_cons (i : Fin 4) (l : List (Fin 4)) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    weylWordPoint (i :: l) A = simpleWeylPoint i A * weylWordPoint l A := by
  simp [weylWordPoint]

/-- Concatenation of words multiplies their representatives. -/
@[simp]
theorem weylWordPoint_append (l l' : List (Fin 4)) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    weylWordPoint (l ++ l') A = weylWordPoint l A * weylWordPoint l' A := by
  simp only [weylWordPoint, List.map_append, List.prod_append]

/-- The prime-field Weyl word has the matrix of the integral Weyl word. -/
@[simp]
theorem coe_weylWordPoint (l : List (Fin 4)) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    (weylWordPoint l A : Matrix.GeneralLinearGroup (Fin 26) A) =
      (F4ShortRoot.weylWordPoint l A : Matrix.GeneralLinearGroup (Fin 26) A) := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

/-- Conjugation by a Weyl word realizes its abstract action on the weight torus. -/
@[simp]
theorem weylWordPoint_conj_weightTorusPoints (l : List (Fin 4)) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (s : Fin 4 → Aˣ) :
    weylWordPoint l A * weightTorusPoints A s * (weylWordPoint l A)⁻¹ =
      weightTorusPoints A
        (DynkinType.F4.geckWeylWordTorusAction DynkinType.valid_F4 l A s) := by
  apply Subtype.ext
  simpa (config := { instances := true }) only [DynkinType.rank,
    Subgroup.coe_mul, Subgroup.coe_inv, coe_weylWordPoint,
    coe_weightTorusPoints] using
    congrArg Subtype.val (F4ShortRoot.weylWordPoint_conj_weightTorusPoints l A s)

/-- Every prime-field Weyl word normalizes the weight torus. -/
theorem weylWordPoint_mem_normalizer_weightTorusPoints (l : List (Fin 4))
    (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    weylWordPoint l A ∈ Subgroup.normalizer (weightTorusPoints A).range := by
  rw [weylWordPoint]
  exact Subgroup.list_prod_mem _ (List.forall_mem_map.2 fun i _ ↦
    simpleWeylPoint_mem_normalizer_weightTorusPoints i A)

/-- Weyl words commute with change of coefficient algebra. -/
@[simp↓]
theorem pointsMap_weylWordPoint {A : Type v} {B : Type w} [CommRing A] [CommRing B]
    [Algebra (ZMod 2) A] [Algebra (ZMod 2) B] (f : A →ₐ[ZMod 2] B) (l : List (Fin 4)) :
    pointsMap f (weylWordPoint l A) = weylWordPoint l B := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

end

end TauCeti.F4ShortRoot.PrimeField
