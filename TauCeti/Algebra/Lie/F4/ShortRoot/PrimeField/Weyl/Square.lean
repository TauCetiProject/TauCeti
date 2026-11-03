/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.PrimeField.Weyl.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Involutive Weyl representatives in the short-root F₄ carrier over 𝔽₂

The pinned representative `nᵢ = xᵢ(1) x₋ᵢ(-1) xᵢ(1)` is an involution over every
commutative 𝔽₂-algebra: its integral square is the simple coroot at `-1`, which becomes
the identity in characteristic two. Consequently reversing any Weyl word gives its inverse.
These equations control cancellation of repeated simple reflections when transporting root
subgroups. They do not assert independence of the chosen word for an abstract Weyl element.

The proof uses `TauCeti.F4ShortRoot.simpleWeylPoint_sq` on the admissible
26-dimensional integral lattice and the existing matrix comparison. No identification of
the generated prime-field carrier with the specialization of the integral closure is needed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.F4ShortRoot.PrimeField

universe v

noncomputable section

/-- Each pinned simple Weyl representative has square one over every 𝔽₂-algebra. -/
@[simp]
theorem simpleWeylPoint_sq (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    simpleWeylPoint i A ^ 2 = 1 := by
  have hsign : (-1 : Aˣ) = 1 := by
    apply Units.ext
    simpa only [Units.val_neg, Units.val_one, map_neg, map_one] using
      congrArg (algebraMap (ZMod 2) A) (CharTwo.neg_one_eq_one (R := ZMod 2))
  have htorus : (Pi.mulSingle i (-1) : Fin 4 → Aˣ) = 1 := by
    rw [hsign, Pi.mulSingle_one]
  apply Subtype.ext
  simpa only [Subgroup.coe_pow, coe_simpleWeylPoint, Subgroup.coe_one, htorus, map_one] using
    congrArg Subtype.val (F4ShortRoot.simpleWeylPoint_sq i A)

/-- The pinned simple Weyl representatives are their own inverses in characteristic two. -/
@[simp]
theorem simpleWeylPoint_inv (i : Fin 4) (A : Type v) [CommRing A] [Algebra (ZMod 2) A] :
    (simpleWeylPoint i A)⁻¹ = simpleWeylPoint i A :=
  inv_eq_of_mul_eq_one_right (by rw [← sq, simpleWeylPoint_sq])

/-- In characteristic two, the inverse-free pinned conjugation sends a positive simple-root
subgroup to its opposite, retaining the integral sign convention. -/
@[simp]
theorem simpleWeylPoint_mul_rootSubgroupPoints_mul_self (i : Fin 4) (A : Type v)
    [CommRing A] [Algebra (ZMod 2) A] (u : A) :
    simpleWeylPoint i A * rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd u) *
        simpleWeylPoint i A =
      rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-u)) := by
  simpa only [simpleWeylPoint_inv] using simpleWeylPoint_conj_rootSubgroupPoints i A u

/-- In characteristic two, the inverse-free pinned conjugation acts on the weight torus
by the simple reflection. -/
@[simp]
theorem simpleWeylPoint_mul_weightTorusPoints_mul_self (i : Fin 4) (A : Type v)
    [CommRing A] [Algebra (ZMod 2) A] (s : Fin 4 → Aˣ) :
    simpleWeylPoint i A * weightTorusPoints A s * simpleWeylPoint i A =
      weightTorusPoints A
        (DynkinType.F4.geckSimpleReflectionTorusPoint DynkinType.valid_F4 i A s) := by
  simpa only [simpleWeylPoint_inv] using simpleWeylPoint_conj_weightTorusPoints i A s

/-- Two equal adjacent pinned simple Weyl representatives cancel in characteristic two. -/
@[simp]
theorem simpleWeylPoint_mul_self (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    simpleWeylPoint i A * simpleWeylPoint i A = 1 := by
  rw [← sq, simpleWeylPoint_sq]

/-- Equal adjacent pinned simple Weyl representatives cancel before any remaining factor. -/
@[simp]
theorem simpleWeylPoint_mul_self_mul (i : Fin 4) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] (g : points A) :
    simpleWeylPoint i A * (simpleWeylPoint i A * g) = g := by
  rw [← mul_assoc, simpleWeylPoint_mul_self, one_mul]

/-- Reversing a Weyl word in characteristic two gives its inverse. This does not assert
independence of the chosen word representing an abstract Weyl-group element. -/
@[simp]
theorem weylWordPoint_reverse (l : List (Fin 4)) (A : Type v) [CommRing A]
    [Algebra (ZMod 2) A] :
    weylWordPoint l.reverse A = (weylWordPoint l A)⁻¹ := by
  induction l with
  | nil => simp only [List.reverse_nil, weylWordPoint_nil, inv_one]
  | cons i l ih =>
    simp only [List.reverse_cons, weylWordPoint_append, weylWordPoint_cons,
      weylWordPoint_nil, mul_one, ih, mul_inv_rev, simpleWeylPoint_inv]

end

end TauCeti.F4ShortRoot.PrimeField
