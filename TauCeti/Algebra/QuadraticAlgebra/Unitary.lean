/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Norm-one elements of quadratic algebras under a change of coefficients

The unitary elements of `QuadraticAlgebra R a b` are its elements of norm one
(`QuadraticAlgebra.norm_eq_one_iff_mem_unitary`), the `R`-points of the norm-one group of the
quadratic algebra. A ring homomorphism `f : R →+* S` carrying `a` and `b` to `a'` and `b'` maps
them coefficientwise to norm-one elements of `QuadraticAlgebra S a' b'`: the coefficientwise map
`QuadraticAlgebra.mapRingHom f a b` commutes with conjugation (`QuadraticAlgebra.mapRingHom_star`),
so it is a star monoid homomorphism, and `Unitary.map` restricts it to unitary elements. The
parameters `a'` and `b'` are carried with proofs of `f a = a'` and `f b = b'`, so that the map
applies to algebras whose parameters are, for instance, integers read in `R` and in `S`, where
`f (n : R)` is not syntactically `(n : S)`.

For injective `f`, such as the inclusion `ℤ_p → ℚ_p` or `ℚ → ℚ_p`, the map is injective, and a
norm-one element over `S` comes from `R` exactly when its two coordinates lie in the range of `f`.

## Main definitions

* `QuadraticAlgebra.unitaryMap`: the coefficientwise map on norm-one elements.

## Main results

* `QuadraticAlgebra.unitaryMap_injective`: the map is injective for injective `f`.
* `QuadraticAlgebra.mem_range_unitaryMap_iff`: for injective `f`, its range consists of the
  norm-one elements whose coordinates lie in the range of `f`.
-/

public section

namespace QuadraticAlgebra

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {a b : R} {a' b' : S}

/-- The coefficientwise image of a norm-one element of `QuadraticAlgebra R a b` under a ring
homomorphism `f` with `f a = a'` and `f b = b'` is a norm-one element of `QuadraticAlgebra S a' b'`.
This is the map of `R`-points to `S`-points of the norm-one group. -/
def unitaryMap (ha : f a = a') (hb : f b = b') :
    unitary (QuadraticAlgebra R a b) →* unitary (QuadraticAlgebra S a' b') :=
  (Unitary.map
    { toFun z := ⟨f z.re, f z.im⟩
      map_one' := by subst ha hb; exact map_one (mapRingHom f a b)
      map_mul' z w := by subst ha hb; exact map_mul (mapRingHom f a b) z w
      map_star' z := by subst ha hb; exact mapRingHom_star f a b z }).toMonoidHom

variable {f}

/-- The first coordinate of the image of a norm-one element is the image of its first
coordinate. -/
@[simp]
theorem re_unitaryMap (ha : f a = a') (hb : f b = b') (z : unitary (QuadraticAlgebra R a b)) :
    (unitaryMap f ha hb z : QuadraticAlgebra S a' b').re = f (z : QuadraticAlgebra R a b).re :=
  (rfl)

/-- The second coordinate of the image of a norm-one element is the image of its second
coordinate. -/
@[simp]
theorem im_unitaryMap (ha : f a = a') (hb : f b = b') (z : unitary (QuadraticAlgebra R a b)) :
    (unitaryMap f ha hb z : QuadraticAlgebra S a' b').im = f (z : QuadraticAlgebra R a b).im :=
  (rfl)

/-- For injective `f`, distinct norm-one elements have distinct images. -/
theorem unitaryMap_injective (hf : Function.Injective f) (ha : f a = a') (hb : f b = b') :
    Function.Injective (unitaryMap f ha hb) := by
  subst ha hb
  exact Unitary.map_injective (mapRingHom_injective f a b hf)

/-- **Norm-one elements with coefficients in a subring.** For injective `f`, a norm-one element of
`QuadraticAlgebra S a' b'` is the image of a norm-one element of `QuadraticAlgebra R a b` exactly
when both of its coordinates lie in the range of `f`. -/
theorem mem_range_unitaryMap_iff (hf : Function.Injective f) (ha : f a = a') (hb : f b = b')
    (z : unitary (QuadraticAlgebra S a' b')) :
    z ∈ (unitaryMap f ha hb).range ↔
      (z : QuadraticAlgebra S a' b').re ∈ f.range ∧
        (z : QuadraticAlgebra S a' b').im ∈ f.range := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨⟨_, (re_unitaryMap ha hb w).symm⟩, ⟨_, (im_unitaryMap ha hb w).symm⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    subst ha hb
    have hw : mapRingHom f a b ⟨x, y⟩ = (z : QuadraticAlgebra S (f a) (f b)) := by
      ext
      · exact hx
      · exact hy
    have hn : norm (⟨x, y⟩ : QuadraticAlgebra R a b) = 1 := by
      apply hf
      rw [← norm_mapRingHom, hw, norm_eq_one_iff_mem_unitary.mpr z.property, map_one]
    refine ⟨⟨⟨x, y⟩, norm_eq_one_iff_mem_unitary.mp hn⟩, ?_⟩
    ext
    · exact hx
    · exact hy

end QuadraticAlgebra
