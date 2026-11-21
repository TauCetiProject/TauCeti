/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Data.Int.Order.Units
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.Tactic.Abel

/-!
# Basic consequences of a signed graded Leibniz rule

This file collects elementary consequences of an `s`-signed graded Leibniz rule on a graded
algebra or ring, independent of any differential or degree-one condition:

`d (a * b) = d a * f b + s i • (f a * d b)` for `a ∈ 𝒜 i`.

In the endomorphism case `f = id`, this is the usual `s`-signed Leibniz rule
`d (a * b) = d a * b + s i • (a * d b)`.

## Main results

* `TauCeti.map_mul_of_leibniz_along_of_map_eq_zero` and
  `TauCeti.map_mul_of_leibniz_of_map_eq_zero`: the signed Leibniz rule against a cycle in the right
  factor holds for an arbitrary left factor.
* `TauCeti.map_one_eq_zero_of_leibniz_along` and `TauCeti.map_one_eq_zero_of_leibniz`: a map
  satisfying an `s`-signed Leibniz rule annihilates `1`.
* `TauCeti.map_algebraMap_of_leibniz_along` and `TauCeti.map_algebraMap_of_leibniz`: a linear map
  satisfying an `s`-signed Leibniz rule annihilates `algebraMap R A r`.
* `TauCeti.map_map_mul_of_leibniz_of_mem` and `TauCeti.map_map_mul_of_leibniz`: when `d` shifts
  degree by `q` and `s (i + q) = -s i`, `d ∘ d` is an unsigned derivation.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.1, for the left-factor
  graded Leibniz convention.
-/

public section

namespace TauCeti

section Leibniz

/-!
### Signed Leibniz against a cycle
-/

/-- An `s`-signed Leibniz rule along `f` against a right factor in the kernel of `d` holds for an
arbitrary left factor, without a homogeneity assumption. -/
theorem map_mul_of_leibniz_along_of_map_eq_zero {A B ι σ F : Type*}
    [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocRing B] [DecidableEq ι]
    [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [DirectSum.Decomposition 𝒜]
    [FunLike F A B] [AddMonoidHomClass F A B] {s : ι → ℤˣ} {d : F} (f : A → B)
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * f b + s i • (f a * d b))
    (a : A) {b : A} (hb : d b = 0) : d (a * b) = d a * f b := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => simp [hl a.property b, hb]
  | add a a' ha ha' => simp [add_mul, ha, ha']

/-- The graded Leibniz rule against a cycle in the right factor, for any index type and sign
family. The vanishing signed term permits an arbitrary left factor, without a homogeneity
hypothesis. -/
theorem map_mul_of_leibniz_of_map_eq_zero {A ι σ F : Type*}
    [NonUnitalNonAssocRing A] [DecidableEq ι]
    [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [DirectSum.Decomposition 𝒜]
    [FunLike F A A] [AddMonoidHomClass F A A] {s : ι → ℤˣ} {d : F}
    (hl : ∀ {p : ι} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * b + s p • (a * d b))
    (a : A) {b : A} (hb : d b = 0) : d (a * b) = d a * b :=
  map_mul_of_leibniz_along_of_map_eq_zero (𝒜 := 𝒜) id hl a hb

end Leibniz

section UnitalLeibniz

/-- A function satisfying an `s`-signed Leibniz rule along a unit-preserving map `f` annihilates
the unit. -/
theorem map_one_eq_zero_of_leibniz_along {A B ι σ F : Type*} [MulOneClass A] [NonAssocRing B]
    [SetLike σ A] [Zero ι] {𝒜 : ι → σ} [SetLike.GradedOne 𝒜] [FunLike F A B] [OneHomClass F A B]
    {s : ι → ℤˣ} (f : F) {d : A → B}
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * f b + s i • (f a * d b)) :
    d 1 = 0 := by
  have key := hl (SetLike.one_mem_graded 𝒜) 1
  simp only [map_one, mul_one, one_mul, left_eq_add] at key
  exact (smul_eq_zero_iff_eq (s 0)).mp key

/-- A function satisfying a graded Leibniz rule with arbitrary unit signs `s : ι → ℤˣ` annihilates
the unit: the rule for `1 * 1` reads `d 1 = d 1 + s 0 • d 1`, hence `s 0 • d 1 = 0` and `d 1 = 0`.
Neither additivity nor a direct-sum decomposition is needed. -/
theorem map_one_eq_zero_of_leibniz {A ι σ : Type*} [NonAssocRing A] [Zero ι] [SetLike σ A]
    (𝒜 : ι → σ) [SetLike.GradedOne 𝒜] {s : ι → ℤˣ} {d : A → A}
    (hl : ∀ {p : ι} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * b + s p • (a * d b)) :
    d 1 = 0 :=
  map_one_eq_zero_of_leibniz_along (𝒜 := 𝒜) (OneHom.id A) hl

end UnitalLeibniz

section AlgebraLeibniz

/-- A linear map satisfying an `s`-signed Leibniz rule along a unit-preserving map `f` annihilates
the image of the ground semiring. Only the unit's degree-zero membership is needed from the
grading. -/
theorem map_algebraMap_of_leibniz_along {R A B ι σ F G : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [NonAssocRing B] [Module R B]
    [Zero ι] [SetLike σ A] {𝒜 : ι → σ} [SetLike.GradedOne 𝒜] {s : ι → ℤˣ}
    [FunLike F A B] [OneHomClass F A B] (f : F) [FunLike G A B] [LinearMapClass G R A B] {d : G}
    (hl : ∀ {p : ι} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * f b + s p • (f a * d b))
    (r : R) : d (algebraMap R A r) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_eq_zero_of_leibniz_along (𝒜 := 𝒜) f hl,
    smul_zero]

/-- A linear map satisfying a graded Leibniz rule with arbitrary unit signs `s : ι → ℤˣ`
annihilates the image of the ground semiring. Only the unit's degree-zero membership is needed from
the grading. -/
theorem map_algebraMap_of_leibniz {R A ι σ F : Type*} [CommSemiring R] [Ring A] [Algebra R A]
    [Zero ι] [SetLike σ A] (𝒜 : ι → σ) [SetLike.GradedOne 𝒜] {s : ι → ℤˣ}
    [FunLike F A A] [LinearMapClass F R A A] {d : F}
    (hl : ∀ {p : ι} {a : A}, a ∈ 𝒜 p → ∀ b : A, d (a * b) = d a * b + s p • (a * d b))
    (r : R) : d (algebraMap R A r) = 0 :=
  map_algebraMap_of_leibniz_along (𝒜 := 𝒜) (OneHom.id A) hl r

end AlgebraLeibniz

section SquareLeibniz

variable {A ι σ F : Type*} [NonUnitalNonAssocRing A] [Add ι] [SetLike σ A] (𝒜 : ι → σ)
  [FunLike F A A] [AddMonoidHomClass F A A] {s : ι → ℤˣ} {q : ι} {d : F}

/-- **The square of an odd-sign Leibniz map satisfies the unsigned Leibniz rule** on any
homogeneous left factor `a ∈ 𝒜 i`: the two middle terms cancel when `s (i + q) = -s i`. -/
theorem map_map_mul_of_leibniz_of_mem
    (hd : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → d a ∈ 𝒜 (i + q))
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    {i : ι} {a : A} (ha : a ∈ 𝒜 i) (hs : s (i + q) = -s i) (b : A) :
    d (d (a * b)) = d (d a) * b + a * d (d b) := by
  have hda := hd ha
  rw [hl ha, map_add, map_zsmul_unit, hl hda, hl ha, hs]
  simp only [Units.smul_def, Units.val_neg, neg_zsmul, zsmul_add, smul_smul,
    ← Units.val_mul, Int.units_mul_self, Units.val_one, one_zsmul]
  abel

/-- **The square of an odd-sign Leibniz map is an unsigned derivation** on the whole algebra:
because the unsigned Leibniz rule has no degree sign, it extends additively from homogeneous left
factors to arbitrary elements. -/
theorem map_map_mul_of_leibniz [DecidableEq ι] [AddSubmonoidClass σ A]
    [DirectSum.Decomposition 𝒜]
    (hd : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → d a ∈ 𝒜 (i + q))
    (hl : ∀ {i : ι} {a : A}, a ∈ 𝒜 i → ∀ b : A, d (a * b) = d a * b + s i • (a * d b))
    (hs : ∀ i, s (i + q) = -s i) (a b : A) :
    d (d (a * b)) = d (d a) * b + a * d (d b) := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a => exact map_map_mul_of_leibniz_of_mem 𝒜 hd hl a.property (hs _) b
  | add x y hx hy =>
    rw [add_mul, map_add, map_add, hx, hy, map_add, map_add, add_mul, add_mul]
    abel

end SquareLeibniz

end TauCeti
