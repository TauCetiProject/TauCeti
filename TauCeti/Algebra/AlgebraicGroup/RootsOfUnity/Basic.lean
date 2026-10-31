/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Basic
import TauCeti.Data.ZMod.MonoidHomEquiv

/-!
# The roots-of-unity group scheme

This file records the functor-of-points calculation for the diagonalizable group
`D(Multiplicative (ZMod n))`. For positive `n`, this is the usual finite diagonalizable group
scheme `μ_n`: for every commutative `R`-algebra `A`, its convolution group of `A`-points is the
group of `n`th roots of unity in `A`.

The result is deliberately just the points calculation. The represented Hopf algebra is the
group algebra `R[Multiplicative (ZMod n)]`; identifying it with the more classical
coordinate ring `R[X]/(X^n - 1)` is separate quotient-polynomial infrastructure
(`TauCeti.RootsOfUnityGroup.adjoinRootEquiv`).

## Main definitions

* `TauCeti.RootsOfUnityGroup.generator_pow_val`: every element of `Multiplicative (ZMod n)` is
  the power of the standard generator given by its `ZMod.val`.
* `TauCeti.RootsOfUnityGroup.generator_pow_eq_one`: the standard cyclic generator is
  `n`-torsion.
* `TauCeti.RootsOfUnityGroup.single_generator_pow_eq_one`: the standard group-algebra generator
  is an `n`th root of unity.
* `TauCeti.RootsOfUnityGroup.characterMulEquivRootsOfUnity`: the multiplicative equivalence from
  characters `Multiplicative (ZMod n) →* Aˣ` to `rootsOfUnity n A`, given by the value on the
  standard generator.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv`: the multiplicative equivalence from
  convolution points of `R[Multiplicative (ZMod n)]` to `rootsOfUnity n A`.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_apply`: the equivalence sends a point to its
  value on the standard generator `single (ofAdd 1) 1`.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator_smul`: the inverse
  equivalence evaluates scalar multiples of the standard generator.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_zmod_val`: the inverse
  equivalence evaluates any cyclic group-algebra generator as the corresponding power of
  the chosen root of unity.
* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator`: the inverse
  equivalence sends a root of unity to the point taking the standard generator to it.
* `TauCeti.RootsOfUnityGroup.algHom_ext`: an algebra map out of the coordinate ring is determined
  by its value on the standard generator.

## References

The diagonalizable-group points calculation is Tau Ceti's
`DiagonalizableGroup.pointsMulEquiv`. The cyclic character group calculation
`characterMulEquivRootsOfUnity` uses Mathlib's
`IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator`, from
`Mathlib.RingTheory.RootsOfUnity.Basic`.
-/

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v

/-- The standard generator of the character group defining `μ_n = D(ℤ/n)`. -/
abbrev generator (n : ℕ) : Multiplicative (ZMod n) :=
  Multiplicative.ofAdd 1

/-- The standard generator of `ℤ/n` is `n`-torsion. -/
@[simp]
theorem generator_pow_eq_one (n : ℕ) : generator n ^ n = 1 := by
  simp [generator, ← ofAdd_nsmul]

/-- The standard group-algebra generator is an `n`th root of unity. -/
@[simp high] -- Simplify the relation before `MonoidAlgebra.single_pow` expands the power.
theorem single_generator_pow_eq_one {R : Type*} [Semiring R] (n : ℕ) :
    MonoidAlgebra.single (generator n) (1 : R) ^ n = 1 := by
  rw [MonoidAlgebra.single_pow, one_pow, generator_pow_eq_one, MonoidAlgebra.one_def]

section Characters

variable {A : Type v} [CommMonoid A]

/-- The characters of `ℤ/n` with values in `Aˣ` are the `n`th roots of unity in `A`, a character
corresponding to its value on the standard generator. -/
noncomputable def characterMulEquivRootsOfUnity (n : ℕ) :
    (Multiplicative (ZMod n) →* Aˣ) ≃* rootsOfUnity n A :=
  let hcard : Nat.card (Multiplicative (ZMod n)) = n :=
    (Nat.card_congr (Multiplicative.ofAdd : ZMod n ≃ Multiplicative (ZMod n))).trans
      (Nat.card_zmod n)
  ((IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator (g := generator n)
      Multiplicative.mem_zpowers_ofAdd_one Aˣ).trans
      (MulEquiv.subgroupCongr (by rw [hcard]))).trans
    (rootsOfUnityUnitsMulEquiv A n)

/-- A character of `ℤ/n` corresponds to its value on the standard generator. -/
@[simp]
lemma characterMulEquivRootsOfUnity_apply (n : ℕ)
    (χ : Multiplicative (ZMod n) →* Aˣ) :
    ((characterMulEquivRootsOfUnity (A := A) n χ : Aˣ) : A) =
      (χ (generator n) : A) := by
  -- once unfolded, the statement is `rfl`: each composed equivalence acts on the underlying unit
  -- by projection
  unfold characterMulEquivRootsOfUnity
  rfl

/-- The character of `ℤ/n` corresponding to an `n`th root of unity `ζ` takes the standard
generator to `ζ`. -/
@[simp]
lemma characterMulEquivRootsOfUnity_symm_apply_generator
    (n : ℕ) (ζ : rootsOfUnity n A) :
    (((characterMulEquivRootsOfUnity (A := A) n).symm ζ (generator n) : Aˣ) : A) =
      ((ζ : Aˣ) : A) := by
  rw [← characterMulEquivRootsOfUnity_apply n
    ((characterMulEquivRootsOfUnity (A := A) n).symm ζ)]
  simp

end Characters

/-- Every element of `Multiplicative (ZMod n)` is the standard generator raised to the `ZMod.val`
of its additive counterpart. -/
lemma generator_pow_val (n : ℕ) [NeZero n] (x : Multiplicative (ZMod n)) :
    generator n ^ (Multiplicative.toAdd x).val = x := by
  rw [generator, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- The functor of points of `μ_n = D(ℤ/n)` is the group of `n`th roots of unity.

The source is the convolution group of `R`-algebra maps out of the group algebra
`R[Multiplicative (ZMod n)]`, and the target is Mathlib's subgroup of units whose `n`th power
is one. -/
noncomputable def pointsMulEquiv (n : ℕ) :
    WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A) ≃*
      rootsOfUnity n A :=
  (DiagonalizableGroup.pointsMulEquiv (R := R) (A := A)
    (G := Multiplicative (ZMod n))).trans (characterMulEquivRootsOfUnity n)

/-- The points equivalence sends a point to its value on the standard generator. -/
@[simp]
lemma pointsMulEquiv_apply (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    ((pointsMulEquiv (R := R) (A := A) n f : Aˣ) : A) =
      f.ofConv (MonoidAlgebra.single (generator n) 1) := by
  rw [pointsMulEquiv, MulEquiv.trans_apply, DiagonalizableGroup.pointsMulEquiv_apply,
    characterMulEquivRootsOfUnity_apply]
  exact DiagonalizableGroup.charOfPoint_apply_coe f.ofConv (generator n)

/-- The value of a power of a point on the standard generator is the power of its value. -/
lemma ofConv_pow_apply_single_generator (n : ℕ)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) (k : ℕ) :
    (f ^ k).ofConv (MonoidAlgebra.single (generator n) 1) =
      f.ofConv (MonoidAlgebra.single (generator n) 1) ^ k := by
  simp only [← pointsMulEquiv_apply, map_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val]

/-- The points equivalence is natural in the value algebra. -/
lemma pointsMulEquiv_mapValue (n : ℕ) (φ : A →ₐ[R] B)
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B) n
        (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ f) =
      restrictRootsOfUnity φ.toMonoidHom n (pointsMulEquiv (R := R) (A := A) n f) := by
  ext
  simp [pointsMulEquiv_apply]

/-- The inverse points equivalence sends a root of unity to the point taking the standard
generator to that root. -/
lemma pointsMulEquiv_symm_apply_single_generator (n : ℕ) (ζ : rootsOfUnity n A) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (generator n) 1) =
      ((ζ : Aˣ) : A) := by
  rw [pointsMulEquiv, MulEquiv.symm_trans_apply,
    DiagonalizableGroup.pointsMulEquiv_symm_apply, ofConv_toConv,
    DiagonalizableGroup.point_single_one,
    characterMulEquivRootsOfUnity_symm_apply_generator]

/-- The inverse points equivalence evaluates scalar multiples of the standard generator by
scalar multiplication of the chosen root of unity. -/
@[simp]
lemma pointsMulEquiv_symm_apply_single_generator_smul (n : ℕ) (ζ : rootsOfUnity n A) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (generator n) r) =
      r • ((ζ : Aˣ) : A) := by
  -- The scalar-action rewrite fixes the coefficient from `r` to `1`, so the existing generator
  -- evaluation lemma applies directly.
  rw [show MonoidAlgebra.single (generator n) r =
      r • MonoidAlgebra.single (generator n) (1 : R) by simp]
  rw [map_smul]
  rw [pointsMulEquiv_symm_apply_single_generator]

/-- The inverse `μ_n` points equivalence evaluates the group-like generator indexed by
`x : Multiplicative (ZMod n)` as the corresponding power of the chosen root of unity.

For `x = generator n`, this specializes to
`RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator`. -/
lemma pointsMulEquiv_symm_apply_single_zmod_val (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (x : Multiplicative (ZMod n)) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single x (1 : R)) =
      ((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) := by
  have hsingle :
      MonoidAlgebra.single x (1 : R) =
        MonoidAlgebra.single (generator n) (1 : R) ^ (Multiplicative.toAdd x).val := by
    rw [MonoidAlgebra.single_pow, one_pow, generator_pow_val]
  rw [hsingle, map_pow, pointsMulEquiv_symm_apply_single_generator]
  rw [Units.val_pow_eq_pow_val]

/-- The inverse `μ_n` points equivalence evaluates scalar multiples of the group-like generator
indexed by `x : Multiplicative (ZMod n)` by scalar multiplication of the corresponding power
of the chosen root of unity. -/
@[simp]
lemma pointsMulEquiv_symm_apply_single_zmod_val_smul (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (x : Multiplicative (ZMod n)) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single x r) =
      r • (((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) : A) := by
  -- The scalar-action rewrite fixes the coefficient from `r` to `1`, so the arbitrary-generator
  -- evaluation lemma applies directly.
  rw [show MonoidAlgebra.single x r = r • MonoidAlgebra.single x (1 : R) by simp]
  rw [map_smul, pointsMulEquiv_symm_apply_single_zmod_val]

/-- The previous normal form, specialized to an additive residue class `j : ZMod n`. -/
lemma pointsMulEquiv_symm_apply_single_ofAdd_val (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (j : ZMod n) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)) =
      ((ζ : Aˣ) ^ j.val : Aˣ) := by
  rw [
    pointsMulEquiv_symm_apply_single_zmod_val (R := R) (A := A) n ζ
      (Multiplicative.ofAdd j), toAdd_ofAdd]

/-- The scalar version of `pointsMulEquiv_symm_apply_single_ofAdd_val`. -/
lemma pointsMulEquiv_symm_apply_single_ofAdd_val_smul (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (j : ZMod n) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd j) r) =
      r • (((ζ : Aˣ) ^ j.val : Aˣ) : A) := by
  rw [
    pointsMulEquiv_symm_apply_single_zmod_val_smul (R := R) (A := A) n ζ
      (Multiplicative.ofAdd j) r, toAdd_ofAdd]

/-- An `R`-algebra map out of the coordinate ring `R[Multiplicative (ZMod n)]` of `μ_n` is
determined by its value on the standard generator. -/
theorem algHom_ext (n : ℕ) {f₁ f₂ : MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] A}
    (h : f₁ (MonoidAlgebra.single (generator n) 1) = f₂ (MonoidAlgebra.single (generator n) 1)) :
    f₁ = f₂ :=
  congrArg ofConv <| (pointsMulEquiv (R := R) (A := A) n).injective <|
    Subtype.ext <| Units.ext <| by simpa only [pointsMulEquiv_apply] using h

/-- Naturality of the inverse `μ_n` points equivalence in the value algebra: post-composing
the point attached to `ζ` gives the point attached to the image of `ζ`. -/
lemma mapValue_pointsMulEquiv_symm_apply (n : ℕ) (φ : A →ₐ[R] B) (ζ : rootsOfUnity n A) :
    AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ
        ((pointsMulEquiv (R := R) (A := A) n).symm ζ) =
      (pointsMulEquiv (R := R) (A := B) n).symm
        (restrictRootsOfUnity φ.toMonoidHom n ζ) := by
  apply (pointsMulEquiv (R := R) (A := B) n).injective
  rw [pointsMulEquiv_mapValue]
  simp

/-- Naturality of the inverse `μ_n` points equivalence, evaluated on an arbitrary cyclic
group-algebra generator. -/
lemma mapValue_pointsMulEquiv_symm_apply_single_zmod_val (n : ℕ) [NeZero n] (φ : A →ₐ[R] B)
    (ζ : rootsOfUnity n A) (x : Multiplicative (ZMod n)) :
    (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ
        ((pointsMulEquiv (R := R) (A := A) n).symm ζ)).ofConv
        (MonoidAlgebra.single x (1 : R)) =
      φ (((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) : A) := by
  rw [mapValue_pointsMulEquiv_symm_apply, pointsMulEquiv_symm_apply_single_zmod_val]
  simp [map_pow]

/-- Naturality of the inverse `μ_n` points equivalence on scalar multiples of arbitrary cyclic
group-algebra generators. -/
lemma mapValue_pointsMulEquiv_symm_apply_single_zmod_val_smul (n : ℕ) [NeZero n] (φ : A →ₐ[R] B)
    (ζ : rootsOfUnity n A) (x : Multiplicative (ZMod n)) (r : R) :
    (AlgHom.mapValue (H := MonoidAlgebra R (Multiplicative (ZMod n))) φ
        ((pointsMulEquiv (R := R) (A := A) n).symm ζ)).ofConv
        (MonoidAlgebra.single x r) =
      φ (r • (((ζ : Aˣ) ^ (Multiplicative.toAdd x).val : Aˣ) : A)) := by
  rw [mapValue_pointsMulEquiv_symm_apply, pointsMulEquiv_symm_apply_single_zmod_val_smul]
  simp [map_pow]

end RootsOfUnityGroup

end TauCeti
