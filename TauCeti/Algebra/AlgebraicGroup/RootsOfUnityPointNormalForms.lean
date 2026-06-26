/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity

/-!
# Normal forms for points of the roots-of-unity group scheme

This file adds pointwise normal forms for the inverse functor-of-points equivalence of
`μ_n = D(ℤ/n)`. The basic file `TauCeti.Algebra.AlgebraicGroup.RootsOfUnity` identifies
convolution points of `R[Multiplicative (ZMod n)]` with `rootsOfUnity n A` by reading the
standard generator. Here we record how the point attached to a chosen root of unity evaluates
on every group-algebra generator, and how that inverse construction is natural in the value
algebra.

These lemmas are a small worked-example API layer for the ReductiveGroups roadmap:
Layer 4 identifies `μ_n` with `D(ℤ/n)`, while Layer 0 develops the functor of points and its
value-algebra functoriality.

## Main declarations

* `TauCeti.RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_zmod_val`: the inverse point
  attached to `ζ` evaluates the generator indexed by `x : Multiplicative (ZMod n)` as the
  corresponding power of `ζ`.
* `TauCeti.RootsOfUnityGroup.mapValue_pointsMulEquiv_symm_apply`: post-composition of the
  inverse point is the inverse point attached to the image root of unity.

## References

The point equivalence is Tau Ceti's `RootsOfUnityGroup.pointsMulEquiv`, built from
`DiagonalizableGroup.pointsMulEquiv`. The cyclic character calculation uses Mathlib's
`IsCyclic.monoidHomMulEquivRootsOfUnityOfGenerator`, as in the base file.
-/

public section

open WithConv

namespace TauCeti

namespace RootsOfUnityGroup

universe u v

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- In `Multiplicative (ZMod n)`, every element is the corresponding natural power of the
standard generator. -/
@[simp]
lemma generator_pow_val (n : ℕ) [NeZero n] (x : Multiplicative (ZMod n)) :
    generator n ^ (Multiplicative.toAdd x).val = x := by
  rw [← ofAdd_nsmul]
  simp only [nsmul_eq_mul, mul_one]
  -- Expose the `ZMod` cast hidden in the additive scalar multiple so that
  -- `ZMod.natCast_zmod_val` applies directly.
  change Multiplicative.ofAdd (((Multiplicative.toAdd x).val : ℕ) : ZMod n) = x
  rw [ZMod.natCast_zmod_val, ofAdd_toAdd]

/-- The inverse `μ_n` points equivalence evaluates the group-like generator indexed by
`x : Multiplicative (ZMod n)` as the corresponding power of the chosen root of unity.

For `x = generator n`, this specializes to
`RootsOfUnityGroup.pointsMulEquiv_symm_apply_single_generator`. -/
@[simp]
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
  rw [show MonoidAlgebra.single x r = r • MonoidAlgebra.single x (1 : R) by simp]
  rw [map_smul, pointsMulEquiv_symm_apply_single_zmod_val]

/-- The previous normal form, specialized to an additive residue class `j : ZMod n`. -/
@[simp]
lemma pointsMulEquiv_symm_apply_single_ofAdd_val (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (j : ZMod n) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd j) (1 : R)) =
      ((ζ : Aˣ) ^ j.val : Aˣ) := by
  rw [
    pointsMulEquiv_symm_apply_single_zmod_val (R := R) (A := A) n ζ
      (Multiplicative.ofAdd j), toAdd_ofAdd]

/-- The scalar version of `pointsMulEquiv_symm_apply_single_ofAdd_val`. -/
@[simp]
lemma pointsMulEquiv_symm_apply_single_ofAdd_val_smul (n : ℕ) [NeZero n] (ζ : rootsOfUnity n A)
    (j : ZMod n) (r : R) :
    ((pointsMulEquiv (R := R) (A := A) n).symm ζ).ofConv
        (MonoidAlgebra.single (Multiplicative.ofAdd j) r) =
      r • (((ζ : Aˣ) ^ j.val : Aˣ) : A) := by
  rw [
    pointsMulEquiv_symm_apply_single_zmod_val_smul (R := R) (A := A) n ζ
      (Multiplicative.ofAdd j) r, toAdd_ofAdd]

variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Naturality of the inverse `μ_n` points equivalence in the value algebra: post-composing
the point attached to `ζ` gives the point attached to the image of `ζ`. -/
@[simp]
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
@[simp]
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
@[simp]
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
