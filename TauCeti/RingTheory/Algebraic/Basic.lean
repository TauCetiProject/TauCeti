/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Transcendental elements under translations, algebra maps, and automorphisms

Adding a base-ring constant to a transcendental element preserves transcendence, over an
arbitrary commutative ring and in an arbitrary ring algebra. So does applying an injective algebra
homomorphism, the transcendental counterpart of Mathlib's `isAlgebraic_algHom_iff`.
An algebraic extension of scalars without zero divisors also preserves transcendence
under an injective algebra map into a common overring, and so does a nonconstant polynomial
with coefficients in a field, mapped into an algebra (`Transcendental.aeval_map`).
Dually, every root in `A` of a polynomial over `R` is algebraic over `R`
(`isAlgebraic_of_mem_aroots`).
The kernel of an algebra map into a field algebraic over the base field is a maximal ideal
(`AlgHom.ker_isMaximal_of_isAlgebraic`).
Every element of a finite-dimensional left ideal of an algebra over a field is algebraic
(`Submodule.isAlgebraic_of_mem`).
In a domain `A` faithful over `R`, the iterates of an `R`-algebra endomorphism on an algebraic
element eventually collide (`IsAlgebraic.exists_pow_apply_eq_of_algHom`), every algebraic element is
fixed by some positive power of any `R`-algebra automorphism
(`IsAlgebraic.exists_pow_apply_eq_self_of_algEquiv`), and an element moved by every positive power
of an `R`-algebra automorphism is transcendental over `R`
(`AlgEquiv.transcendental_of_forall_pow_algEquiv_ne_self`).
-/

public section

open Polynomial

/-- A root in `A` of a polynomial over `R` is algebraic over `R`. -/
theorem isAlgebraic_of_mem_aroots {R A : Type*} [CommRing R] [CommRing A] [IsDomain A]
    [Algebra R A] {p : R[X]} {x : A} (hx : x ∈ p.aroots A) : IsAlgebraic R x :=
  ⟨p, fun hp ↦ by simp [hp] at hx, (mem_aroots'.1 hx).2⟩

/-- The kernel of an `F`-algebra map into a field algebraic over the field `F` is a maximal
ideal, since the image is a field. -/
theorem AlgHom.ker_isMaximal_of_isAlgebraic {F A E : Type*} [Field F] [CommRing A] [Algebra F A]
    [Field E] [Algebra F E] [Algebra.IsAlgebraic F E] (ψ : A →ₐ[F] E) :
    (RingHom.ker ψ).IsMaximal := by
  let : Field ψ.range := (Subalgebra.isField_of_algebraic ψ.range).toField
  have hker : RingHom.ker ψ.rangeRestrict = RingHom.ker ψ := by
    ext a
    simp [RingHom.mem_ker, Subtype.ext_iff]
  rw [← hker]
  exact RingHom.ker_isMaximal_of_surjective _ ψ.rangeRestrict_surjective

namespace Submodule

/-- Every element of a finite-dimensional left ideal of an algebra over a field, given as a scalar
submodule closed under left multiplication, is algebraic. -/
theorem isAlgebraic_of_mem {K B : Type*} [Field K] [Ring B] [Algebra K B] (J : Submodule K B)
    [FiniteDimensional K J] (hJ : ∀ (b : B) {y : B}, y ∈ J → b * y ∈ J) {x : B} (hxJ : x ∈ J) :
    IsAlgebraic K x := by
  -- `p ↦ p (x) * x` maps the infinite-dimensional `K[X]` into `J`, so it has a nonzero kernel.
  let φ : K[X] →ₗ[K] J := LinearMap.codRestrict J
    (LinearMap.mulRight K x ∘ₗ (aeval x).toLinearMap) fun p ↦ hJ _ hxJ
  obtain ⟨p, hp, hp0⟩ : ∃ p, φ p = 0 ∧ p ≠ 0 := by
    by_contra! h
    exact Polynomial.not_finite (Module.Finite.of_injective φ
      ((injective_iff_map_eq_zero φ).2 h))
  have hpx : aeval x p * x = 0 := congrArg Subtype.val hp
  exact ⟨p * X, mul_ne_zero hp0 X_ne_zero, by rw [map_mul, aeval_X, hpx]⟩

end Submodule

namespace Transcendental

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {x : A}

/-- Translating a transcendental element by a constant keeps it transcendental. -/
theorem add_algebraMap (hx : Transcendental R x) (c : R) :
    Transcendental R (x + algebraMap R A c) := by
  rw [transcendental_iff] at hx ⊢
  intro p hp
  apply (comp_X_add_C_eq_zero_iff (t := c)).mp
  apply hx
  simpa only [aeval_comp, map_add, aeval_X, aeval_C] using hp

/-- An injective algebra homomorphism carries a transcendental element to a transcendental
element. -/
protected theorem algHom {B G : Type*} [Ring B] [Algebra R B] [FunLike G A B] [AlgHomClass G R A B]
    (f : G) (hf : Function.Injective f) (hx : Transcendental R x) : Transcendental R (f x) :=
  (isAlgebraic_algHom_iff (AlgHom.ofClass f) hf).not.mpr hx

/-- An algebraic extension of scalars without zero divisors preserves transcendence after an
injective algebra map into a common overring. -/
theorem algebraMap_of_isAlgebraic {R S A B : Type*}
    [CommRing R] [CommRing S] [NoZeroDivisors S] [CommRing A] [Ring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsAlgebraic R S]
    [FaithfulSMul A B] {x : A} (hx : Transcendental R x) :
    Transcendental S (algebraMap A B x) :=
  ((transcendental_algebraMap_iff (FaithfulSMul.algebraMap_injective A B)).2 hx).extendScalars S

/-- A nonconstant polynomial with coefficients in a field `K`, mapped into a `K`-algebra `R`,
carries an element transcendental over `R` to a transcendental element. -/
theorem aeval_map {K : Type*} [Field K] [Algebra K R] (hx : Transcendental R x)
    {q : K[X]} (hq : 0 < q.natDegree) :
    Transcendental R (Polynomial.aeval x (q.map (algebraMap K R))) := by
  cases subsingleton_or_nontrivial R
  · exact is_transcendental_of_subsingleton (R := R) _
  exact hx.aeval _ (by rw [natDegree_map]; exact hq.ne') (by
    rw [leadingCoeff_map]
    exact IsUnit.mem_nonZeroDivisors <|
      (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hq)).isUnit.map _)

end Transcendental

namespace IsAlgebraic

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- In a domain `A` faithful over `R`, the iterates of an `R`-algebra endomorphism `σ : A →ₐ[R] A`
on an algebraic element `x` eventually repeat. -/
theorem exists_pow_apply_eq_of_algHom {x : A} (hx : IsAlgebraic R x) (σ : A →ₐ[R] A) :
    ∃ i j : ℕ, i < j ∧ (σ ^ i) x = (σ ^ j) x := by
  obtain ⟨p, hp0, hpx⟩ := hx
  have hx_mem : x ∈ p.rootSet A :=
    mem_rootSet'.2 ⟨(Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R A)).2 hp0, hpx⟩
  obtain ⟨i, j, hij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (⟨(σ ^ n) x, rootSet_maps_to' id (σ ^ n) hx_mem⟩ : p.rootSet A))
  rcases lt_or_gt_of_ne hij.1 with hlt | hgt
  · exact ⟨i, j, hlt, congrArg Subtype.val hij.2⟩
  · exact ⟨j, i, hgt, (congrArg Subtype.val hij.2).symm⟩

/-- In a domain `A` faithful over `R`, every element algebraic over `R` is fixed by some nonzero
power of any `R`-algebra automorphism `σ : A ≃ₐ[R] A`. -/
theorem exists_pow_apply_eq_self_of_algEquiv {x : A} (hx : IsAlgebraic R x) (σ : A ≃ₐ[R] A) :
    ∃ n : ℕ, n ≠ 0 ∧ (σ ^ n) x = x := by
  obtain ⟨i, j, hij, heq⟩ := hx.exists_pow_apply_eq_of_algHom σ.toAlgHom
  simp only [AlgHom.coe_pow, AlgEquiv.coe_toAlgHom, ← AlgEquiv.coe_pow] at heq
  refine ⟨j - i, Nat.sub_ne_zero_of_lt hij, (σ ^ i).injective ?_⟩
  rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_of_le hij.le, heq]

end IsAlgebraic

namespace AlgEquiv

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- In a domain `A` faithful over `R`, an element moved by every positive power of an `R`-algebra
automorphism `σ : A ≃ₐ[R] A` is transcendental over `R`. -/
theorem transcendental_of_forall_pow_algEquiv_ne_self (σ : A ≃ₐ[R] A) {x : A}
    (h : ∀ n : ℕ, n ≠ 0 → (σ ^ n) x ≠ x) : Transcendental R x :=
  fun hx ↦ let ⟨n, hn0, hnx⟩ := hx.exists_pow_apply_eq_self_of_algEquiv σ; h n hn0 hnx

end AlgEquiv
