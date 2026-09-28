/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Basic
public import TauCeti.NumberTheory.NumberField.Index.Basic
public import TauCeti.NumberTheory.NumberField.IntrinsicLabel
public import TauCeti.NumberTheory.NumberField.Monogenic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
public import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.ClassNumber.SmallDiscriminant
import TauCeti.NumberTheory.NumberField.Index.Discriminant
import TauCeti.NumberTheory.NumberField.Quadratic.Splitting
import TauCeti.NumberTheory.RamificationInertia.Inert
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Invariants of `ℚ(√5)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1`:

* the discriminant of `X² − X − 1` is `5`, so the index formula
  `discr (minpoly ℤ θ) = index θ ^ 2 · discr K` forces `index θ = 1`: `𝓞 K = ℤ[θ]`, `K` is
  monogenic and `discr K = 5`;
* the discriminant is positive, so both infinite places are real: the signature is `(2, 0)` and
  the intrinsic label prefix is `2.2.5`;
* the discriminant is below the quadratic Minkowski threshold, so `𝓞 K` is a principal ideal
  domain and the class number is `1`;
* `2` is inert: there is a single prime above `2` since `5 ≡ 5 (mod 8)`, and `2` does not ramify
  since it does not divide the discriminant, so that prime has residue degree `2` and is the
  ideal `2 𝓞 K` itself.

## Main results

* `TauCeti.NumberField.Sqrt5.discr_eq_five`: `discr K = 5`.
* `TauCeti.NumberField.Sqrt5.adjoin_eq_top`: `𝓞 K = ℤ[θ]`, and `isMonogenic`.
* `TauCeti.NumberField.Sqrt5.isTotallyReal`, `nrComplexPlaces_eq_zero`, `nrRealPlaces_eq_two`:
  the field is totally real, of signature `(2, 0)`; `hasLMFDBIntrinsicLabel`: the intrinsic
  label prefix is `2.2.5`.
* `TauCeti.NumberField.Sqrt5.isPrincipalIdealRing`, `classNumber_eq_one`: `𝓞 K` is a principal
  ideal domain.
* `TauCeti.NumberField.Sqrt5.ncard_primesOver_two_eq_one`,
  `TauCeti.NumberField.Sqrt5.ramificationIdx_eq_one_of_mem_primesOver_two`,
  `TauCeti.NumberField.Sqrt5.inertiaDeg_eq_two_of_mem_primesOver_two`,
  `TauCeti.NumberField.Sqrt5.isPrime_map_span_two`: `2` is inert.

## References

* The dyadic quadratic splitting law is
  `NumberField.ncard_primesOver_two_eq_one_iff_of_minpoly_eq_X_sq_sub_X_add`, in
  `TauCeti.NumberTheory.NumberField.Quadratic.Splitting`.
-/

public section

open Polynomial NumberField NumberField.InfinitePlace TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- The discriminant of `X² − X − 1` is `5`. -/
@[simp]
theorem discr_X_sq_sub_X_sub_one : (X ^ 2 - X - 1 : ℤ[X]).discr = 5 := by
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [coeff_one, coeff_X]

/-- **The index of a root of `X² − X − 1` is `1`**, since `discr (X² − X − 1) = 5` is squarefree. -/
@[simp]
theorem index_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    IntegralPrimitiveElement.index (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = 1 := by
  apply IntegralPrimitiveElement.index_eq_one_of_squarefree_discr
  simp only [hmin, discr_X_sq_sub_X_sub_one]
  exact Int.squarefree_natAbs.mp Nat.prime_five.squarefree

/-- **The ring of integers of `ℚ(√5)` is `ℤ[θ]`**, for a root `θ` of `X² − X − 1`. -/
@[simp]
theorem adjoin_eq_top (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [← IntegralPrimitiveElement.adjoin_def ⟨θ, hgen⟩]
  exact (IntegralPrimitiveElement.index_eq_one_iff ⟨θ, hgen⟩).mp (index_eq_one hmin hgen)

/-- `ℚ(√5)` is monogenic. -/
theorem isMonogenic (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsMonogenic K :=
  isMonogenic_def.mpr ⟨θ, adjoin_eq_top hmin hgen⟩

/-- **The discriminant of `ℚ(√5)` is `5`.** -/
theorem discr_eq_five (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : NumberField.discr K = 5 := by
  have hd := IntegralPrimitiveElement.discr_minpoly_eq_index_sq_mul_discr ⟨θ, hgen⟩
  rw [hmin, discr_X_sq_sub_X_sub_one, index_eq_one hmin hgen] at hd
  simpa using hd.symm

/-- `ℚ(√5)` is totally real: its discriminant `5` is positive. -/
theorem isTotallyReal (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsTotallyReal K :=
  IsTotallyReal.of_zero_lt_discr (by rw [discr_eq_five hmin hgen]; norm_num)
    (by rw [finrank_eq_two hmin hgen]; norm_num)

/-- `ℚ(√5)` has no complex place. -/
theorem nrComplexPlaces_eq_zero (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : nrComplexPlaces K = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr (isTotallyReal hmin hgen)

/-- `ℚ(√5)` has two real places: its signature is `(2, 0)`. -/
theorem nrRealPlaces_eq_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : nrRealPlaces K = 2 := by
  have := isTotallyReal hmin hgen
  rw [← IsTotallyReal.finrank, finrank_eq_two hmin hgen]

/-- The intrinsic label prefix of `ℚ(√5)` is `2.2.5`. -/
theorem hasLMFDBIntrinsicLabel (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : HasLMFDBIntrinsicLabel K 2 2 5 := by
  rw [hasLMFDBIntrinsicLabel_iff]
  refine ⟨finrank_eq_two hmin hgen, nrRealPlaces_eq_two hmin hgen, ?_⟩
  rw [discr_eq_five hmin hgen]
  norm_num

/-- **`𝓞 K` is a principal ideal domain**: the discriminant `5` is below the quadratic Minkowski
threshold `9` of `isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine`. -/
theorem isPrincipalIdealRing (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsPrincipalIdealRing (𝓞 K) :=
  isPrincipalIdealRing_of_finrank_eq_two_of_natAbs_discr_le_nine (finrank_eq_two hmin hgen)
    (by rw [discr_eq_five hmin hgen]; norm_num)

/-- The class number of `ℚ(√5)` is `1`. -/
theorem classNumber_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : classNumber K = 1 :=
  classNumber_eq_one_iff.mpr (isPrincipalIdealRing hmin hgen)

/-- There is a single prime of `𝓞 K` above `2`, since `5 ≡ 5 (mod 8)`. -/
theorem ncard_primesOver_two_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)).ncard = 1 :=
  (NumberField.ncard_primesOver_two_eq_one_iff_of_minpoly_eq_X_sq_sub_X_add
    (minpoly_eq_X_sq_sub_X_add hmin) hgen (by norm_num)).mpr (by norm_num)

/-- `2` does not ramify in `ℚ(√5)`: it does not divide the discriminant `5`. -/
theorem two_notMem_ramifiedPrimes (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 2 ∉ ramifiedPrimes K := by
  rw [mem_ramifiedPrimes_iff_dvd_discr Nat.prime_two, discr_eq_five hmin hgen]
  norm_num

/-- **`2` is unramified in `ℚ(√5)`**: every prime above `2` has ramification index `1`. -/
theorem ramificationIdx_eq_one_of_mem_primesOver_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {Q : Ideal (𝓞 K)}
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) : Q.ramificationIdx ℤ = 1 := by
  have hQp : Q.IsPrime := hQ.1
  have hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) := by
    by_contra h
    exact two_notMem_ramifiedPrimes hmin hgen (mem_ramifiedPrimes_iff.mpr ⟨Nat.prime_two, h⟩)
  exact hunr.ramificationIdx_eq_one hQ.2

/-- **`2` is inert in `ℚ(√5)`**: the single prime above `2` has residue degree `2`. -/
theorem inertiaDeg_eq_two_of_mem_primesOver_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {Q : Ideal (𝓞 K)}
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) : Q.inertiaDeg ℤ = 2 := by
  have := hQ.1
  have := hQ.2
  have hpr : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible).isPrime
  rw [TauCeti.RamificationInertia.inertiaDeg_eq_finrank_of_ncard_primesOver_eq_one _ Q
    (ncard_primesOver_two_eq_one hmin hgen)
    (ramificationIdx_eq_one_of_mem_primesOver_two hmin hgen hQ), RingOfIntegers.rank,
    finrank_eq_two hmin hgen]

/-- **`2` is inert in `ℚ(√5)`**: the ideal `2 𝓞 K` is the single prime above `2`. -/
theorem map_span_two_eq_of_mem_primesOver (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {Q : Ideal (𝓞 K)}
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) :
    (Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Q := by
  have := hQ.1
  have := hQ.2
  have hmax : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  exact TauCeti.RamificationInertia.map_eq_of_ncard_primesOver_eq_one _ (by simp) Q
    (ncard_primesOver_two_eq_one hmin hgen)
    (ramificationIdx_eq_one_of_mem_primesOver_two hmin hgen hQ)

/-- **`2` is inert in `ℚ(√5)`**: the ideal `2 𝓞 K` is prime. -/
theorem isPrime_map_span_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    ((Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 K))).IsPrime := by
  obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp (ncard_primesOver_two_eq_one hmin hgen)
  have hQm : Q ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K) := by
    rw [hQ]; exact Set.mem_singleton Q
  rw [map_span_two_eq_of_mem_primesOver hmin hgen hQm]
  exact hQm.1

end TauCeti.NumberField.Sqrt5
