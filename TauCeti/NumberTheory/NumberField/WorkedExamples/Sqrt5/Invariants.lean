/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.WorkedExamples.Sqrt5.Basic
public import TauCeti.NumberTheory.NumberField.Monogenic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.NumberTheory.NumberField.RamifiedPrimes
import TauCeti.NumberTheory.NumberField.Index.Discriminant
import TauCeti.NumberTheory.NumberField.Quadratic.Splitting
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Invariants of `ℚ(√5)`

For `K` generated over `ℚ` by an algebraic integer `θ` with `minpoly ℤ θ = X² − X − 1`:

* the discriminant of `X² − X − 1` is `5`, so the index formula
  `discr (minpoly ℤ θ) = index θ ^ 2 · discr K` forces `index θ = 1`: `𝓞 K = ℤ[θ]`, `K` is
  monogenic and `discr K = 5`;
* `2` is inert: there is a single prime above `2` since `5 ≡ 5 (mod 8)`, and `2` does not ramify
  since it does not divide the discriminant, so that prime has residue degree `2` and is the
  ideal `2 𝓞 K` itself.

## Main results

* `TauCeti.NumberField.Sqrt5.discr_eq_five`: `discr K = 5`.
* `TauCeti.NumberField.Sqrt5.adjoin_eq_top`: `𝓞 K = ℤ[θ]`, and `isMonogenic`.
* `TauCeti.NumberField.Sqrt5.ncard_primesOver_two_eq_one`,
  `TauCeti.NumberField.Sqrt5.inertiaDeg_eq_two_of_mem_primesOver_two`,
  `TauCeti.NumberField.Sqrt5.isPrime_map_span_two`: `2` is inert.
-/

public section

open Polynomial NumberField TauCeti.NumberField
open scoped NumberField

namespace TauCeti.NumberField.Sqrt5

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- The discriminant of `X² − X − 1` is `5`. -/
theorem discr_X_sq_sub_X_sub_one : (X ^ 2 - X - 1 : ℤ[X]).discr = 5 := by
  rw [discr_of_degree_eq_two (by compute_degree!)]
  simp [coeff_one, coeff_X]

/-- **The index of the golden ratio is `1`**, since `discr (X² − X − 1) = 5` is squarefree. -/
theorem index_eq_one (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    IntegralPrimitiveElement.index (⟨θ, hgen⟩ : IntegralPrimitiveElement K) = 1 := by
  set ϑ : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  have h := ϑ.discr_minpoly_eq_index_sq_mul_discr
  rw [show ϑ.1 = θ from rfl, hmin, discr_X_sq_sub_X_sub_one] at h
  -- `index ^ 2` divides `5`, so the index is `1`.
  have hdvd : ϑ.index ^ 2 ∣ 5 := by
    have : ((ϑ.index ^ 2 : ℕ) : ℤ) ∣ 5 := ⟨NumberField.discr K, by push_cast; exact h⟩
    exact_mod_cast this
  have hle : ϑ.index ≤ 2 := by nlinarith [Nat.le_of_dvd (by norm_num) hdvd]
  have hpos := ϑ.index_pos
  interval_cases hi : ϑ.index
  · rfl
  · norm_num at h
    omega

/-- **The ring of integers of `ℚ(√5)` is `ℤ[θ]`**, for `θ = (1 + √5)/2`. -/
theorem adjoin_eq_top (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Algebra.adjoin ℤ {θ} = ⊤ := by
  have h : Algebra.adjoin ℤ {(⟨θ, hgen⟩ : IntegralPrimitiveElement K).1} = ⊤ :=
    (IntegralPrimitiveElement.adjoin_def ⟨θ, hgen⟩).symm.trans
      ((IntegralPrimitiveElement.index_eq_one_iff ⟨θ, hgen⟩).mp (index_eq_one hmin hgen))
  exact h

/-- `ℚ(√5)` is monogenic. -/
theorem isMonogenic (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : IsMonogenic K :=
  isMonogenic_def.mpr ⟨θ, adjoin_eq_top hmin hgen⟩

/-- **The discriminant of `ℚ(√5)` is `5`.** -/
theorem discr_eq_five (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : NumberField.discr K = 5 := by
  let ϑ : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  have h := ϑ.discr_minpoly_eq_index_sq_mul_discr
  rwa [show ϑ.1 = θ from rfl, hmin, discr_X_sq_sub_X_sub_one, index_eq_one hmin hgen,
    Nat.cast_one, one_pow, one_mul, eq_comm] at h

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

/-- **`2` is inert in `ℚ(√5)`**: the single prime above `2` has residue degree `2`. -/
theorem inertiaDeg_eq_two_of_mem_primesOver_two (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {Q : Ideal (𝓞 K)}
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) : Q.inertiaDeg ℤ = 2 := by
  classical
  -- `2` is unramified, so `e = 1`, and the fundamental identity `Σ e f = 2` over the single
  -- prime above `2` gives `f = 2`.
  have hmax : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  have hpr : (Ideal.span {(2 : ℤ)}).IsPrime := hmax.isPrime
  have hQp : Q.IsPrime := hQ.1
  have hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) := by
    by_contra h
    exact two_notMem_ramifiedPrimes hmin hgen (mem_ramifiedPrimes_iff.mpr ⟨Nat.prime_two, h⟩)
  have he : Q.ramificationIdx ℤ = 1 := hunr.ramificationIdx_eq_one hQ.2
  obtain ⟨Q', hQ'⟩ := Set.ncard_eq_one.mp (ncard_primesOver_two_eq_one hmin hgen)
  have hsub : Subsingleton (Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) := by
    rw [hQ']; infer_instance
  have hfin : Fintype (Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) := by
    rw [hQ']; infer_instance
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (R := ℤ) (S := 𝓞 K)
    (p := Ideal.span {(2 : ℤ)})
  rwa [Fintype.sum_subsingleton _ ⟨Q, hQ⟩, he, one_mul, RingOfIntegers.rank,
    finrank_eq_two hmin hgen] at hsum

/-- **`2` is inert in `ℚ(√5)`**: the ideal `2 𝓞 K` is the single prime above `2`. -/
theorem map_span_two_eq_of_mem_primesOver (hmin : minpoly ℤ θ = X ^ 2 - X - 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {Q : Ideal (𝓞 K)}
    (hQ : Q ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) :
    (Ideal.span {(2 : ℤ)}).map (algebraMap ℤ (𝓞 K)) = Q := by
  classical
  have hmax : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  have hQp : Q.IsPrime := hQ.1
  have hunr : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(2 : ℤ)}) := by
    by_contra h
    exact two_notMem_ramifiedPrimes hmin hgen (mem_ramifiedPrimes_iff.mpr ⟨Nat.prime_two, h⟩)
  have he : Q.ramificationIdx ℤ = 1 := hunr.ramificationIdx_eq_one hQ.2
  obtain ⟨Q', hQ'⟩ := Set.ncard_eq_one.mp (ncard_primesOver_two_eq_one hmin hgen)
  have hQQ : Q = Q' := by rw [hQ'] at hQ; exact hQ
  rw [Ideal.map_algebraMap_eq_finsetProd_pow (by simp), Finset.prod_eq_single Q]
  · rw [he, pow_one]
  · intro P hP hPQ
    rw [Set.mem_toFinset, hQ'] at hP
    exact absurd ((Set.mem_singleton_iff.mp hP).trans hQQ.symm) hPQ
  · intro hQn
    exact absurd (Set.mem_toFinset.mpr hQ) hQn

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
