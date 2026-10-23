/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.RegularLocalRing.Node.Basic
public import TauCeti.RingTheory.KrullDimension.Polynomial

/-!
# Dimension and embedding dimension at a thick node

Over a discrete valuation ring, the local ring of `xy = πⁿ` at the closed origin has
Krull dimension two. For `n ≥ 2` its maximal ideal needs exactly three generators:
the equation belongs to the square of the ambient maximal ideal and therefore imposes
no linear relation on the cotangent space. These calculations explain the failure of
regularity at thick nodes in models of curves.

The dimension calculation only needs `π` in the maximal ideal, not that it generate it.

## References

* The Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

namespace TauCeti.NodeAlgebra

open _root_.IsLocalRing Ideal MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

/-- The closed-origin local ring of `xy = πⁿ` over a DVR has Krull dimension two.
The primality hypothesis excludes `n = 0`, when the origin is absent. -/
theorem ringKrullDim_localization_origin (hπ : π ∈ maximalIdeal R) (n : ℕ)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (mk (π ^ n)).toRingHom).IsPrime] :
    ringKrullDim (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (mk (π ^ n)).toRingHom)) = 2 := by
  let B := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R))
  let f := algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))
  have hn : n ≠ 0 := (isPrime_map_quotient_X_mul_X_sub_C_pow_iff hπ n).mp inferInstance
  have hmem (p : MvPolynomial (Fin 2) R) (hp : constantCoeff p ∈ maximalIdeal R) :
      algebraMap (MvPolynomial (Fin 2) R) B p ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B
      ((maximalIdeal R).comap constantCoeff) p).mpr hp
  have hfm : f ∈ maximalIdeal B := hmem _ (by simpa [hn] using hπ)
  have hf : f ≠ 0 := by
    intro hz
    have h : X 0 * X 1 - C (π ^ n) = (0 : MvPolynomial (Fin 2) R) :=
      IsLocalization.injective B
        (primeCompl_le_nonZeroDivisors ((maximalIdeal R).comap constantCoeff))
        (by simpa only [f, map_zero] using hz)
    have := congrArg (fun p : MvPolynomial (Fin 2) R ↦
      p.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) h
    simp only [coeff_sub, coeff_X_mul, coeff_X, coeff_C] at this
    norm_num [eq_comm, Finsupp.add_eq_zero_iff] at this
  have hdim : ringKrullDim B = 3 := by
    norm_num [B, ringKrullDim_localization_comap_constantCoeff,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hf) hfm
  rw [hdim] at hdrop
  have hquot : ringKrullDim (B ⧸ span {f}) = 2 := by
    apply ENat.WithBot.add_one_cancel.mp
    convert hdrop using 1
    norm_num
  rw [ringKrullDim_eq_of_ringEquiv (S := B ⧸ span {f}) (localizationOriginEquiv hπ n)]
  exact hquot

/-- At a node of thickness at least two over a DVR, the maximal ideal of the local ring at
the closed origin has minimal number of generators three. -/
theorem spanFinrank_maximalIdeal_localization_origin (hπ : π ∈ maximalIdeal R) (n : ℕ)
    (hn : 2 ≤ n)
    [(((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (mk (π ^ n)).toRingHom).IsPrime] :
    (maximalIdeal (Localization.AtPrime
      (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
        (mk (π ^ n)).toRingHom))).spanFinrank = 3 := by
  let B := Localization.AtPrime ((maximalIdeal R).comap
    (constantCoeff : MvPolynomial (Fin 2) R →+* R))
  let f := algebraMap (MvPolynomial (Fin 2) R) B (X 0 * X 1 - C (π ^ n))
  let A := Localization.AtPrime
    (((maximalIdeal R).comap (constantCoeff : MvPolynomial (Fin 2) R →+* R)).map
      (mk (π ^ n)).toRingHom)
  let e : A ≃+* (B ⧸ span {f}) := localizationOriginEquiv hπ n
  have : IsLocalRing (B ⧸ span {f}) := e.isLocalRing
  have hmem (p : MvPolynomial (Fin 2) R) (hp : constantCoeff p ∈ maximalIdeal R) :
      algebraMap (MvPolynomial (Fin 2) R) B p ∈ maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B
      ((maximalIdeal R).comap constantCoeff) p).mpr hp
  have hX (i : Fin 2) : algebraMap (MvPolynomial (Fin 2) R) B (X i) ∈ maximalIdeal B :=
    hmem _ (by simp)
  have hC : algebraMap (MvPolynomial (Fin 2) R) B (C π) ∈ maximalIdeal B :=
    hmem _ (by simpa using hπ)
  have hf : f ∈ maximalIdeal B ^ 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [f, map_sub, map_mul, map_pow, pow_add, pow_two]
    exact sub_mem (mul_mem_mul (hX 0) (hX 1))
      (mul_mem_right _ _ (mul_mem_mul hC hC))
  have hspan := TauCeti.IsLocalRing.spanFinrank_map_maximalIdeal_quotient_of_le_sq
    (maximalIdeal B).fg_of_isNoetherianRing ((span_singleton_le_iff_mem _).mpr hf)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hspan
  have hdim : ringKrullDim B = 3 := by
    norm_num [B, ringKrullDim_localization_comap_constantCoeff,
      IsDiscreteValuationRing.ringKrullDim_eq_one]
  have : IsRegularLocalRing B :=
    _root_.IsRegularLocalRing.of_isRegularRing_of_isLocalRing B
  have hB : (maximalIdeal B).spanFinrank = 3 := by
    have := _root_.IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)
    rw [hdim] at this
    exact_mod_cast this
  have hmap := map_ringEquiv_maximalIdeal (R := A) (S := B ⧸ span {f}) e
  have he := Ideal.spanFinrank_map_eq_of_ringEquiv e (maximalIdeal A)
  rw [hmap] at he
  exact he.symm.trans (hspan.trans hB)

end TauCeti.NodeAlgebra
