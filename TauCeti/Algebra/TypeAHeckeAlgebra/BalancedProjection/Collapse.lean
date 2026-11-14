/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Balanced projections in C⋆-algebras outside the interval `[0, 1)`

The balanced projection algebra `TauCeti.BalancedProjectionAlgebra R τ` is presented by idempotents
`e i` whose adjacent defects `e i * e (i + 1) * e i - τ • e i` and
`e (i + 1) * e i * e (i + 1) - τ • e (i + 1)` agree. When `τ * (q + q⁻¹) ^ 2 = 1` for a unit `q`
it is the infinite type-A Hecke algebra. This file treats instead its representations by
projections in a C⋆-algebra when `τ` is not in the half-open interval `[0, 1)`.

For idempotents `p` and `q` satisfying the balanced relation, the difference `d = p - q` satisfies
`d ^ 3 = (1 - τ) • d` (`IsIdempotentElem.sub_pow_three_eq_smul`). If `p` and `q` are projections in
a C⋆-algebra, `d` is self-adjoint and `-1 ≤ d ≤ 1`, so its spectrum lies in `[-1, 1]` and consists
of roots of `x ^ 3 - (1 - τ) * x`. For real `τ` outside `[0, 1)` the only such root is `0`, so
`d = 0`. For non-real `τ`, comparing the balanced relation with its adjoint already gives `p = q`.
Hence:

* for `τ ∉ [0, 1)`, every representation of the balanced projection algebra over `ℂ` by
  projections in a C⋆-algebra sends all generators to one projection `P`, so it factors through
  the two scalar characters `e i ↦ 1` and `e i ↦ 0`
  (`TauCeti.BalancedProjectionAlgebra.map_eq_character_smul_add_character_smul`);
* consequently, a normalized functional obeying the Markov rule with parameter `η` through such a
  representation has `η ∈ {0, 1}` and is the corresponding scalar character
  (`TauCeti.BalancedProjectionAlgebra.apply_map_eq_character_of_markov`).

The endpoint `τ = 0` is treated in `TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Zero`.

## Main results

* `IsSelfAdjoint.eq_of_mul_mul_sub_smul_eq_of_star_ne`: self-adjoint elements satisfying the
  balanced relation with a non-self-adjoint parameter coincide.
* `IsStarProjection.eq_of_mul_mul_sub_smul_eq_of_notMem_image_Ico`: balanced projections in a
  C⋆-algebra coincide when `τ ∉ [0, 1)`.
* `TauCeti.BalancedProjectionAlgebra.map_eq_character_smul_add_character_smul`: in this regime,
  representations by projections factor through the two scalar characters.
* `TauCeti.BalancedProjectionAlgebra.apply_map_eq_character_of_markov`: in this regime, Markov
  functionals through representations by projections are scalar characters.

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, for
  the projection generators of the Hecke algebra.
* P. Freyd, D. Yetter, J. Hoste, W. B. R. Lickorish, K. Millett and A. Ocneanu, *A new polynomial
  invariant of knots and links*, Bull. Amer. Math. Soc. 12 (1985), 239–246, for the C⋆-algebraic
  approach to the projection presentation and its Markov states.
-/

public section

/-! ### Non-self-adjoint parameters -/

namespace IsSelfAdjoint

variable {R A : Type*} [DivisionRing R] [Star R] [NonUnitalRing A] [StarRing A] [Module R A]
  [StarModule R A] {τ : R} {p q : A}

/-- Self-adjoint elements satisfying the balanced relation with a parameter `τ` that is not
self-adjoint coincide: the adjoint of the relation is the relation with parameter `star τ`. -/
theorem eq_of_mul_mul_sub_smul_eq_of_star_ne (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    (h : p * q * p - τ • p = q * p * q - τ • q) (hτ : star τ ≠ τ) : p = q := by
  have hstar : p * q * p - star τ • p = q * p * q - star τ • q := by
    simpa only [star_sub, star_mul, star_smul, hp.star_eq, hq.star_eq, mul_assoc] using
      congr_arg star h
  have hsmul : (τ - star τ) • (p - q) = 0 := by
    rw [sub_smul, smul_sub, smul_sub, ← sub_eq_sub_iff_sub_eq_sub.mp h,
      ← sub_eq_sub_iff_sub_eq_sub.mp hstar, sub_self]
  rw [← sub_eq_zero, ← inv_smul_smul₀ (sub_ne_zero.mpr hτ.symm) (p - q), hsmul, smul_zero]

end IsSelfAdjoint

/-! ### Real parameters outside `[0, 1)` -/

namespace IsStarProjection

/-- The unital case of `IsStarProjection.eq_of_mul_mul_sub_smul_eq_of_notMem_Ico`, proved by
locating the spectrum of `p - q`. -/
private theorem eq_of_mul_mul_sub_smul_eq_of_notMem_Ico_of_unital {A : Type*} [CStarAlgebra A]
    {p q : A} (hp : IsStarProjection p) (hq : IsStarProjection q) {t : ℝ}
    (h : p * q * p - t • p = q * p * q - t • q) (ht : t ∉ Set.Ico 0 1) : p = q := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  have hcube := hp.isIdempotentElem.sub_pow_three_eq_smul hq.isIdempotentElem h
  have hle : p - q ≤ algebraMap ℝ A 1 := by
    rw [map_one]
    exact (sub_le_self _ hq.nonneg).trans hp.le_one
  have hge : algebraMap ℝ A (-1) ≤ p - q := by
    simpa using sub_le_sub hp.nonneg hq.le_one
  rw [le_algebraMap_iff_spectrum_le] at hle
  rw [algebraMap_le_iff_le_spectrum] at hge
  refine sub_eq_zero.mp (CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) (p - q) fun x hx ↦ ?_)
  have hroot : x ^ 3 - (1 - t) * x = 0 := by
    have hmem := spectrum.subset_polynomial_aeval (p - q)
      (Polynomial.X ^ 3 - Polynomial.C (1 - t) * Polynomial.X) ⟨x, hx, rfl⟩
    simp only [map_sub, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, hcube,
      Algebra.smul_def, sub_self, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] at hmem
    simpa using CFC.spectrum_algebraMap_subset (A := A) (0 : ℝ) (by simpa using hmem)
  have h1 := hle x hx
  have h2 := hge x hx
  rw [Set.mem_singleton_iff]
  refine (eq_or_ne x 0).resolve_right fun hx0 ↦ ht ?_
  have hsq : x ^ 2 = 1 - t := mul_left_cancel₀ hx0 (by linear_combination hroot)
  have hpos : 0 < x ^ 2 := by positivity
  exact ⟨by nlinarith, by nlinarith⟩

variable {A : Type*} [NonUnitalCStarAlgebra A] {p q : A}

/-- Projections in a C⋆-algebra satisfying the balanced relation with a real parameter
`t ∉ [0, 1)` coincide. -/
theorem eq_of_mul_mul_sub_smul_eq_of_notMem_Ico (hp : IsStarProjection p)
    (hq : IsStarProjection q) {t : ℝ} (h : p * q * p - t • p = q * p * q - t • q)
    (ht : t ∉ Set.Ico 0 1) : p = q := by
  refine Unitization.inr_injective (R := ℂ) <|
    eq_of_mul_mul_sub_smul_eq_of_notMem_Ico_of_unital hp.inr hq.inr ?_ ht
  simpa only [Unitization.inr_mul, Unitization.inr_sub, Unitization.inr_smul] using
    congr_arg ((↑) : A → Unitization ℂ A) h

/-- **Collapse of balanced projections.** Projections in a C⋆-algebra satisfying the balanced
relation `p * q * p - τ • p = q * p * q - τ • q` coincide unless `τ` is a real number in
`[0, 1)`. -/
theorem eq_of_mul_mul_sub_smul_eq_of_notMem_image_Ico (hp : IsStarProjection p)
    (hq : IsStarProjection q) {τ : ℂ} (h : p * q * p - τ • p = q * p * q - τ • q)
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) : p = q := by
  by_cases hτr : star τ = τ
  · obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.mp hτr
    refine hp.eq_of_mul_mul_sub_smul_eq_of_notMem_Ico hq ?_ fun ht ↦ hτ ⟨t, ht, rfl⟩
    simpa only [Complex.coe_smul] using h
  · exact hp.isSelfAdjoint.eq_of_mul_mul_sub_smul_eq_of_star_ne hq.isSelfAdjoint h hτr

end IsStarProjection

/-! ### Representations in the collapse regime -/

namespace TauCeti

namespace BalancedProjectionAlgebra

variable {A F : Type*} [CStarAlgebra A] {τ : ℂ} [FunLike F (BalancedProjectionAlgebra ℂ τ) A]
  [AlgHomClass F ℂ (BalancedProjectionAlgebra ℂ τ) A] (φ : F)

/-- For `τ ∉ [0, 1)`, a representation of the balanced projection algebra by projections in a
C⋆-algebra sends every generator to the same projection. -/
theorem map_e_eq_map_e_zero (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (i : ℕ) : φ (e τ i) = φ (e τ 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← ih]
    refine ((hφ i).eq_of_mul_mul_sub_smul_eq_of_notMem_image_Ico (hφ (i + 1)) ?_ hτ).symm
    simpa only [map_sub, map_mul, map_smul] using congr_arg φ (e_balanced i)

/-- **The collapse regime factors through `ℂ²`.** For `τ ∉ [0, 1)`, a representation of the
balanced projection algebra by projections in a C⋆-algebra is determined by the projection
`P = φ (e 0)` and the two scalar characters: `φ x = χ₁ x • P + χ₀ x • (1 - P)`, where `χ₁` and `χ₀`
send every generator to `1` and to `0`. -/
theorem map_eq_character_smul_add_character_smul (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (x : BalancedProjectionAlgebra ℂ τ) :
    φ x = character 1 .one x • φ (e τ 0) + character 0 .zero x • (1 - φ (e τ 0)) :=
  map_eq_character_smul_add_character_smul_of_map_e_eq φ (map_e_eq_map_e_zero φ hφ hτ) x

variable {M : Type*} [FunLike M A ℂ] {μ : M} {η : ℂ}

/-- **The Markov parameter in the collapse regime.** For `τ ∉ [0, 1)`, let `φ` be
a representation of the balanced projection algebra by projections in a C⋆-algebra, and `μ` a
functional with `μ 1 = 1` such that `x ↦ μ (φ x)` obeys the Markov rule with parameter `η`. Then
`η` is idempotent, that is `η = 0` or `η = 1`. -/
theorem isIdempotentElem_of_markov (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (h1 : μ 1 = 1)
    (hmarkov : ∀ n w, w ∈ stage ℂ τ (n + 1) → μ (φ (w * e τ n)) = η * μ (φ w)) :
    IsIdempotentElem η :=
  isIdempotentElem_of_markov_of_map_e_eq φ (map_e_eq_map_e_zero φ hφ hτ) h1 hmarkov

/-- **Markov states in the collapse regime are scalar characters.** Under the hypotheses of
`TauCeti.BalancedProjectionAlgebra.isIdempotentElem_of_markov`, the functional `x ↦ μ (φ x)` is the
scalar character sending every generator to `η`. -/
theorem apply_map_eq_character_of_markov [LinearMapClass M ℂ A ℂ]
    (hφ : ∀ i, IsStarProjection (φ (e τ i))) (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1)
    (h1 : μ 1 = 1)
    (hmarkov : ∀ n w, w ∈ stage ℂ τ (n + 1) → μ (φ (w * e τ n)) = η * μ (φ w))
    (x : BalancedProjectionAlgebra ℂ τ) :
    μ (φ x) = character η (isIdempotentElem_of_markov φ hφ hτ h1 hmarkov) x :=
  apply_map_eq_character_of_markov_of_map_e_eq φ (map_e_eq_map_e_zero φ hφ hτ) h1 hmarkov x

end BalancedProjectionAlgebra

end TauCeti
