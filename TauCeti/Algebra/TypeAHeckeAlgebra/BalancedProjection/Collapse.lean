/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.BalancedProjection.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import TauCeti.Algebra.Star.Projection.Commute
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Balanced projections in C⋆-algebras outside the interval `0 < τ < 1`

The balanced projection algebra `TauCeti.BalancedProjectionAlgebra R τ` is presented by idempotents
`e i` whose adjacent defects `e i * e (i + 1) * e i - τ • e i` and
`e (i + 1) * e i * e (i + 1) - τ • e (i + 1)` agree. When `τ * (q + q⁻¹) ^ 2 = 1` for a unit `q`
it is the infinite type-A Hecke algebra. This file treats instead its representations by
projections in a C⋆-algebra when `τ` is not in the half-open interval `[0, 1)`, and at the
endpoint `τ = 0`.

The key algebraic identity is that for idempotents `p` and `q` satisfying the balanced relation,
the difference `d = p - q` satisfies `d ^ 3 = (1 - τ) • d`. If `p` and `q` are projections in a
C⋆-algebra, `d` is self-adjoint and `-1 ≤ d ≤ 1`, so its spectrum lies in `[-1, 1]` and consists of
roots of `x ^ 3 - (1 - τ) * x`. For real `τ` outside `[0, 1)` the only such root is `0`, so `d = 0`.
For non-real `τ`, comparing the balanced relation with its adjoint already gives `p = q`. Hence:

* for `τ ∉ [0, 1)`, every representation of the balanced projection algebra over `ℂ` by
  projections in a C⋆-algebra sends all generators to one projection `P`, so it factors through
  the two scalar characters `e i ↦ 1` and `e i ↦ 0`
  (`TauCeti.BalancedProjectionAlgebra.map_eq_character_smul_add_character_smul`);
* consequently, a normalized functional obeying the Markov rule with parameter `η` through such a
  representation has `η ∈ {0, 1}` and is the corresponding scalar character
  (`TauCeti.BalancedProjectionAlgebra.apply_map_eq_character_of_markov`);
* for `τ = 0`, the balanced relation `p * q * p = q * p * q` between two projections forces them to
  commute (`IsStarProjection.commute_of_mul_mul_eq`), so every representation by projections in a
  ring with a proper star has commutative image
  (`TauCeti.BalancedProjectionAlgebra.commute_map_of_zero`).

## Main definitions

* `TauCeti.BalancedProjectionAlgebra.character`: the scalar character sending every generator to
  a fixed idempotent scalar.

## Main results

* `TauCeti.BalancedProjectionAlgebra.sub_pow_three_eq_smul`: `(p - q) ^ 3 = (1 - τ) • (p - q)`
  for balanced idempotents.
* `TauCeti.BalancedProjectionAlgebra.commute_map_of_zero`: for `τ = 0`, representations by
  projections have commutative image.
* `TauCeti.BalancedProjectionAlgebra.eq_of_balanced`: balanced projections in a C⋆-algebra
  coincide when `τ ∉ [0, 1)`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, §11, for the projection presentation and its parameter.
-/

public section

namespace TauCeti

namespace BalancedProjectionAlgebra

/-! ### Scalar characters -/

section Character

variable {R : Type*} [CommRing R] {τ : R}

/-- The scalar character of the balanced projection algebra sending every generator `e i` to the
same idempotent scalar `c`. The balanced and distant relations hold trivially for a constant
sequence. -/
def character (c : R) (hc : IsIdempotentElem c) : BalancedProjectionAlgebra R τ →ₐ[R] R :=
  lift (fun _ ↦ c) (fun _ ↦ hc) (fun _ ↦ rfl) fun _ ↦ rfl

/-- The scalar character `TauCeti.BalancedProjectionAlgebra.character c` takes every generator to
`c`. -/
@[simp]
theorem character_e (c : R) (hc : IsIdempotentElem c) (i : ℕ) :
    character (τ := τ) c hc (e τ i) = c :=
  lift_e _ _ _ _ i

end Character

/-! ### The cube identity -/

section Cube

variable {R A : Type*} [Ring R] [Ring A] [Module R A] {τ : R} {p q : A}

/-- For idempotents `p` and `q` satisfying the balanced relation
`p * q * p - τ • p = q * p * q - τ • q`, the difference `p - q` satisfies
`(p - q) ^ 3 = (1 - τ) • (p - q)`. -/
theorem sub_pow_three_eq_smul (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (h : p * q * p - τ • p = q * p * q - τ • q) : (p - q) ^ 3 = (1 - τ) • (p - q) := by
  have h' := sub_eq_sub_iff_sub_eq_sub.mp h
  calc (p - q) ^ 3 = p - p * q * p + q * p * q - q := by
        simp only [pow_succ, pow_zero, one_mul, sub_mul, mul_sub, mul_assoc, hp.eq, hq.eq]
        abel
    _ = (1 - τ) • (p - q) := by
        rw [sub_smul, one_smul, smul_sub, ← h']
        abel

/-- Adjacent generators of the balanced projection algebra satisfy
`(e i - e (i + 1)) ^ 3 = (1 - τ) • (e i - e (i + 1))`. -/
theorem e_sub_e_succ_pow_three {R : Type*} [CommRing R] {τ : R} (i : ℕ) :
    (e τ i - e τ (i + 1)) ^ 3 = (1 - τ) • (e τ i - e τ (i + 1)) :=
  sub_pow_three_eq_smul (isIdempotentElem_e i) (isIdempotentElem_e (i + 1)) (e_balanced i)

end Cube

/-! ### Non-real parameters -/

section NonReal

variable {R A : Type*} [DivisionRing R] [Star R] [Ring A] [StarRing A] [Module R A]
  [StarModule R A] {τ : R} {p q : A}

/-- Self-adjoint elements satisfying the balanced relation with a parameter `τ` that is not
self-adjoint coincide: the adjoint of the relation is the relation with parameter `star τ`. -/
theorem eq_of_balanced_of_star_ne (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    (hτ : star τ ≠ τ) (h : p * q * p - τ • p = q * p * q - τ • q) : p = q := by
  have hstar : p * q * p - star τ • p = q * p * q - star τ • q := by
    simpa only [star_sub, star_mul, star_smul, hp.star_eq, hq.star_eq, mul_assoc] using
      congr_arg star h
  have hsmul : (τ - star τ) • (p - q) = 0 := by
    rw [sub_smul, smul_sub, smul_sub, ← sub_eq_sub_iff_sub_eq_sub.mp h,
      ← sub_eq_sub_iff_sub_eq_sub.mp hstar, sub_self]
  rw [← sub_eq_zero, ← inv_smul_smul₀ (sub_ne_zero.mpr hτ.symm) (p - q), hsmul, smul_zero]

end NonReal

section Adjoin

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {τ : R}

/-- Every element of the balanced projection algebra maps into the subalgebra generated by the
images of the generators. -/
theorem map_mem_adjoin_range (φ : BalancedProjectionAlgebra R τ →ₐ[R] A)
    (x : BalancedProjectionAlgebra R τ) :
    φ x ∈ Algebra.adjoin R (Set.range fun i ↦ φ (e τ i)) := by
  obtain ⟨y, rfl⟩ := mkAlgHom_surjective x
  have hy : y ∈ Algebra.adjoin R (Set.range (FreeAlgebra.ι R)) := by
    rw [FreeAlgebra.adjoin_range_ι]
    trivial
  have hmap : (φ.comp (mkAlgHom R τ)) y ∈
      (Algebra.adjoin R (Set.range (FreeAlgebra.ι R))).map (φ.comp (mkAlgHom R τ)) :=
    Subalgebra.mem_map.mpr ⟨y, hy, rfl⟩
  rw [AlgHom.map_adjoin, ← Set.range_comp] at hmap
  simpa [Function.comp_def] using hmap

end Adjoin

/-! ### The endpoint `τ = 0` -/

section Zero

variable {R A : Type*} [CommRing R] [Ring A] [StarRing A] [IsProperStar A] [Algebra R A]
  (φ : BalancedProjectionAlgebra R (0 : R) →ₐ[R] A)

/-- For `τ = 0`, the images of any two generators under a representation by projections in a ring
with a proper star commute. -/
theorem commute_map_e_of_zero (hφ : ∀ i, IsStarProjection (φ (e 0 i))) (i j : ℕ) :
    Commute (φ (e 0 i)) (φ (e 0 j)) := by
  have hadj (i : ℕ) : Commute (φ (e 0 i)) (φ (e 0 (i + 1))) := by
    refine (hφ i).commute_of_mul_mul_eq (hφ (i + 1)) ?_
    simpa only [map_sub, map_mul, map_smul, zero_smul, sub_zero] using
      congr_arg φ (e_balanced (τ := (0 : R)) i)
  rcases lt_trichotomy i j with hij | rfl | hij
  · rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    rcases k with _ | k
    · exact hadj i
    · exact (commute_e (by omega)).map φ
  · exact Commute.refl _
  · rcases Nat.exists_eq_add_of_lt hij with ⟨k, rfl⟩
    rcases k with _ | k
    · exact (hadj j).symm
    · exact (commute_e (by omega)).map φ

/-- For `τ = 0`, a representation by projections in a ring with a proper star has commutative
image. -/
theorem commute_map_of_zero (hφ : ∀ i, IsStarProjection (φ (e 0 i)))
    (x y : BalancedProjectionAlgebra R (0 : R)) : Commute (φ x) (φ y) := by
  refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (map_mem_adjoin_range φ y) ?_
  rintro _ ⟨j, rfl⟩
  refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute (map_mem_adjoin_range φ x) ?_).symm
  rintro _ ⟨i, rfl⟩
  exact commute_map_e_of_zero φ hφ j i

end Zero

/-! ### Real parameters outside `[0, 1)` -/

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] {p q : A}

/-- Projections in a C⋆-algebra satisfying the balanced relation with a real parameter
`t ∉ [0, 1)` coincide. -/
theorem eq_of_balanced_of_real (hp : IsStarProjection p) (hq : IsStarProjection q) {t : ℝ}
    (ht : t ∉ Set.Ico 0 1) (h : p * q * p - t • p = q * p * q - t • q) : p = q := by
  let _ := CStarAlgebra.spectralOrder A
  let _ := CStarAlgebra.spectralOrderedRing A
  have hd : IsSelfAdjoint (p - q) := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hcube := sub_pow_three_eq_smul hp.isIdempotentElem hq.isIdempotentElem h
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

/-- **Collapse of balanced projections.** Projections in a C⋆-algebra satisfying the balanced
relation `p * q * p - τ • p = q * p * q - τ • q` coincide unless `τ` is a real number in
`[0, 1)`. -/
theorem eq_of_balanced (hp : IsStarProjection p) (hq : IsStarProjection q) {τ : ℂ}
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (h : p * q * p - τ • p = q * p * q - τ • q) :
    p = q := by
  by_cases hτr : star τ = τ
  · obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.mp hτr
    refine eq_of_balanced_of_real hp hq (fun ht ↦ hτ ⟨t, ht, rfl⟩) ?_
    simpa only [Complex.coe_smul] using h
  · exact eq_of_balanced_of_star_ne hp.isSelfAdjoint hq.isSelfAdjoint hτr h

/-! ### Representations in the collapse regime -/

variable {τ : ℂ} (φ : BalancedProjectionAlgebra ℂ τ →ₐ[ℂ] A)

/-- For `τ ∉ [0, 1)`, a representation of the balanced projection algebra by projections in a
C⋆-algebra sends every generator to the same projection. -/
theorem map_e_eq_map_e_zero (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (i : ℕ) : φ (e τ i) = φ (e τ 0) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← ih]
    refine (eq_of_balanced (hφ i) (hφ (i + 1)) hτ ?_).symm
    simpa only [map_sub, map_mul, map_smul] using congr_arg φ (e_balanced i)

/-- **The collapse regime factors through `ℂ²`.** For `τ ∉ [0, 1)`, a representation of the
balanced projection algebra by projections in a C⋆-algebra is determined by the projection
`P = φ (e 0)` and the two scalar characters: `φ x = χ₁ x • P + χ₀ x • (1 - P)`, where `χ₁` and `χ₀`
send every generator to `1` and to `0`. -/
theorem map_eq_character_smul_add_character_smul (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) (x : BalancedProjectionAlgebra ℂ τ) :
    φ x = character 1 .one x • φ (e τ 0) + character 0 .zero x • (1 - φ (e τ 0)) := by
  set P := φ (e τ 0)
  have hP : IsIdempotentElem P := (hφ 0).isIdempotentElem
  let ψ : BalancedProjectionAlgebra ℂ τ →ₐ[ℂ] A := AlgHom.ofLinearMap
    ((character 1 .one).toLinearMap.smulRight P + (character 0 .zero).toLinearMap.smulRight (1 - P))
    (by simp) fun x y ↦ by
      simp only [LinearMap.add_apply, LinearMap.smulRight_apply, AlgHom.toLinearMap_apply,
        map_mul, add_mul, mul_add, smul_mul_smul_comm, hP.eq, hP.mul_one_sub_self,
        hP.one_sub_mul_self, hP.one_sub.eq, smul_zero, add_zero, zero_add]
  have hφψ : φ = ψ := hom_ext fun i ↦ by
    simp [ψ, map_e_eq_map_e_zero φ hφ hτ i, P]
  exact congr($hφψ x)

/-- **The Markov parameter in the collapse regime.** For `τ ∉ [0, 1)`, let `φ` be
a representation of the balanced projection algebra by projections in a C⋆-algebra, and `μ` a
functional with `μ 1 = 1` such that `x ↦ μ (φ x)` obeys the Markov rule with parameter `η`. Then
`η` is idempotent, that is `η = 0` or `η = 1`. -/
theorem isIdempotentElem_of_markov (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) {μ : A →ₗ[ℂ] ℂ} {η : ℂ} (h1 : μ 1 = 1)
    (hmarkov : ∀ n w, w ∈ stage ℂ τ (n + 1) → μ (φ (w * e τ n)) = η * μ (φ w)) :
    IsIdempotentElem η := by
  have hη : μ (φ (e τ 0)) = η := by
    simpa [h1] using hmarkov 0 1 (Subalgebra.one_mem _)
  have h01 := hmarkov 1 (e τ 0) (e_mem_stage (by omega))
  rw [map_mul, map_e_eq_map_e_zero φ hφ hτ 1, (hφ 0).isIdempotentElem.eq, hη] at h01
  exact h01.symm

/-- **Markov states in the collapse regime are scalar characters.** Under the hypotheses of
`TauCeti.BalancedProjectionAlgebra.isIdempotentElem_of_markov`, the functional `x ↦ μ (φ x)` is the
scalar character sending every generator to `η`. -/
theorem apply_map_eq_character_of_markov (hφ : ∀ i, IsStarProjection (φ (e τ i)))
    (hτ : τ ∉ ((↑) : ℝ → ℂ) '' Set.Ico 0 1) {μ : A →ₗ[ℂ] ℂ} {η : ℂ} (h1 : μ 1 = 1)
    (hmarkov : ∀ n w, w ∈ stage ℂ τ (n + 1) → μ (φ (w * e τ n)) = η * μ (φ w))
    (x : BalancedProjectionAlgebra ℂ τ) :
    μ (φ x) = character η (isIdempotentElem_of_markov φ hφ hτ h1 hmarkov) x := by
  have hη : μ (φ (e τ 0)) = η := by
    simpa [h1] using hmarkov 0 1 (Subalgebra.one_mem _)
  rw [map_eq_character_smul_add_character_smul φ hφ hτ x, map_add, map_smul, map_smul, map_sub,
    h1, hη, smul_eq_mul, smul_eq_mul]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (isIdempotentElem_of_markov φ hφ hτ h1 hmarkov)
    with rfl | rfl <;> simp

end CStarAlgebra

end BalancedProjectionAlgebra

end TauCeti
