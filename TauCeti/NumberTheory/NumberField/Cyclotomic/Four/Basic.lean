/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Norm
public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Basic facts about the Gaussian integers as a ring of integers

Let `K = ℚ(i)` be given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]` for a primitive fourth root of unity `i`. This file records the elementary facts
about `ℤ[i]` that the primary normalisation of quartic reciprocity is computed with:

* `IsPrimitiveRoot.minpoly_toInteger_eq_X_sq_add_one`: the minimal polynomial of `i` is
  `X² + 1`, which connects this presentation of `ℚ(i)` with the quadratic-field API;
* `IsPrimitiveRoot.exists_intCast_add_intCast_mul_toInteger_eq_of_four`: every element of `ℤ[i]` is
  `a + b i` for integers `a` and `b`;
* `IsPrimitiveRoot.intCast_dvd_intCast_add_intCast_mul_toInteger_iff_of_four`: an integer divides
  `a + b i` exactly when it divides both `a` and `b`;
* `IsPrimitiveRoot.norm_intCast_add_intCast_mul_toInteger`: the norm of `a + b i` is `a² + b²`;
* `IsPrimitiveRoot.isUnit_intCast_add_intCast_mul_toInteger_iff`: `a + b i` is a unit exactly
  when `a² + b² = 1`;
* `TauCeti.isPrincipalIdealRing_ringOfIntegers_four`: `ℤ[i]` is a principal ideal domain.
-/

public section

open NumberField Polynomial TauCeti.NumberField

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/-- The minimal polynomial over `ℤ` of a primitive fourth root of unity `i ∈ 𝓞 K` is `X² + 1`.
This presents `K` as `ℚ(i)` in the form used by the quadratic-field API. -/
theorem minpoly_toInteger_eq_X_sq_add_one : minpoly ℤ hζ.toInteger = X ^ 2 + 1 := by
  have h : minpoly ℤ ζ = X ^ 2 + 1 := by
    rw [← cyclotomic_eq_minpoly hζ (by norm_num), show (4 : ℕ) = 2 ^ (1 + 1) by norm_num,
      cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [Finset.sum_range_succ, add_comm]
  -- The image of `hζ.toInteger` in `K` is `ζ` by definition (`IsPrimitiveRoot.coe_toInteger`).
  rw [← RingOfIntegers.minpoly_coe]
  exact h

variable [IsCyclotomicExtension {4} ℚ K]

private theorem adjoin_toInteger_four : Algebra.adjoin ℚ {(hζ.toInteger : K)} = ⊤ :=
  IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ

/-- The integral basis `1, i` of `𝓞 K`, indexed by `Fin 2`. -/
private noncomputable def basisFour : Module.Basis (Fin 2) ℤ (𝓞 K) :=
  hζ.integralPowerBasis.basis.reindex (finCongr (by simp [show Nat.totient 4 = 2 by decide]))

private theorem basisFour_apply (j : Fin 2) : basisFour hζ j = hζ.toInteger ^ (j : ℕ) := by
  simp [basisFour, PowerBasis.coe_basis]

private theorem intCast_add_intCast_mul_eq (a b : ℤ) :
    (a : 𝓞 K) + b * hζ.toInteger = a • basisFour hζ 0 + b • basisFour hζ 1 := by
  simp [basisFour_apply]

/-- Every element of `𝓞 K = ℤ[i]` is `a + b i` for integers `a` and `b`. -/
theorem exists_intCast_add_intCast_mul_toInteger_eq_of_four (x : 𝓞 K) :
    ∃ a b : ℤ, (a : 𝓞 K) + b * hζ.toInteger = x := by
  refine ⟨(basisFour hζ).repr x 0, (basisFour hζ).repr x 1, ?_⟩
  rw [intCast_add_intCast_mul_eq]
  conv_rhs => rw [← (basisFour hζ).sum_repr x]
  simp [Fin.sum_univ_two]

/-- An integer `m` divides `a + b i` in `𝓞 K = ℤ[i]` exactly when it divides both coordinates. -/
@[simp]
theorem intCast_dvd_intCast_add_intCast_mul_toInteger_iff_of_four {m a b : ℤ} :
    (m : 𝓞 K) ∣ a + b * hζ.toInteger ↔ m ∣ a ∧ m ∣ b := by
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun ⟨ha, hb⟩ ↦ ?_⟩
  · have hy' : a • basisFour hζ 0 + b • basisFour hζ 1 = m • y := by
      rw [← intCast_add_intCast_mul_eq, hy, zsmul_eq_mul]
    have h0 := congrArg (fun z ↦ (basisFour hζ).repr z 0) hy'
    have h1 := congrArg (fun z ↦ (basisFour hζ).repr z 1) hy'
    simp only [map_add, map_zsmul, Module.Basis.repr_self, Finsupp.coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul] at h0 h1
    exact ⟨⟨_, by simpa using h0⟩, ⟨_, by simpa using h1⟩⟩
  · exact dvd_add (Int.cast_dvd_cast _ _ ha) (dvd_mul_of_dvd_left (Int.cast_dvd_cast _ _ hb) _)

/-- The norm of `a + b i` in `𝓞 K = ℤ[i]` is `a² + b²`. -/
@[simp]
theorem norm_intCast_add_intCast_mul_toInteger (a b : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K) + b * hζ.toInteger) = a ^ 2 + b ^ 2 := by
  rw [TauCeti.NumberField.norm_int_add_mul_gen
    (GaussianRationals.minpoly_eq_X_sq_sub_C hζ.minpoly_toInteger_eq_X_sq_add_one)
    (adjoin_toInteger_four hζ)]
  ring

/-- An element `a + b i` of `𝓞 K = ℤ[i]` is a unit exactly when `a² + b² = 1`, that is, when it is
one of `±1, ±i`. -/
theorem isUnit_intCast_add_intCast_mul_toInteger_iff {a b : ℤ} :
    IsUnit ((a : 𝓞 K) + b * hζ.toInteger) ↔ a ^ 2 + b ^ 2 = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hn := h.map (Algebra.norm ℤ)
    rw [norm_intCast_add_intCast_mul_toInteger, Int.isUnit_iff] at hn
    rcases hn with hn | hn
    · exact hn
    · nlinarith [sq_nonneg a, sq_nonneg b]
  · refine IsUnit.of_mul_eq_one ((a : 𝓞 K) - b * hζ.toInteger) ?_
    have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
    have h' : ((a : 𝓞 K)) ^ 2 + (b : 𝓞 K) ^ 2 = 1 := by exact_mod_cast h
    linear_combination (-(b : 𝓞 K) ^ 2) * hsq + h'

end IsPrimitiveRoot

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **`ℤ[i]` is a principal ideal domain.** This is
`TauCeti.NumberField.GaussianRationals.isPrincipalIdealRing` at a primitive fourth root of
unity. -/
theorem isPrincipalIdealRing_ringOfIntegers_four : IsPrincipalIdealRing (𝓞 K) :=
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  NumberField.GaussianRationals.isPrincipalIdealRing hζ.minpoly_toInteger_eq_X_sq_add_one
    hζ.adjoin_toInteger_four

end TauCeti
