/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NoncommutativeGeometry.SmoothTorus.Basic
public import TauCeti.Algebra.Lie.Derivation.Basic

/-!
# Coordinate derivations of the smooth noncommutative torus

The two coordinate derivations multiply the Fourier coefficient at `(m, n)` by
`2πi m` and `2πi n`, respectively. Polynomial growth of these multipliers preserves rapid
decay. Their additivity on the lattice gives the Leibniz rule for the twisted convolution,
without any restriction on the real rotation parameter.

`coordinateDerivation` takes values in the existing noncommutative `derivationLieAlgebra`.
The derivations commute, preserve the involution, and are annihilated by the canonical trace.
The resulting integration-by-parts identity is the algebraic input to differential-form
characters. This file concerns the algebraic derivations; it does not equip the Fourier
algebra with a topology or assert continuity.

## References

* A. Connes, *Noncommutative Geometry*, Academic Press, 1994, Chapter IV, §6.
-/

public section

open Complex
open scoped ComplexConjugate

noncomputable section

namespace TauCeti.SmoothNoncommutativeTorus

variable {θ : ℝ}

/-- The additive Fourier frequency `2πi m` or `2πi n`, indexed by `0` or `1`. -/
def frequency (j : Fin 2) : (ℤ × ℤ) →+ ℂ where
  toFun x := (2 * Real.pi * I) * (if j = 0 then (x.1 : ℂ) else (x.2 : ℂ))
  map_zero' := by simp
  map_add' x y := by
    split_ifs <;> simp [mul_add]

/-- The coordinate formula for the Fourier frequency. -/
theorem frequency_apply (j : Fin 2) (x : ℤ × ℤ) :
    frequency j x = (2 * Real.pi * I) * (if j = 0 then (x.1 : ℂ) else (x.2 : ℂ)) :=
  (rfl)

@[simp]
theorem frequency_zero (x : ℤ × ℤ) : frequency 0 x = (2 * Real.pi * I) * x.1 := by
  simp [frequency_apply]

@[simp]
theorem frequency_one (x : ℤ × ℤ) : frequency 1 x = (2 * Real.pi * I) * x.2 := by
  simp [frequency_apply]

/-- Fourier frequencies grow at most linearly in the rapid-decay weight. -/
theorem norm_frequency_le (j : Fin 2) (x : ℤ × ℤ) :
    ‖frequency j x‖ ≤ ‖(2 * Real.pi * I : ℂ)‖ * weight x := by
  simp only [frequency_apply]
  split_ifs
  · rw [norm_mul, Complex.norm_intCast]
    gcongr
    exact abs_fst_le_weight x
  · rw [norm_mul, Complex.norm_intCast]
    gcongr
    exact abs_snd_le_weight x

/-- Multiplication by either coordinate frequency preserves rapid decay. -/
theorem IsRapidDecay.frequency_mul {a : ℤ × ℤ → ℂ} (ha : IsRapidDecay a) (j : Fin 2) :
    IsRapidDecay fun x ↦ frequency j x * a x := by
  rw [isRapidDecay_iff]
  intro k
  obtain ⟨C, hC⟩ := (isRapidDecay_iff _).mp ha (k + 1)
  refine ⟨‖(2 * Real.pi * I : ℂ)‖ * C, fun x ↦ ?_⟩
  calc ‖frequency j x * a x‖ * weight x ^ k
      ≤ (‖(2 * Real.pi * I : ℂ)‖ * weight x) * ‖a x‖ * weight x ^ k := by
        rw [norm_mul]
        have hw := weight_pos x
        gcongr
        exact norm_frequency_le j x
    _ = ‖(2 * Real.pi * I : ℂ)‖ * (‖a x‖ * weight x ^ (k + 1)) := by ring
    _ ≤ ‖(2 * Real.pi * I : ℂ)‖ * C := by
      gcongr
      exact hC x

private def coordinateDerivative (j : Fin 2) : Module.End ℂ (SmoothNoncommutativeTorus θ) where
  toFun a := ⟨fun x ↦ frequency j x * a.coeff x, a.isRapidDecay_coeff.frequency_mul j⟩
  map_add' a b := by ext x; simp [coeff_add, mul_add]
  map_smul' c a := by ext x; simp [coeff_smul, mul_left_comm]

private theorem coeff_coordinateDerivative (j : Fin 2) (a : SmoothNoncommutativeTorus θ)
    (x : ℤ × ℤ) : (coordinateDerivative j a).coeff x = frequency j x * a.coeff x :=
  (rfl)

private theorem coordinateDerivative_mul (j : Fin 2) (a b : SmoothNoncommutativeTorus θ) :
    coordinateDerivative j (a * b) =
      coordinateDerivative j a * b + a * coordinateDerivative j b := by
  ext x
  have hsum := (summable_mul_coeff (coordinateDerivative j a) b x).tsum_add
    (summable_mul_coeff a (coordinateDerivative j b) x)
  simp only [coeff_coordinateDerivative] at hsum
  simp only [coeff_coordinateDerivative, coeff_mul, coeff_add, Pi.add_apply]
  rw [← tsum_mul_left, ← hsum]
  refine tsum_congr fun y ↦ ?_
  have hfreq : frequency j x = frequency j y + frequency j (x - y) := by
    rw [map_sub, add_sub_cancel]
  calc frequency j x * (a.coeff y * b.coeff (x - y) * twist θ y (x - y))
      = (frequency j y + frequency j (x - y)) *
          (a.coeff y * b.coeff (x - y) * twist θ y (x - y)) := by rw [hfreq]
    _ = frequency j y * a.coeff y * b.coeff (x - y) * twist θ y (x - y) +
        a.coeff y * (frequency j (x - y) * b.coeff (x - y)) * twist θ y (x - y) := by ring

/-- The coordinate derivations `δ₁` and `δ₂`, indexed by `0` and `1`, of the Fourier algebra.
These use the associative Leibniz rule, not a commutative-algebra derivation type. -/
def coordinateDerivation (j : Fin 2) : derivationLieAlgebra ℂ (SmoothNoncommutativeTorus θ) :=
  ⟨coordinateDerivative j, mem_derivationLieAlgebra.mpr (coordinateDerivative_mul j)⟩

/-- The defining Fourier-coefficient formula for a coordinate derivation. -/
@[simp]
theorem coeff_coordinateDerivation (j : Fin 2) (a : SmoothNoncommutativeTorus θ) (x : ℤ × ℤ) :
    ((coordinateDerivation j).1 a).coeff x = frequency j x * a.coeff x := by
  -- Bundling the Leibniz proof leaves the underlying endomorphism unchanged.
  exact coeff_coordinateDerivative j a x

/-- A coordinate derivation acts diagonally on every Fourier monomial. -/
@[simp]
theorem coordinateDerivation_single (j : Fin 2) (x : ℤ × ℤ) (c : ℂ) :
    (coordinateDerivation j).1 (single x c : SmoothNoncommutativeTorus θ) =
      single x (frequency j x * c) := by
  ext y
  by_cases h : y = x
  · subst y
    simp only [coeff_coordinateDerivation, coeff_single, Pi.single_eq_same]
  · simp [h]

/-- The frequency changes sign under complex conjugation. -/
@[simp]
theorem conj_frequency (j : Fin 2) (x : ℤ × ℤ) : conj (frequency j x) = -frequency j x := by
  simp only [frequency_apply]
  split_ifs <;> simp [map_ofNat, mul_assoc]

/-- Coordinate derivations preserve the involution. -/
@[simp]
theorem coordinateDerivation_star (j : Fin 2) (a : SmoothNoncommutativeTorus θ) :
    (coordinateDerivation j).1 (star a) = star ((coordinateDerivation j).1 a) := by
  ext x
  simp only [coeff_coordinateDerivation, coeff_star, map_mul, map_neg, conj_frequency, neg_neg,
    mul_assoc]

/-- The coordinate derivations commute. -/
theorem coordinateDerivation_comm (j k : Fin 2) (a : SmoothNoncommutativeTorus θ) :
    (coordinateDerivation j).1 ((coordinateDerivation k).1 a) =
      (coordinateDerivation k).1 ((coordinateDerivation j).1 a) := by
  ext x
  simp only [coeff_coordinateDerivation]
  exact mul_left_comm _ _ _

/-- The coordinate derivations commute as linear endomorphisms. -/
theorem commute_coordinateDerivation (j k : Fin 2) :
    Commute ((coordinateDerivation j).1 : Module.End ℂ (SmoothNoncommutativeTorus θ))
      (coordinateDerivation k).1 := by
  exact LinearMap.ext (coordinateDerivation_comm j k)

/-- The canonical trace annihilates each coordinate derivation. -/
@[simp↓]
theorem trace_coordinateDerivation (j : Fin 2) (a : SmoothNoncommutativeTorus θ) :
    trace θ ((coordinateDerivation j).1 a) = 0 := by
  simp [trace_apply]

/-- Integration by parts for the canonical trace and either coordinate derivation. -/
theorem trace_coordinateDerivation_mul (j : Fin 2) (a b : SmoothNoncommutativeTorus θ) :
    trace θ ((coordinateDerivation j).1 a * b) = -trace θ (a * (coordinateDerivation j).1 b) := by
  have h : trace θ ((coordinateDerivation j).1 a * b) +
      trace θ (a * (coordinateDerivation j).1 b) = 0 := by
    rw [← map_add, ← derivationLieAlgebra.leibniz, trace_coordinateDerivation]
  exact eq_neg_of_add_eq_zero_left h

@[simp↓]
theorem coordinateDerivation_zero_U₁ :
    (coordinateDerivation 0).1 (U₁ θ : SmoothNoncommutativeTorus θ) =
      (2 * Real.pi * I : ℂ) • (U₁ θ : SmoothNoncommutativeTorus θ) := by
  simp [smul_single]

@[simp↓]
theorem coordinateDerivation_one_U₁ :
    (coordinateDerivation 1).1 (U₁ θ : SmoothNoncommutativeTorus θ) = 0 := by
  ext x
  simp [Pi.single_apply]

@[simp↓]
theorem coordinateDerivation_zero_U₂ :
    (coordinateDerivation 0).1 (U₂ θ : SmoothNoncommutativeTorus θ) = 0 := by
  ext x
  simp [Pi.single_apply]

@[simp↓]
theorem coordinateDerivation_one_U₂ :
    (coordinateDerivation 1).1 (U₂ θ : SmoothNoncommutativeTorus θ) =
      (2 * Real.pi * I : ℂ) • (U₂ θ : SmoothNoncommutativeTorus θ) := by
  simp [smul_single]

end TauCeti.SmoothNoncommutativeTorus
