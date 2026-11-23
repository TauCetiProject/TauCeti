/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import TauCeti.RingTheory.PowerSeries.Rescale
public import TauCeti.RingTheory.PowerSeries.SubringCoeff

/-!
# Integral coefficient lattices of power series

Let `A → R` be an algebra over a commutative ring. A power series `f = ∑ aₙ Xⁿ` over `R` is
`A`-integral (`TauCeti.IntegralSeries A f`) when every coefficient `aₙ` lies in the image of `A`.
For `A = ℤ` and `R = ℚ` these are the series with integer coefficients; for `A` the integral
closure of `ℤ` in an algebraic coefficient field they are the series with algebraic-integer
coefficients.

The *integral lattice at scale `M`* (`TauCeti.scaledIntegralSeries A M`) consists of the series
`f` for which `f(M X)` is `A`-integral, that is `Mⁿ aₙ` lies in the image of `A` for every `n`.
It is the preimage of the image of `A⟦X⟧` under the native rescaling `PowerSeries.rescale M`,
hence a subring of `R⟦X⟧`. Rescaling never changes the constant coefficient, so a constant series
lies in this lattice exactly when its value is integral, whatever the scale.

A series `χ = X + a₂ X² + a₃ X³ + ⋯` tangent to the identity lies in the *tangent lattice at
scale `M`* (`TauCeti.TangentIntegralSeries A M χ`) when `Mⁿ⁻¹ aₙ` is integral for every `n ≥ 2`.
Over a field this says that the normalized rescaling `χ(M X) / M` is `A`-integral
(`TauCeti.tangentIntegralSeries_iff_integralSeries_inv_smul_rescale`). The tangent lattice is
stronger than the ordinary lattice at the same integral scale: `X + X² / 4` lies in the ordinary
lattice at scale `2`, and in the tangent lattice at scale `4` (and at its multiples) but not at
scale `2`.

These lattices measure the denominators of the Taylor coefficients of arithmetic power series,
such as algebraic series and the inverse series of a normalized coordinate, in the arithmetic
algebraization theorems of Calegari, Dimitrov and Tang.

## Main definitions

* `TauCeti.IntegralSeries A f`: every coefficient of `f` lies in the image of `A`.
* `TauCeti.scaledIntegralSeries A M`: the subring of series `f` with `f(M X)` `A`-integral.
* `TauCeti.TangentIntegralSeries A M χ`: `χ = X + O(X²)` and `Mⁿ⁻¹ aₙ` is integral for `n ≥ 2`.

## Main results

* `TauCeti.mem_scaledIntegralSeries_iff`: membership means integrality of every `Mⁿ aₙ`.
* `TauCeti.mem_scaledIntegralSeries_iff_rescale_mem_range_map`: membership means that
  `f(M X)` is the coefficientwise image of a power series over `A`.
* `TauCeti.scaledIntegralSeries_one`: at scale one the lattice is the image of `A⟦X⟧`.
* `TauCeti.scaledIntegralSeries_le_of_dvd`: the lattice grows along divisibility of scales.
* `TauCeti.C_mem_scaledIntegralSeries_iff`: a constant lies in the lattice iff it is integral.
* `TauCeti.tangentIntegralSeries_iff_integralSeries_inv_smul_rescale`: the tangent lattice
  condition as integrality of `χ(M X) / M`.
* `TauCeti.TangentIntegralSeries.mem_scaledIntegralSeries`: the tangent lattice at an integral
  scale lies in the ordinary lattice at that scale.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  (2025), §2.1, proof of Lemma 2.1.2.
-/

public section

namespace TauCeti

open PowerSeries

variable (A : Type*) {R : Type*} [CommRing A] [CommRing R] [Algebra A R]

/-- A power series over `R` is `A`-integral when each of its coefficients lies in the image of
`A`. For `A = ℤ` and `R = ℚ` these are the power series with integer coefficients. -/
def IntegralSeries (f : R⟦X⟧) : Prop :=
  ∀ n, coeff n f ∈ (algebraMap A R).range

/-- The integral lattice at scale `M`: the power series `f` over `R` for which `f(M X)` is
`A`-integral, that is, `Mⁿ * coeff n f` lies in the image of `A` for every `n`. It is the
preimage under `PowerSeries.rescale M` of the image of `A⟦X⟧`, hence a subring. -/
noncomputable def scaledIntegralSeries (M : R) : Subring R⟦X⟧ :=
  (map (algebraMap A R)).range.comap (rescale M)

/-- A power series `χ = X + a₂ X² + a₃ X³ + ⋯` tangent to the identity lies in the tangent
lattice at scale `M` when `Mⁿ⁻¹ aₙ` lies in the image of `A` for every `n ≥ 2`. Over a field
this says that `χ(M X) / M` is `A`-integral
(`TauCeti.tangentIntegralSeries_iff_integralSeries_inv_smul_rescale`). -/
structure TangentIntegralSeries (M : R) (χ : R⟦X⟧) : Prop where
  /-- The series has no constant term. -/
  coeff_zero : coeff 0 χ = 0
  /-- The linear coefficient of the series is `1`. -/
  coeff_one : coeff 1 χ = 1
  /-- Every coefficient of degree `n ≥ 2`, multiplied by `Mⁿ⁻¹`, is integral. -/
  pow_mul_coeff_mem : ∀ n, 2 ≤ n → M ^ (n - 1) * coeff n χ ∈ (algebraMap A R).range

variable {A}

/-! ### Integral series -/

/-- A power series is `A`-integral exactly when each coefficient lies in the image of `A`. -/
theorem integralSeries_iff {f : R⟦X⟧} :
    IntegralSeries A f ↔ ∀ n, coeff n f ∈ (algebraMap A R).range :=
  Iff.rfl

/-- A power series is `A`-integral exactly when it is the coefficientwise image of a power series
over `A`. -/
theorem integralSeries_iff_mem_range_map {f : R⟦X⟧} :
    IntegralSeries A f ↔ f ∈ (map (algebraMap A R)).range :=
  (mem_map_range _).symm

/-- A power series is `ℤ`-integral exactly when all its coefficients are integers. -/
theorem integralSeries_int_iff {f : R⟦X⟧} :
    IntegralSeries ℤ f ↔ ∀ n, ∃ a : ℤ, (a : R) = coeff n f := by
  simp [integralSeries_iff]

/-! ### The integral lattice at scale `M` -/

/-- A power series lies in the integral lattice at scale `M` exactly when `f(M X)` is the
coefficientwise image of a power series over `A`. -/
theorem mem_scaledIntegralSeries_iff_rescale_mem_range_map {M : R} {f : R⟦X⟧} :
    f ∈ scaledIntegralSeries A M ↔ rescale M f ∈ (map (algebraMap A R)).range :=
  Iff.rfl

/-- A power series lies in the integral lattice at scale `M` exactly when `Mⁿ * coeff n f` is
integral for every `n`. -/
theorem mem_scaledIntegralSeries_iff {M : R} {f : R⟦X⟧} :
    f ∈ scaledIntegralSeries A M ↔ ∀ n, M ^ n * coeff n f ∈ (algebraMap A R).range := by
  simp only [mem_scaledIntegralSeries_iff_rescale_mem_range_map, mem_map_range, coeff_rescale]

/-- The rescaling `f(M X)` is `A`-integral exactly when `f` lies in the integral lattice at
scale `M`. -/
@[simp]
theorem integralSeries_rescale_iff {M : R} {f : R⟦X⟧} :
    IntegralSeries A (rescale M f) ↔ f ∈ scaledIntegralSeries A M := by
  simp [mem_scaledIntegralSeries_iff, integralSeries_iff]

/-- At scale `M`, a power series lies in the `ℤ`-integral lattice exactly when every `Mⁿ aₙ` is an
integer. -/
theorem mem_scaledIntegralSeries_int_iff {M : R} {f : R⟦X⟧} :
    f ∈ scaledIntegralSeries ℤ M ↔ ∀ n, ∃ a : ℤ, (a : R) = M ^ n * coeff n f := by
  simp [mem_scaledIntegralSeries_iff]

/-- At scale `M`, a power series lies in the lattice of algebraic integers exactly when every
`Mⁿ aₙ` is integral over `ℤ`. -/
theorem mem_scaledIntegralSeries_integralClosure_iff {M : R} {f : R⟦X⟧} :
    f ∈ scaledIntegralSeries (integralClosure ℤ R) M ↔ ∀ n, IsIntegral ℤ (M ^ n * coeff n f) := by
  simp [mem_scaledIntegralSeries_iff, mem_integralClosure_iff]

/-- At scale one the integral lattice is the image of the power series over `A`. -/
theorem scaledIntegralSeries_one :
    scaledIntegralSeries A (1 : R) = (map (algebraMap A R)).range := by
  ext f
  simp [mem_scaledIntegralSeries_iff_rescale_mem_range_map]

/-- The integral lattice at scale one consists of the `A`-integral power series. -/
@[simp]
theorem mem_scaledIntegralSeries_one {f : R⟦X⟧} :
    f ∈ scaledIntegralSeries A (1 : R) ↔ IntegralSeries A f := by
  rw [scaledIntegralSeries_one, integralSeries_iff_mem_range_map]

/-- Rescaling by `N` moves the lattice at scale `N * M` onto the lattice at scale `M`. -/
@[simp]
theorem rescale_mem_scaledIntegralSeries_iff {M N : R} {f : R⟦X⟧} :
    rescale N f ∈ scaledIntegralSeries A M ↔ f ∈ scaledIntegralSeries A (N * M) := by
  simp only [mem_scaledIntegralSeries_iff_rescale_mem_range_map, rescale_rescale]

/-- Multiplying the scale by an integral factor enlarges the integral lattice. -/
theorem scaledIntegralSeries_le_mul (M : R) (c : A) :
    scaledIntegralSeries A M ≤ scaledIntegralSeries A (M * algebraMap A R c) := by
  rintro f ⟨g, hg⟩
  exact ⟨rescale c g, by rw [← rescale_map, hg, rescale_rescale]⟩

/-- If `M` divides `N`, the integral lattice at scale `M` is contained in the one at scale `N`. -/
theorem scaledIntegralSeries_le_of_dvd {M N : ℕ} (h : M ∣ N) :
    scaledIntegralSeries A (M : R) ≤ scaledIntegralSeries A (N : R) := by
  obtain ⟨c, rfl⟩ := h
  simpa using scaledIntegralSeries_le_mul (A := A) (M : R) c

/-- A constant power series lies in the integral lattice at any scale exactly when its value is
integral: rescaling does not change the constant coefficient. -/
@[simp]
theorem C_mem_scaledIntegralSeries_iff {M a : R} :
    C a ∈ scaledIntegralSeries A M ↔ a ∈ (algebraMap A R).range := by
  rw [← integralSeries_rescale_iff, rescale_C]
  refine ⟨fun h ↦ by simpa using h 0, fun h n ↦ ?_⟩
  rw [coeff_C]
  split_ifs
  exacts [h, zero_mem _]

/-! ### The tangent lattice at scale `M` -/

/-- The identity series `X` lies in the tangent lattice at every scale. -/
theorem tangentIntegralSeries_X (M : R) : TangentIntegralSeries A M (X : R⟦X⟧) where
  coeff_zero := by simp
  coeff_one := by simp
  pow_mul_coeff_mem n hn := by
    simp [coeff_X, show n ≠ 1 by omega]

/-- Over a field, `χ` lies in the tangent lattice at scale `M` exactly when it is tangent to the
identity, `χ = X + O(X²)`, and its normalized rescaling `χ(M X) / M` is `A`-integral. At `M = 0`
both the lattice condition and the integrality condition hold trivially. -/
theorem tangentIntegralSeries_iff_integralSeries_inv_smul_rescale {K : Type*} [Field K]
    [Algebra A K] {M : K} {χ : K⟦X⟧} :
    TangentIntegralSeries A M χ ↔
      coeff 0 χ = 0 ∧ coeff 1 χ = 1 ∧ IntegralSeries A (M⁻¹ • rescale M χ) := by
  rcases eq_or_ne M 0 with rfl | hM
  · refine ⟨fun h ↦ ⟨h.coeff_zero, h.coeff_one, fun n ↦ by simp⟩,
      fun ⟨h₀, h₁, _⟩ ↦ ⟨h₀, h₁, fun n hn ↦ by simp [zero_pow (show n - 1 ≠ 0 by omega)]⟩⟩
  have hcoeff (n : ℕ) : coeff (n + 1) (M⁻¹ • rescale M χ) = M ^ n * coeff (n + 1) χ := by
    rw [coeff_smul, coeff_rescale, smul_eq_mul, pow_succ', mul_assoc, inv_mul_cancel_left₀ hM]
  refine ⟨fun h ↦ ⟨h.coeff_zero, h.coeff_one, fun n ↦ ?_⟩,
    fun ⟨h₀, h₁, h⟩ ↦ ⟨h₀, h₁, fun n hn ↦ ?_⟩⟩
  · rcases n with _ | _ | n
    · simp [h.coeff_zero]
    · simp [hcoeff, h.coeff_one]
    · simpa [hcoeff] using h.pow_mul_coeff_mem (n + 2) (by omega)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ n by omega)
    simpa [hcoeff] using h (n + 1)

/-- A series in the tangent lattice at an integral scale `M` lies in the ordinary integral lattice
at scale `M`: `Mⁿ aₙ = M · Mⁿ⁻¹ aₙ`. -/
theorem TangentIntegralSeries.mem_scaledIntegralSeries {M : R} {χ : R⟦X⟧}
    (h : TangentIntegralSeries A M χ) (hM : M ∈ (algebraMap A R).range) :
    χ ∈ scaledIntegralSeries A M := by
  rw [mem_scaledIntegralSeries_iff]
  intro n
  rcases n with _ | _ | n
  · simp [h.coeff_zero]
  · simpa [h.coeff_one] using hM
  · have := mul_mem hM (h.pow_mul_coeff_mem (n + 2) (by omega))
    rwa [← mul_assoc, ← pow_succ'] at this

/-- Multiplying the scale by an integral factor preserves the tangent lattice condition. -/
theorem TangentIntegralSeries.mul_algebraMap {M : R} {χ : R⟦X⟧}
    (h : TangentIntegralSeries A M χ) (c : A) :
    TangentIntegralSeries A (M * algebraMap A R c) χ where
  coeff_zero := h.coeff_zero
  coeff_one := h.coeff_one
  pow_mul_coeff_mem n hn := by
    obtain ⟨b, hb⟩ := h.pow_mul_coeff_mem n hn
    exact ⟨c ^ (n - 1) * b, by rw [map_mul, map_pow, hb]; ring⟩

/-- If `M` divides `N`, the tangent lattice at scale `M` is contained in the one at scale `N`. -/
theorem TangentIntegralSeries.of_dvd {M N : ℕ} {χ : R⟦X⟧}
    (h : TangentIntegralSeries A (M : R) χ) (hMN : M ∣ N) :
    TangentIntegralSeries A (N : R) χ := by
  obtain ⟨c, rfl⟩ := hMN
  simpa using h.mul_algebraMap (c : A)

/-! ### Examples -/

section Examples

private theorem not_exists_intCast_eq_half : ¬ ∃ a : ℤ, (a : ℚ) = 1 / 2 := by
  rintro ⟨a, ha⟩
  have h : ((2 * a : ℤ) : ℚ) = 1 := by push_cast; rw [ha]; norm_num
  have : 2 * a = 1 := by exact_mod_cast h
  omega

/-- `∑ (X / 2)ⁿ` lies in the integral lattice at scale `2`, but not at scale `1`. -/
example : mk (fun n ↦ (1 / 2 : ℚ) ^ n) ∈ scaledIntegralSeries ℤ (2 : ℚ) ∧
    mk (fun n ↦ (1 / 2 : ℚ) ^ n) ∉ scaledIntegralSeries ℤ (1 : ℚ) := by
  refine ⟨mem_scaledIntegralSeries_int_iff.mpr fun n ↦ ⟨1, by simp⟩, fun h ↦ ?_⟩
  obtain ⟨a, ha⟩ := mem_scaledIntegralSeries_int_iff.mp h 1
  exact not_exists_intCast_eq_half ⟨a, by simpa using ha⟩

/-- The constant series `1 / 2` lies in the integral lattice at no scale. -/
example (M : ℚ) : C (1 / 2 : ℚ) ∉ scaledIntegralSeries ℤ M := by
  rw [C_mem_scaledIntegralSeries_iff]
  simpa using not_exists_intCast_eq_half

/-- `1 + X / 2` lies in the integral lattice at scale `2`, with scaled coefficients `1, 1`, but
not at scale `1`. -/
example : 1 + C (1 / 2 : ℚ) * X ∈ scaledIntegralSeries ℤ (2 : ℚ) ∧
    1 + C (1 / 2 : ℚ) * X ∉ scaledIntegralSeries ℤ (1 : ℚ) := by
  refine ⟨mem_scaledIntegralSeries_int_iff.mpr fun n ↦ ?_, fun h ↦ ?_⟩
  · rcases n with _ | _ | n
    · exact ⟨1, by simp⟩
    · exact ⟨1, by simp [coeff_one]⟩
    · exact ⟨0, by simp [coeff_one]⟩
  · obtain ⟨a, ha⟩ := mem_scaledIntegralSeries_int_iff.mp h 1
    exact not_exists_intCast_eq_half ⟨a, by simpa [coeff_one] using ha⟩

/-- `X + X² / 4` lies in the ordinary integral lattice at scale `2`, and in the tangent lattice
at scale `4`, but not at scale `2`. -/
example : X + C (1 / 4 : ℚ) * X ^ 2 ∈ scaledIntegralSeries ℤ (2 : ℚ) ∧
    ¬ TangentIntegralSeries ℤ (2 : ℚ) (X + C (1 / 4 : ℚ) * X ^ 2) ∧
    TangentIntegralSeries ℤ (4 : ℚ) (X + C (1 / 4 : ℚ) * X ^ 2) := by
  refine ⟨mem_scaledIntegralSeries_int_iff.mpr fun n ↦ ?_, fun h ↦ ?_, ⟨?_, ?_, fun n hn ↦ ?_⟩⟩
  · rcases n with _ | _ | _ | n
    · exact ⟨0, by simp⟩
    · exact ⟨2, by simp [coeff_X_pow]⟩
    · exact ⟨1, by norm_num [coeff_X, coeff_X_pow]⟩
    · exact ⟨0, by simp [coeff_X, coeff_X_pow]⟩
  · obtain ⟨a, ha⟩ := h.pow_mul_coeff_mem 2 le_rfl
    exact not_exists_intCast_eq_half ⟨a, by norm_num [coeff_X, coeff_X_pow] at ha; linarith⟩
  · simp
  · simp [coeff_X_pow]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rcases n with _ | n
    · exact ⟨1, by norm_num [coeff_X, coeff_X_pow]⟩
    · exact ⟨0, by simp [coeff_X, coeff_X_pow]⟩

/-- `X + X²` has normalized scale-one coefficients `0, 1, 1, 0, …`, all integral. -/
example : TangentIntegralSeries ℤ (1 : ℚ) (X + X ^ 2) := by
  refine ⟨by simp, by simp [coeff_X_pow], fun n hn ↦ ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rcases n with _ | n
  · exact ⟨1, by simp [coeff_X, coeff_X_pow]⟩
  · exact ⟨0, by simp [coeff_X, coeff_X_pow]⟩

/-- `X / 2` is not tangent to the identity, so it lies in the tangent lattice at no scale. -/
example (M : ℚ) : ¬ TangentIntegralSeries ℤ M (C (1 / 2 : ℚ) * X) := fun h ↦ by
  simpa using h.coeff_one

end Examples

end TauCeti
