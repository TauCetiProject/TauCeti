/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Log
public import TauCeti.RingTheory.PowerSeries.Derivative
public import TauCeti.RingTheory.PowerSeries.Substitution
import TauCeti.RingTheory.Binomial

/-!
# The Mahler derivation of power series

The *Mahler derivation* of `R⟦X⟧` is the derivation `∂ = (1 + X) d/dX`. Writing `Y = 1 + X`,
it is the derivation `Y d/dY`, so it acts on the powers `Y ^ a` by `∂ (Y ^ a) = a Y ^ a`. Under the
Amice transform, which sends the Dirac measure at `a ∈ ℤ_p` to `(1 + X) ^ a`, the derivation `∂`
is therefore the transform of multiplying a measure by the coordinate function `x`; this is
proved in `TauCeti.NumberTheory.Padics.Measure.Moments`, where it turns integrals of `x ^ k` into
constant coefficients of iterated Mahler derivatives.

Over a `ℚ`-algebra, substituting `exp X - 1` for `X` conjugates `∂` to the ordinary derivative,
because `d/dX (exp X) = exp X = 1 + (exp X - 1)`. Consequently the constant coefficient of
`∂ ^ k F` is `k !` times the `k`-th coefficient of `F (exp X - 1)`, which is how the moments of a
measure are read off from the exponential substitution in its Amice transform.

For an exponent `r` in any binomial ring, such as `ℤ` or `ℤ_[p]`, the binomial series `(1 + X) ^ r`
is an eigenvector: `∂ ((1 + X) ^ r) = r (1 + X) ^ r`.

The logarithmic derivative of `∂` is the weighted logarithmic derivative `Δ f = (1 + X) f' f⁻¹` of a
unit `f` of `R⟦X⟧`, over any commutative ring `R`. It is a homomorphism from the multiplicative
group of units to the additive group of `R⟦X⟧`, it kills the constant units, and when `R` has no
additive torsion it kills nothing else. Under a substitution `g` it satisfies the chain rule
`(1 + g) Δ (f ∘ g) = ∂ g · (Δ f) ∘ g`, so that substituting `(1 + X) ^ r - 1` multiplies `Δ` by `r`.
This is the logarithmic derivative through which Coleman power series of norm-compatible units are
turned into measures.

## Main definitions

* `PowerSeries.mahlerDerivation R`: the derivation `(1 + X) d/dX` of `R⟦X⟧`.
* `PowerSeries.mahlerLogDeriv`: the logarithmic derivative `Δ f = (1 + X) f' f⁻¹` of a unit.

## Main results

* `PowerSeries.coeff_mahlerDerivation`: the `n`-th coefficient of `∂ F` is
  `(n + 1) a_{n + 1} + n a_n`.
* `PowerSeries.map_iterate_mahlerDerivation`: iterates of `∂` commute with coefficient maps.
* `PowerSeries.derivative_subst_exp_sub_one`: `d/dX (F (exp X - 1)) = (∂ F) (exp X - 1)`.
* `PowerSeries.constantCoeff_iterate_mahlerDerivation`: the constant coefficient of `∂ ^ k F`
  is `k !` times the `k`-th coefficient of `F (exp X - 1)`.
* `PowerSeries.mahlerDerivation_binomialSeries`: `∂ ((1 + X) ^ r) = r (1 + X) ^ r`.
* `PowerSeries.mahlerLogDeriv_mul`, `PowerSeries.mahlerLogDeriv_zpow`: `Δ (f g) = Δ f + Δ g` and
  `Δ (f ^ n) = n Δ f`.
* `PowerSeries.mahlerLogDeriv_eq_zero_iff`: without additive torsion, `Δ f = 0` exactly for
  constant `f`.
* `PowerSeries.map_mahlerLogDeriv`: `Δ` commutes with change of coefficients.
* `PowerSeries.one_add_mul_mahlerLogDeriv_of_coe_eq_subst`: the weighted chain rule.
* `PowerSeries.mahlerLogDeriv_eq_smul_subst_binomialSeries`:
  `Δ (f ((1 + X) ^ r - 1)) = r (Δ f) ((1 + X) ^ r - 1)`.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.1,
  Lemma 3.29 and Corollary 3.30; Proposition 12.5 and Definition 12.8 for the logarithmic
  derivative `Δ` and its behaviour under `(1 + X) ^ a - 1`.
* P. Colmez, *Fonctions d'une variable p-adique*, §II.2.
-/

public section

namespace PowerSeries

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- The Mahler derivation `(1 + X) d/dX` of `R⟦X⟧`. It is `Y d/dY` in the variable
`Y = 1 + X`, and under the Amice transform it corresponds to multiplying a measure on `ℤ_p` by the
coordinate function. -/
noncomputable def mahlerDerivation : Derivation R R⟦X⟧ R⟦X⟧ := (1 + X : R⟦X⟧) • derivative

variable {R}

theorem mahlerDerivation_apply (f : R⟦X⟧) :
    mahlerDerivation R f = (1 + X) * d⁄dX f := (rfl)

/-- The coefficients of the Mahler derivation: `coeff n (∂ f) = (n + 1) a_{n + 1} + n a_n`. -/
theorem coeff_mahlerDerivation (f : R⟦X⟧) (n : ℕ) :
    coeff n (mahlerDerivation R f) = (n + 1) * coeff (n + 1) f + n * coeff n f := by
  rw [mahlerDerivation_apply, add_mul, one_mul, map_add, coeff_derivative]
  rcases n with _ | n
  · simp [mul_comm]
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

@[simp]
theorem mahlerDerivation_C (r : R) : mahlerDerivation R (C r) = 0 := by
  simp [mahlerDerivation_apply]

@[simp]
theorem mahlerDerivation_X : mahlerDerivation R X = 1 + X := by
  simp [mahlerDerivation_apply]

/-- The Mahler derivation commutes with change of coefficients. -/
theorem map_mahlerDerivation {S : Type*} [CommSemiring S] (f : R →+* S) (F : R⟦X⟧) :
    map f (mahlerDerivation R F) = mahlerDerivation S (map f F) := by
  simp [mahlerDerivation_apply]

/-- Iterates of the Mahler derivation commute with change of coefficients. -/
theorem map_iterate_mahlerDerivation {S : Type*} [CommSemiring S] (f : R →+* S) (F : R⟦X⟧)
    (k : ℕ) : map f ((mahlerDerivation R)^[k] F) = (mahlerDerivation S)^[k] (map f F) := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, map_mahlerDerivation]

-- `∂X = 1 + X` rejects both `d/dX` and `X d/dX`.
example : mahlerDerivation ℤ X = 1 + X := by simp

example : mahlerDerivation ℤ ((1 + X) ^ 2) = C 2 * (1 + X) ^ 2 := by
  rw [mahlerDerivation_apply, derivative_pow]
  simp
  ring

end CommSemiring

section Exp

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Substituting `exp X - 1` conjugates the Mahler derivation to the ordinary derivative:
`d/dX (F (exp X - 1)) = (∂ F) (exp X - 1)`. -/
theorem derivative_subst_exp_sub_one (F : A⟦X⟧) :
    d⁄dX (F.subst (exp A - 1)) = (mahlerDerivation A F).subst (exp A - 1) := by
  have h := HasSubst.exp_sub_one (A := A)
  rw [mahlerDerivation_apply]
  apply derivative_subst_of_derivative_eq_subst h
  rw [subst_add h, subst_X h, ← coe_substAlgHom h, map_one]
  simp only [map_sub, derivative_exp, derivative_one, sub_zero, add_sub_cancel]

/-- The iterated form of `derivative_subst_exp_sub_one`. -/
theorem iterate_derivative_subst_exp_sub_one (F : A⟦X⟧) (k : ℕ) :
    d⁄dX^[k] (F.subst (exp A - 1)) = ((mahlerDerivation A)^[k] F).subst (exp A - 1) := by
  exact iterate_derivative_subst derivative_subst_exp_sub_one F k

/-- The constant coefficient of `∂ ^ k F` is `k !` times the `k`-th coefficient of
`F (exp X - 1)`. -/
theorem constantCoeff_iterate_mahlerDerivation (F : A⟦X⟧) (k : ℕ) :
    constantCoeff ((mahlerDerivation A)^[k] F) = k.factorial * coeff k (F.subst (exp A - 1)) := by
  exact constantCoeff_iterate_of_derivative_subst (by simp [constantCoeff_exp])
    derivative_subst_exp_sub_one F k

end Exp

section Binomial

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [BinomialRing S] [Algebra S R]

/-- The Mahler derivation has the binomial series `(1 + X) ^ r` as eigenvector with eigenvalue
`r`, for an exponent `r` in any binomial ring, for instance `ℤ` or `ℤ_[p]`. -/
@[simp]
theorem mahlerDerivation_binomialSeries (r : S) :
    mahlerDerivation R (binomialSeries R r) = r • binomialSeries R r := by
  ext n
  -- Act by `r` on coefficients first, then write both scalar actions through `algebraMap`.
  simp only [coeff_mahlerDerivation, binomialSeries_coeff, coeff_smul]
  simp only [Algebra.smul_def, mul_one]
  have h := congrArg (algebraMap S R) (TauCeti.Ring.add_one_nsmul_choose_add_one r n)
  rw [nsmul_eq_mul, map_mul, map_mul, map_sub, map_natCast] at h
  push_cast at h
  linear_combination h

/-- The Mahler derivation of `(1 + X) ^ m` is `m (1 + X) ^ m`, including for `m = 0`. -/
theorem mahlerDerivation_one_add_X_pow (m : ℕ) :
    mahlerDerivation R ((1 + X) ^ m) = m • (1 + X : R⟦X⟧) ^ m := by
  have h := mahlerDerivation_binomialSeries (R := R) ((m : ℕ) : ℤ)
  rw [binomialSeries_nat] at h
  rw [h]
  ext n
  simp

end Binomial

/-! ## The logarithmic derivative of units -/

section LogDeriv

variable {R : Type*} [CommRing R]

/-- The **Mahler logarithmic derivative** `Δ f = (1 + X) f' f⁻¹` of a unit `f` of `R⟦X⟧`: the
logarithmic derivative for the Mahler derivation `(1 + X) d/dX`. The inverse is the inverse of the
unit `f`, so no division is needed and `R` is an arbitrary commutative ring. It turns products of
units into sums (`PowerSeries.mahlerLogDeriv_mul`). -/
noncomputable def mahlerLogDeriv (f : R⟦X⟧ˣ) : R⟦X⟧ :=
  mahlerDerivation R f * ↑f⁻¹

theorem mahlerLogDeriv_def (f : R⟦X⟧ˣ) : mahlerLogDeriv f = mahlerDerivation R f * ↑f⁻¹ :=
  (rfl)

/-- The weighted formula `Δ f = (1 + X) f' f⁻¹`. -/
theorem mahlerLogDeriv_eq (f : R⟦X⟧ˣ) :
    mahlerLogDeriv f = (1 + X) * d⁄dX (f : R⟦X⟧) * ((f⁻¹ : R⟦X⟧ˣ) : R⟦X⟧) := by
  rw [mahlerLogDeriv_def, mahlerDerivation_apply]

/-- `Δ f` is the unique series `g` with `∂ f = g f`. -/
theorem mahlerLogDeriv_eq_iff {f : R⟦X⟧ˣ} {g : R⟦X⟧} :
    mahlerLogDeriv f = g ↔ mahlerDerivation R f = g * f := by
  rw [mahlerLogDeriv_def, Units.mul_inv_eq_iff_eq_mul]

/-- The defining identity `Δ f · f = ∂ f`. -/
theorem mahlerLogDeriv_mul_coe (f : R⟦X⟧ˣ) : mahlerLogDeriv f * f = mahlerDerivation R f :=
  (mahlerLogDeriv_eq_iff.mp rfl).symm

@[simp]
theorem mahlerLogDeriv_one : mahlerLogDeriv (1 : R⟦X⟧ˣ) = 0 := by
  simp [mahlerLogDeriv_def]

/-- The Mahler logarithmic derivative turns products into sums. -/
@[simp]
theorem mahlerLogDeriv_mul (f g : R⟦X⟧ˣ) :
    mahlerLogDeriv (f * g) = mahlerLogDeriv f + mahlerLogDeriv g := by
  rw [mahlerLogDeriv_eq_iff, Units.val_mul, Derivation.leibniz, ← mahlerLogDeriv_mul_coe f,
    ← mahlerLogDeriv_mul_coe g, smul_eq_mul, smul_eq_mul]
  ring

@[simp]
theorem mahlerLogDeriv_inv (f : R⟦X⟧ˣ) : mahlerLogDeriv f⁻¹ = -mahlerLogDeriv f := by
  rw [eq_neg_iff_add_eq_zero, ← mahlerLogDeriv_mul, inv_mul_cancel, mahlerLogDeriv_one]

@[simp]
theorem mahlerLogDeriv_pow (f : R⟦X⟧ˣ) (n : ℕ) : mahlerLogDeriv (f ^ n) = n • mahlerLogDeriv f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mahlerLogDeriv_mul, ih, succ_nsmul]

@[simp]
theorem mahlerLogDeriv_zpow (f : R⟦X⟧ˣ) (n : ℤ) :
    mahlerLogDeriv (f ^ n) = n • mahlerLogDeriv f := by
  cases n with
  | ofNat n => simp
  | negSucc n => rw [zpow_negSucc, mahlerLogDeriv_inv, mahlerLogDeriv_pow, negSucc_zsmul]

/-- Constant units have vanishing Mahler logarithmic derivative. -/
@[simp]
theorem mahlerLogDeriv_map_C (c : Rˣ) :
    mahlerLogDeriv (Units.map ((C : R →+* R⟦X⟧) : R →* R⟦X⟧) c) = 0 := by
  simp [mahlerLogDeriv_def]

/-- Over a ring without additive torsion, the units with vanishing Mahler logarithmic derivative
are exactly the constant units. Over `ZMod 3` the nonconstant unit `1 + X ^ 3` has `Δ = 0`. -/
theorem mahlerLogDeriv_eq_zero_iff [HasUniqueDiv R] {f : R⟦X⟧ˣ} :
    mahlerLogDeriv f = 0 ↔ (f : R⟦X⟧) = C (constantCoeff (f : R⟦X⟧)) := by
  refine ⟨fun h ↦ derivative.ext ?_ (by simp), fun h ↦ ?_⟩
  · have hY : IsUnit (1 + X : R⟦X⟧) := isUnit_iff_constantCoeff.mpr (by simp)
    rw [mahlerLogDeriv_eq_iff, zero_mul, mahlerDerivation_apply] at h
    rw [hY.mul_right_eq_zero.mp h, derivative_C]
  · rw [mahlerLogDeriv_eq_iff, zero_mul, h, mahlerDerivation_C]

/-- Change of coefficients commutes with the Mahler logarithmic derivative. -/
theorem map_mahlerLogDeriv {S : Type*} [CommRing S] (φ : R →+* S) (f : R⟦X⟧ˣ) :
    map φ (mahlerLogDeriv f) = mahlerLogDeriv (Units.map (map φ : R⟦X⟧ →* S⟦X⟧) f) := by
  simp [mahlerLogDeriv_def, map_mahlerDerivation]

/-- The weighted chain rule: if the unit `u` is the substitution `f ∘ g` of a unit `f`, then
`(1 + g) Δ u = ∂ g · (Δ f) ∘ g`. No division by `g` or `1 + g` is involved. -/
theorem one_add_mul_mahlerLogDeriv_of_coe_eq_subst {g : R⟦X⟧} (hg : HasSubst g) {f u : R⟦X⟧ˣ}
    (hu : (u : R⟦X⟧) = (f : R⟦X⟧).subst g) :
    (1 + g) * mahlerLogDeriv u = mahlerDerivation R g * (mahlerLogDeriv f).subst g := by
  simp only [mahlerLogDeriv_def, coe_inv_eq_subst_of_coe_eq_subst hg hu, hu,
    mahlerDerivation_apply, derivative_subst hg, subst_mul hg, subst_add hg, subst_X hg,
    subst_one]
  ring

/-- If `∂ g = a (1 + g)` and the unit `u` is the substitution `f ∘ g` of a unit `f`, then
`Δ u = a · (Δ f) ∘ g`. -/
theorem mahlerLogDeriv_eq_mul_subst {g a : R⟦X⟧} (hg : HasSubst g)
    (h : mahlerDerivation R g = a * (1 + g)) {f u : R⟦X⟧ˣ}
    (hu : (u : R⟦X⟧) = (f : R⟦X⟧).subst g) :
    mahlerLogDeriv u = a * (mahlerLogDeriv f).subst g := by
  have hunit : IsUnit (1 + g) := by
    rw [isUnit_iff_constantCoeff, map_add, map_one, constantCoeff_eq]
    exact hg.isUnit_one_add
  apply hunit.mul_left_cancel
  rw [one_add_mul_mahlerLogDeriv_of_coe_eq_subst hg hu, h]
  ring

/-- Substituting `(1 + X) ^ r - 1` multiplies the Mahler logarithmic derivative by `r`, for an
exponent `r` in any binomial ring such as `ℤ` or `ℤ_[p]`: if `u = f ((1 + X) ^ r - 1)`, then
`Δ u = r · (Δ f) ((1 + X) ^ r - 1)`. -/
theorem mahlerLogDeriv_eq_smul_subst_binomialSeries {S : Type*} [CommRing S] [BinomialRing S]
    [Algebra S R] (r : S) {f u : R⟦X⟧ˣ}
    (hu : (u : R⟦X⟧) = (f : R⟦X⟧).subst (binomialSeries R r - 1)) :
    mahlerLogDeriv u = r • (mahlerLogDeriv f).subst (binomialSeries R r - 1) := by
  rw [Algebra.smul_def]
  refine mahlerLogDeriv_eq_mul_subst (TauCeti.hasSubst_binomialSeries_sub_one r) ?_ hu
  rw [map_sub, Derivation.map_one_eq_zero, sub_zero, mahlerDerivation_binomialSeries,
    add_sub_cancel, Algebra.smul_def]

/-- Substituting `(1 + X) ^ m - 1` multiplies the Mahler logarithmic derivative by `m`: if
`u = f ((1 + X) ^ m - 1)`, then `Δ u = m · (Δ f) ((1 + X) ^ m - 1)`. -/
theorem mahlerLogDeriv_eq_nsmul_subst_one_add_X_pow (m : ℕ) {f u : R⟦X⟧ˣ}
    (hu : (u : R⟦X⟧) = (f : R⟦X⟧).subst ((1 + X : R⟦X⟧) ^ m - 1)) :
    mahlerLogDeriv u = m • (mahlerLogDeriv f).subst ((1 + X : R⟦X⟧) ^ m - 1) := by
  rw [nsmul_eq_mul]
  refine mahlerLogDeriv_eq_mul_subst (.of_constantCoeff_zero' (by simp)) ?_ hu
  rw [map_sub, Derivation.map_one_eq_zero, sub_zero, mahlerDerivation_one_add_X_pow,
    add_sub_cancel, nsmul_eq_mul]

-- The weight `1 + X` is visible: `Δ (1 + X) = 1`, whereas `f' f⁻¹` would be `(1 + X)⁻¹`.
example (f : ℤ⟦X⟧ˣ) (hf : (f : ℤ⟦X⟧) = 1 + X) : mahlerLogDeriv f = 1 := by
  simp [mahlerLogDeriv_eq_iff, hf]

-- The inverse carries the sign: `Δ ((1 + X)⁻¹) = -1`.
example (f : ℤ⟦X⟧ˣ) (hf : (f : ℤ⟦X⟧) = 1 + X) : mahlerLogDeriv f⁻¹ = -1 := by
  simp [mahlerLogDeriv_eq_iff, hf]

-- Without additive torsion-freeness the kernel is larger: over `ZMod 3` the nonconstant unit
-- `1 + X ^ 3` has vanishing Mahler logarithmic derivative.
example (f : (ZMod 3)⟦X⟧ˣ) (hf : (f : (ZMod 3)⟦X⟧) = 1 + X ^ 3) :
    mahlerLogDeriv f = 0 ∧ (f : (ZMod 3)⟦X⟧) ≠ C (constantCoeff (f : (ZMod 3)⟦X⟧)) := by
  refine ⟨?_, fun h ↦ ?_⟩
  · have h3 : (3 : (ZMod 3)⟦X⟧) = 0 := by
      rw [← map_ofNat C, CharP.ofNat_eq_zero (ZMod 3) 3, map_zero]
    simp [mahlerLogDeriv_eq_iff, hf, mahlerDerivation_apply, h3]
  · have h3 := congrArg (coeff 3) h
    rw [hf] at h3
    simp at h3

end LogDeriv

end PowerSeries
