/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.HostField.Basic
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.NumberField.Cyclotomic.RootDiscr
import TauCeti.NumberTheory.NumberField.Discriminant.Basic

/-!
# Arithmetic of the cyclotomic host for prime level selection

The discriminant of `ℚ(√-d)` gives the modulus condition for selecting split auxiliary
primes. The host `ℚ(√-d)(ζ)` has root discriminant at most `q₁(s) * d`, which bounds its
contribution to the logarithmic level endpoint. It also contains a primitive fourth root
of unity, so representations of primes as sums of two squares give integral norm witnesses
in the host.

These inputs are used in `New.rootDiscr_mem_Icc` and
`New.Parameters.IsLargeScale.exists_isAdmissibleData` in `New/Reduction/Data/AdmissibleData.lean`
and `New/Reduction/Data/Existence.lean` of lsernau/grh-lean at `72fead1`. The upper bound below
uses monotonicity in the ambient rational cyclotomic field rather than the different ideal.
-/

public section

open NumberField

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- The imaginary quadratic base is a quadratic extension of `ℚ`. -/
instance instIsQuadraticExtensionBaseField : Algebra.IsQuadraticExtension ℚ P.baseField :=
  ⟨P.finrank_baseField⟩

/-- The imaginary quadratic base is a CM field, with complex conjugation over `ℚ`. -/
instance instIsCMFieldBaseField : IsCMField P.baseField :=
  IsCMField.ofCMExtension ℚ P.baseField

/-- The discriminant of the imaginary quadratic base is `-d`. -/
@[simp] theorem discr_baseField : discr P.baseField = -(P.d : ℤ) := by
  have hd : (-(P.d : ℤ)) % 4 = 1 := by
    have := P.d_mod_eight
    omega
  let z := QuadraticAlgebra.sqrtRadicand (-(P.d : ℚ))
  let K := IntermediateField.adjoin ℚ ({z} : Set ℂ)
  let e : P.baseField ≃ₐ[ℚ] K := IntermediateField.equivOfEq P.baseField_eq_adjoin
  let : NumberField K :=
    { to_finiteDimensional := FiniteDimensional.of_surjective e.toLinearMap e.surjective }
  have hdpos : (0 : ℚ) < P.d := Nat.cast_pos.mpr P.prime_d.pos
  have hnsq : ¬ IsSquare ((-(P.d : ℤ) : ℤ) : ℚ) := by
    push_cast
    exact not_isSquare_of_neg (neg_neg_of_pos hdpos)
  calc
    discr P.baseField = discr K := discr_eq_discr_of_algEquiv P.baseField e
    _ = Multiquadratic.fundamentalDiscriminant (-(P.d : ℤ)) :=
      Multiquadratic.discr_adjoin_singleton_eq_fundamentalDiscriminant
        (Int.squarefree_natCast.mpr P.prime_d.squarefree).neg (x := z) (by simp [z, sq]) hnsq
    _ = -(P.d : ℤ) := Multiquadratic.fundamentalDiscriminant_of_mod_four_eq_one hd

/-- The root discriminant of the host is between `1` and the ambient cyclotomic order. -/
theorem rootDiscr_hostField_mem_Icc (s : ℕ) :
    rootDiscr (P.hostField s) ∈ Set.Icc 1 (P.q₁ s * P.d : ℝ) := by
  refine ⟨?_, ?_⟩
  · simpa only [rootDiscr_rat] using
      (TauCeti.NumberField.rootDiscr_le_of_extension ℚ (P.hostField s))
  let n := P.q₁ s * P.d
  have hn : n ≠ 0 := Nat.mul_ne_zero (P.q₁_pos s).ne' P.prime_d.ne_zero
  let : NeZero n := ⟨hn⟩
  let ξ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hξ : IsPrimitiveRoot ξ n := Complex.isPrimitiveRoot_exp n hn
  let C := IntermediateField.adjoin ℚ ({ξ} : Set ℂ)
  let : IsCyclotomicExtension {n} ℚ C := hξ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let : NumberField C := IsCyclotomicExtension.numberField {n} ℚ C
  let f : P.hostField s →ₐ[ℚ] C := IntermediateField.inclusion (P.hostField_le_cyclotomic s hξ)
  let : Algebra (P.hostField s) C := f.toRingHom.toAlgebra
  simpa only [n, Nat.cast_mul] using
    (TauCeti.NumberField.rootDiscr_le_of_extension (P.hostField s) C).trans
      (IsCyclotomicExtension.Rat.rootDiscr_le n C)

/-- The host contains a primitive fourth root of unity, obtained from its chosen generator. -/
theorem exists_isPrimitiveRoot_four_hostField (s : ℕ) :
    ∃ i : P.hostField s, IsPrimitiveRoot i 4 := by
  have h : 4 ∣ P.q₁ s := ((by decide : 4 ∣ 18480).trans P.dvd_q₀).trans (P.q₀_dvd_q₁ s)
  obtain ⟨k, hk⟩ := h
  exact ⟨_, (P.isPrimitiveRoot_hostRoot s).pow (P.q₁_pos s) (hk.trans (mul_comm 4 k))⟩

end TauCeti.OneSidedBound.Parameters
