/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.RingTheory.Ideal.LiesOver

/-!
# Arithmetic Frobenius at a rational prime in a cyclotomic field

For a prime `p` coprime to `n`, the arithmetic Frobenius of an `n`-th cyclotomic field over
`ℚ` corresponds to `ZMod.unitOfCoprime p hp` under `IsCyclotomicExtension.Rat.galEquivZMod`.
The statements use a prime of the ring of integers lying over `(p)` in `ℤ`, so the exponent
is the rational prime itself. The formula identifies the Frobenius element in the Galois group.

## Implementation notes

The proof uses `TauCeti.NumberField.isArithFrobAt_iff_galEquivZMod_eq_absNorm` and
`Ideal.isArithFrobAt_ringOfIntegers_rat_iff` to compare the base rings `𝓞 ℚ` and `ℤ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §10.
-/

public section

open NumberField IsCyclotomicExtension Ideal IsDedekindDomain
open scoped NumberField

namespace TauCeti.NumberField

variable {n p : ℕ} [NeZero n] [Fact p.Prime]
  {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
  (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]

/-- At a rational prime coprime to `n`, an automorphism is arithmetic Frobenius exactly
when its cyclotomic exponent is `p mod n`, as a unit of `ZMod n`. -/
theorem isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime (hp : p.Coprime n)
    (σ : K ≃ₐ[ℚ] K) :
    IsArithFrobAt ℤ σ Q ↔ Rat.galEquivZMod n K σ = ZMod.unitOfCoprime p hp := by
  -- Contract `Q` to the rational ring of integers and identify its norm with `p`.
  have hnorm : absNorm (Q.under (𝓞 ℚ)) = p := by
    rw [absNorm_under_ringOfIntegers_rat, absNorm_apply, Submodule.cardQuot_apply,
      natCard_quotient_under_of_liesOver (p := p) Q]
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨Q.under (𝓞 ℚ), inferInstance, fun h ↦ (Fact.out : p.Prime).ne_zero
      (hnorm.symm.trans (by simp [h]))⟩
  -- The structure literal makes `v.asIdeal` definitionally the contraction of `Q`.
  -- This also supplies the `Q.LiesOver v.asIdeal` instance for the norm formula.
  have hn : (n : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd, hnorm]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hp
  -- Transport the Frobenius condition from `ℤ` to `𝓞 ℚ` before using the norm formula.
  rw [← isArithFrobAt_ringOfIntegers_rat_iff,
    isArithFrobAt_iff_galEquivZMod_eq_absNorm v hn Q σ, hnorm,
    ← ZMod.coe_unitOfCoprime p hp, Units.val_inj]

/-- Mathlib's chosen arithmetic Frobenius at a prime above `p` has cyclotomic exponent
`ZMod.unitOfCoprime p hp`. -/
theorem galEquivZMod_arithFrobAt [IsGalois ℚ K] [Finite (𝓞 K ⧸ Q)] (hp : p.Coprime n) :
    Rat.galEquivZMod n K (arithFrobAt ℤ (K ≃ₐ[ℚ] K) Q) = ZMod.unitOfCoprime p hp :=
  (isArithFrobAt_iff_galEquivZMod_eq_unitOfCoprime Q hp _).mp
    (IsArithFrobAt.arithFrobAt _ _ _)

end TauCeti.NumberField
