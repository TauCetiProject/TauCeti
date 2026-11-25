/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
public import TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli
import Mathlib.Algebra.Algebra.Hom.Rat
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.LSeries.HurwitzZeta.Values
import TauCeti.NumberTheory.MulChar.GaloisOrbit

/-!
# Dirichlet L-values at the nonpositive integers

For a Dirichlet character `χ` modulo `N` and `k ≥ 1`, the continued Dirichlet L-function takes
the value `L(χ, 1 - k) = -Bₖ,χ / k`, where `Bₖ,χ` is the generalized Bernoulli number
`DirichletCharacter.generalizedBernoulli`. No primitivity is assumed: for an imprimitive `χ` both
sides carry the Euler factors at the primes dividing `N` but not the conductor. The convention
of `generalizedBernoulli`, with representatives in `{1, …, N}`, is the one that makes the formula
hold also at `N = 1`, `k = 1`, where it reads `ζ(0) = -1 / 2`.

The scalar `-Bₖ,χ / k` makes sense for a character with values in any `ℚ`-algebra `R`. It is
`DirichletCharacter.algebraicDirichletValue`, defined with its algebraic API in
`TauCeti.NumberTheory.DirichletCharacter.GeneralizedBernoulli`; it commutes with every
`ℚ`-algebra map, so for a character with values in a number field each complex embedding sends it
to the complex L-value of the embedded character. This is the common algebraic special value
through which complex and `p`-adic L-values are compared.

The complex formula reduces, via Mathlib's expression of `DirichletCharacter.LFunction` through
Hurwitz zeta functions, to `ZMod.LFunction_neg_nat`. The change-of-level formula is transported
from Mathlib's `DirichletCharacter.LFunction_changeLevel`.

## Main results

* `DirichletCharacter.LFunction_one_sub_natCast`: `L(χ, 1 - k) = -Bₖ,χ / k` for `k ≥ 1`.
* `DirichletCharacter.algebraicDirichletValue_complex`: a complex embedding `ι` sends the algebraic
  value of `χ` to `L(ι ∘ χ, 1 - k)`.
* `DirichletCharacter.algebraicDirichletValue_changeLevel` and
  `DirichletCharacter.algebraicDirichletValue_eq_primitiveCharacter_mul`: raising the level
  multiplies the value by `∏ (1 - χ(p) pᵏ⁻¹)` over the new primes.
* `DirichletCharacter.LFunction_kroneckerChar_neg_three_zero`: `L(χ₋₃, 0) = 1 / 3`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Theorem 4.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Essential Number
  Theory **4** (2025), §2.4.1 and §§5.1–5.2.
-/

public section

noncomputable section

open Complex

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- **Dirichlet L-values at the nonpositive integers.** For a Dirichlet character `χ` modulo `N`
and `k ≥ 1`, `L(χ, 1 - k) = -Bₖ,χ / k`. -/
theorem LFunction_one_sub_natCast (χ : DirichletCharacter ℂ N) {k : ℕ} (hk : k ≠ 0) :
    χ.LFunction (1 - k) = -χ.generalizedBernoulli k / k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  rw [LFunction, show (1 : ℂ) - (m + 1 : ℕ) = -(m : ℂ) by push_cast; ring, ZMod.LFunction_neg_nat,
    generalizedBernoulli_def]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, zpow_natCast, map_pow,
    map_natCast, Finset.mul_sum, Polynomial.eval_map_algebraMap]
  rw [← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [show ((if j = 0 then N else j.val : ℕ) : ℂ) / N =
      algebraMap ℚ ℂ (((if j = 0 then N else j.val : ℕ) : ℚ) / N) by
        rw [map_div₀, map_natCast, map_natCast],
    Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]
  ring

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **The complex image of the algebraic Dirichlet value.** For a character `χ` with values in a
`ℚ`-algebra `R`, a `ℚ`-algebra map `ι : R → ℂ` and `k ≥ 1`, the complex L-value of the character
`ι ∘ χ` at `1 - k` is the image of the algebraic value of `χ`. -/
theorem algebraicDirichletValue_complex (χ : DirichletCharacter R N) (ι : R →ₐ[ℚ] ℂ) {k : ℕ}
    (hk : k ≠ 0) :
    LFunction (χ.ringHomComp (ι : R →+* ℂ)) (1 - k) = ι (χ.algebraicDirichletValue k) := by
  rw [map_algebraicDirichletValue, algebraicDirichletValue_eq_neg_div,
    LFunction_one_sub_natCast _ hk]

/-- **Raising the level.** If `M ∣ N`, the algebraic Dirichlet value of a character `χ` with
values in a field of characteristic zero, viewed at level `N`, is that at level `M` times
`∏ (1 - χ(p) pᵏ⁻¹)` over the primes `p ∣ N`; the factors at primes dividing `M` are `1` unless
`M = 1`. -/
theorem algebraicDirichletValue_changeLevel {F : Type*} [Field F] [Algebra ℚ F] {M : ℕ}
    [NeZero M] (hMN : M ∣ N) (χ : DirichletCharacter F M) (k : ℕ) :
    (changeLevel hMN χ).algebraicDirichletValue k =
      χ.algebraicDirichletValue k * ∏ p ∈ N.primeFactors, (1 - χ p * (p : F) ^ (k - 1)) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  -- `χ` takes values in the subfield `K` generated by its values, which is algebraic over `ℚ`
  -- (`MulChar.isAlgebraic_adjoin_range`), so it embeds into `ℂ`; we transport Mathlib's
  -- `DirichletCharacter.LFunction_changeLevel` through such an embedding
  set K := IntermediateField.adjoin ℚ (Set.range χ)
  let χK : DirichletCharacter K M := χ.restrictValues
  let j : K →ₐ[ℚ] F := (K.val : K →+* F).toRatAlgHom
  have hχK : χK.ringHomComp (j : K →+* F) = χ := by
    rw [RingHom.toRatAlgHom_toRingHom]
    exact χ.ringHomComp_restrictValues
  -- prove the formula over `K` through a complex embedding `ι`
  let ι : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hK : (changeLevel hMN χK).algebraicDirichletValue k =
      χK.algebraicDirichletValue k * ∏ p ∈ N.primeFactors, (1 - χK p * (p : K) ^ (k - 1)) := by
    apply (ι : K →+* ℂ).injective
    simp only [AlgHom.coe_toRingHom, map_mul, map_prod, map_sub, map_one, map_pow, map_natCast,
      map_algebraicDirichletValue, ← changeLevel_ringHomComp]
    set ψ := χK.ringHomComp (ι : K →+* ℂ)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    have hL := LFunction_changeLevel hMN ψ (s := 1 - k) (Or.inr (by simpa using hk'))
    rw [LFunction_one_sub_natCast _ hk, LFunction_one_sub_natCast _ hk] at hL
    rw [algebraicDirichletValue_eq_neg_div, algebraicDirichletValue_eq_neg_div, hL]
    congr 1
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [show -(1 - (k : ℂ)) = ((k - 1 : ℕ) : ℂ) by push_cast [Nat.one_le_iff_ne_zero.mpr hk]; ring,
      cpow_natCast]
    simp only [ψ, MulChar.ringHomComp_apply, AlgHom.coe_toRingHom]
  -- and map it back to `F`
  rw [← hχK, changeLevel_ringHomComp, ← map_algebraicDirichletValue,
    ← map_algebraicDirichletValue, hK, map_mul, map_prod]
  simp only [MulChar.ringHomComp_apply, AlgHom.coe_toRingHom, map_sub, map_one, map_mul, map_pow,
    map_natCast]

/-- **Imprimitive characters.** The algebraic Dirichlet value of a character `χ` with values in a
field of characteristic zero is that of its primitive character `χ₀` times `∏ (1 - χ₀(p) pᵏ⁻¹)`
over the primes `p ∣ N`. -/
theorem algebraicDirichletValue_eq_primitiveCharacter_mul {F : Type*} [Field F] [Algebra ℚ F]
    (χ : DirichletCharacter F N) (k : ℕ) :
    χ.algebraicDirichletValue k = χ.primitiveCharacter.algebraicDirichletValue k *
      ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : F) ^ (k - 1)) := by
  conv_lhs => rw [← χ.changeLevel_primitiveCharacter]
  exact algebraicDirichletValue_changeLevel χ.conductor_dvd_level _ k

section KroneckerNegThree

local instance : NeZero (-3 : ℤ).natAbs := ⟨by decide⟩

/-- `L(χ₋₃, 0) = 1 / 3` for the quadratic character `(-3 / ·)` of conductor `3`. -/
theorem LFunction_kroneckerChar_neg_three_zero :
    (TauCeti.kroneckerChar ℂ (-3) (by decide) (by decide)).LFunction 0 = 1 / 3 := by
  have h := LFunction_one_sub_natCast (TauCeti.kroneckerChar ℂ (-3) (by decide) (by decide))
    one_ne_zero
  rw [Nat.cast_one, sub_self, generalizedBernoulli_one_kroneckerChar_neg_three] at h
  rw [h]
  norm_num

end KroneckerNegThree

end DirichletCharacter
