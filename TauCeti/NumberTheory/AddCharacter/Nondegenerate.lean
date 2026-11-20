/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.Algebra.Group.AddChar
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Nondegenerate additive characters of `ZMod p`

An additive character `ψ : ZMod p → Λ` with values in a commutative ring `Λ` is *nondegenerate*
when `ψ 1 - 1` is a unit of `Λ`. This is the condition under which the character sums of the
finite Fourier transform behave as they do for complex-valued characters, for an arbitrary
coefficient ring: Mathlib's `AddChar.sum_eq_zero_of_ne_one` and `AddChar.sum_mulShift` need a
domain as target, while nondegeneracy makes the same orthogonality hold in every commutative ring.
For a local ring in which `p` is invertible, nondegeneracy is nontriviality; for a product ring it
is stronger: `ψ 1 = (2, 1)` in `ZMod 7 × ZMod 7` defines a nontrivial character of `ZMod 3` whose
values do not sum to zero.

## Main definitions

* `AddChar.IsNondegenerate`: `ψ 1 - 1` is a unit.

## Main results

* `AddChar.IsNondegenerate.isUnit_sub_one`: `ψ a - 1` is a unit for every `a ≠ 0`.
* `AddChar.IsNondegenerate.isUnit_natCast` and `AddChar.IsNondegenerate.eval_cyclotomic`: `p` is a
  unit of `Λ`, and `ψ 1` is a root of the `p`-th cyclotomic polynomial.
* `AddChar.IsNondegenerate.isPrimitive`: over a nontrivial ring a nondegenerate character is
  primitive.
* `AddChar.IsNondegenerate.sum_apply_trace_mul`: orthogonality over a finite field `k` of
  characteristic `p`, `∑ x, ψ (Tr (x * y)) = if y = 0 then #k else 0`.
* `AddChar.isNondegenerate_iff_forall_isMaximal`: `ψ` is nondegenerate if and only if its reduction
  modulo every maximal ideal of `Λ` is nontrivial.
* `AddChar.isNondegenerate_iff_ne_one`: over a local ring in which `p` is a unit, nondegenerate
  means nontrivial.

## References

* N. Katz and G. Laumon, *Transformation de Fourier et majoration de sommes exponentielles*,
  Publ. Math. IHÉS 62 (1985), where nondegeneracy is nontriviality over a local coefficient ring.
* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987).

## Tags

additive character, nondegenerate character, orthogonality
-/

public section

open Finset

namespace AddChar

variable {p : ℕ} {Λ : Type*} [CommRing Λ] {ψ : AddChar (ZMod p) Λ}

/-- An additive character `ψ` of `ZMod p` with values in a commutative ring `Λ` is
*nondegenerate* if `ψ 1 - 1` is a unit of `Λ`.

For prime `p` this makes every `ψ a - 1` with `a ≠ 0` a unit (`IsNondegenerate.isUnit_sub_one`)
and forces `p` to be a unit of `Λ` (`IsNondegenerate.isUnit_natCast`). Over a local ring in which
`p` is a unit it is equivalent to `ψ ≠ 1` (`isNondegenerate_iff_ne_one`), but over a product of
rings it is stronger than nontriviality. -/
def IsNondegenerate (ψ : AddChar (ZMod p) Λ) : Prop :=
  IsUnit (ψ 1 - 1)

/-- Unfolding `AddChar.IsNondegenerate`. -/
theorem isNondegenerate_iff : ψ.IsNondegenerate ↔ IsUnit (ψ 1 - 1) :=
  Iff.rfl

/-- For a nondegenerate character `ψ` of `ZMod p`, `ψ a - 1` is a unit for every `a ≠ 0`. -/
theorem IsNondegenerate.isUnit_sub_one [Fact p.Prime] (hψ : ψ.IsNondegenerate) {a : ZMod p}
    (ha : a ≠ 0) : IsUnit (ψ a - 1) := by
  -- `ψ 1` is a power of `ψ a`, so `ψ a - 1` divides the unit `ψ 1 - 1`.
  have h : ψ 1 = ψ a ^ (a⁻¹).val := by
    rw [← map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ ha]
  refine isUnit_of_dvd_unit ?_ hψ
  rw [h]
  exact sub_one_dvd_pow_sub_one _ _

/-- A character of `ZMod p` is nondegenerate if and only if `ψ a - 1` is a unit for every
`a ≠ 0`. -/
theorem isNondegenerate_iff_forall_isUnit_sub_one [Fact p.Prime] :
    ψ.IsNondegenerate ↔ ∀ a : ZMod p, a ≠ 0 → IsUnit (ψ a - 1) :=
  ⟨fun hψ _ ha ↦ hψ.isUnit_sub_one ha, fun h ↦ h 1 one_ne_zero⟩

/-- The values of a nondegenerate character of `ZMod p` sum to zero. -/
theorem IsNondegenerate.sum_eq_zero [NeZero p] (hψ : ψ.IsNondegenerate) : ∑ a, ψ a = 0 :=
  sum_eq_zero_of_isUnit_sub_one hψ

/-- If `ψ` is a nondegenerate character of `ZMod p`, then `p` is a unit of the coefficient
ring. -/
theorem IsNondegenerate.isUnit_natCast [hp : Fact p.Prime] (hψ : ψ.IsNondegenerate) :
    IsUnit (p : Λ) := by
  -- Writing `ψ 1 = 1 + u`, the binomial theorem and `ψ 1 ^ p = 1` give `u ^ p ∈ p Λ`.
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out 1 (ψ 1 - 1)
  rw [add_sub_cancel, pow_char_eq_one, one_pow] at hr
  have hu : (p : Λ) * (-((ψ 1 - 1) * r)) = (ψ 1 - 1) ^ p := by linear_combination hr
  exact isUnit_of_mul_isUnit_left (hu ▸ hψ.pow p)

/-- The value `ψ 1` of a nondegenerate character of `ZMod p` is a root of the `p`-th cyclotomic
polynomial. -/
theorem IsNondegenerate.eval_cyclotomic [Fact p.Prime] (hψ : ψ.IsNondegenerate) :
    (Polynomial.cyclotomic p Λ).eval (ψ 1) = 0 := by
  have h := congrArg (Polynomial.eval (ψ 1)) (Polynomial.cyclotomic_prime_mul_X_sub_one Λ p)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, pow_char_eq_one, sub_self] at h
  exact hψ.mul_left_eq_zero.mp h

/-- Over a nontrivial ring, a nondegenerate character of `ZMod p` is primitive. The converse
fails: `ψ 1 = (2, 1)` in `ZMod 7 × ZMod 7` gives a primitive character of `ZMod 3` for which
`ψ 1 - 1 = (1, 0)` is not a unit. -/
theorem IsNondegenerate.isPrimitive [Fact p.Prime] [Nontrivial Λ] (hψ : ψ.IsNondegenerate) :
    ψ.IsPrimitive := by
  intro a ha h
  apply (hψ.isUnit_sub_one ha).ne_zero
  rw [← mul_one a, ← mulShift_apply, h, one_apply, sub_self]

/-- The inverse of a nondegenerate character is nondegenerate. -/
theorem IsNondegenerate.inv (hψ : ψ.IsNondegenerate) : ψ⁻¹.IsNondegenerate := by
  have h : ψ⁻¹ 1 - 1 = -(ψ (-1) * (ψ 1 - 1)) := by
    rw [inv_apply, mul_sub, ← map_add_eq_mul, neg_add_cancel, map_zero_eq_one, mul_one, neg_sub]
  rw [isNondegenerate_iff, h]
  exact ((ψ.val_isUnit _).mul hψ).neg

/-- Scaling a nondegenerate character by a nonzero `c`, `a ↦ ψ (c * a)`, gives a nondegenerate
character. -/
theorem IsNondegenerate.mulShift [Fact p.Prime] (hψ : ψ.IsNondegenerate) {c : ZMod p}
    (hc : c ≠ 0) : (ψ.mulShift c).IsNondegenerate := by
  rw [isNondegenerate_iff, mulShift_apply, mul_one]
  exact hψ.isUnit_sub_one hc

/-- The image of a nondegenerate character under a ring homomorphism is nondegenerate; in
particular nondegeneracy survives reduction modulo every ideal. -/
theorem IsNondegenerate.compAddChar {Λ' : Type*} [CommRing Λ'] (hψ : ψ.IsNondegenerate)
    (f : Λ →+* Λ') : (f.compAddChar ψ).IsNondegenerate := by
  simpa [isNondegenerate_iff] using hψ.map f

/-- A character of `ZMod p` is nondegenerate if and only if its reduction modulo every maximal
ideal of the coefficient ring is nontrivial. -/
theorem isNondegenerate_iff_forall_isMaximal [NeZero p] :
    ψ.IsNondegenerate ↔
      ∀ m : Ideal Λ, m.IsMaximal → (Ideal.Quotient.mk m).compAddChar ψ ≠ 1 := by
  have key (m : Ideal Λ) : (Ideal.Quotient.mk m).compAddChar ψ ≠ 1 ↔ ψ 1 - 1 ∉ m := by
    simp [zmod_char_ne_one_iff, ← Ideal.Quotient.eq_zero_iff_mem, sub_eq_zero]
  simp_rw [key]
  refine ⟨fun hψ m hm hmem ↦ hm.ne_top (Ideal.eq_top_of_isUnit_mem m hmem hψ), fun h ↦ ?_⟩
  by_contra hψ
  obtain ⟨m, hm, hmem⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hψ)
  exact h m hm hmem

/-- Over a local ring in which `p` is a unit (that is, of residue characteristic different from
`p`), a character of `ZMod p` is nondegenerate if and only if it is nontrivial. If `p` is not a
unit, no character is nondegenerate, by `IsNondegenerate.isUnit_natCast`. -/
theorem isNondegenerate_iff_ne_one [IsLocalRing Λ] (hp : IsUnit (p : Λ)) :
    ψ.IsNondegenerate ↔ ψ ≠ 1 := by
  have : NeZero p := ⟨by rintro rfl; exact not_isUnit_zero (by exact_mod_cast hp)⟩
  rw [zmod_char_ne_one_iff, ne_eq, ← sub_eq_zero]
  refine ⟨fun hψ ↦ hψ.ne_zero, fun hψ ↦ ?_⟩
  by_contra hnu
  -- `ψ 1 ≡ 1` modulo the maximal ideal, so `∑ i < p, ψ 1 ^ i ≡ p` is a unit, and multiplying it
  -- by `ψ 1 - 1` gives `ψ 1 ^ p - 1 = 0`.
  have h1 : IsLocalRing.residue Λ (ψ 1) = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue Λ), ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hs : IsUnit (∑ i ∈ range p, ψ 1 ^ i) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_sum]
    simp_rw [map_pow, h1, one_pow, sum_const, card_range, nsmul_one]
    exact_mod_cast (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hp
  refine hψ (hs.mul_right_eq_zero.mp ?_)
  rw [geom_sum_mul, pow_char_eq_one, sub_self]

/-- The characteristic of a finite ring carrying a nondegenerate character of `ZMod p` is prime
to `p`. -/
theorem IsNondegenerate.coprime_ringChar [hp : Fact p.Prime] [Finite Λ]
    (hψ : ψ.IsNondegenerate) : p.Coprime (ringChar Λ) :=
  (Nat.Prime.coprime_iff_not_dvd hp.out).mpr ((isUnit_iff_not_dvd_char Λ p).mp hψ.isUnit_natCast)

/-- Orthogonality for a nondegenerate character: the sum of `ψ (f x)` over a finite group
vanishes for every nonzero homomorphism `f` to `ZMod p`. -/
theorem IsNondegenerate.sum_apply_eq_zero [Fact p.Prime] {A : Type*} [AddGroup A] [Fintype A]
    (hψ : ψ.IsNondegenerate) {f : A →+ ZMod p} (hf : f ≠ 0) : ∑ x, ψ (f x) = 0 := by
  obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hf
  exact sum_eq_zero_of_isUnit_sub_one (φ := ψ.compAddMonoidHom f) (a := x₀)
    (hψ.isUnit_sub_one hx₀)

/-- Orthogonality of a nondegenerate character over a finite field `k` of characteristic `p`:
`∑ x, ψ (Tr_{k/𝔽_p} (x * y))` is `#k` when `y = 0` and `0` otherwise. -/
theorem IsNondegenerate.sum_apply_trace_mul [Fact p.Prime] {k : Type*} [Field k] [Fintype k]
    [DecidableEq k] [Algebra (ZMod p) k] (hψ : ψ.IsNondegenerate) (y : k) :
    ∑ x : k, ψ (Algebra.trace (ZMod p) k (x * y)) = if y = 0 then (Fintype.card k : Λ) else 0 := by
  split_ifs with hy
  · simp [hy]
  -- The trace form of the separable extension `k / 𝔽_p` is nondegenerate.
  have hf : (Algebra.trace (ZMod p) k).toAddMonoidHom.comp (AddMonoidHom.mulRight y) ≠ 0 := by
    intro h
    refine hy ((traceForm_nondegenerate (ZMod p) k).1 y fun x ↦ ?_)
    rw [Algebra.traceForm_apply, mul_comm]
    exact DFunLike.congr_fun h x
  exact hψ.sum_apply_eq_zero hf

end AddChar
