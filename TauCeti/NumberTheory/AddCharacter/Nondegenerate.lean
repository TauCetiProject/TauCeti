/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.NumberTheory.AddCharacter.Trace
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.Algebra.Group.AddChar
public import TauCeti.NumberTheory.LegendreSymbol.AddCharacter.Nondegenerate
public import TauCeti.RingTheory.Idempotents.Connected.Spectrum

/-!
# Further properties of nondegenerate additive characters of `ZMod p`

An additive character `ψ : ZMod p → Λ` of the prime field with values in a commutative ring `Λ` is
*nondegenerate* (`AddChar.IsNondegenerate`, in
`TauCeti.NumberTheory.LegendreSymbol.AddCharacter.Nondegenerate`) when `ψ 1 - 1` is a unit of `Λ`.
This file adds the evaluation and orthogonality results that the finite Fourier transform of
`Λ`-valued functions and the Artin–Schreier sheaves of Deligne, Katz and Laumon use, together with
the description of the values of `ψ` over a ring with connected spectrum.

## Main results

* `AddChar.isNondegenerate_zmodChar_iff`: the character sending `1` to a `p`-th root of unity `ζ`
  is nondegenerate exactly when `ζ - 1` is a unit.
* `AddChar.IsNondegenerate.apply_eq_one_iff`, `AddChar.IsNondegenerate.ne_one`,
  `AddChar.IsNondegenerate.isPrimitiveRoot`: over a nontrivial ring, `ψ` takes the value `1` only
  at `0`, is nontrivial, and `ψ 1` is a primitive `p`-th root of unity.
* `AddChar.IsNondegenerate.sum_comp_eq_ite`: for an additive map `f` from a finite group to
  `ZMod p`, `∑ x, ψ (f x)` is the order of the group if `f = 0` and `0` otherwise.
* `AddChar.IsNondegenerate.exists_apply_eq`: if `Spec Λ` is preconnected, every `p`-th root of
  unity of `Λ` is a value of `ψ`.
* `AddChar.IsNondegenerate.existsUnique_trace_mul`: if `Spec Λ` is connected, every additive
  character of a finite field `k` of characteristic `p` is `x ↦ ψ (Tr (c * x))` for a unique
  `c ∈ k`.

## References

* [N. Katz, G. Laumon, *Transformation de Fourier et majoration de sommes exponentielles*,
  Publ. Math. IHÉS 62 (1985)], §2.
* [G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987)], (0.2).
-/

public section

open Finset

namespace AddChar

variable {p : ℕ} [Fact p.Prime] {Λ : Type*} [CommRing Λ] {ψ : AddChar (ZMod p) Λ}

/-- The character of `ZMod p` sending `1` to a `p`-th root of unity `ζ` is nondegenerate exactly
when `ζ - 1` is a unit. -/
@[simp]
theorem isNondegenerate_zmodChar_iff {ζ : Λ} (hζ : ζ ^ p = 1) :
    (zmodChar p hζ).IsNondegenerate ↔ IsUnit (ζ - 1) := by
  rw [isNondegenerate_iff, zmodChar_apply, ZMod.val_one, pow_one]

/-- Over a nontrivial ring, a nondegenerate character takes the value `1` only at `0`. -/
@[simp]
theorem IsNondegenerate.apply_eq_one_iff [Nontrivial Λ] (hψ : ψ.IsNondegenerate) {a : ZMod p} :
    ψ a = 1 ↔ a = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero_eq_one]⟩
  by_contra ha
  simpa [h] using hψ.isUnit_sub_one ha

/-- Over a nontrivial ring, a nondegenerate character is nontrivial. -/
theorem IsNondegenerate.ne_one [Nontrivial Λ] (hψ : ψ.IsNondegenerate) : ψ ≠ 1 :=
  ne_one_iff.2 ⟨1, by simpa using hψ.apply_eq_one_iff.not.2 one_ne_zero⟩

/-- Over a nontrivial ring, the value at `1` of a nondegenerate character is a primitive `p`-th
root of unity. -/
theorem IsNondegenerate.isPrimitiveRoot [Nontrivial Λ] (hψ : ψ.IsNondegenerate) :
    IsPrimitiveRoot (ψ 1) p where
  pow_eq_one := ψ.pow_char_eq_one p 1
  dvd_of_pow_eq_one l hl := by
    rwa [← map_nsmul_eq_pow, nsmul_one, hψ.apply_eq_one_iff, ZMod.natCast_eq_zero_iff] at hl

/-- Composing a nondegenerate character with the trace of a `ZMod p`-algebra `A` gives Mathlib's
`AddChar.traceChar` at the primitive root `ψ 1`. -/
theorem IsNondegenerate.compAddMonoidHom_trace_eq_traceChar [Nontrivial Λ] (hψ : ψ.IsNondegenerate)
    (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    ψ.compAddMonoidHom (Algebra.trace (ZMod p) A).toAddMonoidHom =
      traceChar A hψ.isPrimitiveRoot := by
  ext x
  simp [traceChar_apply, ← map_nsmul_eq_pow]

/-- The values of a nondegenerate character sum to zero. -/
theorem IsNondegenerate.sum_eq_zero (hψ : ψ.IsNondegenerate) : ∑ a, ψ a = 0 :=
  sum_eq_zero_of_isLeftRegular_sub_one (isNondegenerate_iff.1 hψ).isRegular.left

/-- **Orthogonality.** For an additive map `f` from a finite group to `ZMod p`, the sum of a
nondegenerate character over the values of `f` is the order of the group if `f = 0` and `0`
otherwise. -/
theorem IsNondegenerate.sum_comp_eq_ite (hψ : ψ.IsNondegenerate) {G : Type*} [AddGroup G]
    [Fintype G] (f : G →+ ZMod p) [Decidable (f = 0)] :
    ∑ x, ψ (f x) = if f = 0 then (Fintype.card G : Λ) else 0 := by
  split_ifs with hf
  · simp [hf]
  obtain ⟨b, hb⟩ := DFunLike.ne_iff.1 hf
  exact sum_eq_zero_of_isLeftRegular_sub_one (ψ := ψ.compAddMonoidHom f) (b := b)
    (hψ.isUnit_sub_one hb).isRegular.left

section Connected

/-- **Roots of unity over a connected base.** If `Spec Λ` is preconnected, every `p`-th root of
unity of `Λ` is a value of a nondegenerate character `ψ`. Over `ZMod 7 × ZMod 7` with
`ψ 1 = (2, 2)` the root of unity `(2, 4)` is not a value of `ψ`, so connectedness cannot be
dropped. -/
theorem IsNondegenerate.exists_apply_eq [PreconnectedSpace (PrimeSpectrum Λ)]
    (hψ : ψ.IsNondegenerate) {η : Λ} (hη : η ^ p = 1) : ∃ a, ψ a = η := by
  by_contra hne
  push Not at hne
  -- the elements `e j = p⁻¹ ∑ i, η ^ i ψ (- j * i)` are idempotents summing to `1`, and
  -- `e j = 1` would force `η = ψ j`; so every `e j` vanishes and `Λ` is the zero ring
  set φ := zmodChar p hη
  set u : Λ := ↑hψ.isUnit_natCast.unit⁻¹
  have hup : u * p = 1 := hψ.isUnit_natCast.val_inv_mul
  -- the character `χ j = φ * (ψ.mulShift j)⁻¹` and its normalized sum `e j`
  set χ : ZMod p → AddChar (ZMod p) Λ := fun j ↦ φ * (ψ.mulShift j)⁻¹
  set e : ZMod p → Λ := fun j ↦ u * ∑ i, χ j i
  have hfix (j i : ZMod p) : χ j i * e j = e j := by
    simp only [e, mul_left_comm (χ j i), (χ j).apply_mul_sum]
  have hidem (j : ZMod p) : IsIdempotentElem (e j) := by
    have h : u * ∑ i, χ j i * e j = e j * e j := by
      simp only [e]
      rw [← sum_mul, ← mul_assoc]
    rw [IsIdempotentElem, ← h]
    simp only [hfix, sum_const, card_univ, ZMod.card, nsmul_eq_mul, ← mul_assoc, hup, one_mul]
  have hsum : ∑ j, e j = 1 := by
    simp only [e, χ, ← mul_sum, mul_apply, inv_apply, mulShift_apply]
    rw [sum_comm]
    simp only [← mul_sum, hψ.sum_mulShift, neg_eq_zero, mul_ite, mul_zero, sum_ite_eq',
      mem_univ, ite_true, map_zero_eq_one, one_mul, hup]
  have hzero (j : ZMod p) : e j = 0 := by
    refine (hidem j).eq_zero_or_eq_one_of_preconnectedSpace.resolve_right fun h1 ↦ hne j ?_
    have h := hfix j 1
    rw [h1, mul_one] at h
    simp only [χ, φ, mul_apply, inv_apply, mulShift_apply, zmodChar_apply, ZMod.val_one,
      pow_one, mul_neg, mul_one] at h
    have hj : ψ j * ψ (-j) = 1 := by rw [← map_add_eq_mul, add_neg_cancel, map_zero_eq_one]
    linear_combination η * hj - ψ j * h
  have : Subsingleton Λ := subsingleton_of_zero_eq_one <| by
    simpa only [hzero, sum_const_zero] using hsum
  exact hne 0 (Subsingleton.elim _ _)

/-- **Additive characters of a finite field over a connected base.** If `Spec Λ` is connected
and `ψ` is nondegenerate, every additive character of a finite field `k` of characteristic `p`
with values in `Λ` is `x ↦ ψ (Tr (c * x))` for a unique `c ∈ k`. -/
theorem IsNondegenerate.existsUnique_trace_mul [ConnectedSpace (PrimeSpectrum Λ)]
    (hψ : ψ.IsNondegenerate) {k : Type*} [Field k] [Finite k] [Algebra (ZMod p) k]
    (φ : AddChar k Λ) : ∃! c : k, ∀ x, φ x = ψ (Algebra.trace (ZMod p) k (c * x)) := by
  have : Nontrivial Λ := PrimeSpectrum.nonempty_iff_nontrivial.1 inferInstance
  have : CharP k p := (Algebra.charP_iff (ZMod p) k p).mp (ZMod.charP p)
  -- `φ` takes values in the `p`-th roots of unity, hence factors through `ψ`
  choose L hL using fun x ↦ hψ.exists_apply_eq (φ.pow_char_eq_one p x)
  let L' : k →+ ZMod p :=
    { toFun := L
      map_zero' := hψ.injective <| by rw [hL, map_zero_eq_one, map_zero_eq_one]
      map_add' x y := hψ.injective <| by rw [hL, map_add_eq_mul, map_add_eq_mul, hL, hL] }
  have hB := traceForm_nondegenerate (ZMod p) k
  refine ⟨((Algebra.traceForm (ZMod p) k).toDual hB).symm (L'.toZModLinearMap p), fun x ↦ ?_,
    fun c hc ↦ ?_⟩
  · rw [← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply,
      AddMonoidHom.coe_toZModLinearMap]
    exact (hL x).symm
  · refine ((Algebra.traceForm (ZMod p) k).toDual hB).injective (LinearMap.ext fun x ↦ ?_)
    rw [LinearEquiv.apply_symm_apply, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
      AddMonoidHom.coe_toZModLinearMap]
    exact hψ.injective ((hc x).symm.trans (hL x).symm)

end Connected

/-! ### Examples -/

/-- A nontrivial character into a non-reduced local ring of residue characteristic different
from `p` is nondegenerate: `18 ^ 3 = 1` and `18 - 1 = 17` is a unit in `ZMod 49`. -/
example : (zmodChar 3 (by decide : (18 : ZMod 49) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_zmodChar_iff]
  decide

/-- Nontriviality is not enough in residue characteristic `p`: the character of `ZMod 3` sending
`1` to `4` in `ZMod 9` is nontrivial, but `4 - 1 = 3` is not a unit. -/
example : ¬(zmodChar 3 (by decide : (4 : ZMod 9) ^ 3 = 1)).IsNondegenerate := by
  rw [isNondegenerate_zmodChar_iff]
  decide

/-- Over the disconnected `ZMod 7 × ZMod 7`, the `3`-rd root of unity `(2, 4)` is not a value of
the nondegenerate character sending `1` to `(2, 2)`. -/
example : (zmodChar 3 (by decide : ((2, 2) : ZMod 7 × ZMod 7) ^ 3 = 1)).IsNondegenerate ∧
    ∀ a, zmodChar 3 (by decide : ((2, 2) : ZMod 7 × ZMod 7) ^ 3 = 1) a ≠ (2, 4) := by
  refine ⟨by rw [isNondegenerate_zmodChar_iff]; decide, fun a ↦ ?_⟩
  rw [zmodChar_apply]
  fin_cases a <;> decide

/-- Over the zero ring, which has an empty, hence preconnected but not connected, spectrum, the
trivial character is nondegenerate but not primitive: the `Nontrivial` and connectedness
hypotheses cannot be dropped. -/
example : (1 : AddChar (ZMod 3) Unit).IsNondegenerate ∧ ¬(1 : AddChar (ZMod 3) Unit).IsPrimitive :=
  ⟨isNondegenerate_iff.2 (isUnit_of_subsingleton _),
    fun h ↦ h one_ne_zero (DFunLike.ext _ _ fun _ ↦ Subsingleton.elim _ _)⟩

/-- No character of `ZMod 3` with values in `ZMod 5` is nondegenerate: `ψ 1` would be a root of
`1 + X + X ^ 2`, which has no root in `ZMod 5`. -/
example : ∀ ψ : AddChar (ZMod 3) (ZMod 5), ¬ψ.IsNondegenerate := by
  intro ψ hψ
  have h := hψ.isRoot_cyclotomic
  rw [Polynomial.IsRoot, Polynomial.cyclotomic_prime, Polynomial.eval_geom_sum] at h
  generalize ψ 1 = x at h
  revert x
  decide

end AddChar
