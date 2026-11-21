/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import TauCeti.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# The canonical additive character of a finite field

Let `F` be a finite field of characteristic `p`. Its canonical additive character is
`ψ_F(x) = e(Tr(x) / p)`, where `Tr` is the trace from `F` to its prime field `ZMod p` and
`e(t) = exp(2 π i t)`. It is the additive character against which Gauss, Jacobi and Kloosterman
sums over `F` are normally written. Mathlib's `AddChar.FiniteField.primitiveChar_to_Complex` is a
primitive complex additive character chosen through an abstract cyclotomic extension, and its
values are not explicit; `ψ_F` has an explicit value formula.

`ψ_F` is primitive, so every complex additive character of `F` is `ψ_F.mulShift a` for exactly one
`a : F`, and the shifts form an isomorphism from `F` onto its group of complex additive characters
(`AddChar.IsPrimitive.existsUnique_mulShift_eq` and `AddChar.IsPrimitive.mulShiftAddEquiv`, in
`TauCeti.Analysis.Fourier.FiniteAbelian.PontryaginDuality`). A nontrivial character, such as
`AddChar.FiniteField.primitiveChar_to_Complex F`, is the shift by a nonzero element.
Its other standard properties hold for every complex additive character of a finite group and are
in Mathlib: `AddChar.norm_apply` (its values have norm one), `AddChar.map_neg_eq_conj` (its value
at `-x` is the conjugate of its value at `x`) and `AddChar.sum_mulShift` (the sum of its shift by
`a` is `#F` if `a = 0` and zero otherwise).

## Main definitions

* `TauCeti.FiniteField.stdAddChar F`: the canonical additive character `x ↦ e(Tr(x) / p)`.

## Main results

* `TauCeti.FiniteField.stdAddChar_apply`: for every prime `p` and every `ZMod p`-algebra
  structure on `F`, `ψ_F(x) = ZMod.stdAddChar (Tr(x))`, with the trace taken to `ZMod p`.
* `TauCeti.FiniteField.stdAddChar_apply_eq_exp`: the value formula
  `ψ_F(x) = exp(2 π i (Tr x).val / p)`.
* `TauCeti.FiniteField.isPrimitive_stdAddChar`: `ψ_F` is primitive.
* `TauCeti.FiniteField.stdAddChar_zmod`: on the prime field `ZMod p`, `ψ_F` is Mathlib's
  `ZMod.stdAddChar`.
* `TauCeti.FiniteField.existsUnique_ne_zero_mulShift_stdAddChar_eq`: every nontrivial complex
  additive character of `F` is `ψ_F.mulShift u` for exactly one `u ≠ 0`.
-/

public section

open Complex

namespace TauCeti.FiniteField

variable (F : Type*) [Field F] [Finite F]

/-- **The canonical additive character** `ψ_F(x) = e(Tr(x) / p)` of a finite field `F` of
characteristic `p`, where `Tr` is the trace from `F` to `ZMod p` and `e(t) = exp(2 π i t)`. -/
noncomputable def stdAddChar : AddChar F ℂ :=
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  haveI : NeZero (ringChar F) := ⟨(CharP.char_is_prime F (ringChar F)).ne_zero⟩
  (ZMod.stdAddChar : AddChar (ZMod (ringChar F)) ℂ).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

variable {F}

/-- `ψ_F(x)` is `ZMod.stdAddChar` at the trace of `x` to the prime field `ZMod p`. Any two
`ZMod p`-algebra structures on `F` agree, so this holds for whichever one is in scope. -/
theorem stdAddChar_apply (p : ℕ) [Fact p.Prime] [inst : Algebra (ZMod p) F] (x : F) :
    stdAddChar F x = ZMod.stdAddChar (Algebra.trace (ZMod p) F x) := by
  have := charP_of_injective_algebraMap' (A := F) (ZMod p) p
  obtain rfl := ringChar.eq F p
  obtain rfl : inst = ZMod.algebra F (ringChar F) := Subsingleton.elim _ _
  rfl

/-- The value formula `ψ_F(x) = exp(2 π i (Tr x).val / p)`, the trace to `ZMod p` read in
`{0, …, p - 1}`. -/
theorem stdAddChar_apply_eq_exp (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] (x : F) :
    stdAddChar F x = exp (2 * Real.pi * I * (Algebra.trace (ZMod p) F x).val / p) := by
  rw [stdAddChar_apply p, ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- The canonical additive character is nontrivial. -/
theorem stdAddChar_ne_one : stdAddChar F ≠ 1 := by
  set p := ringChar F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let : Algebra (ZMod p) F := ZMod.algebra F p
  obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod p) F 1
  intro h
  have h1 := DFunLike.congr_fun h x
  rw [stdAddChar_apply p, hx, one_apply, ← (ZMod.stdAddChar (N := p)).map_zero_eq_one,
    ZMod.injective_stdAddChar.eq_iff] at h1
  exact one_ne_zero h1

/-- The canonical additive character is primitive. -/
theorem isPrimitive_stdAddChar : (stdAddChar F).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one stdAddChar_ne_one

/-- On the prime field `ZMod p`, the canonical additive character is `ZMod.stdAddChar`. -/
@[simp]
theorem stdAddChar_zmod (p : ℕ) [Fact p.Prime] : stdAddChar (ZMod p) = ZMod.stdAddChar := by
  ext x
  rw [stdAddChar_apply p, Algebra.trace_self_apply]

/-- Every nontrivial complex additive character of a finite field `F` is the shift
`ψ_F.mulShift u` of the canonical one by exactly one nonzero `u`. -/
theorem existsUnique_ne_zero_mulShift_stdAddChar_eq {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∃! u : F, u ≠ 0 ∧ (stdAddChar F).mulShift u = ψ := by
  obtain ⟨u, hu, huniq⟩ := isPrimitive_stdAddChar.existsUnique_mulShift_eq ψ
  refine ⟨u, ⟨?_, hu⟩, fun v hv ↦ huniq v hv.2⟩
  rintro rfl
  exact hψ (hu ▸ AddChar.mulShift_zero _)

end TauCeti.FiniteField
