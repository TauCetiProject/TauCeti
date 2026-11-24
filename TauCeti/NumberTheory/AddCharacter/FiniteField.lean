/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.AddCharacter.Trace
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import TauCeti.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# The canonical additive character of a finite field

Let `F` be a finite field of characteristic `p`. Its canonical additive character is
`ψ_F(x) = e(Tr(x) / p)`, where `e(t) = exp(2 π i t)` and `Tr : F → 𝔽_p` is the trace to the prime
field. It is the additive character against which Gauss, Jacobi and Kloosterman sums over `F` are
normally formed, and over a prime field `ZMod p` it is Mathlib's `ZMod.stdAddChar`.

The character `TauCeti.FiniteField.stdAddChar F` is defined intrinsically from `F`, with
`p = ringChar F` and Mathlib's `ZMod.algebra` structure, as Mathlib's trace character
`AddChar.traceChar` at the root of unity `exp(2 π i / p)`. Its value at `x` is computed in
terms of any `ZMod p`-algebra structure on `F` (all of them coincide), so that consumers which
fix such a structure, for instance to take traces, can use it directly.

Every additive character of `F` with complex values is a shift of `ψ_F`: as `ψ_F` is
primitive, `a ↦ ψ_F.mulShift a` is an isomorphism of `F` onto its character group
(`AddChar.IsPrimitive.mulShiftAddEquiv` applied to `TauCeti.FiniteField.isPrimitive_stdAddChar`),
and the nontrivial characters are the shifts by the nonzero elements
(`AddChar.IsPrimitive.mulShift_eq_one_iff`). In particular Gauss sums against any nontrivial
additive character reduce to Gauss sums against `ψ_F` (`gaussSum_mulShift_eq`). The general
facts about complex characters of a finite group apply to `ψ_F` as they stand: its values have
norm one (`AddChar.norm_apply`), its value at `-x` is the conjugate of its value at `x`
(`AddChar.map_neg_eq_conj`), and its sums over the multiples `x a` are the orthogonality
relations `AddChar.sum_mulShift`.

## Main definitions

* `TauCeti.FiniteField.stdAddChar F`: the canonical additive character `x ↦ e(Tr(x) / p)` of a
  finite field `F`.

## Main results

* `TauCeti.FiniteField.stdAddChar_eq_traceChar`: `stdAddChar F` is Mathlib's trace character at
  `exp(2 π i / p)`, for any `ZMod p`-algebra structure on `F`.
* `TauCeti.FiniteField.stdAddChar_apply`: `ψ_F(x) = ZMod.stdAddChar (Tr x)`.
* `TauCeti.FiniteField.stdAddChar_apply_eq_exp`: `ψ_F(x) = exp(2 π i (Tr x).val / p)`.
* `TauCeti.FiniteField.stdAddChar_apply_eq_one_iff`: the kernel of `ψ_F` is the kernel of the
  trace.
* `TauCeti.FiniteField.isPrimitive_stdAddChar`: `ψ_F` is primitive.
* `TauCeti.FiniteField.stdAddChar_zmod`: over `ZMod p`, `ψ_F` is `ZMod.stdAddChar`.
* `TauCeti.FiniteField.existsUnique_ne_zero_mulShift_stdAddChar_eq`: every nontrivial complex
  additive character of `F` is `ψ_F.mulShift u` for exactly one `u ≠ 0`.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, Chapter 5, §1 (the canonical additive
  character).
-/

public section

open Complex

namespace TauCeti.FiniteField

variable (F : Type*) [Field F] [Finite F]

/-- The **canonical additive character** of a finite field `F` of characteristic `p`:
`x ↦ e(Tr(x) / p)`, where `Tr : F → 𝔽_p` is the trace to the prime field and `e(t) = exp(2 π i t)`.
It is Mathlib's trace character `AddChar.traceChar` at the root of unity `exp(2 π i / p)`. -/
noncomputable def stdAddChar : AddChar F ℂ :=
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  AddChar.traceChar F (isPrimitiveRoot_exp (ringChar F) (Fact.out : (ringChar F).Prime).ne_zero)

variable {F}

/-- The canonical additive character of `F` is the trace character of `F` at `exp(2 π i / p)`,
read through any `ZMod p`-algebra structure on `F`. -/
theorem stdAddChar_eq_traceChar {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) F] :
    stdAddChar F =
      AddChar.traceChar F (isPrimitiveRoot_exp p (Fact.out : p.Prime).ne_zero) := by
  have : CharP F p := (Algebra.charP_iff (ZMod p) F p).mp (ZMod.charP p)
  -- Replace `p` by `ringChar F`, and the algebra structure by the one in the definition.
  obtain rfl : ringChar F = p := ringChar.eq F p
  obtain rfl : ‹Algebra (ZMod (ringChar F)) F› = ZMod.algebra F (ringChar F) :=
    Subsingleton.elim _ _
  rfl

/-- The value formula `ψ_F(x) = exp(2 π i (Tr x).val / p)` for the canonical additive character
of a finite field `F` of characteristic `p`, with the trace read in `{0, …, p - 1}`. -/
theorem stdAddChar_apply_eq_exp {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) F] (x : F) :
    stdAddChar F x = exp (2 * Real.pi * I * (Algebra.trace (ZMod p) F x).val / p) := by
  rw [stdAddChar_eq_traceChar (p := p), AddChar.traceChar_apply, ← exp_natCast_mul]
  congr 1
  ring

/-- The canonical additive character of `F` is `ZMod.stdAddChar` composed with the trace
`F → ZMod p`. -/
theorem stdAddChar_apply {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) F] (x : F) :
    stdAddChar F x = ZMod.stdAddChar (Algebra.trace (ZMod p) F x) := by
  rw [stdAddChar_apply_eq_exp (p := p), ZMod.stdAddChar_apply, ZMod.toCircle_apply]

/-- The kernel of the canonical additive character of `F` is the kernel of the trace to the prime
field. -/
theorem stdAddChar_apply_eq_one_iff {p : ℕ} [Fact p.Prime] [Algebra (ZMod p) F] {x : F} :
    stdAddChar F x = 1 ↔ Algebra.trace (ZMod p) F x = 0 := by
  rw [stdAddChar_eq_traceChar (p := p), AddChar.traceChar_apply_eq_one_iff]

variable (F)

/-- The canonical additive character of a finite field is nontrivial. -/
theorem stdAddChar_ne_one : stdAddChar F ≠ 1 := by
  let : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  rw [stdAddChar_eq_traceChar (p := ringChar F)]
  exact AddChar.traceChar_ne_one _

/-- The canonical additive character of a finite field is primitive. -/
theorem isPrimitive_stdAddChar : (stdAddChar F).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (stdAddChar_ne_one F)

/-- Over the prime field `ZMod p`, the canonical additive character is `ZMod.stdAddChar`, the
trace of `ZMod p` over itself being the identity. -/
@[simp]
theorem stdAddChar_zmod (p : ℕ) [Fact p.Prime] : stdAddChar (ZMod p) = ZMod.stdAddChar := by
  ext x
  rw [stdAddChar_apply (p := p), Algebra.trace_self_apply]

variable {F}

/-- Every nontrivial complex additive character of a finite field `F` is the shift
`ψ_F.mulShift u` of the canonical one by exactly one nonzero `u`. -/
theorem existsUnique_ne_zero_mulShift_stdAddChar_eq {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    ∃! u : F, u ≠ 0 ∧ (stdAddChar F).mulShift u = ψ := by
  obtain ⟨u, hu, huniq⟩ := (isPrimitive_stdAddChar F).existsUnique_mulShift_eq ψ
  refine ⟨u, ⟨?_, hu⟩, fun v hv ↦ huniq v hv.2⟩
  rintro rfl
  exact hψ (hu ▸ AddChar.mulShift_zero _)

end TauCeti.FiniteField
