/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
-- Proof-only: `deg [n] = n²`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree

/-!
# The function field is Galois over its pullback along `[n]`

Let `W` be an elliptic curve over a separably closed field `F`, and `n` an integer invertible in
`F`. The pullback of multiplication by `n` embeds the function field `F(W)` in itself, and the
translations by the `n`-torsion points fix its image `[n]^*F(W)`. This file shows that they fix
nothing more, and that there is no other symmetry: `F(W)` is Galois over `[n]^*F(W)`, and every
automorphism of `F(W)` over it is the translation by an `n`-torsion point (AEC III.4.10(c) for
`[n]`).

Everything follows from a count. Over a separably closed field with `n` invertible the kernel of
`[n]` has `n²` points (`TauCeti.Isogeny.card_ker_mulByIntIsogeny`), and `[n]` has degree `n²`
(`TauCeti.Isogeny.degree_mulByIntIsogeny`). An isogeny whose kernel has as many points as its degree
is exactly one whose kernel cuts out the pulled-back field
(`TauCeti.Isogeny.card_ker_eq_degree_iff`), and the two Galois statements are then the Galois
correspondence for the finite translation action
(`WeierstrassCurve.Affine.isGalois_translationFixedField` and
`WeierstrassCurve.Affine.fixingSubgroup_translationFixedField`).

## Main results

* `TauCeti.Isogeny.card_ker_mulByIntIsogeny_eq_degree`: `#ker [n] = deg [n]`.
* `TauCeti.Isogeny.translationFixedField_ker_mulByIntIsogeny`: the functions fixed by every
  `n`-torsion translation are exactly the pullbacks along `[n]`.
* `TauCeti.Isogeny.mem_fieldRange_mulByIntIsogeny_iff`: the same, as a membership test.
* `TauCeti.Isogeny.isGalois_fieldRange_mulByIntIsogeny`: `F(W)` is Galois over `[n]^*F(W)`.
* `TauCeti.Isogeny.mem_fixingSubgroup_fieldRange_mulByIntIsogeny_iff`: the automorphisms of `F(W)`
  over `[n]^*F(W)` are exactly the translations by `n`-torsion points.

## Use

The Weil pairing uses these results in both directions. A function whose `n`-th power is pulled
back along `[n]` is moved by each `n`-torsion translation only by an `n`-th root of unity, which is
what makes the pairing well defined. A function that no `n`-torsion translation moves is itself
pulled back along `[n]`, which is the step of AEC III.8.1(c) that makes the pairing
nondegenerate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, III.6.4, III.8.1.
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic] {n : ℤ} {hn : psiFunctionField W n ≠ 0}

/-- **`#ker [n] = deg [n]`** over a separably closed field in which `n` is invertible: both are
`n²`. -/
theorem card_ker_mulByIntIsogeny_eq_degree (hchar : (n : F) ≠ 0) :
    Nat.card (mulByIntIsogeny W hn).ker = (mulByIntIsogeny W hn).degree := by
  rw [card_ker_mulByIntIsogeny W hchar, degree_mulByIntIsogeny]

/-- **The `n`-torsion translations fix exactly the pullbacks along `[n]`**, over a separably
closed field in which `n` is invertible: `F(W)^{E[n]} = [n]^*F(W)`. -/
@[simp]
theorem translationFixedField_ker_mulByIntIsogeny (hchar : (n : F) ≠ 0) :
    translationFixedField W (mulByIntIsogeny W hn).ker =
      (mulByIntIsogeny W hn).fieldPullback.fieldRange :=
  le_antisymm ((card_ker_eq_degree_iff _).mp (card_ker_mulByIntIsogeny_eq_degree W hchar))
    (by rw [ker_def]; exact le_translationFixedField_translationFixingSubgroup W _)

-- Not `@[simp]`: Mathlib's `AlgHom.mem_fieldRange` rewrites the left-hand side first, so `simpNF`
-- rejects it as not in simp normal form.
/-- **A function is a pullback along `[n]` exactly when no `n`-torsion translation moves it**,
over a separably closed field in which `n` is invertible. -/
theorem mem_fieldRange_mulByIntIsogeny_iff (hchar : (n : F) ≠ 0) {z : W.FunctionField} :
    z ∈ (mulByIntIsogeny W hn).fieldPullback.fieldRange ↔
      ∀ P : (W⁄F).toAffine.Point, n • P = 0 → translation W P z = z := by
  rw [← translationFixedField_ker_mulByIntIsogeny W hchar, mem_translationFixedField_iff]
  simp only [mem_ker_mulByIntIsogeny_iff]

omit [DecidableEq F] in
/-- **`F(W)` is Galois over its pullback along `[n]`**, over a separably closed field in which
`n` is invertible. -/
theorem isGalois_fieldRange_mulByIntIsogeny (hchar : (n : F) ≠ 0) :
    IsGalois (mulByIntIsogeny W hn).fieldPullback.fieldRange W.FunctionField := by
  classical
  rw [← translationFixedField_ker_mulByIntIsogeny W hchar]
  infer_instance

-- Not `@[simp]`: Mathlib's `IntermediateField.mem_fixingSubgroup_iff` rewrites the left-hand side
-- first, so `simpNF` rejects it as not in simp normal form.
/-- **The automorphisms of `F(W)` over `[n]^*F(W)` are the `n`-torsion translations**, over a
separably closed field in which `n` is invertible. -/
theorem mem_fixingSubgroup_fieldRange_mulByIntIsogeny_iff (hchar : (n : F) ≠ 0)
    {σ : W.FunctionField ≃ₐ[F] W.FunctionField} :
    σ ∈ (mulByIntIsogeny W hn).fieldPullback.fieldRange.fixingSubgroup ↔
      ∃ P : (W⁄F).toAffine.Point, n • P = 0 ∧ translation W P = σ := by
  rw [← translationFixedField_ker_mulByIntIsogeny W hchar, fixingSubgroup_translationFixedField,
    mem_translationSubgroup_iff]
  simp only [mem_ker_mulByIntIsogeny_iff]

end TauCeti.Isogeny

end
