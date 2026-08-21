/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.LinearCombination
public import TauCeti.Data.ZMod.FinEquiv

/-!
# Exactly one residue index solves `n ∣ a + i * c`

For a nonzero modulus `n` and integers `a c` with `c` a unit mod `n`, exactly one `i : Fin n`
satisfies

```text
(n : ℤ) ∣ a + i * c
```

namely the index whose natural value is `ZMod.val (-a * c⁻¹)`, where `c⁻¹` is the inverse of the
unit.

All of it is arithmetic in `ZMod n` — no matrix, determinant or group action occurs — so that is
where the file starts. `existsUnique_mul_add_eq_zero` solves `c * z + a = 0` for `z : ZMod n`;
`ZMod.finEquiv` re-indexes it by `Fin n`; and one exchange lemma,
`dvd_add_mul_iff_mul_natCast_add_eq_zero`, carries a single index between the equation and the
divisibility. Every other result here is a corollary of those three, so the cast argument is made
exactly once in the file rather than once per direction per statement.

The uniqueness statement is therefore available in **two forms**. The `ZMod n` one takes its
coefficients in `ZMod n` itself, so a consumer already holding residues needs no integer
preimages; the `ℤ` one is the divisibility displayed above, which is how the downstream Hecke sums
are phrased.

Invertibility of `c` is the only thing the argument uses, so nothing here asks for a prime
modulus. Over a prime `p` the hypothesis is implied by `((c : ℤ) : ZMod p) ≠ 0`, since `ZMod p` is
then a field.

## Main results

* `TauCeti.existsUnique_mul_add_eq_zero`: the underlying algebra — in `ZMod n` a unit coefficient
  makes `c * z + a = 0` uniquely solvable.
* `TauCeti.existsUnique_mul_natCast_add_eq_zero`: the same, indexed by `Fin n` along
  `ZMod.finEquiv`.
* `TauCeti.dvd_add_mul_iff_mul_natCast_add_eq_zero`: the exchange between the two forms, at a
  single index.
* `TauCeti.existsUnique_dvd_add_mul`: existence and uniqueness as a divisibility over `ℤ`, the
  form the downstream Hecke sums are phrased in.
* `TauCeti.dvd_add_mul_iff_eq_of_dvd`: given one such index, an index satisfies the divisibility
  exactly when it equals that one.
* `TauCeti.dvd_add_mul_val_neg_mul_inv`: the explicit witness, of natural value
  `ZMod.val (-a * c⁻¹)`, and `TauCeti.exists_dvd_sub_val_mul`: the same for the `a - j * c`
  phrasing, which is what the `Γ₀(pᵏ)` index computation consumes.

## Provenance

The two halves are AINTLIB's, in
[`LeanModularForms/HeckeRIngs/GL2/HeckeT_p.lean`](https://github.com/CBirkbeck/AINTLIB) at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0, Chris Birkbeck:
`dvd_add_mul_iff_eq_of_dvd` is `dvd_topLeft_add_iff_eq_canonicalIndex` (lines 301-310) and
`dvd_add_mul_val_neg_mul_inv` is `dvd_topLeft_add_canonicalIndex` (lines 263-276).

Both are generalised here. The source states them for a matrix `M` with `M.det = 1`, in the entries
`M 0 0` and `M 1 0`, over a prime modulus; these take arbitrary coefficients `a c : ℤ` over an
arbitrary nonzero modulus, and assume only `IsUnit ((c : ℤ) : ZMod n)`, since invertibility of that
one coefficient is all the argument uses. `b₀` is implicit, and the section supplies the binders the
source passes explicitly.

**Neither proof is the source's, and the direction is reversed.** AINTLIB proves uniqueness by
rewriting through the `if`-split in its own `moebiusFin`, taking the two divisibility statements as
primitive. Here the primitive is the `ZMod n` equation — `existsUnique_mul_add_eq_zero`, where the
unit `c` cancels and no group action appears — and both ported statements are corollaries of it,
reached through `ZMod.finEquiv` and the single exchange lemma. `existsUnique_dvd_add_mul` has no
counterpart in the source, which never states existence and uniqueness together.
-/

public section

namespace TauCeti

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- **The underlying algebra.** In `ZMod n` a unit coefficient makes the linear equation
`c * z + a = 0` uniquely solvable, with solution `-a * c⁻¹`.

Everything else in this file is this fact re-indexed or re-cast; stating it here means the
unit-cancellation argument is made once. -/
lemma existsUnique_mul_add_eq_zero (a c : ZMod n) (hc : IsUnit c) :
    ∃! z : ZMod n, c * z + a = 0 := by
  have hci : c * c⁻¹ = 1 := ZMod.mul_inv_of_unit c hc
  refine ⟨-a * c⁻¹, by linear_combination -a * hci, fun y hy ↦ ?_⟩
  refine sub_eq_zero.mp (hc.mul_right_eq_zero.mp ?_)
  linear_combination hy + a * hci

/-- **Exactly one index solves the equation in `ZMod n`.** The `Fin n`-indexed face of
`existsUnique_mul_add_eq_zero`, transported along `ZMod.finEquiv`.

The coefficients are elements of `ZMod n`, not integers read through `Int.cast`, so a consumer
already holding residues applies this directly. -/
theorem existsUnique_mul_natCast_add_eq_zero (a c : ZMod n) (hc : IsUnit c) :
    ∃! i : Fin n, c * ((i : ℕ) : ZMod n) + a = 0 :=
  ((ZMod.finEquiv n).toEquiv.existsUnique_congr fun i ↦ by
    simp [ZMod.finEquiv_apply]).mpr (existsUnique_mul_add_eq_zero a c hc)

omit [NeZero n] in
/-- **The exchange between the two forms**, at a single index: `n` divides `a + i * c` over `ℤ`
exactly when the corresponding equation holds in `ZMod n`.

This is the only place the `ℤ`/`ZMod n` cast argument is made; the `∃!` statements transport
through it with `existsUnique_congr` rather than repeating it per direction. -/
lemma dvd_add_mul_iff_mul_natCast_add_eq_zero (a c : ℤ) (i : ℕ) :
    (n : ℤ) ∣ (a + i * c) ↔
      ((c : ℤ) : ZMod n) * ((i : ℕ) : ZMod n) + ((a : ℤ) : ZMod n) = 0 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- **Exactly one index solves the divisibility.** When `c` is a unit mod `n` there is a unique
`i : Fin n` with `n ∣ a + i * c`. This is the form a consumer indexing by `Fin n` wants, and the
form the downstream Hecke sums are phrased in. -/
theorem existsUnique_dvd_add_mul (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) :
    ∃! i : Fin n, (n : ℤ) ∣ (a + (i : ℕ) * c) :=
  (existsUnique_congr fun i : Fin n ↦
      dvd_add_mul_iff_mul_natCast_add_eq_zero a c (i : ℕ)).mpr
    (existsUnique_mul_natCast_add_eq_zero ((a : ℤ) : ZMod n) ((c : ℤ) : ZMod n) hc)

/-- **At most one index.** If `b₀` satisfies the divisibility then an index `i` satisfies it
exactly when `i = b₀`.

`existsUnique_dvd_add_mul` is the form to reach for when no solution is already in hand; this is
the form to reach for when one is. -/
lemma dvd_add_mul_iff_eq_of_dvd (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) {b₀ : Fin n}
    (hb₀ : (n : ℤ) ∣ (a + (b₀ : ℕ) * c)) (i : Fin n) :
    (n : ℤ) ∣ (a + (i : ℕ) * c) ↔ i = b₀ := by
  obtain ⟨b, -, hbu⟩ := existsUnique_dvd_add_mul a c hc
  exact ⟨fun hi ↦ (hbu i hi).trans (hbu b₀ hb₀).symm, fun hji ↦ hji ▸ hb₀⟩

/-- **The explicit witness.** The unique index of `existsUnique_dvd_add_mul` has natural value
`ZMod.val (-a * c⁻¹)`, the canonical representative of the residue solving the equation. -/
lemma dvd_add_mul_val_neg_mul_inv (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) :
    (n : ℤ) ∣ (a +
      (((-((a : ℤ) : ZMod n) * ((c : ℤ) : ZMod n)⁻¹).val : ℕ)) * c) := by
  have hci : ((c : ℤ) : ZMod n) * ((c : ℤ) : ZMod n)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hc
  rw [dvd_add_mul_iff_mul_natCast_add_eq_zero, ZMod.natCast_val, ZMod.cast_id]
  linear_combination -((a : ℤ) : ZMod n) * hci

/-- **The subtraction form of the explicit witness.** Some consumers phrase the divisibility as
`a - j * c` rather than `a + j * c`; this is `dvd_add_mul_val_neg_mul_inv` at `-c`, so the sign
flip is made here once rather than at each such site. The witness is stated as an existential
because those consumers only need *a* residue, not the canonical one. -/
lemma exists_dvd_sub_val_mul (a c : ℤ) (hc : IsUnit ((c : ℤ) : ZMod n)) :
    ∃ j : ZMod n, (n : ℤ) ∣ a - (j.val : ℤ) * c :=
  ⟨_, by
    have h := dvd_add_mul_val_neg_mul_inv (n := n) a (-c) (by simpa using hc.neg)
    simpa [sub_eq_add_neg, mul_neg] using h⟩

end TauCeti

end
