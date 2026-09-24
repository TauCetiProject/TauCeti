/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Int.Interval
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
import TauCeti.Algebra.QuadraticDiscriminant

/-!
# Reduced binary quadratic forms

An integral binary quadratic form `a x² + b x y + c y²` is **reduced** when `|b| ≤ a ≤ c`, and
`0 ≤ b` whenever `|b| = a` or `a = c` (Cohen, Definition 5.3.2). Every positive-definite form is
`SL₂(ℤ)`-equivalent to exactly one reduced form, the boundary conditions being what removes the
double count on the edges of the fundamental domain. This file defines the predicate and, for
`D ≠ 0`, the finite set of reduced forms of discriminant `-D`: a reduced form of discriminant
`-D < 0` has `|b| ≤ a ≤ √(D / 3)` and `c ≤ D / 3`, so the set is a filter of an explicit box and is
decidable. Weighted, it counts the Hurwitz class number `TauCeti.hurwitzClassNumber`.

## Main definitions

* `TauCeti.IsReducedForm f`: the form `f = a x² + b x y + c y²` is reduced.
* `TauCeti.reducedForms D`: for `D ≠ 0`, the finite set of reduced forms of discriminant `-D`.

## Main results

* `TauCeti.mem_reducedForms`: for `D ≠ 0`, `f ∈ reducedForms D` exactly when `f.discrim = -D` and
  `f` is reduced, so the box the definition searches is no restriction.
* `TauCeti.reducedForms_eq_empty_of_mod_four_eq_one_or_two`: there are no reduced forms of
  discriminant `-D` when `D ≡ 1, 2 (mod 4)`, since a discriminant `b² - 4 a c` is `0` or `1`
  modulo `4` (`Int.discrim_emod_four`).

## Implementation notes

The definitions are exposed, so that the kernel can evaluate `reducedForms D`, as `decide` does for
the values of `TauCeti.hurwitzClassNumber`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, GTM 138, §5.3.
-/

@[expose] public section

open Finset

namespace TauCeti

/-- The integral binary quadratic form `f = a x² + b x y + c y²` is **reduced**: `|b| ≤ a ≤ c`,
and `0 ≤ b` whenever `|b| = a` or `a = c` (Cohen, Definition 5.3.2).

For a positive-definite form this picks exactly one representative of each `SL₂(ℤ)`-class: the
inequalities place the root `τ = (-b + i √(4 a c - b²)) / (2 a)` of `a τ² + b τ + c` in
`ModularGroup.fd`, and the sign condition chooses one of each pair of boundary points that `SL₂(ℤ)`
identifies. Definiteness is not part of the predicate (`IsReducedForm ⟨0, 0, 1⟩` holds), but a
reduced form with `f.discrim < 0` has `0 < f.a` (`pos_of_nonneg_of_discrim_lt_zero`). -/
def IsReducedForm (f : BinaryQuadraticForm ℤ) : Prop :=
  |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ (|f.b| = f.a ∨ f.a = f.c → 0 ≤ f.b)
deriving Decidable

/-- The form `f = a x² + b x y + c y²` is reduced exactly when `|b| ≤ a ≤ c`, and `0 ≤ b` whenever
`|b| = a` or `a = c`. -/
theorem isReducedForm_iff {f : BinaryQuadraticForm ℤ} :
    IsReducedForm f ↔ |f.b| ≤ f.a ∧ f.a ≤ f.c ∧ (|f.b| = f.a ∨ f.a = f.c → 0 ≤ f.b) :=
  Iff.rfl

/-- The reduced forms `a x² + b x y + c y²` of discriminant `b² - 4 a c = -D`.

The definition searches the box `1 ≤ a ≤ √(D / 3)`, `|b| ≤ √(D / 3)`, `1 ≤ c ≤ D / 3` (with
`Nat.sqrt`), which makes it a finite, decidable set; `mem_reducedForms` shows that for `D ≠ 0` this
box loses nothing. For `D = 0` the box is empty, so `reducedForms 0 = ∅`, although every `c y²`
with `0 ≤ c` is a reduced form of discriminant `0`. -/
def reducedForms (D : ℕ) : Finset (BinaryQuadraticForm ℤ) :=
  {f ∈ (Icc 1 ((D / 3).sqrt : ℤ) ×ˢ Icc (-(D / 3).sqrt : ℤ) (D / 3).sqrt ×ˢ Icc 1 (D / 3 : ℤ)).map
    BinaryQuadraticForm.equivProd.symm.toEmbedding | f.discrim = -D ∧ IsReducedForm f}

/-- **The reduced forms of discriminant `-D`**: for `D ≠ 0`, `f ∈ reducedForms D` exactly when
`f.discrim = -D` and `f` is reduced, so the box that `reducedForms` searches loses nothing. -/
@[simp] theorem mem_reducedForms {D : ℕ} (hD : D ≠ 0) {f : BinaryQuadraticForm ℤ} :
    f ∈ reducedForms D ↔ f.discrim = -D ∧ IsReducedForm f := by
  refine mem_filter.trans <| and_iff_right_of_imp fun h ↦ mem_map_equiv.2 ?_
  obtain ⟨a, b, c⟩ := f
  simp only [BinaryQuadraticForm.discrim_def, isReducedForm_iff, abs_le, Equiv.symm_symm,
    BinaryQuadraticForm.equivProd_apply, mem_product, mem_Icc] at h ⊢
  obtain ⟨hd, ⟨hb₁, hb₂⟩, hac, -⟩ := h
  have ha := pos_of_nonneg_of_discrim_lt_zero (by lia) (hd.trans_lt <| by lia)
  rw [discrim] at hd
  -- `3 a² ≤ 3 a c ≤ 4 a c - b² = D`, as `b² ≤ a² ≤ a c`; so `|b| ≤ a ≤ √(D / 3)` and `c ≤ D / 3`
  have hbb := sq_le_sq' hb₁ hb₂
  have hac' := mul_le_mul_of_nonneg_left hac ha.le
  have hc := le_mul_of_one_le_left (ha.le.trans hac) ha
  lift a to ℕ using ha.le
  have hn : a ≤ (D / 3).sqrt := Nat.le_sqrt.2 <| by lia
  lia

/-- The search box of `reducedForms 0` is empty. -/
@[simp] theorem reducedForms_zero : reducedForms 0 = ∅ := rfl

/-- There are no reduced forms of discriminant `-D` when `D ≡ 1, 2 (mod 4)`: a discriminant
`b² - 4 a c` is `0` or `1` modulo `4` (`Int.discrim_emod_four`). -/
@[simp]
theorem reducedForms_eq_empty_of_mod_four_eq_one_or_two {D : ℕ} (hD : D % 4 = 1 ∨ D % 4 = 2) :
    reducedForms D = ∅ :=
  filter_eq_empty_iff.mpr fun f _ ⟨h, _⟩ ↦ by
    have := f.discrim_def ▸ Int.discrim_emod_four f.a f.b f.c
    lia

end TauCeti
