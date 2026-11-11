/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ObjectProperty.Syzygy
public import TauCeti.Algebra.Homology.Ext.Presentation
public import Mathlib.CategoryTheory.Abelian.Injective.Dimension

/-!
# `Ext` out of syzygies into objects of finite injective dimension

Let `X` be a `k`-th syzygy relative to a class of projective objects of an abelian category, so
that there is an exact sequence `0 ⟶ X ⟶ Q₁ ⟶ ⋯ ⟶ Q_k` with projective `Qᵢ`
(`CategoryTheory.ObjectProperty.IsSyzygy`). Dimension shifting along the `k` short exact sequences
gives `Ext^{n+1}(X, Y) ≅ Ext^{n+k+1}(X', Y)` for the last cokernel `X'`. So if `Y` has injective
dimension at most `d`, then `Ext^{n+1}(X, Y) = 0` as soon as `n + k ≥ d`; in particular a `d`-th
syzygy has no higher extensions into `Y`.

## Main results

* `CategoryTheory.ObjectProperty.IsSyzygy.ext_eq_zero`: `Ext^{n+1}(X, Y) = 0` for a `k`-th syzygy
  `X` and `Y` of injective dimension at most `d ≤ n + k`.
* `CategoryTheory.ObjectProperty.IsSyzygy.ext_eq_zero_of_hasInjectiveDimensionLE`: a `d`-th
  syzygy has no higher extensions into an object of injective dimension at most `d`.
-/

public section

namespace CategoryTheory.ObjectProperty

open Abelian

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {P : ObjectProperty C}

/-- **`Ext` out of a syzygy**: if `X` is a `k`-th syzygy relative to projective objects and `Y` has
injective dimension at most `d`, then `Ext^{n+1}(X, Y) = 0` whenever `d ≤ n + k`. -/
theorem IsSyzygy.ext_eq_zero (hP : ∀ Q, P Q → Projective Q) {k : ℕ} {X : C}
    (hX : P.IsSyzygy k X) {Y : C} {d : ℕ} [HasInjectiveDimensionLE Y d] {n : ℕ}
    (hn : d ≤ n + k) (e : Ext.{w} X Y (n + 1)) : e = 0 := by
  induction k generalizing X n with
  | zero => exact e.eq_zero_of_hasInjectiveDimensionLT (d + 1) (by lia)
  | succ k ih =>
    obtain ⟨S, hS, ⟨i⟩, hQ, hX'⟩ := (P.isSyzygy_succ_iff k X).1 hX
    have := hP _ hQ
    exact TauCeti.ext_eq_zero_of_iso i
      (hS.ext_X₁_eq_zero_of_ext_X₃_eq_zero fun e' ↦ ih hX' (n := n + 1) (by lia) e') e

/-- **A `d`-th syzygy has no higher extensions into an object of injective dimension at most
`d`.** -/
theorem IsSyzygy.ext_eq_zero_of_hasInjectiveDimensionLE (hP : ∀ Q, P Q → Projective Q) {d : ℕ}
    {X : C} (hX : P.IsSyzygy d X) (Y : C) [HasInjectiveDimensionLE Y d] (n : ℕ)
    (e : Ext.{w} X Y (n + 1)) : e = 0 :=
  hX.ext_eq_zero hP (n := n) (Nat.le_add_left d n) e

end CategoryTheory.ObjectProperty
