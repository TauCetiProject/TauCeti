/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Finsupp.Basic

/-!
# Roadmap: JacobianChallenge
Target: Relative cohomology and symmetric powers.
<!--tauceti-target:v1
  {"focus":"JacobianChallenge",
   "id":"JacobianChallenge.Relative_cohomology_and_symmetric_powers"}-->
-/

public section

open scoped BigOperators

namespace JacobianChallenge

/-- An algebraic curve over a ground field `k`, with closed points and residue degrees
representing `[κ(x) : k] ≥ 1`. -/
structure Curve (k : Type*) [Field k] where
  /-- The closed points of the curve. -/
  Point : Type
  /-- Residue degree `[κ(x) : k]` of each point. -/
  deg : Point → ℕ+

/-- The `d`-th symmetric power of a curve `C` over a field `k`, modeled as the moduli of
effective zero-cycles (relative effective Cartier divisors) of degree `d`: formal sums
`∑ n_p [p]` with `n_p ≥ 0` and total degree `∑ n_p [κ(p) : k] = d`. -/
abbrev SymmetricPower {k : Type*} [Field k] (C : Curve k) (d : ℕ) : Type :=
  { D : C.Point →₀ ℕ // D.sum (fun p n => n * (C.deg p : ℕ)) = d }

/-- The unique configuration of degree zero (the empty cycle). -/
def symZero {k : Type*} [Field k] (C : Curve k) : SymmetricPower C 0 :=
  ⟨0, by simp⟩

/-- Monoidal addition map on symmetric powers: summing effective cycles adds degrees. -/
noncomputable def symAdd {k : Type*} [Field k] {C : Curve k} {d₁ d₂ : ℕ}
    (D₁ : SymmetricPower C d₁) (D₂ : SymmetricPower C d₂) : SymmetricPower C (d₁ + d₂) :=
  ⟨D₁.1 + D₂.1, by
    have h : (D₁.1 + D₂.1).sum (fun p n => n * (C.deg p : ℕ)) =
        D₁.1.sum (fun p n => n * (C.deg p : ℕ)) + D₂.1.sum (fun p n => n * (C.deg p : ℕ)) :=
      Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_mul _ _ _)
    rw [h, D₁.2, D₂.2]⟩

/-- Identity law: adding the zero cycle yields the original cycle. -/
theorem symAdd_zero {k : Type*} [Field k] {C : Curve k} {d : ℕ}
    (D : SymmetricPower C d) :
    (symAdd D (symZero C)).1 = D.1 := by
  change D.1 + 0 = D.1
  rw [add_zero]

/-- Associativity of addition on symmetric powers of a curve. -/
theorem symAdd_assoc {k : Type*} [Field k] {C : Curve k} {d₁ d₂ d₃ : ℕ}
    (D₁ : SymmetricPower C d₁) (D₂ : SymmetricPower C d₂) (D₃ : SymmetricPower C d₃) :
    (symAdd D₁ (symAdd D₂ D₃)).1 = (symAdd (symAdd D₁ D₂) D₃).1 := by
  change D₁.1 + (D₂.1 + D₃.1) = (D₁.1 + D₂.1) + D₃.1
  rw [add_assoc]

end JacobianChallenge
