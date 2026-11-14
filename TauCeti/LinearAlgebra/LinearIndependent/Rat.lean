/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.Localization.Module

/-!
# Linear independence over `ℚ` and integer relations

In a (nonassociative) ring `A` that is a `ℚ`-module, a finite family `α` is linearly independent
over `ℚ` exactly when it satisfies no nontrivial integer relation `∑ i, xᵢ αᵢ = 0` with
`x : ι → ℤ`.
In particular the family `1, α₁, …, αₙ` is linearly independent over `ℚ` exactly when
`x₀ + ∑ i, xᵢ αᵢ = 0` with integers `xᵢ` forces `x = 0`. This is the form of the hypothesis
of Kronecker's approximation theorem (`TauCeti.kronecker_approximation`).

## Main results

* `TauCeti.linearIndependent_rat_iff`: a finite family is `ℚ`-linearly independent if and only
  if it has no nontrivial integer relation.
* `TauCeti.linearIndependent_rat_option_one_iff`: the family `1, α` indexed by `Option ι`.
* `TauCeti.linearIndependent_rat_finCons_one_iff`: the family `Fin.cons 1 α` indexed by
  `Fin (n + 1)`.
-/

public section

namespace TauCeti

variable {A : Type*} [NonAssocRing A] [Module ℚ A]

/-- A finite family in a `ℚ`-module ring is linearly independent over `ℚ` if and only if it
satisfies no nontrivial integer relation. -/
theorem linearIndependent_rat_iff {ι : Type*} [Fintype ι] (α : ι → A) :
    LinearIndependent ℚ α ↔ ∀ x : ι → ℤ, ∑ i, (x i : A) * α i = 0 → x = 0 := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ, Fintype.linearIndependent_iff]
  simp [zsmul_eq_mul, funext_iff]

/-- The family `1, α` indexed by `Option ι` is linearly independent over `ℚ` if and only if
`1` and the `α i` satisfy no nontrivial integer relation. -/
theorem linearIndependent_rat_option_one_iff {ι : Type*} [Fintype ι] (α : ι → A) :
    LinearIndependent ℚ (Option.elim' (1 : A) α) ↔
      ∀ x : ℤ × (ι → ℤ), (x.1 : A) + ∑ i, (x.2 i : A) * α i = 0 → x = 0 := by
  rw [linearIndependent_rat_iff]
  constructor
  · intro h x hx
    have := h (Option.elim' x.1 x.2) (by simpa [Fintype.sum_option] using hx)
    exact Prod.ext (by simpa using congrFun this none)
      (funext fun i ↦ by simpa using congrFun this (some i))
  · intro h g hg
    have := h (g none, fun i ↦ g (some i)) (by simpa [Fintype.sum_option] using hg)
    funext i
    cases i with
    | none => simpa using congrArg Prod.fst this
    | some j => simpa using congrFun (congrArg Prod.snd this) j

/-- `1, α₁, …, αₙ` are linearly independent over `ℚ` if and only if they satisfy no nontrivial
integer relation. -/
theorem linearIndependent_rat_finCons_one_iff {n : ℕ} (α : Fin n → A) :
    LinearIndependent ℚ (Fin.cons (1 : A) α : Fin (n + 1) → A) ↔
      ∀ x : ℤ × (Fin n → ℤ), (x.1 : A) + ∑ i, (x.2 i : A) * α i = 0 → x = 0 := by
  rw [← linearIndependent_rat_option_one_iff,
    ← linearIndependent_equiv (finSuccEquiv n).symm]
  congr! 1
  ext i
  cases i <;> rfl

end TauCeti
