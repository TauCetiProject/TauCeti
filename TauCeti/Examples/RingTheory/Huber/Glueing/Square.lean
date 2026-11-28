/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.PUnit
public import TauCeti.RingTheory.Huber.Glueing.Square
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks and non-examples for `GlueingSquare`

* Positive examples: `GlueingSquare.id ℚ_[p]` and `GlueingSquare.of_subsingleton_right`.
* Diagonal failure: `ℚ_[p], ℚ_[p] → ℚ_[p] × ℚ_[p]` fails `surjective_sub`.
* Failure of `exact_sub`: discrete `ℤ → ℤ[X], ℤ[X] → ℤ[X]` satisfies density, surjectivity, and
  prime contraction, yet fails `exact_sub` at `(X, X)`.
* Flat module recovery: `GlueingSquare.equivSectionsOfModule` on `ℚ_[p] × ℚ_[p]`.
-/

public section

open Polynomial

namespace TauCeti.Huber.GlueingSquareChecks

/-- Identity glueing square on `ℚ_[p]`. -/
example (p : ℕ) [Fact p.Prime] : GlueingSquare ℚ_[p] ℚ_[p] ℚ_[p] ℚ_[p] := GlueingSquare.id ℚ_[p]

section Padic
variable (p : ℕ) [Fact p.Prime]

/-- Degenerate check: replacing the right-hand branch by `PUnit` yields a glueing square. -/
example : GlueingSquare ℚ_[p] ℚ_[p] PUnit PUnit := GlueingSquare.of_subsingleton_right

/-- Non-example (diagonal failure): `R₁ = R₂ = ℚ_[p]` mapping diagonally to `ℚ_[p] × ℚ_[p]`. -/
example : ¬ GlueingSquare ℚ_[p] ℚ_[p] ℚ_[p] (ℚ_[p] × ℚ_[p]) := fun h ↦
  let ⟨⟨_, _⟩, hab⟩ := h.surjective_sub (1, 0)
  one_ne_zero ((congrArg Prod.fst hab).symm.trans (congrArg Prod.snd hab))

/-- Flat module recovery on `GlueingSquare.id ℚ_[p]` for `ℚ_[p] × ℚ_[p]`. -/
noncomputable example : (ℚ_[p] × ℚ_[p]) ≃ₗ[ℚ_[p]]
    (GlueingDatum.ofModule ℚ_[p] ℚ_[p] ℚ_[p] ℚ_[p] (ℚ_[p] × ℚ_[p])).sections ℚ_[p] :=
  (GlueingSquare.id ℚ_[p]).equivSectionsOfModule (ℚ_[p] × ℚ_[p])
end Padic

/-- Non-example (failure of `exact_sub`): discrete `ℤ → ℤ[X], ℤ[X] → ℤ[X]`. -/
example : letI : TopologicalSpace ℤ := ⊥; letI : TopologicalSpace ℤ[X] := ⊥
    DenseRange (algebraMap ℤ[X] ℤ[X]) ∧ Function.Surjective (fun q : ℤ[X] × ℤ[X] ↦
      algebraMap ℤ[X] ℤ[X] q.1 - algebraMap ℤ[X] ℤ[X] q.2) ∧
      (∀ m : Ideal ℤ, m.IsMaximal → ∃ q : Ideal (ℤ[X] × ℤ[X]), q.IsPrime ∧
        Ideal.comap (RingHom.prod (algebraMap ℤ ℤ[X]) (algebraMap ℤ ℤ[X])) q = m) ∧
      ¬ GlueingSquare ℤ ℤ[X] ℤ[X] ℤ[X] := by
  let _ : TopologicalSpace ℤ := ⊥; let _ : TopologicalSpace ℤ[X] := ⊥
  refine ⟨Function.surjective_id.denseRange, fun p ↦ ⟨(p, 0), by simp⟩, fun m hm ↦ ?_, fun h ↦ ?_⟩
  · let ev : ℤ[X] × ℤ[X] →+* ℤ := (evalRingHom 0).comp (RingHom.fst ℤ[X] ℤ[X])
    exact ⟨m.comap ev, hm.isPrime.comap ev, by ext a; simp [ev]⟩
  · obtain ⟨a, ha⟩ := (h.exact_sub (X, X)).mp (sub_self _)
    have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff 1) (congrArg Prod.fst ha)
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C] at hcoeff; simp at hcoeff

end TauCeti.Huber.GlueingSquareChecks

end
