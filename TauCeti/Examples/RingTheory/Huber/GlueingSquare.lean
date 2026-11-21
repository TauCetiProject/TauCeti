/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.PUnit
public import TauCeti.RingTheory.Huber.Glueing.Square
public import TauCeti.RingTheory.Huber.Padic.Field

/-!
# Checks and non-examples for `GlueingSquare` and `GlueingDatum`

* Positive examples: the identity square `GlueingSquare.id ℚ_[p]` and right-subsingleton squares
  `GlueingSquare.of_subsingleton_right`.
* Non-example (diagonal failure): `ℚ_[p], ℚ_[p] → ℚ_[p] × ℚ_[p]` fails `surjective_sub`, hence is
  not a `GlueingSquare`.
* Non-example (independence of `exact_sub`): over discrete `ℤ` and `ℤ[X]`, the square with
  `R = ℤ` and `R₁ = R₂ = R₁₂ = ℤ[X]` satisfies `denseRange`, `surjective_sub`, and
  `exists_prime_comap_eq`, yet is not a `GlueingSquare` because `(X, X)` maps to `0` without coming
  from `ℤ`.
* Module glueing checks: explicit section membership and non-membership on `ℚ × ℚ`, and flat
  module recovery `GlueingSquare.equivSectionsOfModule` on `ℚ_[p] × ℚ_[p]`.
-/

public section

open TensorProduct Polynomial

namespace TauCeti.Huber.GlueingSquareChecks

/-- Identity glueing square on `ℚ_[p]`. -/
example (p : ℕ) [Fact p.Prime] : GlueingSquare ℚ_[p] ℚ_[p] ℚ_[p] ℚ_[p] :=
  GlueingSquare.id ℚ_[p]

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- **Degenerate check**: replacing the right-hand branch by `PUnit` yields a glueing square. -/
example : GlueingSquare ℚ_[p] ℚ_[p] PUnit PUnit :=
  GlueingSquare.of_subsingleton_right

/-- **Non-example (diagonal failure)**: `R₁ = R₂ = ℚ_[p]` mapping diagonally to `ℚ_[p] × ℚ_[p]`
is not a glueing square, since `surjective_sub` fails outside the diagonal. -/
example : ¬ GlueingSquare ℚ_[p] ℚ_[p] ℚ_[p] (ℚ_[p] × ℚ_[p]) := by
  intro h
  obtain ⟨⟨a, b⟩, hab⟩ := h.surjective_sub (1, 0)
  exact one_ne_zero ((congrArg Prod.fst hab).symm.trans (congrArg Prod.snd hab))

/-- **Flat module recovery**: on `GlueingSquare.id ℚ_[p]`, the rank-`2` vector space `ℚ_[p] × ℚ_[p]`
is canonically isomorphic to the sections of its induced glueing datum. -/
noncomputable example :
    (ℚ_[p] × ℚ_[p]) ≃ₗ[ℚ_[p]]
      (GlueingDatum.ofModule ℚ_[p] ℚ_[p] ℚ_[p] ℚ_[p] (ℚ_[p] × ℚ_[p])).sections ℚ_[p] :=
  (GlueingSquare.id ℚ_[p]).equivSectionsOfModule (ℚ_[p] × ℚ_[p])

end Padic

/-- **Independence of `exact_sub`**: with `R = ℤ` and `R₁ = R₂ = R₁₂ = ℤ[X]` (equipped with the
discrete topology), `denseRange`, `surjective_sub`, and `exists_prime_comap_eq` all hold, yet
`GlueingSquare` fails because `(X, X)` lies in the kernel of subtraction without coming from `ℤ`. -/
example :
    letI : TopologicalSpace ℤ := ⊥
    letI : TopologicalSpace ℤ[X] := ⊥
    DenseRange (algebraMap ℤ[X] ℤ[X]) ∧
      Function.Surjective (fun q : ℤ[X] × ℤ[X] ↦
        algebraMap ℤ[X] ℤ[X] q.1 - algebraMap ℤ[X] ℤ[X] q.2) ∧
      (∀ m : Ideal ℤ, m.IsMaximal →
        ∃ q : Ideal (ℤ[X] × ℤ[X]), q.IsPrime ∧
          Ideal.comap (RingHom.prod (algebraMap ℤ ℤ[X]) (algebraMap ℤ ℤ[X])) q = m) ∧
      ¬ GlueingSquare ℤ ℤ[X] ℤ[X] ℤ[X] := by
  let _ : TopologicalSpace ℤ := ⊥
  let _ : TopologicalSpace ℤ[X] := ⊥
  refine ⟨Function.surjective_id.denseRange, fun p ↦ ⟨(p, 0), by simp⟩, fun m hm ↦ ?_, fun h ↦ ?_⟩
  · have := hm.isPrime
    let ev : ℤ[X] × ℤ[X] →+* ℤ := (evalRingHom 0).comp (RingHom.fst ℤ[X] ℤ[X])
    exact ⟨m.comap ev, Ideal.IsPrime.comap ev, by ext a; simp [ev]⟩
  · obtain ⟨a, ha⟩ := (h.exact_sub (X, X)).mp (sub_self _)
    have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff 1) (congrArg Prod.fst ha)
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C] at hcoeff; simp at hcoeff

/-- **Positive section check**: `((1, 2), (1, 2))` satisfies the cocycle condition for the trivial
glueing datum of `ℚ × ℚ` over `ℚ`. -/
example :
    (((1 : ℚ) ⊗ₜ[ℚ] ((1 : ℚ), (2 : ℚ)), (1 : ℚ) ⊗ₜ[ℚ] ((1 : ℚ), (2 : ℚ))) :
      (ℚ ⊗[ℚ] (ℚ × ℚ)) × (ℚ ⊗[ℚ] (ℚ × ℚ))) ∈
      (GlueingDatum.ofModule ℚ ℚ ℚ ℚ (ℚ × ℚ)).sections ℚ := by
  simp

/-- **Sign / cocycle check**: `((1, 2), (2, 1))` does *not* lie in the sections of the glueing datum
of `ℚ × ℚ` over `ℚ`. -/
example :
    (((1 : ℚ) ⊗ₜ[ℚ] ((1 : ℚ), (2 : ℚ)), (1 : ℚ) ⊗ₜ[ℚ] ((2 : ℚ), (1 : ℚ))) :
      (ℚ ⊗[ℚ] (ℚ × ℚ)) × (ℚ ⊗[ℚ] (ℚ × ℚ))) ∉
      (GlueingDatum.ofModule ℚ ℚ ℚ ℚ (ℚ × ℚ)).sections ℚ := by
  intro hmem
  simp only [GlueingDatum.mem_sections_iff, GlueingDatum.ofModule_ψ₁_tmul,
    GlueingDatum.ofModule_ψ₂_tmul, one_smul] at hmem
  simpa using congrArg (TensorProduct.lid ℚ (ℚ × ℚ)) hmem

end TauCeti.Huber.GlueingSquareChecks

end
