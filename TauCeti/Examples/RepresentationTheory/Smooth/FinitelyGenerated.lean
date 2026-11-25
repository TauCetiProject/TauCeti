/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.FinitelyGenerated
import Mathlib.LinearAlgebra.Dimension.Finite
import TauCeti.RepresentationTheory.OfMulAction.Coset.Lift

/-!
# Examples of finitely generated smooth representations

The permutation representation `A[G ⧸ U]` on the cosets of any subgroup is finitely generated,
for instance `ℚ[ℚ_[p] ⧸ ℤ_[p]]`, which is smooth but not admissible, and so are finite direct sums
of these. The trivial rank-one
representation is finitely generated, being the quotient of `A[G ⧸ G]`, while the trivial
representation of the trivial group on `ℚ^(ℕ)` is not.
-/

public section

open Representation
open scoped MonoidAlgebra

namespace TauCeti

variable {A G : Type*} [CommSemiring A] [Group G]

/-- A permutation representation on cosets, such as `ℚ[ℚ_[p] ⧸ ℤ_[p]]`, is finitely generated. -/
example (U : Subgroup G) : Module.Finite A[G] (ofMulAction A G (G ⧸ U)).asModule :=
  inferInstance

/-- A finite direct sum `⊕_{i < n} A[G ⧸ U_i]` is finitely generated, by instance search. -/
example {n : ℕ} (U : Fin n → Subgroup G) :
    Module.Finite A[G] (directSum fun i ↦ ofMulAction A G (G ⧸ U i)).asModule :=
  inferInstance

/-- The trivial rank-one representation is finitely generated: it is the quotient of
`A[G ⧸ G]` by `g G ↦ 1`. -/
example : Module.Finite A[G] (trivial A G A).asModule := by
  refine finite_asModule_of_surjective
    ((trivial A G A).cosetLift ⊤ 1 fun g _ ↦ mem_stabilizer.2 rfl) fun c ↦ ?_
  refine ⟨MonoidAlgebra.single ((1 : G) : G ⧸ (⊤ : Subgroup G)) c, ?_⟩
  rw [cosetLift_single]
  simp

/-- The trivial representation of the trivial group on `ℚ^(ℕ)` is not finitely generated. -/
example : ¬Module.Finite ℚ[Unit] (trivial ℚ Unit (ℕ →₀ ℚ)).asModule := by
  intro h
  have : Module.Finite ℚ (trivial ℚ Unit (ℕ →₀ ℚ)).asModule := Module.Finite.trans ℚ[Unit] _
  have h' : Module.Finite ℚ (ℕ →₀ ℚ) :=
    Module.Finite.equiv (trivial ℚ Unit (ℕ →₀ ℚ)).asModuleEquiv
  rcases Module.finite_finsupp_self_iff.1 h' with h | h
  · exact not_subsingleton ℚ h
  · exact not_finite ℕ

end TauCeti
