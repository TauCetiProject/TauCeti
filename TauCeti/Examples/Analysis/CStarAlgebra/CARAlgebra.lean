/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CARAlgebra
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# The CAR algebra as a C⋆-inductive limit

The CAR algebra `TauCeti.CARAlgebra` is the C⋆-inductive limit of the matrix algebras `M_{2^n}`
along the unital embeddings `a ↦ a ⊗ 1₂`. These examples check with the C⋆-inductive limit API of
`TauCeti.Analysis.CStarAlgebra.InductiveLimit` that it is a nonzero unital C⋆-algebra, that it is
separable, that the canonical maps of the stages are unital isometric ⋆-homomorphisms, and that it
is simple because its stages are.
-/

public section

noncomputable section

open scoped ComplexOrder

namespace TauCeti.CARAlgebra

/-- The CAR algebra is a unital C⋆-algebra. -/
example : CStarAlgebra CARAlgebra := inferInstance

/-- The CAR algebra is nonzero. -/
example : Nontrivial CARAlgebra := inferInstance

/-- The CAR algebra is separable, as a limit of a countable system of finite-dimensional
algebras. -/
example : TopologicalSpace.SeparableSpace CARAlgebra := inferInstance

/-- The canonical maps `M_{2^n} → CARAlgebra` are isometric. -/
example (n : ℕ) : Isometry (CStarInductiveLimit.of Stage (StarAlgHom.natLERec step) n) :=
  isometry_of n

/-- The canonical maps `M_{2^n} → CARAlgebra` are unital. -/
example (n : ℕ) : CStarInductiveLimit.of Stage (StarAlgHom.natLERec step) n 1 = 1 :=
  CStarInductiveLimit.of_one n

/-- Each stage `M_{2^n}` is a simple ring. -/
example (n : ℕ) : IsSimpleRing (Stage n) := inferInstance

/-- The CAR algebra is simple: a closed two-sided ideal is `⊥` or `⊤`. -/
example (J : TwoSidedIdeal CARAlgebra) (hJ : IsClosed (J : Set CARAlgebra)) : J = ⊥ ∨ J = ⊤ :=
  forall_isClosed_eq_bot_or_eq_top J hJ

end TauCeti.CARAlgebra
