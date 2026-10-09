/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Compact

/-!
# Compactness of real orthogonal groups and definiteness

The orthogonal group of a nondegenerate quadratic form on a finite-dimensional real vector space
is compact exactly when the form is positive or negative definite. The topology is the canonical
topology on linear automorphisms, recording each automorphism and its inverse; no topology on the
underlying vector space needs to be chosen. The criterion includes the zero-dimensional space.

The criterion is `QuadraticForm.isCompact_orthogonalGroup_iff_posDef_or_negDef`.
-/

public section

namespace QuadraticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- The orthogonal group of a nondegenerate real quadratic form is compact if and only if the
form is positive or negative definite, with the canonical topology on linear automorphisms. -/
theorem isCompact_orthogonalGroup_iff_posDef_or_negDef (Q : _root_.QuadraticForm ℝ V)
    (hQ : Q.Nondegenerate) :
    IsCompact (TauCeti.QuadraticMap.orthogonalGroup Q : Set (V ≃ₗ[ℝ] V)) ↔
      Q.PosDef ∨ (-Q).PosDef := by
  let _ : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  exact (TauCeti.QuadraticMap.isCompact_orthogonalGroup_iff Q hQ.radical_eq_bot).trans
    (_root_.QuadraticForm.anisotropic_iff_posDef_or_negDef Q)

end QuadraticForm
