/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.LinearAlgebra.Matrix.Alternating.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.SetTheory.Cardinal.Finite

/-!
# Dimension of the orthogonal Lie algebra

The strictly upper-triangular entries give linear coordinates on the skew-symmetric matrices
when doubling has trivial kernel.
-/

public section

namespace TauCeti

open LieAlgebra.Orthogonal

/-- The strictly upper-triangular entries are linear coordinates on skew-symmetric matrices
when doubling has trivial kernel. -/
def soStrictUpperLinearEquiv {n R : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [CommRing R]
    (h₂ : ∀ x : R, x + x = 0 → x = 0) : so n R ≃ₗ[R] ({p : n × n // p.1 < p.2} → R) :=
  let e : so n R ≃ Matrix.skewAddSubgroup n R :=
    Equiv.subtypeEquiv (Equiv.refl _) fun A ↦
      (mem_so n R A).trans (Matrix.mem_skewAddSubgroup A).symm
  { toEquiv := e.trans (Matrix.skewStrictUpperAddEquiv h₂).toEquiv
    map_add' := by intro A B; ext p; simp [e]
    map_smul' := by intro a A; ext p; simp [e] }

/-- The dimension of `so(n)` over a field of characteristic other than two is `n.choose 2`. -/
theorem finrank_so {n R : Type*} [Fintype n] [dec : DecidableEq n] [Field R] [NeZero (2 : R)] :
    Module.finrank R (so n R) = (Fintype.card n).choose 2 := by
  let : LinearOrder n := LinearOrder.lift' (Fintype.equivFin n) (Fintype.equivFin n).injective
  have h₂ (x : R) (hx : x + x = 0) : x = 0 :=
    (mul_eq_zero.1 ((two_mul x).trans hx)).resolve_left (NeZero.ne 2)
  rw [(@soStrictUpperLinearEquiv n R _ dec _ _ h₂).finrank_eq,
    Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, Fintype.natCard_subtype_lt]

end TauCeti
