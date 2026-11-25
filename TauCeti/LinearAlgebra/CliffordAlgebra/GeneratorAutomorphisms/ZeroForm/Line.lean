/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
public import TauCeti.Algebra.DualNumber.Automorphism
public import TauCeti.LinearAlgebra.CliffordAlgebra.GeneratorAutomorphisms.ZeroForm.Basic

/-!
# Vector-preserving automorphisms for the zero form on a line

On the line `M = R` the Clifford algebra of the zero form is the dual numbers `R[ε]`
(`CliffordAlgebraDualNumber.equiv`). Over every commutative ring, read on the dual numbers, the
vector-preserving automorphism attached to the multiplication by a unit `u`
(`TauCeti.ExteriorAlgebra.linearEquivEquivVectorStabilizer`) is `ε ↦ u • ε`
(`autCongr_cliffordAlgebraDualNumberEquiv_linearEquivEquivVectorStabilizer`, in the namespace
`TauCeti.CliffordAlgebra`).

If `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or `2`
is invertible in `R`, then every automorphism of `R[ε]` is `ε ↦ u • ε` for a unit `u`
(`TauCeti.DualNumber.linearEquivEquivAlgEquiv`). So every automorphism preserves the vectors
(`TauCeti.CliffordAlgebra.vectorStabilizer_zero_line_eq_top`).

## Main results

* `TauCeti.CliffordAlgebra.vectorStabilizer_zero_line_eq_top`: on a line, if `R` has no nonzero
  `a` with `a ^ 2 = 0` and `2 * a = 0`, every automorphism of the Clifford algebra of the zero form
  preserves the vectors.
* `TauCeti.CliffordAlgebra.autCongr_cliffordAlgebraDualNumberEquiv_linearEquivEquivVectorStabilizer`
  says that, read on the dual numbers, the automorphism attached to a linear automorphism `e` of
  `R` is `e.trivSqZeroExtCongr`.
-/

public section

universe u

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra

variable {R : Type u} [CommRing R]

/-- **The correspondence on the dual numbers.** Read on the dual numbers through
`CliffordAlgebraDualNumber.equiv`, the vector-preserving automorphism attached to a linear
automorphism `e` of `R` is `e.trivSqZeroExtCongr`; for the multiplication by a unit
`u` this is `ε ↦ u • ε`. This holds over every commutative ring. If moreover `R` has no nonzero
`a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or `2` is invertible in `R`,
then together with `TauCeti.CliffordAlgebra.vectorStabilizer_zero_line_eq_top` this identifies the
isometry group `GL₁(R)` of the zero form with all automorphisms of `R[ε]`, by `u ↦ u`. -/
theorem autCongr_cliffordAlgebraDualNumberEquiv_linearEquivEquivVectorStabilizer
    (e : R ≃ₗ[R] R) :
    CliffordAlgebraDualNumber.equiv.autCongr
        (ExteriorAlgebra.linearEquivEquivVectorStabilizer R R e :
          CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R] CliffordAlgebra (0 : QuadraticForm R R)) =
      e.trivSqZeroExtCongr :=
  AlgEquiv.coe_toAlgHom_injective <| _root_.DualNumber.algHom_ext <| by simp

/-- The simp normal form of
`TauCeti.CliffordAlgebra.autCongr_cliffordAlgebraDualNumberEquiv_linearEquivEquivVectorStabilizer`,
with `AlgEquiv.autCongr` expanded into compositions. -/
@[simp]
theorem cliffordAlgebraDualNumberEquiv_symm_trans_linearEquivEquivVectorStabilizer_trans
    (e : R ≃ₗ[R] R) :
    CliffordAlgebraDualNumber.equiv.symm.trans
        ((ExteriorAlgebra.linearEquivEquivVectorStabilizer R R e :
            CliffordAlgebra (0 : QuadraticForm R R) ≃ₐ[R]
              CliffordAlgebra (0 : QuadraticForm R R)).trans
          CliffordAlgebraDualNumber.equiv) =
      e.trivSqZeroExtCongr := by
  simpa only [AlgEquiv.autCongr_apply] using
    autCongr_cliffordAlgebraDualNumberEquiv_linearEquivEquivVectorStabilizer e

/-- **The zero form on a line.** If `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for
instance if `R` is reduced or `2` is invertible in `R`, then every algebra automorphism of the
Clifford algebra of the zero form on `R`, which is the dual numbers `R[ε]`, maps the vectors
`R • ε` onto themselves: such an automorphism is `ε ↦ u • ε` for a unit `u`
(`TauCeti.DualNumber.linearEquivEquivAlgEquiv`). -/
theorem vectorStabilizer_zero_line_eq_top (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0) :
    vectorStabilizer (0 : QuadraticForm R R) = ⊤ := by
  refine eq_top_iff.mpr fun φ _ ↦ ?_
  obtain ⟨e, he⟩ :=
    (CliffordAlgebraDualNumber.equiv.autCongr φ).exists_trivSqZeroExtCongr_eq_iff.mpr
      (DualNumber.fst_algEquiv_apply_eps_eq_zero hR _)
  -- `φ` is the automorphism attached to `e`, since both read as `e.trivSqZeroExtCongr` on the dual
  -- numbers.
  rw [← CliffordAlgebraDualNumber.equiv.autCongr.injective
    ((autCongr_cliffordAlgebraDualNumberEquiv_linearEquivEquivVectorStabilizer e).trans he)]
  exact (ExteriorAlgebra.linearEquivEquivVectorStabilizer R R e).property

end TauCeti.CliffordAlgebra
