/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Generators under an invertible change of basis

The columns of an invertible two-by-two matrix transform a two-element module basis into
another basis. In particular, the first transformed generator is nonzero and the two
transformed generators span the module. A special-linear change is obtained by applying
`Module.Basis.fin_two_basis_generators` to its image in the general linear group.
-/

public section

namespace Module.Basis

/-- An invertible change of a two-element basis has nonzero first generator and
still generates every element over the coefficient ring. -/
theorem fin_two_basis_generators
    {R M : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 2) R M) (γ : Matrix.GeneralLinearGroup (Fin 2) R) :
    (γ 0 0 • b 0 + γ 1 0 • b 1) ≠ 0 ∧
      ∀ z : M, ∃ m n : R,
        m • (γ 0 0 • b 0 + γ 1 0 • b 1) +
          n • (γ 0 1 • b 0 + γ 1 1 • b 1) = z := by
  let e := (Matrix.GeneralLinearGroup.toLin' b γ).toLinearEquiv
  let c := b.map e
  have hc (i : Fin 2) : c i = γ 0 i • b 0 + γ 1 i • b 1 := by
    simp [c, e, Matrix.GeneralLinearGroup.toLin'_apply, Finsupp.single_eq_pi_single,
      Fintype.linearCombination_apply, Fin.sum_univ_two]
  constructor
  · simpa only [hc] using c.ne_zero 0
  · intro z
    refine ⟨c.repr z 0, c.repr z 1, ?_⟩
    simpa only [Fin.sum_univ_two, hc] using c.sum_repr z

end Module.Basis
