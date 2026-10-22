/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.Algebra.QuadraticAlgebra.NormTrace
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.Discriminant
import Mathlib.Algebra.CharP.Invertible
import TauCeti.Algebra.Squarefree

/-!
# The discriminant of the standard quadratic-algebra basis

The algebra discriminant of the basis `1, ω` is `b² + 4a`, where `ω² = a + bω`.
This identifies Mathlib's explicit quadratic discriminant with the discriminant computed
from the trace pairing. Over `ℤ`, choosing `a` and `b` with `b² + 4a = Δ` gives `Δ` as the
discriminant of the basis `1, ω` of `QuadraticAlgebra ℤ a b`.

Over `ℚ`, Mathlib classifies quadratic algebras by their discriminant modulo unit squares
(`QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two`). Since a squarefree integer is the
unique such representative of its class (`Rat.eq_of_squarefree_of_intCast_mul_sq_eq`),
`QuadraticAlgebra.nonempty_algEquiv_iff_of_squarefree` shows that `ℚ(√d) ≃ₐ[ℚ] ℚ(√e)` exactly when
`d = e`, for squarefree integers `d` and `e`.
-/

public section

namespace QuadraticAlgebra

/-- The discriminant of the standard basis `1, ω` is the explicit quadratic discriminant. -/
@[simp] theorem algebraDiscr_basis {R : Type*} [CommRing R] (a b : R) :
    Algebra.discr R (basis a b) = discr a b := by
  simp [Algebra.discr_def, Matrix.det_fin_two, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, basis_apply_zero, basis_apply_one, trace_def, discr_def]
  ring

/-- **Squarefree radicands classify rational quadratic algebras.** For squarefree integers `d` and
`e`, the rational quadratic algebras `ℚ(√d)` and `ℚ(√e)` are isomorphic exactly when `d = e`. In
general two such algebras are isomorphic exactly when the radicands have the same class in
`ℚ× / (ℚ×)²` (`QuadraticAlgebra.nonempty_algEquiv_iff_of_invertible_two`), and a squarefree integer
is the unique such representative of its class. -/
theorem nonempty_algEquiv_iff_of_squarefree {d e : ℤ} (hd : Squarefree d) (he : Squarefree e) :
    Nonempty (QuadraticAlgebra ℚ (d : ℚ) 0 ≃ₐ[ℚ] QuadraticAlgebra ℚ (e : ℚ) 0) ↔ d = e := by
  refine ⟨fun h => ?_, fun h => h ▸ ⟨AlgEquiv.refl⟩⟩
  obtain ⟨u, hu⟩ := nonempty_algEquiv_iff_of_invertible_two.mp h
  rw [discr_def, discr_def] at hu
  exact Rat.eq_of_squarefree_of_intCast_mul_sq_eq (c := 1) (c' := u) hd he one_ne_zero
    (by linear_combination hu / 4)

end QuadraticAlgebra
