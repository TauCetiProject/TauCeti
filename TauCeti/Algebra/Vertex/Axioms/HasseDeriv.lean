/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.HasseDeriv

/-!
# Hasse derivatives of fields in formal vertex algebras

In a formal vertex algebra `A : FormalVertexAxioms R V`, the divided-power creation identity relates
Hasse derivatives of the state–field map to powers of the translation operator and negative modes on
the vacuum:

* `TauCeti.FormalVertexAxioms.factorial_smul_hasseDeriv_field`:
  `k! • ∂_z^{(k)} Y(a, z) = Y(Tᵏ a, z)` over any commutative ring `R`.
* `TauCeti.FormalVertexAxioms.field_ncoeff_neg_succ_apply_vacuum`:
  `Y(a₍₋ₖ₋₁₎|0⟩, z) = ∂_z^{(k)} Y(a, z)` under unique divisibility `[HasUniqueDiv V]`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.5.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- Without division, `k!` times the `k`-th Hasse derivative of `Y(a, z)` is `Y(Tᵏ a, z)`. -/
theorem factorial_smul_hasseDeriv_field (a : V) (k : ℕ) :
    k.factorial • hasseDeriv k (A.field a) = A.field ((A.translation ^ k) a) := by
  rw [← iterate_derivative_eq_factorial_smul_hasseDeriv, A.field_pow_translation]

/-- The field of `a₍₋ₖ₋₁₎|0⟩` is the `k`-th Hasse derivative of `Y(a, z)`. -/
@[simp]
theorem field_ncoeff_neg_succ_apply_vacuum [HasUniqueDiv V] (a : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) A.vacuum) = hasseDeriv k (A.field a) := by
  have h := A.eq_field_of_lie_translation
    (fun c ↦ let ⟨N, hN⟩ := A.exists_isLocalOfOrder a c; ⟨N + k, hN.hasseDeriv_left k⟩)
    (lie_ncoeff_hasseDeriv (A.lie_translation_ncoeff a) k)
  rw [ncoeff_neg_one_hasseDeriv] at h
  exact h.symm

end FormalVertexAxioms

end TauCeti
