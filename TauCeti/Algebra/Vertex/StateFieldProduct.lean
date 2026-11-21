/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.Axioms
public import TauCeti.Algebra.Vertex.Dong

/-!
# State–field correspondence for integer products

Let `A : FormalVertexAxioms R V` be a formal vertex algebra over a commutative ring `R`. While the
axioms of `FormalVertexAxioms` are division-free, recovering the negative modes of a field on the
vacuum from powers of the translation operator `T` via `k! • a₍₋ₖ₋₁₎|0⟩ = Tᵏ a` requires cancelling
`k!`, i.e. unique divisibility `[HasUniqueDiv V]` (satisfied in particular by every `ℚ`-module).

Under `[HasUniqueDiv V]`, Dong's lemma (`VertexOperator.IsLocalOfOrder.nthProduct_left`) and
Goddard uniqueness (`FormalVertexAxioms.eq_field_of_lie_translation_ncoeff`) identify the
state–field map on every integer mode product `(a₍ₙ₎ b)` (`n : ℤ`) with the `n`-th field product
`VertexOperator.nthProduct n (A.field a) (A.field b)`.

## Main results

* `TauCeti.FormalVertexAxioms.field_ncoeff_apply`: state–field correspondence
  `Y(a₍ₙ₎ b, z) = Y(a, z)₍ₙ₎ Y(b, z)` for all `n : ℤ` under `[HasUniqueDiv V]`, together with the
  specializations `field_ncoeff_neg_one_apply`, `field_ncoeff_natCast_apply`,
  `field_ncoeff_zero_apply`, and `field_ncoeff_neg_succ_apply`.

## References

* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §4.5 (Theorem 4.5, state–field correspondence
  for `n`-th products).
* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), 143–195, Proposition 3.2.7.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §3.2.
-/

public section

noncomputable section

open scoped VertexOperator
open VertexOperator

namespace TauCeti

namespace FormalVertexAxioms

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable (A : FormalVertexAxioms R V)

/-- **State–field correspondence for integer products.** When `V` has unique divisibility
(in particular over any `ℚ`-module), the field of every `n`-th product `a₍ₙ₎ b` (`n : ℤ`) is the
`n`-th field product `nthProduct n (Y(a, z)) (Y(b, z))`. -/
theorem field_ncoeff_apply [HasUniqueDiv V] (a b : V) (n : ℤ) :
    A.field (((A.field a)[[n]]) b) = nthProduct n (A.field a) (A.field b) := by
  symm
  refine A.eq_field_of_lie_translation_ncoeff (fun c ↦ ?_)
    (lie_ncoeff_nthProduct (A.lie_translation_ncoeff a) (A.lie_translation_ncoeff b) n)
    ((ncoeff_neg_one_nthProduct_apply (A.ncoeff_field_apply_vacuum_of_nonneg a)
      (A.ncoeff_field_apply_vacuum_of_nonneg b) n).trans (by simp))
  obtain ⟨r₀, h₀⟩ := A.exists_isLocalOfOrder a b
  obtain ⟨r₁, h₁⟩ := A.exists_isLocalOfOrder a c
  obtain ⟨r₂, h₂⟩ := A.exists_isLocalOfOrder b c
  exact ⟨_, h₀.nthProduct_left h₁ h₂ n⟩

/-- The field of the `(-1)`-st product `a₍₋₁₎ b` is the normal-ordered product `:Y(a,z) Y(b,z):`. -/
theorem field_ncoeff_neg_one_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[-1]]) b) = normalOrder (A.field a) (A.field b) := by
  simp [A.field_ncoeff_apply]

/-- For `n : ℕ`, the field of `a₍ₙ₎ b` is `nonnegResidueProduct n (Y(a,z)) (Y(b,z))`. -/
theorem field_ncoeff_natCast_apply [HasUniqueDiv V] (a b : V) (n : ℕ) :
    A.field (((A.field a)[[(n : ℤ)]]) b) = nonnegResidueProduct n (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_natCast]

/-- The field of the `0`-th product `a₍₀₎ b` is `nonnegResidueProduct 0 (Y(a,z)) (Y(b,z))`. -/
theorem field_ncoeff_zero_apply [HasUniqueDiv V] (a b : V) :
    A.field (((A.field a)[[0]]) b) = nonnegResidueProduct 0 (A.field a) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_zero]

/-- For `k : ℕ`, `Y(a₍₋ₖ₋₁₎ b, z)` is `:(∂_z^{(k)} Y(a, z)) Y(b, z):`. -/
theorem field_ncoeff_neg_succ_apply [HasUniqueDiv V] (a b : V) (k : ℕ) :
    A.field (((A.field a)[[-(k : ℤ) - 1]]) b) =
      normalOrder (hasseDeriv k (A.field a)) (A.field b) := by
  rw [A.field_ncoeff_apply, nthProduct_neg_natCast_sub_one]

end FormalVertexAxioms

end TauCeti
