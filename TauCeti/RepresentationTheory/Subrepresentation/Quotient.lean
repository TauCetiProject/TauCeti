/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The quotient by a subrepresentation with a complement

Mathlib's `Subrepresentation.quotient` is the representation a subrepresentation `ρ₁` of `ρ`
induces on the quotient `W ⧸ ρ₁`. When `ρ₁` has a complementary subrepresentation `ρ₂`, that
quotient is the representation `ρ₂` carries: `Subrepresentation.quotientEquivOfIsCompl` is this
equivalence of representations. Its linear part is `Submodule.quotientEquivOfIsCompl`, and it is
equivariant because its inverse, the restriction of the quotient map to `ρ₂`, is.

This is the representation-level form of the statement that a subrepresentation with a complement
is a direct summand whose cokernel is the complement. It identifies a top graded piece
`F_0 / F_1` of a filtration of a representation with a complement of `F_1`, as for the harmonic
tensors inside the tensor powers of the orthogonal and symplectic standard representations. It sits
beside `Subrepresentation.equivProdOfIsCompl`, the splitting `ρ ≃ ρ₁ × ρ₂` along the same
complement.

## Main definitions

* `Subrepresentation.quotientEquivOfIsCompl`: the quotient by a subrepresentation is equivalent to
  any complementary subrepresentation.
-/

public section

namespace Subrepresentation

variable {A G W : Type*} [Ring A] [Monoid G] [AddCommGroup W] [Module A W]
  {ρ : Representation A G W}

/-- **The quotient by a subrepresentation is equivalent to any complement of it.** If `ρ₁` and
`ρ₂` are complementary subrepresentations of `ρ`, the representation `ρ₁.quotient` on `W ⧸ ρ₁` is
equivalent to the representation `ρ₂` carries. The linear isomorphism is
`Submodule.quotientEquivOfIsCompl`, whose inverse is the quotient map restricted to `ρ₂`. -/
noncomputable def quotientEquivOfIsCompl {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂) :
    ρ₁.quotient.Equiv ρ₂.toRepresentation :=
  (Representation.Equiv.mk
    (Submodule.quotientEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule
      (isCompl_toSubmodule.mpr h)).symm
    fun _ => LinearMap.ext fun _ => rfl).symm

/-- The equivalence is the linear isomorphism `Submodule.quotientEquivOfIsCompl` of the carriers:
it sends the class of a vector to its component along `ρ₂`. -/
@[simp]
theorem quotientEquivOfIsCompl_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂)
    (x : W ⧸ ρ₁.toSubmodule) :
    quotientEquivOfIsCompl h x =
      Submodule.quotientEquivOfIsCompl ρ₁.toSubmodule ρ₂.toSubmodule
        (isCompl_toSubmodule.mpr h) x :=
  -- `(rfl)`, not `rfl`: the body of `quotientEquivOfIsCompl` is not `@[expose]`d, so this must not
  -- be inferred `@[defeq]`.
  (rfl)

/-- The inverse of the equivalence sends a vector of `ρ₂` to its class in the quotient. -/
@[simp]
theorem quotientEquivOfIsCompl_symm_apply {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂)
    (v : ρ₂.toSubmodule) :
    (quotientEquivOfIsCompl h).symm v = Submodule.Quotient.mk (v : W) :=
  -- `(rfl)`, not `rfl`: the body of `quotientEquivOfIsCompl` is not `@[expose]`d, so this must not
  -- be inferred `@[defeq]`.
  (rfl)

/-- The class of a vector of `ρ₂` goes back to that vector. -/
theorem quotientEquivOfIsCompl_apply_mk_right {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂)
    (v : ρ₂.toSubmodule) :
    quotientEquivOfIsCompl h (Submodule.Quotient.mk (v : W)) = v := by
  rw [← quotientEquivOfIsCompl_symm_apply h, Representation.Equiv.apply_symm_apply]

/-- A vector differs from the component along `ρ₂` of its class by a vector of `ρ₁`. -/
theorem sub_quotientEquivOfIsCompl_apply_mk_mem {ρ₁ ρ₂ : Subrepresentation ρ} (h : IsCompl ρ₁ ρ₂)
    (x : W) :
    x - (quotientEquivOfIsCompl h (Submodule.Quotient.mk x) : W) ∈ ρ₁ := by
  rw [← mem_toSubmodule, ← Submodule.Quotient.eq, ← quotientEquivOfIsCompl_symm_apply h,
    Representation.Equiv.symm_apply_apply]

end Subrepresentation
