/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Projection

/-!
# A surjective linear map restricted to a complement of its kernel

A surjective linear map `f : M →ₗ[R] M₂` restricts to a linear equivalence `S ≃ₗ[R] M₂` on any
complement `S` of its kernel. This is the composite of Mathlib's
`Submodule.quotientEquivOfIsCompl`, identifying `M ⧸ ker f` with `S`, and
`LinearMap.quotKerEquivOfSurjective`, identifying `M ⧸ ker f` with `M₂`. Its inverse is the lift
of `M₂` into `S`: for the orthogonal complement of the kernel of a submersion's differential this
is the horizontal lift.

## Main definitions

* `LinearMap.equivOfIsComplKer`: the restriction of a surjective linear map to a complement of its
  kernel, as a linear equivalence onto the codomain.

## Main results

* `LinearMap.equivOfIsComplKer_apply`: the equivalence is `f` on `S`.
* `LinearMap.apply_equivOfIsComplKer_symm_apply`: its inverse is a right inverse of `f`.
* `LinearMap.equivOfIsComplKer_symm_apply_of_mem`: its inverse lifts `f x` back to `x` for
  `x ∈ S`.
-/

public section

namespace LinearMap

variable {R M M₂ : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R M₂]
variable (f : M →ₗ[R] M₂) (hf : Function.Surjective f) {S : Submodule R M}
variable (h : IsCompl (ker f) S)

/-- The restriction of a surjective linear map `f` to a complement `S` of its kernel, as a linear
equivalence `S ≃ₗ[R] M₂`. Its forward map is `f ∘ₗ S.subtype`. -/
noncomputable def equivOfIsComplKer : S ≃ₗ[R] M₂ :=
  (Submodule.quotientEquivOfIsCompl (ker f) S h).symm.trans (f.quotKerEquivOfSurjective hf)

/-- The restriction of `f` to a complement of its kernel is `f` on that complement. -/
@[simp]
theorem equivOfIsComplKer_apply (x : S) : equivOfIsComplKer f hf h x = f x := by
  simp [equivOfIsComplKer]

/-- The restriction of `f` to a complement of its kernel has forward map `f ∘ₗ S.subtype`. -/
theorem coe_equivOfIsComplKer :
    (equivOfIsComplKer f hf h : S →ₗ[R] M₂) = f ∘ₗ S.subtype :=
  LinearMap.ext (equivOfIsComplKer_apply f hf h)

/-- The inverse of the restriction of `f` to a complement of its kernel is a right inverse of `f`.
-/
@[simp]
theorem apply_equivOfIsComplKer_symm_apply (y : M₂) :
    f ((equivOfIsComplKer f hf h).symm y) = y := by
  rw [← equivOfIsComplKer_apply f hf h, LinearEquiv.apply_symm_apply]

/-- The inverse of the restriction of `f` to a complement `S` of its kernel lifts `f x` back to `x`
for `x ∈ S`. -/
theorem equivOfIsComplKer_symm_apply_of_mem {x : M} (hx : x ∈ S) :
    ((equivOfIsComplKer f hf h).symm (f x) : M) = x := by
  have := (equivOfIsComplKer f hf h).symm_apply_apply ⟨x, hx⟩
  rw [equivOfIsComplKer_apply] at this
  exact congrArg Subtype.val this

end LinearMap
