/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Linear maps after extension of scalars

Extending scalars along an algebra `A` turns a linear map `f` into `f.baseChange A`.  If the
coefficient algebra is faithfully flat, this operation loses no information: two linear maps that
agree after extension of scalars are equal, and an endomorphism is nilpotent exactly when its
extension of scalars is.

This builds on `LinearMap.baseChange` and `Module.End.baseChangeHom` from
`Mathlib/LinearAlgebra/TensorProduct/Tower.lean` and on
`Module.FaithfullyFlat.one_tmul_eq_zero_iff` from
`Mathlib/RingTheory/Flat/FaithfullyFlat/Basic.lean`.

## Main results

* `LinearMap.baseChange_injective`: over a faithfully flat coefficient algebra, two linear maps
  agreeing after extension of scalars are equal.
* `LinearMap.isNilpotent_baseChange_iff`: over a faithfully flat coefficient algebra, an
  endomorphism is nilpotent exactly when its extension of scalars is.
-/

public section

open TensorProduct

namespace LinearMap

universe u v w x

variable {R : Type u} {A : Type v} {M : Type w} {N : Type x}
variable [CommRing R] [Ring A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [Module.FaithfullyFlat R A]

/-- Over a faithfully flat coefficient algebra, extension of scalars loses no information about a
linear map: two maps agreeing after extension of scalars are equal.

Mathlib's `LinearMap.baseChangeHom_injective` proves injectivity under the incomparable hypotheses
that `A` is merely faithful over `R` and that the *target* module `N` is flat over `R`; faithful
flatness of the coefficient algebra asks nothing of `N`. -/
theorem baseChange_injective :
    Function.Injective (baseChange A : (M →ₗ[R] N) → A ⊗[R] M →ₗ[A] A ⊗[R] N) := by
  intro f g h
  ext x
  have hx : (1 : A) ⊗ₜ[R] (f x - g x) = 0 := by
    rw [TensorProduct.tmul_sub, ← baseChange_tmul (A := A) f, ← baseChange_tmul (A := A) g, h,
      sub_self]
  rw [← sub_eq_zero]
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff R _ (f x - g x)).mp hx

/-- **An endomorphism is nilpotent exactly when its extension of scalars is**, over a faithfully
flat coefficient algebra. -/
theorem isNilpotent_baseChange_iff (f : Module.End R M) :
    IsNilpotent (f.baseChange A) ↔ IsNilpotent f :=
  IsNilpotent.map_iff (f := Module.End.baseChangeHom R A M) baseChange_injective

end LinearMap
