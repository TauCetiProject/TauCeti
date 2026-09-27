/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Base change of Eichler transvections

An Eichler transvection is defined by a polynomial formula in the quadratic form and its polar
form. Extending scalars therefore carries the transvection determined by `u` and `w` to the one
determined by their pure tensors. The corresponding statement for `SO(Q)` follows from this
identity and the existing base-change homomorphism of special orthogonal groups. These formulas
let the same transvection be used over a rational quadratic space and at each of its completions.
-/

public section

open TauCeti

namespace QuadraticMap

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  (Q : QuadraticForm R M) {u w : M}

/-- Base change carries `E_{u,w}` to `E_{1 ⊗ u,1 ⊗ w}` over commutative rings in which `2` is
invertible; neither nondegeneracy nor finite dimensionality is needed. -/
@[simp]
theorem transvection_baseChange (hu : Q u = 0) (huw : polar Q u w = 0) :
    LinearEquiv.baseChange R A M M (transvection Q hu huw) =
      transvection (Q.baseChange A) (u := 1 ⊗ₜ[R] u) (w := 1 ⊗ₜ[R] w)
        (by simp [QuadraticForm.baseChange_tmul, hu])
        (by simp [QuadraticForm.polar_baseChange_tmul, huw]) := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      rw [LinearEquiv.baseChange_tmul, transvection_apply, transvection_apply,
        QuadraticForm.polar_baseChange_tmul, QuadraticForm.baseChange_tmul]
      simp [TensorProduct.tmul_add, TensorProduct.tmul_sub, TensorProduct.smul_tmul',
        Algebra.smul_def, mul_assoc]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The special-orthogonal base-change homomorphism carries the class of an Eichler
transvection to the class of the base-changed transvection. -/
@[simp]
theorem specialOrthogonalGroupBaseChange_transvection [Module.Free R M] [Module.Finite R M]
    (hu : Q u = 0)
    (huw : polar Q u w = 0) :
    TauCeti.QuadraticMap.specialOrthogonalGroupBaseChange (A := A) Q
        ⟨transvection Q hu huw, transvection_mem_specialOrthogonalGroup hu huw⟩ =
      ⟨transvection (Q.baseChange A) (u := 1 ⊗ₜ[R] u) (w := 1 ⊗ₜ[R] w)
        (by simp [QuadraticForm.baseChange_tmul, hu])
        (by simp [QuadraticForm.polar_baseChange_tmul, huw]),
        transvection_mem_specialOrthogonalGroup
          (by simp [QuadraticForm.baseChange_tmul, hu])
          (by simp [QuadraticForm.polar_baseChange_tmul, huw])⟩ := by
  apply Subtype.ext
  rw [TauCeti.QuadraticMap.coe_specialOrthogonalGroupBaseChange]
  exact transvection_baseChange (A := A) Q hu huw

end QuadraticMap
