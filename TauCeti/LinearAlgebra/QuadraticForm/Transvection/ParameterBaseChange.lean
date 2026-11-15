/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Transvection.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange

/-!
# Scalar extension of Eichler-transvection parameters

The pure-tensor map sends vectors orthogonal to `u` to vectors orthogonal to `1 ⊗ u`, and
sends the span of `u` into the span of `1 ⊗ u`. It therefore induces a semilinear map on the
quotient parameter spaces. For isotropic `u`, these are the spaces `u^⊥ / R ∙ u` that
parametrize Eichler transvections and their canonical Spin lifts. The map lets entire root
subgroups, rather than just individual elements, be transported by extension of scalars.

The maps are `TauCeti.QuadraticMap.polarKernelBaseChange` and
`TauCeti.QuadraticMap.transvectionParameterBaseChange`, alongside the orthogonal-group
base-change maps. Use function application, for example
`TauCeti.QuadraticMap.transvectionParameterBaseChange (A := A) Q u`.
-/

public section

open scoped TensorProduct

namespace TauCeti.QuadraticMap

open _root_.QuadraticMap

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Invertible (2 : R)]

/-- Scalar extension on the quotient parameter space of Eichler transvections. The class of
`w` is sent to the class of `1 ⊗ w`; the map is semilinear along `algebraMap R A`. -/
def transvectionParameterBaseChange (Q : QuadraticForm R M) (u : M) :
    -- Fix Mathlib's additive structure before synthesizing the nested quotient.
    letI : AddCommGroup (A ⊗[R] M) := TensorProduct.addCommGroup
    (LinearMap.ker (Q.polarBilin u) ⧸
        (R ∙ u).comap (LinearMap.ker (Q.polarBilin u)).subtype) →ₛₗ[algebraMap R A]
      (LinearMap.ker ((Q.baseChange A).polarBilin (1 ⊗ₜ[R] u)) ⧸
        (A ∙ (1 ⊗ₜ[R] u)).comap
          (LinearMap.ker ((Q.baseChange A).polarBilin (1 ⊗ₜ[R] u))).subtype) := by
  letI : AddCommGroup (A ⊗[R] M) := TensorProduct.addCommGroup
  exact Submodule.mapQ _ _ (polarKernelBaseChange Q u) fun w hw => by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hw
    have hr' : r • u = (w : M) := hr
    refine Submodule.mem_span_singleton.mpr ⟨algebraMap R A r, ?_⟩
    rw [Submodule.coe_subtype, coe_polarKernelBaseChange_apply]
    rw [← hr']
    simp [TensorProduct.tmul_smul]

/-- Extension of a quotient parameter is computed on representatives by pure tensors. -/
@[simp]
theorem transvectionParameterBaseChange_mk (Q : QuadraticForm R M) (u : M)
    (w : LinearMap.ker (Q.polarBilin u)) :
    letI : AddCommGroup (A ⊗[R] M) := TensorProduct.addCommGroup
    transvectionParameterBaseChange (A := A) Q u (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨1 ⊗ₜ[R] (w : M), by
        rw [LinearMap.mem_ker, polarBilin_apply_apply, QuadraticForm.polar_baseChange_tmul]
        have hw : polar Q u w = 0 := LinearMap.mem_ker.mp w.2
        simp [hw]⟩ := by
  let : AddCommGroup (A ⊗[R] M) := TensorProduct.addCommGroup
  rw [transvectionParameterBaseChange, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  exact coe_polarKernelBaseChange_apply Q u w

end TauCeti.QuadraticMap
