/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# Integral lattices in a quadratic space

An integral lattice for a quadratic form `Q` is a full lattice on which `Q` takes values
in the image of the base ring. When the base ring embeds into the ambient scalars, these values
define a quadratic form on the carrier. Its polar pairing extends to the polar pairing of `Q`,
including when two is a nonunit. The values of the integral form determine `Q` uniquely.

## References

* John Voight, *Quaternion algebras*, §§9.3, 9.7.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable (R : Type*) {K V : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/-- A full `R`-lattice in the ambient quadratic space on which the form takes integral values. -/
@[ext]
structure IntegralQuadraticLattice (Q : QuadraticForm K V) where
  ofCarrier ::
  /-- The underlying submodule of the ambient space. -/
  carrier : Submodule R V
  /-- The submodule is a full lattice for the ambient scalars. -/
  [isFullLattice : carrier.IsFullLattice K]
  /-- The ambient form takes values in the image of the base ring on the carrier. -/
  integral : ∀ x ∈ carrier, Q x ∈ Set.range (algebraMap R K)

attribute [instance] IntegralQuadraticLattice.isFullLattice

namespace IntegralQuadraticLattice

variable {R} {Q : QuadraticForm K V}

/-- The lattice built on a given carrier has that carrier as its underlying submodule. -/
@[simp]
theorem carrier_ofCarrier (M : Submodule R V) [M.IsFullLattice K]
    (h : ∀ x ∈ M, Q x ∈ Set.range (algebraMap R K)) :
    (ofCarrier M h).carrier = M := rfl

variable [FaithfulSMul R K] (L : IntegralQuadraticLattice R Q)

/-- The base-ring-valued quadratic form induced on the lattice. -/
noncomputable def integralForm : QuadraticForm R L.carrier :=
  let i := Algebra.linearMap R K
  let e := LinearEquiv.ofInjective i (FaithfulSMul.algebraMap_injective R K)
  e.symm.toLinearMap.compQuadraticMap <|
    ((Q.restrictScalars (S := R)).restrict L.carrier).codRestrict (LinearMap.range i)
      (fun x ↦ L.integral x x.property)

/-- The integral quadratic form takes the original value after extending coefficients. -/
@[simp]
theorem algebraMap_integralForm (x : L.carrier) :
    algebraMap R K (L.integralForm x) = Q x := by
  rw [integralForm, LinearMap.compQuadraticMap_apply, LinearEquiv.coe_coe]
  refine (LinearEquiv.ofInjective_symm_apply (Algebra.linearMap R K) _).trans ?_
  refine (QuadraticMap.coe_codRestrict_apply _ _ _ x).trans ?_
  rw [QuadraticMap.restrict_apply, QuadraticMap.restrictScalars_apply]

/-- The polar pairing on the carrier takes the ambient polar value after extending coefficients. -/
@[simp]
theorem algebraMap_polar_integralForm (x y : L.carrier) :
    algebraMap R K (QuadraticMap.polar L.integralForm x y) =
      QuadraticMap.polar Q (x : V) (y : V) := by
  simp [QuadraticMap.polar]

/-- The generic quadratic form is the unique extension of the integral form to the ambient space. -/
theorem eq_iff_forall_eq_integralForm (Q' : QuadraticForm K V) :
    Q' = Q ↔ ∀ x : L.carrier, Q' x = algebraMap R K (L.integralForm x) := by
  simp only [algebraMap_integralForm]
  exact ⟨fun h x ↦ DFunLike.congr_fun h (x : V),
    QuadraticMap.ext_of_span_range_eq_top L.carrier.subtype
      (by rw [Submodule.range_subtype, Submodule.IsFullLattice.span_eq_top])⟩

section FractionField

open scoped nonZeroDivisors

variable {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  [Module F V] [IsScalarTower R F V] {q : QuadraticForm F V} (N : IntegralQuadraticLattice R q)

/-- The generic space is the scalar extension of the lattice to the fraction field. -/
theorem isBaseChange_subtype : IsBaseChange F N.carrier.subtype :=
  have := N.carrier.isLocalizedModule_subtype_of_span_eq_top (R⁰ : Submonoid R)
    (Submodule.IsFullLattice.span_eq_top (A := F))
  IsLocalizedModule.isBaseChange R⁰ F N.carrier.subtype

/-- The pullback of the generic form to the scalar extension is characterized by the values
of the integral form on pure tensors with first factor one. -/
theorem eq_comp_isBaseChange_subtype_iff (q' : QuadraticForm F (F ⊗[R] N.carrier)) :
    q' = q.comp N.isBaseChange_subtype.equiv.toLinearMap ↔
      ∀ x : N.carrier, q' (1 ⊗ₜ[R] x) = algebraMap R F (N.integralForm x) := by
  have h (x : N.carrier) :
      (q.comp N.isBaseChange_subtype.equiv.toLinearMap) (1 ⊗ₜ[R] x) =
        algebraMap R F (N.integralForm x) := by
    simp [IsBaseChange.equiv_tmul]
  exact ⟨fun heq x ↦ heq ▸ h x, fun heq ↦ baseChange_ext fun x ↦ (heq x).trans (h x).symm⟩

end FractionField

end IntegralQuadraticLattice

end TauCeti
