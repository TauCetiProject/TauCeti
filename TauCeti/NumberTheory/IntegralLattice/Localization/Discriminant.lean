/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Group
public import TauCeti.NumberTheory.IntegralLattice.Localization.Dual
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TauCeti.NumberTheory.Padics.TensorPrimaryComponent

/-!
# The discriminant group of a localized lattice

Let `L` be a nondegenerate integral lattice with discriminant group `A_L = Lᵛ / L`, and let `p` be
a prime. The localization `L_p = ℤ_p ⊗[ℤ] L` has dual `ℤ_p ⊗[ℤ] Lᵛ` with respect to the completed
rational form (`TauCeti.IntegralLattice.range_localizationDualToCompletion`), so its discriminant
group is the quotient

```text
A_{L_p} = (ℤ_p ⊗[ℤ] Lᵛ) / L_p.
```

This file identifies it with the `p`-primary component of `A_L`: the class of `x ∈ Lᵛ` goes to the
class of `1 ⊗ x`. Localization is right exact, so `A_{L_p}` is the scalar extension
`ℤ_p ⊗[ℤ] A_L`, and scalar extension to `ℤ_p` keeps exactly the `p`-primary component of a finite
abelian group (`TauCeti.AddCommGroup.primaryComponentEquivPadicIntTensor`).

This is the first step in reading the `p`-primary part of the discriminant form of `L` off a
Jordan splitting of `L_p`.

## Main declarations

* `TauCeti.IntegralLattice.LocalDiscriminantGroup`: the quotient `(ℤ_p ⊗[ℤ] Lᵛ) / L_p` by the
  localized inclusion `TauCeti.IntegralLattice.localCarrierToDual`.
* `TauCeti.IntegralLattice.primaryComponentEquivLocalDiscriminantGroup`: the `p`-primary
  component of `A_L` is additively equivalent to the discriminant group of `L_p`.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Chapter 1.
* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter VIII.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- The discriminant group `(ℤ_p ⊗[ℤ] Lᵛ) / L_p` of the localization of `L` at `p`. For
nondegenerate `L` the localized dual carrier is the dual of `L_p` for the completed rational form
(`TauCeti.IntegralLattice.range_localizationDualToCompletion`). -/
abbrev LocalDiscriminantGroup : Type u :=
  L.LocalDualCarrier p ⧸ LinearMap.range (L.localCarrierToDual p)

/-- The range of the localized inclusion is the scalar extension of the copy of `L` inside its
dual carrier. -/
private theorem range_lTensor_carrierInDual_subtype :
    LinearMap.range (AlgebraTensorModule.lTensor ℤ_[p] ℤ_[p]
        (L.carrierInDual.subtype.restrictScalars ℤ)) =
      LinearMap.range (L.localCarrierToDual p) := by
  have h : L.localCarrierToDual p =
      AlgebraTensorModule.lTensor ℤ_[p] ℤ_[p] (L.carrierInDual.subtype.restrictScalars ℤ) ∘ₗ
        (((Submodule.submoduleOfEquivOfLe L.le_dualCarrier).symm.trans
          (LinearEquiv.ofEq _ _ L.carrierInDual_eq_submoduleOf.symm)).baseChange ℤ ℤ_[p] _ _ :
          L.LocalCarrier p ≃ₗ[ℤ_[p]] ℤ_[p] ⊗[ℤ] L.carrierInDual).toLinearMap := by
    ext x
    simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
      localCarrierToDual_tmul, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.baseChange_tmul, AlgebraTensorModule.lTensor_tmul]
    -- Mathlib has no `submoduleOfEquivOfLe_symm_apply` lemma: the inverse is the identity on
    -- ambient vectors by definition.
    rfl
  rw [h, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

variable [L.IsNondegenerate]

/-- **The `p`-primary discriminant group is the discriminant group of the localization.** For a
nondegenerate integral lattice `L` and a prime `p`, the class of `x ∈ Lᵛ` in the `p`-primary
component of `A_L = Lᵛ / L` goes to the class of `1 ⊗ x` in `(ℤ_p ⊗[ℤ] Lᵛ) / L_p`, and this is an
additive equivalence. -/
noncomputable def primaryComponentEquivLocalDiscriminantGroup :
    AddCommGroup.primaryComponent L.DiscriminantGroup p ≃+ L.LocalDiscriminantGroup p :=
  (TauCeti.AddCommGroup.primaryComponentEquivPadicIntTensor p L.DiscriminantGroup
      (AddMonoid.ExponentExists.of_finite)).trans <|
    (AlgebraTensorModule.tensorQuotientEquiv ℤ_[p] ℤ ℤ_[p] L.carrierInDual).toAddEquiv.trans
      (Submodule.quotEquivOfEq _ _ (L.range_lTensor_carrierInDual_subtype p)).toAddEquiv

/-- The discriminant group of the localization of a nondegenerate lattice is finite. -/
instance : Finite (L.LocalDiscriminantGroup p) :=
  Finite.of_equiv _ (L.primaryComponentEquivLocalDiscriminantGroup p).toEquiv

/-- The comparison sends the class of `x ∈ Lᵛ` to the class of `1 ⊗ x`. -/
@[simp]
theorem primaryComponentEquivLocalDiscriminantGroup_apply_mk (x : L.dualCarrier)
    (hx : (Submodule.Quotient.mk x : L.DiscriminantGroup) ∈
      AddCommGroup.primaryComponent L.DiscriminantGroup p) :
    L.primaryComponentEquivLocalDiscriminantGroup p ⟨Submodule.Quotient.mk x, hx⟩ =
      Submodule.Quotient.mk ((1 : ℤ_[p]) ⊗ₜ x) := by
  simp only [primaryComponentEquivLocalDiscriminantGroup, AddEquiv.trans_apply,
    TauCeti.AddCommGroup.primaryComponentEquivPadicIntTensor_apply, LinearEquiv.coe_toAddEquiv]
  -- `ℤ_p ⊗[ℤ] A_L` carries the `ℤ`-module structure of the additive group `A_L` here, and the
  -- quotient-module structure in `tensorQuotientEquiv`; the two agree only up to unfolding, so
  -- its evaluation lemma is applied by unification rather than by rewriting.
  exact (congrArg _ (AlgebraTensorModule.tensorQuotientEquiv_apply_tmul ℤ_[p] ℤ ℤ_[p]
    L.carrierInDual 1 x)).trans
      (Submodule.quotEquivOfEq_mk _ _ (L.range_lTensor_carrierInDual_subtype p) _)

end TauCeti.IntegralLattice
