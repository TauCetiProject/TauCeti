/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.InternalHom.Basic
public import TauCeti.Geometry.Hodge.SelfDuality
public import TauCeti.Geometry.Hodge.TensorProduct.Polarization

/-!
# Polarizability of internal homs

The integral internal hom of two polarizable pure Hodge structures is polarizable.
Its lattice `Hom_ℤ(V, W)` is identified with `V* ⊗ W` by Mathlib's `dualTensorHomEquiv`;
the complexification of this identification respects the Hodge filtrations, by
`TauCeti.Hodge.HodgeStructureOn.internalHom_F_eq_comap`.

A polarizing form on the dual of `V` and a polarizing form on `W` therefore give a polarizing
form on the internal hom: pull their tensor product back along the inverse contraction.
The dual polarization exists without unimodularity of the original integral form, by
`TauCeti.Hodge.IsPolarizable.dual`.

## Main results

* `TauCeti.Hodge.IsPolarization.internalHom`: the pullback of the tensor product of polarizing
  forms on `V*` and `W` polarizes their internal hom.
* `TauCeti.Hodge.IsPolarizable.internalHom`: polarizable pure Hodge structures are closed
  under internal homs.

## References

Deligne, *Théorie de Hodge II*, §2.1; Peters--Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.Hodge

universe u₁ u₂ v₁ v₂

variable {V₁ : Type u₁} {V₂ : Type u₂} {W₁ : Type v₁} {W₂ : Type v₂}
variable [AddCommGroup V₁] [Module.Free ℤ V₁] [Module.Finite ℤ V₁]
variable [AddCommGroup V₂]
variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂}
variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂} {n₁ n₂ : ℤ}
variable {hs₁ : HodgeStructure h₁ n₁} {hs₂ : HodgeStructure h₂ n₂}

/-- Polarizing forms on the dual of the source and on the target induce a polarization of the
integral internal hom, by pulling their tensor product back along the inverse contraction. -/
theorem IsPolarization.internalHom {Q₁ : LinearMap.BilinForm ℤ (Module.Dual ℤ V₁)}
    {Q₂ : LinearMap.BilinForm ℤ V₂}
    (hQ₁ : IsPolarization (isBaseChange_dualLatticeMap h₁) hs₁.dual Q₁)
    (hQ₂ : IsPolarization h₂ hs₂ Q₂) :
    IsPolarization (isBaseChange_homLatticeMap h₁ h₂) (hs₁.internalHom hs₂)
      (LinearMap.BilinForm.comp (Q₁.tmul Q₂)
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap) := by
  let : Module.Finite ℂ W₁ := h₁.finite
  let e := dualTensorHomEquiv ℂ W₁ W₂
  have he : ∀ f, e.symm ((latticeConjugation (isBaseChange_homLatticeMap h₁ h₂)).toEquiv f) =
      (latticeConjugation
        (isBaseChange_tensorLatticeMap (isBaseChange_dualLatticeMap h₁) h₂)).toEquiv
          (e.symm f) := by
    intro f
    rw [latticeConjugation_internalHom h₁ h₂,
      latticeConjugation_tensorProduct (isBaseChange_dualLatticeMap h₁) h₂,
      latticeConjugation_dual h₁]
    exact (latticeConjugation h₁).dualTensorHomEquiv_symm_map_internalHom_conj
      (latticeConjugation h₂) f
  let hs := (hs₁.dual.tensorProduct hs₂).comap e.symm he
  have hF (p : ℤ) : hs.F p = (hs₁.internalHom hs₂).F p := by
    rw [HodgeStructureOn.comap_F, HodgeStructure.tensorProduct_F,
      HodgeStructure.internalHom_F, HodgeStructureOn.internalHom_F_eq_comap]
    simp only [e, HodgeStructureOn.tensorProduct_F_eq_iSup_piece, HodgeStructure.dual_piece]
  let f : HodgeStructure.Hom hs (hs₁.dual.tensorProduct hs₂) :=
    { toIntLinearMap :=
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap
      map_mem_F p x hx := by
        rw [integralMapToComplex_dualTensorHomEquiv_symm h₁ h₂]
        rwa [HodgeStructureOn.comap_F, Submodule.mem_comap] at hx }
  have hf : Function.Injective f.toIntLinearMap := (dualTensorHomEquiv ℤ V₁ V₂).symm.injective
  refine ((hQ₁.tensorProduct hQ₂).comp f hf).of_F_eq_F_add 0 (by omega) ?_
  exact fun p ↦ by simpa only [add_zero] using (hF p).symm

/-- **Polarizable pure Hodge structures are closed under internal homs.** The internal hom of
weights `n₁` and `n₂` is polarizable of weight `n₂ - n₁`. -/
theorem IsPolarizable.internalHom (h : IsPolarizable h₁ hs₁) (h' : IsPolarizable h₂ hs₂) :
    IsPolarizable (isBaseChange_homLatticeMap h₁ h₂) (hs₁.internalHom hs₂) := by
  obtain ⟨P₁⟩ := isPolarizable_iff_nonempty.mp h.dual
  obtain ⟨P₂⟩ := isPolarizable_iff_nonempty.mp h'
  exact (⟨_, P₁.isPolarization.internalHom P₂.isPolarization⟩ : Polarization _ _).isPolarizable

end TauCeti.Hodge
