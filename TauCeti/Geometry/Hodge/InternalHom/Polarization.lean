/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Hodge.InternalHom.Contraction
public import TauCeti.Geometry.Hodge.SelfDuality
public import TauCeti.Geometry.Hodge.TensorProduct.Polarization

/-!
# Polarizability of the internal hom

The internal hom of polarizable integral pure Hodge structures is polarizable. Given integral
polarizing forms on `V*` and `W`, their tensor product pulls back along inverse contraction
`Hom_ℤ(V, W) ≃ V* ⊗ W` to polarize the internal hom, of weight `weight W - weight V`.

A polarizing form on the dual lattice exists by `TauCeti.Hodge.IsPolarizable.dual`. It need not
be the inverse of a chosen integral form on `V`: that inverse is generally rational. The
construction here takes any integral polarization of the dual, so it needs no unimodularity
hypothesis.

## Main declarations

* `TauCeti.Hodge.IsPolarization.internalHom`: the explicit pulled-back integral form polarizes
  the internal hom.
* `TauCeti.Hodge.IsPolarizable.internalHom`: polarizable pure Hodge structures are closed under
  internal homs.

## References

Deligne, *Théorie de Hodge II*, §2.1; Peters–Steenbrink, *Mixed Hodge Structures*, §2.1.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

variable {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [AddCommGroup V₂]
variable [Module.Free ℤ V₁] [Module.Finite ℤ V₁]
variable [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
variable {ι₁ : V₁ →ₗ[ℤ] W₁} {ι₂ : V₂ →ₗ[ℤ] W₂}
variable {h₁ : IsBaseChange ℂ ι₁} {h₂ : IsBaseChange ℂ ι₂} {n₁ n₂ : ℤ}
variable {hs₁ : HodgeStructure h₁ n₁} {hs₂ : HodgeStructure h₂ n₂}

/-- Polarizing forms on the dual and target induce an integral polarization of the internal hom:
pull back their tensor product along inverse integral contraction. -/
theorem IsPolarization.internalHom {Q₁ : LinearMap.BilinForm ℤ (Module.Dual ℤ V₁)}
    {Q₂ : LinearMap.BilinForm ℤ V₂}
    (hQ₁ : IsPolarization (isBaseChange_dualLatticeMap h₁) hs₁.dual Q₁)
    (hQ₂ : IsPolarization h₂ hs₂ Q₂) :
    IsPolarization (isBaseChange_homLatticeMap h₁ h₂) (hs₁.internalHom hs₂)
      (LinearMap.BilinForm.comp (Q₁.tmul Q₂ : LinearMap.BilinForm ℤ (Module.Dual ℤ V₁ ⊗[ℤ] V₂))
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap) := by
  let _ : Module.Finite ℂ W₁ := h₁.finite
  let E := (dualTensorHomEquiv ℂ W₁ W₂).symm
  have hconj : ∀ φ, E ((latticeConjugation (isBaseChange_homLatticeMap h₁ h₂)).toEquiv φ) =
      (latticeConjugation
        (isBaseChange_tensorLatticeMap (isBaseChange_dualLatticeMap h₁) h₂)).toEquiv (E φ) := by
    rw [latticeConjugation_internalHom h₁ h₂,
      latticeConjugation_tensorProduct (isBaseChange_dualLatticeMap h₁) h₂,
      latticeConjugation_dual h₁]
    exact (latticeConjugation h₁).dualTensorHomEquiv_symm_map_internalHom_conj
      (latticeConjugation h₂)
  let source := (hs₁.dual.tensorProduct hs₂).comap E hconj
  let f : HodgeStructure.Hom source (hs₁.dual.tensorProduct hs₂) :=
    { toIntLinearMap :=
        (dualTensorHomEquiv ℤ V₁ V₂).symm.toLinearMap.toAddMonoidHom.toIntLinearMap
      map_mem_F p φ hφ := by
        rw [integralMapToComplex_dualTensorHomEquiv_symm h₁ h₂]
        dsimp only [source] at hφ
        rw [HodgeStructureOn.comap_F] at hφ
        exact hφ }
  have hpol := (hQ₁.tensorProduct hQ₂).comp f
    (dualTensorHomEquiv ℤ V₁ V₂).symm.injective
  -- The tensor presentation has weight `-n₁ + n₂`; the internal hom writes the same weight
  -- as `n₂ - n₁`. Transfer the form by the proved filtration comparison, with shift zero.
  refine hpol.of_F_eq_F_add (hs' := hs₁.internalHom hs₂) 0 (by omega) ?_
  intro p
  dsimp only [source]
  rw [HodgeStructure.internalHom_F_eq_comap, add_zero, HodgeStructureOn.comap_F]

/-- **The internal hom of polarizable integral pure Hodge structures is polarizable.** -/
theorem IsPolarizable.internalHom (hpol₁ : IsPolarizable h₁ hs₁)
    (hpol₂ : IsPolarizable h₂ hs₂) :
    IsPolarizable (isBaseChange_homLatticeMap h₁ h₂) (hs₁.internalHom hs₂) := by
  obtain ⟨P₁⟩ := isPolarizable_iff_nonempty.mp hpol₁.dual
  obtain ⟨P₂⟩ := isPolarizable_iff_nonempty.mp hpol₂
  exact (⟨_, P₁.isPolarization.internalHom P₂.isPolarization⟩ :
    Polarization _ (hs₁.internalHom hs₂)).isPolarizable

end TauCeti.Hodge
