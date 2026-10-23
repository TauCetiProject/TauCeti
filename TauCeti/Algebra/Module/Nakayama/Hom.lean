/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Nakayama.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.DualHom

/-!
# Hom duality for the Nakayama construction

For a finite projective left module `P` over a possibly noncommutative algebra `A`,
the Nakayama module `ν(P) = D Hom_A(P,A)` represents the scalar dual of `Hom_A(P,-)`:

`D Hom_A(P,N) ≃ Hom_A(N,ν(P))`.

The equivalence is linear over any commutative ground ring and natural in both modules.
Neither the algebra nor the coefficient module needs to be finite-dimensional. Evaluation
on the elementary map `x ↦ ψ(x) • n` characterizes both directions of the equivalence.

Applied to the terms of a projective presentation, naturality identifies the dual Hom
complex with the Hom complex into the Nakayama terms. Together with the kernel description
of `D Tr`, this is the termwise comparison used in Auslander–Reiten duality.

The construction uses `balancedDualTensorHomEquiv` for finite projective modules and the
universal property of `BalancedTensorProduct` to curry its scalar dual. The Nakayama action
is the domain action on functionals, rather than codomain scaling.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace TauCeti

variable (k A P N : Type*) [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid P] [Module A P]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

private def nakayamaTensorDualEquiv :
    Module.Dual k (BalancedTensorProduct k A (Module.Dual A P) N) ≃ₗ[k]
      (N →ₗ[A] NakayamaModule k A P) where
  toFun χ :=
    { toFun := fun n ↦ (NakayamaModule.equivDual k A P).symm
        { toFun := fun ψ ↦ χ (BalancedTensorProduct.tmul k A ψ n)
          map_add' := fun ψ ψ' ↦ by simp [BalancedTensorProduct.add_tmul]
          map_smul' := fun c ψ ↦ by simp }
      map_add' := fun n n' ↦ by ext ψ; simp [BalancedTensorProduct.tmul_add]
      map_smul' := fun a n ↦ by
        ext ψ
        simp [NakayamaModule.smul_apply, BalancedTensorProduct.balance] }
  invFun F := BalancedTensorProduct.lift
    { toFun := fun ψ ↦
        { toFun := fun n ↦ NakayamaModule.equivDual k A P (F n) ψ
          map_add' := fun n n' ↦ by simp
          map_smul' := fun c n ↦ by simp }
      map_add' := fun ψ ψ' ↦ by ext n; simp
      map_smul' := fun c ψ ↦ by ext n; simp }
    (fun a ψ n ↦ by simp [NakayamaModule.smul_apply])
  left_inv χ := by
    apply BalancedTensorProduct.hom_ext
    intro ψ n
    simp
  right_inv F := by
    ext n ψ
    simp
  map_add' χ χ' := by ext n ψ; simp
  map_smul' c χ := by ext n ψ; simp

variable [Module.Finite A P] [Module.Projective A P]

/-- Scalar duality of Hom from a finite projective module is represented by its Nakayama
module: `D Hom_A(P,N) ≃ Hom_A(N,ν(P))`. -/
noncomputable def nakayamaHomEquiv :
    Module.Dual k (P →ₗ[A] N) ≃ₗ[k] (N →ₗ[A] NakayamaModule k A P) :=
  (balancedDualTensorHomEquiv k A P N).dualMap.trans (nakayamaTensorDualEquiv k A P N)

/-- The functional corresponding to `χ` evaluates on `ψ` at `n` by applying `χ` to the
elementary map `x ↦ ψ(x) • n`. -/
@[simp]
theorem nakayamaHomEquiv_apply (χ : Module.Dual k (P →ₗ[A] N))
    (n : N) (ψ : Module.Dual A P) :
    NakayamaModule.equivDual k A P (nakayamaHomEquiv k A P N χ n) ψ =
      χ (balancedDualTensorHom k A P N (BalancedTensorProduct.tmul k A ψ n)) := by
  simp [nakayamaHomEquiv, nakayamaTensorDualEquiv]

/-- Inverse Hom duality evaluates on a elementary map by the associated Nakayama functional. -/
@[simp]
theorem nakayamaHomEquiv_symm_apply (F : N →ₗ[A] NakayamaModule k A P)
    (ψ : Module.Dual A P) (n : N) :
    (nakayamaHomEquiv k A P N).symm F
        (balancedDualTensorHom k A P N (BalancedTensorProduct.tmul k A ψ n)) =
      NakayamaModule.equivDual k A P (F n) ψ := by
  simpa only [nakayamaHomEquiv_apply] using
    congrArg (fun G ↦ NakayamaModule.equivDual k A P (G n) ψ)
      ((nakayamaHomEquiv k A P N).apply_symm_apply F)

section Naturality

variable {P N} {Q N' : Type*}
  [AddCommMonoid Q] [Module A Q] [Module.Finite A Q] [Module.Projective A Q]
  [AddCommGroup N'] [Module A N'] [Module k N'] [IsScalarTower k A N']

/-- Nakayama Hom duality is covariantly natural in the projective module: dualizing
precomposition by `f` corresponds to postcomposition by `ν(f)`. -/
@[simp]
theorem nakayamaHomEquiv_dualMap_lcomp (f : P →ₗ[A] Q)
    (χ : Module.Dual k (P →ₗ[A] N)) :
    nakayamaHomEquiv k A Q N ((f.lcomp k N).dualMap χ) =
      f.nakayamaMap.comp (nakayamaHomEquiv k A P N χ) := by
  ext n ψ
  simp only [nakayamaHomEquiv_apply, LinearMap.dualMap_apply, LinearMap.comp_apply,
    LinearMap.nakayamaMap_apply]
  congr 1
  ext x
  simp

/-- Nakayama Hom duality is contravariantly natural in the coefficient module: dualizing
postcomposition by `g` corresponds to precomposition by `g`. -/
@[simp]
theorem nakayamaHomEquiv_dualMap_compRight (g : N' →ₗ[A] N)
    (χ : Module.Dual k (P →ₗ[A] N)) :
    nakayamaHomEquiv k A P N' ((g.compRight k).dualMap χ) =
      (nakayamaHomEquiv k A P N χ).comp g := by
  ext n ψ
  simp only [nakayamaHomEquiv_apply, LinearMap.dualMap_apply, LinearMap.comp_apply]
  congr 1
  ext x
  simp

end Naturality

end TauCeti
