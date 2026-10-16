/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Transpose
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.DualHom
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Tensoring the Auslander–Bridger transpose

For a map `f : P₁ →ₗ[A] P₀` between finite projective left modules, tensoring its
transpose with a left module `N` gives the cokernel of precomposition
`Hom_A(P₀,N) → Hom_A(P₁,N)`. The equivalence sends `[φ] ⊗ n` to the class of
`x ↦ φ(x) • n`, and is natural in `N`.

This identifies the cokernel of a projective presentation's Hom complex with the tensor product of
its transpose, a comparison used in Auslander–Reiten duality. For a general projective
presentation, this cokernel is not asserted to be `Ext¹`: the presenting arrow need
not be injective. No minimality, exactness, or finite-dimensionality is needed here.

For finite projectives, `balancedDualTensorHomEquiv` identifies dual tensors with Hom spaces.
Evaluation carries the relations defining the transpose to the image of precomposition,
so it descends to the Hom cokernel.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

namespace LinearMap

open TauCeti MulOpposite

variable {k A P₀ P₁ N : Type*} [CommRing k] [Ring A] [Algebra k A]
  [AddCommMonoid P₀] [Module A P₀] [AddCommMonoid P₁] [Module A P₁]
  [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

private noncomputable def transposeTensorBilinear (f : P₁ →ₗ[A] P₀) :
    AuslanderReitenTranspose f →ₗ[k]
      N →ₗ[k] ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) := by
  let b := (BalancedTensorProduct.mk k A (M := Module.Dual A P₁) (N := N)).compr₂
    ((range (f.lcomp k N)).mkQ.comp (balancedDualTensorHom k A P₁ N))
  refine ((AuslanderReitenTranspose.mk f).restrictScalars k).liftOfSurjective
    (by simpa only [LinearMap.coe_restrictScalars] using
      AuslanderReitenTranspose.mk_surjective f) ⟨b, ?_⟩
  intro φ hφ
  have hmem : φ ∈ range (f.lcomp Aᵐᵒᵖ A) := by
    simpa only [ker_restrictScalars, AuslanderReitenTranspose.ker_mk,
      Submodule.restrictScalars_mem] using hφ
  obtain ⟨ψ, rfl⟩ := hmem
  apply LinearMap.mem_ker.mpr
  ext n
  dsimp [b]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨balancedDualTensorHom k A P₀ N (BalancedTensorProduct.tmul k A ψ n), ?_⟩
  ext x
  simp

private theorem transposeTensorBilinear_mk (f : P₁ →ₗ[A] P₀)
    (φ : Module.Dual A P₁) (n : N) :
    transposeTensorBilinear (k := k) f (AuslanderReitenTranspose.mk f φ) n =
      Submodule.Quotient.mk
        (balancedDualTensorHom k A P₁ N (BalancedTensorProduct.tmul k A φ n)) := by
  rw [transposeTensorBilinear, ← LinearMap.restrictScalars_apply k
    (AuslanderReitenTranspose.mk f) φ, LinearMap.equivOfSurjective_apply]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, BalancedTensorProduct.mk_apply,
    Submodule.mkQ_apply]

private noncomputable def transposeTensorToCokernel (f : P₁ →ₗ[A] P₀) :
    BalancedTensorProduct k A (AuslanderReitenTranspose f) N →ₗ[k]
      ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) :=
  BalancedTensorProduct.lift (transposeTensorBilinear (k := k) f) fun a t n ↦ by
    obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective f t
    rw [← map_smul, transposeTensorBilinear_mk, transposeTensorBilinear_mk]
    congr 1
    ext x
    simp [MulOpposite.smul_eq_mul_unop, mul_smul]

private theorem transposeTensorToCokernel_tmul (f : P₁ →ₗ[A] P₀)
    (φ : Module.Dual A P₁) (n : N) :
    transposeTensorToCokernel f
        (BalancedTensorProduct.tmul k A (AuslanderReitenTranspose.mk f φ) n) =
      Submodule.Quotient.mk
        (balancedDualTensorHom k A P₁ N (BalancedTensorProduct.tmul k A φ n)) := by
  simp [transposeTensorToCokernel, transposeTensorBilinear_mk]

variable [Module.Finite A P₀] [Module.Projective A P₀]
  [Module.Finite A P₁] [Module.Projective A P₁]

private noncomputable def cokernelToTransposeTensor (f : P₁ →ₗ[A] P₀) :
    ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) →ₗ[k]
      BalancedTensorProduct k A (AuslanderReitenTranspose f) N := by
  let t := BalancedTensorProduct.map ((AuslanderReitenTranspose.mk f).restrictScalars k)
    (LinearMap.id : N →ₗ[k] N) (fun a φ ↦ by
      simpa only [LinearMap.restrictScalars_apply] using
        map_smul (AuslanderReitenTranspose.mk f) (op a) φ) (fun _ _ ↦ rfl)
  apply (range (f.lcomp k N)).liftQ
    (t.comp (balancedDualTensorHomEquiv k A P₁ N).symm.toLinearMap)
  rintro _ ⟨F, rfl⟩
  obtain ⟨z, rfl⟩ := balancedDualTensorHom_bijective k A (P := P₀) (N := N) |>.surjective F
  induction z using BalancedTensorProduct.induction_on with
  | ht ψ n =>
    have heq : f.lcomp k N
        (balancedDualTensorHom k A P₀ N (BalancedTensorProduct.tmul k A ψ n)) =
        balancedDualTensorHom k A P₁ N
          (BalancedTensorProduct.tmul k A (f.lcomp Aᵐᵒᵖ A ψ) n) := by
      ext x
      simp
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe, heq,
      balancedDualTensorHomEquiv_symm_balancedDualTensorHom]
    dsimp [t]
    rw [BalancedTensorProduct.map_tmul]
    simp
  | ha z w hz hw =>
    simpa only [LinearMap.mem_ker, map_add, add_zero] using congrArg₂ (· + ·) hz hw

private theorem cokernelToTransposeTensor_mk (f : P₁ →ₗ[A] P₀) (F : P₁ →ₗ[A] N) :
    cokernelToTransposeTensor f (Submodule.Quotient.mk F) =
      BalancedTensorProduct.map ((AuslanderReitenTranspose.mk f).restrictScalars k)
        (LinearMap.id : N →ₗ[k] N) (fun a φ ↦ by
      simpa only [LinearMap.restrictScalars_apply] using
        map_smul (AuslanderReitenTranspose.mk f) (op a) φ) (fun _ _ ↦ rfl)
        ((balancedDualTensorHomEquiv k A P₁ N).symm F) := by
  simp [cokernelToTransposeTensor]

/-- Tensoring the transpose of a map between finite projectives identifies it with the
cokernel of precomposition on Hom spaces. The tensor product is balanced over the possibly
noncommutative algebra `A`, and the equivalence is linear over the ground ring `k`. -/
noncomputable def auslanderReitenTransposeTensorEquivCokernel (f : P₁ →ₗ[A] P₀) :
    BalancedTensorProduct k A (AuslanderReitenTranspose f) N ≃ₗ[k]
      ((P₁ →ₗ[A] N) ⧸ range (f.lcomp k N)) :=
  LinearEquiv.ofLinearMap (transposeTensorToCokernel f) (cokernelToTransposeTensor f)
    (by
      apply LinearMap.ext
      intro y
      induction y using Submodule.Quotient.induction_on with
      | _ F =>
        obtain ⟨z, rfl⟩ := balancedDualTensorHom_bijective k A (P := P₁) (N := N) |>.surjective F
        induction z using BalancedTensorProduct.induction_on with
        | ht φ n =>
          simp only [LinearMap.comp_apply, cokernelToTransposeTensor_mk,
            balancedDualTensorHomEquiv_symm_balancedDualTensorHom, LinearMap.id_apply]
          rw [BalancedTensorProduct.map_tmul]
          simp only [LinearMap.restrictScalars_apply, LinearMap.id_apply,
            transposeTensorToCokernel_tmul]
        | ha z w hz hw =>
          simpa only [LinearMap.comp_apply, ← Submodule.mkQ_apply, map_add, LinearMap.id_apply]
            using congrArg₂ (· + ·) hz hw)
    (by
      apply BalancedTensorProduct.hom_ext
      intro t n
      obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective f t
      simp only [LinearMap.comp_apply, transposeTensorToCokernel_tmul,
        cokernelToTransposeTensor_mk, balancedDualTensorHomEquiv_symm_balancedDualTensorHom]
      rw [BalancedTensorProduct.map_tmul]
      rfl)

/-- The tensor–cokernel equivalence evaluates a functional representative on the source
of the presenting map and takes its Hom-cokernel class. -/
@[simp]
theorem auslanderReitenTransposeTensorEquivCokernel_tmul (f : P₁ →ₗ[A] P₀)
    (φ : Module.Dual A P₁) (n : N) :
    auslanderReitenTransposeTensorEquivCokernel f
        (BalancedTensorProduct.tmul k A (AuslanderReitenTranspose.mk f φ) n) =
      Submodule.Quotient.mk
        (balancedDualTensorHom k A P₁ N (BalancedTensorProduct.tmul k A φ n)) :=
  transposeTensorToCokernel_tmul f φ n

/-- Inverse transport tensors the transpose quotient with `N` after the finite-projective
tensor–Hom identification. -/
@[simp]
theorem auslanderReitenTransposeTensorEquivCokernel_symm_mk (f : P₁ →ₗ[A] P₀)
    (F : P₁ →ₗ[A] N) :
    (auslanderReitenTransposeTensorEquivCokernel f).symm (Submodule.Quotient.mk F) =
      BalancedTensorProduct.map ((AuslanderReitenTranspose.mk f).restrictScalars k)
        (LinearMap.id : N →ₗ[k] N) (fun a φ ↦ by
      simpa only [LinearMap.restrictScalars_apply] using
        map_smul (AuslanderReitenTranspose.mk f) (op a) φ) (fun _ _ ↦ rfl)
        ((balancedDualTensorHomEquiv k A P₁ N).symm F) :=
  cokernelToTransposeTensor_mk f F

variable {N' : Type*} [AddCommGroup N'] [Module A N'] [Module k N']
  [IsScalarTower k A N']

/-- The tensor–cokernel comparison commutes with postcomposition in the coefficient module. -/
@[simp]
theorem auslanderReitenTransposeTensorEquivCokernel_map (f : P₁ →ₗ[A] P₀)
    (g : N →ₗ[A] N') (z : BalancedTensorProduct k A (AuslanderReitenTranspose f) N) :
    auslanderReitenTransposeTensorEquivCokernel f
        (BalancedTensorProduct.map LinearMap.id (g.restrictScalars k)
          (fun _ _ ↦ rfl) (fun a n ↦ by simp only [restrictScalars_apply, map_smul]) z) =
      (range (f.lcomp k N)).mapQ (range (f.lcomp k N')) (g.compRight k)
        (by
          rintro _ ⟨F, rfl⟩
          exact ⟨g.comp F, rfl⟩)
        (auslanderReitenTransposeTensorEquivCokernel f z) := by
  induction z using BalancedTensorProduct.induction_on with
  | ht t n =>
    obtain ⟨φ, rfl⟩ := AuslanderReitenTranspose.mk_surjective f t
    rw [BalancedTensorProduct.map_tmul]
    simp only [LinearMap.id_apply, restrictScalars_apply,
      auslanderReitenTransposeTensorEquivCokernel_tmul, Submodule.mapQ_apply]
    congr 1
    ext x
    simp
  | ha z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

end LinearMap
