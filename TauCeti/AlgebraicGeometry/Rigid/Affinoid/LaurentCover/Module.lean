/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.LaurentCover.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod
import TauCeti.RingTheory.Affinoid.Subdomain.Flat
import Mathlib.RingTheory.Flat.Equalizer

/-!
# The Laurent sequence for arbitrary modules

For an affinoid algebra `A`, an element `f : A`, and any algebraic `A`-module `M`,
the augmented two-piece Laurent sequence

`0 → M → (A⟨f⟩ ⊗[A] M) × (A⟨f⁻¹⟩ ⊗[A] M) → A⟨f,f⁻¹⟩ ⊗[A] M → 0`

is exact. The differential is second restriction minus first restriction. These are
algebraic tensors with the actual overlap algebra, not an identification of the overlap
with an algebraic tensor product of the two pieces. No topology or finiteness assumption
is imposed on `M`.

Right exactness of tensor product gives middle exactness and surjectivity over any complete
ultrametric normed ring. For affinoids, flatness of the overlap algebra also preserves
injectivity of the augmentation. In particular gluing holds for infinitely generated and
nonflat modules, as well as for modules detecting nilpotents.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§8.2.1–8.2.2.
-/

public section

namespace TauCeti.LaurentCover

open TensorProduct

variable {A : Type*} [NormedCommRing A] [IsUltrametricDist A]
  (M : Type*) [AddCommGroup M] [Module A M]

local notation "L(" f ")" => LaurentFraction (fun _ : Fin 1 ↦ f) (Fin.elim0 : Fin 0 → A)
local notation "G(" f ")" => LaurentFraction (Fin.elim0 : Fin 0 → A) (fun _ : Fin 1 ↦ f)
local notation "O(" f ")" => LaurentFraction (fun _ : Fin 1 ↦ f) (fun _ : Fin 1 ↦ f)

/-- Restrict an algebraic module element to both pieces of the Laurent cover. -/
noncomputable def moduleAugmentation (f : A) :
    M →ₗ[A] (L(f) ⊗[A] M) × (G(f) ⊗[A] M) :=
  (TensorProduct.mk A (L(f)) M 1).prod (TensorProduct.mk A (G(f)) M 1)

@[simp]
theorem moduleAugmentation_apply (f : A) (m : M) :
    moduleAugmentation M f m = (1 ⊗ₜ[A] m, 1 ⊗ₜ[A] m) := (rfl)

/-- The Laurent differential on algebraic modules: second restriction minus first. -/
noncomputable def moduleDiff (f : A) :
    ((L(f) ⊗[A] M) × (G(f) ⊗[A] M)) →ₗ[A] O(f) ⊗[A] M :=
  ((geToOverlap f).toLinearMap.rTensor M).comp (LinearMap.snd A _ _) -
    ((leToOverlap f).toLinearMap.rTensor M).comp (LinearMap.fst A _ _)

@[simp]
theorem moduleDiff_apply (f : A) (u : L(f) ⊗[A] M) (v : G(f) ⊗[A] M) :
    moduleDiff M f (u, v) =
      (geToOverlap f).toLinearMap.rTensor M v - (leToOverlap f).toLinearMap.rTensor M u := (rfl)

private theorem moduleAugmentation_lid (f : A) :
    (moduleAugmentation M f).comp (TensorProduct.lid A M).toLinearMap =
      (TensorProduct.prodLeft A A (L(f)) (G(f)) M).toLinearMap.comp
        ((Algebra.linearMap A (L(f) × G(f))).rTensor M) := by
  apply TensorProduct.ext'
  intro a m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_tmul,
    moduleAugmentation_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply,
    Prod.algebraMap_apply, TensorProduct.prodLeft_tmul]
  simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul']

private theorem moduleDiff_prodLeft (f : A) :
    (moduleDiff M f).comp (TensorProduct.prodLeft A A (L(f)) (G(f)) M).toLinearMap =
      (diff f).rTensor M := by
  apply TensorProduct.ext'
  rintro ⟨u, v⟩ m
  simp [sub_tmul]

/-- Restriction to the Laurent pieces commutes with every algebraic module map. -/
theorem moduleAugmentation_natural {N : Type*} [AddCommGroup N] [Module A N]
    (f : A) (ψ : M →ₗ[A] N) (m : M) :
    ((ψ.lTensor (L(f))).prodMap (ψ.lTensor (G(f)))) (moduleAugmentation M f m) =
      moduleAugmentation N f (ψ m) := by
  simp

/-- The Laurent differential commutes with every algebraic module map. -/
theorem moduleDiff_natural {N : Type*} [AddCommGroup N] [Module A N]
    (f : A) (ψ : M →ₗ[A] N)
    (z : (L(f) ⊗[A] M) × (G(f) ⊗[A] M)) :
    ψ.lTensor (O(f)) (moduleDiff M f z) =
      moduleDiff N f (((ψ.lTensor (L(f))).prodMap (ψ.lTensor (G(f)))) z) := by
  rcases z with ⟨u, v⟩
  simp only [moduleDiff_apply, map_sub, LinearMap.prodMap_apply]
  simp only [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
    LinearMap.rTensor_comp_lTensor]

variable [CompleteSpace A]

/-- Tensoring the scalar Laurent sequence gives exactness at the pair of module sections.
The module need not be flat or finite. -/
theorem exact_moduleAugmentation_moduleDiff (f : A) :
    Function.Exact (moduleAugmentation M f) (moduleDiff M f) := by
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.lid A M)
    (e₂ := TensorProduct.prodLeft A A (L(f)) (G(f)) M)
    (e₃ := LinearEquiv.refl A (O(f) ⊗[A] M))
    (moduleAugmentation_lid M f) (by simpa using moduleDiff_prodLeft M f)
  exact rTensor_exact M (exact_algebraMap_diff f) (diff_surjective f)

/-- Every module section on the Laurent overlap is a difference of restrictions. -/
theorem moduleDiff_surjective (f : A) : Function.Surjective (moduleDiff M f) := by
  have h := LinearMap.rTensor_surjective M (diff_surjective f)
  intro w
  obtain ⟨z, hz⟩ := h w
  refine ⟨TensorProduct.prodLeft A A (L(f)) (G(f)) M z, ?_⟩
  exact (LinearMap.congr_fun (moduleDiff_prodLeft M f) z).trans hz

section Affinoid

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedAlgebra K A] (hA : IsAffinoidAlgebra K A)

include hA in
/-- The module augmentation of a Laurent cover of an affinoid algebra is injective,
even for nonflat and infinitely generated modules. -/
theorem moduleAugmentation_injective (f : A) :
    Function.Injective (moduleAugmentation M f) := by
  have : Module.Flat A (O(f)) := RingHom.flat_algebraMap_iff.mp
    ((LaurentFraction.isAffinoidSubdomainMap hA (f := fun _ : Fin 1 ↦ f)
      (g := fun _ : Fin 1 ↦ f)).flat hA)
  let α := Algebra.linearMap A (L(f) × G(f))
  have hi := LinearMap.lTensor_injective_of_exact_of_flat (diff f) (diff_surjective f)
    α (algebraMap_injective hA f) (exact_algebraMap_diff f) M
  have hr : Function.Injective (α.rTensor M) := by
    intro x y hxy
    apply (TensorProduct.comm A A M).injective
    apply hi
    rw [LinearMap.lTensor_comm, LinearMap.lTensor_comm]
    exact congrArg (TensorProduct.comm A (L(f) × G(f)) M) hxy
  intro m n hmn
  apply (TensorProduct.lid A M).symm.injective
  apply hr
  apply (TensorProduct.prodLeft A A (L(f)) (G(f)) M).injective
  have he (x : M) := LinearMap.congr_fun (moduleAugmentation_lid M f)
    ((TensorProduct.lid A M).symm x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply] at he
  exact (he m).symm.trans (hmn.trans (he n))

include hA in
/-- Compatible algebraic module sections on the two Laurent pieces glue uniquely. -/
theorem existsUnique_module_gluing (f : A) (u : L(f) ⊗[A] M) (v : G(f) ⊗[A] M)
    (h : (leToOverlap f).toLinearMap.rTensor M u =
      (geToOverlap f).toLinearMap.rTensor M v) :
    ∃! m : M, moduleAugmentation M f m = (u, v) := by
  obtain ⟨m, hm⟩ := (exact_moduleAugmentation_moduleDiff M f (u, v)).mp (by simp [h])
  exact ⟨m, hm, fun n hn ↦ moduleAugmentation_injective M hA f (hn.trans hm.symm)⟩

end Affinoid

end TauCeti.LaurentCover
