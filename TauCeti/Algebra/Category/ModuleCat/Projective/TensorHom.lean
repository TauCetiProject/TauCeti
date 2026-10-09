/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.DualHom
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Tensor evaluation and stable Hom spaces

For a finitely generated left module `M` over a possibly noncommutative algebra `A`,
the image of evaluation `Hom_A(M,A) ⊗_A N → Hom_A(M,N)` consists exactly of the maps
factoring through projectives. Consequently its cokernel is the Hom space in the
projective stable category. The intermediate projectives and the target `N` may be
arbitrarily large; neither finite presentation nor finite dimensionality is needed.

This identifies the tensor description of stable Hom with the existing categorical
quotient, as used in Auslander–Reiten duality. Evaluation is `balancedDualTensorHom`,
and the stable quotient is `ExactStructure.projectiveStableFunctor` for the canonical
abelian exact structure on `ModuleCat A`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Cambridge University Press (1995), Section IV.2.
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra

namespace ModuleCat

open TauCeti

universe u v w

variable (k : Type w) [CommRing k] {A : Type u} [Ring A] [Algebra k A]
  [Small.{v} A] {M N : ModuleCat.{v} A}

local notation "St" =>
  ExactStructure.projectiveStableFunctor (ExactStructure.abelian (ModuleCat A))

/-- Tensor evaluation always becomes zero modulo maps through projective modules. -/
@[simp]
theorem projectiveStableFunctor_map_balancedDualTensorHom_eq_zero
    (z : BalancedTensorProduct k A (Module.Dual A M) N) :
    (St).map (ofHom (balancedDualTensorHom k A M N z)) = 0 := by
  induction z using BalancedTensorProduct.induction_on with
  | ht φ n =>
    rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff,
      ObjectProperty.factorsThrough_iff]
    let g : A →ₗ[A] N := LinearMap.toSpanSingleton A N n
    let e : Shrink.{v} A ≃ₗ[A] A := Shrink.linearEquiv A A
    refine ⟨ModuleCat.of A (Shrink.{v} A), ?_,
      ofHom (e.symm.toLinearMap.comp φ), ofHom (g.comp e.toLinearMap), ?_⟩
    · exact (ExactStructure.abelian_isProjective_iff _).mpr inferInstance
    · ext x
      simp [g]
  | ha x y hx hy =>
    simp only [map_add, ofHom_add, Functor.map_add, hx, hy, add_zero]

variable [Module.Finite A M]

/-- A map out of a finitely generated module is zero in the projective stable category
exactly when it is in the image of balanced tensor evaluation. -/
theorem projectiveStableFunctor_map_eq_zero_iff_mem_range_balancedDualTensorHom
    (f : M →ₗ[A] N) :
    (St).map (ofHom f) = 0 ↔ f ∈ LinearMap.range (balancedDualTensorHom k A M N) := by
  constructor
  · intro hf
    rw [ExactStructure.projectiveStableFunctor_map_eq_zero_iff,
      ObjectProperty.factorsThrough_iff] at hf
    obtain ⟨P, hP, g, h, hgh⟩ := hf
    have : Projective P := (ExactStructure.abelian_isProjective_iff P).mp hP
    have : Module.Projective A P := inferInstance
    simpa only [← hom_comp, ← hgh, hom_ofHom] using
      g.hom.comp_mem_range_balancedDualTensorHom (k := k) h.hom
  · rintro ⟨z, rfl⟩
    exact projectiveStableFunctor_map_balancedDualTensorHom_eq_zero k z

/-- The cokernel of balanced tensor evaluation is the categorical stable Hom space.
The equivalence sends the class of a linear map to its image in the stable category. -/
noncomputable def tensorHomCokernelEquivProjectiveStableHom :
    ((M →ₗ[A] N) ⧸ LinearMap.range (balancedDualTensorHom k A M N)) ≃ₗ[k]
      ((St).obj M ⟶ (St).obj N) := by
  let q := ((St).mapLinearMap k).comp (homLinearEquiv (M := M) (N := N) (S := k)).symm.toLinearMap
  have hker : LinearMap.ker q = LinearMap.range (balancedDualTensorHom k A M N) := by
    ext f
    exact projectiveStableFunctor_map_eq_zero_iff_mem_range_balancedDualTensorHom k f
  have hsurj : Function.Surjective q :=
    (St).map_surjective.comp (homLinearEquiv (M := M) (N := N) (S := k)).symm.surjective
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (q.quotKerEquivOfSurjective hsurj)

/-- The tensor-cokernel comparison sends a representative to its stable morphism. -/
@[simp]
theorem tensorHomCokernelEquivProjectiveStableHom_mk (f : M →ₗ[A] N) :
    tensorHomCokernelEquivProjectiveStableHom k (Submodule.Quotient.mk f) =
      (St).map (ofHom f) := by
  rw [tensorHomCokernelEquivProjectiveStableHom, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk]
  -- The surjectivity proof uses the function composition underlying the bundled linear map.
  erw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

/-- The inverse comparison sends a stable morphism to the class of any representative. -/
@[simp]
theorem tensorHomCokernelEquivProjectiveStableHom_symm_map (f : M ⟶ N) :
    (tensorHomCokernelEquivProjectiveStableHom k).symm ((St).map f) =
      Submodule.Quotient.mk f.hom := by
  apply (tensorHomCokernelEquivProjectiveStableHom k).injective
  simp

end ModuleCat
