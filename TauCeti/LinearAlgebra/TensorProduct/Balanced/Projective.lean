/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.Projective
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basis
import TauCeti.LinearAlgebra.TensorProduct.Balanced.Finsupp

/-!
# Balanced tensor products with projective modules

Tensoring an injection with a projective module preserves injectivity on either side
of the balanced tensor product. On a free module this is injectivity in each finitely
supported coordinate. The result for a projective module follows by retraction.
This gives degreewise injectivity when tensoring a short exact sequence with a
projective resolution.

See T. Y. Lam, *A First Course in Noncommutative Rings*, §24, (24.20), p. 365.
-/

public section

open MulOpposite

namespace TauCeti.BalancedTensorProduct

section LeftProjective

variable {R A M M' P : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M'] [IsScalarTower R Aᵐᵒᵖ M']
  [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P] [Module.Projective A P]

variable (R P) in
/-- Tensoring an injective right module map with a projective left module is injective. -/
theorem injective_map_id_of_projective (f : M →ₗ[Aᵐᵒᵖ] M') (hf : Function.Injective f) :
    Function.Injective (map (A := A) (f.restrictScalars R) (LinearMap.id : P →ₗ[R] P)
      (fun a m ↦ by simpa only [LinearMap.restrictScalars_apply] using f.map_smul (op a) m)
      (fun _ _ ↦ rfl)) := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective A P)
  let p := Finsupp.linearCombination A (id : P → P)
  let i := lTensor R M s
  let i' := lTensor R M' s
  have hi : Function.Injective i := LinearMap.injective_of_comp_eq_id i (lTensor R M p) <| by
    apply hom_ext
    intro m x
    simp only [LinearMap.comp_apply, i, lTensor_tmul, p, hs x, LinearMap.id_apply]
  have hsmul (a : A) (m : M) :
      f.restrictScalars R (op a • m) = op a • f.restrictScalars R m := by
    simpa only [LinearMap.restrictScalars_apply] using f.map_smul (op a) m
  let fFree := map (f.restrictScalars R) (LinearMap.id : (P →₀ A) →ₗ[R] (P →₀ A))
    hsmul (fun _ _ ↦ rfl)
  have hfree : Function.Injective fFree := by
    apply Function.Injective.of_comp (f := (finsuppScalarRight R A M' P).toLinearMap)
    have hnat := finsuppScalarRight_map R A P (f.restrictScalars R) hsmul
    rw [← LinearMap.coe_comp, hnat, LinearMap.coe_comp]
    exact (Finsupp.mapRange_injective _ f.map_zero hf).comp (finsuppScalarRight R A M P).injective
  have hcomm : i'.comp (map (f.restrictScalars R) (LinearMap.id : P →ₗ[R] P)
      hsmul (fun _ _ ↦ rfl)) = fFree.comp i := by
    apply hom_ext
    intro m x
    simp only [LinearMap.comp_apply, i, i', fFree, map_tmul, lTensor_tmul, LinearMap.id_apply]
  intro x y h
  apply hi (hfree ?_)
  simpa only [← LinearMap.comp_apply, hcomm] using congrArg i' h

end LeftProjective

section RightProjective

variable {R A P N N' : Type*} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup P] [Module R P] [Module Aᵐᵒᵖ P] [IsScalarTower R Aᵐᵒᵖ P]
  [Module.Projective Aᵐᵒᵖ P]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommGroup N'] [Module R N'] [Module A N'] [IsScalarTower R A N']

variable (R P) in
/-- Tensoring an injective left module map with a projective right module is injective. -/
theorem injective_lTensor_of_projective (f : N →ₗ[A] N') (hf : Function.Injective f) :
    Function.Injective (lTensor R P f) := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp (inferInstance : Module.Projective Aᵐᵒᵖ P)
  let p := Finsupp.linearCombination Aᵐᵒᵖ (id : P → P)
  have hsmul (a : A) (x : P) : s.restrictScalars R (op a • x) = op a • s.restrictScalars R x := by
    simpa only [LinearMap.restrictScalars_apply] using s.map_smul (op a) x
  let i : BalancedTensorProduct R A P N →ₗ[R] BalancedTensorProduct R A (P →₀ Aᵐᵒᵖ) N :=
    map (s.restrictScalars R) LinearMap.id hsmul (fun _ _ ↦ rfl)
  let i' : BalancedTensorProduct R A P N' →ₗ[R] BalancedTensorProduct R A (P →₀ Aᵐᵒᵖ) N' :=
    map (s.restrictScalars R) LinearMap.id hsmul (fun _ _ ↦ rfl)
  let r : BalancedTensorProduct R A (P →₀ Aᵐᵒᵖ) N →ₗ[R] BalancedTensorProduct R A P N :=
    map (p.restrictScalars R) LinearMap.id
      (fun a x ↦ by simpa only [LinearMap.restrictScalars_apply] using p.map_smul (op a) x)
      (fun _ _ ↦ rfl)
  have hi : Function.Injective i := LinearMap.injective_of_comp_eq_id i r <| by
    apply hom_ext
    intro x n
    simp only [LinearMap.comp_apply, i, r, map_tmul, LinearMap.restrictScalars_apply,
      LinearMap.id_apply, p, hs x]
  let b : Module.Basis P Aᵐᵒᵖ (P →₀ Aᵐᵒᵖ) := Finsupp.basisSingleOne
  have hfree : Function.Injective (lTensor R (P →₀ Aᵐᵒᵖ) f) := by
    apply Function.Injective.of_comp
      (f := (b.balancedTensorProductEquiv (k := R) (N := N')).toLinearMap)
    have hsmul' (a : A) (n : N) : f.restrictScalars R (a • n) = a • f.restrictScalars R n := by
      simpa only [LinearMap.restrictScalars_apply] using f.map_smul a n
    have hTensor : lTensor R (P →₀ Aᵐᵒᵖ) f =
        map LinearMap.id (f.restrictScalars R) (fun _ _ ↦ rfl) hsmul' := by
      apply hom_ext
      intro x n
      simp only [lTensor_tmul, map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply]
    rw [← LinearMap.coe_comp, hTensor, b.balancedTensorProductEquiv_map, LinearMap.coe_comp]
    exact (Finsupp.mapRange_injective _ f.map_zero hf).comp b.balancedTensorProductEquiv.injective
  have hcomm : i'.comp (lTensor R P f) = (lTensor R (P →₀ Aᵐᵒᵖ) f).comp i := by
    apply hom_ext
    intro x n
    simp only [LinearMap.comp_apply, i, i', lTensor_tmul, map_tmul, LinearMap.id_apply]
  intro x y h
  apply hi (hfree ?_)
  simpa only [← LinearMap.comp_apply, hcomm] using congrArg i' h

end RightProjective

end TauCeti.BalancedTensorProduct
