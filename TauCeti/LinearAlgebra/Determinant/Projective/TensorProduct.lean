/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.ConstantRank
public import TauCeti.LinearAlgebra.Determinant.TensorProduct
public import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# The determinant of a tensor product of finite projective modules

For endomorphisms `f` of `M` and `g` of `N`, finite projective modules over a commutative ring `R`
of constant ranks `m` and `n`,

`projectiveDet (f ⊗ g) = projectiveDet f ^ n * projectiveDet g ^ m`

(`LinearMap.projectiveDet_tensorProductMap`). This extends `LinearMap.det_tensorProductMap` from
free modules. As for `LinearMap.projectiveDet_smul`, the identity is checked after localizing at
each maximal ideal `𝔪`: base change to `R_𝔪` commutes with `projectiveDet`
(`LinearMap.projectiveDet_baseChange`), carries `f ⊗ g` to `(R_𝔪 ⊗ f) ⊗ (R_𝔪 ⊗ g)` up to the
isomorphism `R_𝔪 ⊗ (M ⊗ N) ≅ (R_𝔪 ⊗ M) ⊗ (R_𝔪 ⊗ N)` (Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`), and makes `M` and `N` free of ranks `m`
and `n`.
-/

public section

open Module TensorProduct

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
  [Module.Projective R N]

/-- After a base change `R → A` making `M` and `N` free, the determinant of `f ⊗ g` is
`det f ^ rank N * det g ^ rank M`, ranks taken over `A`. -/
theorem algebraMap_projectiveDet_tensorProductMap (A : Type*) [CommRing A] [Algebra R A]
    [Module.Free A (A ⊗[R] M)] [Module.Free A (A ⊗[R] N)] (f : Module.End R M)
    (g : Module.End R N) :
    algebraMap R A (projectiveDet (TensorProduct.map f g)) =
      algebraMap R A (projectiveDet f) ^ finrank A (A ⊗[R] N) *
        algebraMap R A (projectiveDet g) ^ finrank A (A ⊗[R] M) := by
  have h : (TensorProduct.map f g).baseChange A =
      (AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ∘ₗ
        TensorProduct.map (f.baseChange A) (g.baseChange A) ∘ₗ
          (AlgebraTensorModule.distribBaseChange R A M N).toLinearMap := by
    rw [← comp_assoc, AlgebraTensorModule.distribBaseChange_symm_comp_map_baseChange, comp_assoc,
      LinearEquiv.symm_comp, comp_id]
  rw [← projectiveDet_baseChange, ← projectiveDet_baseChange, ← projectiveDet_baseChange, h]
  have := projectiveDet_conj (R := A) (M := (A ⊗[R] M) ⊗[A] (A ⊗[R] N))
    (N := A ⊗[R] (M ⊗[R] N)) (TensorProduct.map (f.baseChange A) (g.baseChange A))
    (AlgebraTensorModule.distribBaseChange R A M N).symm
  rw [LinearEquiv.symm_symm] at this
  rw [this, projectiveDet_eq_det, projectiveDet_eq_det, projectiveDet_eq_det, det_tensorProductMap]

/-- **The determinant of a tensor product of finite projective modules**: for `M` and `N` of
constant ranks `m` and `n`, `projectiveDet (f ⊗ g) = projectiveDet f ^ n * projectiveDet g ^ m`. -/
theorem projectiveDet_tensorProductMap {m n : ℕ} (hM : ∀ p, rankAtStalk (R := R) M p = m)
    (hN : ∀ p, rankAtStalk (R := R) N p = n) (f : Module.End R M) (g : Module.End R N) :
    projectiveDet (TensorProduct.map f g) = projectiveDet f ^ n * projectiveDet g ^ m := by
  refine Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P)) _ _ fun P _ ↦ ?_
  let A := Localization.AtPrime P
  have : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  have : Module.Free A (A ⊗[R] N) := Module.free_of_flat_of_isLocalRing
  simp only [Algebra.linearMap_apply, map_mul, map_pow]
  rw [algebraMap_projectiveDet_tensorProductMap A,
    TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq (funext hM),
    TauCeti.Module.finrank_tensorProduct_eq_of_rankAtStalk_eq (funext hN)]

end LinearMap
