/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Opposite

/-!
# Linear maps with the precomposition scalar action

`Algebra.PrecompLinearMap R B M` is `Hom_R(B,M)` with scalars acting on the domain.
It uses Mathlib's `DomMulAct` action, restricted along `S → B → Bᵈᵐᵃ`.
The synonym keeps this action distinct from the usual action on the codomain, including when
`M` itself is a `B`-module. Evaluation and conversion to ordinary linear maps are `R`-linear.
-/

public section

namespace Algebra

/-- `R`-linear maps from `B` to `M`, with scalar multiplication by precomposition. The body is
exposed so that its inherited additive structure and function coercion agree definitionally. -/
@[expose]
def PrecompLinearMap (R B M : Type*) [CommSemiring R] [CommSemiring B] [Algebra R B]
    [AddCommGroup M] [Module R M] := B →ₗ[R] M

namespace PrecompLinearMap

variable {R B M : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]
  [AddCommGroup M] [Module R M]

instance : AddCommGroup (PrecompLinearMap R B M) :=
  inferInstanceAs (AddCommGroup (B →ₗ[R] M))
instance : CoeFun (PrecompLinearMap R B M) (fun _ ↦ B → M) :=
  ⟨fun φ c ↦ @DFunLike.coe (B →ₗ[R] M) B (fun _ ↦ M) _ φ c⟩

instance {S : Type*} [CommSemiring S] [Algebra S B] : Module S (PrecompLinearMap R B M) :=
  let f : S →+* Bᵈᵐᵃ := (RingEquiv.toOpposite B).toRingHom.comp (algebraMap S B)
  Module.compHom (B →ₗ[R] M) f

@[ext]
lemma ext {φ ψ : PrecompLinearMap R B M} (h : ∀ c, φ c = ψ c) : φ = ψ := LinearMap.ext h

@[simp] lemma zero_apply (c : B) : (0 : PrecompLinearMap R B M) c = 0 := (rfl)
@[simp] lemma add_apply (φ ψ : PrecompLinearMap R B M) (c : B) :
    (φ + ψ) c = φ c + ψ c := (rfl)

@[simp] lemma smul_apply {S : Type*} [CommSemiring S] [Algebra S B]
    (s : S) (φ : PrecompLinearMap R B M) (c : B) : (s • φ) c = φ (s • c) := by
  exact congrArg (fun b ↦ φ b) (Algebra.smul_def s c).symm

instance {S T : Type*} [CommSemiring S] [CommSemiring T] [Algebra S B] [Algebra T B]
    [SMul S T] [IsScalarTower S T B] : IsScalarTower S T (PrecompLinearMap R B M) :=
  ⟨fun s t φ ↦ ext fun c ↦ by simp only [smul_apply, smul_assoc, smul_comm s t]⟩

/-- Forget the precomposition scalar action. -/
def toLinearMap : PrecompLinearMap R B M →ₗ[R] (B →ₗ[R] M) where
  toFun φ := φ
  map_add' _ _ := (rfl)
  map_smul' r φ := LinearMap.ext fun c ↦ by
    -- Convert only this forgetful map's structure field to evaluation in the synonym.
    change (r • φ : PrecompLinearMap R B M) c = r • φ c
    rw [smul_apply]
    exact (φ : B →ₗ[R] M).map_smul r c

@[simp] lemma toLinearMap_apply (φ : PrecompLinearMap R B M) (c : B) :
    toLinearMap φ c = φ c := (rfl)

/-- Evaluation is linear over the original scalar ring. -/
def eval (c : B) : PrecompLinearMap R B M →ₗ[R] M where
  toFun φ := φ c
  map_add' φ ψ := add_apply φ ψ c
  map_smul' r φ := by
    rw [smul_apply]
    exact (φ : B →ₗ[R] M).map_smul r c

@[simp] lemma eval_apply (c : B) (φ : PrecompLinearMap R B M) : eval c φ = φ c := (rfl)

/-- Regard an ordinary linear map as a precomposition module element. -/
def ofLinearMap (φ : B →ₗ[R] M) : PrecompLinearMap R B M := φ

@[simp] lemma ofLinearMap_apply (φ : B →ₗ[R] M) (c : B) : ofLinearMap φ c = φ c := (rfl)

end PrecompLinearMap
end Algebra
