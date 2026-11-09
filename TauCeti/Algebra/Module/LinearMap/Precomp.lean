/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Linear maps with the precomposition scalar action

`TauCeti.Algebra.PrecompLinearMap R B M` is `Hom_R(B,M)` with scalars acting on the domain.
It uses Mathlib's `DomMulAct` action, restricted along `S → B → Bᵈᵐᵃ`.
The wrapper keeps this action distinct from the usual action on the codomain, including when
`M` itself is a `B`-module. Evaluation and conversion to ordinary linear maps are `R`-linear.
-/

public section

namespace TauCeti.Algebra

/-- `R`-linear maps from `B` to `M`, with scalar multiplication by precomposition. -/
structure PrecompLinearMap (R B M : Type*) [CommSemiring R] [CommSemiring B] [Algebra R B]
    [AddCommMonoid M] [Module R M] where
  /-- The underlying linear map. -/
  linearMap : B →ₗ[R] M

namespace PrecompLinearMap

variable {R B M : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]
  [AddCommMonoid M] [Module R M]

/-- The equivalence forgetting the precomposition scalar action. -/
def equivLinearMap : PrecompLinearMap R B M ≃ (B →ₗ[R] M) where
  toFun := PrecompLinearMap.linearMap
  invFun := PrecompLinearMap.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommMonoid (PrecompLinearMap R B M) := by
  exact equivLinearMap.addCommMonoid

instance {R B M : Type*} [CommSemiring R] [CommSemiring B] [Algebra R B]
    [AddCommGroup M] [Module R M] : AddCommGroup (PrecompLinearMap R B M) := by
  exact equivLinearMap.addCommGroup

instance : CoeFun (PrecompLinearMap R B M) (fun _ ↦ B → M) := by
  exact ⟨fun φ ↦ φ.linearMap⟩

instance {S : Type*} [CommSemiring S] [Algebra S B] : Module S (PrecompLinearMap R B M) := by
  let f : S →+* Bᵈᵐᵃ := (RingEquiv.toOpposite B).toRingHom.comp (algebraMap S B)
  letI : Module S (B →ₗ[R] M) := Module.compHom (B →ₗ[R] M) f
  exact AddEquiv.module S { equivLinearMap with map_add' := fun _ _ ↦ by rfl }

@[ext]
lemma ext {φ ψ : PrecompLinearMap R B M} (h : ∀ c, φ c = ψ c) : φ = ψ := by
  apply equivLinearMap.injective
  exact LinearMap.ext h

@[simp] lemma zero_apply (c : B) : (0 : PrecompLinearMap R B M) c = 0 := (rfl)
@[simp] lemma add_apply (φ ψ : PrecompLinearMap R B M) (c : B) :
    (φ + ψ) c = φ c + ψ c := (rfl)

@[simp] lemma smul_apply {S : Type*} [CommSemiring S] [Algebra S B]
    (s : S) (φ : PrecompLinearMap R B M) (c : B) : (s • φ) c = φ (s • c) := by
  -- Unfold the transferred AddEquiv.module action and Module.compHom to compute
  -- the domain action through DomMulAct before applying Algebra.smul_def.
  change φ.linearMap (algebraMap S B s * c) = φ.linearMap (s • c)
  exact congrArg (fun b ↦ φ.linearMap b) (Algebra.smul_def s c).symm

instance {S T : Type*} [CommSemiring S] [CommSemiring T] [Algebra S B] [Algebra T B]
    [SMul S T] [IsScalarTower S T B] : IsScalarTower S T (PrecompLinearMap R B M) :=
  ⟨fun s t φ ↦ ext fun c ↦ by simp only [smul_apply, smul_assoc, smul_comm s t]⟩

/-- Forget the precomposition scalar action. -/
def toLinearMap : PrecompLinearMap R B M →ₗ[R] (B →ₗ[R] M) where
  toFun φ := φ.linearMap
  map_add' _ _ := by rfl
  map_smul' r φ := LinearMap.ext fun c ↦ by
    -- The source scalar action precomposes; the target scalar action acts on the values.
    change (r • φ : PrecompLinearMap R B M) c = r • φ c
    rw [smul_apply]
    exact φ.linearMap.map_smul r c

@[simp] lemma toLinearMap_apply (φ : PrecompLinearMap R B M) (c : B) :
    toLinearMap φ c = φ c := (rfl)

/-- Evaluation is linear over the original scalar ring. -/
def eval (c : B) : PrecompLinearMap R B M →ₗ[R] M where
  toFun φ := φ c
  map_add' φ ψ := add_apply φ ψ c
  map_smul' r φ := by
    rw [smul_apply]
    exact φ.linearMap.map_smul r c

@[simp] lemma eval_apply (c : B) (φ : PrecompLinearMap R B M) : eval c φ = φ c := (rfl)

/-- Regard an ordinary linear map as a precomposition module element. -/
def ofLinearMap (φ : B →ₗ[R] M) : PrecompLinearMap R B M := ⟨φ⟩

@[simp] lemma ofLinearMap_apply (φ : B →ₗ[R] M) (c : B) : ofLinearMap φ c = φ c := (rfl)

/-- Converting to and from ordinary linear maps cancels. -/
@[simp]
lemma toLinearMap_ofLinearMap (φ : B →ₗ[R] M) : toLinearMap (ofLinearMap φ) = φ := (rfl)

/-- Converting from and to ordinary linear maps cancels. -/
@[simp]
lemma ofLinearMap_toLinearMap (φ : PrecompLinearMap R B M) :
    ofLinearMap (toLinearMap φ) = φ := (rfl)

@[simp]
lemma equivLinearMap_apply (φ : PrecompLinearMap R B M) :
    equivLinearMap φ = toLinearMap φ := (rfl)

@[simp]
lemma equivLinearMap_symm_apply (φ : B →ₗ[R] M) :
    equivLinearMap.symm φ = ofLinearMap φ := (rfl)

end PrecompLinearMap
end TauCeti.Algebra
