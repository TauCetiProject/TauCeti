/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Star

/-!
# Non-unital star-algebra homomorphisms and equivalences on `C(X, A)`

Mathlib's `Mathlib.Topology.ContinuousMap.Star` bundles precomposition, postcomposition,
homeomorphism transport, and point evaluation on `C(X, A)` as unital `StarAlgHom`s / `StarAlgEquiv`s
under `[Semiring A]`. For non-unital C⋆-algebras and `C₀`-fibers (cones, suspensions, and mapping
cones), we need the corresponding non-unital `⋆`-algebra homomorphisms (`A →⋆ₙₐ[𝕜] B`) and
`⋆`-equivalences (`A ≃⋆ₐ[𝕜] B`), together with the constant-function `⋆`-homomorphism and currying
`C(X × Y, A) ≃⋆ₐ[𝕜] C(X, C(Y, A))`.

## Main declarations

* `ContinuousMap.instContinuousStar`: continuity of `star` on `C(X, A)` in the compact-open
  topology whenever `A` has a continuous `star`.
* `ContinuousMap.compNonUnitalStarAlgHom'`: precomposition `C(Y, A) →⋆ₙₐ[𝕜] C(X, A)` along
  `f : C(X, Y)`.
* `ContinuousMap.compNonUnitalStarAlgHom`: postcomposition `C(X, A) →⋆ₙₐ[𝕜] C(X, B)` with a
  continuous `φ : A →⋆ₙₐ[𝕜] B`.
* `ContinuousMap.evalNonUnitalStarAlgHom` and `ContinuousMap.constNonUnitalStarAlgHom`: evaluation
  `C(X, A) →⋆ₙₐ[𝕜] A` at `x : X` and constant inclusion `A →⋆ₙₐ[𝕜] C(X, A)`.
* `Homeomorph.compNonUnitalStarAlgEquiv'`: transport `C(Y, A) ≃⋆ₐ[𝕜] C(X, A)` along `X ≃ₜ Y` for
  possibly non-unital `A`.
* `ContinuousMap.curryStarAlgEquiv`: currying `C(X × Y, A) ≃⋆ₐ[𝕜] C(X, C(Y, A))` when `Y` is
  locally compact.
-/

public section

namespace ContinuousMap

section ContinuousStar

variable {X A : Type*} [TopologicalSpace X] [TopologicalSpace A] [Star A] [ContinuousStar A]

instance instContinuousStar : ContinuousStar C(X, A) :=
  ⟨continuous_postcomp starContinuousMap⟩

end ContinuousStar

section Precomposition

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (𝕜 A : Type*) [Monoid 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [Star A] [ContinuousStar A]

/-- Precomposition with `f : C(X, Y)` as a non-unital `⋆`-algebra homomorphism
`C(Y, A) →⋆ₙₐ[𝕜] C(X, A)`. -/
def compNonUnitalStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₙₐ[𝕜] C(X, A) where
  toFun g := g.comp f
  map_smul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem compNonUnitalStarAlgHom'_apply (f : C(X, Y)) (g : C(Y, A)) :
    compNonUnitalStarAlgHom' 𝕜 A f g = g.comp f :=
  (rfl)

@[simp]
theorem compNonUnitalStarAlgHom'_id :
    compNonUnitalStarAlgHom' 𝕜 A (ContinuousMap.id X) = .id 𝕜 C(X, A) :=
  NonUnitalStarAlgHom.ext fun _ => ext fun _ => rfl

theorem compNonUnitalStarAlgHom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compNonUnitalStarAlgHom' 𝕜 A (g.comp f) =
      (compNonUnitalStarAlgHom' 𝕜 A f).comp (compNonUnitalStarAlgHom' 𝕜 A g) :=
  NonUnitalStarAlgHom.ext fun _ => ext fun _ => rfl

end Precomposition

section Postcomposition

variable (X : Type*) {𝕜 A B : Type*} [TopologicalSpace X] [Monoid 𝕜]
variable [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A]
  [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A] [Star A] [ContinuousStar A]
variable [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B]
  [DistribMulAction 𝕜 B] [ContinuousConstSMul 𝕜 B] [Star B] [ContinuousStar B]

/-- Postcomposition with a continuous non-unital `⋆`-algebra homomorphism `φ : A →⋆ₙₐ[𝕜] B` as a
non-unital `⋆`-algebra homomorphism `C(X, A) →⋆ₙₐ[𝕜] C(X, B)`. -/
def compNonUnitalStarAlgHom (φ : A →⋆ₙₐ[𝕜] B) (hφ : Continuous φ) :
    C(X, A) →⋆ₙₐ[𝕜] C(X, B) where
  toFun f := (⟨φ, hφ⟩ : C(A, B)).comp f
  map_smul' r f := ext fun x => map_smul φ r (f x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_star' f := ext fun x => map_star φ (f x)

@[simp]
theorem compNonUnitalStarAlgHom_apply (φ : A →⋆ₙₐ[𝕜] B) (hφ : Continuous φ) (f : C(X, A)) :
    compNonUnitalStarAlgHom X φ hφ f = (⟨φ, hφ⟩ : C(A, B)).comp f :=
  (rfl)

@[simp]
theorem compNonUnitalStarAlgHom_id :
    compNonUnitalStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A) :=
  (rfl)

theorem compNonUnitalStarAlgHom_comp {C : Type*} [TopologicalSpace C]
    [NonUnitalNonAssocSemiring C] [IsTopologicalSemiring C] [DistribMulAction 𝕜 C]
    [ContinuousConstSMul 𝕜 C] [Star C] [ContinuousStar C]
    (φ : A →⋆ₙₐ[𝕜] B) (ψ : B →⋆ₙₐ[𝕜] C) (hφ : Continuous φ) (hψ : Continuous ψ) :
    compNonUnitalStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compNonUnitalStarAlgHom X ψ hψ).comp (compNonUnitalStarAlgHom X φ hφ) :=
  (rfl)

end Postcomposition

section Eval

variable (𝕜 A : Type*) [Monoid 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [Star A] [ContinuousStar A] {X : Type*} [TopologicalSpace X]

/-- Evaluation at `x : X` as a non-unital `⋆`-algebra homomorphism `C(X, A) →⋆ₙₐ[𝕜] A`. -/
def evalNonUnitalStarAlgHom (x : X) : C(X, A) →⋆ₙₐ[𝕜] A where
  toFun f := f x
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem evalNonUnitalStarAlgHom_apply (x : X) (f : C(X, A)) :
    evalNonUnitalStarAlgHom 𝕜 A x f = f x :=
  (rfl)

end Eval

section Const

variable (𝕜 X A : Type*) [TopologicalSpace X] [Monoid 𝕜] [TopologicalSpace A]
  [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A] [DistribMulAction 𝕜 A]
  [ContinuousConstSMul 𝕜 A] [Star A] [ContinuousStar A]

/-- Inclusion of constant maps as a non-unital `⋆`-algebra homomorphism `A →⋆ₙₐ[𝕜] C(X, A)`. -/
def constNonUnitalStarAlgHom : A →⋆ₙₐ[𝕜] C(X, A) where
  toFun := const X
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem constNonUnitalStarAlgHom_apply (a : A) :
    constNonUnitalStarAlgHom 𝕜 X A a = const X a :=
  (rfl)

@[simp]
theorem evalNonUnitalStarAlgHom_comp_constNonUnitalStarAlgHom (x : X) :
    (evalNonUnitalStarAlgHom 𝕜 A x).comp (constNonUnitalStarAlgHom 𝕜 X A) = .id 𝕜 A :=
  (rfl)

@[simp]
theorem compNonUnitalStarAlgHom'_comp_constNonUnitalStarAlgHom {Y : Type*} [TopologicalSpace Y]
    (f : C(X, Y)) :
    (compNonUnitalStarAlgHom' 𝕜 A f).comp (constNonUnitalStarAlgHom 𝕜 Y A) =
      constNonUnitalStarAlgHom 𝕜 X A :=
  (rfl)

end Const

section Curry

variable (𝕜 X Y A : Type*) [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace Y]
  [TopologicalSpace A] [Add A] [ContinuousAdd A] [Mul A] [ContinuousMul A]
  [SMul 𝕜 A] [ContinuousConstSMul 𝕜 A] [Star A] [ContinuousStar A]

/-- Currying `C(X × Y, A) ≃⋆ₐ[𝕜] C(X, C(Y, A))` as a `⋆`-algebra equivalence when `Y` is locally
compact. -/
def curryStarAlgEquiv : C(X × Y, A) ≃⋆ₐ[𝕜] C(X, C(Y, A)) where
  toFun := curry
  invFun := uncurry
  left_inv _ := ext fun ⟨_, _⟩ => rfl
  right_inv _ := ext fun _ => ext fun _ => rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem curryStarAlgEquiv_apply (f : C(X × Y, A)) :
    curryStarAlgEquiv 𝕜 X Y A f = f.curry :=
  (rfl)

@[simp]
theorem curryStarAlgEquiv_symm_apply (g : C(X, C(Y, A))) :
    (curryStarAlgEquiv 𝕜 X Y A).symm g = g.uncurry :=
  (rfl)

end Curry

end ContinuousMap

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (𝕜 A : Type*) [TopologicalSpace A] [Add A] [ContinuousAdd A] [Mul A] [ContinuousMul A]
  [SMul 𝕜 A] [ContinuousConstSMul 𝕜 A] [Star A] [ContinuousStar A]

/-- Precomposition along a homeomorphism `f : X ≃ₜ Y` as a `⋆`-algebra equivalence
`C(Y, A) ≃⋆ₐ[𝕜] C(X, A)` for possibly non-unital `A`. -/
def compNonUnitalStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) where
  toFun g := g.comp (f : C(X, Y))
  invFun g := g.comp (f.symm : C(Y, X))
  left_inv g := by ext y; simp
  right_inv g := by ext x; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem compNonUnitalStarAlgEquiv'_apply (f : X ≃ₜ Y) (g : C(Y, A)) :
    f.compNonUnitalStarAlgEquiv' 𝕜 A g = g.comp (f : C(X, Y)) :=
  (rfl)

@[simp]
theorem compNonUnitalStarAlgEquiv'_symm_apply (f : X ≃ₜ Y) (g : C(X, A)) :
    (f.compNonUnitalStarAlgEquiv' 𝕜 A).symm g = g.comp (f.symm : C(Y, X)) :=
  (rfl)

@[simp]
theorem compNonUnitalStarAlgEquiv'_refl :
    (Homeomorph.refl X).compNonUnitalStarAlgEquiv' 𝕜 A = StarAlgEquiv.refl 𝕜 C(X, A) :=
  StarAlgEquiv.ext fun _ => ContinuousMap.ext fun _ => rfl

theorem compNonUnitalStarAlgEquiv'_symm (f : X ≃ₜ Y) :
    (f.compNonUnitalStarAlgEquiv' 𝕜 A).symm = f.symm.compNonUnitalStarAlgEquiv' 𝕜 A :=
  (rfl)

theorem compNonUnitalStarAlgEquiv'_trans {Z : Type*} [TopologicalSpace Z]
    (f : X ≃ₜ Y) (g : Y ≃ₜ Z) :
    (f.trans g).compNonUnitalStarAlgEquiv' 𝕜 A =
      (g.compNonUnitalStarAlgEquiv' 𝕜 A).trans (f.compNonUnitalStarAlgEquiv' 𝕜 A) :=
  (rfl)

end Homeomorph
