/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Star
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.ExtendByZero

/-!
# Non-unital star-algebra homomorphisms and equivalences on `C₀(X, A)`

Mathlib defines `ZeroAtInftyContinuousMap.compNonUnitalAlgHom` (`C₀(Y, A) →ₙₐ[𝕜] C₀(X, A)`) along a
cocompact map, and `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty` (`C(X, A) ≃ C₀(X, A)`)
for compact `X`. This file supplies the `⋆`-algebra homomorphisms and equivalences needed for
C⋆-algebras of functions vanishing at infinity:

* `ContinuousMap.liftZeroAtInftyStarAlgEquiv`: for compact `X`, `liftZeroAtInfty` bundled as a
  `⋆`-algebra equivalence `C(X, A) ≃⋆ₐ[𝕜] C₀(X, A)`, together with supremum-norm preservation
  `ContinuousMap.norm_liftZeroAtInfty`.
* `ZeroAtInftyContinuousMap.compNonUnitalStarAlgHom`: precomposition `C₀(Y, A) →⋆ₙₐ[𝕜] C₀(X, A)`
  along a cocompact map `X →co Y`.
* `ZeroAtInftyContinuousMap.evalNonUnitalStarAlgHom`: evaluation `C₀(X, A) →⋆ₙₐ[𝕜] A` at `x : X`.
* `ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom`: postcomposition
  `C₀(X, A) →⋆ₙₐ[𝕜] C₀(X, B)` with a continuous `φ : A →⋆ₙₐ[𝕜] B`.
* `ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv`: reindexing `C₀(X, A) ≃⋆ₐ[𝕜] C₀(Y, A)` along a
  homeomorphism `e : X ≃ₜ Y` (`f ↦ f ∘ e.symm`).
* `ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom`: extension by zero
  `C₀(X, A) →⋆ₙₐ[𝕜] C₀(Y, A)` along an open embedding `e : X → Y` into an `R₁` space `Y`.
-/

public section

open Filter Set Topology
open scoped ZeroAtInfty

namespace ContinuousMap

section LiftZeroAtInfty

@[simp]
theorem norm_liftZeroAtInfty {X E : Type*} [TopologicalSpace X] [CompactSpace X]
    [SeminormedAddCommGroup E] (f : C(X, E)) :
    ‖ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f‖ = ‖f‖ :=
  le_antisymm
    ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg f)).mpr fun x => f.norm_coe_le_norm x)
    ((f.norm_le (norm_nonneg _)).mpr fun x =>
      ZeroAtInftyContinuousMap.norm_coe_le_norm
        (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f) x)

variable (𝕜 X A : Type*) [TopologicalSpace X] [CompactSpace X] [TopologicalSpace A]
  [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A] [SMulZeroClass 𝕜 A]
  [ContinuousConstSMul 𝕜 A] [StarAddMonoid A] [ContinuousStar A]

/-- On a compact space `X`, `liftZeroAtInfty` is a `⋆`-algebra equivalence
`C(X, A) ≃⋆ₐ[𝕜] C₀(X, A)`. -/
def liftZeroAtInftyStarAlgEquiv : C(X, A) ≃⋆ₐ[𝕜] C₀(X, A) where
  __ := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem liftZeroAtInftyStarAlgEquiv_apply (f : C(X, A)) :
    liftZeroAtInftyStarAlgEquiv 𝕜 X A f =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f :=
  (rfl)

@[simp]
theorem liftZeroAtInftyStarAlgEquiv_symm_apply (f : C₀(X, A)) :
    (liftZeroAtInftyStarAlgEquiv 𝕜 X A).symm f = (f : C(X, A)) :=
  (rfl)

end LiftZeroAtInfty

end ContinuousMap

namespace ZeroAtInftyContinuousMap

local notation α " →co " β => CocompactMap α β

section Precomp

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (𝕜 A : Type*) [Semiring 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [Module 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [StarAddMonoid A] [ContinuousStar A]

/-- Precomposition with a cocompact map `g : X →co Y` as a non-unital `⋆`-algebra homomorphism
`C₀(Y, A) →⋆ₙₐ[𝕜] C₀(X, A)`. -/
def compNonUnitalStarAlgHom (g : X →co Y) : C₀(Y, A) →⋆ₙₐ[𝕜] C₀(X, A) where
  __ := compNonUnitalAlgHom g
  map_star' _ := rfl

@[simp]
theorem compNonUnitalStarAlgHom_apply (g : X →co Y) (f : C₀(Y, A)) :
    compNonUnitalStarAlgHom 𝕜 A g f = f.comp g :=
  (rfl)

@[simp]
theorem compNonUnitalStarAlgHom_id :
    compNonUnitalStarAlgHom 𝕜 A (CocompactMap.id X) = .id 𝕜 C₀(X, A) :=
  NonUnitalStarAlgHom.ext comp_id

theorem compNonUnitalStarAlgHom_comp (h : Y →co Z) (g : X →co Y) :
    compNonUnitalStarAlgHom 𝕜 A (h.comp g) =
      (compNonUnitalStarAlgHom 𝕜 A g).comp (compNonUnitalStarAlgHom 𝕜 A h) :=
  (rfl)

end Precomp

section Eval

variable {X : Type*} [TopologicalSpace X]
variable (𝕜 A : Type*) [Semiring 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [Module 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [StarAddMonoid A] [ContinuousStar A]

/-- Evaluation at `x : X` as a non-unital `⋆`-algebra homomorphism `C₀(X, A) →⋆ₙₐ[𝕜] A`. -/
def evalNonUnitalStarAlgHom (x : X) : C₀(X, A) →⋆ₙₐ[𝕜] A where
  toFun f := f x
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem evalNonUnitalStarAlgHom_apply (x : X) (f : C₀(X, A)) :
    evalNonUnitalStarAlgHom 𝕜 A x f = f x :=
  (rfl)

end Eval

section Postcomp

variable (X : Type*) {𝕜 A B : Type*} [TopologicalSpace X] [Semiring 𝕜]
variable [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A]
  [Module 𝕜 A] [ContinuousConstSMul 𝕜 A] [StarAddMonoid A] [ContinuousStar A]
variable [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B]
  [Module 𝕜 B] [ContinuousConstSMul 𝕜 B] [StarAddMonoid B] [ContinuousStar B]

/-- Postcomposition with a continuous `φ : A →⋆ₙₐ[𝕜] B` as a non-unital `⋆`-algebra homomorphism
`C₀(X, A) →⋆ₙₐ[𝕜] C₀(X, B)`. Vanishing at infinity is preserved because `φ 0 = 0` and `φ` is
continuous at `0`. -/
def compLeftNonUnitalStarAlgHom (φ : A →⋆ₙₐ[𝕜] B) (hφ : Continuous φ) :
    C₀(X, A) →⋆ₙₐ[𝕜] C₀(X, B) where
  toFun f :=
    { toFun x := φ (f x)
      continuous_toFun := hφ.comp f.continuous
      zero_at_infty' := by
        simpa only [map_zero, Function.comp_def] using (hφ.tendsto (0 : A)).comp (zero_at_infty f) }
  map_smul' r f := ext fun x => map_smul φ r (f x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_star' f := ext fun x => map_star φ (f x)

@[simp]
theorem compLeftNonUnitalStarAlgHom_apply (φ : A →⋆ₙₐ[𝕜] B) (hφ : Continuous φ) (f : C₀(X, A))
    (x : X) : compLeftNonUnitalStarAlgHom X φ hφ f x = φ (f x) :=
  (rfl)

@[simp]
theorem compLeftNonUnitalStarAlgHom_id :
    compLeftNonUnitalStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C₀(X, A) :=
  NonUnitalStarAlgHom.ext fun _ => ext fun _ => rfl

theorem compLeftNonUnitalStarAlgHom_comp {C : Type*} [TopologicalSpace C]
    [NonUnitalNonAssocSemiring C] [IsTopologicalSemiring C] [Module 𝕜 C]
    [ContinuousConstSMul 𝕜 C] [StarAddMonoid C] [ContinuousStar C]
    (φ : A →⋆ₙₐ[𝕜] B) (ψ : B →⋆ₙₐ[𝕜] C) (hφ : Continuous φ) (hψ : Continuous ψ) :
    compLeftNonUnitalStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compLeftNonUnitalStarAlgHom X ψ hψ).comp (compLeftNonUnitalStarAlgHom X φ hφ) :=
  NonUnitalStarAlgHom.ext fun _ => ext fun _ => rfl

end Postcomp

section CongrLeft

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (𝕜 A : Type*) [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [SMulZeroClass 𝕜 A] [ContinuousConstSMul 𝕜 A] [StarAddMonoid A]
  [ContinuousStar A]

/-- Reindexing along a homeomorphism `e : X ≃ₜ Y` (`f ↦ f ∘ e.symm`) as a `⋆`-algebra equivalence
`C₀(X, A) ≃⋆ₐ[𝕜] C₀(Y, A)`. -/
def congrLeftStarAlgEquiv (e : X ≃ₜ Y) : C₀(X, A) ≃⋆ₐ[𝕜] C₀(Y, A) where
  toFun f := f.comp e.symm.toCocompactMap
  invFun f := f.comp e.toCocompactMap
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem congrLeftStarAlgEquiv_apply (e : X ≃ₜ Y) (f : C₀(X, A)) (y : Y) :
    congrLeftStarAlgEquiv 𝕜 A e f y = f (e.symm y) :=
  (rfl)

@[simp]
theorem congrLeftStarAlgEquiv_symm (e : X ≃ₜ Y) :
    (congrLeftStarAlgEquiv 𝕜 A e).symm = congrLeftStarAlgEquiv 𝕜 A e.symm :=
  (rfl)

@[simp]
theorem congrLeftStarAlgEquiv_refl :
    congrLeftStarAlgEquiv 𝕜 A (Homeomorph.refl X) = StarAlgEquiv.refl 𝕜 C₀(X, A) :=
  (rfl)

theorem congrLeftStarAlgEquiv_trans {Z : Type*} [TopologicalSpace Z] (e : X ≃ₜ Y) (e' : Y ≃ₜ Z) :
    congrLeftStarAlgEquiv 𝕜 A (e.trans e') =
      (congrLeftStarAlgEquiv 𝕜 A e).trans (congrLeftStarAlgEquiv 𝕜 A e') :=
  (rfl)

end CongrLeft

section ExtendByZero

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y] {e : X → Y}
variable (𝕜 A : Type*) [Semiring 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [Module 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [StarAddMonoid A] [ContinuousStar A]

/-- Extension by `0` outside `Set.range e` along an open embedding `e : X → Y` into an `R₁` space
`Y`, bundled as a non-unital `⋆`-algebra homomorphism `C₀(X, A) →⋆ₙₐ[𝕜] C₀(Y, A)`. -/
noncomputable def extendByZeroNonUnitalStarAlgHom (he : IsOpenEmbedding e) :
    C₀(X, A) →⋆ₙₐ[𝕜] C₀(Y, A) where
  toFun := extendByZero he
  map_smul' := extendByZero_smul he
  map_zero' := extendByZero_zero he
  map_add' := extendByZero_add he
  map_mul' := extendByZero_mul he
  map_star' := extendByZero_star he

@[simp]
theorem coe_extendByZeroNonUnitalStarAlgHom (he : IsOpenEmbedding e) :
    ⇑(extendByZeroNonUnitalStarAlgHom 𝕜 A he) = extendByZero he :=
  (rfl)

theorem extendByZeroNonUnitalStarAlgHom_apply_mem (he : IsOpenEmbedding e) (f : C₀(X, A))
    (x : X) : extendByZeroNonUnitalStarAlgHom 𝕜 A he f (e x) = f x :=
  extendByZero_apply_mem he f x

theorem extendByZeroNonUnitalStarAlgHom_apply_of_notMem (he : IsOpenEmbedding e) (f : C₀(X, A))
    {y : Y} (hy : y ∉ range e) : extendByZeroNonUnitalStarAlgHom 𝕜 A he f y = 0 :=
  extendByZero_apply_of_notMem he f hy

theorem extendByZeroNonUnitalStarAlgHom_injective (he : IsOpenEmbedding e) :
    Function.Injective (extendByZeroNonUnitalStarAlgHom 𝕜 A he) :=
  extendByZero_injective he

end ExtendByZero

end ZeroAtInftyContinuousMap
