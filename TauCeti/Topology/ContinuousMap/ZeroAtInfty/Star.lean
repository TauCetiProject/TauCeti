/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Star
public import TauCeti.Topology.ContinuousMap.Ideals
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.ExtendByZero

/-!
# Non-unital star-algebra homomorphisms on `C₀(X, A)`

Mathlib defines `ZeroAtInftyContinuousMap.compNonUnitalAlgHom` (`C₀(Y, A) →ₙₐ[𝕜] C₀(X, A)`) along a
cocompact map, and `TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic` provides
`ContinuousMap.liftZeroAtInftyStarAlgEquiv` and `ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv`.
This file supplies the remaining non-unital `⋆`-algebra homomorphisms on `C₀(X, A)` needed for
C⋆-algebras of functions vanishing at infinity:

* `ZeroAtInftyContinuousMap.compNonUnitalStarAlgHom`: precomposition `C₀(Y, A) →⋆ₙₐ[𝕜] C₀(X, A)`
  along a cocompact map `X →co Y`.
* `ZeroAtInftyContinuousMap.evalNonUnitalStarAlgHom`: evaluation `C₀(X, A) →⋆ₙₐ[𝕜] A` at `x : X`.
* `ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom`: postcomposition
  `C₀(X, A) →⋆ₙₐ[𝕜] C₀(X, B)` with a continuous `φ : A →⋆ₙₐ[𝕜] B`.
* `ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom`: extension by zero
  `C₀(X, A) →⋆ₙₐ[𝕜] C₀(Y, A)` along an open embedding `e : X → Y` into an `R₁` space `Y`.
* `ContinuousMap.restrictStarAlgEquivOfNotMemRange`: `⋆`-algebra isomorphism
  `evalKerSubalgebra S A y₀ ≃⋆ₐ[S] C₀(X, A)` for a compact `R₁` space `Y` and an open embedding
  `e : X → Y` omitting only `y₀`.
-/

public section

open Filter Set Topology
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

local notation α " →co " β => CocompactMap α β

section Precomp

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (𝕜 A : Type*) [Monoid 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [StarAddMonoid A] [ContinuousStar A]

/-- Precomposition with a cocompact map `g : X →co Y` as a non-unital `⋆`-algebra homomorphism
`C₀(Y, A) →⋆ₙₐ[𝕜] C₀(X, A)`. -/
def compNonUnitalStarAlgHom (g : X →co Y) : C₀(Y, A) →⋆ₙₐ[𝕜] C₀(X, A) where
  toFun f := f.comp g
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem compNonUnitalStarAlgHom_apply (g : X →co Y) (f : C₀(Y, A)) :
    compNonUnitalStarAlgHom 𝕜 A g f = f.comp g := (rfl)

@[simp] theorem compNonUnitalStarAlgHom_id :
    compNonUnitalStarAlgHom 𝕜 A (CocompactMap.id X) = .id 𝕜 C₀(X, A) :=
  NonUnitalStarAlgHom.ext comp_id

theorem compNonUnitalStarAlgHom_comp (h : Y →co Z) (g : X →co Y) :
    compNonUnitalStarAlgHom 𝕜 A (h.comp g) =
      (compNonUnitalStarAlgHom 𝕜 A g).comp (compNonUnitalStarAlgHom 𝕜 A h) := (rfl)

end Precomp

section Eval

variable {X : Type*} [TopologicalSpace X]
variable (𝕜 A : Type*) [Monoid 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A]
  [StarAddMonoid A] [ContinuousStar A]

/-- Evaluation at `x : X` as a non-unital `⋆`-algebra homomorphism `C₀(X, A) →⋆ₙₐ[𝕜] A`. -/
def evalNonUnitalStarAlgHom (x : X) : C₀(X, A) →⋆ₙₐ[𝕜] A where
  toFun f := f x
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem evalNonUnitalStarAlgHom_apply (x : X) (f : C₀(X, A)) :
    evalNonUnitalStarAlgHom 𝕜 A x f = f x := (rfl)

end Eval

section Postcomp

variable (X : Type*) {𝕜 A B : Type*} [TopologicalSpace X] [Monoid 𝕜]
variable [TopologicalSpace A] [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A]
  [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A] [StarAddMonoid A] [ContinuousStar A]
variable [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B]
  [DistribMulAction 𝕜 B] [ContinuousConstSMul 𝕜 B] [StarAddMonoid B] [ContinuousStar B]

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
    (x : X) : compLeftNonUnitalStarAlgHom X φ hφ f x = φ (f x) := (rfl)

@[simp] theorem compLeftNonUnitalStarAlgHom_id :
    compLeftNonUnitalStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C₀(X, A) :=
  NonUnitalStarAlgHom.ext fun _ => ext fun _ => rfl

theorem compLeftNonUnitalStarAlgHom_comp {C : Type*} [TopologicalSpace C]
    [NonUnitalNonAssocSemiring C] [IsTopologicalSemiring C] [DistribMulAction 𝕜 C]
    [ContinuousConstSMul 𝕜 C] [StarAddMonoid C] [ContinuousStar C]
    (φ : A →⋆ₙₐ[𝕜] B) (ψ : B →⋆ₙₐ[𝕜] C) (hφ : Continuous φ) (hψ : Continuous ψ) :
    compLeftNonUnitalStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compLeftNonUnitalStarAlgHom X ψ hψ).comp (compLeftNonUnitalStarAlgHom X φ hφ) :=
  NonUnitalStarAlgHom.ext fun _ => ext fun _ => rfl

end Postcomp

section ExtendByZero

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y] {e : X → Y}
variable (𝕜 A : Type*) [Monoid 𝕜] [TopologicalSpace A] [NonUnitalNonAssocSemiring A]
  [IsTopologicalSemiring A] [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A]
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

@[simp] theorem coe_extendByZeroNonUnitalStarAlgHom (he : IsOpenEmbedding e) :
    ⇑(extendByZeroNonUnitalStarAlgHom 𝕜 A he) = extendByZero he := (rfl)

end ExtendByZero

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section RestrictOfNotMemRange

variable {X Y S A E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [R1Space Y]

variable (S A) in
/-- Restriction along an open embedding `e : X → Y` into a compact `R₁` space omitting only `y₀`
is a `⋆`-algebra isomorphism from `evalKerSubalgebra S A y₀` onto `C₀(X, A)`, with inverse given by
extension by zero. -/
noncomputable def restrictStarAlgEquivOfNotMemRange [CommSemiring S]
    [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [IsTopologicalSemiring A]
    [StarAddMonoid A] [ContinuousStar A] [Module S A] [ContinuousConstSMul S A]
    {e : X → Y} {y₀ : Y} (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ Set.range e ↔ y = y₀) :
    evalKerSubalgebra S A y₀ ≃⋆ₐ[S] C₀(X, A) where
  toFun F := ZeroAtInftyContinuousMap.restrictOfEqZero he.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty F.val) fun y hy => by
      rw [(hcompl y).mp hy]
      exact mem_evalKerSubalgebra.mp F.property
  invFun g :=
    ⟨(ZeroAtInftyContinuousMap.extendByZero he g).toContinuousMap,
      mem_evalKerSubalgebra.mpr
        (ZeroAtInftyContinuousMap.extendByZero_apply_of_notMem he g ((hcompl y₀).mpr rfl))⟩
  left_inv F := Subtype.ext <| ContinuousMap.ext fun y => by
    simp
  right_inv g := ZeroAtInftyContinuousMap.restrictOfEqZero_extendByZero he g
  map_smul' _ _ := by ext x; simp
  map_add' _ _ := by ext x; simp
  map_mul' _ _ := by ext x; simp
  map_star' _ := by ext x; simp

@[simp]
theorem restrictStarAlgEquivOfNotMemRange_apply [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [TopologicalSpace A] [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A]
    [Module S A] [ContinuousConstSMul S A] {e : X → Y} {y₀ : Y} (he : IsOpenEmbedding e)
    (hcompl : ∀ y, y ∉ Set.range e ↔ y = y₀) (F : evalKerSubalgebra S A y₀) (x : X) :
    restrictStarAlgEquivOfNotMemRange S A he hcompl F x = F.val (e x) := by
  have h : restrictStarAlgEquivOfNotMemRange S A he hcompl F =
      ZeroAtInftyContinuousMap.restrictOfEqZero he.isEmbedding
        (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty F.val)
        (fun y hy => by rw [(hcompl y).mp hy]; exact mem_evalKerSubalgebra.mp F.property) := rfl
  rw [h, ZeroAtInftyContinuousMap.restrictOfEqZero_apply]
  simp

@[simp]
theorem coe_restrictStarAlgEquivOfNotMemRange_symm_apply [CommSemiring S]
    [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [IsTopologicalSemiring A]
    [StarAddMonoid A] [ContinuousStar A] [Module S A] [ContinuousConstSMul S A]
    {e : X → Y} {y₀ : Y} (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ Set.range e ↔ y = y₀)
    (g : C₀(X, A)) :
    ((restrictStarAlgEquivOfNotMemRange S A he hcompl).symm g : C(Y, A)) =
      (ZeroAtInftyContinuousMap.extendByZero he g).toContinuousMap := (rfl)

theorem norm_restrictStarAlgEquivOfNotMemRange [CommRing S] [NonUnitalSeminormedRing E]
    [StarAddMonoid E] [ContinuousStar E] [Module S E] [ContinuousConstSMul S E]
    {e : X → Y} {y₀ : Y} (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ Set.range e ↔ y = y₀)
    (F : evalKerSubalgebra S E y₀) :
    ‖restrictStarAlgEquivOfNotMemRange S E he hcompl F‖ = ‖F‖ := by
  have h : restrictStarAlgEquivOfNotMemRange S E he hcompl F =
      ZeroAtInftyContinuousMap.restrictOfEqZero he.isEmbedding
        (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty F.val)
        (fun y hy => by rw [(hcompl y).mp hy]; exact mem_evalKerSubalgebra.mp F.property) := rfl
  rw [h, ZeroAtInftyContinuousMap.norm_restrictOfEqZero, norm_liftZeroAtInfty]
  rfl

theorem isometry_restrictStarAlgEquivOfNotMemRange [CommSemiring S] [NonUnitalNonAssocSemiring A]
    [PseudoMetricSpace A] [IsTopologicalSemiring A] [StarAddMonoid A] [ContinuousStar A]
    [Module S A] [ContinuousConstSMul S A] {e : X → Y} {y₀ : Y} (he : IsOpenEmbedding e)
    (hcompl : ∀ y, y ∉ Set.range e ↔ y = y₀) :
    Isometry (restrictStarAlgEquivOfNotMemRange S A he hcompl) :=
  Isometry.of_dist_eq fun F G => by
    have h := (ZeroAtInftyContinuousMap.isometry_extendByZero (β := A) he).dist_eq
      (restrictStarAlgEquivOfNotMemRange S A he hcompl F)
      (restrictStarAlgEquivOfNotMemRange S A he hcompl G)
    rw [← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist,
      ← ZeroAtInftyContinuousMap.dist_toBCF_eq_dist] at h
    have heq (H : evalKerSubalgebra S A y₀) :
        ZeroAtInftyContinuousMap.extendByZero he
            (restrictStarAlgEquivOfNotMemRange S A he hcompl H) =
          ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty H.val :=
      ZeroAtInftyContinuousMap.extendByZero_restrictOfEqZero he _ _
    rw [heq F, heq G] at h
    simpa only [ZeroAtInftyContinuousMap.dist_toBCF_eq_dist,
      isometry_liftZeroAtInfty.dist_eq, Subtype.dist_eq] using h.symm

end RestrictOfNotMemRange

end ContinuousMap
