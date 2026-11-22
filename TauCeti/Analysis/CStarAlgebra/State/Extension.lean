/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# Extension of states

Every state of a unital C⋆-subalgebra extends to a state of the ambient C⋆-algebra.

* `TauCeti.surjOn_pullbackFunctional_stateSpace`: along an injective unital star homomorphism
  `f : A → B`, restriction of states along `(PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B)`
  maps the state space of `B` onto the state space of `A`.
* `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`: every state of a closed star
  subalgebra `S` of `A` (containing the unit of `A`) is the restriction of a state of `A`.
* `TauCeti.isExtreme_stateSpace_inter_preimage_pullbackFunctional`: the states of `B` restricting
  along a star homomorphism `f : A → B` to a pure state of `A` form a face of the state space of
  `B`; neither `A`, `B` nor `f` need be unital. When `B` is unital this face is weak-* compact, by
  `TauCeti.isCompact_stateSpace_inter_preimage`.
* `TauCeti.surjOn_pullbackFunctional_extremePoints_stateSpace` and
  `StarSubalgebra.exists_mem_extremePoints_stateSpace_forall_apply_coe_eq`: along an injective
  unital star homomorphism of unital C⋆-algebras, and in particular for a closed unital star
  subalgebra, every pure state extends to a pure state.

The proof takes a norm-preserving Hahn–Banach extension of the state along `f`, by
`LinearIsometry.exists_extension_norm_eq`, and reads off that it is a state from its value `1` at
the unit, by `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The extension applies because
an injective star homomorphism of C⋆-algebras is isometric. An extension of a state need not be
pure, multiplicative or unique.

For an injective unital star homomorphism `f : A → B` of unital C⋆-algebras, a pure state `φ` of
`A` has a pure extension: restriction is a continuous affine map sending the weak-* compact state
space of `B` onto that of `A`, so by Mathlib's `surjOn_extremePoints_image`
(a consequence of the Krein–Milman lemma) every extreme point of the image is the image of an
extreme point. Equivalently, the extensions of `φ` form a nonempty weak-* compact face of the
state space of `B`, whose extreme points are extreme points of the whole state space.

Pure states are the extreme points `extremePoints ℝ (stateSpace A)` of the state space.

## References

* B. Blackadar, *Operator Algebras*, II.6.3.1 and II.6.3.2.
-/

public section

open Set WeakDual
open scoped ComplexOrder

namespace TauCeti

section Compact

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- The states of `B` restricting along `f` to a given functional `φ` of `A` form a weak-* compact
set. -/
theorem isCompact_stateSpace_inter_preimage (f : F) (φ : WeakDual ℂ A) :
    IsCompact (stateSpace B ∩
      (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional ⁻¹' {φ}) :=
  isCompact_stateSpace.inter_right <| isClosed_singleton.preimage
    (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional.continuous

end Compact

section Face

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **The extensions of a pure state form a face.** Along a star homomorphism `f : A → B` of
C⋆-algebras, the states of `B` restricting to a pure state `φ` of `A` form an extreme subset of the
state space of `B`. Neither `A`, `B` nor `f` need be unital. -/
theorem isExtreme_stateSpace_inter_preimage_pullbackFunctional (f : F) {φ : WeakDual ℂ A}
    (hφ : φ ∈ extremePoints ℝ (stateSpace A)) :
    IsExtreme ℝ (stateSpace B) (stateSpace B ∩
      (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional ⁻¹' {φ}) := by
  let T : A →L[ℂ] B := PositiveContinuousLinearMap.ofClass f
  refine ⟨inter_subset_left, fun ψ₁ hψ₁ ψ₂ hψ₂ ψ hψ hseg => ⟨hψ₁, ?_⟩⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have hcomb : a • T.pullbackFunctional ψ₁ + b • T.pullbackFunctional ψ₂ = φ := by
    rw [← (hψ.2 : T.pullbackFunctional (a • ψ₁ + b • ψ₂) = φ)]
    exact DFunLike.ext _ _ fun x => by simp [T]
  -- the restriction of a state of `B` is nonnegative and has norm at most `1`
  have hres {χ : WeakDual ℂ B} (hχ : χ ∈ stateSpace B) :
      (∀ x, 0 ≤ x → 0 ≤ T.pullbackFunctional χ x) ∧
        ‖toStrongDual (T.pullbackFunctional χ)‖ ≤ 1 := by
    refine ⟨fun x hx => ?_, ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_⟩
    · rw [ContinuousLinearMap.pullbackFunctional_apply]
      exact map_nonneg_of_mem_stateSpace hχ (map_nonneg f hx)
    calc ‖toStrongDual (T.pullbackFunctional χ) x‖ = ‖χ (f x)‖ := by
          rw [toStrongDual_apply, ContinuousLinearMap.pullbackFunctional_apply]
          rfl
      _ ≤ ‖f x‖ := norm_apply_le_of_mem_stateSpace hχ _
      _ ≤ ‖x‖ := NonUnitalStarAlgHom.norm_apply_le f x
      _ = 1 * ‖x‖ := (one_mul _).symm
  obtain ⟨hpos₁, hle₁⟩ := hres hψ₁
  obtain ⟨hpos₂, hle₂⟩ := hres hψ₂
  -- the norms of the restrictions average to at least `‖φ‖ = 1`, so both are `1`
  have h1 : 1 ≤ a * ‖toStrongDual (T.pullbackFunctional ψ₁)‖ +
      b * ‖toStrongDual (T.pullbackFunctional ψ₂)‖ := by
    have hsplit : toStrongDual φ = (a : ℂ) • toStrongDual (T.pullbackFunctional ψ₁) +
        (b : ℂ) • toStrongDual (T.pullbackFunctional ψ₂) := by
      rw [← hcomb]
      exact ContinuousLinearMap.ext fun x => by simp
    calc (1 : ℝ) = ‖toStrongDual φ‖ := (norm_toStrongDual_of_mem_stateSpace hφ.1).symm
      _ ≤ _ := hsplit ▸ norm_add_le _ _
      _ = _ := by simp [norm_smul, abs_of_pos ha, abs_of_pos hb]
  exact hφ.2 (mem_stateSpace_iff.2 ⟨hpos₁, by nlinarith⟩)
    (mem_stateSpace_iff.2 ⟨hpos₂, by nlinarith⟩) ⟨a, b, ha, hb, hab, hcomb⟩

end Face

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Extension of states.** Along an injective unital star homomorphism `f : A → B` of C⋆-algebras,
every state of `A` is the restriction `φ ∘ f` of a state `φ` of `B`. -/
theorem surjOn_pullbackFunctional_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional
      (stateSpace B) (stateSpace A) := by
  intro φ hφ
  let i : A →ₗᵢ[ℂ] B := ⟨(f : A →ₗ[ℂ] B), NonUnitalStarAlgHom.norm_map f hf⟩
  obtain ⟨ψ, hψ, hnorm⟩ := i.exists_extension_norm_eq (toStrongDual φ)
  have hrestrict (a : A) : ψ (f a) = φ a := DFunLike.congr_fun hψ a
  have h1 : ψ 1 = 1 := by
    simpa [map_one f] using (hrestrict 1).trans (map_one_of_mem_stateSpace hφ)
  refine ⟨StrongDual.toWeakDual ψ, mem_stateSpace_iff_norm_eq_one_and_map_one.2
    ⟨hnorm.trans (norm_toStrongDual_of_mem_stateSpace hφ), by simpa⟩,
    DFunLike.ext _ _ fun a => by simpa using hrestrict a⟩

/-- **Extension of pure states.** Along an injective unital star homomorphism `f : A → B` of
C⋆-algebras, every pure state of `A` is the restriction `φ ∘ f` of a pure state `φ` of `B`. -/
theorem surjOn_pullbackFunctional_extremePoints_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional
      (extremePoints ℝ (stateSpace B)) (extremePoints ℝ (stateSpace A)) := by
  have h := surjOn_extremePoints_image
    (((PositiveContinuousLinearMap.ofClass f : A →L[ℂ] B).pullbackFunctional).restrictScalars ℝ
      ).toContinuousAffineMap
    (isCompact_stateSpace (A := B))
  rwa [ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.coe_restrictScalars',
    (surjOn_pullbackFunctional_stateSpace f hf).image_eq_of_mapsTo
      (mapsTo_pullbackFunctional_stateSpace f)] at h

end TauCeti

namespace StarSubalgebra

open TauCeti

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Extension of states from a C⋆-subalgebra.** Every state of a closed star subalgebra `S` of a
unital C⋆-algebra `A`, containing the unit of `A`, is the restriction of a state of `A`. -/
theorem exists_mem_stateSpace_forall_apply_coe_eq (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ stateSpace S) :
    ∃ ψ ∈ stateSpace A, ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ := surjOn_pullbackFunctional_stateSpace S.subtype Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => by simp [ContinuousLinearMap.pullbackFunctional_apply]⟩

/-- **Extension of pure states from a C⋆-subalgebra.** Every pure state of a closed star subalgebra
`S` of a unital C⋆-algebra `A`, containing the unit of `A`, is the restriction of a pure state of
`A`. -/
theorem exists_mem_extremePoints_stateSpace_forall_apply_coe_eq (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ extremePoints ℝ (stateSpace S)) :
    ∃ ψ ∈ extremePoints ℝ (stateSpace A), ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ :=
    surjOn_pullbackFunctional_extremePoints_stateSpace S.subtype Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => by simp [ContinuousLinearMap.pullbackFunctional_apply]⟩

end StarSubalgebra
