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
import TauCeti.Analysis.Normed.Module.HahnBanach

/-!
# Extension of states

Every state of a unital C⋆-subalgebra extends to a state of the ambient C⋆-algebra.

* `TauCeti.surjOn_pullbackFunctional_stateSpace`: along an injective unital star homomorphism
  `f : A → B`, restriction of states `pullbackFunctional A f` maps the state space of `B` onto the
  state space of `A`.
* `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`: every state of a closed star
  subalgebra `S` of `A` (containing the unit of `A`) is the restriction of a state of `A`.
* `TauCeti.isExtreme_stateSpace_inter_preimage_pullbackFunctional`: the states of `B` restricting
  along a star homomorphism `f : A → B` to a pure state of `A` form a face of the state space of
  `B`, which is weak-* compact by `TauCeti.isCompact_stateSpace_inter_preimage`.
* `TauCeti.surjOn_pullbackFunctional_extremePoints_stateSpace` and
  `StarSubalgebra.exists_mem_extremePoints_stateSpace_forall_apply_coe_eq`: every pure state
  extends to a pure state.

The proof takes a norm-preserving Hahn–Banach extension of the state along `f`, by
`LinearIsometry.exists_extension_norm_eq`, and reads off that it is a state from its value `1` at
the unit, by `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The extension applies because
an injective star homomorphism of C⋆-algebras is isometric. An extension of a state need not be
pure, multiplicative or unique.

A pure state `φ` of `A` has a pure extension: restriction is a continuous affine map sending the
weak-* compact state space of `B` onto that of `A`, so by Mathlib's `surjOn_extremePoints_image`
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
    IsCompact (stateSpace B ∩ pullbackFunctional A f ⁻¹' {φ}) :=
  isCompact_stateSpace.inter_right <|
    isClosed_singleton.preimage (pullbackFunctional A f).continuous

end Compact

section Face

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **The extensions of a pure state form a face.** Along a star homomorphism `f : A → B` from a
unital C⋆-algebra to a C⋆-algebra, the states of `B` restricting to a pure state `φ` of `A` form an
extreme subset of the state space of `B`. Neither `B` nor `f` need be unital. -/
theorem isExtreme_stateSpace_inter_preimage_pullbackFunctional (f : F) {φ : WeakDual ℂ A}
    (hφ : φ ∈ extremePoints ℝ (stateSpace A)) :
    IsExtreme ℝ (stateSpace B) (stateSpace B ∩ pullbackFunctional A f ⁻¹' {φ}) := by
  refine ⟨inter_subset_left, fun ψ₁ hψ₁ ψ₂ hψ₂ ψ hψ hseg => ⟨hψ₁, ?_⟩⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have hcomb : a • pullbackFunctional A f ψ₁ + b • pullbackFunctional A f ψ₂ = φ := by
    rw [← (hψ.2 : pullbackFunctional A f (a • ψ₁ + b • ψ₂) = φ)]
    exact DFunLike.ext _ _ fun x => by simp
  -- the restriction of a state of `B` has value at most `1` at the unit, and is a state if `1`
  have hres {χ : WeakDual ℂ B} (hχ : χ ∈ stateSpace B) : (χ (f 1)).re ≤ 1 ∧
      ((χ (f 1)).re = 1 → pullbackFunctional A f χ ∈ stateSpace A) := by
    have hpos (x : A) (hx : 0 ≤ x) : 0 ≤ χ (f x) :=
      map_nonneg_of_mem_stateSpace hχ (map_nonneg f hx)
    refine ⟨?_, fun h => mem_stateSpace_iff_map_one.2
      ⟨fun x hx => by simpa using hpos x hx, ?_⟩⟩
    · calc (χ (f 1)).re ≤ ‖χ (f 1)‖ := Complex.re_le_norm _
        _ ≤ ‖f 1‖ := norm_apply_le_of_mem_stateSpace hχ _
        _ ≤ ‖(1 : A)‖ := NonUnitalStarAlgHom.norm_apply_le f 1
        _ ≤ 1 := by nontriviality A; simp
    · rw [pullbackFunctional_apply]
      exact Complex.ext (by simpa using h)
        (by simpa using (Complex.nonneg_iff.1 (hpos 1 zero_le_one)).2.symm)
  obtain ⟨hle₁, hstate₁⟩ := hres hψ₁
  obtain ⟨hle₂, hstate₂⟩ := hres hψ₂
  -- the values at the unit average to `φ 1 = 1`, so both are `1`
  have h1 : a * (ψ₁ (f 1)).re + b * (ψ₂ (f 1)).re = 1 := by
    have := congrArg (fun χ : WeakDual ℂ A => (χ 1).re) hcomb
    simpa [map_one_of_mem_stateSpace hφ.1, real_smul_apply] using this
  exact hφ.2 (hstate₁ (by nlinarith)) (hstate₂ (by nlinarith)) ⟨a, b, ha, hb, hab, hcomb⟩

end Face

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Extension of states.** Along an injective unital star homomorphism `f : A → B` of C⋆-algebras,
every state of `A` is the restriction `φ ∘ f` of a state `φ` of `B`. -/
theorem surjOn_pullbackFunctional_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
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
    SurjOn (pullbackFunctional A f) (extremePoints ℝ (stateSpace B))
      (extremePoints ℝ (stateSpace A)) := by
  have h := surjOn_extremePoints_image
    ((pullbackFunctional A f).restrictScalars ℝ).toContinuousAffineMap
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
  exact ⟨ψ, hψ, fun s => (pullbackFunctional_apply S.subtype ψ s).symm⟩

/-- **Extension of pure states from a C⋆-subalgebra.** Every pure state of a closed star subalgebra
`S` of a unital C⋆-algebra `A`, containing the unit of `A`, is the restriction of a pure state of
`A`. -/
theorem exists_mem_extremePoints_stateSpace_forall_apply_coe_eq (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ extremePoints ℝ (stateSpace S)) :
    ∃ ψ ∈ extremePoints ℝ (stateSpace A), ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ :=
    surjOn_pullbackFunctional_extremePoints_stateSpace S.subtype Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => (pullbackFunctional_apply S.subtype ψ s).symm⟩

end StarSubalgebra
