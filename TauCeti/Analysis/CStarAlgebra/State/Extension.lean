/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Space
public import Mathlib.Algebra.Order.Star.Unitization
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.Hom
import TauCeti.Analysis.CStarAlgebra.State.Unitization
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.HahnBanach.Basic

/-!
# Restriction and extension of states

Every state of a C⋆-subalgebra extends to a state of the ambient C⋆-algebra, with or without
units. Functoriality and norm bounds of restriction are in
`TauCeti.Analysis.CStarAlgebra.State.Space`.

* `TauCeti.mem_extremePoints_stateSpace_of_pullbackFunctional_inr`: a state of the unitization
  restricting to a pure state of `A` is pure, and
  `TauCeti.pullbackFunctional_inr_mem_extremePoints_stateSpace`: a pure state of the unitization
  restricting to a state of `A` restricts to a pure state.
* `TauCeti.isExtreme_stateSpace_inter_preimage_pullbackFunctional`: the states of `B` restricting
  along a star homomorphism `f : A → B` to a pure state of `A` form a face of the state space of
  `B`. When `B` is unital this face is weak-* compact, by
  `TauCeti.isCompact_stateSpace_inter_preimage`.
* `TauCeti.surjOn_pullbackFunctional_stateSpace`: along an injective star homomorphism
  `f : A → B`, restriction of states maps the state space of `B` onto the state space of `A`.
  `TauCeti.surjOn_pullbackFunctional_extremePoints_stateSpace`: every pure state of `A` is the
  restriction of a pure state of `B`. Neither `A`, `B` nor `f` need be unital.
* `StarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq`,
  `NonUnitalStarSubalgebra.exists_mem_stateSpace_forall_apply_coe_eq` and their pure-state
  versions: every (pure) state of a closed star subalgebra `S` of `A` is the restriction of a
  (pure) state of `A`. For a nonunital subalgebra neither `S` nor `A` need be unital.

For unital `A` and `B` and a unital `f`, the extension is a norm-preserving Hahn–Banach extension
of the state along `f`, by `LinearIsometry.exists_extension_norm_eq`, which is a state because it
takes the value `1` at the unit, by `TauCeti.mem_stateSpace_iff_norm_eq_one_and_map_one`. The
extension applies because an injective star homomorphism of C⋆-algebras is isometric. A pure state
`φ` of `A` has a pure extension because restriction is a continuous affine map sending the weak-*
compact state space of `B` onto that of `A`, so by Mathlib's `surjOn_extremePoints_image`
(a consequence of the Krein–Milman lemma) every extreme point of the image is the image of an
extreme point. An extension of a state need not be pure, multiplicative or unique.

The general case passes through the unitizations. A state `φ` of `A` is the restriction of the
state `λ + a ↦ λ + φ a` of `Unitization ℂ A`
(`PositiveContinuousLinearMap.unitization`), which is pure when `φ` is, since the states of the
unitization restricting to `φ` form a face with one point. Extend it along the injective unital
star homomorphism `Unitization.starMap f` and restrict the extension to `B`. The restriction is a
state: it is positive with norm at most `1`, and its norm is at least `‖φ‖ = 1` because restricting
it further to `A` gives `φ` and restriction does not increase norms. It is pure when the extension
is, because a convex decomposition of it extends to one of the extension.

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

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **The extensions of a pure state form a face.** Along a star homomorphism `f : A → B` of
C⋆-algebras, the states of `B` restricting to a pure state `φ` of `A` form an extreme subset of the
state space of `B`. Neither `A`, `B` nor `f` need be unital. -/
theorem isExtreme_stateSpace_inter_preimage_pullbackFunctional (f : F) {φ : WeakDual ℂ A}
    (hφ : φ ∈ extremePoints ℝ (stateSpace A)) :
    IsExtreme ℝ (stateSpace B) (stateSpace B ∩ pullbackFunctional A f ⁻¹' {φ}) := by
  refine ⟨inter_subset_left, fun ψ₁ hψ₁ ψ₂ hψ₂ ψ hψ hseg => ⟨hψ₁, ?_⟩⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  have hcomb : a • pullbackFunctional A f ψ₁ + b • pullbackFunctional A f ψ₂ = φ := by
    rw [← (hψ.2 : pullbackFunctional A f (a • ψ₁ + b • ψ₂) = φ)]
    exact DFunLike.ext _ _ fun x => by simp
  have hle₁ := norm_toStrongDual_pullbackFunctional_le_one f hψ₁
  have hle₂ := norm_toStrongDual_pullbackFunctional_le_one f hψ₂
  -- the norms of the restrictions average to at least `‖φ‖ = 1`, so both are `1`
  have h1 : 1 ≤ a * ‖toStrongDual (pullbackFunctional A f ψ₁)‖ +
      b * ‖toStrongDual (pullbackFunctional A f ψ₂)‖ := by
    have hsplit : toStrongDual φ = (a : ℂ) • toStrongDual (pullbackFunctional A f ψ₁) +
        (b : ℂ) • toStrongDual (pullbackFunctional A f ψ₂) := by
      rw [← hcomb]
      exact ContinuousLinearMap.ext fun x => by simp
    calc (1 : ℝ) = ‖toStrongDual φ‖ := (norm_toStrongDual_of_mem_stateSpace hφ.1).symm
      _ ≤ _ := hsplit ▸ norm_add_le _ _
      _ = _ := by simp [norm_smul, abs_of_pos ha, abs_of_pos hb]
  exact hφ.2 ((pullbackFunctional_mem_stateSpace_iff f hψ₁).2 (by nlinarith))
    ((pullbackFunctional_mem_stateSpace_iff f hψ₂).2 (by nlinarith)) ⟨a, b, ha, hb, hab, hcomb⟩

end Face

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state of `Unitization ℂ A` is determined by its restriction to `A`: it takes the value
`λ + ψ a` at `λ + a`. The restriction need not be a state (it may have norm less than one), so
this is not a case of `PositiveContinuousLinearMap.eq_unitization_of_mem_stateSpace`. -/
private theorem injOn_pullbackFunctional_inr_stateSpace_aux :
    InjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A))
      (stateSpace (Unitization ℂ A)) := by
  have key {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A))
      (x : Unitization ℂ A) :
      ψ x = x.fst + pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ x.snd := by
    have hinl : (Unitization.inl x.fst : Unitization ℂ A) = x.fst • 1 := by ext <;> simp
    conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq x, hinl]
    simp [map_one_of_mem_stateSpace hψ]
  intro ψ₁ hψ₁ ψ₂ hψ₂ h
  exact DFunLike.ext _ _ fun x => by rw [key hψ₁, key hψ₂, h]

/-- A state of `Unitization ℂ A` restricting to a pure state of `A` is pure. -/
theorem mem_extremePoints_stateSpace_of_pullbackFunctional_inr {φ : WeakDual ℂ A}
    (hφ : φ ∈ extremePoints ℝ (stateSpace A)) {ψ : WeakDual ℂ (Unitization ℂ A)}
    (hψ : ψ ∈ stateSpace (Unitization ℂ A))
    (h : pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ = φ) :
    ψ ∈ extremePoints ℝ (stateSpace (Unitization ℂ A)) := by
  have hface := isExtreme_stateSpace_inter_preimage_pullbackFunctional
    (B := Unitization ℂ A) (Unitization.inrNonUnitalStarAlgHom ℂ A) hφ
  -- the face of states restricting to `φ` is the single point `ψ`
  have hE : stateSpace (Unitization ℂ A) ∩
      pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ⁻¹' {φ} = {ψ} :=
    Subset.antisymm (fun χ ⟨hχ, hχφ⟩ =>
      injOn_pullbackFunctional_inr_stateSpace_aux hχ hψ (hχφ.trans h.symm))
      (singleton_subset_iff.2 ⟨hψ, h⟩)
  rw [hE] at hface
  exact hface.mem_extremePoints

/-- A pure state of `Unitization ℂ A` whose restriction to `A` is a state restricts to a pure
state of `A`. -/
theorem pullbackFunctional_inr_mem_extremePoints_stateSpace {ψ : WeakDual ℂ (Unitization ℂ A)}
    (hψ : ψ ∈ extremePoints ℝ (stateSpace (Unitization ℂ A)))
    (hψA : pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈ stateSpace A) :
    pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ ∈
      extremePoints ℝ (stateSpace A) := by
  refine ⟨hψA, fun χ₁ hχ₁ χ₂ hχ₂ hseg => ?_⟩
  obtain ⟨χ₁', hχ₁', rfl⟩ := surjOn_pullbackFunctional_inr_stateSpace hχ₁
  obtain ⟨χ₂', hχ₂', rfl⟩ := surjOn_pullbackFunctional_inr_stateSpace hχ₂
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
  -- the combination `a χ₁' + b χ₂'` is a state of the unitization restricting as `ψ` does
  have hψ' : a • χ₁' + b • χ₂' = ψ := by
    refine injOn_pullbackFunctional_inr_stateSpace_aux
      (convex_stateSpace hχ₁' hχ₂' ha.le hb.le hab) hψ.1 ?_
    rw [← hcomb]
    exact DFunLike.ext _ _ fun x => by simp
  rw [hψ.2 hχ₁' hχ₂' ⟨a, b, ha, hb, hab, hψ'⟩]

end Unitization

section Unital

variable {A B F : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [AlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Extension of states along an injective unital star homomorphism of unital C⋆-algebras. -/
private theorem surjOn_pullbackFunctional_stateSpace_of_unital (f : F)
    (hf : Function.Injective f) :
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

/-- Extension of pure states along an injective unital star homomorphism of unital
C⋆-algebras. -/
private theorem surjOn_pullbackFunctional_extremePoints_stateSpace_of_unital (f : F)
    (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (extremePoints ℝ (stateSpace B))
      (extremePoints ℝ (stateSpace A)) := by
  have h := surjOn_extremePoints_image
    ((pullbackFunctional A f).restrictScalars ℝ).toContinuousAffineMap
    (isCompact_stateSpace (A := B))
  rwa [ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearMap.coe_restrictScalars',
    (surjOn_pullbackFunctional_stateSpace_of_unital f hf).image_eq_of_mapsTo
      (mapsTo_pullbackFunctional_stateSpace f)] at h

end Unital

section Extension

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Restricting a state of `Unitization ℂ B` to `B` and then along `f` is restricting it along
`Unitization.starMap f` and then to `A`. -/
private theorem pullbackFunctional_pullbackFunctional_inr (f : F)
    (ψ : WeakDual ℂ (Unitization ℂ B)) :
    pullbackFunctional A f (pullbackFunctional B (Unitization.inrNonUnitalStarAlgHom ℂ B) ψ) =
      pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A)
        (pullbackFunctional (Unitization ℂ A) (Unitization.starMap (.ofClass f : A →⋆ₙₐ[ℂ] B)) ψ) :=
  DFunLike.ext _ _ fun a => by simp

/-- **Extension of states.** Along an injective star homomorphism `f : A → B` of C⋆-algebras,
every state of `A` is the restriction `φ ∘ f` of a state `φ` of `B`. Neither `A`, `B` nor `f` need
be unital. -/
theorem surjOn_pullbackFunctional_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (stateSpace B) (stateSpace A) := by
  intro φ hφ
  obtain ⟨φ', hφ', rfl⟩ := surjOn_pullbackFunctional_inr_stateSpace hφ
  obtain ⟨ψ', hψ', rfl⟩ := surjOn_pullbackFunctional_stateSpace_of_unital
    (Unitization.starMap (.ofClass f : A →⋆ₙₐ[ℂ] B)) (Unitization.starMap_injective hf) hφ'
  rw [← pullbackFunctional_pullbackFunctional_inr] at hφ ⊢
  exact ⟨_,
    pullbackFunctional_mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace f _
      hψ' hφ, rfl⟩

/-- **Extension of pure states.** Along an injective star homomorphism `f : A → B` of C⋆-algebras,
every pure state of `A` is the restriction `φ ∘ f` of a pure state `φ` of `B`. Neither `A`, `B`
nor `f` need be unital. -/
theorem surjOn_pullbackFunctional_extremePoints_stateSpace (f : F) (hf : Function.Injective f) :
    SurjOn (pullbackFunctional A f) (extremePoints ℝ (stateSpace B))
      (extremePoints ℝ (stateSpace A)) := by
  intro φ hφ
  obtain ⟨φ', hφ', rfl⟩ := surjOn_pullbackFunctional_inr_stateSpace hφ.1
  obtain ⟨ψ', hψ', rfl⟩ := surjOn_pullbackFunctional_extremePoints_stateSpace_of_unital
    (Unitization.starMap (.ofClass f : A →⋆ₙₐ[ℂ] B)) (Unitization.starMap_injective hf)
    (mem_extremePoints_stateSpace_of_pullbackFunctional_inr hφ hφ' rfl)
  rw [← pullbackFunctional_pullbackFunctional_inr] at hφ ⊢
  exact ⟨_, pullbackFunctional_inr_mem_extremePoints_stateSpace hψ'
    (pullbackFunctional_mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace f _
      hψ'.1 hφ.1), rfl⟩

end Extension

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

namespace NonUnitalStarSubalgebra

open TauCeti

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Extension of states from a nonunital C⋆-subalgebra.** Every state of a closed star
subalgebra `S` of a C⋆-algebra `A` is the restriction of a state of `A`. Neither `S` nor `A` need
be unital. -/
theorem exists_mem_stateSpace_forall_apply_coe_eq (S : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ stateSpace S) :
    ∃ ψ ∈ stateSpace A, ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ := surjOn_pullbackFunctional_stateSpace
    (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => by simp⟩

/-- **Extension of pure states from a nonunital C⋆-subalgebra.** Every pure state of a closed star
subalgebra `S` of a C⋆-algebra `A` is the restriction of a pure state of `A`. Neither `S` nor `A`
need be unital. -/
theorem exists_mem_extremePoints_stateSpace_forall_apply_coe_eq (S : NonUnitalStarSubalgebra ℂ A)
    [IsClosed (S : Set A)] {φ : WeakDual ℂ S} (hφ : φ ∈ extremePoints ℝ (stateSpace S)) :
    ∃ ψ ∈ extremePoints ℝ (stateSpace A), ∀ s : S, ψ s = φ s := by
  obtain ⟨ψ, hψ, rfl⟩ := surjOn_pullbackFunctional_extremePoints_stateSpace
    (NonUnitalStarSubalgebraClass.subtype S) Subtype.val_injective hφ
  exact ⟨ψ, hψ, fun s => by simp⟩

end NonUnitalStarSubalgebra
