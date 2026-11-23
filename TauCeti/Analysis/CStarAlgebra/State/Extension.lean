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

Restriction of states along star homomorphisms is functorial, and every state of a C⋆-subalgebra
extends to a state of the ambient C⋆-algebra, with or without units.

* `TauCeti.pullbackFunctional_id` and `TauCeti.pullbackFunctional_comp`: restriction of functionals
  `pullbackFunctional A f` along star homomorphisms is a contravariant functor.
* `TauCeti.mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace`: if the
  restriction of a state along a composite `A → B → C` is a state, so is its restriction to `B`.
* `TauCeti.injOn_pullbackFunctional_inr_stateSpace` and
  `TauCeti.surjOn_pullbackFunctional_inr_stateSpace`: each state of `A` is the restriction of
  exactly one state of the unitization `Unitization ℂ A`. A pure state of `A` comes from a pure
  state of the unitization, `TauCeti.mem_extremePoints_stateSpace_of_pullbackFunctional_inr`, and
  a pure state of the unitization restricting to a state of `A` restricts to a pure state,
  `TauCeti.pullbackFunctional_inr_mem_extremePoints_stateSpace`.
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
state because restriction to `A` does not lower its norm below `‖φ‖ = 1`, and it is pure when the
extension is, because a convex decomposition of it extends to one of the extension.

Pure states are the extreme points `extremePoints ℝ (stateSpace A)` of the state space.

## References

* B. Blackadar, *Operator Algebras*, II.6.3.1 and II.6.3.2.
-/

public section

open Set WeakDual
open scoped ComplexOrder

namespace TauCeti

section Functorial

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

/-- Restriction of functionals along the identity is the identity. -/
@[simp]
theorem pullbackFunctional_id :
    pullbackFunctional A (NonUnitalStarAlgHom.id ℂ A) = ContinuousLinearMap.id ℂ (WeakDual ℂ A) :=
  ContinuousLinearMap.ext fun _ => DFunLike.ext _ _ fun _ => by simp

/-- **Functoriality of restriction.** Restricting along `g.comp f` is restricting along `g` and
then along `f`. -/
theorem pullbackFunctional_comp (g : B →⋆ₙₐ[ℂ] C) (f : A →⋆ₙₐ[ℂ] B) :
    pullbackFunctional A (g.comp f) = (pullbackFunctional A f).comp (pullbackFunctional B g) :=
  ContinuousLinearMap.ext fun _ => DFunLike.ext _ _ fun _ => by simp

end Functorial

section Restriction

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {φ : WeakDual ℂ B}

/-- The restriction of a state along a star homomorphism is nonnegative on nonnegative
elements. -/
theorem map_nonneg_pullbackFunctional_of_mem_stateSpace (f : F) (hφ : φ ∈ stateSpace B) {a : A}
    (ha : 0 ≤ a) : 0 ≤ pullbackFunctional A f φ a := by
  rw [pullbackFunctional_apply]
  exact map_nonneg_of_mem_stateSpace hφ (map_nonneg f ha)

/-- Restriction along a star homomorphism does not increase the norm of a functional. -/
theorem norm_toStrongDual_pullbackFunctional_le (f : F) (φ : WeakDual ℂ B) :
    ‖toStrongDual (pullbackFunctional A f φ)‖ ≤ ‖toStrongDual φ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  calc ‖toStrongDual (pullbackFunctional A f φ) x‖ = ‖toStrongDual φ (f x)‖ := by
        rw [toStrongDual_apply, pullbackFunctional_apply]; rfl
    _ ≤ ‖toStrongDual φ‖ * ‖f x‖ := (toStrongDual φ).le_opNorm _
    _ ≤ ‖toStrongDual φ‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le f x) (norm_nonneg _)

/-- The restriction of a state along a star homomorphism has norm at most `1`. -/
theorem norm_toStrongDual_pullbackFunctional_le_one (f : F) (hφ : φ ∈ stateSpace B) :
    ‖toStrongDual (pullbackFunctional A f φ)‖ ≤ 1 :=
  (norm_toStrongDual_pullbackFunctional_le f φ).trans (norm_toStrongDual_of_mem_stateSpace hφ).le

/-- If the restriction of a state of `C` along a composite `A → B → C` of star homomorphisms is a
state of `A`, then its restriction to `B` is a state of `B`. -/
theorem mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace
    {C G : Type*} [NonUnitalCStarAlgebra C] [PartialOrder C] [StarOrderedRing C]
    [FunLike G B C] [NonUnitalAlgHomClass G ℂ B C] [StarHomClass G B C] (f : F) (g : G)
    {ψ : WeakDual ℂ C} (hψ : ψ ∈ stateSpace C)
    (h : pullbackFunctional A f (pullbackFunctional B g ψ) ∈ stateSpace A) :
    pullbackFunctional B g ψ ∈ stateSpace B := by
  refine mem_stateSpace_iff.2 ⟨fun b hb => map_nonneg_pullbackFunctional_of_mem_stateSpace g hψ hb,
    le_antisymm (norm_toStrongDual_pullbackFunctional_le_one g hψ) ?_⟩
  rw [← norm_toStrongDual_of_mem_stateSpace h]
  exact norm_toStrongDual_pullbackFunctional_le f _

end Restriction

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
  exact hφ.2 (mem_stateSpace_iff.2
      ⟨fun _ hx => map_nonneg_pullbackFunctional_of_mem_stateSpace f hψ₁ hx, by nlinarith⟩)
    (mem_stateSpace_iff.2
      ⟨fun _ hx => map_nonneg_pullbackFunctional_of_mem_stateSpace f hψ₂ hx, by nlinarith⟩)
    ⟨a, b, ha, hb, hab, hcomb⟩

end Face

section Unitization

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- A state of `Unitization ℂ A` is determined by its restriction to `A`: it takes the value
`λ + ψ a` at `λ + a`. -/
theorem injOn_pullbackFunctional_inr_stateSpace :
    InjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A))
      (stateSpace (Unitization ℂ A)) := by
  have key {ψ : WeakDual ℂ (Unitization ℂ A)} (hψ : ψ ∈ stateSpace (Unitization ℂ A))
      (x : Unitization ℂ A) :
      ψ x = x.fst + pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A) ψ x.snd := by
    have hinl : (Unitization.inl x.fst : Unitization ℂ A) = x.fst • 1 := by ext <;> simp
    conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq x]
    rw [map_add, hinl, map_smul, map_one_of_mem_stateSpace hψ, smul_eq_mul, mul_one,
      pullbackFunctional_apply]
    rfl
  intro ψ₁ hψ₁ ψ₂ hψ₂ h
  exact DFunLike.ext _ _ fun x => by rw [key hψ₁, key hψ₂, h]

/-- Every state `φ` of `A` is the restriction of a state of `Unitization ℂ A`, namely
`λ + a ↦ λ + φ a`. -/
theorem surjOn_pullbackFunctional_inr_stateSpace :
    SurjOn (pullbackFunctional A (Unitization.inrNonUnitalStarAlgHom ℂ A))
      (stateSpace (Unitization ℂ A)) (stateSpace A) := by
  intro φ hφ
  let τ : A →P[ℂ] ℂ := .mk₀ (toStrongDual φ) fun _ => map_nonneg_of_mem_stateSpace hφ
  refine ⟨StrongDual.toWeakDual (τ.unitization : Unitization ℂ A →L[ℂ] ℂ), ?_,
    DFunLike.ext _ _ fun a => ?_⟩
  · rw [PositiveContinuousLinearMap.toWeakDual_mem_stateSpace_iff,
      PositiveContinuousLinearMap.norm_unitization]
    exact norm_toStrongDual_of_mem_stateSpace hφ
  · -- `PositiveContinuousLinearMap.mk₀` has no evaluation lemma; `τ` evaluates as `φ`
    rw [pullbackFunctional_apply]
    exact τ.unitization_apply_inr a

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
      injOn_pullbackFunctional_inr_stateSpace hχ hψ (hχφ.trans h.symm))
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
    refine injOn_pullbackFunctional_inr_stateSpace
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
  exact ⟨_, mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace f _ hψ' hφ,
    rfl⟩

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
    (mem_stateSpace_of_pullbackFunctional_pullbackFunctional_mem_stateSpace f _ hψ'.1 hφ.1), rfl⟩

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
