/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Tracial
public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
public import TauCeti.RingTheory.TraceFunctional.Radical
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# The trace kernel of a tracial positive functional

For a positive functional `τ` on a possibly nonunital C⋆-algebra `A` with
`τ (a * b) = τ (b * a)`, the *trace kernel* is `N_τ = {a | τ (star a * a) = 0}`. For an
arbitrary positive functional this set is only a closed left ideal; traciality makes it
closed under `star`, since `τ (star a * a) = τ (a * star a)`, and hence a closed two-sided
ideal. It is the kernel of the GNS representation of `τ`, and for unital `A` it is the
algebraic trace radical `LinearMap.traceRadical` of `τ`.

A positive functional is *faithful* (`PositiveContinuousLinearMap.IsFaithfulTrace`) when
`τ (star a * a) = 0` only for `a = 0`. For a tracial one this means that the trace kernel is
zero, equivalently that the GNS representation is injective. Faithfulness pulls back along
injective star homomorphisms, and every tracial state of a C⋆-algebra without nontrivial
closed two-sided ideals is faithful, because the trace kernel of a nonzero functional is a
proper closed ideal.

## Main declarations

* `PositiveContinuousLinearMap.traceKernel`: the trace kernel `N_τ` as a `TwoSidedIdeal`,
  closed (`PositiveContinuousLinearMap.isClosed_traceKernel`) and stable under `star`.
* `PositiveContinuousLinearMap.mem_traceKernel_iff_forall_map_mul_eq_zero`: `a ∈ N_τ` iff
  `τ (a * b) = 0` for every `b`; for unital `A` this identifies `N_τ` with the trace radical
  (`PositiveContinuousLinearMap.asIdeal_traceKernel`).
* `PositiveContinuousLinearMap.traceKernel_eq_ker_gnsNonUnitalStarAlgHom`: `N_τ = ker π_τ`.
* `PositiveContinuousLinearMap.traceKernel_eq_top_iff`: `N_τ = A` only for `τ = 0`.
* `PositiveContinuousLinearMap.isFaithfulTrace_iff_traceKernel_eq_bot` and
  `PositiveContinuousLinearMap.isFaithfulTrace_iff_gnsNonUnitalStarAlgHom_injective`.
* `PositiveContinuousLinearMap.IsTracialState.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top`:
  on a C⋆-algebra whose only closed two-sided ideals are `⊥` and `⊤`, every tracial state is
  faithful (`PositiveContinuousLinearMap.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top`
  for nonzero tracial positive functionals).
* `PositiveContinuousLinearMap.IsFaithfulTrace.comp`: faithfulness pulls back along injective
  star homomorphisms.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865, Section 3.5.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open Filter Topology
open scoped ComplexOrder

namespace PositiveContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (τ : A →P[ℂ] ℂ)

omit [StarOrderedRing A] in
/-- For a tracial positive functional, an element has zero square mass exactly when its
adjoint does. -/
private theorem map_star_mul_self_eq_zero_iff_star (hτ : ∀ a b, τ (a * b) = τ (b * a)) (a : A) :
    τ (star (star a) * star a) = 0 ↔ τ (star a * a) = 0 := by
  rw [star_star, hτ]

open TauCeti.StarPositiveFunctional in
/-- The GNS null space of `τ` consists of the elements with `τ (star a * a) = 0`. -/
private theorem mem_nullSubmodule_ofPositiveLinearMap_iff (a : A) :
    a ∈ (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).nullSubmodule ↔ τ (star a * a) = 0 := by
  rw [mem_nullSubmodule_iff_apply_star_mul_self_eq_zero, ofPositiveLinearMap_apply,
    coe_toPositiveLinearMap]

open TauCeti.StarPositiveFunctional in
/-- The **trace kernel** `N_τ = {a | τ (star a * a) = 0}` of a positive functional `τ` with
`τ (a * b) = τ (b * a)`, as a two-sided ideal. It is closed (`isClosed_traceKernel`), stable
under `star` (`star_mem_traceKernel_iff`), and equal to the kernel of the GNS representation
(`traceKernel_eq_ker_gnsNonUnitalStarAlgHom`). Without traciality the set is only a left
ideal: for the vector state `x ↦ x₁₁` on `2 × 2` matrices it contains `e₁₂` but not
`e₁₂ * e₂₁ = e₁₁`. -/
def traceKernel (hτ : ∀ a b, τ (a * b) = τ (b * a)) : TwoSidedIdeal A :=
  .mk' {a | τ (star a * a) = 0} (by simp)
    (fun {a b} ha hb => (mem_nullSubmodule_ofPositiveLinearMap_iff τ _).1 <|
      (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).nullSubmodule.add_mem
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ a).2 ha)
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ b).2 hb))
    (fun {a} ha => by simpa using ha)
    -- the null space of a positive functional is a left ideal
    (fun {a b} hb => (mem_nullSubmodule_ofPositiveLinearMap_iff τ _).1 <|
      (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).mul_mem_nullSubmodule a
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ b).2 hb))
    (fun {a b} ha => by
      -- `a * b = star (star b * star a)`, and `N_τ` is a left ideal stable under `star`
      have h := (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).mul_mem_nullSubmodule (star b)
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ (star a)).2
          ((map_star_mul_self_eq_zero_iff_star τ hτ a).2 ha))
      rw [mem_nullSubmodule_ofPositiveLinearMap_iff, ← star_mul] at h
      exact (map_star_mul_self_eq_zero_iff_star τ hτ _).1 h)

section TraceKernel

variable (hτ : ∀ a b, τ (a * b) = τ (b * a))

/-- Membership in the trace kernel is vanishing of `τ (star a * a)`. -/
@[simp]
theorem mem_traceKernel_iff {a : A} : a ∈ τ.traceKernel hτ ↔ τ (star a * a) = 0 := by
  simp [traceKernel]

/-- The trace kernel is stable under `star`. -/
-- Not a simp lemma: `mem_traceKernel_iff` and traciality already decide membership of `star a`.
theorem star_mem_traceKernel_iff {a : A} :
    star a ∈ τ.traceKernel hτ ↔ a ∈ τ.traceKernel hτ := by
  simp only [mem_traceKernel_iff, map_star_mul_self_eq_zero_iff_star τ hτ]

/-- The trace kernel is closed. -/
instance isClosed_traceKernel : IsClosed (τ.traceKernel hτ : Set A) := by
  have : (τ.traceKernel hτ : Set A) = (fun a => τ (star a * a)) ⁻¹' {0} := by
    ext a
    exact mem_traceKernel_iff τ hτ
  rw [this]
  exact isClosed_singleton.preimage (by fun_prop)

/-- `τ` vanishes on its trace kernel. -/
theorem map_eq_zero_of_mem_traceKernel {a : A} (ha : a ∈ τ.traceKernel hτ) : τ a = 0 :=
  τ.map_eq_zero_of_map_star_mul_self_eq_zero ((mem_traceKernel_iff τ hτ).1 ha)

/-- An element lies in the trace kernel exactly when `τ (a * b) = 0` for every `b`. The
right-hand side is the trace radical of `τ` as a linear map, see `asIdeal_traceKernel`. -/
theorem mem_traceKernel_iff_forall_map_mul_eq_zero {a : A} :
    a ∈ τ.traceKernel hτ ↔ ∀ b, τ (a * b) = 0 := by
  rw [mem_traceKernel_iff]
  -- the forward direction is the Cauchy–Schwarz inequality
  -- `|τ (b * a)| ^ 2 ≤ τ (b * star b) τ (star a * a)`, the converse takes `b = star a`
  refine ⟨fun ha b => ?_, fun h => by rw [hτ]; exact h (star a)⟩
  have h := PositiveLinearMap.norm_map_star_mul_le τ (star b) a
  rw [star_star, ha, norm_zero, Real.sqrt_zero, mul_zero, norm_le_zero_iff] at h
  rw [hτ, h]

/-- The trace kernel is the kernel of the GNS representation of `τ`. -/
theorem traceKernel_eq_ker_gnsNonUnitalStarAlgHom :
    τ.traceKernel hτ = TwoSidedIdeal.ker (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom := by
  ext a
  rw [TwoSidedIdeal.mem_ker, mem_traceKernel_iff, ← coe_toPositiveLinearMap]
  set f : A →ₚ[ℂ] ℂ := (τ : A →ₚ[ℂ] ℂ)
  constructor
  -- one inclusion uses that `N_τ` is a right ideal, the other an approximate unit of `A`
  · intro ha
    ext1 ξ
    -- `π(a)` vanishes on the dense set of classes `[c] = f.toGNS c`
    refine congrFun (f.denseRange_toGNS.equalizer (map_continuous (f.gnsNonUnitalStarAlgHom a))
      (map_continuous (0 : f.GNS →L[ℂ] f.GNS)) (funext fun c => ?_)) ξ
    have hac := (τ.traceKernel hτ).mul_mem_right a c ((mem_traceKernel_iff τ hτ).2 ha)
    rw [mem_traceKernel_iff, ← coe_toPositiveLinearMap, ← f.toGNS_eq_zero_iff] at hac
    simp only [Function.comp_apply, f.gnsNonUnitalStarAlgHom_apply_toGNS, zero_apply]
    exact hac
  · intro ha
    rw [← f.toGNS_eq_zero_iff]
    -- `[a * e] = π(a)[e] = 0` along an approximate unit `e`, and `[a * e] → [a]`
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    refine tendsto_nhds_unique ((f.toGNS.continuous.tendsto a).comp (hl.tendsto_mul_left a))
      (tendsto_const_nhds.congr fun e => ?_)
    simp only [Function.comp_apply, ← f.gnsNonUnitalStarAlgHom_apply_toGNS, ha, zero_apply]

/-- The trace kernel is all of `A` only for the zero functional. -/
theorem traceKernel_eq_top_iff : τ.traceKernel hτ = ⊤ ↔ τ = 0 := by
  refine ⟨fun h => ext fun a => τ.map_eq_zero_of_mem_traceKernel hτ (by simp [h]), fun h => ?_⟩
  ext a
  simp [h]

end TraceKernel

/-- A positive functional `τ` is **faithful** when `τ (star a * a) = 0` only for `a = 0`. For a
tracial functional this says that its trace kernel is zero
(`isFaithfulTrace_iff_traceKernel_eq_bot`), equivalently that its GNS representation is
injective (`isFaithfulTrace_iff_gnsNonUnitalStarAlgHom_injective`). -/
def IsFaithfulTrace : Prop :=
  ∀ a, τ (star a * a) = 0 → a = 0

variable {τ}

omit [StarOrderedRing A] in
/-- A positive functional is faithful when `τ (star a * a) = 0` only for `a = 0`. -/
theorem isFaithfulTrace_iff : τ.IsFaithfulTrace ↔ ∀ a, τ (star a * a) = 0 → a = 0 :=
  Iff.rfl

omit [StarOrderedRing A] in
/-- A faithful positive functional vanishes on `star a * a` only for `a = 0`. -/
theorem IsFaithfulTrace.eq_zero_of_map_star_mul_self_eq_zero (h : τ.IsFaithfulTrace) {a : A}
    (ha : τ (star a * a) = 0) : a = 0 :=
  isFaithfulTrace_iff.1 h a ha

/-- A positive functional is faithful exactly when it is strictly positive on `star a * a` for
every `a ≠ 0`. -/
theorem isFaithfulTrace_iff_pos : τ.IsFaithfulTrace ↔ ∀ a ≠ 0, 0 < τ (star a * a) := by
  refine ⟨fun h a ha => (τ.map_nonneg (star_mul_self_nonneg a)).lt_of_ne' fun h0 =>
    ha (h.eq_zero_of_map_star_mul_self_eq_zero h0), fun h => isFaithfulTrace_iff.2 fun a ha => ?_⟩
  by_contra hne
  exact (h a hne).ne' ha

/-- A tracial positive functional is faithful exactly when its trace kernel is zero. -/
theorem isFaithfulTrace_iff_traceKernel_eq_bot (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    τ.IsFaithfulTrace ↔ τ.traceKernel hτ = ⊥ := by
  simp only [eq_bot_iff, IsConcreteLE.le_iff, mem_traceKernel_iff, TwoSidedIdeal.mem_bot,
    isFaithfulTrace_iff]

/-- A tracial positive functional is faithful exactly when its GNS representation is
injective. Traciality is needed for the converse: the vector state `x ↦ x₁₁` on `2 × 2`
matrices has an injective GNS representation but vanishes at `star e₁₂ * e₁₂ = e₂₂`. -/
theorem isFaithfulTrace_iff_gnsNonUnitalStarAlgHom_injective
    (hτ : ∀ a b, τ (a * b) = τ (b * a)) :
    τ.IsFaithfulTrace ↔ Function.Injective (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom := by
  rw [isFaithfulTrace_iff_traceKernel_eq_bot hτ, traceKernel_eq_ker_gnsNonUnitalStarAlgHom,
    TwoSidedIdeal.ker_eq_bot]

/-- A nonzero tracial positive functional on a C⋆-algebra whose only closed two-sided ideals are
`⊥` and `⊤` is faithful, since its trace kernel is a proper closed ideal. -/
theorem isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (hτ0 : τ ≠ 0)
    (hA : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤) : τ.IsFaithfulTrace :=
  (isFaithfulTrace_iff_traceKernel_eq_bot hτ).2 <|
    (hA _ (isClosed_traceKernel τ hτ)).resolve_right ((traceKernel_eq_top_iff τ hτ).not.2 hτ0)

/-- **Tracial states of simple C⋆-algebras are faithful.** If the only closed two-sided ideals
of `A` are `⊥` and `⊤`, every tracial state of `A` is faithful. -/
theorem IsTracialState.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top
    (hτ : τ.IsTracialState)
    (hA : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤) : τ.IsFaithfulTrace :=
  PositiveContinuousLinearMap.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top hτ.map_mul_comm
    (by rintro rfl; simpa using hτ.norm_eq_one) hA

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- **Pullback of faithfulness.** A faithful positive functional composed with an injective star
homomorphism is faithful. -/
theorem IsFaithfulTrace.comp (hσ : σ.IsFaithfulTrace) (f : F) (hf : Function.Injective f) :
    (σ.comp (.ofClass f)).IsFaithfulTrace := isFaithfulTrace_iff.2 fun a ha =>
  hf <| by
    simpa using hσ.eq_zero_of_map_star_mul_self_eq_zero (a := f a) (by simpa [map_star] using ha)

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {τ : A →P[ℂ] ℂ}
  (hτ : ∀ a b, τ (a * b) = τ (b * a))

/-- On a unital C⋆-algebra the trace kernel is the algebraic trace radical
`{x | ∀ y, τ (x * y) = 0}` of `τ`. -/
theorem asIdeal_traceKernel :
    (τ.traceKernel hτ).asIdeal = (τ : A →ₗ[ℂ] ℂ).traceRadical hτ := by
  ext a
  simpa using mem_traceKernel_iff_forall_map_mul_eq_zero τ hτ

end Unital

end PositiveContinuousLinearMap
