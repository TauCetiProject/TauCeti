/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.CStarAlgebra.State.Tracial
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import TauCeti.Algebra.Star.Subalgebra

/-!
# The trace kernel and faithful quotient descent of a tracial positive functional

For a positive functional `τ` on a possibly nonunital C⋆-algebra `A` with
`τ (a * b) = τ (b * a)`, the *trace kernel* is `N_τ = {a | τ (star a * a) = 0}`. For an
arbitrary positive functional this set is only a closed left ideal; traciality makes it
closed under `star`, since `τ (star a * a) = τ (a * star a)`, and hence a closed two-sided
ideal. It is the kernel of the GNS representation of `τ`, and for unital `A` it is the
algebraic trace radical `LinearMap.traceRadical` of `τ`.

A positive functional is *faithful* (`PositiveContinuousLinearMap.IsFaithfulTrace`) when
`τ (star a * a) = 0` only for `a = 0`, equivalently when no nonzero nonnegative element maps
to `0` (`PositiveContinuousLinearMap.isFaithfulTrace_iff_eq_zero_of_nonneg`) or when strictly
positive elements map to strictly positive scalars
(`PositiveContinuousLinearMap.isFaithfulTrace_iff_map_pos`). For a tracial one this means that
the trace kernel is zero, equivalently that the GNS representation is injective. Faithfulness
pulls back along injective star homomorphisms and restricts to closed star subalgebras, and
every tracial state of a C⋆-algebra without nontrivial closed two-sided ideals is faithful,
because the trace kernel of a nonzero functional is a proper closed ideal.

Finally, lifting a positive functional along a surjective star homomorphism via
`PositiveContinuousLinearMap.liftOfSurjective` produces a faithful functional exactly when the
homomorphism kills `{a | τ (star a * a) = 0}` (`isFaithfulTrace_liftOfSurjective_iff`).
Specializing to the range restriction of the GNS representation and to the quotient map
`A →⋆ₙₐ[ℂ] A ⧸ τ.traceKernel hτ` yields the faithful descended traces
`PositiveContinuousLinearMap.gnsRangeTrace` (on `π_τ(A)`) and
`PositiveContinuousLinearMap.quotientTrace` (on `A ⧸ τ.traceKernel hτ`), which are faithful
tracial states whenever `τ` is a tracial state.

## Main declarations

* `PositiveContinuousLinearMap.traceKernel`: the trace kernel `N_τ` as a `TwoSidedIdeal`,
  closed (`PositiveContinuousLinearMap.isClosed_traceKernel`) and stable under `star`.
* `PositiveContinuousLinearMap.mem_traceKernel_iff_forall_map_mul_eq_zero`: `a ∈ N_τ` iff
  `τ (a * b) = 0` for every `b`; for unital `A` this identifies `N_τ` with the trace radical
  (`PositiveContinuousLinearMap.asIdeal_traceKernel`,
  `PositiveContinuousLinearMap.toTwoSided_traceRadical`).
* `PositiveContinuousLinearMap.traceKernel_eq_ker_gnsNonUnitalStarAlgHom`: `N_τ = ker π_τ`.
* `PositiveContinuousLinearMap.traceKernel_eq_top_iff`: `N_τ = A` only for `τ = 0`.
* `PositiveContinuousLinearMap.isFaithfulTrace_iff_eq_zero_of_nonneg`,
  `PositiveContinuousLinearMap.isFaithfulTrace_iff_map_pos`,
  `PositiveContinuousLinearMap.isFaithfulTrace_iff_traceKernel_eq_bot`, and
  `PositiveContinuousLinearMap.isFaithfulTrace_iff_gnsNonUnitalStarAlgHom_injective`.
* `PositiveContinuousLinearMap.IsTracialState.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top`:
  on a C⋆-algebra whose only closed two-sided ideals are `⊥` and `⊤`, every tracial state is
  faithful (`PositiveContinuousLinearMap.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top`
  for nonzero tracial positive functionals).
* `PositiveContinuousLinearMap.IsFaithfulTrace.comp` and
  `PositiveContinuousLinearMap.IsFaithfulTrace.domRestrict`: faithfulness pulls back along
  injective star homomorphisms and restricts to closed star subalgebras.
* `PositiveContinuousLinearMap.gnsRangeTrace` and `PositiveContinuousLinearMap.quotientTrace`:
  the faithful descended traces on `π_τ(A)` and on `A ⧸ τ.traceKernel hτ`.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), no. 865, Section 3.5 (Proposition 3.5.8).
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

section General

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
    (fun {a b} ha hb => (mem_nullSubmodule_ofPositiveLinearMap_iff τ _).mp <|
      (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).nullSubmodule.add_mem
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ a).mpr ha)
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ b).mpr hb))
    (fun {a} ha => by simpa using ha)
    -- the null space of a positive functional is a left ideal
    (fun {a b} hb => (mem_nullSubmodule_ofPositiveLinearMap_iff τ _).mp <|
      (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).mul_mem_nullSubmodule a
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ b).mpr hb))
    (fun {a b} ha => by
      -- `a * b = star (star b * star a)`, and `N_τ` is a left ideal stable under `star`
      have h := (ofPositiveLinearMap (τ : A →ₚ[ℂ] ℂ)).mul_mem_nullSubmodule (star b)
        ((mem_nullSubmodule_ofPositiveLinearMap_iff τ (star a)).mpr
          ((map_star_mul_self_eq_zero_iff_star τ hτ a).mpr ha))
      rw [mem_nullSubmodule_ofPositiveLinearMap_iff, ← star_mul] at h
      exact (map_star_mul_self_eq_zero_iff_star τ hτ _).mp h)

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
  τ.map_eq_zero_of_map_star_mul_self_eq_zero ((mem_traceKernel_iff τ hτ).mp ha)

/-- An element lies in the trace kernel exactly when `τ (a * b) = 0` for every `b`. The
right-hand side is the trace radical of `τ` as a linear map, see `asIdeal_traceKernel`. -/
theorem mem_traceKernel_iff_forall_map_mul_eq_zero {a : A} :
    a ∈ τ.traceKernel hτ ↔ ∀ b, τ (a * b) = 0 := by
  rw [mem_traceKernel_iff]
  -- the forward direction is the Cauchy–Schwarz inequality
  -- `|τ (b * a)| ^ 2 ≤ τ (b * star b) τ (star a * a)`, the converse takes `b = star a`
  refine ⟨fun ha b => ?_, fun h => by rw [hτ]; exact h (star a)⟩
  have h : τ (b * a) = 0 := by simpa [ha] using PositiveLinearMap.norm_map_star_mul_le τ (star b) a
  rw [hτ, h]

/-- The trace kernel is the kernel of the GNS representation of `τ`. -/
theorem traceKernel_eq_ker_gnsNonUnitalStarAlgHom :
    τ.traceKernel hτ = TwoSidedIdeal.ker (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom := by
  ext a
  rw [TwoSidedIdeal.mem_ker, mem_traceKernel_iff, ← coe_toPositiveLinearMap]
  set f : A →ₚ[ℂ] ℂ := (τ : A →ₚ[ℂ] ℂ)
  refine ⟨fun ha => ?_, f.map_star_mul_self_eq_zero_of_gnsNonUnitalStarAlgHom_eq_zero⟩
  ext1 ξ
  -- `π(a)` vanishes on the dense set of classes `[c] = f.toGNS c` because `N_τ` is a right ideal
  refine congrFun (f.denseRange_toGNS.equalizer (map_continuous (f.gnsNonUnitalStarAlgHom a))
    (map_continuous (0 : f.GNS →L[ℂ] f.GNS)) (funext fun c => ?_)) ξ
  have hac := (τ.traceKernel hτ).mul_mem_right a c ((mem_traceKernel_iff τ hτ).mpr ha)
  rw [mem_traceKernel_iff, ← coe_toPositiveLinearMap, ← f.toGNS_eq_zero_iff] at hac
  simp only [Function.comp_apply, f.gnsNonUnitalStarAlgHom_apply_toGNS, zero_apply]
  exact hac

/-- For a tracial positive functional, the GNS representation kills `a` if and only if
`τ (star a * a) = 0`. -/
theorem gnsNonUnitalStarAlgHom_apply_eq_zero_iff (hτ : ∀ a b, τ (a * b) = τ (b * a)) {a : A} :
    (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom a = 0 ↔ τ (star a * a) = 0 := by
  rw [← TwoSidedIdeal.mem_ker, ← traceKernel_eq_ker_gnsNonUnitalStarAlgHom τ hτ,
    mem_traceKernel_iff]

/-- The trace kernel is all of `A` only for the zero functional. -/
@[simp]
theorem traceKernel_eq_top_iff : τ.traceKernel hτ = ⊤ ↔ τ = 0 := by
  refine ⟨fun h => ext fun a => τ.map_eq_zero_of_mem_traceKernel hτ (by simp [h]), fun h => ?_⟩
  ext a
  simp [h]

end TraceKernel

/-- The trace kernel of a tracial state is a proper closed two-sided ideal (`N_τ ≠ ⊤`). -/
theorem IsTracialState.traceKernel_ne_top {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState) :
    τ.traceKernel hτ.map_mul_comm ≠ ⊤ :=
  (traceKernel_eq_top_iff τ hτ.map_mul_comm).not.mpr hτ.ne_zero

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
  isFaithfulTrace_iff.mp h a ha

/-- A positive functional is faithful exactly when it is strictly positive on `star a * a` for
every `a ≠ 0`. -/
theorem isFaithfulTrace_iff_pos : τ.IsFaithfulTrace ↔ ∀ a ≠ 0, 0 < τ (star a * a) := by
  refine ⟨fun h a ha => (τ.map_nonneg (star_mul_self_nonneg a)).lt_of_ne' fun h0 =>
    ha (h.eq_zero_of_map_star_mul_self_eq_zero h0), fun h => isFaithfulTrace_iff.mpr fun a ha => ?_⟩
  by_contra hne
  exact (h a hne).ne' ha

/-- A positive functional on a C⋆-algebra is faithful if and only if no nonzero nonnegative
element lies in its kernel. -/
theorem isFaithfulTrace_iff_eq_zero_of_nonneg :
    τ.IsFaithfulTrace ↔ ∀ a : A, 0 ≤ a → τ a = 0 → a = 0 := by
  refine ⟨fun hf a ha hτa => ?_,
    fun h => isFaithfulTrace_iff.mpr fun a ha =>
      star_mul_self_eq_zero.mp (h _ (star_mul_self_nonneg a) ha)⟩
  obtain ⟨s, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp ha
  rw [hf.eq_zero_of_map_star_mul_self_eq_zero hτa, mul_zero]

/-- A positive functional on a C⋆-algebra is faithful if and only if it maps strictly positive
elements to strictly positive scalars. -/
theorem isFaithfulTrace_iff_map_pos :
    τ.IsFaithfulTrace ↔ ∀ a : A, 0 < a → 0 < τ a := by
  rw [isFaithfulTrace_iff_eq_zero_of_nonneg]
  refine ⟨fun h a ha => ?_, fun h a ha hτa => ?_⟩
  · exact (τ.map_nonneg ha.le).lt_of_ne' fun h0 => ha.ne' (h a ha.le h0)
  · by_contra hne
    exact (h a (ha.lt_of_ne' hne)).ne' hτa

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
  (isFaithfulTrace_iff_traceKernel_eq_bot hτ).mpr <|
    (hA _ (isClosed_traceKernel τ hτ)).resolve_right ((traceKernel_eq_top_iff τ hτ).not.mpr hτ0)

/-- **Tracial states of simple C⋆-algebras are faithful.** If the only closed two-sided ideals
of `A` are `⊥` and `⊤`, every tracial state of `A` is faithful. -/
theorem IsTracialState.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top
    (hτ : τ.IsTracialState)
    (hA : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤) : τ.IsFaithfulTrace :=
  PositiveContinuousLinearMap.isFaithfulTrace_of_forall_isClosed_eq_bot_or_eq_top hτ.map_mul_comm
    hτ.ne_zero hA

section Pullback

variable {B F : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B] {σ : B →P[ℂ] ℂ}

/-- **Pullback of faithfulness.** A faithful positive functional composed with an injective star
homomorphism is faithful. -/
theorem IsFaithfulTrace.comp (hσ : σ.IsFaithfulTrace) (f : F) (hf : Function.Injective f) :
    (σ.comp (.ofClass f)).IsFaithfulTrace := isFaithfulTrace_iff.mpr fun a ha =>
  hf <| by
    simpa using hσ.eq_zero_of_map_star_mul_self_eq_zero (a := f a) (by simpa [map_star] using ha)

end Pullback

omit [StarOrderedRing A] in
/-- Restricting a faithful positive functional to a closed star subalgebra preserves
faithfulness. -/
theorem IsFaithfulTrace.domRestrict {M : Type*} [SetLike M A] [NonUnitalSubringClass M A]
    [SMulMemClass M ℂ A] [StarMemClass M A] (hτ : τ.IsFaithfulTrace) (s : M)
    [IsClosed (s : Set A)] :
    (τ.domRestrict s).IsFaithfulTrace :=
  isFaithfulTrace_iff.mpr fun _ ha =>
    Subtype.ext (hτ.eq_zero_of_map_star_mul_self_eq_zero (by simpa using ha))

end General

section Unital

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {τ : A →P[ℂ] ℂ}
  (hτ : ∀ a b, τ (a * b) = τ (b * a))

/-- On a unital C⋆-algebra the trace kernel is the algebraic trace radical
`{x | ∀ y, τ (x * y) = 0}` of `τ`. -/
theorem asIdeal_traceKernel :
    (τ.traceKernel hτ).asIdeal = (τ : A →ₗ[ℂ] ℂ).traceRadical hτ := by
  ext a
  simpa using mem_traceKernel_iff_forall_map_mul_eq_zero τ hτ

/-- Converting the algebraic trace radical of `τ` on a unital C⋆-algebra to a `TwoSidedIdeal`
recovers `τ.traceKernel hτ`. -/
theorem toTwoSided_traceRadical :
    ((τ : A →ₗ[ℂ] ℂ).traceRadical hτ).toTwoSided = τ.traceKernel hτ := by
  ext a
  rw [Ideal.mem_toTwoSided, ← asIdeal_traceKernel hτ, TwoSidedIdeal.mem_asIdeal]

end Unital

/-! ### Lifting along surjective star homomorphisms and faithful quotient traces -/

section LiftOfSurjective

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- The lifted positive functional `τ.liftOfSurjective f hf hker` is faithful if and only if `f`
annihilates `{a : A | τ (star a * a) = 0}`. -/
theorem isFaithfulTrace_liftOfSurjective_iff (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.liftOfSurjective f hf hker).IsFaithfulTrace ↔ ∀ a : A, τ (star a * a) = 0 → f a = 0 := by
  rw [isFaithfulTrace_iff]
  refine ⟨fun h a ha => h (f a) ?_, fun h y hy => ?_⟩
  · rw [← map_star, ← map_mul, liftOfSurjective_apply]
    exact ha
  · obtain ⟨a, rfl⟩ := hf y
    rw [← map_star, ← map_mul, liftOfSurjective_apply] at hy
    exact h a hy

/-- When `f` annihilates `{a : A | τ (star a * a) = 0}`, the lifted positive functional
`τ.liftOfSurjective f hf hker` is faithful. -/
theorem isFaithfulTrace_liftOfSurjective (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) (hnull : ∀ a : A, τ (star a * a) = 0 → f a = 0) :
    (τ.liftOfSurjective f hf hker).IsFaithfulTrace :=
  (τ.isFaithfulTrace_liftOfSurjective_iff f hf hker).mpr hnull

end LiftOfSurjective

section GNSRangeAndQuotient

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The faithful descended trace on the GNS image `π_τ(A)`.** For a tracial positive continuous
linear functional `τ : A →P[ℂ] ℂ`, `τ.gnsRangeTrace hτ` is the positive continuous linear
functional on `(τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range` sending `π_τ a` to `τ a`. -/
noncomputable def gnsRangeTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range →P[ℂ] ℂ :=
  τ.liftOfSurjective (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict
    (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict_surjective fun _ ha =>
      τ.map_eq_zero_of_map_star_mul_self_eq_zero
        ((τ.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ).mp (congrArg Subtype.val ha))

/-- `τ.gnsRangeTrace hτ` evaluates on `π_τ(a)` as `τ a`. -/
@[simp]
theorem gnsRangeTrace_rangeRestrict (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a : A) :
    τ.gnsRangeTrace hτ ((τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict a) = τ a :=
  τ.liftOfSurjective_apply (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict _ _ a

/-- Pulling `τ.gnsRangeTrace hτ` back along `π_τ.rangeRestrict` recovers `τ`. -/
@[simp]
theorem gnsRangeTrace_comp_rangeRestrict (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    (τ.gnsRangeTrace hτ).comp
      (.ofClass (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict) = τ :=
  τ.liftOfSurjective_comp_ofClass (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict _ _

/-- **Uniqueness of `gnsRangeTrace`.** A positive functional `ψ` on `π_τ(A)` equals
`τ.gnsRangeTrace hτ` if and only if its pullback along `π_τ.rangeRestrict` equals `τ`. -/
theorem eq_gnsRangeTrace_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    {ψ : (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range →P[ℂ] ℂ} :
    ψ = τ.gnsRangeTrace hτ ↔
      ψ.comp (.ofClass (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict) = τ :=
  τ.eq_liftOfSurjective_iff (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict _ _

/-- `τ.gnsRangeTrace hτ` is tracial. -/
theorem gnsRangeTrace_map_mul_comm (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (x y : (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range) :
    τ.gnsRangeTrace hτ (x * y) = τ.gnsRangeTrace hτ (y * x) :=
  τ.liftOfSurjective_map_mul_comm (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict _ _ hτ x y

/-- **Faithfulness on `π_τ(A)`.** `τ.gnsRangeTrace hτ` is always faithful. -/
theorem isFaithfulTrace_gnsRangeTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    IsFaithfulTrace (A := (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range) (τ.gnsRangeTrace hτ) :=
  τ.isFaithfulTrace_liftOfSurjective (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict _ _
    fun _ ha => Subtype.ext ((τ.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ).mpr ha)

/-- `τ.gnsRangeTrace hτ` is a tracial state if and only if `τ` is a tracial state. -/
@[simp]
theorem isTracialState_gnsRangeTrace_iff (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    IsTracialState (A := (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range)
      (τ.gnsRangeTrace hτ) ↔ τ.IsTracialState :=
  τ.isTracialState_liftOfSurjective_iff
    (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.rangeRestrict _ _

/-- If `τ` is a tracial state, then `τ.gnsRangeTrace hτ.map_mul_comm` is a tracial state on
`π_τ(A)`. -/
theorem IsTracialState.gnsRangeTrace {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState) :
    IsTracialState (A := (τ : A →ₚ[ℂ] ℂ).gnsNonUnitalStarAlgHom.range)
      (τ.gnsRangeTrace hτ.map_mul_comm) :=
  (τ.isTracialState_gnsRangeTrace_iff hτ.map_mul_comm).mpr hτ

/-- **The faithful descended trace on `A ⧸ τ.traceKernel hτ`.** Equipped with its C⋆-algebra order,
the quotient C⋆-algebra `A ⧸ τ.traceKernel hτ` carries the lifted positive continuous linear
functional `τ.quotientTrace hτ` satisfying `τ.quotientTrace hτ (mk a) = τ a`. -/
noncomputable def quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (A ⧸ τ.traceKernel hτ) →P[ℂ] ℂ :=
  τ.liftOfSurjective (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))
    (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective (τ.traceKernel hτ)) fun _ ha => by
      rw [TwoSidedIdeal.Quotient.mkStarAlgHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem] at ha
      exact τ.map_eq_zero_of_mem_traceKernel hτ ha

/-- `τ.quotientTrace hτ` evaluates on a quotient class `mk a` as `τ a`. -/
@[simp]
theorem quotientTrace_mk (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] (a : A) :
    τ.quotientTrace hτ (TwoSidedIdeal.Quotient.mk (τ.traceKernel hτ) a) = τ a := by
  rw [← TwoSidedIdeal.Quotient.mkStarAlgHom_apply]
  exact τ.liftOfSurjective_apply (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _ a

/-- Pulling `τ.quotientTrace hτ` back along `mkStarAlgHom` recovers `τ`. -/
@[simp]
theorem quotientTrace_comp_mkStarAlgHom (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).comp (.ofClass (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))) =
      τ :=
  τ.liftOfSurjective_comp_ofClass (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _

/-- **Uniqueness of `quotientTrace`.** A positive functional `ψ` on `A ⧸ τ.traceKernel hτ` equals
`τ.quotientTrace hτ` if and only if its pullback along `mkStarAlgHom` equals `τ`. -/
theorem eq_quotientTrace_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)]
    {ψ : (A ⧸ τ.traceKernel hτ) →P[ℂ] ℂ} :
    ψ = τ.quotientTrace hτ ↔
      ψ.comp (.ofClass (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))) = τ :=
  τ.eq_liftOfSurjective_iff (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _

/-- `τ.quotientTrace hτ` has the same operator norm as `τ`. -/
@[simp]
theorem opNorm_quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    ‖(τ.quotientTrace hτ : (A ⧸ τ.traceKernel hτ) →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ :=
  τ.opNorm_liftOfSurjective (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _

/-- `τ.quotientTrace hτ` is tracial. -/
theorem quotientTrace_map_mul_comm (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)]
    (x y : A ⧸ τ.traceKernel hτ) :
    τ.quotientTrace hτ (x * y) = τ.quotientTrace hτ (y * x) :=
  τ.liftOfSurjective_map_mul_comm
    (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _ hτ x y

/-- `τ.quotientTrace hτ` is faithful on `A ⧸ τ.traceKernel hτ`. -/
theorem isFaithfulTrace_quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).IsFaithfulTrace :=
  τ.isFaithfulTrace_liftOfSurjective (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _
    fun _ ha => by
      rw [TwoSidedIdeal.Quotient.mkStarAlgHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem,
        mem_traceKernel_iff]
      exact ha

/-- `τ.quotientTrace hτ` is a tracial state if and only if `τ` is a tracial state. -/
@[simp]
theorem isTracialState_quotientTrace_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).IsTracialState ↔ τ.IsTracialState :=
  τ.isTracialState_liftOfSurjective_iff (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _

/-- If `τ` is a tracial state, then `τ.quotientTrace hτ.map_mul_comm` is a tracial state on
`A ⧸ τ.traceKernel hτ.map_mul_comm`. -/
theorem IsTracialState.quotientTrace {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState)
    [PartialOrder (A ⧸ τ.traceKernel hτ.map_mul_comm)]
    [StarOrderedRing (A ⧸ τ.traceKernel hτ.map_mul_comm)] :
    (τ.quotientTrace hτ.map_mul_comm).IsTracialState :=
  (τ.isTracialState_quotientTrace_iff hτ.map_mul_comm).mpr hτ

end GNSRangeAndQuotient

end PositiveContinuousLinearMap
