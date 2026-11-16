/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Algebra.Star.Subalgebra
public import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.CStarAlgebra.State.Tracial.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import Mathlib.Analysis.InnerProductSpace.StarOrder
import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The trace kernel, faithfulness, quotient descent, and simplicity

Let `A` be a possibly nonunital C⋆-algebra and let `τ : A →P[ℂ] ℂ` be a positive continuous linear
functional satisfying the trace identity `hτ : ∀ a b : A, τ (a * b) = τ (b * a)`.

Its **trace kernel** `PositiveContinuousLinearMap.traceKernel τ hτ : TwoSidedIdeal A` is the null
set `{a : A | τ (star a * a) = 0}`. For an arbitrary positive functional this set is only a closed
left ideal (the null space of the GNS class map `τ.toPositiveLinearMap.toGNS`); traciality makes it
closed under `star` (`τ (a * star a) = τ (star a * a)`), hence also a right ideal, and equates it
with the kernel of the GNS representation `τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom`
(`PositiveContinuousLinearMap.traceKernel_eq_ker_gnsNonUnitalStarAlgHom`). When `A` is unital it
also agrees with the algebraic multiplication-pairing radical `LinearMap.traceRadical`
(`PositiveContinuousLinearMap.asIdeal_traceKernel_eq_traceRadical`).

For a tracial positive functional `τ : A →P[ℂ] ℂ`, faithfulness
(`PositiveContinuousLinearMap.IsFaithful`) is equivalent to `τ.traceKernel hτ = ⊥` and to
injectivity of `τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom`
(`PositiveContinuousLinearMap.isFaithful_iff_injective_gnsNonUnitalStarAlgHom`). Because the trace
kernel of a tracial state is a proper closed two-sided ideal, every tracial state on a simple
C⋆-algebra (unital or nonunital) is faithful
(`PositiveContinuousLinearMap.IsTracialState.isFaithful_of_isSimple`).

Finally, descending a tracial positive functional along a surjective star homomorphism via
`PositiveContinuousLinearMap.descend` preserves traciality and tracial states, and produces a
faithful functional whenever the homomorphism's kernel is `τ.traceKernel hτ`. Specializing to the
range restriction of the GNS representation and to the quotient map `A →⋆ₙₐ[ℂ] A ⧸ τ.traceKernel hτ`
produces the faithful descended traces `PositiveContinuousLinearMap.gnsRangeTrace` (on `π_τ(A)`)
and `PositiveContinuousLinearMap.quotientTrace`, which are faithful tracial states whenever `τ` is
a tracial state.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Memoirs of the
  American Mathematical Society 184 (2006), no. 865, Proposition 3.5.8.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, §3.3.
-/

public section

open Filter Set Topology
open scoped CStarAlgebra ComplexOrder

namespace PositiveLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **GNS kernel of a tracial positive functional.** When `f : A →ₚ[ℂ] ℂ` satisfies
`f (x * y) = f (y * x)` for all `x, y : A`, its GNS representation kills `a` if and only if
`f (star a * a) = 0`. -/
theorem gnsNonUnitalStarAlgHom_apply_eq_zero_iff (f : A →ₚ[ℂ] ℂ)
    (hf : ∀ x y : A, f (x * y) = f (y * x)) (a : A) :
    f.gnsNonUnitalStarAlgHom a = 0 ↔ f (star a * a) = 0 := by
  refine ⟨f.map_star_mul_self_eq_zero_of_gnsNonUnitalStarAlgHom_eq_zero, fun ha => ?_⟩
  -- Traciality gives `f (a * star a) = f (star a * a) = 0`, so `star a` has zero GNS class;
  -- left multiplication by `star c` then kills `star (a * c) = star c * star a`, and applying
  -- traciality once more gives `f.toGNS (a * c) = 0` for every `c : A`.
  have hstar_a : f.toGNS (star a) = 0 := by
    rw [f.toGNS_eq_zero_iff, star_star, hf a (star a)]
    exact ha
  have hmul (c : A) : f.gnsNonUnitalStarAlgHom a (f.toGNS c) = 0 := by
    have hc : f.toGNS (star c * star a) = 0 := by
      have h1 : f.gnsNonUnitalStarAlgHom (star c) (f.toGNS (star a)) = 0 := by
        rw [hstar_a, map_zero]
      simpa [toGNS_apply] using h1
    have hca : f (star (a * c) * (a * c)) = 0 := by
      have hc0 := (f.toGNS_eq_zero_iff (star c * star a)).mp hc
      rwa [← star_mul a c, star_star, hf (a * c) (star (a * c))] at hc0
    have hac : f.toGNS (a * c) = 0 := (f.toGNS_eq_zero_iff (a * c)).mpr hca
    simpa [toGNS_apply] using hac
  ext ξ
  refine f.denseRange_toGNS.induction_on ξ ?_ hmul
  exact isClosed_eq (by fun_prop) continuous_const

/-- The closed C⋆-subalgebra image `f.gnsNonUnitalStarAlgHom.range` inherits `StarOrderedRing` from
`f.GNS →L[ℂ] f.GNS`. -/
instance instStarOrderedRingRangeGNSNonUnitalStarAlgHom (f : A →ₚ[ℂ] ℂ) :
    StarOrderedRing f.gnsNonUnitalStarAlgHom.range :=
  Subtype.starOrderedRing (𝕜 := ℂ) f.gnsNonUnitalStarAlgHom.range

end PositiveLinearMap

namespace PositiveContinuousLinearMap

/-! ### Faithfulness and the closed trace kernel -/

section TraceKernel

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Faithfulness and GNS injectivity for traces.** A tracial positive functional `τ : A →P[ℂ] ℂ`
is faithful if and only if its GNS representation `τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom` is
injective. -/
theorem isFaithful_iff_injective_gnsNonUnitalStarAlgHom {τ : A →P[ℂ] ℂ}
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.IsFaithful ↔ Function.Injective τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom := by
  refine ⟨IsFaithful.gnsNonUnitalStarAlgHom_injective,
    fun hinj => isFaithful_iff.mpr fun a ha => ?_⟩
  apply hinj
  rw [map_zero]
  exact (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ a).mpr ha

/-- **The trace kernel `N_τ`.** For a positive continuous linear functional `τ : A →P[ℂ] ℂ`
satisfying `hτ : ∀ a b : A, τ (a * b) = τ (b * a)`, `τ.traceKernel hτ` is the closed two-sided ideal
`{a : A | τ (star a * a) = 0}`. -/
def traceKernel (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) : TwoSidedIdeal A :=
  have hker (a : A) : τ (star a * a) = 0 ↔ τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a = 0 :=
    (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ a).symm
  TwoSidedIdeal.mk' {a : A | τ (star a * a) = 0}
    (by simp)
    (fun {x y} hx hy => by
      change τ _ = 0 at hx hy ⊢
      rw [hker] at hx hy ⊢
      rw [map_add, hx, hy, add_zero])
    (fun {x} hx => by simpa using hx)
    (fun {x y} hy => by
      change τ _ = 0 at hy ⊢
      rw [hker] at hy ⊢
      rw [map_mul, hy, mul_zero])
    (fun {x y} hx => by
      change τ _ = 0 at hx ⊢
      rw [hker] at hx ⊢
      rw [map_mul, hx, zero_mul])

/-- Membership in `τ.traceKernel hτ` is `τ (star a * a) = 0`. -/
@[simp]
theorem mem_traceKernel (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) {a : A} :
    a ∈ τ.traceKernel hτ ↔ τ (star a * a) = 0 := by
  unfold traceKernel
  exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ a

/-- The trace kernel of a tracial positive continuous linear functional is norm-closed. -/
instance isClosed_traceKernel (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    IsClosed (τ.traceKernel hτ : Set A) := by
  have hcoe : (τ.traceKernel hτ : Set A) = {a : A | τ (star a * a) = 0} :=
    Set.ext fun _ => τ.mem_traceKernel hτ
  rw [hcoe]
  exact isClosed_eq ((map_continuous τ).comp (continuous_star.mul continuous_id)) continuous_const

/-- **Equality with the GNS kernel.** `τ.traceKernel hτ` is the two-sided ideal kernel of the GNS
representation `τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom`. -/
theorem traceKernel_eq_ker_gnsNonUnitalStarAlgHom (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.traceKernel hτ = TwoSidedIdeal.ker τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom := by
  ext a
  rw [mem_traceKernel, TwoSidedIdeal.mem_ker,
    τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ]
  rfl

/-- Every element in `τ.traceKernel hτ` is annihilated by `τ` itself, even when `A` has no unit. -/
theorem apply_eq_zero_of_mem_traceKernel {τ : A →P[ℂ] ℂ} {hτ : ∀ a b : A, τ (a * b) = τ (b * a)}
    {a : A} (ha : a ∈ τ.traceKernel hτ) : τ a = 0 := by
  -- Use the approximate-unit Cauchy–Schwarz bound `‖τ a‖ ^ 2 ≤ ‖τ‖ * ‖τ (star a * a)‖`.
  have hsq := τ.norm_map_sq_le_opNorm_mul a
  rw [τ.mem_traceKernel hτ] at ha
  rw [ha, norm_zero, mul_zero] at hsq
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _)))

/-- `τ.traceKernel hτ = ⊥` if and only if `τ` is faithful. -/
@[simp]
theorem traceKernel_eq_bot_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.traceKernel hτ = ⊥ ↔ τ.IsFaithful := by
  rw [isFaithful_iff]
  refine ⟨fun h a ha => ?_, fun h => ?_⟩
  · rw [← TwoSidedIdeal.mem_bot, ← h, mem_traceKernel]
    exact ha
  · ext a
    simp only [mem_traceKernel, TwoSidedIdeal.mem_bot]
    exact ⟨h a, fun ha => by simp [ha]⟩

/-- `τ.traceKernel hτ = ⊤` if and only if `τ = 0`. -/
@[simp]
theorem traceKernel_eq_top_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.traceKernel hτ = ⊤ ↔ τ = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · ext a
    have ha : a ∈ (⊤ : TwoSidedIdeal A) := TwoSidedIdeal.mem_top A
    rw [← h] at ha
    exact apply_eq_zero_of_mem_traceKernel ha
  · subst h
    ext a
    simp

/-- The trace kernel of a tracial state is a proper closed two-sided ideal (`N_τ ≠ ⊤`). -/
theorem IsTracialState.traceKernel_ne_top {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState) :
    τ.traceKernel hτ.mul_comm ≠ ⊤ := by
  rw [ne_eq, traceKernel_eq_top_iff]
  exact hτ.ne_zero

/-- **Simplicity implies faithfulness.** On a C⋆-algebra (unital or nonunital) whose only closed
two-sided ideals are `⊥` and `⊤`, every tracial state is faithful. -/
theorem IsTracialState.isFaithful_of_isSimple {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState)
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤) :
    τ.IsFaithful := by
  rw [← τ.traceKernel_eq_bot_iff hτ.mul_comm]
  exact (hsimple (τ.traceKernel hτ.mul_comm) inferInstance).resolve_right hτ.traceKernel_ne_top

end TraceKernel

section UnitalTraceRadical

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- On a unital C⋆-algebra, `τ.traceKernel hτ` viewed as a ring `Ideal` agrees with the algebraic
multiplication-pairing radical `τ.toLinearMap.traceRadical hτ`. -/
theorem asIdeal_traceKernel_eq_traceRadical (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    (τ.traceKernel hτ).asIdeal = τ.toLinearMap.traceRadical hτ := by
  let φ : TauCeti.StarPositiveFunctional A :=
    ⟨τ.toLinearMap, fun a => τ.map_nonneg (star_mul_self_nonneg a)⟩
  ext a
  rw [TwoSidedIdeal.mem_asIdeal, mem_traceKernel]
  exact (φ.mem_traceRadical_iff_apply_star_mul_self_eq_zero hτ a).symm

/-- On a unital C⋆-algebra, converting `τ.toLinearMap.traceRadical hτ` to a `TwoSidedIdeal` recovers
`τ.traceKernel hτ`. -/
theorem toTwoSided_traceRadical_eq_traceKernel (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    (τ.toLinearMap.traceRadical hτ).toTwoSided = τ.traceKernel hτ := by
  ext a
  rw [Ideal.mem_toTwoSided, ← asIdeal_traceKernel_eq_traceRadical, TwoSidedIdeal.mem_asIdeal]

end UnitalTraceRadical

/-! ### Descent along surjective star homomorphisms and faithful quotient traces -/

section Descend

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Descending a tracial positive functional along a surjective star homomorphism preserves the
trace identity. -/
theorem descend_mul_comm (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (x y : B) :
    τ.descend f hf hker (x * y) = τ.descend f hf hker (y * x) := by
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, descend_apply, descend_apply, hτ]

/-- `τ.descend f hf hker` is a tracial state if and only if `τ` is a tracial state. -/
@[simp]
theorem isTracialState_descend_iff (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.descend f hf hker).IsTracialState ↔ τ.IsTracialState := by
  rw [← isTracialState_comp_iff_of_surjective f hf, descend_comp_ofClass]

/-- When the kernel of `f` is `{a : A | τ (star a * a) = 0}`, the descended positive functional
`τ.descend f hf hker` is faithful. -/
theorem isFaithful_descend (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) (hiff : ∀ a : A, f a = 0 ↔ τ (star a * a) = 0) :
    (τ.descend f hf hker).IsFaithful := by
  rw [isFaithful_iff]
  intro y hy
  obtain ⟨a, rfl⟩ := hf y
  rw [← map_star, ← map_mul, descend_apply] at hy
  exact (hiff a).mpr hy

end Descend

section GNSRangeAndQuotient

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The faithful descended trace on the GNS image `π_τ(A)`.** For a tracial positive continuous
linear functional `τ : A →P[ℂ] ℂ`, `τ.gnsRangeTrace hτ` is the positive continuous linear
functional on `τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range` sending `π_τ a` to `τ a`. -/
noncomputable def gnsRangeTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range →P[ℂ] ℂ :=
  τ.descend τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict
    τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict_surjective fun a ha => by
      have ha' : τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a = 0 := congrArg Subtype.val ha
      exact apply_eq_zero_of_mem_traceKernel
        ((τ.mem_traceKernel hτ).mpr
          ((τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ a).mp ha'))

/-- `τ.gnsRangeTrace hτ` evaluates on `π_τ(a)` as `τ a`. -/
@[simp]
theorem gnsRangeTrace_rangeRestrict (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (a : A) :
    τ.gnsRangeTrace hτ (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict a) = τ a :=
  τ.descend_apply τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict _ _ a

/-- Pulling `τ.gnsRangeTrace hτ` back along `π_τ.rangeRestrict` recovers `τ`. -/
@[simp]
theorem gnsRangeTrace_comp_rangeRestrict (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    (τ.gnsRangeTrace hτ).comp
      (.ofClass τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict) = τ := by
  ext a
  exact τ.gnsRangeTrace_rangeRestrict hτ a

/-- `τ.gnsRangeTrace hτ` is tracial. -/
theorem gnsRangeTrace_mul_comm (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (x y : τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range) :
    τ.gnsRangeTrace hτ (x * y) = τ.gnsRangeTrace hτ (y * x) := by
  have aux {ω : τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range → ℂ}
      {f : A → τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range}
      (hf : Function.Surjective f) (hmul : ∀ a b : A, f (a * b) = f a * f b)
      (hω : ∀ a b : A, ω (f (a * b)) = ω (f (b * a))) : ω (x * y) = ω (y * x) := by
    obtain ⟨a, rfl⟩ := hf x
    obtain ⟨b, rfl⟩ := hf y
    rw [← hmul, ← hmul, hω]
  exact aux τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict_surjective
    (fun a b => Subtype.ext (map_mul τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a b))
    fun a b => by rw [gnsRangeTrace_rangeRestrict, gnsRangeTrace_rangeRestrict, hτ]

/-- **Faithfulness on `π_τ(A)`.** `τ.gnsRangeTrace hτ` is always faithful. -/
theorem isFaithful_gnsRangeTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    IsFaithful (A := τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range)
      (τ.gnsRangeTrace hτ) := by
  rw [isFaithful_iff]
  intro y hy
  obtain ⟨a, ha⟩ := τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict_surjective y
  have hstar_mul : star y * y =
      τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict (star a * a) := by
    apply Subtype.ext
    rw [MulMemClass.coe_mul, StarMemClass.coe_star, ← ha]
    change star (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a) *
        τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a =
      τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom (star a * a)
    rw [← map_star, ← map_mul]
  rw [hstar_mul, gnsRangeTrace_rangeRestrict] at hy
  rw [← ha]
  exact Subtype.ext
    ((τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom_apply_eq_zero_iff hτ a).mpr hy)

/-- `τ.gnsRangeTrace hτ` is a tracial state if and only if `τ` is a tracial state. -/
@[simp]
theorem isTracialState_gnsRangeTrace_iff (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    IsTracialState (A := τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range)
      (τ.gnsRangeTrace hτ) ↔ τ.IsTracialState := by
  rw [← isTracialState_comp_iff_of_surjective
      τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict
      τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict_surjective,
    gnsRangeTrace_comp_rangeRestrict]

/-- If `τ` is a tracial state, then `τ.gnsRangeTrace hτ.mul_comm` is a tracial state on `π_τ(A)`. -/
theorem IsTracialState.gnsRangeTrace {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState) :
    IsTracialState (A := τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range)
      (τ.gnsRangeTrace hτ.mul_comm) :=
  (τ.isTracialState_gnsRangeTrace_iff hτ.mul_comm).mpr hτ

/-- **The faithful descended trace on `A ⧸ τ.traceKernel hτ`.** Equipped with its C⋆-algebra order,
the quotient C⋆-algebra `A ⧸ τ.traceKernel hτ` carries the descended positive continuous linear
functional `τ.quotientTrace hτ` satisfying `τ.quotientTrace hτ (mk a) = τ a`. -/
noncomputable def quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (A ⧸ τ.traceKernel hτ) →P[ℂ] ℂ :=
  τ.descend (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))
    (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective (τ.traceKernel hτ)) fun _ ha => by
      rw [TwoSidedIdeal.Quotient.mkStarAlgHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem] at ha
      exact apply_eq_zero_of_mem_traceKernel ha

/-- `τ.quotientTrace hτ` evaluates on a quotient class `mk a` as `τ a`. -/
@[simp]
theorem quotientTrace_mk (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] (a : A) :
    τ.quotientTrace hτ (TwoSidedIdeal.Quotient.mk (τ.traceKernel hτ) a) = τ a := by
  rw [← TwoSidedIdeal.Quotient.mkStarAlgHom_apply]
  exact τ.descend_apply (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _ a

/-- Pulling `τ.quotientTrace hτ` back along `mkStarAlgHom` recovers `τ`. -/
@[simp]
theorem quotientTrace_comp_mkStarAlgHom (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).comp (.ofClass (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))) =
      τ := by
  ext a
  simp

/-- `τ.quotientTrace hτ` has the same operator norm as `τ`. -/
@[simp]
theorem opNorm_quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    ‖(τ.quotientTrace hτ : (A ⧸ τ.traceKernel hτ) →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ := by
  rw [← opNorm_comp_ofClass_of_surjective (τ.quotientTrace hτ)
      (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective (τ.traceKernel hτ)),
    quotientTrace_comp_mkStarAlgHom]

/-- `τ.quotientTrace hτ` is tracial. -/
theorem quotientTrace_mul_comm (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)]
    (x y : A ⧸ τ.traceKernel hτ) :
    τ.quotientTrace hτ (x * y) = τ.quotientTrace hτ (y * x) := by
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (τ.traceKernel hτ) x
  obtain ⟨b, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (τ.traceKernel hτ) y
  rw [← map_mul, ← map_mul, quotientTrace_mk, quotientTrace_mk, hτ]

/-- `τ.quotientTrace hτ` is faithful on `A ⧸ τ.traceKernel hτ`. -/
theorem isFaithful_quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).IsFaithful := by
  rw [isFaithful_iff]
  intro y hy
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (τ.traceKernel hτ) y
  rw [← TwoSidedIdeal.Quotient.mk_star, ← map_mul, quotientTrace_mk, ← mem_traceKernel τ hτ,
    ← TwoSidedIdeal.Quotient.eq_zero_iff_mem] at hy
  exact hy

/-- `τ.quotientTrace hτ` is a tracial state if and only if `τ` is a tracial state. -/
@[simp]
theorem isTracialState_quotientTrace_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).IsTracialState ↔ τ.IsTracialState := by
  rw [← isTracialState_comp_iff_of_surjective
      (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective (τ.traceKernel hτ)),
    quotientTrace_comp_mkStarAlgHom]

/-- If `τ` is a tracial state, then `τ.quotientTrace hτ.mul_comm` is a tracial state on
`A ⧸ τ.traceKernel hτ.mul_comm`. -/
theorem IsTracialState.quotientTrace {τ : A →P[ℂ] ℂ} (hτ : τ.IsTracialState)
    [PartialOrder (A ⧸ τ.traceKernel hτ.mul_comm)]
    [StarOrderedRing (A ⧸ τ.traceKernel hτ.mul_comm)] :
    (τ.quotientTrace hτ.mul_comm).IsTracialState :=
  (τ.isTracialState_quotientTrace_iff hτ.mul_comm).mpr hτ

end GNSRangeAndQuotient

end PositiveContinuousLinearMap
