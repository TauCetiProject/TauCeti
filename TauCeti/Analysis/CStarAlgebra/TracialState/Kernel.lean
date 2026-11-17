/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.CStarAlgebra.GNS.Basic
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.CStarAlgebra.TracialState.Basic
public import TauCeti.RingTheory.TraceFunctional.Radical
import TauCeti.Algebra.Star.Subalgebra
import TauCeti.Analysis.CStarAlgebra.GNS.Nondegenerate
import TauCeti.Analysis.CStarAlgebra.PositiveLinearFunctional

/-!
# Trace kernels, faithfulness, and descended traces on C⋆-algebras

For a positive continuous linear functional `τ : A →P[ℂ] ℂ` on a possibly nonunital complex
C⋆-algebra `A`, faithfulness means that `τ (star a * a) = 0` implies `a = 0` (equivalently,
`τ a > 0` for every nonzero `a ≥ 0`, or the GNS class map `τ.toGNS` is injective). When `τ` is
tracial (`∀ a b, τ (a * b) = τ (b * a)`), its null set `N_τ = {a : A | τ (star a * a) = 0}` is a
closed two-sided ideal (`PositiveContinuousLinearMap.traceKernel`), equal to the kernel of the GNS
representation `π_τ` (`PositiveContinuousLinearMap.traceKernel_eq_ker_gnsNonUnitalStarAlgHom`) and,
for unital `A`, to the algebraic trace radical `LinearMap.traceRadical`
(`PositiveContinuousLinearMap.asIdeal_traceKernel`).

Consequently, a tracial positive functional is faithful if and only if its GNS representation is
faithful, and every nonzero tracial functional (in particular every tracial state) on a simple
C⋆-algebra is faithful. Moreover, any positive functional vanishing on the kernel of a surjective
`⋆`-homomorphism `f : A → B` descends uniquely to `B →P[ℂ] ℂ` with the same operator norm
(`PositiveContinuousLinearMap.descend`), yielding faithful descended traces on both the GNS image
`π_τ(A)` (`PositiveContinuousLinearMap.gnsRangeTrace`) and the C⋆-quotient `A ⧸ N_τ`
(`PositiveContinuousLinearMap.quotientTrace`), intertwined by the canonical isometric
`⋆`-isomorphism `A ⧸ N_τ ≃⋆ₐ[ℂ] π_τ(A)`.

## Main declarations

* `PositiveContinuousLinearMap.IsFaithful`: faithfulness of a positive continuous linear functional,
  with characterizations by positivity on nonzero squares
  (`isFaithful_iff_forall_star_mul_self_pos`), positivity on positive elements
  (`isFaithful_iff_forall_nonneg_eq_zero`, `isFaithful_iff_forall_pos`), and injectivity of the GNS
  class map (`isFaithful_iff_toGNS_injective`), together with pullback along injective
  `⋆`-homomorphisms (`IsFaithful.comp_of_injective`, `IsFaithful.comp_ofClass_iff`).
* `PositiveContinuousLinearMap.traceKernel`: the closed two-sided ideal
  `N_τ = {a | τ (star a * a) = 0}` of a tracial positive functional, with `isClosed_traceKernel`,
  `mem_traceKernel_iff_forall_mul_eq_zero`, `traceKernel_eq_ker_gnsNonUnitalStarAlgHom`,
  `traceKernel_ne_top`, `isFaithful_iff_traceKernel_eq_bot`,
  `isFaithful_iff_gnsNonUnitalStarAlgHom_injective`, and unital identifications
  `asIdeal_traceKernel` and `traceKernel_eq_ker_gnsStarAlgHom`.
* `PositiveContinuousLinearMap.isFaithful_of_forall_isClosed_eq_bot_or_top` and
  `PositiveContinuousLinearMap.IsTracialState.isFaithful_of_forall_isClosed_eq_bot_or_top`: every
  nonzero tracial positive functional (in particular every tracial state) on a simple C⋆-algebra is
  faithful.
* `PositiveContinuousLinearMap.descend`, `PositiveContinuousLinearMap.descendRange`,
  `PositiveContinuousLinearMap.gnsRangeTrace`, and `PositiveContinuousLinearMap.quotientTrace`:
  uniqueness, norm preservation, traciality, and faithfulness of descended positive functionals and
  traces, together with `PositiveContinuousLinearMap.quotientTraceKernelEquivGNSRange`.

## References

* N. P. Brown, *Invariant Means and Finite Representation Theory of C*-Algebras*, Mem. Amer. Math.
  Soc. 184 (2006), Proposition 3.5.8.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Academic Press (1990), Sections 3.3 and 3.4.
* G. K. Pedersen, *C*-Algebras and their Automorphism Groups*, second edition (2018), Chapter 5.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace PositiveContinuousLinearMap

section FaithfulBasic

variable {A : Type*} [AddCommMonoid A] [Mul A] [Star A] [PartialOrder A]
  [Module ℂ A] [TopologicalSpace A] {τ : A →P[ℂ] ℂ}

/-- A positive continuous linear functional `τ : A →P[ℂ] ℂ` is *faithful* if
`τ (star a * a) = 0` implies `a = 0`. -/
def IsFaithful (τ : A →P[ℂ] ℂ) : Prop :=
  ∀ a : A, τ (star a * a) = 0 → a = 0

/-- Unfolding faithfulness of a positive continuous linear functional. -/
theorem isFaithful_iff : τ.IsFaithful ↔ ∀ a : A, τ (star a * a) = 0 → a = 0 :=
  Iff.rfl

/-- If `τ` is faithful and `τ (star a * a) = 0`, then `a = 0`. -/
theorem IsFaithful.eq_zero_of_apply_star_mul_self_eq_zero (hτ : τ.IsFaithful) {a : A}
    (ha : τ (star a * a) = 0) : a = 0 :=
  hτ a ha

/-- Every positive continuous linear functional on a subsingleton algebra is vacuously faithful. -/
theorem isFaithful_of_subsingleton [Subsingleton A] (τ : A →P[ℂ] ℂ) : τ.IsFaithful :=
  fun a _ => Subsingleton.elim a 0

/-- The zero functional on a nontrivial algebra is not faithful. -/
theorem not_isFaithful_zero [Nontrivial A] : ¬ (0 : A →P[ℂ] ℂ).IsFaithful := by
  intro h0
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  exact ha (h0 a (by simp))

/-- **Pullback of faithfulness along an injective `⋆`-homomorphism.** If `ψ` is faithful and `f`
is an injective continuous positive `⋆`-multiplicative linear map, then `ψ ∘ f` is faithful. -/
theorem IsFaithful.comp_of_injective {B F : Type*} [AddCommMonoid B] [Mul B] [Star B]
    [PartialOrder B] [Module ℂ B] [TopologicalSpace B] [FunLike F A B]
    [ContinuousLinearMapClass F ℂ A B] [OrderHomClass F A B] [MulHomClass F A B]
    [StarHomClass F A B] {ψ : B →P[ℂ] ℂ} (hψ : ψ.IsFaithful) (f : F) (hf : Function.Injective f) :
    (ψ.comp (.ofClass f)).IsFaithful := by
  intro a ha
  apply hf
  rw [map_zero]
  exact hψ (f a) (by simpa [map_mul, map_star] using ha)

/-- If a pullback `ψ ∘ f` along a multiplicative continuous positive linear map `f` is faithful,
then `f` must be injective. -/
theorem injective_of_isFaithful_comp_ofClass {B F : Type*} [NonUnitalNonAssocSemiring B]
    [PartialOrder B] [Module ℂ B] [TopologicalSpace B] [FunLike F A B]
    [ContinuousLinearMapClass F ℂ A B] [OrderHomClass F A B] [MulHomClass F A B]
    {ψ : B →P[ℂ] ℂ} (f : F) (h : (ψ.comp (.ofClass f)).IsFaithful) :
    Function.Injective f := by
  let _ : AddCommGroup A := Module.addCommMonoidToAddCommGroup ℂ
  let _ : AddCommGroup B := Module.addCommMonoidToAddCommGroup ℂ
  intro a b hab
  have hsub : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have h0 : a - b = 0 := h (a - b) (by simp [map_mul, hsub])
  exact sub_eq_zero.mp h0

/-- For a faithful functional `ψ`, the pullback `ψ ∘ f` along a `⋆`-multiplicative continuous
positive linear map `f` is faithful if and only if `f` is injective. -/
theorem IsFaithful.comp_ofClass_iff {B F : Type*} [NonUnitalNonAssocSemiring B] [Star B]
    [PartialOrder B] [Module ℂ B] [TopologicalSpace B] [FunLike F A B]
    [ContinuousLinearMapClass F ℂ A B] [OrderHomClass F A B] [MulHomClass F A B]
    [StarHomClass F A B] {ψ : B →P[ℂ] ℂ} (hψ : ψ.IsFaithful) (f : F) :
    (ψ.comp (.ofClass f)).IsFaithful ↔ Function.Injective f :=
  ⟨injective_of_isFaithful_comp_ofClass f, hψ.comp_of_injective f⟩

end FaithfulBasic

section FaithfulStarOrdered

variable {A : Type*} [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [Module ℂ A] [TopologicalSpace A] {τ : A →P[ℂ] ℂ}

/-- A positive continuous linear functional is faithful if and only if `0 < τ (star a * a)` for
every nonzero `a`. -/
theorem isFaithful_iff_forall_star_mul_self_pos :
    τ.IsFaithful ↔ ∀ a : A, a ≠ 0 → 0 < τ (star a * a) := by
  constructor
  · intro hτ a ha
    refine lt_of_le_of_ne (τ.map_nonneg (star_mul_self_nonneg a)) ?_
    exact fun h0 => ha (hτ a h0.symm)
  · intro h a ha
    by_contra ha0
    exact (h a ha0).ne' ha

/-- A faithful positive continuous linear functional is strictly positive on `star a * a` for
every nonzero `a`. -/
theorem IsFaithful.apply_star_mul_self_pos (hτ : τ.IsFaithful) {a : A} (ha : a ≠ 0) :
    0 < τ (star a * a) :=
  isFaithful_iff_forall_star_mul_self_pos.mp hτ a ha

/-- On a star-ordered algebra with proper star, a positive functional is faithful if and only if
`0` is the only nonnegative element on which it vanishes. -/
theorem isFaithful_iff_forall_nonneg_eq_zero [IsProperStar A] :
    τ.IsFaithful ↔ ∀ a : A, 0 ≤ a → τ a = 0 → a = 0 := by
  constructor
  · intro hτ a ha h0
    refine AddSubmonoid.closure_induction (motive := fun x _ => τ x = 0 → x = 0)
      (fun x hx hτx => ?_) (fun _ => rfl) (fun x y hx hy ihx ihy hxy => ?_)
      (StarOrderedRing.nonneg_iff.mp ha) h0
    · rcases hx with ⟨s, rfl⟩
      simp [hτ s hτx]
    · rw [map_add] at hxy
      have ⟨hx0, hy0⟩ := (add_eq_zero_iff_of_nonneg
        (τ.map_nonneg (StarOrderedRing.nonneg_iff.mpr hx))
        (τ.map_nonneg (StarOrderedRing.nonneg_iff.mpr hy))).mp hxy
      rw [ihx hx0, ihy hy0, add_zero]
  · intro h a ha
    exact star_mul_self_eq_zero.mp (h (star a * a) (star_mul_self_nonneg a) ha)

/-- On a star-ordered algebra with proper star, a positive functional is faithful if and only if it
maps strictly positive elements to strictly positive scalars. -/
theorem isFaithful_iff_forall_pos [IsProperStar A] : τ.IsFaithful ↔ ∀ a : A, 0 < a → 0 < τ a := by
  rw [isFaithful_iff_forall_nonneg_eq_zero]
  constructor
  · intro h a ha
    exact lt_of_le_of_ne (τ.map_nonneg ha.le) fun h0 => ha.ne' (h a ha.le h0.symm)
  · intro h a ha h0
    by_contra ha0
    exact (h a (lt_of_le_of_ne ha (Ne.symm ha0))).ne' h0

end FaithfulStarOrdered

section FaithfulCStar

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {τ : A →P[ℂ] ℂ}

/-- If a positive continuous linear functional vanishes on `star a * a`, then it vanishes on `a`. -/
theorem apply_eq_zero_of_apply_star_mul_self_eq_zero {a : A} (ha : τ (star a * a) = 0) :
    τ a = 0 := by
  have h := τ.norm_map_le_sqrt_opNorm_mul a
  rw [ha] at h
  simpa using h

/-- A positive functional on a C⋆-algebra is faithful if and only if its GNS class map
`τ.toPositiveLinearMap.toGNS` is injective. -/
theorem isFaithful_iff_toGNS_injective :
    τ.IsFaithful ↔ Function.Injective τ.toPositiveLinearMap.toGNS := by
  rw [injective_iff_map_eq_zero]
  simp only [IsFaithful, PositiveLinearMap.toGNS_eq_zero_iff, coe_toPositiveLinearMap]

/-- A faithful positive functional on a C⋆-algebra has a faithful (injective) GNS representation.
The converse fails without traciality (for example, a pure vector state on `M₂(ℂ)` has faithful
GNS representation but is not faithful). -/
theorem IsFaithful.gnsNonUnitalStarAlgHom_injective (hτ : τ.IsFaithful) :
    Function.Injective τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom :=
  τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom_injective hτ

/-- On a unital C⋆-algebra, a faithful positive functional has an injective unital GNS
representation. -/
theorem IsFaithful.gnsStarAlgHom_injective {B : Type*} [CStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] {ψ : B →P[ℂ] ℂ} (hψ : ψ.IsFaithful) :
    Function.Injective ψ.toPositiveLinearMap.gnsStarAlgHom :=
  hψ.gnsNonUnitalStarAlgHom_injective

/-- The identity functional on `ℂ` is faithful. -/
theorem isFaithful_id_complex : (PositiveContinuousLinearMap.id ℂ ℂ).IsFaithful :=
  fun _ hz => star_mul_self_eq_zero.mp (by simpa using hz)

end FaithfulCStar

section TraceKernel

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **trace kernel** `N_τ = {a : A | τ (star a * a) = 0}` of a tracial positive continuous
linear functional `τ : A →P[ℂ] ℂ`, as a two-sided ideal of `A`. Traciality makes the left ideal
`{a | τ (star a * a) = 0}` self-adjoint, hence two-sided. -/
noncomputable def traceKernel (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {a : A | τ (star a * a) = 0}
    (by simp)
    (fun {x y} hx hy => by
      have hx' : τ.toPositiveLinearMap.toGNS x = 0 :=
        (PositiveLinearMap.toGNS_eq_zero_iff _ x).mpr hx
      have hy' : τ.toPositiveLinearMap.toGNS y = 0 :=
        (PositiveLinearMap.toGNS_eq_zero_iff _ y).mpr hy
      exact (PositiveLinearMap.toGNS_eq_zero_iff _ (x + y)).mp <| by
        rw [map_add, hx', hy', add_zero])
    (fun {x} hx => by simpa using hx)
    (fun {x y} hy => by
      have hy' : τ.toPositiveLinearMap.toGNS y = 0 :=
        (PositiveLinearMap.toGNS_eq_zero_iff _ y).mpr hy
      exact (PositiveLinearMap.toGNS_eq_zero_iff _ (x * y)).mp <| by
        simpa [PositiveLinearMap.toGNS_apply] using
          congrArg (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom x) hy')
    (fun {x y} hx => by
      have hstar {z : A} (hz : τ (star z * z) = 0) : τ (star (star z) * star z) = 0 := by
        simpa [hτ (star z) z] using hz
      have hxs : τ.toPositiveLinearMap.toGNS (star x) = 0 :=
        (PositiveLinearMap.toGNS_eq_zero_iff _ (star x)).mpr (hstar hx)
      have hleft : τ (star (star y * star x) * (star y * star x)) = 0 :=
        (PositiveLinearMap.toGNS_eq_zero_iff _ (star y * star x)).mp <| by
          simpa [PositiveLinearMap.toGNS_apply] using
            congrArg (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom (star y)) hxs
      simpa [star_mul] using hstar hleft)

variable {τ : A →P[ℂ] ℂ}

/-- Membership in the trace kernel `N_τ` is `τ (star a * a) = 0`. -/
@[simp]
theorem mem_traceKernel_iff (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) {a : A} :
    a ∈ τ.traceKernel hτ ↔ τ (star a * a) = 0 :=
  TwoSidedIdeal.mem_mk' ..

/-- An element belongs to the trace kernel `N_τ` if and only if its GNS class vanishes. -/
theorem mem_traceKernel_iff_toGNS_eq_zero (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) {a : A} :
    a ∈ τ.traceKernel hτ ↔ τ.toPositiveLinearMap.toGNS a = 0 := by
  rw [mem_traceKernel_iff, PositiveLinearMap.toGNS_eq_zero_iff, coe_toPositiveLinearMap]

/-- The trace kernel of a tracial positive continuous linear functional is closed. -/
instance isClosed_traceKernel (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    IsClosed (τ.traceKernel hτ : Set A) := by
  have hcarrier : (τ.traceKernel hτ : Set A) = (fun a : A => τ (star a * a)) ⁻¹' {0} := by
    ext a
    simp
  rw [hcarrier]
  exact isClosed_singleton.preimage (by fun_prop)

/-- A tracial positive continuous linear functional vanishes on its trace kernel. -/
theorem apply_eq_zero_of_mem_traceKernel (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) {a : A}
    (ha : a ∈ τ.traceKernel hτ) : τ a = 0 :=
  apply_eq_zero_of_apply_star_mul_self_eq_zero ((mem_traceKernel_iff hτ).mp ha)

/-- An element belongs to the trace kernel `N_τ` if and only if `τ (a * b) = 0` for all `b`. -/
theorem mem_traceKernel_iff_forall_mul_eq_zero (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) {a : A} :
    a ∈ τ.traceKernel hτ ↔ ∀ b : A, τ (a * b) = 0 := by
  refine ⟨fun ha b => apply_eq_zero_of_mem_traceKernel hτ ((τ.traceKernel hτ).mul_mem_right a b ha),
    fun h => ?_⟩
  rw [mem_traceKernel_iff, hτ]
  exact h (star a)

/-- An element belongs to the trace kernel `N_τ` if and only if `τ (b * a) = 0` for all `b`. -/
theorem mem_traceKernel_iff_forall_mul_left_eq_zero (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    {a : A} : a ∈ τ.traceKernel hτ ↔ ∀ b : A, τ (b * a) = 0 := by
  simp only [mem_traceKernel_iff_forall_mul_eq_zero, hτ a]

/-- **Identification of the trace kernel with the GNS kernel.** For a tracial positive functional,
the trace kernel `N_τ` equals the kernel of the GNS representation `π_τ`. -/
theorem traceKernel_eq_ker_gnsNonUnitalStarAlgHom (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.traceKernel hτ = TwoSidedIdeal.ker τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom := by
  ext a
  rw [TwoSidedIdeal.mem_ker]
  constructor
  · intro ha
    have hdense : ∀ c : A,
        τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a (τ.toPositiveLinearMap.toGNS c) = 0 := by
      intro c
      have hmul : τ.toPositiveLinearMap.toGNS (a * c) = 0 :=
        (mem_traceKernel_iff_toGNS_eq_zero hτ).mp ((τ.traceKernel hτ).mul_mem_right a c ha)
      simpa [PositiveLinearMap.toGNS_apply] using hmul
    ext ξ
    have hfun : (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom a : _ → _) =
        (0 : τ.toPositiveLinearMap.GNS →L[ℂ] τ.toPositiveLinearMap.GNS) := by
      refine τ.toPositiveLinearMap.denseRange_toGNS.equalizer (by fun_prop) (by fun_prop) ?_
      ext c
      exact hdense c
    exact congrFun hfun ξ
  · intro ha
    rw [mem_traceKernel_iff_toGNS_eq_zero]
    have hl := CStarAlgebra.increasingApproximateUnit A
    have := hl.neBot
    have hlim : Tendsto (fun e : A => τ.toPositiveLinearMap.toGNS (a * e))
        (CStarAlgebra.approximateUnit A) (𝓝 (τ.toPositiveLinearMap.toGNS a)) :=
      (τ.toPositiveLinearMap.toGNS.continuous.tendsto a).comp (hl.tendsto_mul_left a)
    have hzero : (fun e : A => τ.toPositiveLinearMap.toGNS (a * e)) = fun _ => 0 := by
      ext e
      simpa [PositiveLinearMap.toGNS_apply] using
        DFunLike.congr_fun ha (τ.toPositiveLinearMap.toGNS e)
    rw [hzero] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- The trace kernel of a nonzero tracial positive continuous linear functional is a proper
ideal. -/
theorem traceKernel_ne_top (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (hτ0 : τ ≠ 0) :
    τ.traceKernel hτ ≠ ⊤ := by
  intro htop
  apply hτ0
  ext a
  exact apply_eq_zero_of_mem_traceKernel hτ (htop ▸ trivial)

/-- A tracial positive functional is faithful if and only if its trace kernel is `⊥`. -/
theorem isFaithful_iff_traceKernel_eq_bot (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.IsFaithful ↔ τ.traceKernel hτ = ⊥ := by
  simp only [IsFaithful, TwoSidedIdeal.ext_iff, mem_traceKernel_iff, TwoSidedIdeal.mem_bot]
  exact ⟨fun h a => ⟨h a, fun ha => by simp [ha]⟩, fun h a ha => (h a).mp ha⟩

/-- **GNS faithfulness criterion for tracial functionals.** A tracial positive functional is
faithful if and only if its GNS representation is injective. -/
theorem isFaithful_iff_gnsNonUnitalStarAlgHom_injective (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.IsFaithful ↔ Function.Injective τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom := by
  rw [isFaithful_iff_traceKernel_eq_bot hτ, traceKernel_eq_ker_gnsNonUnitalStarAlgHom hτ,
    TwoSidedIdeal.ext_iff, injective_iff_map_eq_zero]
  simp only [TwoSidedIdeal.mem_ker, TwoSidedIdeal.mem_bot]
  exact ⟨fun h a ha => (h a).mp ha, fun h a => ⟨h a, fun ha => by simp [ha]⟩⟩

/-- **Simplicity implies faithfulness.** If the only closed two-sided ideals of `A` are `⊥` and
`⊤`, then every nonzero tracial positive continuous linear functional on `A` is faithful. -/
theorem isFaithful_of_forall_isClosed_eq_bot_or_top (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤) (hτ0 : τ ≠ 0) :
    τ.IsFaithful :=
  (isFaithful_iff_traceKernel_eq_bot hτ).mpr <|
    (hsimple (τ.traceKernel hτ) inferInstance).resolve_right (traceKernel_ne_top hτ hτ0)

/-- Every tracial state of a simple C⋆-algebra is faithful. -/
theorem IsTracialState.isFaithful_of_forall_isClosed_eq_bot_or_top (hτ : τ.IsTracialState)
    (hsimple : ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤) :
    τ.IsFaithful :=
  PositiveContinuousLinearMap.isFaithful_of_forall_isClosed_eq_bot_or_top
    hτ.apply_mul_comm hsimple hτ.ne_zero

section Unital

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {ψ : B →P[ℂ] ℂ}

/-- On a unital C⋆-algebra, the trace kernel coincides as an ideal with the algebraic trace
radical `LinearMap.traceRadical`. -/
theorem asIdeal_traceKernel (hψ : ∀ a b : B, ψ (a * b) = ψ (b * a)) :
    (ψ.traceKernel hψ).asIdeal = ψ.toPositiveLinearMap.toLinearMap.traceRadical hψ := by
  ext a
  simp only [TwoSidedIdeal.mem_asIdeal, mem_traceKernel_iff_forall_mul_eq_zero,
    LinearMap.mem_traceRadical, PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap]

/-- On a unital C⋆-algebra, the trace kernel equals the two-sided ideal associated to the algebraic
trace radical `LinearMap.traceRadical`. -/
theorem traceKernel_eq_toTwoSided_traceRadical (hψ : ∀ a b : B, ψ (a * b) = ψ (b * a)) :
    ψ.traceKernel hψ = (ψ.toPositiveLinearMap.toLinearMap.traceRadical hψ).toTwoSided := by
  ext a
  simp only [Ideal.mem_toTwoSided, mem_traceKernel_iff_forall_mul_eq_zero,
    LinearMap.mem_traceRadical, PositiveLinearMap.coe_toLinearMap, coe_toPositiveLinearMap]

/-- On a unital C⋆-algebra, the trace kernel equals the kernel of the unital GNS representation. -/
theorem traceKernel_eq_ker_gnsStarAlgHom (hψ : ∀ a b : B, ψ (a * b) = ψ (b * a)) :
    ψ.traceKernel hψ = TwoSidedIdeal.ker ψ.toPositiveLinearMap.gnsStarAlgHom :=
  (traceKernel_eq_ker_gnsNonUnitalStarAlgHom hψ).trans <| by
    ext a
    simp only [TwoSidedIdeal.mem_ker, PositiveLinearMap.gnsStarAlgHom_apply,
      NonUnitalAlgHom.toFun_eq_coe, NonUnitalStarAlgHom.coe_toNonUnitalAlgHom]

/-- On a unital C⋆-algebra, a tracial positive functional is faithful if and only if its unital
GNS representation is injective. -/
theorem isFaithful_iff_gnsStarAlgHom_injective (hψ : ∀ a b : B, ψ (a * b) = ψ (b * a)) :
    ψ.IsFaithful ↔ Function.Injective ψ.toPositiveLinearMap.gnsStarAlgHom :=
  isFaithful_iff_gnsNonUnitalStarAlgHom_injective hψ

/-- On a unital C⋆-algebra, a tracial positive functional is faithful if and only if its algebraic
trace radical is `⊥`. -/
theorem isFaithful_iff_traceRadical_eq_bot (hψ : ∀ a b : B, ψ (a * b) = ψ (b * a)) :
    ψ.IsFaithful ↔ ψ.toPositiveLinearMap.toLinearMap.traceRadical hψ = ⊥ := by
  rw [isFaithful_iff_traceKernel_eq_bot hψ, ← asIdeal_traceKernel hψ]
  constructor
  · intro h
    rw [h, TwoSidedIdeal.bot_asIdeal]
  · intro h
    ext a
    simpa [TwoSidedIdeal.mem_asIdeal] using SetLike.ext_iff.mp h a

end Unital

end TraceKernel

section Descent

variable {A B F : Type*} [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A]
  [Module ℂ A] [TopologicalSpace A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- **Descent of a positive continuous linear functional along a surjective `⋆`-homomorphism.**
If `f : A → B` is a surjective `⋆`-homomorphism onto a C⋆-algebra `B` and `τ : A →P[ℂ] ℂ` vanishes
on `ker f`, then `τ` factors uniquely through a positive continuous linear functional
`τ.descend f hf hker : B →P[ℂ] ℂ`. Positivity follows from lifting `star y * y` along `f`, and
continuity is automatic on the C⋆-algebra `B`. -/
noncomputable def descend (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) : B →P[ℂ] ℂ :=
  have happly (a : A) : τ (Function.surjInv hf (f a)) = τ a := by
    let _ : AddCommGroup A := Module.addCommMonoidToAddCommGroup ℂ
    have h0 : f (Function.surjInv hf (f a) - a) = 0 := by
      rw [map_sub, Function.surjInv_eq hf, sub_self]
    exact sub_eq_zero.mp ((map_sub τ _ _).symm.trans (hker _ h0))
  let lin : B →ₗ[ℂ] ℂ :=
    { toFun := fun b => τ (Function.surjInv hf b)
      map_add' := fun x y => by
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        rw [← map_add, happly, happly, happly, map_add]
      map_smul' := fun c x => by
        obtain ⟨a, rfl⟩ := hf x
        simp only [RingHom.id_apply, ← map_smul, happly] }
  let pos : B →ₚ[ℂ] ℂ :=
    { __ := lin
      monotone' := (monotone_iff_map_nonneg lin).mpr fun x hx => by
        obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hx
        obtain ⟨a, rfl⟩ := hf y
        simp only [lin, LinearMap.coe_mk, AddHom.coe_mk, ← map_star, ← map_mul, happly]
        exact τ.map_nonneg (star_mul_self_nonneg a) }
  PositiveContinuousLinearMap.ofClass pos

/-- Evaluating the descended functional at `f a` recovers `τ a`. -/
@[simp]
theorem descend_apply (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) (a : A) :
    τ.descend f hf hker (f a) = τ a := by
  let _ : AddCommGroup A := Module.addCommMonoidToAddCommGroup ℂ
  simp only [descend, PositiveContinuousLinearMap.coe_ofClass, ← PositiveLinearMap.coe_toLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk]
  have h0 : f (Function.surjInv hf (f a) - a) = 0 := by
    rw [map_sub, Function.surjInv_eq hf, sub_self]
  exact sub_eq_zero.mp ((map_sub τ _ _).symm.trans (hker _ h0))

/-- Precomposing the descended functional with `f` recovers `τ`. -/
@[simp]
theorem descend_comp_ofClass [ContinuousLinearMapClass F ℂ A B] [OrderHomClass F A B]
    (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f) (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.descend f hf hker).comp (.ofClass f) = τ :=
  PositiveContinuousLinearMap.ext (descend_apply τ f hf hker)

/-- Uniqueness of the descended functional along a surjective `⋆`-homomorphism. -/
theorem eq_descend {τ : A →P[ℂ] ℂ} {f : F} (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) {ψ : B →P[ℂ] ℂ} (hψ : ∀ a : A, ψ (f a) = τ a) :
    ψ = τ.descend f hf hker := by
  ext b
  obtain ⟨a, rfl⟩ := hf b
  rw [hψ, descend_apply]

/-- Descending a tracial positive functional along a surjective `⋆`-homomorphism preserves
traciality. -/
theorem descend_mul_comm {τ : A →P[ℂ] ℂ} (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (f : F)
    (hf : Function.Surjective f) (hker : ∀ a : A, f a = 0 → τ a = 0) (x y : B) :
    τ.descend f hf hker (x * y) = τ.descend f hf hker (y * x) := by
  obtain ⟨a, rfl⟩ := hf x
  obtain ⟨b, rfl⟩ := hf y
  rw [← map_mul, ← map_mul, descend_apply, descend_apply, hτ]

/-- The descended functional is faithful if and only if every `a` with `τ (star a * a) = 0` lies
in the kernel of `f`. -/
theorem isFaithful_descend_iff (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.descend f hf hker).IsFaithful ↔ ∀ a : A, τ (star a * a) = 0 → f a = 0 := by
  constructor
  · intro h a ha
    apply h (f a)
    rw [← map_star, ← map_mul, descend_apply, ha]
  · intro h x hx
    obtain ⟨a, rfl⟩ := hf x
    rw [← map_star, ← map_mul, descend_apply] at hx
    exact h a hx

end Descent

section DescentCStar

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- Descending a positive functional along a surjective `⋆`-homomorphism preserves its operator
norm. -/
theorem opNorm_descend (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    ‖(τ.descend f hf hker : B →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ := by
  rw [← opNorm_comp_ofClass_of_surjective (τ.descend f hf hker) f hf, descend_comp_ofClass]

/-- The descended functional is a tracial state if and only if the original functional is. -/
theorem isTracialState_descend_iff (τ : A →P[ℂ] ℂ) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.descend f hf hker).IsTracialState ↔ τ.IsTracialState := by
  rw [← isTracialState_comp_iff_of_surjective f hf, descend_comp_ofClass]

/-- For a tracial positive functional, the descended functional along `f` is faithful if and only
if `ker f = N_τ`. -/
theorem isFaithful_descend_iff_ker_eq_traceKernel {τ : A →P[ℂ] ℂ}
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (f : F) (hf : Function.Surjective f)
    (hker : ∀ a : A, f a = 0 → τ a = 0) :
    (τ.descend f hf hker).IsFaithful ↔ TwoSidedIdeal.ker f = τ.traceKernel hτ := by
  rw [isFaithful_descend_iff, TwoSidedIdeal.ext_iff]
  constructor
  · intro h a
    rw [TwoSidedIdeal.mem_ker, mem_traceKernel_iff]
    exact ⟨fun ha => hker (star a * a) (by simp [map_mul, map_star, ha]), h a⟩
  · intro h a ha
    exact (TwoSidedIdeal.mem_ker f).mp ((h a).mpr ((mem_traceKernel_iff hτ).mpr ha))

end DescentCStar

section DescendRange

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Descend a positive continuous linear functional `τ : A →P[ℂ] ℂ` to the closed C⋆-subalgebra
range `φ.range` of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` whenever `τ` vanishes on `ker φ`. -/
noncomputable def descendRange (τ : A →P[ℂ] ℂ) (φ : A →⋆ₙₐ[ℂ] B)
    (hker : ∀ a : A, φ a = 0 → τ a = 0) : φ.range →P[ℂ] ℂ :=
  τ.descend φ.rangeRestrict (NonUnitalStarAlgHom.rangeRestrict_surjective φ) fun a ha =>
    hker a (congrArg Subtype.val ha)

/-- Evaluating `τ.descendRange φ hker` at `φ.rangeRestrict a` recovers `τ a`. -/
@[simp]
theorem descendRange_apply (τ : A →P[ℂ] ℂ) (φ : A →⋆ₙₐ[ℂ] B)
    (hker : ∀ a : A, φ a = 0 → τ a = 0) (a : A) :
    τ.descendRange φ hker (φ.rangeRestrict a) = τ a :=
  descend_apply τ φ.rangeRestrict (NonUnitalStarAlgHom.rangeRestrict_surjective φ) _ a

/-- Uniqueness of `descendRange`. -/
theorem eq_descendRange {τ : A →P[ℂ] ℂ} {φ : A →⋆ₙₐ[ℂ] B} (hker : ∀ a : A, φ a = 0 → τ a = 0)
    {ψ : φ.range →P[ℂ] ℂ} (hψ : ∀ a : A, ψ (φ.rangeRestrict a) = τ a) :
    ψ = τ.descendRange φ hker :=
  eq_descend (NonUnitalStarAlgHom.rangeRestrict_surjective φ) _ hψ

/-- Descending a positive functional to `φ.range` preserves its operator norm. -/
theorem opNorm_descendRange (τ : A →P[ℂ] ℂ) (φ : A →⋆ₙₐ[ℂ] B)
    (hker : ∀ a : A, φ a = 0 → τ a = 0) :
    ‖(τ.descendRange φ hker : φ.range →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ :=
  opNorm_descend τ φ.rangeRestrict (NonUnitalStarAlgHom.rangeRestrict_surjective φ) _

/-- Descending a tracial positive functional to `φ.range` preserves traciality. -/
theorem descendRange_mul_comm {τ : A →P[ℂ] ℂ} (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (φ : A →⋆ₙₐ[ℂ] B) (hker : ∀ a : A, φ a = 0 → τ a = 0) (x y : φ.range) :
    τ.descendRange φ hker (x * y) = τ.descendRange φ hker (y * x) :=
  descend_mul_comm hτ φ.rangeRestrict (NonUnitalStarAlgHom.rangeRestrict_surjective φ) _ x y

/-- `τ.descendRange φ hker` is a tracial state if and only if `τ` is. -/
theorem isTracialState_descendRange_iff (τ : A →P[ℂ] ℂ) (φ : A →⋆ₙₐ[ℂ] B)
    (hker : ∀ a : A, φ a = 0 → τ a = 0) :
    (τ.descendRange φ hker).IsTracialState ↔ τ.IsTracialState :=
  isTracialState_descend_iff τ φ.rangeRestrict (NonUnitalStarAlgHom.rangeRestrict_surjective φ) _

/-- For a tracial positive functional `τ`, `τ.descendRange φ hker` is faithful if and only if
`ker φ = N_τ`. -/
theorem isFaithful_descendRange_iff_ker_eq_traceKernel {τ : A →P[ℂ] ℂ}
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (φ : A →⋆ₙₐ[ℂ] B)
    (hker : ∀ a : A, φ a = 0 → τ a = 0) :
    (τ.descendRange φ hker).IsFaithful ↔ TwoSidedIdeal.ker φ = τ.traceKernel hτ := by
  rw [descendRange, isFaithful_descend_iff_ker_eq_traceKernel hτ,
    NonUnitalStarAlgHom.ker_rangeRestrict φ]

end DescendRange

section FaithfulDescendedTraces

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Descended faithful trace on the GNS image `π_τ(A)`.** For a tracial positive functional
`τ : A →P[ℂ] ℂ`, `τ.gnsRangeTrace hτ` is the unique positive functional on the C⋆-algebra
`π_τ(A)` satisfying `(τ.gnsRangeTrace hτ) (π_τ a) = τ a`. -/
noncomputable def gnsRangeTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range →P[ℂ] ℂ :=
  τ.descendRange τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom fun _ ha =>
    apply_eq_zero_of_mem_traceKernel hτ <|
      (traceKernel_eq_ker_gnsNonUnitalStarAlgHom hτ).symm ▸
        (TwoSidedIdeal.mem_ker _).mpr ha

/-- Evaluating `τ.gnsRangeTrace hτ` at `π_τ(a)` recovers `τ a`. -/
@[simp]
theorem gnsRangeTrace_apply (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    τ.gnsRangeTrace hτ (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict a) = τ a :=
  descendRange_apply τ τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom _ a

/-- Uniqueness of the descended trace on the GNS image `π_τ(A)`. -/
theorem eq_gnsRangeTrace {τ : A →P[ℂ] ℂ} (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    {ψ : τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range →P[ℂ] ℂ}
    (hψ : ∀ a : A, ψ (τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict a) = τ a) :
    ψ = τ.gnsRangeTrace hτ :=
  eq_descendRange _ hψ

/-- The descended trace on the GNS image `π_τ(A)` is tracial. -/
theorem gnsRangeTrace_mul_comm (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    (x y : τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range) :
    τ.gnsRangeTrace hτ (x * y) = τ.gnsRangeTrace hτ (y * x) :=
  descendRange_mul_comm hτ τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom _ x y

/-- The descended trace on the GNS image `π_τ(A)` is a tracial state if and only if `τ` is. -/
theorem isTracialState_gnsRangeTrace_iff (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    PositiveContinuousLinearMap.IsTracialState
      (A := τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range) (τ.gnsRangeTrace hτ) ↔
      τ.IsTracialState :=
  isTracialState_descendRange_iff τ τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom _

/-- The descended trace on the GNS image `π_τ(A)` is faithful. -/
theorem isFaithful_gnsRangeTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    (τ.gnsRangeTrace hτ).IsFaithful :=
  (isFaithful_descendRange_iff_ker_eq_traceKernel hτ
    τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom _).mpr
    (traceKernel_eq_ker_gnsNonUnitalStarAlgHom hτ).symm

/-- **Descended faithful trace on the C⋆-quotient `A ⧸ N_τ`.** For a tracial positive functional
`τ : A →P[ℂ] ℂ`, `τ.quotientTrace hτ` is the unique positive functional on `A ⧸ N_τ` whose
pullback along `mk N_τ` is `τ`. -/
noncomputable def quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (A ⧸ τ.traceKernel hτ) →P[ℂ] ℂ :=
  τ.descend (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))
    (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective _)
    fun _ ha => apply_eq_zero_of_mem_traceKernel hτ <|
      TwoSidedIdeal.Quotient.eq_zero_iff_mem.mp (by simpa using ha)

/-- Evaluating `τ.quotientTrace hτ` on the coset of `a` recovers `τ a`. -/
@[simp]
theorem quotientTrace_mk (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] (a : A) :
    τ.quotientTrace hτ (TwoSidedIdeal.Quotient.mk (τ.traceKernel hτ) a) = τ a := by
  simpa [quotientTrace] using
    descend_apply τ (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ))
      (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective _) _ a

/-- Uniqueness of the descended trace on `A ⧸ N_τ`. -/
theorem eq_quotientTrace {τ : A →P[ℂ] ℂ} (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)]
    {ψ : (A ⧸ τ.traceKernel hτ) →P[ℂ] ℂ}
    (hψ : ∀ a : A, ψ (TwoSidedIdeal.Quotient.mk (τ.traceKernel hτ) a) = τ a) :
    ψ = τ.quotientTrace hτ :=
  eq_descend (TwoSidedIdeal.Quotient.mkStarAlgHom_surjective _) _ fun a => by simpa using hψ a

/-- The descended trace on `A ⧸ N_τ` has the same operator norm as `τ`. -/
theorem opNorm_quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    ‖(τ.quotientTrace hτ : (A ⧸ τ.traceKernel hτ) →L[ℂ] ℂ)‖ = ‖(τ : A →L[ℂ] ℂ)‖ :=
  opNorm_descend τ (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _

/-- The descended trace on `A ⧸ N_τ` is tracial. -/
theorem quotientTrace_mul_comm (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)]
    (x y : A ⧸ τ.traceKernel hτ) :
    τ.quotientTrace hτ (x * y) = τ.quotientTrace hτ (y * x) :=
  descend_mul_comm hτ (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _ x y

/-- The descended trace on `A ⧸ N_τ` is a tracial state if and only if `τ` is. -/
theorem isTracialState_quotientTrace_iff (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).IsTracialState ↔ τ.IsTracialState :=
  isTracialState_descend_iff τ (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _

/-- The descended trace on `A ⧸ N_τ` is faithful. -/
theorem isFaithful_quotientTrace (τ : A →P[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)] :
    (τ.quotientTrace hτ).IsFaithful :=
  (isFaithful_descend_iff_ker_eq_traceKernel hτ
    (TwoSidedIdeal.Quotient.mkStarAlgHom (τ.traceKernel hτ)) _ _).mpr
    (TwoSidedIdeal.Quotient.ker_mkStarAlgHom _)

/-- The canonical isometric `⋆`-isomorphism `A ⧸ N_τ ≃⋆ₐ[ℂ] π_τ(A)` identifying the quotient by
the trace kernel with the GNS image. -/
noncomputable def quotientTraceKernelEquivGNSRange (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) :
    A ⧸ τ.traceKernel hτ ≃⋆ₐ[ℂ] τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.range :=
  (TwoSidedIdeal.Quotient.quotStarAlgEquivOfEq
      (traceKernel_eq_ker_gnsNonUnitalStarAlgHom hτ)).trans
    τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.quotientKerEquivRange

/-- Action of `quotientTraceKernelEquivGNSRange` on cosets. -/
@[simp]
theorem quotientTraceKernelEquivGNSRange_mk (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (a : A) :
    τ.quotientTraceKernelEquivGNSRange hτ (TwoSidedIdeal.Quotient.mk (τ.traceKernel hτ) a) =
      τ.toPositiveLinearMap.gnsNonUnitalStarAlgHom.rangeRestrict a := by
  simp [quotientTraceKernelEquivGNSRange]

/-- The canonical isomorphism `A ⧸ N_τ ≃⋆ₐ[ℂ] π_τ(A)` intertwines the descended traces
`quotientTrace` and `gnsRangeTrace`. -/
theorem gnsRangeTrace_quotientTraceKernelEquivGNSRange (τ : A →P[ℂ] ℂ)
    (hτ : ∀ a b : A, τ (a * b) = τ (b * a))
    [PartialOrder (A ⧸ τ.traceKernel hτ)] [StarOrderedRing (A ⧸ τ.traceKernel hτ)]
    (x : A ⧸ τ.traceKernel hτ) :
    τ.gnsRangeTrace hτ (τ.quotientTraceKernelEquivGNSRange hτ x) = τ.quotientTrace hτ x := by
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective (τ.traceKernel hτ) x
  simp

end FaithfulDescendedTraces

end PositiveContinuousLinearMap
