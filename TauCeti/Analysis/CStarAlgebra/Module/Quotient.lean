/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.Analysis.CStarAlgebra.Module.Action
public import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
public import TauCeti.Analysis.CStarAlgebra.Quotient
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import TauCeti.Analysis.Normed.Module.Quotient

/-!
# Quotient Hilbert C⋆-modules by closed two-sided ideals

For a Hilbert C⋆-module `E` over a (possibly nonunital) C⋆-algebra `A` and a two-sided ideal
`J : TwoSidedIdeal A`, we define the closed submodule
`E J = CStarModule.idealSubmodule J E = closure (span_ℂ {a • x | a ∈ J, x ∈ E})`.
When `J` is closed, `E J` coincides with `{x : E | ⟪x, x⟫_A ∈ J}`
(`CStarModule.mem_idealSubmodule_iff`):
* for `z ∈ E J`, continuity and `ℂ`-linearity of `innerSL y` together with right ideal absorption
  `⟪y, a • x⟫_A = a * ⟪y, x⟫_A ∈ J` give `⟪y, z⟫_A ∈ J` for all `y : E`;
* conversely, if `⟪x, x⟫_A ∈ J`, its positive square root `s = CFC.sqrt ⟪x, x⟫_A` lies in `J` by
  functional-calculus stability of the C⋆-subalgebra `J.toNonUnitalStarSubalgebra`, so along an
  increasing approximate unit `e` of `J` we have `(e : A) • x ∈ E J` and
  `‖(e : A) • x - x‖ = ‖(e : A) * s - s‖ → 0` (`CStarModule.norm_smul_sub_self`).

Thus `x ∈ E J` already holds as a norm limit of single products `a • x` (`a ∈ J`), without taking
linear combinations (`CStarModule.mem_idealSubmodule_iff_mem_closure`). Because `E J` is closed
(`CStarModule.isClosed_idealSubmodule`), the Banach quotient `E ⧸ idealSubmodule J E` inherits
`NormedAddCommGroup`, `NormedSpace ℂ`, and (when `E` is complete) `CompleteSpace` directly from
Mathlib's `Submodule.Quotient` instances.

Equipping `E ⧸ idealSubmodule J E` with `(A ⧸ J)`-action `mk J a • mk x = mk (a • x)` and
`(A ⧸ J)`-valued inner product `⟪mk x, mk y⟫_{A ⧸ J} = mk J ⟪x, y⟫_A`, we prove the quotient norm
formula `‖mk x‖ = √‖mk J ⟪x, x⟫_A‖` (`CStarModule.norm_mk_idealSubmodule`) by combining
representative lifting in one direction with the unitization C⋆-estimate
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le` applied to `s = CFC.sqrt ⟪x, x⟫_A` along an increasing
approximate unit of `J` in the other. Together with positivity of the quotient `⋆`-homomorphism
`mkStarAlgHom J`, this makes `E ⧸ idealSubmodule J E` a `CStarModule (A ⧸ J)`
(`CStarModule.instCStarModuleQuotient`), and in right-module form makes
`E ⧸ idealSubmodule J.op E` a right Hilbert `(A ⧸ J)`-module `CStarModule (A ⧸ J)ᵐᵒᵖ`
(`CStarModule.instCStarModuleQuotientMulOpposite`).

Note that we do not register a global `PartialOrder (A ⧸ J)` instance (which would conflict with
`Quotient.instPreorderQuotient` in `Mathlib/Order/Quotient.lean`); scalar multiplication, inner
products, the quotient norm formula, and functoriality require no order on `A ⧸ J`, while
`CStarModule` instances accept any `[PartialOrder (A ⧸ J)] [StarOrderedRing (A ⧸ J)]` (such as
`CStarAlgebra.spectralOrder (A ⧸ J)`).

Finally, we establish functoriality in `E` (`CStarModule.quotientMapCLM`, including contractive
operator-norm bounds, isometricity under inner-product preservation, and descent of adjoint pairs)
and in `J` (`CStarModule.quotientFactorCLM`, intertwining `factorStarAlgHom`). Compatibility with
`innerIdeal`, `IsFull`, and self-modules is established in
`TauCeti.Analysis.CStarAlgebra.Module.Full`.

## Main declarations

* `CStarModule.idealSubmodule`: the closed submodule `E J` of `E` associated to
  `J : TwoSidedIdeal A` (use `idealSubmodule J.op E` for right modules `CStarModule Aᵐᵒᵖ E`).
* `CStarModule.mem_idealSubmodule_iff` and `CStarModule.mem_idealSubmodule_op_iff`:
  `x ∈ idealSubmodule J E ↔ ⟪x, x⟫_A ∈ J` (and `⟨x, x⟩_A ∈ J` for right modules).
* `CStarModule.norm_mk_idealSubmodule` and `CStarModule.norm_mk_idealSubmodule_op`: the quotient
  norm formula `‖mk x‖ = √‖mk J ⟪x, x⟫_A‖`.
* `CStarModule.instCStarModuleQuotient` and `CStarModule.instCStarModuleQuotientMulOpposite`: the
  Hilbert `(A ⧸ J)`-module structures on `E ⧸ idealSubmodule J E` and `E ⧸ idealSubmodule J.op E`.
* `CStarModule.quotientMapCLM` and `CStarModule.quotientFactorCLM`: functoriality of `E ⧸ E J` in
  `E` and in `J`.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 1.
* Iain Raeburn and Dana P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Proposition 3.25 and Section 3.3.
-/

public section

open MulOpposite Filter Topology
open scoped CStarAlgebra

namespace CStarModule

/-! ### The closed submodule `E J` -/

section IdealSubmoduleDefs

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- For a two-sided ideal `J` of `A`, `idealSubmodule J E` is the closed complex submodule
`E J = closure (span_ℂ {a • x | a ∈ J, x ∈ E})` of `E`. For a right Hilbert `A`-module
`CStarModule Aᵐᵒᵖ E`, use `idealSubmodule J.op E`, whose generators are `op a • x` (`a ∈ J`). -/
def idealSubmodule (J : TwoSidedIdeal A) (E : Type*) [TopologicalSpace E] [AddCommMonoid E]
    [Module ℂ E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] [SMul A E] : Submodule ℂ E :=
  (Submodule.span ℂ {y : E | ∃ a ∈ J, ∃ x : E, a • x = y}).topologicalClosure

section TopologicalModule

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℂ E]
  [ContinuousAdd E] [ContinuousConstSMul ℂ E] [SMul A E]

instance isClosed_idealSubmodule (J : TwoSidedIdeal A) (E : Type*) [TopologicalSpace E]
    [AddCommMonoid E] [Module ℂ E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] [SMul A E] :
    IsClosed (idealSubmodule J E : Set E) :=
  Submodule.isClosed_topologicalClosure _

theorem coe_idealSubmodule (J : TwoSidedIdeal A) :
    (idealSubmodule J E : Set E) =
      closure (Submodule.span ℂ {y : E | ∃ a ∈ J, ∃ x : E, a • x = y} : Set E) := (rfl)

theorem smul_mem_idealSubmodule {J : TwoSidedIdeal A} {a : A} (ha : a ∈ J) (x : E) :
    a • x ∈ idealSubmodule J E :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, ha, x, rfl⟩)

theorem op_smul_mem_idealSubmodule_op {E : Type*} [TopologicalSpace E] [AddCommMonoid E]
    [Module ℂ E] [ContinuousAdd E] [ContinuousConstSMul ℂ E] [SMul Aᵐᵒᵖ E]
    {J : TwoSidedIdeal A} {a : A} (ha : a ∈ J) (x : E) :
    op a • x ∈ idealSubmodule J.op E :=
  smul_mem_idealSubmodule (J := J.op) (TwoSidedIdeal.mem_op_iff.mpr ha) x

theorem idealSubmodule_le_iff {J : TwoSidedIdeal A} {S : Submodule ℂ E}
    (hS : IsClosed (S : Set E)) :
    idealSubmodule J E ≤ S ↔ ∀ a ∈ J, ∀ x : E, a • x ∈ S := by
  refine ⟨fun h a ha x => h (smul_mem_idealSubmodule ha x), fun h => ?_⟩
  refine Submodule.topologicalClosure_minimal _ ?_ hS
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, x, rfl⟩
  exact h a ha x

theorem idealSubmodule_mono {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂) :
    idealSubmodule J₁ E ≤ idealSubmodule J₂ E :=
  (idealSubmodule_le_iff (isClosed_idealSubmodule J₂ E)).mpr fun _ ha x =>
    smul_mem_idealSubmodule (h ha) x

end TopologicalModule

end IdealSubmoduleDefs

/-! ### Inner-product characterization `E J = {x : ⟪x, x⟫_A ∈ J}` -/

section Characterization

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

-- Verify that Banach-space completeness of `E ⧸ idealSubmodule J E` is synthesized automatically
-- from `isClosed_idealSubmodule` and Mathlib's `Submodule.Quotient.completeSpace`.
example (J : TwoSidedIdeal A) [CompleteSpace E] : CompleteSpace (E ⧸ idealSubmodule J E) :=
  inferInstance

@[simp]
theorem idealSubmodule_bot : idealSubmodule (⊥ : TwoSidedIdeal A) E = ⊥ :=
  le_antisymm ((idealSubmodule_le_iff isClosed_singleton).mpr fun a ha x => by
    rw [TwoSidedIdeal.mem_bot] at ha; rw [ha, (smulWithZero A E).zero_smul]
    exact Submodule.zero_mem ⊥) bot_le

/-- `idealSubmodule` carries binary suprema of ideals to the closed sum of submodules. -/
theorem idealSubmodule_sup (J₁ J₂ : TwoSidedIdeal A) :
    idealSubmodule (J₁ ⊔ J₂) E =
      (idealSubmodule J₁ E ⊔ idealSubmodule J₂ E).topologicalClosure := by
  refine le_antisymm ?_ ?_
  · refine (idealSubmodule_le_iff (Submodule.isClosed_topologicalClosure _)).mpr fun a ha x => ?_
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := TwoSidedIdeal.mem_sup.mp ha
    rw [CStarModule.add_smul]
    exact Submodule.le_topologicalClosure _
      (Submodule.add_mem_sup (smul_mem_idealSubmodule ha₁ x) (smul_mem_idealSubmodule ha₂ x))
  · exact Submodule.topologicalClosure_minimal _
      (sup_le (idealSubmodule_mono le_sup_left) (idealSubmodule_mono le_sup_right))
      (isClosed_idealSubmodule (J₁ ⊔ J₂) E)

variable [StarOrderedRing A]

/-- `idealSubmodule J E` is stable under the full coefficient action of `A` (even when `J` is not
closed). -/
theorem coeff_smul_mem_idealSubmodule {J : TwoSidedIdeal A} (b : A) {z : E}
    (hz : z ∈ idealSubmodule J E) : b • z ∈ idealSubmodule J E := by
  let S : Submodule ℂ E := (idealSubmodule J E).comap (smulCLM (E := E) b).toLinearMap
  have hS : IsClosed (S : Set E) :=
    (isClosed_idealSubmodule J E).preimage (smulCLM (E := E) b).continuous
  have hle : idealSubmodule J E ≤ S := (idealSubmodule_le_iff hS).mpr fun a ha x => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, smulCLM_apply,
      ← (semigroupAction A E).mul_smul]
    exact smul_mem_idealSubmodule (J.mul_mem_left b a ha) x
  simpa only [S, Submodule.mem_comap, ContinuousLinearMap.coe_coe, smulCLM_apply] using hle hz

@[simp]
theorem idealSubmodule_top : idealSubmodule (⊤ : TwoSidedIdeal A) E = ⊤ :=
  eq_top_iff.mpr fun x _ => by
  have hl := (CStarAlgebra.increasingApproximateUnit A).toIsApproximateUnit
  have := hl.neBot
  exact (isClosed_idealSubmodule ⊤ E).mem_of_tendsto
    (tendsto_smul (fun b => hl.tendsto_mul_right b) x)
    (Eventually.of_forall fun e => smul_mem_idealSubmodule (TwoSidedIdeal.mem_top A) x)

section ClosedIdeal

variable {J : TwoSidedIdeal A} [hJ : IsClosed (J : Set A)]

/-- Pairing any vector `y : E` on the left with `z ∈ idealSubmodule J E` lands in `J`. -/
theorem inner_mem_of_mem_idealSubmodule_right (y : E) {z : E} (hz : z ∈ idealSubmodule J E) :
    inner A y z ∈ J := by
  let S : Submodule ℂ E := J.toSubmodule.comap (innerSL (A := A) y).toLinearMap
  have hS : IsClosed (S : Set E) := by
    rw [Submodule.comap_coe, ContinuousLinearMap.coe_coe, TwoSidedIdeal.coe_toSubmodule]
    exact hJ.preimage (innerSL (A := A) y).continuous
  have hle : idealSubmodule J E ≤ S := (idealSubmodule_le_iff hS).mpr fun a ha x => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, innerSL_apply,
      TwoSidedIdeal.mem_toSubmodule, inner_op_smul_right]
    exact J.mul_mem_right a (inner A y x) ha
  exact hle hz

/-- Pairing `z ∈ idealSubmodule J E` on the left with any vector `y : E` lands in `J`. -/
theorem inner_mem_of_mem_idealSubmodule_left {z : E} (hz : z ∈ idealSubmodule J E) (y : E) :
    inner A z y ∈ J :=
  star_inner (A := A) y z ▸ J.star_mem_of_isClosed (inner_mem_of_mem_idealSubmodule_right y hz)

private theorem mem_closure_smul_of_isClosed {x : E} (hx : inner A x x ∈ J) :
    x ∈ closure {y : E | ∃ a ∈ J, a • x = y} := by
  have hsqrt_mem : CFC.sqrt (inner A x x) ∈ J := by
    rw [CFC.sqrt_eq_real_sqrt _ inner_self_nonneg]
    exact J.cfcₙ_mem_of_isClosed Real.sqrt hx
  let S := J.toNonUnitalStarSubalgebra
  let l : Filter S := CStarAlgebra.approximateUnit S
  have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit S
  have := hl.neBot
  let s : S := ⟨CFC.sqrt (inner A x x), J.mem_toNonUnitalStarSubalgebra.mpr hsqrt_mem⟩
  have hlim : Tendsto (fun e : S => (e : A) • x) l (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp_rw [norm_smul_sub_self]
    exact tendsto_iff_norm_sub_tendsto_zero.mp
      ((continuous_subtypeVal.tendsto s).comp (hl.tendsto_mul_right s))
  exact mem_closure_of_tendsto hlim
    (Eventually.of_forall fun e => ⟨(e : A), J.mem_toNonUnitalStarSubalgebra.mp e.property, rfl⟩)

/-- For a closed two-sided ideal `J` of `A`, `x ∈ idealSubmodule J E` if and only if
`⟪x, x⟫_A ∈ J`. -/
theorem mem_idealSubmodule_iff {x : E} :
    x ∈ idealSubmodule J E ↔ inner A x x ∈ J :=
  ⟨inner_mem_of_mem_idealSubmodule_right x, fun hx => by
    rw [← SetLike.mem_coe, coe_idealSubmodule]
    exact closure_mono (by rintro _ ⟨a, ha, rfl⟩; exact Submodule.subset_span ⟨a, ha, x, rfl⟩)
      (mem_closure_smul_of_isClosed hx)⟩

theorem mem_idealSubmodule_iff_forall_inner_right {x : E} :
    x ∈ idealSubmodule J E ↔ ∀ y : E, inner A y x ∈ J :=
  ⟨fun hx y => inner_mem_of_mem_idealSubmodule_right y hx,
   fun h => mem_idealSubmodule_iff.mpr (h x)⟩

theorem mem_idealSubmodule_iff_forall_inner_left {x : E} :
    x ∈ idealSubmodule J E ↔ ∀ y : E, inner A x y ∈ J :=
  ⟨fun hx y => inner_mem_of_mem_idealSubmodule_left hx y,
   fun h => mem_idealSubmodule_iff.mpr (h x)⟩

theorem coe_idealSubmodule_eq_setOf (J : TwoSidedIdeal A) [IsClosed (J : Set A)] :
    (idealSubmodule J E : Set E) = {x : E | inner A x x ∈ J} :=
  Set.ext fun _ => mem_idealSubmodule_iff

end ClosedIdeal

private theorem closure_smul_topologicalClosure_subset (J : TwoSidedIdeal A) (x : E) :
    closure {y : E | ∃ a ∈ J.topologicalClosure, a • x = y} ⊆
      closure {y : E | ∃ a ∈ J, a • x = y} := by
  let f : A →+ E :=
    ⟨⟨(· • x), (smulWithZero A E).zero_smul x⟩, fun a b => CStarModule.add_smul a b x⟩
  have hcont : Continuous f :=
    AddMonoidHomClass.continuous_of_bound f ‖x‖ fun a =>
      (CStarModule.norm_smul_le a x).trans_eq (mul_comm _ _)
  exact closure_minimal (fun _ ⟨a, ha, hax⟩ =>
    hax ▸ image_closure_subset_closure_image hcont ⟨a, J.mem_topologicalClosure.mp ha, rfl⟩)
    isClosed_closure

/-- If `⟪x, x⟫_A ∈ J`, then `x` is a norm limit of elements `a • x` with `a ∈ J`. -/
theorem mem_closure_smul_of_inner_self_mem {J : TwoSidedIdeal A} {x : E} (hx : inner A x x ∈ J) :
    x ∈ closure {y : E | ∃ a ∈ J, a • x = y} :=
  have := J.isClosed_topologicalClosure
  closure_smul_topologicalClosure_subset J x
    (mem_closure_smul_of_isClosed (J.le_topologicalClosure hx))

/-- `x ∈ idealSubmodule J E` if and only if `x` lies in the closure of `{a • x | a ∈ J}` (no linear
combinations needed). -/
theorem mem_idealSubmodule_iff_mem_closure {J : TwoSidedIdeal A} {x : E} :
    x ∈ idealSubmodule J E ↔ x ∈ closure {y : E | ∃ a ∈ J, a • x = y} :=
  ⟨fun hx => have := J.isClosed_topologicalClosure
    closure_smul_topologicalClosure_subset J x
      (mem_closure_smul_of_isClosed
        (mem_idealSubmodule_iff.mp (idealSubmodule_mono J.le_topologicalClosure hx))),
   fun hx => by
    rw [← SetLike.mem_coe, coe_idealSubmodule]
    exact closure_mono (by rintro _ ⟨a, ha, rfl⟩; exact Submodule.subset_span ⟨a, ha, x, rfl⟩) hx⟩

/-- For closed ideals `J₁` and `J₂`,
`idealSubmodule (J₁ ⊓ J₂) E = idealSubmodule J₁ E ⊓ idealSubmodule J₂ E`. -/
theorem idealSubmodule_inf (J₁ J₂ : TwoSidedIdeal A) [IsClosed (J₁ : Set A)]
    [IsClosed (J₂ : Set A)] :
    idealSubmodule (J₁ ⊓ J₂) E = idealSubmodule J₁ E ⊓ idealSubmodule J₂ E := by
  ext x
  rw [mem_idealSubmodule_iff, TwoSidedIdeal.mem_inf, Submodule.mem_inf, mem_idealSubmodule_iff,
    mem_idealSubmodule_iff]

end Characterization

section RightCharacterization

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  {J : TwoSidedIdeal A} [IsClosed (J : Set A)]

/-- Right-module form: for a closed two-sided ideal `J` of `A` and `CStarModule Aᵐᵒᵖ E`,
`x ∈ idealSubmodule J.op E` if and only if `⟨x, x⟩_A = unop (inner Aᵐᵒᵖ x x) ∈ J`. -/
theorem mem_idealSubmodule_op_iff {x : E} :
    x ∈ idealSubmodule J.op E ↔ unop (inner Aᵐᵒᵖ x x) ∈ J :=
  (mem_idealSubmodule_iff (J := J.op)).trans TwoSidedIdeal.mem_op_iff

theorem coe_idealSubmodule_op_eq_setOf (J : TwoSidedIdeal A) [IsClosed (J : Set A)] :
    (idealSubmodule J.op E : Set E) = {x : E | unop (inner Aᵐᵒᵖ x x) ∈ J} :=
  Set.ext fun _ => mem_idealSubmodule_op_iff

end RightCharacterization

/-! ### Quotient action, inner product, norm formula, and `CStarModule` structure -/

section QuotientModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]

/-- Induced `(A ⧸ J)`-action on `E ⧸ idealSubmodule J E`, given on representatives by
`mk J a • mk x = mk (a • x)`. -/
instance instSMulQuotient (J : TwoSidedIdeal A) : SMul (A ⧸ J) (E ⧸ idealSubmodule J E) where
  smul q v := Quotient.liftOn₂' q v (fun a z => Submodule.Quotient.mk (a • z))
    fun a₁ z₁ a₂ z₂ ha hz => by
      rw [TwoSidedIdeal.quotientRel_def] at ha
      rw [Submodule.quotientRel_def] at hz
      rw [Submodule.Quotient.eq, show a₁ • z₁ - a₂ • z₂ = (a₁ - a₂) • z₁ + a₂ • (z₁ - z₂) by
        rw [← smulCLM_apply a₂ (z₁ - z₂), (smulCLM a₂).map_sub, smulCLM_apply, smulCLM_apply,
          CStarModule.sub_smul, sub_add_sub_cancel]]
      exact (idealSubmodule J E).add_mem (smul_mem_idealSubmodule ha z₁)
        (coeff_smul_mem_idealSubmodule a₂ hz)

@[simp]
theorem mk_smul_mk (J : TwoSidedIdeal A) (a : A) (x : E) :
    TwoSidedIdeal.Quotient.mk J a • (Submodule.Quotient.mk x : E ⧸ idealSubmodule J E) =
      Submodule.Quotient.mk (a • x) := by
  rw [← TwoSidedIdeal.Quotient.quotientAddGroupMk_eq_mk]; rfl

/-- For any positive contractive element `e ∈ J`, adjusting the representative `x` to `x - e • x`
yields the squared quotient-norm estimate `‖mk x‖ ^ 2 ≤ ‖⟪x, x⟫_A + z‖ + ‖z - z * e‖` via
`TauCeti.CStarAlgebra.norm_sub_mul_sq_le` applied to `|x| = CFC.sqrt ⟪x, x⟫_A`. -/
private theorem norm_mk_idealSubmodule_sq_le_of_mem {J : TwoSidedIdeal A} {e : A}
    (heJ : e ∈ J) (he₀ : 0 ≤ e) (he₁ : ‖e‖ ≤ 1) (x : E) (z : A) :
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ^ 2 ≤
      ‖inner A x x + z‖ + ‖z - z * e‖ := by
  set s := CFC.sqrt (inner A x x)
  have hs_star : star s = s := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hs_mul : star s * s = inner A x x :=
    hs_star.symm ▸ CFC.sqrt_mul_sqrt_self _ inner_self_nonneg
  have he_star : star e = e := (IsSelfAdjoint.of_nonneg he₀).star_eq
  have hq_eq : (Submodule.Quotient.mk x : E ⧸ idealSubmodule J E) =
      Submodule.Quotient.mk (x - e • x) := by
    symm
    rw [Submodule.Quotient.eq, sub_sub_cancel_left, neg_mem_iff]
    exact smul_mem_idealSubmodule heJ x
  have hnorm_le : ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ≤ ‖s - s * e‖ := by
    have h1 : ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ≤ ‖x - e • x‖ := by
      rw [hq_eq]
      exact Submodule.Quotient.norm_mk_le (idealSubmodule J E) _
    refine h1.trans_eq ?_
    rw [norm_sub_rev, norm_smul_sub_self, norm_sub_rev, ← norm_star, star_sub, star_mul,
      hs_star, he_star]
  calc
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ^ 2
        ≤ ‖s - s * e‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
    _ ≤ ‖star s * s + z‖ + ‖z - z * e‖ :=
      TauCeti.CStarAlgebra.norm_sub_mul_sq_le he₀ he₁ s z
    _ = ‖inner A x x + z‖ + ‖z - z * e‖ := by rw [hs_mul]

section ClosedQuotient

variable (J : TwoSidedIdeal A) [IsClosed (J : Set A)]

/-- Induced `(A ⧸ J)`-valued inner product on `E ⧸ idealSubmodule J E` for a closed two-sided ideal
`J`, given on representatives by `⟪mk x, mk y⟫_{A ⧸ J} = mk J ⟪x, y⟫_A`. -/
instance instInnerQuotient : Inner (A ⧸ J) (E ⧸ idealSubmodule J E) where
  inner u v := Quotient.liftOn₂' u v (fun x y => TwoSidedIdeal.Quotient.mk J (inner A x y))
    fun x₁ y₁ x₂ y₂ hx hy => by
      rw [Submodule.quotientRel_def] at hx hy
      rw [TwoSidedIdeal.Quotient.eq]
      have hsplit : inner A x₁ y₁ - inner A x₂ y₂ =
          inner A (x₁ - x₂) y₁ + inner A x₂ (y₁ - y₂) := by
        rw [inner_sub_left, inner_sub_right, sub_add_sub_cancel]
      rw [hsplit]
      exact J.add_mem (inner_mem_of_mem_idealSubmodule_left hx y₁)
        (inner_mem_of_mem_idealSubmodule_right x₂ hy)

@[simp]
theorem inner_mk_mk (x y : E) :
    inner (A ⧸ J) (Submodule.Quotient.mk x : E ⧸ idealSubmodule J E) (Submodule.Quotient.mk y) =
      TwoSidedIdeal.Quotient.mk J (inner A x y) := (rfl)

/-- Upper bound in the quotient norm formula: `‖mk x‖ ^ 2 ≤ ‖mk J ⟪x, x⟫_A‖`, obtained by taking
the limit of `norm_mk_idealSubmodule_sq_le_of_mem` along an increasing approximate unit of `J` and
then the infimum over `z ∈ J`. -/
private theorem norm_mk_idealSubmodule_sq_le (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ^ 2 ≤
      ‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖ := by
  rw [TwoSidedIdeal.Quotient.norm_mk_eq J (inner A x x)]
  refine le_csInf ⟨‖inner A x x + 0‖, 0, J.zero_mem, rfl⟩ ?_
  rintro _ ⟨z, hz, rfl⟩
  let S := J.toNonUnitalStarSubalgebra
  let l : Filter S := CStarAlgebra.approximateUnit S
  have hl : l.IsIncreasingApproximateUnit := CStarAlgebra.increasingApproximateUnit S
  have := hl.neBot
  let z' : S := ⟨z, J.mem_toNonUnitalStarSubalgebra.mpr hz⟩
  have hz_lim : Tendsto (fun e : S => ‖inner A x x + z‖ + ‖(z' - z' * e : S)‖) l
      (𝓝 ‖inner A x x + z‖) := by
    simpa only [add_zero, norm_sub_rev] using tendsto_const_nhds.add
      (tendsto_iff_norm_sub_tendsto_zero.mp (hl.tendsto_mul_left z'))
  refine ge_of_tendsto hz_lim ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he₀ he₁
  simpa only [AddSubgroupClass.coe_norm, AddSubgroupClass.coe_sub, MulMemClass.coe_mul] using
    norm_mk_idealSubmodule_sq_le_of_mem (J.mem_toNonUnitalStarSubalgebra.mp e.property)
      (Subtype.coe_le_coe.mpr he₀) (by simpa only [AddSubgroupClass.coe_norm] using he₁) x z

/-- Lower bound in the quotient norm formula: `‖mk J ⟪x, x⟫_A‖ ≤ ‖mk x‖ ^ 2`, obtained by lifting
`mk x` to representatives with norm arbitrarily close to `‖mk x‖`. -/
private theorem norm_mk_inner_le_norm_mk_idealSubmodule_sq (x : E) :
    ‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖ ≤
      ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ^ 2 := by
  set q : E ⧸ idealSubmodule J E := Submodule.Quotient.mk x
  have hle : √‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖ ≤ ‖q‖ := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨y, hy, hlt⟩ := Submodule.Quotient.norm_mk_lt q hε
    have hinner : TwoSidedIdeal.Quotient.mk J (inner A x x) =
        TwoSidedIdeal.Quotient.mk J (inner A y y) := by
      rw [← inner_mk_mk J x x, ← inner_mk_mk J y y, hy]
    calc
      √‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖
          = √‖TwoSidedIdeal.Quotient.mk J (inner A y y)‖ := by rw [hinner]
      _ ≤ √‖inner A y y‖ := Real.sqrt_le_sqrt (TwoSidedIdeal.Quotient.norm_mk_le J _)
      _ = ‖y‖ := (norm_eq_sqrt_norm_inner_self (A := A) y).symm
      _ ≤ ‖q‖ + ε := hlt.le
  calc
    ‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖
        = √‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖ ^ 2 :=
          (Real.sq_sqrt (norm_nonneg _)).symm
    _ ≤ ‖q‖ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2

/-- Squared quotient norm formula on `E ⧸ idealSubmodule J E`:
`‖mk x‖ ^ 2 = ‖mk J ⟪x, x⟫_A‖`. -/
theorem norm_mk_idealSubmodule_sq (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ ^ 2 =
      ‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖ :=
  le_antisymm (norm_mk_idealSubmodule_sq_le J x) (norm_mk_inner_le_norm_mk_idealSubmodule_sq J x)

/-- Quotient norm formula on `E ⧸ idealSubmodule J E`:
`‖mk x‖ = √‖mk J ⟪x, x⟫_A‖`. -/
theorem norm_mk_idealSubmodule (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J E)‖ =
      √‖TwoSidedIdeal.Quotient.mk J (inner A x x)‖ :=
  by rw [← norm_mk_idealSubmodule_sq J x, Real.sqrt_sq (norm_nonneg _)]

/-- For any closed two-sided ideal `J` of `A`, `E ⧸ idealSubmodule J E` is a Hilbert
`(A ⧸ J)`-module with respect to any `StarOrderedRing` partial order on `A ⧸ J` (such as
`CStarAlgebra.spectralOrder (A ⧸ J)`). -/
noncomputable instance instCStarModuleQuotient [PartialOrder (A ⧸ J)] [StarOrderedRing (A ⧸ J)] :
    CStarModule (A ⧸ J) (E ⧸ idealSubmodule J E) where
  toInner := inferInstance
  inner_add_right {u v w} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_add, inner_mk_mk, inner_mk_mk, inner_mk_mk, inner_add_right,
      map_add]
  inner_self_nonneg {u} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [inner_mk_mk, ← TwoSidedIdeal.Quotient.mkStarAlgHom_apply,
      ← map_zero (TwoSidedIdeal.Quotient.mkStarAlgHom J)]
    exact OrderHomClass.mono (TwoSidedIdeal.Quotient.mkStarAlgHom J) inner_self_nonneg
  inner_self {u} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [inner_mk_mk, TwoSidedIdeal.Quotient.eq_zero_iff_mem, ← mem_idealSubmodule_iff,
      Submodule.Quotient.mk_eq_zero]
  inner_op_smul_right {q u v} := by
    obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective J q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [mk_smul_mk, inner_mk_mk, inner_mk_mk, inner_op_smul_right, map_mul]
  inner_smul_right_complex {c u v} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [← Submodule.Quotient.mk_smul, inner_mk_mk, inner_mk_mk, inner_smul_right_complex,
      TwoSidedIdeal.Quotient.mk_smul_complex]
  star_inner u v := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [inner_mk_mk, inner_mk_mk, ← TwoSidedIdeal.Quotient.mk_star, star_inner]
  norm_eq_sqrt_norm_inner_self u := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [inner_mk_mk]
    exact norm_mk_idealSubmodule J x

end ClosedQuotient

end QuotientModule

section RightQuotientModule

variable {A E : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]

/-- Induced right `(A ⧸ J)`-action on `E ⧸ idealSubmodule J.op E` for a right Hilbert `A`-module
`CStarModule Aᵐᵒᵖ E`, transported from `Aᵐᵒᵖ ⧸ J.op` via `TwoSidedIdeal.Quotient.opEquiv`. -/
noncomputable instance instSMulQuotientMulOpposite (J : TwoSidedIdeal A) :
    SMul (A ⧸ J)ᵐᵒᵖ (E ⧸ idealSubmodule J.op E) where
  smul u v := TwoSidedIdeal.Quotient.opEquiv J u • v

@[simp]
theorem op_mk_smul_mk (J : TwoSidedIdeal A) (a : A) (x : E) :
    op (TwoSidedIdeal.Quotient.mk J a) • (Submodule.Quotient.mk x : E ⧸ idealSubmodule J.op E) =
      Submodule.Quotient.mk (op a • x) := by
  -- Unfold `instSMulQuotientMulOpposite.smul` to the action transported along `opEquiv J`;
  -- this lemma is the defining computation rule, so no rewrite lemma can unfold `•` here.
  change TwoSidedIdeal.Quotient.opEquiv J (op (TwoSidedIdeal.Quotient.mk J a)) •
    (Submodule.Quotient.mk x : E ⧸ idealSubmodule J.op E) = _
  rw [TwoSidedIdeal.Quotient.opEquiv_op_mk, mk_smul_mk]

variable (J : TwoSidedIdeal A) [IsClosed (J : Set A)]

/-- Induced `(A ⧸ J)ᵐᵒᵖ`-valued inner product on `E ⧸ idealSubmodule J.op E` for a closed two-sided
ideal `J`, whose `unop` is `mk J ⟨x, y⟩_A`. -/
noncomputable instance instInnerQuotientMulOpposite :
    Inner (A ⧸ J)ᵐᵒᵖ (E ⧸ idealSubmodule J.op E) where
  inner u v := (TwoSidedIdeal.Quotient.opEquiv J).symm (inner (Aᵐᵒᵖ ⧸ J.op) u v)

@[simp]
theorem unop_inner_mk_mk (x y : E) :
    unop (inner (A ⧸ J)ᵐᵒᵖ (Submodule.Quotient.mk x : E ⧸ idealSubmodule J.op E)
      (Submodule.Quotient.mk y)) =
      TwoSidedIdeal.Quotient.mk J (unop (inner Aᵐᵒᵖ x y)) := by
  -- Unfold `instInnerQuotientMulOpposite.inner` to the inner product transported along
  -- `(opEquiv J).symm`; this lemma is the defining computation rule, so no rewrite lemma can
  -- unfold `inner` here.
  change unop ((TwoSidedIdeal.Quotient.opEquiv J).symm
    (inner (Aᵐᵒᵖ ⧸ J.op) (Submodule.Quotient.mk x) (Submodule.Quotient.mk y))) = _
  rw [inner_mk_mk, TwoSidedIdeal.Quotient.opEquiv_symm_mk, unop_op]

theorem norm_mk_idealSubmodule_op_sq (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J.op E)‖ ^ 2 =
      ‖TwoSidedIdeal.Quotient.mk J (unop (inner Aᵐᵒᵖ x x))‖ := by
  rw [norm_mk_idealSubmodule_sq J.op x]
  have heq : TwoSidedIdeal.Quotient.mk J.op (inner Aᵐᵒᵖ x x) =
      TwoSidedIdeal.Quotient.opStarAlgEquiv J
        (op (TwoSidedIdeal.Quotient.mk J (unop (inner Aᵐᵒᵖ x x)))) := by
    rw [TwoSidedIdeal.Quotient.opStarAlgEquiv_op_mk, op_unop]
  rw [heq, (StarAlgEquiv.isometry (TwoSidedIdeal.Quotient.opStarAlgEquiv J)).norm_map_of_map_zero
    (map_zero _), norm_op]

theorem norm_mk_idealSubmodule_op (x : E) :
    ‖(Submodule.Quotient.mk x : E ⧸ idealSubmodule J.op E)‖ =
      √‖TwoSidedIdeal.Quotient.mk J (unop (inner Aᵐᵒᵖ x x))‖ :=
  by rw [← norm_mk_idealSubmodule_op_sq J x, Real.sqrt_sq (norm_nonneg _)]

/-- Right Hilbert `(A ⧸ J)`-module structure on `E ⧸ idealSubmodule J.op E` for a closed two-sided
ideal `J` of `A`. -/
noncomputable instance instCStarModuleQuotientMulOpposite [PartialOrder (A ⧸ J)]
    [StarOrderedRing (A ⧸ J)] :
    CStarModule (A ⧸ J)ᵐᵒᵖ (E ⧸ idealSubmodule J.op E) where
  toInner := inferInstance
  inner_add_right {u v w} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    exact unop_injective (by
      rw [← Submodule.Quotient.mk_add, unop_inner_mk_mk, unop_add, unop_inner_mk_mk,
        unop_inner_mk_mk, inner_add_right, unop_add, map_add])
  inner_self_nonneg {u} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [← unop_nonneg, unop_inner_mk_mk, ← TwoSidedIdeal.Quotient.mkStarAlgHom_apply,
      ← map_zero (TwoSidedIdeal.Quotient.mkStarAlgHom J)]
    exact OrderHomClass.mono (TwoSidedIdeal.Quotient.mkStarAlgHom J)
      (unop_nonneg.mpr (inner_self_nonneg (A := Aᵐᵒᵖ) (x := x)))
  inner_self {u} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [← unop_eq_zero_iff, unop_inner_mk_mk, TwoSidedIdeal.Quotient.eq_zero_iff_mem,
      ← mem_idealSubmodule_op_iff, Submodule.Quotient.mk_eq_zero]
  inner_op_smul_right {q u v} := by
    obtain ⟨q, rfl⟩ := op_surjective q
    obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective J q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact unop_injective (by
      rw [op_mk_smul_mk, unop_inner_mk_mk, unop_mul, unop_op, unop_inner_mk_mk,
        inner_op_smul_right, unop_mul, unop_op, map_mul])
  inner_smul_right_complex {c u v} := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact unop_injective (by
      rw [← Submodule.Quotient.mk_smul, unop_inner_mk_mk, unop_smul, unop_inner_mk_mk,
        inner_smul_right_complex, unop_smul, TwoSidedIdeal.Quotient.mk_smul_complex])
  star_inner u v := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact unop_injective (by
      rw [unop_star, unop_inner_mk_mk, unop_inner_mk_mk, ← TwoSidedIdeal.Quotient.mk_star,
        ← unop_star, star_inner])
  norm_eq_sqrt_norm_inner_self u := by
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    rw [← norm_unop, unop_inner_mk_mk]; exact norm_mk_idealSubmodule_op J x

end RightQuotientModule

/-! ### Functoriality in `E` and in `J` -/

section FunctorialityTopological

variable {A : Type*} [NonUnitalNonAssocRing A]

section Map

variable {E F G : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℂ E] [ContinuousAdd E]
  [ContinuousConstSMul ℂ E] [SMul A E]
  [TopologicalSpace F] [AddCommGroup F] [Module ℂ F] [ContinuousAdd F]
  [ContinuousConstSMul ℂ F] [SMul A F]
  [TopologicalSpace G] [AddCommGroup G] [Module ℂ G] [ContinuousAdd G]
  [ContinuousConstSMul ℂ G] [SMul A G]

/-- Any continuous `ℂ`-linear map commuting with the `A`-action maps `idealSubmodule J E` into
`idealSubmodule J F`. -/
theorem map_mem_idealSubmodule (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) {z : E} (hz : z ∈ idealSubmodule J E) :
    T z ∈ idealSubmodule J F := by
  let S : Submodule ℂ E := (idealSubmodule J F).comap T.toLinearMap
  have hS : IsClosed (S : Set E) := (isClosed_idealSubmodule J F).preimage T.continuous
  have hle : idealSubmodule J E ≤ S := (idealSubmodule_le_iff hS).mpr fun a ha x => by
    rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe, hT]
    exact smul_mem_idealSubmodule ha (T x)
  exact hle hz

/-- Descend a continuous `ℂ`-linear map `T : E →L[ℂ] F` commuting with the `A`-action to the
quotients `E ⧸ idealSubmodule J E →L[ℂ] F ⧸ idealSubmodule J F`. For right modules, apply this at
`J.op`. -/
def quotientMapCLM (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    E ⧸ idealSubmodule J E →L[ℂ] F ⧸ idealSubmodule J F :=
  (idealSubmodule J E).liftQL ((idealSubmodule J F).mkQL.comp T) fun z hz => by
    simpa [Submodule.Quotient.mk_eq_zero] using map_mem_idealSubmodule J T hT hz

@[simp]
theorem quotientMapCLM_mk (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) (x : E) :
    quotientMapCLM J T hT (Submodule.Quotient.mk x) = Submodule.Quotient.mk (T x) := (rfl)

@[simp]
theorem quotientMapCLM_id (J : TwoSidedIdeal A) :
    quotientMapCLM J (ContinuousLinearMap.id ℂ E) (fun _ _ => rfl) =
      ContinuousLinearMap.id ℂ (E ⧸ idealSubmodule J E) := by
  ext v; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v; rfl

@[simp]
theorem quotientMapCLM_comp (J : TwoSidedIdeal A) (S : F →L[ℂ] G)
    (hS : ∀ (a : A) (y : F), S (a • y) = a • S y) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    quotientMapCLM J (S.comp T) (fun a x => by simp [hT, hS]) =
      (quotientMapCLM J S hS).comp (quotientMapCLM J T hT) := by
  ext v; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v; rfl

/-- Canonical continuous `ℂ`-linear quotient map
`E ⧸ idealSubmodule J₁ E →L[ℂ] E ⧸ idealSubmodule J₂ E` induced by an inclusion `J₁ ≤ J₂` of
two-sided ideals. -/
def quotientFactorCLM {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂) :
    E ⧸ idealSubmodule J₁ E →L[ℂ] E ⧸ idealSubmodule J₂ E :=
  (idealSubmodule J₁ E).liftQL (idealSubmodule J₂ E).mkQL fun z hz => by
    simpa [Submodule.Quotient.mk_eq_zero] using idealSubmodule_mono h hz

@[simp]
theorem quotientFactorCLM_mk {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂) (x : E) :
    quotientFactorCLM h (Submodule.Quotient.mk x : E ⧸ idealSubmodule J₁ E) =
      Submodule.Quotient.mk x := (rfl)

theorem quotientFactorCLM_surjective {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂) :
    Function.Surjective (quotientFactorCLM (E := E) h) := fun u =>
  let ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ u; ⟨Submodule.Quotient.mk x, hx⟩

@[simp]
theorem quotientFactorCLM_refl (J : TwoSidedIdeal A) :
    quotientFactorCLM (E := E) (le_refl J) =
      ContinuousLinearMap.id ℂ (E ⧸ idealSubmodule J E) := by
  ext u; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u; rfl

@[simp]
theorem quotientFactorCLM_comp {J₁ J₂ J₃ : TwoSidedIdeal A} (h₁ : J₁ ≤ J₂) (h₂ : J₂ ≤ J₃) :
    (quotientFactorCLM (E := E) h₂).comp (quotientFactorCLM h₁) =
      quotientFactorCLM (h₁.trans h₂) := by
  ext u; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u; rfl

/-- Naturality of `quotientMapCLM` and `quotientFactorCLM`: functoriality in `E` and in `J`
commute. -/
theorem quotientFactorCLM_comp_quotientMapCLM {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂)
    (T : E →L[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    (quotientFactorCLM h).comp (quotientMapCLM J₁ T hT) =
      (quotientMapCLM J₂ T hT).comp (quotientFactorCLM h) := by
  ext u; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u; rfl

end Map

section Seminormed

variable {E F : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E]
  [SeminormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F]

/-- Passing to the quotient modulo `E J` does not increase operator norm:
`‖quotientMapCLM J T hT‖ ≤ ‖T‖`. -/
theorem norm_quotientMapCLM_le (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) :
    ‖quotientMapCLM J T hT‖ ≤ ‖T‖ :=
  ((idealSubmodule J E).norm_liftQL_le ((idealSubmodule J F).mkQL.comp T) _).trans
    ((idealSubmodule J F).norm_mkQL_comp_le T)

theorem norm_quotientMapCLM_apply_le (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) (v : E ⧸ idealSubmodule J E) :
    ‖quotientMapCLM J T hT v‖ ≤ ‖T‖ * ‖v‖ :=
  ((quotientMapCLM J T hT).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_quotientMapCLM_le J T hT) (norm_nonneg v))

theorem norm_quotientFactorCLM_le {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂) :
    ‖quotientFactorCLM (E := E) h‖ ≤ 1 :=
  ((idealSubmodule J₁ E).norm_liftQL_le (idealSubmodule J₂ E).mkQL _).trans
    (idealSubmodule J₂ E).norm_mkQL_le

theorem norm_quotientFactorCLM_apply_le {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂)
    (u : E ⧸ idealSubmodule J₁ E) :
    ‖quotientFactorCLM h u‖ ≤ ‖u‖ :=
  ((quotientFactorCLM h).le_opNorm u).trans <| by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (norm_quotientFactorCLM_le h) (norm_nonneg u)

end Seminormed

end FunctorialityTopological

section FunctorialityCStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

section LeftModules

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul A E] [CStarModule A E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul A F] [CStarModule A F]

/-- `quotientMapCLM J T hT` is `(A ⧸ J)`-linear. -/
theorem quotientMapCLM_smul (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (a : A) (x : E), T (a • x) = a • T x) (q : A ⧸ J) (v : E ⧸ idealSubmodule J E) :
    quotientMapCLM J T hT (q • v) = q • quotientMapCLM J T hT v := by
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective J q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [mk_smul_mk, quotientMapCLM_mk, hT, quotientMapCLM_mk, mk_smul_mk]

/-- An `A`-linear map preserving `A`-valued inner products induces an inner-product-preserving map
on `E ⧸ idealSubmodule J E`. -/
theorem inner_quotientMapCLM_of_inner_eq (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    (T : E →L[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x)
    (hinner : ∀ x y : E, inner A (T x) (T y) = inner A x y)
    (u v : E ⧸ idealSubmodule J E) :
    inner (A ⧸ J) (quotientMapCLM J T hT u) (quotientMapCLM J T hT v) = inner (A ⧸ J) u v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [quotientMapCLM_mk, quotientMapCLM_mk, inner_mk_mk, inner_mk_mk, hinner]

/-- An `A`-linear map preserving `A`-valued inner products descends to an isometry on quotients. -/
theorem isometry_quotientMapCLM (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    (T : E →L[ℂ] F) (hT : ∀ (a : A) (x : E), T (a • x) = a • T x)
    (hinner : ∀ x y : E, inner A (T x) (T y) = inner A x y) :
    Isometry (quotientMapCLM J T hT) := by
  refine AddMonoidHomClass.isometry_of_norm _ fun u => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [quotientMapCLM_mk, norm_mk_idealSubmodule, norm_mk_idealSubmodule, hinner]

/-- Pointwise adjoint identity on quotients, without requiring an order on `A ⧸ J`: if `T` and `S`
commute with the `A`-action and satisfy `⟪T x, y⟫_A = ⟪x, S y⟫_A`, then
`⟪quotientMapCLM J T hT u, v⟫_{A ⧸ J} = ⟪u, quotientMapCLM J S hS v⟫_{A ⧸ J}`. -/
theorem inner_quotientMapCLM_adjoint (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    {T : E →L[ℂ] F} (hT : ∀ (a : A) (x : E), T (a • x) = a • T x)
    {S : F →L[ℂ] E} (hS : ∀ (a : A) (y : F), S (a • y) = a • S y)
    (hinner : ∀ (x : E) (y : F), inner A (T x) y = inner A x (S y))
    (u : E ⧸ idealSubmodule J E) (v : F ⧸ idealSubmodule J F) :
    inner (A ⧸ J) (quotientMapCLM J T hT u) v =
      inner (A ⧸ J) u (quotientMapCLM J S hS v) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [quotientMapCLM_mk, quotientMapCLM_mk, inner_mk_mk, inner_mk_mk, hinner]

/-- Adjoint pairs of bounded operators between Hilbert `A`-modules descend to adjoint pairs between
the quotient Hilbert `(A ⧸ J)`-modules. -/
theorem isAdjointPair_quotientMapCLM (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    [PartialOrder (A ⧸ J)] [StarOrderedRing (A ⧸ J)]
    {T : E →L[ℂ] F} {S : F →L[ℂ] E}
    (h : LinearMap.IsAdjointPair (innerₛₗ (A := A) (E := E)).flip
      (innerₛₗ (A := A) (E := F)).flip T S) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := A ⧸ J) (E := E ⧸ idealSubmodule J E)).flip
      (innerₛₗ (A := A ⧸ J) (E := F ⧸ idealSubmodule J F)).flip
      (quotientMapCLM J T h.map_smul_coeff_cstarModule)
      (quotientMapCLM J S h.symm_cstarModule.map_smul_coeff_cstarModule) :=
  isAdjointPair_inner_iff.mpr <|
    inner_quotientMapCLM_adjoint J h.map_smul_coeff_cstarModule
      h.symm_cstarModule.map_smul_coeff_cstarModule h.inner_eq_cstarModule

/-- `quotientFactorCLM h` intertwines the quotient actions along `TwoSidedIdeal.Quotient.factor h`.
-/
theorem quotientFactorCLM_smul {J₁ J₂ : TwoSidedIdeal A} (h : J₁ ≤ J₂) (q : A ⧸ J₁)
    (u : E ⧸ idealSubmodule J₁ E) :
    quotientFactorCLM h (q • u) =
      TwoSidedIdeal.Quotient.factor h q • quotientFactorCLM h u := by
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective J₁ q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [mk_smul_mk, quotientFactorCLM_mk, TwoSidedIdeal.Quotient.factor_mk, quotientFactorCLM_mk,
    mk_smul_mk]

/-- `quotientFactorCLM h` intertwines the quotient inner products along
`TwoSidedIdeal.Quotient.factorStarAlgHom h`. -/
theorem inner_quotientFactorCLM {J₁ J₂ : TwoSidedIdeal A} [IsClosed (J₁ : Set A)]
    [IsClosed (J₂ : Set A)] (h : J₁ ≤ J₂) (u v : E ⧸ idealSubmodule J₁ E) :
    inner (A ⧸ J₂) (quotientFactorCLM h u) (quotientFactorCLM h v) =
      TwoSidedIdeal.Quotient.factorStarAlgHom h (inner (A ⧸ J₁) u v) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [quotientFactorCLM_mk, quotientFactorCLM_mk, inner_mk_mk, inner_mk_mk,
    TwoSidedIdeal.Quotient.factorStarAlgHom_mk]

end LeftModules

section RightModules

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Aᵐᵒᵖ E] [CStarModule Aᵐᵒᵖ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Aᵐᵒᵖ F] [CStarModule Aᵐᵒᵖ F]

/-- Right-module `(A ⧸ J)ᵐᵒᵖ`-linearity of `quotientMapCLM J.op T hT`. -/
theorem quotientMapCLM_op_smul (J : TwoSidedIdeal A) (T : E →L[ℂ] F)
    (hT : ∀ (u : Aᵐᵒᵖ) (x : E), T (u • x) = u • T x) (q : (A ⧸ J)ᵐᵒᵖ)
    (v : E ⧸ idealSubmodule J.op E) :
    quotientMapCLM J.op T hT (q • v) = q • quotientMapCLM J.op T hT v := by
  obtain ⟨q, rfl⟩ := op_surjective q
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective J q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [op_mk_smul_mk, quotientMapCLM_mk, hT, quotientMapCLM_mk, op_mk_smul_mk]

/-- A right `A`-linear map preserving `Aᵐᵒᵖ`-valued inner products preserves the transported
`(A ⧸ J)ᵐᵒᵖ`-valued inner product on right quotients. -/
theorem inner_quotientMapCLM_op_of_inner_eq (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    (T : E →L[ℂ] F) (hT : ∀ (u : Aᵐᵒᵖ) (x : E), T (u • x) = u • T x)
    (hinner : ∀ x y : E, inner Aᵐᵒᵖ (T x) (T y) = inner Aᵐᵒᵖ x y)
    (u v : E ⧸ idealSubmodule J.op E) :
    inner (A ⧸ J)ᵐᵒᵖ (quotientMapCLM J.op T hT u) (quotientMapCLM J.op T hT v) =
      inner (A ⧸ J)ᵐᵒᵖ u v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact unop_injective (by
    rw [quotientMapCLM_mk, quotientMapCLM_mk, unop_inner_mk_mk, unop_inner_mk_mk, hinner])

/-- Pointwise adjoint identity on right quotients, without requiring an order on `A ⧸ J`. -/
theorem inner_quotientMapCLM_op_adjoint (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    {T : E →L[ℂ] F} (hT : ∀ (u : Aᵐᵒᵖ) (x : E), T (u • x) = u • T x)
    {S : F →L[ℂ] E} (hS : ∀ (u : Aᵐᵒᵖ) (y : F), S (u • y) = u • S y)
    (hinner : ∀ (x : E) (y : F), inner Aᵐᵒᵖ (T x) y = inner Aᵐᵒᵖ x (S y))
    (u : E ⧸ idealSubmodule J.op E) (v : F ⧸ idealSubmodule J.op F) :
    inner (A ⧸ J)ᵐᵒᵖ (quotientMapCLM J.op T hT u) v =
      inner (A ⧸ J)ᵐᵒᵖ u (quotientMapCLM J.op S hS v) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact unop_injective (by
    rw [quotientMapCLM_mk, quotientMapCLM_mk, unop_inner_mk_mk, unop_inner_mk_mk, hinner])

/-- Adjoint pairs of bounded operators between right Hilbert `A`-modules descend to adjoint pairs
between the right quotient Hilbert `(A ⧸ J)`-modules. -/
theorem isAdjointPair_quotientMapCLM_op (J : TwoSidedIdeal A) [IsClosed (J : Set A)]
    [PartialOrder (A ⧸ J)] [StarOrderedRing (A ⧸ J)]
    {T : E →L[ℂ] F} {S : F →L[ℂ] E}
    (h : LinearMap.IsAdjointPair (innerₛₗ (A := Aᵐᵒᵖ) (E := E)).flip
      (innerₛₗ (A := Aᵐᵒᵖ) (E := F)).flip T S) :
    LinearMap.IsAdjointPair
      (innerₛₗ (A := (A ⧸ J)ᵐᵒᵖ) (E := E ⧸ idealSubmodule J.op E)).flip
      (innerₛₗ (A := (A ⧸ J)ᵐᵒᵖ) (E := F ⧸ idealSubmodule J.op F)).flip
      (quotientMapCLM J.op T h.map_smul_coeff_cstarModule)
      (quotientMapCLM J.op S h.symm_cstarModule.map_smul_coeff_cstarModule) :=
  isAdjointPair_inner_iff.mpr <|
    inner_quotientMapCLM_op_adjoint J h.map_smul_coeff_cstarModule
      h.symm_cstarModule.map_smul_coeff_cstarModule h.inner_eq_cstarModule

/-- `quotientFactorCLM` at `J₁.op ≤ J₂.op` intertwines the right quotient actions along
`TwoSidedIdeal.Quotient.factor`. -/
theorem quotientFactorCLM_op_smul {J₁ J₂ : TwoSidedIdeal A} (h : J₁.op ≤ J₂.op)
    (q : (A ⧸ J₁)ᵐᵒᵖ) (u : E ⧸ idealSubmodule J₁.op E) :
    quotientFactorCLM h (q • u) =
      op (TwoSidedIdeal.Quotient.factor (TwoSidedIdeal.opOrderIso.le_iff_le.mp h) q.unop) •
        quotientFactorCLM h u := by
  obtain ⟨q, rfl⟩ := op_surjective q
  obtain ⟨a, rfl⟩ := TwoSidedIdeal.Quotient.mk_surjective J₁ q
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  rw [op_mk_smul_mk, quotientFactorCLM_mk, unop_op, TwoSidedIdeal.Quotient.factor_mk,
    quotientFactorCLM_mk, op_mk_smul_mk]

/-- `quotientFactorCLM` at `J₁.op ≤ J₂.op` intertwines the right quotient inner products along
`TwoSidedIdeal.Quotient.factorStarAlgHom`. -/
theorem inner_quotientFactorCLM_op {J₁ J₂ : TwoSidedIdeal A} [IsClosed (J₁ : Set A)]
    [IsClosed (J₂ : Set A)] (h : J₁.op ≤ J₂.op) (u v : E ⧸ idealSubmodule J₁.op E) :
    inner (A ⧸ J₂)ᵐᵒᵖ (quotientFactorCLM h u) (quotientFactorCLM h v) =
      op (TwoSidedIdeal.Quotient.factorStarAlgHom (TwoSidedIdeal.opOrderIso.le_iff_le.mp h)
        (unop (inner (A ⧸ J₁)ᵐᵒᵖ u v))) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  exact unop_injective (by
    rw [quotientFactorCLM_mk, quotientFactorCLM_mk, unop_op, unop_inner_mk_mk,
      unop_inner_mk_mk, TwoSidedIdeal.Quotient.factorStarAlgHom_mk])

end RightModules

end FunctorialityCStarModule

end CStarModule
