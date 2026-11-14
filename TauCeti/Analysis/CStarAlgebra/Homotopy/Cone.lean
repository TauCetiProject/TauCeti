/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Homotopy.Basic
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Star
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Tactic.FieldSimp

/-!
# Cone and suspension C⋆-algebras

For a non-unital complex C⋆-algebra `A`, the cone and suspension C⋆-algebras are
`CStarCone A := C₀(Set.Ioc (0 : ℝ) 1, A)` and `CStarSuspension A := C₀(Set.Ioo (0 : ℝ) 1, A)`,
equipped with the supremum norm and pointwise `⋆`-algebra operations (Blackadar,
*Operator Algebras*, II.5.5.10–II.5.5.11).

## Main declarations

* `ZeroAtInftyContinuousMap.equivKerEvalOfNotMemRangeIff` and
  `ZeroAtInftyContinuousMap.equivKerContinuousMapEvalOfNotMemRangeIff`: for an open embedding
  `e : X → Y` whose image complement is a singleton `{y₀}`, extension by zero identifies `C₀(X, A)`
  isometrically with the kernel ideal of evaluation at `y₀` in `C₀(Y, A)` (and in `C(Y, A)` when
  `Y` is compact).
* `TauCeti.CStarCone` and `TauCeti.CStarSuspension`: `C₀((0, 1], A)` and `C₀((0, 1), A)`.
* `TauCeti.CStarCone.toPath` and `TauCeti.CStarCone.equivKerEvalZero`: isometric `⋆`-embedding into
  `C(unitInterval, A)` and `⋆`-isomorphism onto the kernel of evaluation at `0`, together with the
  quotient `TauCeti.pathQuotientKerEvalZeroEquiv : C(unitInterval, A) ⧸ ker ev₀ ≃⋆ₐ[ℂ] A`.
* `TauCeti.CStarCone.evalOne`, `TauCeti.CStarCone.linearPath`,
  `TauCeti.CStarSuspension.toCone`, `TauCeti.CStarSuspension.equivKerEvalOne`, and
  `TauCeti.CStarCone.quotientKerEvalOneEquiv`: the exact sequence
  `0 → CStarSuspension A → CStarCone A → A → 0`.
* `TauCeti.CStarSuspension.equivReal`: orientation-preserving `⋆`-isomorphism
  `CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A)` via `t ↦ tan(π(t - 1/2))`.
* `TauCeti.CStarCone.map` and `TauCeti.CStarSuspension.map`: functoriality for `⋆`-homomorphisms.
* `TauCeti.CStarCone.contractionHomotopy`, `TauCeti.CStarCone.isContractible`, and
  `TauCeti.CStarSuspension.toCone_homotopic_zero`: explicit cone contraction
  `φ_t(f)(s) = f(s - t)` for `s > t` and `0` otherwise, and subcontractibility of the suspension.
* `TauCeti.CStarSuspension.not_isContractible_complex` and
  `TauCeti.not_isContractibleCStarAlgebra_c0_real`: `CStarSuspension ℂ` and `C₀(ℝ, ℂ)` are not
  contractible (proved via a quasi-unitary generator and `AddCircle.windingNumber`).

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.5.5.10–II.5.5.11.
-/

public section

open Filter Set Topology unitInterval
open scoped CStarAlgebra ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section KerEval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [R1Space Y]
  {e : X → Y} {y₀ : Y}

/-- When an open embedding `e : X → Y` into an `R₁` space misses only a single point `y₀`,
extension by zero identifies `C₀(X, A)` with `TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)`.
-/
noncomputable def equivKerEvalOfNotMemRangeIff (A : Type*) [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) :
    C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀) where
  toFun f := ⟨extendByZero he f, by
    rw [TwoSidedIdeal.mem_ker, evalNonUnitalStarAlgHom_apply]
    exact extendByZero_apply_of_notMem he f ((hcompl y₀).mpr rfl)⟩
  invFun g := restrictOfEqZero he.isEmbedding (g : C₀(Y, A)) fun y hy => by
    rw [(hcompl y).mp hy]
    have hg := (TwoSidedIdeal.mem_ker (evalNonUnitalStarAlgHom ℂ A y₀)).mp g.2
    rwa [evalNonUnitalStarAlgHom_apply] at hg
  left_inv f := restrictOfEqZero_extendByZero he f
  right_inv g := Subtype.ext (extendByZero_restrictOfEqZero he (g : C₀(Y, A)) _)
  map_mul' f₁ f₂ := Subtype.ext (extendByZero_mul he f₁ f₂)
  map_add' f₁ f₂ := Subtype.ext (extendByZero_add he f₁ f₂)
  map_smul' c f := Subtype.ext (extendByZero_smul he c f)
  map_star' f := Subtype.ext (extendByZero_star he f)

@[simp]
theorem coe_equivKerEvalOfNotMemRangeIff_apply {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) (f : C₀(X, A)) :
    ((equivKerEvalOfNotMemRangeIff A he hcompl f :
      TwoSidedIdeal.ker (evalNonUnitalStarAlgHom ℂ A y₀)) : C₀(Y, A)) = extendByZero he f :=
  (rfl)

/-- Compact-codomain variant of `equivKerEvalOfNotMemRangeIff` landing in the kernel of
`ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀` inside `C(Y, A)`. -/
noncomputable def equivKerContinuousMapEvalOfNotMemRangeIff [CompactSpace Y]
    (A : Type*) [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) :
    C₀(X, A) ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀) where
  toFun f := ⟨(extendByZero he f : C(Y, A)), by
    rw [TwoSidedIdeal.mem_ker, ContinuousMap.evalNonUnitalStarAlgHom_apply]
    exact extendByZero_apply_of_notMem he f ((hcompl y₀).mpr rfl)⟩
  invFun g := restrictOfEqZero he.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (g : C(Y, A))) fun y hy => by
      rw [(hcompl y).mp hy]
      have hg := (TwoSidedIdeal.mem_ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)).mp g.2
      rw [ContinuousMap.evalNonUnitalStarAlgHom_apply] at hg
      simpa using hg
  left_inv f := restrictOfEqZero_extendByZero he f
  right_inv g := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun
      (extendByZero_restrictOfEqZero he
        (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (g : C(Y, A))) _) y
  map_mul' f₁ f₂ := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_mul he f₁ f₂) y
  map_add' f₁ f₂ := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_add he f₁ f₂) y
  map_smul' c f := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_smul he c f) y
  map_star' f := Subtype.ext <| ContinuousMap.ext fun y =>
    DFunLike.congr_fun (extendByZero_star he f) y

@[simp]
theorem coe_equivKerContinuousMapEvalOfNotMemRangeIff_apply [CompactSpace Y]
    {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀) (f : C₀(X, A)) :
    ((equivKerContinuousMapEvalOfNotMemRangeIff A he hcompl f :
      TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) : C(Y, A)) =
      (extendByZero he f : C(Y, A)) :=
  (rfl)

@[simp]
theorem equivKerContinuousMapEvalOfNotMemRangeIff_symm_apply [CompactSpace Y]
    {A : Type*} [NonUnitalCStarAlgebra A]
    (he : IsOpenEmbedding e) (hcompl : ∀ y, y ∉ range e ↔ y = y₀)
    (g : TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A y₀)) (x : X) :
    (equivKerContinuousMapEvalOfNotMemRangeIff A he hcompl).symm g x = (g : C(Y, A)) (e x) :=
  restrictOfEqZero_apply he.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (g : C(Y, A))) _ x

end KerEval

end ZeroAtInftyContinuousMap

namespace TauCeti

section IntervalTopology

/-- Canonical inclusion `(0, 1] → [0, 1]`. -/
def iocToUnitInterval (x : Ioc (0 : ℝ) 1) : I :=
  ⟨x.1, Ioc_subset_Icc_self x.2⟩

@[simp]
theorem coe_iocToUnitInterval (x : Ioc (0 : ℝ) 1) : (iocToUnitInterval x : ℝ) = x.1 :=
  (rfl)

theorem continuous_iocToUnitInterval : Continuous iocToUnitInterval :=
  continuous_subtype_val.subtype_mk _

theorem range_iocToUnitInterval : range iocToUnitInterval = {(0 : I)}ᶜ := by
  ext t
  simp only [mem_range, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩ h0
    exact x.2.1.ne' (congrArg Subtype.val h0)
  · intro ht0
    have hpos : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 fun h => ht0 (Subtype.ext h.symm)
    exact ⟨⟨t.1, hpos, t.2.2⟩, rfl⟩

theorem notMem_range_iocToUnitInterval_iff (t : I) :
    t ∉ range iocToUnitInterval ↔ t = 0 := by
  rw [range_iocToUnitInterval, mem_compl_iff, mem_singleton_iff, not_not]

theorem isOpenEmbedding_iocToUnitInterval : IsOpenEmbedding iocToUnitInterval :=
  ⟨IsEmbedding.of_comp continuous_iocToUnitInterval continuous_subtype_val IsEmbedding.subtypeVal,
    range_iocToUnitInterval ▸ isOpen_compl_singleton⟩

/-- The endpoint `1` of `Set.Ioc (0 : ℝ) 1`. -/
def iocOne : Ioc (0 : ℝ) 1 :=
  ⟨1, right_mem_Ioc.mpr zero_lt_one⟩

@[simp]
theorem coe_iocOne : (iocOne : ℝ) = 1 :=
  (rfl)

@[simp]
theorem iocToUnitInterval_iocOne : iocToUnitInterval iocOne = 1 :=
  (rfl)

/-- Canonical inclusion `(0, 1) → (0, 1]`. -/
def iooToIoc (x : Ioo (0 : ℝ) 1) : Ioc (0 : ℝ) 1 :=
  ⟨x.1, Ioo_subset_Ioc_self x.2⟩

@[simp]
theorem coe_iooToIoc (x : Ioo (0 : ℝ) 1) : (iooToIoc x : ℝ) = x.1 :=
  (rfl)

theorem continuous_iooToIoc : Continuous iooToIoc :=
  continuous_subtype_val.subtype_mk _

theorem range_iooToIoc : range iooToIoc = {iocOne}ᶜ := by
  ext t
  simp only [mem_range, mem_compl_iff, mem_singleton_iff]
  constructor
  · rintro ⟨x, rfl⟩ h1
    exact x.2.2.ne (congrArg Subtype.val h1)
  · intro ht1
    have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht1 (Subtype.ext h)
    exact ⟨⟨t.1, t.2.1, hlt⟩, rfl⟩

theorem notMem_range_iooToIoc_iff (t : Ioc (0 : ℝ) 1) :
    t ∉ range iooToIoc ↔ t = iocOne := by
  rw [range_iooToIoc, mem_compl_iff, mem_singleton_iff, not_not]

theorem isOpenEmbedding_iooToIoc : IsOpenEmbedding iooToIoc :=
  ⟨IsEmbedding.of_comp continuous_iooToIoc continuous_subtype_val IsEmbedding.subtypeVal,
    range_iooToIoc ▸ isOpen_compl_singleton⟩

/-- Orientation-preserving order isomorphism `(0, 1) ≃o (-π/2, π/2)` given by `t ↦ π(t - 1/2)`. -/
noncomputable def iooZeroOneOrderIsoPiHalf :
    Ioo (0 : ℝ) 1 ≃o Ioo (-(Real.pi / 2)) (Real.pi / 2) where
  toFun x := ⟨Real.pi * ((x : ℝ) - 2⁻¹), by
    have hpi := Real.pi_pos
    constructor <;> nlinarith [x.2.1, x.2.2]⟩
  invFun y := ⟨(y : ℝ) / Real.pi + 2⁻¹, by
    have hpi := Real.pi_pos
    constructor
    · rw [div_add' _ _ _ hpi.ne', lt_div_iff₀ hpi]
      linarith [y.2.1]
    · rw [div_add' _ _ _ hpi.ne', div_lt_iff₀ hpi]
      linarith [y.2.2]⟩
  left_inv x := by
    ext
    have hpi := Real.pi_ne_zero
    field_simp
    ring
  right_inv y := by
    ext
    have hpi := Real.pi_ne_zero
    field_simp
    ring
  map_rel_iff' {x₁ x₂} := by
    simp only [Equiv.coe_fn_mk, ← Subtype.coe_le_coe]
    exact ⟨fun h => by nlinarith [Real.pi_pos], fun h => by nlinarith [Real.pi_pos]⟩

/-- Orientation-preserving homeomorphism `(0, 1) ≃ₜ ℝ` given by `t ↦ tan(π(t - 1/2))`. -/
noncomputable def iooZeroOneHomeomorphReal : Ioo (0 : ℝ) 1 ≃ₜ ℝ :=
  (iooZeroOneOrderIsoPiHalf.trans Real.tanOrderIso).toHomeomorph

@[simp]
theorem iooZeroOneHomeomorphReal_apply (x : Ioo (0 : ℝ) 1) :
    iooZeroOneHomeomorphReal x = Real.tan (Real.pi * ((x : ℝ) - 2⁻¹)) :=
  (rfl)

end IntervalTopology

/-- The cone `C₀((0, 1], A)` of a topological space with zero (in particular, a C⋆-algebra). -/
abbrev CStarCone (A : Type*) [TopologicalSpace A] [Zero A] : Type _ :=
  C₀(Ioc (0 : ℝ) 1, A)

/-- The suspension `C₀((0, 1), A)` of a topological space with zero (in particular, a C⋆-algebra).
-/
abbrev CStarSuspension (A : Type*) [TopologicalSpace A] [Zero A] : Type _ :=
  C₀(Ioo (0 : ℝ) 1, A)

/-- Evaluation at `0 : unitInterval` on `C(unitInterval, A)` is surjective, with quotient
isometrically `⋆`-isomorphic to `A`. -/
noncomputable def pathQuotientKerEvalZeroEquiv (A : Type*) [NonUnitalCStarAlgebra A] :
    C(I, A) ⧸ TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I)) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective
    (φ := ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I))
    fun a => ⟨ContinuousMap.const I a, by simp⟩

namespace CStarCone

section Basic

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Isometric `⋆`-homomorphism embedding `CStarCone A` into `C(unitInterval, A)` as paths vanishing
at `0`. -/
noncomputable def toPath : CStarCone A →⋆ₙₐ[ℂ] C(I, A) :=
  (ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ I A).symm.toNonUnitalStarAlgHom.comp
    (ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom ℂ A isOpenEmbedding_iocToUnitInterval)

theorem coe_toPath_apply (f : CStarCone A) :
    (toPath f : C(I, A)) =
      (ZeroAtInftyContinuousMap.extendByZero isOpenEmbedding_iocToUnitInterval f : C(I, A)) := by
  ext t
  simp [toPath]

@[simp]
theorem toPath_apply_ioc (f : CStarCone A) (x : Ioc (0 : ℝ) 1) :
    toPath f (iocToUnitInterval x) = f x := by
  rw [coe_toPath_apply]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_mem isOpenEmbedding_iocToUnitInterval f x

@[simp]
theorem toPath_apply_zero (f : CStarCone A) : toPath f 0 = 0 := by
  rw [coe_toPath_apply]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_of_notMem isOpenEmbedding_iocToUnitInterval f
    ((notMem_range_iocToUnitInterval_iff 0).mpr rfl)

theorem toPath_injective : Function.Injective (toPath (A := A)) := fun f g h =>
  ZeroAtInftyContinuousMap.extendByZero_injective isOpenEmbedding_iocToUnitInterval <|
    ZeroAtInftyContinuousMap.ext fun t => by
      have ht := DFunLike.congr_fun h t
      simpa [coe_toPath_apply] using ht

theorem isometry_toPath : Isometry (toPath (A := A)) :=
  NonUnitalStarAlgHom.isometry toPath toPath_injective

/-- `CStarCone A` is `⋆`-isomorphic to the closed ideal of paths in `C(unitInterval, A)` vanishing
at `0`. -/
noncomputable def equivKerEvalZero :
    CStarCone A ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I)) :=
  ZeroAtInftyContinuousMap.equivKerContinuousMapEvalOfNotMemRangeIff A
    isOpenEmbedding_iocToUnitInterval notMem_range_iocToUnitInterval_iff

@[simp]
theorem coe_equivKerEvalZero_apply (f : CStarCone A) :
    ((equivKerEvalZero f :
      TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I))) : C(I, A)) =
      toPath f := by
  rw [coe_toPath_apply, equivKerEvalZero,
    ZeroAtInftyContinuousMap.coe_equivKerContinuousMapEvalOfNotMemRangeIff_apply]

/-- Evaluation at `1` as a `⋆`-homomorphism `CStarCone A →⋆ₙₐ[ℂ] A`. -/
abbrev evalOne : CStarCone A →⋆ₙₐ[ℂ] A :=
  ZeroAtInftyContinuousMap.evalNonUnitalStarAlgHom ℂ A iocOne

theorem evalOne_apply (f : CStarCone A) : evalOne f = f iocOne := by
  simp [evalOne]

@[simp]
theorem toPath_apply_one (f : CStarCone A) : toPath f 1 = evalOne f := by
  rw [← iocToUnitInterval_iocOne, toPath_apply_ioc, evalOne_apply]

/-- Restrict any path `g : C(unitInterval, A)` with `g 0 = 0` to `CStarCone A`. -/
noncomputable def ofPathEqZero (g : C(I, A)) (hg0 : g 0 = 0) : CStarCone A :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_iocToUnitInterval.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty g) fun t ht => by
      rw [(notMem_range_iocToUnitInterval_iff t).mp ht]
      simpa using hg0

@[simp]
theorem ofPathEqZero_apply (g : C(I, A)) (hg0 : g 0 = 0) (x : Ioc (0 : ℝ) 1) :
    ofPathEqZero g hg0 x = g (iocToUnitInterval x) := by
  simp [ofPathEqZero]

@[simp]
theorem toPath_ofPathEqZero (g : C(I, A)) (hg0 : g 0 = 0) :
    toPath (ofPathEqZero g hg0) = g := by
  ext t
  by_cases ht0 : t = 0
  · subst ht0
    rw [toPath_apply_zero, hg0]
  · obtain ⟨x, rfl⟩ := notMem_compl_iff.mp fun hx =>
      ht0 ((notMem_range_iocToUnitInterval_iff t).mp hx)
    rw [toPath_apply_ioc, ofPathEqZero_apply]

/-- Linear cone element `t ↦ (t : ℝ) • a` in `CStarCone A`. -/
noncomputable def linearPath (a : A) : CStarCone A :=
  ofPathEqZero ⟨fun t : I => (t : ℝ) • a, continuous_subtype_val.smul continuous_const⟩ (by simp)

@[simp]
theorem linearPath_apply (a : A) (t : Ioc (0 : ℝ) 1) : linearPath a t = (t : ℝ) • a := by
  simp [linearPath]

theorem evalOne_linearPath (a : A) : evalOne (linearPath a) = a := by
  simp

@[simp]
theorem norm_linearPath (a : A) : ‖linearPath a‖ = ‖a‖ := by
  refine le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg a)).mpr fun t => ?_) ?_
  · rw [linearPath_apply, norm_smul, Real.norm_of_nonneg t.2.1.le]
    exact mul_le_of_le_one_left (norm_nonneg a) t.2.2
  · have h := ZeroAtInftyContinuousMap.norm_coe_le_norm (linearPath a) iocOne
    simpa only [linearPath_apply, coe_iocOne, one_smul] using h

theorem evalOne_surjective : Function.Surjective (evalOne (A := A)) :=
  fun a => ⟨linearPath a, evalOne_linearPath a⟩

/-- The quotient of `CStarCone A` by the kernel of `evalOne` is `⋆`-isomorphic to `A`. -/
noncomputable def quotientKerEvalOneEquiv :
    CStarCone A ⧸ TwoSidedIdeal.ker (evalOne (A := A)) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective evalOne_surjective

/-- Functorial action of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` on cones. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : CStarCone A →⋆ₙₐ[ℂ] CStarCone B :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom (Ioc (0 : ℝ) 1) φ (map_continuous φ)

@[simp]
theorem map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : CStarCone A) (t : Ioc (0 : ℝ) 1) :
    map φ f t = φ (f t) := by
  simp [map]

@[simp]
theorem map_id : map (.id ℂ A) = .id ℂ (CStarCone A) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_id (Ioc (0 : ℝ) 1)

theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_comp (Ioc (0 : ℝ) 1) φ ψ
    (map_continuous φ) (map_continuous ψ)

@[simp]
theorem evalOne_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    evalOne.comp (map φ) = φ.comp evalOne := by
  ext f
  simp

end Basic

section Contraction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Truncated shift `(t, s) ↦ max(s - t, 0)` on `unitInterval × unitInterval`. -/
private noncomputable def coneShift : C(I × I, I) where
  toFun p := ⟨max ((p.2 : ℝ) - (p.1 : ℝ)) 0,
    le_max_right _ _, max_le ((sub_le_self _ p.1.2.1).trans p.2.2.2) zero_le_one⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_subtype_val.comp continuous_snd).sub
      (continuous_subtype_val.comp continuous_fst)).max continuous_const

private theorem coneShift_zero_right (t : I) : coneShift (t, 0) = 0 := by
  ext
  simp [coneShift, t.2.1]

private theorem coneShift_zero_left (s : I) : coneShift (0, s) = s := by
  ext
  simp [coneShift, s.2.1]

private theorem coneShift_one_left (s : I) : coneShift (1, s) = 0 := by
  ext
  have hle : (s : ℝ) - 1 ≤ 0 := sub_nonpos.mpr s.2.2
  simp [coneShift, hle]

/-- Continuous path `t ↦ φ_t(f)` in `CStarCone A` induced by precomposing `toPath f` with
`coneShift`. -/
private noncomputable def contractionPath (f : CStarCone A) : C(I, CStarCone A) where
  toFun t := ofPathEqZero (((toPath f).comp coneShift).curry t) (by
    rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply, coneShift_zero_right,
      toPath_apply_zero])
  continuous_toFun := by
    rw [(isometry_toPath (A := A)).isUniformInducing.isInducing.continuous_iff]
    have hcomp : (toPath (A := A) ∘ fun t =>
        ofPathEqZero (((toPath f).comp coneShift).curry t)
          (by rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply, coneShift_zero_right,
            toPath_apply_zero])) = ((toPath f).comp coneShift).curry := by
      ext t s
      simp
    rw [hcomp]
    exact ((toPath f).comp coneShift).curry.continuous

@[simp]
private theorem contractionPath_apply (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1) :
    contractionPath f t s = toPath f (coneShift (t, iocToUnitInterval s)) := by
  simp [contractionPath]

/-- Explicit contraction homotopy on `CStarCone A` given by `φ_t(f)(s) = f(s - t)` for `s > t` and
`0` for `s ≤ t` (Blackadar, II.5.5.11). -/
noncomputable def contractionHomotopy :
    NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarCone A)) (0 : CStarCone A →⋆ₙₐ[ℂ] CStarCone A) where
  toHom :=
    { toFun := contractionPath
      map_smul' c f := by ext t s; simp [map_smul]
      map_zero' := by ext t s; simp
      map_add' f g := by ext t s; simp [map_add]
      map_mul' f g := by ext t s; simp [map_mul]
      map_star' f := by ext t s; simp [map_star] }
  eval_zero f := by
    ext s
    simp [coneShift_zero_left]
  eval_one f := by
    ext s
    simp [coneShift_one_left]

theorem contractionHomotopy_apply_of_lt (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1)
    (hst : (t : ℝ) < (s : ℝ)) :
    (contractionHomotopy (A := A)).eval t f s =
      f ⟨(s : ℝ) - (t : ℝ), sub_pos.mpr hst, (sub_le_self _ t.2.1).trans s.2.2⟩ := by
  have hshift :
      coneShift (t, iocToUnitInterval s) =
        iocToUnitInterval ⟨(s : ℝ) - (t : ℝ), sub_pos.mpr hst,
          (sub_le_self _ t.2.1).trans s.2.2⟩ := by
    ext
    simp [coneShift, max_eq_left (sub_pos.mpr hst).le]
  simp [contractionHomotopy, hshift]

theorem contractionHomotopy_apply_of_le (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1)
    (hst : (s : ℝ) ≤ (t : ℝ)) :
    (contractionHomotopy (A := A)).eval t f s = 0 := by
  have hshift : coneShift (t, iocToUnitInterval s) = 0 := by
    ext
    simp [coneShift, max_eq_right (sub_nonpos.mpr hst)]
  simp [contractionHomotopy, hshift]

/-- Every cone C⋆-algebra `CStarCone A` is contractible. -/
theorem isContractible (A : Type*) [NonUnitalCStarAlgebra A] :
    IsContractibleCStarAlgebra (CStarCone A) :=
  ⟨contractionHomotopy⟩

end Contraction

end CStarCone

namespace CStarSuspension

section Basic

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Isometric `⋆`-homomorphism embedding `CStarSuspension A` into `CStarCone A` by setting the
value at `1` to `0`. -/
noncomputable def toCone : CStarSuspension A →⋆ₙₐ[ℂ] CStarCone A :=
  ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom ℂ A isOpenEmbedding_iooToIoc

@[simp]
theorem toCone_apply_ioo (f : CStarSuspension A) (x : Ioo (0 : ℝ) 1) :
    toCone f (iooToIoc x) = f x := by
  simp [toCone]

@[simp]
theorem toCone_apply_iocOne (f : CStarSuspension A) : toCone f iocOne = 0 := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_of_notMem isOpenEmbedding_iooToIoc f
    ((notMem_range_iooToIoc_iff iocOne).mpr rfl)

theorem toCone_apply_one (f : CStarSuspension A) : CStarCone.evalOne (toCone f) = 0 := by
  simp

@[simp]
theorem evalOne_comp_toCone :
    (CStarCone.evalOne (A := A)).comp toCone = 0 :=
  NonUnitalStarAlgHom.ext toCone_apply_one

theorem toCone_injective : Function.Injective (toCone (A := A)) :=
  ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom_injective ℂ A isOpenEmbedding_iooToIoc

theorem isometry_toCone : Isometry (toCone (A := A)) :=
  NonUnitalStarAlgHom.isometry toCone toCone_injective

/-- `CStarSuspension A` is `⋆`-isomorphic to the kernel of `CStarCone.evalOne`. -/
noncomputable def equivKerEvalOne :
    CStarSuspension A ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (CStarCone.evalOne (A := A)) :=
  ZeroAtInftyContinuousMap.equivKerEvalOfNotMemRangeIff A
    isOpenEmbedding_iooToIoc notMem_range_iooToIoc_iff

@[simp]
theorem coe_equivKerEvalOne_apply (f : CStarSuspension A) :
    ((equivKerEvalOne f : TwoSidedIdeal.ker (CStarCone.evalOne (A := A))) : CStarCone A) =
      toCone f := by
  rw [equivKerEvalOne, ZeroAtInftyContinuousMap.coe_equivKerEvalOfNotMemRangeIff_apply, toCone,
    ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom]

/-- Restrict any cone element `f : CStarCone A` satisfying `CStarCone.evalOne f = 0` to
`CStarSuspension A`. -/
noncomputable def ofConeEqZero (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0) :
    CStarSuspension A :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_iooToIoc.isEmbedding f fun t ht => by
    rw [(notMem_range_iooToIoc_iff t).mp ht, ← CStarCone.evalOne_apply]
    exact hf1

@[simp]
theorem ofConeEqZero_apply (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0)
    (x : Ioo (0 : ℝ) 1) :
    ofConeEqZero f hf1 x = f (iooToIoc x) := by
  simp [ofConeEqZero]

@[simp]
theorem toCone_ofConeEqZero (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0) :
    toCone (ofConeEqZero f hf1) = f := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom, ofConeEqZero]
  exact ZeroAtInftyContinuousMap.extendByZero_restrictOfEqZero isOpenEmbedding_iooToIoc f _

@[simp]
theorem ofConeEqZero_toCone (g : CStarSuspension A) :
    ofConeEqZero (toCone g) (toCone_apply_one g) = g :=
  toCone_injective (toCone_ofConeEqZero _ _)

/-- Orientation-preserving `⋆`-isomorphism `CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A)` induced by
`iooZeroOneHomeomorphReal`. -/
noncomputable def equivReal (A : Type*) [NonUnitalCStarAlgebra A] :
    CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A) :=
  ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ A iooZeroOneHomeomorphReal

@[simp]
theorem equivReal_symm_apply (f : C₀(ℝ, A)) (x : Ioo (0 : ℝ) 1) :
    (equivReal A).symm f x = f (Real.tan (Real.pi * ((x : ℝ) - 2⁻¹))) := by
  simp [equivReal]

/-- Functorial action of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` on suspensions. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : CStarSuspension A →⋆ₙₐ[ℂ] CStarSuspension B :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom (Ioo (0 : ℝ) 1) φ (map_continuous φ)

@[simp]
theorem map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : CStarSuspension A) (t : Ioo (0 : ℝ) 1) :
    map φ f t = φ (f t) := by
  simp [map]

@[simp]
theorem map_id : map (.id ℂ A) = .id ℂ (CStarSuspension A) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_id (Ioo (0 : ℝ) 1)

theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_comp (Ioo (0 : ℝ) 1) φ ψ
    (map_continuous φ) (map_continuous ψ)

/-- The inclusion `CStarSuspension A →⋆ₙₐ[ℂ] CStarCone A` is null-homotopic (the suspension is
subcontractible inside the cone). -/
noncomputable def toConeContractionHomotopy :
    NonUnitalStarAlgHom.Homotopy (toCone (A := A)) 0 := by
  have h0 : (0 : CStarCone A →⋆ₙₐ[ℂ] CStarCone A).comp (toCone (A := A)) = 0 := by
    ext f t
    rfl
  exact h0 ▸ (CStarCone.contractionHomotopy (A := A)).compRight toCone

theorem toCone_homotopic_zero : NonUnitalStarAlgHom.Homotopic (toCone (A := A)) 0 :=
  ⟨toConeContractionHomotopy⟩

end Basic

section NonContractibleComplex

/-- Embedding `CStarSuspension ℂ →⋆ₙₐ[ℂ] C(unitInterval, ℂ)` as paths vanishing at `0` and `1`. -/
private noncomputable def toLoopPath : CStarSuspension ℂ →⋆ₙₐ[ℂ] C(I, ℂ) :=
  CStarCone.toPath.comp toCone

private theorem toLoopPath_zero (f : CStarSuspension ℂ) : toLoopPath f 0 = 0 := by
  simp [toLoopPath]

private theorem toLoopPath_one (f : CStarSuspension ℂ) : toLoopPath f 1 = 0 := by
  simp [toLoopPath]

/-- The winding-number-`1` loop on `unitInterval` shifted by `-1`, vanishing at `0` and `1`. -/
private noncomputable def windingQuasiUnitaryPath : C(I, ℂ) where
  toFun s := ((AddCircle.homeomorphCircle one_ne_zero
    (AddCircle.zsmulLoop (1 : ℝ) 0 1 s) : Circle) : ℂ) - 1
  continuous_toFun := by fun_prop

private theorem windingQuasiUnitaryPath_zero : windingQuasiUnitaryPath 0 = 0 := by
  simp [windingQuasiUnitaryPath, AddCircle.homeomorphCircle_apply]

private theorem windingQuasiUnitaryPath_one : windingQuasiUnitaryPath 1 = 0 := by
  simp [windingQuasiUnitaryPath, AddCircle.homeomorphCircle_apply]

/-- The winding-number-`1` quasi-unitary generator in `CStarSuspension ℂ`. -/
private noncomputable def windingQuasiUnitary : CStarSuspension ℂ :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_iooToIoc.isEmbedding
    (CStarCone.ofPathEqZero windingQuasiUnitaryPath windingQuasiUnitaryPath_zero)
    fun t ht => by
      rw [(notMem_range_iooToIoc_iff t).mp ht]
      simp [windingQuasiUnitaryPath_one]

private theorem toLoopPath_windingQuasiUnitary :
    toLoopPath windingQuasiUnitary = windingQuasiUnitaryPath := by
  ext s
  by_cases hs0 : s = 0
  · subst hs0
    rw [toLoopPath_zero, windingQuasiUnitaryPath_zero]
  · obtain ⟨x, rfl⟩ := notMem_compl_iff.mp fun hx =>
      hs0 ((notMem_range_iocToUnitInterval_iff s).mp hx)
    by_cases hx1 : x = iocOne
    · subst hx1
      rw [iocToUnitInterval_iocOne, toLoopPath_one, windingQuasiUnitaryPath_one]
    · obtain ⟨y, rfl⟩ := notMem_compl_iff.mp fun hy =>
        hx1 ((notMem_range_iooToIoc_iff x).mp hy)
      simp [toLoopPath, windingQuasiUnitary]

private theorem windingQuasiUnitary_relation :
    star windingQuasiUnitary + windingQuasiUnitary +
      star windingQuasiUnitary * windingQuasiUnitary = 0 := by
  apply CStarCone.toPath_injective.comp toCone_injective
  have hcomp_eq : (CStarCone.toPath (A := ℂ) ∘ toCone) = toLoopPath := rfl
  rw [hcomp_eq, map_add, map_add, map_mul, map_star, map_zero, toLoopPath_windingQuasiUnitary]
  ext s
  set u : Circle := AddCircle.homeomorphCircle one_ne_zero (AddCircle.zsmulLoop (1 : ℝ) 0 1 s)
  have hu : star (u : ℂ) * (u : ℂ) = 1 := by
    rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_coe]
    simp
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    ContinuousMap.zero_apply, windingQuasiUnitaryPath, ContinuousMap.coe_mk]
  calc
    star ((u : ℂ) - 1) + ((u : ℂ) - 1) + star ((u : ℂ) - 1) * ((u : ℂ) - 1) =
        star (u : ℂ) * (u : ℂ) - 1 := by
      rw [star_sub, star_one]
      ring
    _ = 0 := by rw [hu, sub_self]

/-- Complex-valued continuous square `(t, s) ↦ toLoopPath (H_t(windingQuasiUnitary)) s` induced by
a null-homotopy `H` of `CStarSuspension ℂ`. -/
private noncomputable def windingComplexSquare
    (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
      (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ)) :
    C(I × I, ℂ) :=
  ((ContinuousMap.compNonUnitalStarAlgHom I toLoopPath (map_continuous toLoopPath))
    (H.toHom windingQuasiUnitary)).uncurry

private theorem windingComplexSquare_apply
    (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
      (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ))
    (p : I × I) :
    windingComplexSquare H p = toLoopPath (H.toHom windingQuasiUnitary p.1) p.2 := by
  simp [windingComplexSquare, Function.uncurry]

private theorem windingComplexSquare_relation
    (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
      (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ))
    (p : I × I) :
    star (windingComplexSquare H p) + windingComplexSquare H p +
      star (windingComplexSquare H p) * windingComplexSquare H p = 0 := by
  have hrel := congrArg (fun x => toLoopPath (H.eval p.1 x) p.2) windingQuasiUnitary_relation
  simpa only [map_add, map_mul, map_star, map_zero, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.zero_apply,
    NonUnitalStarAlgHom.Homotopy.eval_apply, ← windingComplexSquare_apply] using hrel

/-- Circle-valued continuous square `(t, s) ↦ toLoopPath (H_t(windingQuasiUnitary)) s + 1` induced
by a null-homotopy `H` of `CStarSuspension ℂ`. -/
private noncomputable def windingCircleSquare
    (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
      (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ)) :
    C(I × I, Circle) :=
  ⟨fun p => ⟨windingComplexSquare H p + 1, by
    have hmul : star (windingComplexSquare H p + 1) * (windingComplexSquare H p + 1) = 1 := by
      calc
        star (windingComplexSquare H p + 1) * (windingComplexSquare H p + 1) =
            (star (windingComplexSquare H p) + windingComplexSquare H p +
              star (windingComplexSquare H p) * windingComplexSquare H p) + 1 := by
          rw [star_add, star_one]
          ring
        _ = 1 := by rw [windingComplexSquare_relation H p, zero_add]
    have hnorm_sq : ‖windingComplexSquare H p + 1‖ * ‖windingComplexSquare H p + 1‖ = 1 := by
      simpa only [CStarRing.norm_star_mul_self, norm_one] using congrArg norm hmul
    exact mem_sphere_zero_iff_norm.mpr (by nlinarith [norm_nonneg (windingComplexSquare H p + 1)])⟩,
    Continuous.subtype_mk ((windingComplexSquare H).continuous.add continuous_const) _⟩

private theorem coe_windingCircleSquare
    (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
      (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ))
    (t s : I) :
    (windingCircleSquare H (t, s) : ℂ) = toLoopPath (H.toHom windingQuasiUnitary t) s + 1 :=
  congrArg (· + 1) (windingComplexSquare_apply H (t, s))

/-- Transport a null-homotopy of `.id ℂ (CStarSuspension ℂ)` along `windingQuasiUnitary` to a
path homotopy from the winding-number-`1` loop on `AddCircle 1` to the constant loop. -/
private noncomputable def windingNullHomotopy
    (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
      (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ)) :
    Path.Homotopy (AddCircle.zsmulLoop (1 : ℝ) 0 1)
      (Path.refl ((0 : ℝ) : AddCircle (1 : ℝ))) := by
  let eCircle := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  let U := windingCircleSquare H
  let W : C(I × I, AddCircle (1 : ℝ)) :=
    (ContinuousMap.mk eCircle.symm eCircle.continuous_symm).comp U
  have he1 : eCircle.symm 1 = (0 : AddCircle (1 : ℝ)) :=
    eCircle.symm_apply_eq.mpr (by simp [eCircle, AddCircle.homeomorphCircle_apply])
  exact
    { toContinuousMap := W
      map_zero_left s := by
        have hU0 : U (0, s) = eCircle (AddCircle.zsmulLoop (1 : ℝ) 0 1 s) := by
          apply Circle.ext
          rw [coe_windingCircleSquare]
          simp [toLoopPath_windingQuasiUnitary, windingQuasiUnitaryPath, eCircle]
        simp [W, hU0]
      map_one_left s := by
        have hU1 : U (1, s) = 1 := by
          apply Circle.ext
          rw [coe_windingCircleSquare]
          simp
        simp [W, hU1, he1]
      prop' t s hs := by
        rcases hs with rfl | rfl
        · have hUs : U (t, 0) = 1 := by
            apply Circle.ext
            rw [coe_windingCircleSquare, toLoopPath_zero, zero_add]
            rfl
          simp [W, hUs, he1]
        · have hUs : U (t, 1) = 1 := by
            apply Circle.ext
            rw [coe_windingCircleSquare, toLoopPath_one, zero_add]
            rfl
          simp [W, hUs, he1] }

/-- `CStarSuspension ℂ = C₀((0, 1), ℂ)` is not contractible (Blackadar, II.5.5.11): any homotopy
from `.id` to `0` transports the quasi-unitary loop `s ↦ exp(2πis) - 1` to a null-homotopy of the
winding-number-`1` loop in `AddCircle 1`. -/
theorem not_isContractible_complex : ¬IsContractibleCStarAlgebra (CStarSuspension ℂ) := by
  rintro ⟨H⟩
  have hfg : (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop (1 : ℝ) 0 1)) :
        FundamentalGroup (AddCircle (1 : ℝ)) (0 : ℝ)) = 1 :=
    congrArg FundamentalGroup.fromPath (Quotient.sound ⟨windingNullHomotopy H⟩)
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hw := congrArg (AddCircle.windingNumber (p := (1 : ℝ)) (x := (0 : ℝ))) hfg
  rw [AddCircle.windingNumber_zsmulLoop (p := (1 : ℝ)) 0 1] at hw
  have hw1 : AddCircle.windingNumber (p := (1 : ℝ))
      (1 : FundamentalGroup (AddCircle (1 : ℝ)) (0 : ℝ)) = 0 := by
    simp [AddCircle.windingNumber]
  exact one_ne_zero (hw.trans hw1)

end NonContractibleComplex

end CStarSuspension

/-- `C₀(ℝ, ℂ)` is not contractible. -/
theorem not_isContractibleCStarAlgebra_c0_real : ¬IsContractibleCStarAlgebra C₀(ℝ, ℂ) := fun h =>
  CStarSuspension.not_isContractible_complex
    ((IsContractibleCStarAlgebra.iff_of_starAlgEquiv (CStarSuspension.equivReal ℂ)).mpr h)

end TauCeti
