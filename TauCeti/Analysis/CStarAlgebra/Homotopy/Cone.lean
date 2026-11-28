/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousMap
public import TauCeti.Analysis.CStarAlgebra.Homotopy.Basic
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Topology.Homeomorph.Interval
public import TauCeti.Topology.UnitInterval.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.FundamentalGroupCircle
import Mathlib.Topology.Order.ProjIcc

/-!
# Cone and suspension C⋆-algebras

For a non-unital complex C⋆-algebra `A`, the cone and suspension C⋆-algebras are
`CStarCone A := C₀(Set.Ioc (0 : ℝ) 1, A)` and `CStarSuspension A := C₀(Set.Ioo (0 : ℝ) 1, A)`,
equipped with the supremum norm and pointwise `⋆`-algebra operations (Blackadar,
*Operator Algebras*, II.5.5.10–II.5.5.11).

## Main declarations

* `TauCeti.CStarCone` and `TauCeti.CStarSuspension`: `C₀((0, 1], A)` and `C₀((0, 1), A)`.
* `TauCeti.CStarCone.toUnitIntervalMap` and `TauCeti.CStarCone.equivKerEvalZero`: isometric
  `⋆`-embedding into `C(unitInterval, A)` and `⋆`-isomorphism onto the evaluation kernel at `0`.
* `TauCeti.CStarCone.evalOne`, `TauCeti.CStarCone.linear`,
  `TauCeti.CStarSuspension.toCone`, `TauCeti.CStarSuspension.equivKerEvalOne`, and
  `TauCeti.CStarCone.quotientKerEvalOneEquiv`: the exact sequence
  `0 → CStarSuspension A → CStarCone A → A → 0`.
* `TauCeti.CStarSuspension.equivReal`: orientation-preserving `⋆`-isomorphism
  `CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A)` via `t ↦ tan(π(t - 1/2))`.
* `TauCeti.CStarCone.map` and `TauCeti.CStarSuspension.map`: functoriality for `⋆`-homomorphisms.
* `TauCeti.CStarCone.contractionHomotopy`, `TauCeti.CStarCone.isContractibleCStarAlgebra`, and
  `TauCeti.CStarSuspension.toCone_homotopic_zero`: explicit cone contraction
  `φ_t(f)(s) = f(s - t)` for `s > t` and `0` otherwise, and subcontractibility of the suspension.
* `TauCeti.CStarSuspension.not_isContractibleCStarAlgebra_complex` and
  `TauCeti.not_isContractibleCStarAlgebra_zeroAtInfty_real`: `CStarSuspension ℂ` and `C₀(ℝ, ℂ)` are
  not contractible (proved via a quasi-unitary generator and `AddCircle.windingNumber`).

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.5.5.10–II.5.5.11.
-/

public section

open Filter Set Topology unitInterval
open scoped CStarAlgebra ZeroAtInfty

namespace TauCeti

/-- The cone `C₀((0, 1], A)` of a topological space with zero (in particular, a C⋆-algebra). -/
abbrev CStarCone (A : Type*) [TopologicalSpace A] [Zero A] : Type _ := C₀(Ioc (0 : ℝ) 1, A)

/-- The suspension `C₀((0, 1), A)` of a topological space with zero (in particular, a C⋆-algebra).
-/
abbrev CStarSuspension (A : Type*) [TopologicalSpace A] [Zero A] : Type _ := C₀(Ioo (0 : ℝ) 1, A)

namespace CStarCone

section Basic

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Isometric `⋆`-homomorphism embedding `CStarCone A` into `C(unitInterval, A)` as continuous
maps vanishing at `0`. -/
noncomputable def toUnitIntervalMap : CStarCone A →⋆ₙₐ[ℂ] C(I, A) :=
  (ContinuousMap.liftZeroAtInftyStarAlgEquiv ℂ I A).symm.toNonUnitalStarAlgHom.comp
    (ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom ℂ A isOpenEmbedding_inclusion_Ioc_Icc)

theorem coe_toUnitIntervalMap_apply (f : CStarCone A) :
    (toUnitIntervalMap f : C(I, A)) =
      (ZeroAtInftyContinuousMap.extendByZero isOpenEmbedding_inclusion_Ioc_Icc f : C(I, A)) := by
  ext t; simp [toUnitIntervalMap]

@[simp] theorem toUnitIntervalMap_apply_inclusion (f : CStarCone A) (x : Ioc (0 : ℝ) 1) :
    toUnitIntervalMap f (Set.inclusion Ioc_subset_Icc_self x) = f x := by
  rw [coe_toUnitIntervalMap_apply]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_mem isOpenEmbedding_inclusion_Ioc_Icc f x

@[simp] theorem toUnitIntervalMap_apply_zero (f : CStarCone A) : toUnitIntervalMap f 0 = 0 := by
  rw [coe_toUnitIntervalMap_apply]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_of_notMem isOpenEmbedding_inclusion_Ioc_Icc f
    ((notMem_range_inclusion_Ioc_Icc_iff 0).mpr rfl)

theorem toUnitIntervalMap_injective : Function.Injective (toUnitIntervalMap (A := A)) :=
  fun f g h => ZeroAtInftyContinuousMap.extendByZero_injective isOpenEmbedding_inclusion_Ioc_Icc <|
    ZeroAtInftyContinuousMap.ext fun t => by
      simpa [coe_toUnitIntervalMap_apply] using DFunLike.congr_fun h t

theorem isometry_toUnitIntervalMap : Isometry (toUnitIntervalMap (A := A)) :=
  NonUnitalStarAlgHom.isometry toUnitIntervalMap toUnitIntervalMap_injective

/-- `CStarCone A` is `⋆`-isomorphic to the closed evaluation-kernel subalgebra of maps in
`C(unitInterval, A)` vanishing at `0`. -/
noncomputable def equivKerEvalZero :
    CStarCone A ≃⋆ₐ[ℂ] ContinuousMap.evalKerSubalgebra ℂ A (0 : I) :=
  (ContinuousMap.restrictStarAlgEquivOfNotMemRange ℂ A
    isOpenEmbedding_inclusion_Ioc_Icc notMem_range_inclusion_Ioc_Icc_iff).symm

@[simp] theorem coe_equivKerEvalZero_apply (f : CStarCone A) :
    ((equivKerEvalZero f : ContinuousMap.evalKerSubalgebra ℂ A (0 : I)) : C(I, A)) =
      toUnitIntervalMap f := by
  ext t
  simp [equivKerEvalZero, toUnitIntervalMap]

@[simp] theorem equivKerEvalZero_symm_apply
    (g : ContinuousMap.evalKerSubalgebra ℂ A (0 : I)) (x : Ioc (0 : ℝ) 1) :
    equivKerEvalZero.symm g x = (g : C(I, A)) (Set.inclusion Ioc_subset_Icc_self x) := by
  simp [equivKerEvalZero]

/-- Evaluation at `1` as a `⋆`-homomorphism `CStarCone A →⋆ₙₐ[ℂ] A`. -/
abbrev evalOne : CStarCone A →⋆ₙₐ[ℂ] A :=
  ZeroAtInftyContinuousMap.evalNonUnitalStarAlgHom ℂ A iocOne

theorem evalOne_apply (f : CStarCone A) : evalOne f = f iocOne := by simp [evalOne]

@[simp] theorem toUnitIntervalMap_apply_one (f : CStarCone A) :
    toUnitIntervalMap f 1 = evalOne f := by
  rw [← inclusion_Ioc_Icc_iocOne, toUnitIntervalMap_apply_inclusion, evalOne_apply]

/-- Restrict any continuous map `g : C(unitInterval, A)` with `g 0 = 0` to `CStarCone A`. -/
noncomputable def ofUnitIntervalMapEqZero (g : C(I, A)) (hg0 : g 0 = 0) : CStarCone A :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_inclusion_Ioc_Icc.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty g) fun t ht => by
      rw [(notMem_range_inclusion_Ioc_Icc_iff t).mp ht]; simpa using hg0

@[simp] theorem ofUnitIntervalMapEqZero_apply (g : C(I, A)) (hg0 : g 0 = 0)
    (x : Ioc (0 : ℝ) 1) :
    ofUnitIntervalMapEqZero g hg0 x = g (Set.inclusion Ioc_subset_Icc_self x) := by
  simp [ofUnitIntervalMapEqZero]

@[simp] theorem toUnitIntervalMap_ofUnitIntervalMapEqZero (g : C(I, A)) (hg0 : g 0 = 0) :
    toUnitIntervalMap (ofUnitIntervalMapEqZero g hg0) = g :=
  DFunLike.coe_injective <| eq_of_zero_of_inclusion_Ioc_Icc (by simp [hg0]) (by simp)

@[simp] theorem ofUnitIntervalMapEqZero_toUnitIntervalMap (f : CStarCone A) :
    ofUnitIntervalMapEqZero (toUnitIntervalMap f) (toUnitIntervalMap_apply_zero f) = f :=
  toUnitIntervalMap_injective (toUnitIntervalMap_ofUnitIntervalMapEqZero _ _)

/-- A continuous family `F : X → C(unitInterval, A)` vanishing at `0` induces a continuous map
`X → CStarCone A` via `ofUnitIntervalMapEqZero`. -/
theorem continuous_ofUnitIntervalMapEqZero {X : Type*} [TopologicalSpace X] {F : X → C(I, A)}
    (hF : Continuous F) (hF0 : ∀ x, F x 0 = 0) :
    Continuous fun x => ofUnitIntervalMapEqZero (F x) (hF0 x) := by
  rw [(isometry_toUnitIntervalMap (A := A)).isUniformInducing.isInducing.continuous_iff]
  simpa only [Function.comp_def, toUnitIntervalMap_ofUnitIntervalMapEqZero] using hF

theorem mem_range_toUnitIntervalMap_iff {g : C(I, A)} :
    g ∈ range (toUnitIntervalMap (A := A)) ↔ g 0 = 0 :=
  ⟨fun ⟨f, hf⟩ => hf ▸ toUnitIntervalMap_apply_zero f,
    fun hg0 => ⟨ofUnitIntervalMapEqZero g hg0, toUnitIntervalMap_ofUnitIntervalMapEqZero g hg0⟩⟩

/-- Linear cone element `t ↦ (t : ℝ) • a` in `CStarCone A`. -/
noncomputable def linear (a : A) : CStarCone A :=
  ofUnitIntervalMapEqZero
    ⟨fun t : I => (t : ℝ) • a, continuous_subtypeVal.smul continuous_const⟩ (by simp)

@[simp] theorem linear_apply (a : A) (t : Ioc (0 : ℝ) 1) : linear a t = (t : ℝ) • a := by
  simp [linear]

theorem evalOne_linear (a : A) : evalOne (linear a) = a := by simp

@[simp] theorem norm_linear (a : A) : ‖linear a‖ = ‖a‖ :=
  le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg a)).mpr fun t => by
    rw [linear_apply, norm_smul, Real.norm_of_nonneg t.property.1.le]
    exact mul_le_of_le_one_left (norm_nonneg a) t.property.2)
    (by simpa only [linear_apply, coe_iocOne, one_smul] using
      ZeroAtInftyContinuousMap.norm_coe_le_norm (linear a) iocOne)

theorem evalOne_surjective : Function.Surjective (evalOne (A := A)) :=
  fun a => ⟨linear a, evalOne_linear a⟩

/-- The quotient of `CStarCone A` by the kernel of `evalOne` is `⋆`-isomorphic to `A`. -/
noncomputable def quotientKerEvalOneEquiv :
    CStarCone A ⧸ TwoSidedIdeal.ker (evalOne (A := A)) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective evalOne_surjective

@[simp] theorem quotientKerEvalOneEquiv_mk (f : CStarCone A) :
    quotientKerEvalOneEquiv (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (evalOne (A := A))) f) =
      f iocOne := by simp [quotientKerEvalOneEquiv]

/-- Functorial action of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` on cones. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : CStarCone A →⋆ₙₐ[ℂ] CStarCone B :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom (Ioc (0 : ℝ) 1) φ (map_continuous φ)

@[simp] theorem map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : CStarCone A) (t : Ioc (0 : ℝ) 1) :
    map φ f t = φ (f t) := by simp [map]

@[simp] theorem map_id : map (.id ℂ A) = .id ℂ (CStarCone A) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_id (Ioc (0 : ℝ) 1)

theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_comp (Ioc (0 : ℝ) 1) φ ψ
    (map_continuous φ) (map_continuous ψ)

@[simp] theorem evalOne_comp_map (φ : A →⋆ₙₐ[ℂ] B) : evalOne.comp (map φ) = φ.comp evalOne := by
  ext f; simp

theorem toUnitIntervalMap_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    toUnitIntervalMap.comp (map φ) =
      (ContinuousMap.compNonUnitalStarAlgHom I φ (map_continuous φ)).comp toUnitIntervalMap := by
  ext f : 1
  exact DFunLike.coe_injective <| eq_of_zero_of_inclusion_Ioc_Icc (by simp) (by simp)

end Basic

section Contraction

/-- Truncated shift `(t, s) ↦ max (s - t) 0` on `unitInterval × unitInterval`. -/
private noncomputable def truncatedShift : C(I × I, I) where
  toFun p := Set.projIcc (0 : ℝ) 1 zero_le_one ((p.2 : ℝ) - (p.1 : ℝ))
  continuous_toFun := continuous_projIcc.comp
    ((continuous_subtypeVal.comp continuous_snd).sub (continuous_subtypeVal.comp continuous_fst))

/-- The real value of `truncatedShift p` is `max (p.2 - p.1) 0`. -/
@[simp] private theorem coe_truncatedShift (p : I × I) :
    (truncatedShift p : ℝ) = max ((p.2 : ℝ) - (p.1 : ℝ)) 0 := by
  simp [truncatedShift, Set.coe_projIcc,
    min_eq_right ((sub_le_self _ p.1.property.1).trans p.2.property.2), max_comm]

@[simp] private theorem truncatedShift_zero_right (t : I) : truncatedShift (t, 0) = 0 :=
  Set.projIcc_of_le_left zero_le_one (by simpa using t.property.1)

@[simp] private theorem truncatedShift_zero_left (s : I) : truncatedShift (0, s) = s := by
  simp [truncatedShift]

@[simp] private theorem truncatedShift_one_left (s : I) : truncatedShift (1, s) = 0 :=
  Set.projIcc_of_le_left zero_le_one (sub_nonpos.mpr s.property.2)

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Continuous family `t ↦ φ_t(f)` in `CStarCone A` induced by precomposing
`toUnitIntervalMap f` with `truncatedShift`. -/
private noncomputable def contractionMap (f : CStarCone A) : C(I, CStarCone A) where
  toFun t := ofUnitIntervalMapEqZero (((toUnitIntervalMap f).comp truncatedShift).curry t) (by
    rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply, truncatedShift_zero_right,
      toUnitIntervalMap_apply_zero])
  continuous_toFun := by
    exact continuous_ofUnitIntervalMapEqZero
      ((toUnitIntervalMap f).comp truncatedShift).curry.continuous _

@[simp] private theorem contractionMap_apply (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1) :
    contractionMap f t s =
      toUnitIntervalMap f (truncatedShift (t, Set.inclusion Ioc_subset_Icc_self s)) := by
  simp [contractionMap]

/-- Explicit contraction homotopy on `CStarCone A` given by `φ_t(f)(s) = f(s - t)` for `s > t` and
`0` for `s ≤ t` (Blackadar, II.5.5.11). -/
noncomputable def contractionHomotopy :
    NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarCone A)) (0 : CStarCone A →⋆ₙₐ[ℂ] CStarCone A) where
  toHom :=
    { toFun := contractionMap
      map_smul' c f := by ext t s; simp [map_smul]
      map_zero' := by ext t s; simp
      map_add' f g := by ext t s; simp [map_add]
      map_mul' f g := by ext t s; simp [map_mul]
      map_star' f := by ext t s; simp [map_star] }
  toHom_apply_zero f := by ext s; simp
  toHom_apply_one f := by ext s; simp

private theorem contractionHomotopy_toHom_apply (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1) :
    (contractionHomotopy (A := A)).toHom f t s =
      toUnitIntervalMap f (truncatedShift (t, Set.inclusion Ioc_subset_Icc_self s)) :=
  contractionMap_apply f t s

@[simp]
theorem contractionHomotopy_toHom_apply_of_lt (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1)
    (hst : (t : ℝ) < (s : ℝ)) :
    (contractionHomotopy (A := A)).toHom f t s =
      f ⟨(s : ℝ) - (t : ℝ), sub_pos.mpr hst, (sub_le_self _ t.property.1).trans s.property.2⟩ := by
  have hshift : truncatedShift (t, Set.inclusion Ioc_subset_Icc_self s) =
      Set.inclusion Ioc_subset_Icc_self ⟨(s : ℝ) - (t : ℝ), sub_pos.mpr hst,
        (sub_le_self _ t.property.1).trans s.property.2⟩ := by
    ext; simp [max_eq_left (sub_pos.mpr hst).le]
  rw [contractionHomotopy_toHom_apply, hshift, toUnitIntervalMap_apply_inclusion]

@[simp]
theorem contractionHomotopy_toHom_apply_of_le (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1)
    (hst : (s : ℝ) ≤ (t : ℝ)) : (contractionHomotopy (A := A)).toHom f t s = 0 := by
  have hshift : truncatedShift (t, Set.inclusion Ioc_subset_Icc_self s) = 0 := by
    ext; simp [max_eq_right (sub_nonpos.mpr hst)]
  rw [contractionHomotopy_toHom_apply, hshift, toUnitIntervalMap_apply_zero]

/-- Every cone C⋆-algebra `CStarCone A` is contractible. -/
theorem isContractibleCStarAlgebra (A : Type*) [NonUnitalCStarAlgebra A] :
    IsContractibleCStarAlgebra (CStarCone A) := ⟨contractionHomotopy⟩

end Contraction

end CStarCone

namespace CStarSuspension

section Basic

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Isometric `⋆`-homomorphism embedding `CStarSuspension A` into `CStarCone A` by setting the
value at `1` to `0`. -/
noncomputable def toCone : CStarSuspension A →⋆ₙₐ[ℂ] CStarCone A :=
  ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom ℂ A isOpenEmbedding_inclusion_Ioo_Ioc

@[simp] theorem toCone_apply_inclusion (f : CStarSuspension A) (x : Ioo (0 : ℝ) 1) :
    toCone f (Set.inclusion Ioo_subset_Ioc_self x) = f x := by simp [toCone]

@[simp] theorem toCone_apply_iocOne (f : CStarSuspension A) : toCone f iocOne = 0 := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_of_notMem isOpenEmbedding_inclusion_Ioo_Ioc f
    ((notMem_range_inclusion_Ioo_Ioc_iff iocOne).mpr rfl)

theorem evalOne_toCone (f : CStarSuspension A) : CStarCone.evalOne (toCone f) = 0 := by simp

@[simp] theorem evalOne_comp_toCone : (CStarCone.evalOne (A := A)).comp toCone = 0 :=
  NonUnitalStarAlgHom.ext evalOne_toCone

theorem toCone_injective : Function.Injective (toCone (A := A)) := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom]
  exact ZeroAtInftyContinuousMap.extendByZero_injective isOpenEmbedding_inclusion_Ioo_Ioc

theorem isometry_toCone : Isometry (toCone (A := A)) :=
  NonUnitalStarAlgHom.isometry toCone toCone_injective

/-- `CStarSuspension A` is `⋆`-isomorphic to the kernel of `CStarCone.evalOne`. -/
noncomputable def equivKerEvalOne :
    CStarSuspension A ≃⋆ₐ[ℂ] TwoSidedIdeal.ker (CStarCone.evalOne (A := A)) :=
  ZeroAtInftyContinuousMap.equivKerEvalOfNotMemRange A
    isOpenEmbedding_inclusion_Ioo_Ioc notMem_range_inclusion_Ioo_Ioc_iff

@[simp] theorem coe_equivKerEvalOne_apply (f : CStarSuspension A) :
    ((equivKerEvalOne f : TwoSidedIdeal.ker (CStarCone.evalOne (A := A))) : CStarCone A) =
      toCone f := by
  rw [equivKerEvalOne, ZeroAtInftyContinuousMap.coe_equivKerEvalOfNotMemRange_apply, toCone,
    ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom]

@[simp] theorem equivKerEvalOne_symm_apply
    (g : TwoSidedIdeal.ker (CStarCone.evalOne (A := A))) (x : Ioo (0 : ℝ) 1) :
    equivKerEvalOne.symm g x = (g : CStarCone A) (Set.inclusion Ioo_subset_Ioc_self x) := by
  simp [equivKerEvalOne]

/-- Restrict any cone element `f : CStarCone A` satisfying `CStarCone.evalOne f = 0` to
`CStarSuspension A`. -/
noncomputable def ofConeEqZero (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0) :
    CStarSuspension A :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_inclusion_Ioo_Ioc.isEmbedding f
    fun t ht => by
      rw [(notMem_range_inclusion_Ioo_Ioc_iff t).mp ht, ← CStarCone.evalOne_apply]; exact hf1

@[simp] theorem ofConeEqZero_apply (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0)
    (x : Ioo (0 : ℝ) 1) :
    ofConeEqZero f hf1 x = f (Set.inclusion Ioo_subset_Ioc_self x) := by simp [ofConeEqZero]

@[simp] theorem toCone_ofConeEqZero (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0) :
    toCone (ofConeEqZero f hf1) = f := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom, ofConeEqZero]
  exact ZeroAtInftyContinuousMap.extendByZero_restrictOfEqZero isOpenEmbedding_inclusion_Ioo_Ioc f _

@[simp] theorem ofConeEqZero_toCone (g : CStarSuspension A) :
    ofConeEqZero (toCone g) (evalOne_toCone g) = g := toCone_injective (toCone_ofConeEqZero _ _)

theorem mem_range_toCone_iff {f : CStarCone A} :
    f ∈ range (toCone (A := A)) ↔ CStarCone.evalOne f = 0 :=
  ⟨fun ⟨g, hg⟩ => hg ▸ evalOne_toCone g,
    fun hf1 => ⟨ofConeEqZero f hf1, toCone_ofConeEqZero f hf1⟩⟩

/-- Orientation-preserving `⋆`-isomorphism `CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A)` induced by
`iooZeroOneHomeomorphReal`. -/
noncomputable def equivReal (A : Type*) [NonUnitalCStarAlgebra A] :
    CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A) :=
  ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ A iooZeroOneHomeomorphReal

@[simp] theorem equivReal_apply (f : CStarSuspension A) (y : ℝ) :
    equivReal A f y = f (iooZeroOneHomeomorphReal.symm y) := by simp [equivReal]

@[simp] theorem equivReal_symm_apply (f : C₀(ℝ, A)) (x : Ioo (0 : ℝ) 1) :
    (equivReal A).symm f x = f (Real.tan (Real.pi * ((x : ℝ) - 2⁻¹))) := by simp [equivReal]

/-- Functorial action of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` on suspensions. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : CStarSuspension A →⋆ₙₐ[ℂ] CStarSuspension B :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom (Ioo (0 : ℝ) 1) φ (map_continuous φ)

@[simp] theorem map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : CStarSuspension A) (t : Ioo (0 : ℝ) 1) :
    map φ f t = φ (f t) := by simp [map]

@[simp] theorem map_id : map (.id ℂ A) = .id ℂ (CStarSuspension A) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_id (Ioo (0 : ℝ) 1)

theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_comp (Ioo (0 : ℝ) 1) φ ψ
    (map_continuous φ) (map_continuous ψ)

theorem toCone_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    toCone.comp (map φ) = (CStarCone.map φ).comp toCone := by
  ext f : 1
  exact DFunLike.coe_injective <| eq_of_iocOne_of_inclusion_Ioo_Ioc (by simp) (by simp)

/-- The inclusion `CStarSuspension A →⋆ₙₐ[ℂ] CStarCone A` is null-homotopic (the suspension is
subcontractible inside the cone). -/
noncomputable def toConeContractionHomotopy :
    NonUnitalStarAlgHom.Homotopy (toCone (A := A)) 0 where
  toHom := (CStarCone.contractionHomotopy (A := A)).toHom.comp toCone
  toHom_apply_zero g := by simp
  toHom_apply_one g := by simp

theorem toCone_homotopic_zero : NonUnitalStarAlgHom.Homotopic (toCone (A := A)) 0 :=
  ⟨toConeContractionHomotopy⟩

end Basic

section NonContractibleComplex

/-- Embedding `CStarSuspension ℂ →⋆ₙₐ[ℂ] C(unitInterval, ℂ)` as loops vanishing at `0` and `1`. -/
private noncomputable def toLoopMap : CStarSuspension ℂ →⋆ₙₐ[ℂ] C(I, ℂ) :=
  CStarCone.toUnitIntervalMap.comp toCone

private theorem toLoopMap_zero (f : CStarSuspension ℂ) : toLoopMap f 0 = 0 := by simp [toLoopMap]

private theorem toLoopMap_one (f : CStarSuspension ℂ) : toLoopMap f 1 = 0 := by simp [toLoopMap]

/-- The winding-number-`1` loop on `unitInterval` shifted by `-1`, vanishing at `0` and `1`. -/
private noncomputable def windingQuasiUnitaryMap : C(I, ℂ) where
  toFun s := ((AddCircle.homeomorphCircle one_ne_zero
    (AddCircle.zsmulLoop (1 : ℝ) 0 1 s) : Circle) : ℂ) - 1
  continuous_toFun := by fun_prop

private theorem windingQuasiUnitaryMap_zero : windingQuasiUnitaryMap 0 = 0 := by
  simp [windingQuasiUnitaryMap, AddCircle.homeomorphCircle_apply]

private theorem windingQuasiUnitaryMap_one : windingQuasiUnitaryMap 1 = 0 := by
  simp [windingQuasiUnitaryMap, AddCircle.homeomorphCircle_apply]

/-- The winding-number-`1` quasi-unitary generator in `CStarSuspension ℂ`. -/
private noncomputable def windingQuasiUnitary : CStarSuspension ℂ :=
  ofConeEqZero
    (CStarCone.ofUnitIntervalMapEqZero windingQuasiUnitaryMap windingQuasiUnitaryMap_zero)
    (by simp [windingQuasiUnitaryMap_one])

private theorem toLoopMap_injective : Function.Injective toLoopMap :=
  CStarCone.toUnitIntervalMap_injective.comp toCone_injective

private theorem toLoopMap_windingQuasiUnitary :
    toLoopMap windingQuasiUnitary = windingQuasiUnitaryMap := by
  simp [toLoopMap, windingQuasiUnitary]

private theorem windingQuasiUnitary_relation :
    star windingQuasiUnitary + windingQuasiUnitary +
      star windingQuasiUnitary * windingQuasiUnitary = 0 := by
  apply toLoopMap_injective
  ext s
  set u : Circle := AddCircle.homeomorphCircle one_ne_zero (AddCircle.zsmulLoop (1 : ℝ) 0 1 s)
  have hu : star (u : ℂ) * (u : ℂ) = 1 := by simp [mul_comm, Complex.mul_conj]
  simp only [map_add, map_mul, map_star, map_zero, toLoopMap_windingQuasiUnitary,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    ContinuousMap.zero_apply, windingQuasiUnitaryMap, ContinuousMap.coe_mk]
  rw [star_sub, star_one]; linear_combination hu

section NullHomotopy

variable (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
  (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ))

/-- Complex-valued continuous square `(t, s) ↦ toLoopMap (H_t(windingQuasiUnitary)) s` induced by
a null-homotopy `H` of `CStarSuspension ℂ`. -/
private noncomputable def windingComplexSquare : C(I × I, ℂ) :=
  ((ContinuousMap.compNonUnitalStarAlgHom I toLoopMap (map_continuous toLoopMap))
    (H.toHom windingQuasiUnitary)).uncurry

private theorem windingComplexSquare_apply (p : I × I) :
    windingComplexSquare H p = toLoopMap (H.toHom windingQuasiUnitary p.1) p.2 := by
  simp [windingComplexSquare, Function.uncurry]

private theorem windingComplexSquare_relation (p : I × I) :
    star (windingComplexSquare H p) + windingComplexSquare H p +
      star (windingComplexSquare H p) * windingComplexSquare H p = 0 := by
  have hrel := congrArg (fun x => toLoopMap (H.eval p.1 x) p.2) windingQuasiUnitary_relation
  simpa only [map_add, map_mul, map_star, map_zero, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.zero_apply,
    NonUnitalStarAlgHom.Homotopy.eval_apply, ← windingComplexSquare_apply] using hrel

/-- Circle-valued continuous square `(t, s) ↦ toLoopMap (H_t(windingQuasiUnitary)) s + 1` induced
by a null-homotopy `H` of `CStarSuspension ℂ`. -/
private noncomputable def windingCircleSquare : C(I × I, Circle) :=
  ⟨fun p => ⟨windingComplexSquare H p + 1, by
    have hmul : star (windingComplexSquare H p + 1) * (windingComplexSquare H p + 1) = 1 := by
      rw [star_add, star_one]; linear_combination windingComplexSquare_relation H p
    have hnorm_sq : ‖windingComplexSquare H p + 1‖ * ‖windingComplexSquare H p + 1‖ = 1 := by
      simpa only [CStarRing.norm_star_mul_self, norm_one] using congrArg norm hmul
    exact mem_sphere_zero_iff_norm.mpr (by nlinarith [norm_nonneg (windingComplexSquare H p + 1)])⟩,
    Continuous.subtype_mk ((windingComplexSquare H).continuous.add continuous_const) _⟩

private theorem coe_windingCircleSquare (t s : I) :
    (windingCircleSquare H (t, s) : ℂ) = toLoopMap (H.toHom windingQuasiUnitary t) s + 1 :=
  congrArg (· + 1) (windingComplexSquare_apply H (t, s))

/-- Transport a null-homotopy of `.id ℂ (CStarSuspension ℂ)` along `windingQuasiUnitary` to a
path homotopy from the winding-number-`1` loop on `AddCircle 1` to the constant loop. -/
private noncomputable def windingNullHomotopy :
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
          apply Circle.ext; rw [coe_windingCircleSquare]
          simp [toLoopMap_windingQuasiUnitary, windingQuasiUnitaryMap, eCircle]
        simp [W, hU0]
      map_one_left s := by
        have hU1 : U (1, s) = 1 := by apply Circle.ext; rw [coe_windingCircleSquare]; simp
        simp [W, hU1, he1]
      prop' t s hs := by
        have hUs : U (t, s) = 1 := by
          apply Circle.ext; rw [coe_windingCircleSquare]
          rcases hs with rfl | rfl <;> simp [toLoopMap_zero, toLoopMap_one]
        rcases hs with rfl | rfl <;> simp [W, hUs, he1] }

end NullHomotopy

/-- `CStarSuspension ℂ = C₀((0, 1), ℂ)` is not contractible (Blackadar, II.5.5.11): any homotopy
from `.id` to `0` transports the quasi-unitary loop `s ↦ exp(2πis) - 1` to a null-homotopy of the
winding-number-`1` loop in `AddCircle 1`. -/
theorem not_isContractibleCStarAlgebra_complex :
    ¬IsContractibleCStarAlgebra (CStarSuspension ℂ) := by
  rintro ⟨H⟩
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have h0 : AddCircle.windingNumber (p := (1 : ℝ)) (x := ((0 : ℝ) : AddCircle (1 : ℝ)))
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl _))) = 0 := by
    have hdiv := AddCircle.windingNumber_eq_div (p := (1 : ℝ))
      (Path.refl ((0 : ℝ) : AddCircle (1 : ℝ))) (ContinuousMap.const I 0) rfl
    norm_num at hdiv
    exact Int.cast_eq_zero.mp hdiv
  have hfg : (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (AddCircle.zsmulLoop (1 : ℝ) 0 1)) :
        FundamentalGroup (AddCircle (1 : ℝ)) (0 : ℝ)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (Path.refl ((0 : ℝ) : AddCircle (1 : ℝ)))) :=
    congrArg FundamentalGroup.fromPath (Quotient.sound ⟨windingNullHomotopy H⟩)
  have hw := congrArg (AddCircle.windingNumber (p := (1 : ℝ)) (x := (0 : ℝ))) hfg
  rw [AddCircle.windingNumber_zsmulLoop (p := (1 : ℝ)) 0 1] at hw
  exact one_ne_zero (hw.trans h0)

end NonContractibleComplex

end CStarSuspension

/-- `C₀(ℝ, ℂ)` is not contractible. -/
theorem not_isContractibleCStarAlgebra_zeroAtInfty_real : ¬IsContractibleCStarAlgebra C₀(ℝ, ℂ) :=
  fun h =>
    CStarSuspension.not_isContractibleCStarAlgebra_complex
      ((IsContractibleCStarAlgebra.iff_of_starAlgEquiv (CStarSuspension.equivReal ℂ)).mpr h)

end TauCeti
