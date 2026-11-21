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

/-!
# Cone and suspension C⋆-algebras

For a non-unital complex C⋆-algebra `A`, the cone and suspension C⋆-algebras are
`CStarCone A := C₀(Set.Ioc (0 : ℝ) 1, A)` and `CStarSuspension A := C₀(Set.Ioo (0 : ℝ) 1, A)`,
equipped with the supremum norm and pointwise `⋆`-algebra operations (Blackadar,
*Operator Algebras*, II.5.5.10–II.5.5.11).

## Main declarations

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

namespace TauCeti

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

@[simp]
theorem pathQuotientKerEvalZeroEquiv_mk (A : Type*) [NonUnitalCStarAlgebra A] (f : C(I, A)) :
    pathQuotientKerEvalZeroEquiv A
        (TwoSidedIdeal.Quotient.mk
          (TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I))) f) = f 0 :=
  (NonUnitalStarAlgHom.quotientKerEquivOfSurjective_mk
    (φ := ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I)) _ f).trans
    (ContinuousMap.evalNonUnitalStarAlgHom_apply ℂ A (0 : I) f)

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
  ext t; simp [toPath]

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
    ZeroAtInftyContinuousMap.ext fun t => by simpa [coe_toPath_apply] using DFunLike.congr_fun h t

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

@[simp]
theorem equivKerEvalZero_symm_apply
    (g : TwoSidedIdeal.ker (ContinuousMap.evalNonUnitalStarAlgHom ℂ A (0 : I)))
    (x : Ioc (0 : ℝ) 1) :
    equivKerEvalZero.symm g x = (g : C(I, A)) (iocToUnitInterval x) := by
  simp [equivKerEvalZero]

/-- Evaluation at `1` as a `⋆`-homomorphism `CStarCone A →⋆ₙₐ[ℂ] A`. -/
abbrev evalOne : CStarCone A →⋆ₙₐ[ℂ] A :=
  ZeroAtInftyContinuousMap.evalNonUnitalStarAlgHom ℂ A iocOne

theorem evalOne_apply (f : CStarCone A) : evalOne f = f iocOne := by simp [evalOne]

@[simp]
theorem toPath_apply_one (f : CStarCone A) : toPath f 1 = evalOne f := by
  rw [← iocToUnitInterval_iocOne, toPath_apply_ioc, evalOne_apply]

/-- Restrict any path `g : C(unitInterval, A)` with `g 0 = 0` to `CStarCone A`. -/
noncomputable def ofPathEqZero (g : C(I, A)) (hg0 : g 0 = 0) : CStarCone A :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_iocToUnitInterval.isEmbedding
    (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty g) fun t ht => by
      rw [(notMem_range_iocToUnitInterval_iff t).mp ht]; simpa using hg0

@[simp]
theorem ofPathEqZero_apply (g : C(I, A)) (hg0 : g 0 = 0) (x : Ioc (0 : ℝ) 1) :
    ofPathEqZero g hg0 x = g (iocToUnitInterval x) := by simp [ofPathEqZero]

@[simp]
theorem toPath_ofPathEqZero (g : C(I, A)) (hg0 : g 0 = 0) : toPath (ofPathEqZero g hg0) = g := by
  ext t
  by_cases ht0 : t = 0
  · subst ht0; rw [toPath_apply_zero, hg0]
  · obtain ⟨x, rfl⟩ := notMem_compl_iff.mp fun hx =>
      ht0 ((notMem_range_iocToUnitInterval_iff t).mp hx)
    rw [toPath_apply_ioc, ofPathEqZero_apply]

@[simp]
theorem ofPathEqZero_toPath (f : CStarCone A) :
    ofPathEqZero (toPath f) (toPath_apply_zero f) = f :=
  toPath_injective (toPath_ofPathEqZero _ _)

theorem mem_range_toPath_iff {g : C(I, A)} :
    g ∈ range (toPath (A := A)) ↔ g 0 = 0 :=
  ⟨fun ⟨f, hf⟩ => hf ▸ toPath_apply_zero f,
    fun hg0 => ⟨ofPathEqZero g hg0, toPath_ofPathEqZero g hg0⟩⟩

/-- Linear cone element `t ↦ (t : ℝ) • a` in `CStarCone A`. -/
noncomputable def linearPath (a : A) : CStarCone A :=
  ofPathEqZero ⟨fun t : I => (t : ℝ) • a, continuous_subtypeVal.smul continuous_const⟩ (by simp)

@[simp]
theorem linearPath_apply (a : A) (t : Ioc (0 : ℝ) 1) : linearPath a t = (t : ℝ) • a := by
  simp [linearPath]

theorem evalOne_linearPath (a : A) : evalOne (linearPath a) = a := by simp

@[simp]
theorem norm_linearPath (a : A) : ‖linearPath a‖ = ‖a‖ :=
  le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg a)).mpr fun t => by
    rw [linearPath_apply, norm_smul, Real.norm_of_nonneg t.property.1.le]
    exact mul_le_of_le_one_left (norm_nonneg a) t.property.2)
    (by simpa only [linearPath_apply, coe_iocOne, one_smul] using
      ZeroAtInftyContinuousMap.norm_coe_le_norm (linearPath a) iocOne)

theorem evalOne_surjective : Function.Surjective (evalOne (A := A)) :=
  fun a => ⟨linearPath a, evalOne_linearPath a⟩

/-- The quotient of `CStarCone A` by the kernel of `evalOne` is `⋆`-isomorphic to `A`. -/
noncomputable def quotientKerEvalOneEquiv :
    CStarCone A ⧸ TwoSidedIdeal.ker (evalOne (A := A)) ≃⋆ₐ[ℂ] A :=
  NonUnitalStarAlgHom.quotientKerEquivOfSurjective evalOne_surjective

@[simp]
theorem quotientKerEvalOneEquiv_mk (f : CStarCone A) :
    quotientKerEvalOneEquiv (TwoSidedIdeal.Quotient.mk (TwoSidedIdeal.ker (evalOne (A := A))) f) =
      f iocOne := by
  simp [quotientKerEvalOneEquiv]

/-- Functorial action of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` on cones. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : CStarCone A →⋆ₙₐ[ℂ] CStarCone B :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom (Ioc (0 : ℝ) 1) φ (map_continuous φ)

@[simp]
theorem map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : CStarCone A) (t : Ioc (0 : ℝ) 1) :
    map φ f t = φ (f t) := by simp [map]

@[simp]
theorem map_id : map (.id ℂ A) = .id ℂ (CStarCone A) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_id (Ioc (0 : ℝ) 1)

theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_comp (Ioc (0 : ℝ) 1) φ ψ
    (map_continuous φ) (map_continuous ψ)

@[simp]
theorem evalOne_comp_map (φ : A →⋆ₙₐ[ℂ] B) : evalOne.comp (map φ) = φ.comp evalOne := by
  ext f; simp

theorem toPath_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    toPath.comp (map φ) =
      (ContinuousMap.compNonUnitalStarAlgHom I φ (map_continuous φ)).comp toPath := by
  ext f t
  by_cases ht0 : t = 0
  · subst ht0; simp
  · obtain ⟨x, rfl⟩ := notMem_compl_iff.mp fun hx =>
      ht0 ((notMem_range_iocToUnitInterval_iff t).mp hx)
    simp

end Basic

section Contraction

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Continuous path `t ↦ φ_t(f)` in `CStarCone A` induced by precomposing `toPath f` with
`truncatedShift`. -/
private noncomputable def contractionPath (f : CStarCone A) : C(I, CStarCone A) where
  toFun t := ofPathEqZero (((toPath f).comp truncatedShift).curry t) (by
    rw [ContinuousMap.curry_apply, ContinuousMap.comp_apply, truncatedShift_zero_right,
      toPath_apply_zero])
  continuous_toFun := by
    rw [(isometry_toPath (A := A)).isUniformInducing.isInducing.continuous_iff]
    convert ((toPath f).comp truncatedShift).curry.continuous using 1
    ext t s
    simp

@[simp]
private theorem contractionPath_apply (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1) :
    contractionPath f t s = toPath f (truncatedShift (t, iocToUnitInterval s)) := by
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
  eval_zero f := by ext s; simp
  eval_one f := by ext s; simp

@[simp]
theorem contractionHomotopy_toHom_apply_of_lt (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1)
    (hst : (t : ℝ) < (s : ℝ)) :
    (contractionHomotopy (A := A)).toHom f t s =
      f ⟨(s : ℝ) - (t : ℝ), sub_pos.mpr hst, (sub_le_self _ t.property.1).trans s.property.2⟩ := by
  have hshift : truncatedShift (t, iocToUnitInterval s) =
      iocToUnitInterval ⟨(s : ℝ) - (t : ℝ), sub_pos.mpr hst,
        (sub_le_self _ t.property.1).trans s.property.2⟩ := by
    ext; simp [max_eq_left (sub_pos.mpr hst).le]
  simp [contractionHomotopy, hshift]

@[simp]
theorem contractionHomotopy_toHom_apply_of_le (f : CStarCone A) (t : I) (s : Ioc (0 : ℝ) 1)
    (hst : (s : ℝ) ≤ (t : ℝ)) : (contractionHomotopy (A := A)).toHom f t s = 0 := by
  have hshift : truncatedShift (t, iocToUnitInterval s) = 0 := by
    ext; simp [max_eq_right (sub_nonpos.mpr hst)]
  simp [contractionHomotopy, hshift]

/-- Every cone C⋆-algebra `CStarCone A` is contractible. -/
theorem isContractible (A : Type*) [NonUnitalCStarAlgebra A] :
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
  ZeroAtInftyContinuousMap.extendByZeroNonUnitalStarAlgHom ℂ A isOpenEmbedding_iooToIoc

@[simp]
theorem toCone_apply_ioo (f : CStarSuspension A) (x : Ioo (0 : ℝ) 1) :
    toCone f (iooToIoc x) = f x := by simp [toCone]

@[simp]
theorem toCone_apply_iocOne (f : CStarSuspension A) : toCone f iocOne = 0 := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom]
  exact ZeroAtInftyContinuousMap.extendByZero_apply_of_notMem isOpenEmbedding_iooToIoc f
    ((notMem_range_iooToIoc_iff iocOne).mpr rfl)

theorem toCone_apply_one (f : CStarSuspension A) : CStarCone.evalOne (toCone f) = 0 := by simp

@[simp]
theorem evalOne_comp_toCone : (CStarCone.evalOne (A := A)).comp toCone = 0 :=
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

@[simp]
theorem equivKerEvalOne_symm_apply
    (g : TwoSidedIdeal.ker (CStarCone.evalOne (A := A))) (x : Ioo (0 : ℝ) 1) :
    equivKerEvalOne.symm g x = (g : CStarCone A) (iooToIoc x) := by
  simp [equivKerEvalOne]

/-- Restrict any cone element `f : CStarCone A` satisfying `CStarCone.evalOne f = 0` to
`CStarSuspension A`. -/
noncomputable def ofConeEqZero (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0) :
    CStarSuspension A :=
  ZeroAtInftyContinuousMap.restrictOfEqZero isOpenEmbedding_iooToIoc.isEmbedding f fun t ht => by
    rw [(notMem_range_iooToIoc_iff t).mp ht, ← CStarCone.evalOne_apply]; exact hf1

@[simp]
theorem ofConeEqZero_apply (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0)
    (x : Ioo (0 : ℝ) 1) : ofConeEqZero f hf1 x = f (iooToIoc x) := by simp [ofConeEqZero]

@[simp]
theorem toCone_ofConeEqZero (f : CStarCone A) (hf1 : CStarCone.evalOne f = 0) :
    toCone (ofConeEqZero f hf1) = f := by
  rw [toCone, ZeroAtInftyContinuousMap.coe_extendByZeroNonUnitalStarAlgHom, ofConeEqZero]
  exact ZeroAtInftyContinuousMap.extendByZero_restrictOfEqZero isOpenEmbedding_iooToIoc f _

@[simp]
theorem ofConeEqZero_toCone (g : CStarSuspension A) :
    ofConeEqZero (toCone g) (toCone_apply_one g) = g :=
  toCone_injective (toCone_ofConeEqZero _ _)

theorem mem_range_toCone_iff {f : CStarCone A} :
    f ∈ range (toCone (A := A)) ↔ CStarCone.evalOne f = 0 :=
  ⟨fun ⟨g, hg⟩ => hg ▸ toCone_apply_one g,
    fun hf1 => ⟨ofConeEqZero f hf1, toCone_ofConeEqZero f hf1⟩⟩

/-- Orientation-preserving `⋆`-isomorphism `CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A)` induced by
`iooZeroOneHomeomorphReal`. -/
noncomputable def equivReal (A : Type*) [NonUnitalCStarAlgebra A] :
    CStarSuspension A ≃⋆ₐ[ℂ] C₀(ℝ, A) :=
  ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv ℂ A iooZeroOneHomeomorphReal

@[simp]
theorem equivReal_apply (f : CStarSuspension A) (y : ℝ) :
    equivReal A f y = f (iooZeroOneHomeomorphReal.symm y) := by
  simp [equivReal]

@[simp]
theorem equivReal_symm_apply (f : C₀(ℝ, A)) (x : Ioo (0 : ℝ) 1) :
    (equivReal A).symm f x = f (Real.tan (Real.pi * ((x : ℝ) - 2⁻¹))) := by simp [equivReal]

/-- Functorial action of a `⋆`-homomorphism `φ : A →⋆ₙₐ[ℂ] B` on suspensions. -/
def map (φ : A →⋆ₙₐ[ℂ] B) : CStarSuspension A →⋆ₙₐ[ℂ] CStarSuspension B :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom (Ioo (0 : ℝ) 1) φ (map_continuous φ)

@[simp]
theorem map_apply (φ : A →⋆ₙₐ[ℂ] B) (f : CStarSuspension A) (t : Ioo (0 : ℝ) 1) :
    map φ f t = φ (f t) := by simp [map]

@[simp]
theorem map_id : map (.id ℂ A) = .id ℂ (CStarSuspension A) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_id (Ioo (0 : ℝ) 1)

theorem map_comp (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B) :
    map (ψ.comp φ) = (map ψ).comp (map φ) :=
  ZeroAtInftyContinuousMap.compLeftNonUnitalStarAlgHom_comp (Ioo (0 : ℝ) 1) φ ψ
    (map_continuous φ) (map_continuous ψ)

theorem toCone_comp_map (φ : A →⋆ₙₐ[ℂ] B) :
    toCone.comp (map φ) = (CStarCone.map φ).comp toCone := by
  ext f t
  by_cases ht1 : t = iocOne
  · subst ht1; simp
  · obtain ⟨x, rfl⟩ := notMem_compl_iff.mp fun hx =>
      ht1 ((notMem_range_iooToIoc_iff t).mp hx)
    simp

/-- The inclusion `CStarSuspension A →⋆ₙₐ[ℂ] CStarCone A` is null-homotopic (the suspension is
subcontractible inside the cone). -/
noncomputable def toConeContractionHomotopy :
    NonUnitalStarAlgHom.Homotopy (toCone (A := A)) 0 :=
  (by ext f t; rfl : (0 : CStarCone A →⋆ₙₐ[ℂ] CStarCone A).comp (toCone (A := A)) = 0) ▸
    (CStarCone.contractionHomotopy (A := A)).compRight toCone

theorem toCone_homotopic_zero : NonUnitalStarAlgHom.Homotopic (toCone (A := A)) 0 :=
  ⟨toConeContractionHomotopy⟩

end Basic

section NonContractibleComplex

/-- Embedding `CStarSuspension ℂ →⋆ₙₐ[ℂ] C(unitInterval, ℂ)` as paths vanishing at `0` and `1`. -/
private noncomputable def toLoopPath : CStarSuspension ℂ →⋆ₙₐ[ℂ] C(I, ℂ) :=
  CStarCone.toPath.comp toCone

private theorem toLoopPath_zero (f : CStarSuspension ℂ) : toLoopPath f 0 = 0 := by simp [toLoopPath]

private theorem toLoopPath_one (f : CStarSuspension ℂ) : toLoopPath f 1 = 0 := by simp [toLoopPath]

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
  ofConeEqZero (CStarCone.ofPathEqZero windingQuasiUnitaryPath windingQuasiUnitaryPath_zero)
    (by simp [windingQuasiUnitaryPath_one])

private theorem toLoopPath_windingQuasiUnitary :
    toLoopPath windingQuasiUnitary = windingQuasiUnitaryPath := by
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
    rw [mul_comm, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, u.norm_coe]; simp
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.star_apply,
    ContinuousMap.zero_apply, windingQuasiUnitaryPath, ContinuousMap.coe_mk]
  rw [star_sub, star_one]; linear_combination hu

section NullHomotopy

variable (H : NonUnitalStarAlgHom.Homotopy (.id ℂ (CStarSuspension ℂ))
  (0 : CStarSuspension ℂ →⋆ₙₐ[ℂ] CStarSuspension ℂ))

/-- Complex-valued continuous square `(t, s) ↦ toLoopPath (H_t(windingQuasiUnitary)) s` induced by
a null-homotopy `H` of `CStarSuspension ℂ`. -/
private noncomputable def windingComplexSquare : C(I × I, ℂ) :=
  ((ContinuousMap.compNonUnitalStarAlgHom I toLoopPath (map_continuous toLoopPath))
    (H.toHom windingQuasiUnitary)).uncurry

private theorem windingComplexSquare_apply (p : I × I) :
    windingComplexSquare H p = toLoopPath (H.toHom windingQuasiUnitary p.1) p.2 := by
  simp [windingComplexSquare, Function.uncurry]

private theorem windingComplexSquare_relation (p : I × I) :
    star (windingComplexSquare H p) + windingComplexSquare H p +
      star (windingComplexSquare H p) * windingComplexSquare H p = 0 := by
  have hrel := congrArg (fun x => toLoopPath (H.eval p.1 x) p.2) windingQuasiUnitary_relation
  simpa only [map_add, map_mul, map_star, map_zero, ContinuousMap.add_apply,
    ContinuousMap.mul_apply, ContinuousMap.star_apply, ContinuousMap.zero_apply,
    NonUnitalStarAlgHom.Homotopy.eval_apply, ← windingComplexSquare_apply] using hrel

/-- Circle-valued continuous square `(t, s) ↦ toLoopPath (H_t(windingQuasiUnitary)) s + 1` induced
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
    (windingCircleSquare H (t, s) : ℂ) = toLoopPath (H.toHom windingQuasiUnitary t) s + 1 :=
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
          simp [toLoopPath_windingQuasiUnitary, windingQuasiUnitaryPath, eCircle]
        simp [W, hU0]
      map_one_left s := by
        have hU1 : U (1, s) = 1 := by apply Circle.ext; rw [coe_windingCircleSquare]; simp
        simp [W, hU1, he1]
      prop' t s hs := by
        have hUs : U (t, s) = 1 := by
          apply Circle.ext; rw [coe_windingCircleSquare]
          rcases hs with rfl | rfl <;> simp [toLoopPath_zero, toLoopPath_one]
        rcases hs with rfl | rfl <;> simp [W, hUs, he1] }

end NullHomotopy

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
  exact one_ne_zero (hw.trans (by simp [AddCircle.windingNumber]))

end NonContractibleComplex

end CStarSuspension

/-- `C₀(ℝ, ℂ)` is not contractible. -/
theorem not_isContractibleCStarAlgebra_c0_real : ¬IsContractibleCStarAlgebra C₀(ℝ, ℂ) := fun h =>
  CStarSuspension.not_isContractible_complex
    ((IsContractibleCStarAlgebra.iff_of_starAlgEquiv (CStarSuspension.equivReal ℂ)).mpr h)

end TauCeti
