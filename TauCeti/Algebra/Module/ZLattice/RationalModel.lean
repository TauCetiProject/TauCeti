/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Determinant
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization
public import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# The rational model of an integral lattice in a real inner product space

Let `L` be a full integral lattice in a finite-dimensional real inner product space `E`. Its inner
product is an integer-valued symmetric form `ZLattice.IsIntegral.integralForm` on `L`, and
`TauCeti.IntegralLattice.ofIntegralForm` rationalizes it to an integral lattice in the rational
vector space `ℚ ⊗[ℤ] L`. This is the *rational model* `ZLattice.ratModel` of `L`: an integral
lattice in the sense of `TauCeti.IntegralLattice`, whose carrier is the image `1 ⊗ L` of `L`.

The map `ZLattice.ratModelMap L : ℚ ⊗[ℤ] L → E`, `q ⊗ x ↦ q • x`, is injective, carries the
rational form to the inner product of `E`, and carries the carrier of the rational model exactly
onto `L`. Consequently the rational model is positive definite and nondegenerate, it has the rank
of `L`, it is even exactly when `L` is, and it is unimodular exactly when `L` is; its determinant
and its discriminant are both the determinant `ZLattice.det L = covolume L ^ 2` of `L`.

The bridge extends to duals. The map `ratModelMap` carries the dual carrier of the rational model
onto the dual lattice `L^∨` (`ZLattice.mem_ratModel_dualCarrier_iff`; surjectivity uses that `L` has
finite index in `L^∨`), which identifies the two duals (`ZLattice.ratModelDualEquiv`) and the two
discriminant groups (`ZLattice.ratModelDiscriminantGroupEquiv`). Under this identification the
discriminant pairing of the rational model is the inner product `⟪x, y⟫` of `x, y ∈ L^∨` modulo `ℤ`,
and, for even `L`, its discriminant quadratic map is the half-norm `‖x‖² / 2` modulo `ℤ`.

These comparisons let the arithmetic theory of rational integral lattices (discriminant forms,
isometry classes, genus invariants) be applied to lattices in Euclidean space, such as those
whose theta series are studied analytically.

## Main definitions

* `ZLattice.ratModelMap L`: the map `ℚ ⊗[ℤ] L → E`, `q ⊗ x ↦ q • x`.
* `ZLattice.ratModel hL`: the rational model of an integral full lattice `L`.
* `ZLattice.ratModelCarrierEquiv hL`: the identification of `L` with the carrier of its rational
  model.
* `ZLattice.ratModelDualEquiv hL`: the identification of `L^∨` with the dual carrier of the
  rational model.
* `ZLattice.ratModelDiscriminantGroupEquiv hL`: the identification of the discriminant group
  `L^∨ ⧸ L` with the discriminant group of the rational model.

## Main results

* `ZLattice.ratModelMap_injective`: the map `ℚ ⊗[ℤ] L → E` is injective.
* `ZLattice.ratModel_form_cast`: the rational form is the inner product of `E`.
* `ZLattice.mem_ratModel_carrier_iff`: the carrier of the rational model is the preimage of
  `L`.
* `ZLattice.isPosDef_ratModel`, `ZLattice.instIsNondegenerateRatModel`: the rational model is
  positive definite and nondegenerate.
* `ZLattice.finrank_ratModel`, `ZLattice.isEven_ratModel_iff`,
  `ZLattice.isUnimodular_ratModel_iff`: rank, evenness and unimodularity agree.
* `ZLattice.determinant_ratModel`, `ZLattice.discriminant_ratModel`: the determinant and the
  discriminant of the rational model are `ZLattice.det L`.
* `ZLattice.mem_ratModel_dualCarrier_iff`, `ZLattice.exists_ratModelMap_eq_of_mem_dual`: the dual
  carrier of the rational model is the preimage of `L^∨`, and `ratModelMap` maps it onto `L^∨`.
* `ZLattice.discriminantPairing_ratModelDiscriminantGroupEquiv_mk_eq_coe_iff`,
  `ZLattice.discriminantQuadraticMap_ratModelDiscriminantGroupEquiv_mk_eq_coe_iff`: the
  discriminant pairing and quadratic map of the rational model are `⟪x, y⟫` and `‖x‖² / 2`
  modulo `ℤ`, computed on representatives in `L^∨`.

## Implementation notes

The space `E` carries no `ℚ`-module structure of its own, so `ratModelMap` is stated as a
`ℤ`-linear map. Inside this file the `ℚ`-module structure restricted from `ℝ` is a local instance,
used to build `ratModelMap` from `LinearMap.liftBaseChange` and to prove it injective.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* @sqrt-of-2, [Tau Ceti PR #20950](https://github.com/TauCetiProject/TauCeti/pull/20950), an
  earlier formalization of this rational model whose approach is adapted here.
-/

public section

open Module TensorProduct
open scoped RealInnerProductSpace

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Rational scalars act on `E` through their embedding into the real scalars. -/
noncomputable local instance moduleRat : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)

/-- The restricted rational action is compatible with the real action. -/
local instance isScalarTower_rat_real : IsScalarTower ℚ ℝ E :=
  ⟨fun q r x ↦ mul_smul (q : ℝ) r x⟩

/-- The canonical map `ℚ ⊗[ℤ] L → E`, `q ⊗ x ↦ q • x`, from the scalar extension of a lattice to
its ambient real space. -/
noncomputable def ratModelMap (L : Submodule ℤ E) : ℚ ⊗[ℤ] L →ₗ[ℤ] E :=
  (L.subtype.liftBaseChange ℚ).restrictScalars ℤ

/-- The map `ratModelMap L` sends a pure tensor `q ⊗ x` to the real multiple `q • x`. -/
@[simp]
theorem ratModelMap_tmul (L : Submodule ℤ E) (q : ℚ) (x : L) :
    ratModelMap L (q ⊗ₜ[ℤ] x) = (q : ℝ) • (x : E) := by
  rw [ratModelMap, LinearMap.restrictScalars_apply, LinearMap.liftBaseChange_tmul]
  exact (IsScalarTower.algebraMap_smul ℝ q (x : E)).symm

/-- The canonical map `ℚ ⊗[ℤ] L → E` is injective. -/
theorem ratModelMap_injective {L : Submodule ℤ E} : Function.Injective (ratModelMap L) :=
  L.subtype.liftBaseChange_injective (K := ℚ) (nonZeroDivisors ℤ) L.injective_subtype

variable {L : Submodule ℤ E} [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The **rational model** of an integral full lattice `L`: the integral lattice in `ℚ ⊗[ℤ] L`
obtained by rationalizing the integer-valued inner product of `L`. -/
noncomputable def ratModel (hL : IsIntegral L) : TauCeti.IntegralLattice (ℚ ⊗[ℤ] L) :=
  have := ZLattice.module_free ℝ L
  have := ZLattice.module_finite ℝ L
  TauCeti.IntegralLattice.ofIntegralForm hL.integralForm hL.isSymm_integralForm

/-- The form of the rational model is the scalar extension of the integer-valued inner
product. -/
@[simp]
theorem ratModel_form (hL : IsIntegral L) :
    (ratModel hL).form = hL.integralForm.baseChange ℚ :=
  TauCeti.IntegralLattice.ofIntegralForm_form _ _

/-- The form of the rational model is the inner product of `E`, read through `ratModelMap`. -/
theorem ratModel_form_cast (hL : IsIntegral L) (x y : ℚ ⊗[ℤ] L) :
    ((ratModel hL).form x y : ℝ) = ⟪ratModelMap L x, ratModelMap L y⟫ := by
  rw [ratModel_form]
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, Rat.cast_add, inner_add_left, hx, hz]
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, Rat.cast_add, inner_add_right, hy, hz]
    | tmul r y =>
      simp only [LinearMap.BilinForm.baseChange_tmul, ratModelMap_tmul, inner_smul_left,
        inner_smul_right, conj_trivial, zsmul_eq_mul]
      push_cast [IsIntegral.integralForm_cast]
      ring

/-- The identification of an integral full lattice `L` with the carrier of its rational model,
`x ↦ 1 ⊗ x`. -/
noncomputable def ratModelCarrierEquiv (hL : IsIntegral L) : L ≃ₗ[ℤ] ratModel hL :=
  have := ZLattice.module_free ℝ L
  have := ZLattice.module_finite ℝ L
  TauCeti.IntegralLattice.ofIntegralForm.carrierEquiv _ _

@[simp]
theorem coe_ratModelCarrierEquiv (hL : IsIntegral L) (x : L) :
    (ratModelCarrierEquiv hL x : ℚ ⊗[ℤ] L) = 1 ⊗ₜ[ℤ] x :=
  TauCeti.IntegralLattice.ofIntegralForm.coe_carrierEquiv_apply _ _ _

/-- The inverse carrier identification recovers a lattice vector from its unit pure tensor. -/
@[simp]
theorem ratModelCarrierEquiv_symm_tmul (hL : IsIntegral L) (x : L)
    (h : (1 : ℚ) ⊗ₜ[ℤ] x ∈ (ratModel hL).carrier) :
    (ratModelCarrierEquiv hL).symm ⟨1 ⊗ₜ[ℤ] x, h⟩ = x :=
  TauCeti.IntegralLattice.ofIntegralForm.carrierEquiv_symm_tmul _ _ _ _

/-- The carrier identification carries the integer-valued inner product of `L` to the integral
form of the rational model. -/
@[simp]
theorem integralForm_ratModelCarrierEquiv (hL : IsIntegral L) (x y : L) :
    (ratModel hL).integralForm (ratModelCarrierEquiv hL x) (ratModelCarrierEquiv hL y) =
      hL.integralForm x y :=
  TauCeti.IntegralLattice.ofIntegralForm.integralForm_carrierEquiv _ _ _ _

/-- The carrier of the rational model is the preimage of `L` under `ratModelMap`. -/
@[simp]
theorem mem_ratModel_carrier_iff (hL : IsIntegral L) (x : ℚ ⊗[ℤ] L) :
    x ∈ (ratModel hL).carrier ↔ ratModelMap L x ∈ L := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · obtain ⟨y, hy⟩ := (ratModelCarrierEquiv hL).surjective ⟨x, hx⟩
    have : (ratModelCarrierEquiv hL y : ℚ ⊗[ℤ] L) = x := congrArg Subtype.val hy
    simp [← this]
  · have : ratModelCarrierEquiv hL ⟨_, hx⟩ = x := ratModelMap_injective (by simp)
    exact this ▸ (ratModelCarrierEquiv hL ⟨_, hx⟩).property

/-- The rational model of an integral full lattice is positive definite. -/
theorem isPosDef_ratModel (hL : IsIntegral L) : (ratModel hL).IsPosDef := by
  refine (ratModel hL).isPosDef_iff.mpr fun x hx ↦ ?_
  have hne : ratModelMap L x ≠ 0 := fun h ↦ hx (ratModelMap_injective (h.trans (map_zero _).symm))
  have hpos := real_inner_self_pos.mpr hne
  rw [← ratModel_form_cast hL] at hpos
  exact_mod_cast hpos

/-- The rational model of an integral full lattice is nondegenerate. -/
instance instIsNondegenerateRatModel (hL : IsIntegral L) : (ratModel hL).IsNondegenerate :=
  ⟨((ratModel hL).isPosDef_iff_isPosSemidef_and_nondegenerate.mp (isPosDef_ratModel hL)).2⟩

/-- The rank of the rational model is the rank of `L`, the dimension of `E`. -/
@[simp]
theorem finrank_ratModel (hL : IsIntegral L) : finrank ℤ (ratModel hL) = finrank ℝ E :=
  (ratModelCarrierEquiv hL).symm.finrank_eq.trans (ZLattice.rank ℝ L)

/-- The rational model is even exactly when `L` is. -/
@[simp]
theorem isEven_ratModel_iff (hL : IsIntegral L) : (ratModel hL).IsEven ↔ IsEven L := by
  rw [(ratModel hL).isEven_iff_of_integralForm_equiv hL.integralForm (ratModelCarrierEquiv hL)
    fun x ↦ integralForm_ratModelCarrierEquiv hL x x, isEven_iff, Subtype.forall]
  refine forall₂_congr fun x hx ↦ ?_
  rw [even_iff_exists_two_mul]
  refine exists_congr fun m ↦ ?_
  rw [← Int.cast_inj (α := ℝ)]
  simp

section Determinant

variable [MeasurableSpace E] [BorelSpace E]

/-- The determinant of the rational model is the determinant `covolume L ^ 2` of `L`. -/
@[simp]
theorem determinant_ratModel (hL : IsIntegral L) :
    ((ratModel hL).determinant : ℝ) = det L := by
  classical
  have := ZLattice.module_free ℝ L
  have := ZLattice.module_finite ℝ L
  let b := Free.chooseBasis ℤ L
  let e := ratModelCarrierEquiv hL
  -- realize the rational model in `E` through the inclusion of `L`
  let φ : ratModel hL →ₗ[ℤ] E := L.subtype ∘ₗ e.symm.toLinearMap
  have hφ (x y : ratModel hL) : ⟪φ x, φ y⟫ = (ratModel hL).integralForm x y := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    simp [φ, e]
  rw [det_eq_det_gram L b, ← TauCeti.IntegralLattice.det_gram_comp_eq_determinant hφ (b.map e)]
  simp [φ]

/-- The discriminant of the rational model is the determinant `covolume L ^ 2` of `L`. -/
@[simp]
theorem discriminant_ratModel (hL : IsIntegral L) :
    ((ratModel hL).discriminant : ℝ) = det L := by
  rw [TauCeti.IntegralLattice.discriminant_def, Nat.cast_natAbs, Int.cast_abs,
    determinant_ratModel, abs_of_pos (det_pos L)]

end Determinant

/-- The rational model is unimodular exactly when `L` is. -/
theorem isUnimodular_ratModel_iff (hL : IsIntegral L) :
    (ratModel hL).IsUnimodular ↔ IsUnimodular L := by
  -- both sides are measure-free; compare them through the determinant for the Borel structure
  borelize E
  rw [(ratModel hL).isUnimodular_iff_discriminant_eq_one, hL.isUnimodular_iff_det_eq_one,
    ← discriminant_ratModel hL, Nat.cast_eq_one]

/-! ### The dual lattice and the discriminant group -/

section Discriminant

open TauCeti.IntegralLattice (dualCarrier mem_carrierInDual_iff discriminantPairing_mk
  discriminantQuadraticMap_mk)

/-- The dual carrier of the rational model is the preimage of the dual lattice `L^∨` under
`ratModelMap`. -/
@[simp]
theorem mem_ratModel_dualCarrier_iff (hL : IsIntegral L) (x : ℚ ⊗[ℤ] L) :
    x ∈ (ratModel hL).dualCarrier ↔ ratModelMap L x ∈ dual L := by
  rw [dualCarrier, LinearMap.BilinForm.mem_dualSubmodule, mem_dual]
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · have hy' : (1 : ℚ) ⊗ₜ[ℤ] (⟨y, hy⟩ : L) ∈ (ratModel hL).carrier := by
      simpa using hy
    obtain ⟨m, hm⟩ := Submodule.mem_one.mp (h _ hy')
    refine ⟨m, ?_⟩
    have := ratModel_form_cast hL x (1 ⊗ₜ[ℤ] ⟨y, hy⟩)
    rw [← hm] at this
    simpa using this.symm
  · obtain ⟨m, hm⟩ := h _ ((mem_ratModel_carrier_iff hL y).mp hy)
    refine Submodule.mem_one.mpr ⟨m, Rat.cast_injective (α := ℝ) ?_⟩
    rw [ratModel_form_cast, hm]
    simp

/-- Every vector of the dual lattice `L^∨` of an integral full lattice `L` is in the image of
`ratModelMap`: a multiple `d • y` with `d ≠ 0` lies in `L`, since `L^∨ ⧸ L` is finite. -/
theorem exists_ratModelMap_eq_of_mem_dual (hL : IsIntegral L) {y : E} (hy : y ∈ dual L) :
    ∃ x : ℚ ⊗[ℤ] L, ratModelMap L x = y := by
  -- the finiteness of the discriminant group is proved through the covolume
  borelize E
  have := hL.finite_discriminantGroup
  set d := Nat.card (DiscriminantGroup L)
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hdy : d • y ∈ L := by
    have h0 : (Submodule.Quotient.mk (d • (⟨y, hy⟩ : dual L)) : DiscriminantGroup L) = 0 := by
      rw [Submodule.Quotient.mk_smul, card_nsmul_eq_zero']
    simpa using (discriminantGroup_mk_eq_zero_iff _).mp h0
  refine ⟨(d : ℚ)⁻¹ ⊗ₜ[ℤ] ⟨d • y, hdy⟩, ?_⟩
  rw [ratModelMap_tmul, Rat.cast_inv, Rat.cast_natCast, Submodule.coe_mk,
    ← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀ hd]

/-- `ratModelMap`, restricted to the dual carrier of the rational model, as a map to `L^∨`. -/
private noncomputable def ratModelDualCarrierToDual (hL : IsIntegral L) :
    (ratModel hL).dualCarrier →ₗ[ℤ] dual L :=
  (ratModelMap L ∘ₗ (ratModel hL).dualCarrier.subtype).codRestrict (dual L) fun x ↦
    (mem_ratModel_dualCarrier_iff hL x).mp x.2

private theorem bijective_ratModelDualCarrierToDual (hL : IsIntegral L) :
    Function.Bijective (ratModelDualCarrierToDual hL) := by
  refine ⟨fun x y hxy ↦ Subtype.ext <| ratModelMap_injective <| congrArg Subtype.val hxy,
    fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := exists_ratModelMap_eq_of_mem_dual hL y.2
  exact ⟨⟨x, (mem_ratModel_dualCarrier_iff hL x).mpr (hx ▸ y.2)⟩, Subtype.ext hx⟩

/-- The identification of the dual lattice `L^∨` of an integral full lattice `L` with the dual
carrier of its rational model; it is inverse to `ratModelMap`. -/
noncomputable def ratModelDualEquiv (hL : IsIntegral L) :
    dual L ≃ₗ[ℤ] (ratModel hL).dualCarrier :=
  (LinearEquiv.ofBijective _ (bijective_ratModelDualCarrierToDual hL)).symm

/-- `ratModelMap` recovers a dual vector from its image under `ratModelDualEquiv`. -/
@[simp]
theorem ratModelMap_ratModelDualEquiv (hL : IsIntegral L) (x : dual L) :
    ratModelMap L (ratModelDualEquiv hL x) = x :=
  congrArg Subtype.val <|
    (LinearEquiv.ofBijective _ (bijective_ratModelDualCarrierToDual hL)).apply_symm_apply x

/-- The inverse of `ratModelDualEquiv` is `ratModelMap`. -/
@[simp]
theorem coe_ratModelDualEquiv_symm (hL : IsIntegral L) (x : (ratModel hL).dualCarrier) :
    ((ratModelDualEquiv hL).symm x : E) = ratModelMap L x := by
  conv_rhs => rw [← (ratModelDualEquiv hL).apply_symm_apply x]
  rw [ratModelMap_ratModelDualEquiv]

/-- The form of the rational model on the dual carrier is the inner product of `L^∨`. -/
theorem ratModel_form_ratModelDualEquiv_cast (hL : IsIntegral L) (x y : dual L) :
    (((ratModel hL).form (ratModelDualEquiv hL x) (ratModelDualEquiv hL y) : ℚ) : ℝ) =
      ⟪(x : E), (y : E)⟫ := by
  rw [ratModel_form_cast, ratModelMap_ratModelDualEquiv, ratModelMap_ratModelDualEquiv]

/-- `ratModelDualEquiv` carries `L`, seen inside `L^∨`, onto the carrier of the rational model
seen inside its dual carrier. -/
theorem map_ratModelDualEquiv_submoduleOf (hL : IsIntegral L) :
    (L.submoduleOf (dual L)).map (ratModelDualEquiv hL : dual L →ₗ[ℤ] _) =
      (ratModel hL).carrierInDual := by
  ext x
  rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, mem_carrierInDual_iff,
    mem_ratModel_carrier_iff, Submodule.submoduleOf, Submodule.mem_comap]
  simp

/-- The identification of the discriminant group `L^∨ ⧸ L` of an integral full lattice `L` with the
discriminant group of its rational model, induced by `ratModelDualEquiv`. -/
noncomputable def ratModelDiscriminantGroupEquiv (hL : IsIntegral L) :
    DiscriminantGroup L ≃ₗ[ℤ] (ratModel hL).DiscriminantGroup :=
  Submodule.Quotient.equiv _ _ (ratModelDualEquiv hL) (map_ratModelDualEquiv_submoduleOf hL)

/-- On representatives, `ratModelDiscriminantGroupEquiv` is `ratModelDualEquiv`. -/
@[simp]
theorem ratModelDiscriminantGroupEquiv_mk (hL : IsIntegral L) (x : dual L) :
    ratModelDiscriminantGroupEquiv hL (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ratModelDualEquiv hL x) :=
  (rfl)

/-- The discriminant pairing of the rational model, read on the classes of `x, y ∈ L^∨`, is the
inner product `⟪x, y⟫` modulo `ℤ`: it takes the value `q` exactly when `⟪x, y⟫ - q ∈ ℤ`. -/
theorem discriminantPairing_ratModelDiscriminantGroupEquiv_mk_eq_coe_iff (hL : IsIntegral L)
    (x y : dual L) (q : ℚ) :
    (ratModel hL).discriminantPairing (ratModelDiscriminantGroupEquiv hL (Submodule.Quotient.mk x))
        (ratModelDiscriminantGroupEquiv hL (Submodule.Quotient.mk y)) = (q : AddCircle (1 : ℚ)) ↔
      ∃ m : ℤ, ⟪(x : E), (y : E)⟫ = q + m := by
  rw [ratModelDiscriminantGroupEquiv_mk, ratModelDiscriminantGroupEquiv_mk, discriminantPairing_mk,
    ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  refine exists_congr fun m ↦ ?_
  rw [zsmul_one, ← (Rat.cast_injective (α := ℝ)).eq_iff, Rat.cast_sub,
    ratModel_form_ratModelDualEquiv_cast, Rat.cast_intCast]
  constructor <;> intro h <;> linarith

/-- For an even lattice `L`, the discriminant quadratic map of the rational model, read on the
class of `x ∈ L^∨`, is the half-norm `‖x‖² / 2` modulo `ℤ`: it takes the value `q` exactly when
`‖x‖² / 2 - q ∈ ℤ`. -/
theorem discriminantQuadraticMap_ratModelDiscriminantGroupEquiv_mk_eq_coe_iff
    (hL : IsIntegral L) (hE : IsEven L) (x : dual L) (q : ℚ) :
    (ratModel hL).discriminantQuadraticMap ((isEven_ratModel_iff hL).mpr hE)
        (ratModelDiscriminantGroupEquiv hL (Submodule.Quotient.mk x)) = (q : AddCircle (1 : ℚ)) ↔
      ∃ m : ℤ, ‖(x : E)‖ ^ 2 / 2 = q + m := by
  rw [ratModelDiscriminantGroupEquiv_mk, discriminantQuadraticMap_mk, ← sub_eq_zero,
    ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff, ← real_inner_self_eq_norm_sq]
  refine exists_congr fun m ↦ ?_
  rw [zsmul_one, ← (Rat.cast_injective (α := ℝ)).eq_iff, Rat.cast_sub, Rat.cast_div,
    ratModel_form_ratModelDualEquiv_cast, Rat.cast_intCast, Rat.cast_ofNat]
  constructor <;> intro h <;> linarith

end Discriminant

end ZLattice
