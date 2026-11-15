/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.Algebra.Module.ZLattice.RationalModel
public import TauCeti.LinearAlgebra.BilinearForm.BaseChange
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Basic

/-!
# The real model of a positive definite rational lattice

Let `M` be a positive definite integral lattice in a rational vector space `V`. Extending scalars
to `ℝ`, the form of `M` becomes a positive definite symmetric bilinear form on `ℝ ⊗[ℚ] V`, hence
an inner product. The space `ℝ ⊗[ℚ] V` with this inner product is the Euclidean space
`TauCeti.IntegralLattice.RealModelSpace`, and the image `1 ⊗ M` of the carrier is the
*real model* `TauCeti.IntegralLattice.realModel` of `M`: a full integral `ℤ`-lattice in it.

This is the converse of the rational model `ZLattice.ratModel` of an integral lattice in a real
inner product space, and the two constructions are mutually inverse up to isometry:

* the rational model of the real model of `M` is isometric to `M`
  (`TauCeti.IntegralLattice.ratModelRealModelIsometry`);
* the real model of the rational model of an integral full lattice `L ⊆ E` is carried onto `L`
  by a linear isometry equivalence of its real model space with `E`
  (`ZLattice.realModelRatModelIsometry`).

The rational embedding also identifies the dual carrier with the dual real lattice
(`realModelDualEquiv`) and the discriminant groups (`realModelDiscriminantGroupEquiv`). The
latter preserves the discriminant pairing and, for even lattices, the half-norm quadratic map,
read through `ZLattice.ratModelDiscriminantGroupEquiv`. Thus discriminant-form computations on
the rational lattice apply to the real model without introducing another discriminant form.

Moreover a real linear isometry carrying one real model onto another induces an isometry of the
rational lattices (`TauCeti.IntegralLattice.Isometry.ofRealModel`), so that facts proved about
isometry classes of rational lattices, such as non-isometry, transfer to the real models.

## Main definitions

* `TauCeti.IntegralLattice.RealModelSpace M hM`: the real inner product space `ℝ ⊗[ℚ] V`.
* `TauCeti.IntegralLattice.realModelMap M hM`: the rational embedding `V → ℝ ⊗[ℚ] V`.
* `TauCeti.IntegralLattice.realModel M hM`: the real model of `M`, a full lattice.
* `TauCeti.IntegralLattice.realModelCarrierEquiv M hM`: the carrier of `M` is identified with
  its real model.
* `TauCeti.IntegralLattice.ratModelRealModelIsometry M hM`: the isometry from `M` to the rational
  model of its real model.
* `ZLattice.realModelRatModelIsometry hL`: the linear isometry from the real model space of the
  rational model of `L` onto `E`.
* `TauCeti.IntegralLattice.Isometry.ofRealModel`: the isometry of rational lattices induced by an
  isometry of real models.

## Main results

* `TauCeti.IntegralLattice.inner_realModelMap`: the inner product extends the rational form.
* `TauCeti.IntegralLattice.isIntegral_realModel`: the real model is an integral lattice.
* `TauCeti.IntegralLattice.isEven_realModel_iff` and
  `TauCeti.IntegralLattice.isUnimodular_realModel_iff`: the real model is even, resp. unimodular,
  exactly when `M` is.
* `TauCeti.IntegralLattice.RealModelSpace.finrank_eq`: the real model space has the rank of `M`.
* `TauCeti.IntegralLattice.det_realModel`,
  `TauCeti.IntegralLattice.natCard_discriminantGroup_realModel`, and
  `TauCeti.IntegralLattice.IsPosDef.determinant_eq_card_discriminantGroup`: the real model has the
  determinant of `M`, its discriminant group has the order of that of `M`, and
  `M.determinant = |M.DiscriminantGroup|`.
* `ZLattice.map_realModel_realModelRatModelIsometry`: the isometry carries the real model of the
  rational model onto `L`.
* `TauCeti.IntegralLattice.Isometry.realModelMap_ofRealModel_apply`: the induced isometry agrees
  with the real isometry on the rational vectors.
* `TauCeti.IntegralLattice.map_realModel_ne_realModel`: if two positive definite rational lattices
  are not isometric, no real linear isometry carries the real model of one onto that of the other.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct
open scoped RealInnerProductSpace

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The real vector space `ℝ ⊗[ℚ] V` of a positive definite integral lattice `M` in `V`. It
carries the inner product extending the form of `M` (`inner_realModelMap`). -/
@[expose]
def RealModelSpace (M : IntegralLattice V) (_hM : M.IsPosDef) : Type _ := ℝ ⊗[ℚ] V

namespace RealModelSpace

variable {M : IntegralLattice V} {hM : M.IsPosDef}

noncomputable instance : AddCommGroup (M.RealModelSpace hM) :=
  inferInstanceAs (AddCommGroup (ℝ ⊗[ℚ] V))

noncomputable instance : Module ℝ (M.RealModelSpace hM) :=
  inferInstanceAs (Module ℝ (ℝ ⊗[ℚ] V))

noncomputable instance : Module ℚ (M.RealModelSpace hM) :=
  inferInstanceAs (Module ℚ (ℝ ⊗[ℚ] V))

instance : IsScalarTower ℚ ℝ (M.RealModelSpace hM) :=
  inferInstanceAs (IsScalarTower ℚ ℝ (ℝ ⊗[ℚ] V))

/-- The scalar extension to `ℝ` of the form of a positive definite lattice is positive
definite. -/
private theorem posDef_baseChange (hM : M.IsPosDef) :
    (M.form.baseChange ℝ).toQuadraticMap.PosDef :=
  have := M.finiteDimensional
  (M.form.posDef_toQuadraticMap_baseChange_iff (K := ℝ)).mpr hM

/-- The inner product structure on `ℝ ⊗[ℚ] V` given by the scalar extension of the form of a
positive definite lattice. -/
@[instance_reducible]
noncomputable def core (M : IntegralLattice V) (hM : M.IsPosDef) :
    InnerProductSpace.Core ℝ (M.RealModelSpace hM) where
  inner x y := M.form.baseChange ℝ x y
  conj_inner_symm x y :=
    (LinearMap.BilinForm.IsSymm.baseChange ℝ (LinearMap.BilinForm.isSymm_iff.mp M.isSymm)).eq y x
  re_inner_nonneg x := by
    rw [RCLike.re_to_real]
    exact (posDef_baseChange hM).nonneg x
  add_left x y z := LinearMap.map_add₂ _ x y z
  smul_left x y r := LinearMap.map_smul₂ _ r x y
  definite x hx := by
    by_contra hne
    exact (posDef_baseChange hM x hne).ne' hx

noncomputable instance : NormedAddCommGroup (M.RealModelSpace hM) :=
  (core M hM).toNormedAddCommGroup

noncomputable instance : InnerProductSpace ℝ (M.RealModelSpace hM) :=
  InnerProductSpace.ofCore (core M hM).toCore

/-- The inner product of the real model space is the scalar extension of the form. -/
theorem inner_def (x y : M.RealModelSpace hM) : ⟪x, y⟫ = M.form.baseChange ℝ x y := (rfl)

instance : FiniteDimensional ℝ (M.RealModelSpace hM) :=
  have := M.finiteDimensional
  inferInstanceAs (FiniteDimensional ℝ (ℝ ⊗[ℚ] V))

/-- The real model space has the rank of the lattice. -/
@[simp]
theorem finrank_eq : finrank ℝ (M.RealModelSpace hM) = finrank ℤ M :=
  Module.finrank_baseChange.trans M.finrank_carrier.symm

end RealModelSpace

variable (M : IntegralLattice V) (hM : M.IsPosDef)

/-- The rational embedding `x ↦ 1 ⊗ x` of `V` into the real model space. -/
noncomputable def realModelMap : V →ₗ[ℚ] M.RealModelSpace hM :=
  TensorProduct.mk ℚ ℝ V 1

/-- The rational embedding sends `x` to the pure tensor `1 ⊗ x`. -/
theorem realModelMap_apply (x : V) : M.realModelMap hM x = (1 : ℝ) ⊗ₜ[ℚ] x := (rfl)

/-- The inner product of the real model space extends the rational form of `M`. -/
@[simp]
theorem inner_realModelMap (x y : V) :
    ⟪M.realModelMap hM x, M.realModelMap hM y⟫ = (M.form x y : ℝ) := by
  rw [RealModelSpace.inner_def]
  simp [realModelMap_apply, Algebra.smul_def]

/-- The squared norm in the real model is the rational lattice norm, cast to `ℝ`. -/
@[simp]
theorem norm_sq_realModelMap (x : V) :
    ‖M.realModelMap hM x‖ ^ 2 = (M.norm x : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_realModelMap, norm_apply]

/-- The rational embedding into the real model space is injective. -/
theorem realModelMap_injective : Function.Injective (M.realModelMap hM) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff ℚ V x).mp hx

/-- The **real model** of a positive definite integral lattice `M`: the image `1 ⊗ M` of its
carrier in the Euclidean space `ℝ ⊗[ℚ] V`. -/
noncomputable def realModel : Submodule ℤ (M.RealModelSpace hM) :=
  M.carrier.map ((M.realModelMap hM).restrictScalars ℤ)

/-- The vectors of the real model are the images `1 ⊗ x` of the carrier vectors `x`. -/
theorem mem_realModel_iff {y : M.RealModelSpace hM} :
    y ∈ M.realModel hM ↔ ∃ x ∈ M.carrier, M.realModelMap hM x = y :=
  Submodule.mem_map

/-- A rational vector lies in the real model exactly when it lies in the carrier. -/
@[simp]
theorem realModelMap_mem_realModel_iff {x : V} :
    M.realModelMap hM x ∈ M.realModel hM ↔ x ∈ M.carrier := by
  rw [← SetLike.mem_coe, realModel, Submodule.map_coe]
  exact (M.realModelMap_injective hM).mem_set_image

/-- The `ℝ`-basis of the real model space obtained from a `ℤ`-basis of the carrier. -/
private noncomputable def realModelBasis :
    Basis (Free.ChooseBasisIndex ℤ M) ℝ (M.RealModelSpace hM) :=
  M.rationalBasis.baseChange ℝ

private theorem realModelBasis_apply (i : Free.ChooseBasisIndex ℤ M) :
    realModelBasis M hM i = M.realModelMap hM (M.rationalBasis i) :=
  Basis.baseChange_apply ℝ M.rationalBasis i

/-- The real model is spanned over `ℤ` by an `ℝ`-basis of the real model space. -/
private theorem realModel_eq_span :
    M.realModel hM = Submodule.span ℤ (Set.range (realModelBasis M hM)) := by
  have hb : M.carrier =
      Submodule.span ℤ (Set.range (M.carrier.subtype ∘ Free.chooseBasis ℤ M)) := by
    rw [Set.range_comp, ← Submodule.map_span, (Free.chooseBasis ℤ M).span_eq, Submodule.map_top,
      Submodule.range_subtype]
  rw [realModel]
  conv_lhs => rw [hb]
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  ext i
  simp [realModelBasis_apply]

instance : DiscreteTopology (M.realModel hM) := by
  rw [realModel_eq_span]
  infer_instance

instance : IsZLattice ℝ (M.realModel hM) :=
  ⟨by rw [realModel_eq_span]; exact ZSpan.span_top _⟩

/-- The real model of a positive definite integral lattice is integral. -/
theorem isIntegral_realModel : ZLattice.IsIntegral (M.realModel hM) := by
  rw [ZLattice.isIntegral_iff]
  intro x' hx' y' hy'
  obtain ⟨x, hx, rfl⟩ := (M.mem_realModel_iff hM).mp hx'
  obtain ⟨y, hy, rfl⟩ := (M.mem_realModel_iff hM).mp hy'
  refine ⟨M.integralForm ⟨x, hx⟩ ⟨y, hy⟩, ?_⟩
  rw [inner_realModelMap, ← M.integralForm_cast ⟨x, hx⟩ ⟨y, hy⟩, Rat.cast_intCast]

/-- The identification of the carrier of `M` with its real model, `x ↦ 1 ⊗ x`. -/
noncomputable def realModelCarrierEquiv : M ≃ₗ[ℤ] M.realModel hM :=
  M.carrier.equivMapOfInjective ((M.realModelMap hM).restrictScalars ℤ)
    (M.realModelMap_injective hM)

/-- The carrier identification sends `x` to `1 ⊗ x`. -/
@[simp]
theorem coe_realModelCarrierEquiv (x : M) :
    (M.realModelCarrierEquiv hM x : M.RealModelSpace hM) = M.realModelMap hM x := (rfl)

/-- The integer-valued inner product of the real model is the integral form of `M`. -/
@[simp]
theorem integralForm_realModelCarrierEquiv (x y : M) :
    (M.isIntegral_realModel hM).integralForm (M.realModelCarrierEquiv hM x)
      (M.realModelCarrierEquiv hM y) = M.integralForm x y := by
  apply Int.cast_injective (α := ℝ)
  rw [← Rat.cast_intCast (M.integralForm x y), M.integralForm_cast]
  simp [ZLattice.IsIntegral.integralForm_cast]

/-- A positive definite integral lattice `M` is isometric to the rational model of its real
model: the isometry sends a lattice vector `x` to `1 ⊗ (1 ⊗ x)`. -/
noncomputable def ratModelRealModelIsometry :
    Isometry M (ZLattice.ratModel (M.isIntegral_realModel hM)) :=
  .ofCarrierEquiv
    ((M.realModelCarrierEquiv hM).trans (ZLattice.ratModelCarrierEquiv _))
    fun x y ↦ by simp

/-- The isometry from `M` to the rational model of its real model sends a lattice vector to the
unit pure tensor of its image in the real model. -/
theorem ratModelRealModelIsometry_apply_coe (x : M) :
    M.ratModelRealModelIsometry hM x = 1 ⊗ₜ[ℤ] M.realModelCarrierEquiv hM x := by
  simp [ratModelRealModelIsometry]

/-- The real model of `M` is even exactly when `M` is even. -/
theorem isEven_realModel_iff : ZLattice.IsEven (M.realModel hM) ↔ M.IsEven :=
  (ZLattice.isEven_ratModel_iff _).symm.trans (M.ratModelRealModelIsometry hM).isEven_iff.symm

/-- The real model of `M` is unimodular exactly when `M` is unimodular. -/
theorem isUnimodular_realModel_iff : ZLattice.IsUnimodular (M.realModel hM) ↔ M.IsUnimodular := by
  rw [← ZLattice.isUnimodular_ratModel_iff (M.isIntegral_realModel hM),
    isUnimodular_iff_natCard_discriminantGroup_eq_one,
    isUnimodular_iff_natCard_discriminantGroup_eq_one,
    Nat.card_congr (M.ratModelRealModelIsometry hM).discriminantGroupEquiv.toEquiv]

/-! ### Duals and discriminant forms -/

/-- The rational-model embedding after the round-trip isometry is the original rational
embedding into the real model space. -/
@[simp]
theorem ratModelMap_ratModelRealModelIsometry (x : V) :
    ZLattice.ratModelMap (M.realModel hM) (M.ratModelRealModelIsometry hM x) =
      M.realModelMap hM x := by
  let f := (ZLattice.ratModelMap (M.realModel hM)).toAddMonoidHom.toRatLinearMap
  have he : f.comp (M.ratModelRealModelIsometry hM).toLinearEquiv.toLinearMap =
      M.realModelMap hM := by
    refine M.rationalBasis.ext fun i ↦ ?_
    rw [rationalBasis_apply]
    simp [f, AddMonoidHom.coe_toRatLinearMap, ratModelRealModelIsometry_apply_coe]
  exact LinearMap.congr_fun he x

/-- The dual carrier of a positive definite rational lattice identifies with the dual of its
real model, by the rational embedding. -/
noncomputable def realModelDualEquiv :
    M.dualCarrier ≃ₗ[ℤ] ZLattice.dual (M.realModel hM) :=
  (M.ratModelRealModelIsometry hM).dualCarrierEquiv.trans
    (ZLattice.ratModelDualEquiv (M.isIntegral_realModel hM)).symm

/-- The dual identification followed by rationalization is the round-trip isometry on duals. -/
@[simp]
theorem ratModelDualEquiv_realModelDualEquiv (x : M.dualCarrier) :
    ZLattice.ratModelDualEquiv (M.isIntegral_realModel hM) (M.realModelDualEquiv hM x) =
      (M.ratModelRealModelIsometry hM).dualCarrierEquiv x := by
  simp [realModelDualEquiv]

/-- On dual vectors, the dual identification is the rational embedding. -/
@[simp]
theorem coe_realModelDualEquiv (x : M.dualCarrier) :
    (M.realModelDualEquiv hM x : M.RealModelSpace hM) = M.realModelMap hM x := by
  simp [realModelDualEquiv]

/-- The inverse dual identification recovers a real dual vector through the rational embedding. -/
@[simp]
theorem realModelMap_realModelDualEquiv_symm (y : ZLattice.dual (M.realModel hM)) :
    M.realModelMap hM ((M.realModelDualEquiv hM).symm y) = y := by
  rw [← coe_realModelDualEquiv, LinearEquiv.apply_symm_apply]

/-- A rational vector belongs to the dual of the real model exactly when it belongs to the
rational dual carrier. -/
theorem realModelMap_mem_dual_realModel_iff (x : V) :
    M.realModelMap hM x ∈ ZLattice.dual (M.realModel hM) ↔ x ∈ M.dualCarrier := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := (M.realModelDualEquiv hM).surjective ⟨_, hx⟩
    have hxy := congrArg Subtype.val hy
    rw [coe_realModelDualEquiv] at hxy
    exact (M.realModelMap_injective hM hxy) ▸ y.property
  · intro hx
    exact (coe_realModelDualEquiv M hM ⟨x, hx⟩) ▸ (M.realModelDualEquiv hM ⟨x, hx⟩).property

/-- The discriminant group of a positive definite rational lattice identifies with the
(discrete Euclidean) discriminant group of its real model. -/
noncomputable def realModelDiscriminantGroupEquiv :
    M.DiscriminantGroup ≃ₗ[ℤ] ZLattice.DiscriminantGroup (M.realModel hM) :=
  (M.ratModelRealModelIsometry hM).discriminantGroupEquiv.trans
    (ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)).symm

/-- The discriminant identification followed by rationalization is the round-trip isometry. -/
@[simp]
theorem ratModelDiscriminantGroupEquiv_realModelDiscriminantGroupEquiv
    (x : M.DiscriminantGroup) :
    ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)
      (M.realModelDiscriminantGroupEquiv hM x) =
        (M.ratModelRealModelIsometry hM).discriminantGroupEquiv x := by
  simp [realModelDiscriminantGroupEquiv]

/-- The discriminant-group identification sends the class of a rational dual vector to the
class of its real image. -/
@[simp]
theorem realModelDiscriminantGroupEquiv_mk (x : M.dualCarrier) :
    M.realModelDiscriminantGroupEquiv hM (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (M.realModelDualEquiv hM x) := by
  apply (ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)).injective
  simp [realModelDiscriminantGroupEquiv, realModelDualEquiv]

/-- The inverse discriminant identification sends a real dual class to the class of its
rational preimage. -/
@[simp]
theorem realModelDiscriminantGroupEquiv_symm_mk (y : ZLattice.dual (M.realModel hM)) :
    (M.realModelDiscriminantGroupEquiv hM).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((M.realModelDualEquiv hM).symm y) := by
  apply (M.realModelDiscriminantGroupEquiv hM).injective
  simp

/-- The discriminant pairing transported through the real model agrees with the original
rational discriminant pairing. The real-model pairing is read through its rational model,
so no second discriminant form is introduced. -/
@[simp↓]
theorem discriminantPairing_realModelDiscriminantGroupEquiv (x y : M.DiscriminantGroup) :
    (ZLattice.ratModel (M.isIntegral_realModel hM)).discriminantPairing
      (ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)
        (M.realModelDiscriminantGroupEquiv hM x))
      (ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)
        (M.realModelDiscriminantGroupEquiv hM y)) = M.discriminantPairing x y := by
  have : M.IsNondegenerate := ⟨(M.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hM).2⟩
  simpa [Isometry.discriminantBilinearIsometry_apply] using
    (M.ratModelRealModelIsometry hM).discriminantBilinearIsometry.map_pairing x y

/-- For an even lattice, the half-norm discriminant quadratic map transported through the
real model agrees with the original quadratic map. -/
@[simp↓]
theorem discriminantQuadraticMap_realModelDiscriminantGroupEquiv (hE : M.IsEven)
    (x : M.DiscriminantGroup) :
    (ZLattice.ratModel (M.isIntegral_realModel hM)).discriminantQuadraticMap
      ((ZLattice.isEven_ratModel_iff _).mpr ((M.isEven_realModel_iff hM).mpr hE))
      (ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)
        (M.realModelDiscriminantGroupEquiv hM x)) = M.discriminantQuadraticMap hE x := by
  have : M.IsNondegenerate := ⟨(M.isPosDef_iff_isPosSemidef_and_nondegenerate.mp hM).2⟩
  simpa [Isometry.discriminantQuadraticIsometry_apply] using
    ((M.ratModelRealModelIsometry hM).discriminantQuadraticIsometry hE).map_app x

/-- The discriminant group of the real model of `M` has the order of the discriminant group of
`M`. -/
@[simp]
theorem natCard_discriminantGroup_realModel :
    Nat.card (ZLattice.DiscriminantGroup (M.realModel hM)) = Nat.card M.DiscriminantGroup :=
  Nat.card_congr <|
    (ZLattice.ratModelDiscriminantGroupEquiv (M.isIntegral_realModel hM)).toEquiv.trans
      (M.ratModelRealModelIsometry hM).discriminantGroupEquiv.symm.toEquiv

/-- The determinant of the real model of `M`, its squared covolume, is the determinant of `M`. -/
@[simp]
theorem det_realModel [MeasurableSpace (M.RealModelSpace hM)] [BorelSpace (M.RealModelSpace hM)] :
    ZLattice.det (M.realModel hM) = M.determinant := by
  rw [← ZLattice.determinant_ratModel (M.isIntegral_realModel hM),
    (M.ratModelRealModelIsometry hM).determinant_eq]

namespace Isometry

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {M} {hM} {M' : IntegralLattice W}
  {hM' : M'.IsPosDef}

/-- The carrier equivalence induced by a real linear isometry carrying one real model onto
another. -/
private noncomputable def realModelCarrierEquivOfIsometry
    (f : M.RealModelSpace hM ≃ₗᵢ[ℝ] M'.RealModelSpace hM')
    (hf : (M.realModel hM).map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      M'.realModel hM') :
    M ≃ₗ[ℤ] M' :=
  (M.realModelCarrierEquiv hM).trans <|
    ((f.toLinearEquiv.restrictScalars ℤ).ofSubmodules _ _ hf).trans
      (M'.realModelCarrierEquiv hM').symm

private theorem realModelMap_realModelCarrierEquivOfIsometry
    (f : M.RealModelSpace hM ≃ₗᵢ[ℝ] M'.RealModelSpace hM')
    (hf : (M.realModel hM).map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      M'.realModel hM')
    (x : M) :
    M'.realModelMap hM' (realModelCarrierEquivOfIsometry f hf x) = f (M.realModelMap hM x) := by
  simp [← coe_realModelCarrierEquiv, realModelCarrierEquivOfIsometry]

/-- A real linear isometry carrying the real model of `M` onto the real model of `M'` induces an
isometry of the integral lattices `M` and `M'`. -/
noncomputable def ofRealModel (f : M.RealModelSpace hM ≃ₗᵢ[ℝ] M'.RealModelSpace hM')
    (hf : (M.realModel hM).map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      M'.realModel hM') :
    Isometry M M' :=
  .ofCarrierEquiv (realModelCarrierEquivOfIsometry f hf) fun x y ↦ by
    apply Int.cast_injective (α := ℚ)
    apply Rat.cast_injective (α := ℝ)
    simp [← inner_realModelMap (hM := hM'), realModelMap_realModelCarrierEquivOfIsometry]

/-- The isometry induced by a real isometry of real models agrees with it on rational vectors. -/
@[simp]
theorem realModelMap_ofRealModel_apply (f : M.RealModelSpace hM ≃ₗᵢ[ℝ] M'.RealModelSpace hM')
    (hf : (M.realModel hM).map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap =
      M'.realModel hM')
    (x : V) : M'.realModelMap hM' (ofRealModel f hf x) = f (M.realModelMap hM x) := by
  have h : M'.realModelMap hM' ∘ₗ (ofRealModel f hf : V ≃ₗ[ℚ] W).toLinearMap =
      f.toLinearMap.restrictScalars ℚ ∘ₗ M.realModelMap hM := by
    refine M.rationalBasis.ext fun i ↦ ?_
    rw [rationalBasis_apply]
    simpa [ofRealModel] using realModelMap_realModelCarrierEquivOfIsometry f hf _
  exact LinearMap.congr_fun h x

end Isometry

section

variable {W : Type*} [AddCommGroup W] [Module ℚ W] {M} {hM} {N : IntegralLattice W}
  {hN : N.IsPosDef}

/-- **Non-isometric lattices have non-isometric real models**: if the positive definite rational
lattices `M` and `N` are not isometric, no real linear isometry of the ambient spaces carries the
real model of `M` onto that of `N`. -/
theorem map_realModel_ne_realModel (hMN : IsEmpty (M.Isometry N))
    (f : M.RealModelSpace hM ≃ₗᵢ[ℝ] N.RealModelSpace hN) :
    (M.realModel hM).map (f.toLinearEquiv.restrictScalars ℤ).toLinearMap ≠ N.realModel hN :=
  fun hf ↦ hMN.false (Isometry.ofRealModel f hf)

end

/-- The determinant of a positive definite rational integral lattice is the order of its
discriminant group. -/
theorem IsPosDef.determinant_eq_card_discriminantGroup {L : IntegralLattice V} (hL : L.IsPosDef) :
    L.determinant = Nat.card L.DiscriminantGroup := by
  borelize (L.RealModelSpace hL)
  refine Int.cast_injective (α := ℝ) ?_
  rw [← L.det_realModel hL, (L.isIntegral_realModel hL).det_eq_card_discriminantGroup,
    L.natCard_discriminantGroup_realModel hL, Int.cast_natCast]

end TauCeti.IntegralLattice

namespace ZLattice

open TauCeti.IntegralLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

/-- The real-linear map `ℝ ⊗[ℚ] (ℚ ⊗[ℤ] L) → E`, `r ⊗ z ↦ r • ratModelMap L z`. -/
private noncomputable def realModelRatModelLinearMap (L : Submodule ℤ E) :
    ℝ ⊗[ℚ] (ℚ ⊗[ℤ] L) →ₗ[ℝ] E :=
  L.subtype.liftBaseChange ℝ ∘ₗ (AlgebraTensorModule.cancelBaseChange ℤ ℚ ℝ ℝ L).toLinearMap

private theorem realModelRatModelLinearMap_tmul (r : ℝ) (z : ℚ ⊗[ℤ] L) :
    realModelRatModelLinearMap L (r ⊗ₜ[ℚ] z) = r • ratModelMap L z := by
  induction z using TensorProduct.inductionOn with
  | tmul q x =>
    simp [realModelRatModelLinearMap, ratModelMap_tmul, smul_smul, Algebra.smul_def, mul_comm]
  | add z w hz hw => rw [tmul_add, map_add, hz, hw, map_add, smul_add]

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

private theorem inner_realModelRatModelLinearMap (hL : IsIntegral L)
    (x y : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] L)) :
    ⟪realModelRatModelLinearMap L x, realModelRatModelLinearMap L y⟫ =
      (ratModel hL).form.baseChange ℝ x y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, LinearMap.add_apply, inner_add_left, hx, hx']
  | tmul r z =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
    | tmul s w =>
      simp [realModelRatModelLinearMap_tmul, real_inner_smul_left, real_inner_smul_right,
        ← ratModel_form_cast hL, Algebra.smul_def]
      ring

/-- The real model space of the rational model of an integral full lattice `L` is isometric to
`E`, by the real-linear extension `r ⊗ z ↦ r • ratModelMap L z` of `ratModelMap L`. It carries the
real model onto `L` (`map_realModel_realModelRatModelIsometry`). -/
noncomputable def realModelRatModelIsometry (hL : IsIntegral L) :
    (ratModel hL).RealModelSpace (isPosDef_ratModel hL) ≃ₗᵢ[ℝ] E :=
  LinearIsometry.toLinearIsometryEquiv
    (LinearMap.isometryOfInner (realModelRatModelLinearMap L) fun x y ↦
      (inner_realModelRatModelLinearMap hL x y).trans (RealModelSpace.inner_def x y).symm)
    (RealModelSpace.finrank_eq.trans (finrank_ratModel hL))

/-- The isometry `realModelRatModelIsometry hL` sends `r ⊗ z` to `r • ratModelMap L z`. -/
@[simp]
theorem realModelRatModelIsometry_tmul (hL : IsIntegral L) (r : ℝ) (z : ℚ ⊗[ℤ] L) :
    realModelRatModelIsometry hL (r ⊗ₜ[ℚ] z) = r • ratModelMap L z :=
  realModelRatModelLinearMap_tmul r z

/-- The isometry `realModelRatModelIsometry hL` extends `ratModelMap L`. -/
@[simp]
theorem realModelRatModelIsometry_realModelMap (hL : IsIntegral L) (z : ℚ ⊗[ℤ] L) :
    realModelRatModelIsometry hL ((ratModel hL).realModelMap (isPosDef_ratModel hL) z) =
      ratModelMap L z :=
  (realModelRatModelLinearMap_tmul 1 z).trans (one_smul ℝ _)

/-- The isometry `realModelRatModelIsometry hL` carries the real model of the rational model of
`L` onto `L`. -/
theorem map_realModel_realModelRatModelIsometry (hL : IsIntegral L) :
    ((ratModel hL).realModel (isPosDef_ratModel hL)).map
      ((realModelRatModelIsometry hL).toLinearEquiv.restrictScalars ℤ).toLinearMap = L := by
  ext y
  simp only [Submodule.mem_map, mem_realModel_iff]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hy
    refine ⟨_, ⟨_, (ratModelCarrierEquiv hL ⟨y, hy⟩).property, rfl⟩, ?_⟩
    simp

end ZLattice
