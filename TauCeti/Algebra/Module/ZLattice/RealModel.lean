/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
* `ZLattice.map_realModel_realModelRatModelIsometry`: the isometry carries the real model of the
  rational model onto `L`.
* `TauCeti.IntegralLattice.Isometry.realModelMap_ofRealModel_apply`: the induced isometry agrees
  with the real isometry on the rational vectors.

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
