/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Integral
public import TauCeti.LinearAlgebra.IntegralLattice.Rationalization
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume
public import TauCeti.LinearAlgebra.IntegralLattice.Even
public import TauCeti.Algebra.Module.ZLattice.Determinant

/-!
# The rational model of an integral real lattice

An integral lattice in a real inner product space has an integer-valued inner product.
Rationalizing this form gives `ratModel`, on the ambient space `ℚ ⊗[ℤ] L`, using
`IntegralLattice.ofIntegralForm` rather than a second rational-lattice construction.

The map `ratModelMap` sends `q ⊗ x` to `q • x` in the original real space. For a full
lattice it is injective, identifies the rational form with the real inner product, and carries
the rational model's integral carrier exactly onto `L`. Consequently the rational model is
positive definite, with the same rank, evenness and unimodularity as the original lattice.
Its determinant and discriminant both equal the squared covolume of `L`. These comparisons
allow the arithmetic theory of integral lattices to be used for analytic lattice theta series.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct
open scoped RealInnerProductSpace

namespace TauCeti.ThetaSeries

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {L : Submodule ℤ E}

/-- The integer-valued inner product on an integral real lattice. -/
noncomputable def integralForm (hL : ZLattice.IsIntegral L) : LinearMap.BilinForm ℤ L :=
  (LinearMap.BilinForm.dualSubmoduleToDual (innerₗ E) L).comp
    (Submodule.inclusion (ZLattice.dual_def L ▸ ZLattice.isIntegral_iff_le_dual.mp hL))

/-- The integral form recovers the real inner product after coercion. -/
@[simp]
theorem integralForm_cast (hL : ZLattice.IsIntegral L) (x y : L) :
    (integralForm hL x y : ℝ) = ⟪(x : E), (y : E)⟫ := by
  rw [integralForm, LinearMap.comp_apply,
    LinearMap.BilinForm.dualSubmoduleToDual_apply_apply]
  exact LinearMap.BilinForm.dualSubmodulePairing_spec (innerₗ E)
    (Submodule.inclusion (ZLattice.dual_def L ▸ ZLattice.isIntegral_iff_le_dual.mp hL) x) y

/-- The integer-valued inner product is symmetric. -/
theorem isSymm_integralForm (hL : ZLattice.IsIntegral L) : (integralForm hL).IsSymm := by
  constructor
  intro x y
  apply Int.cast_injective (α := ℝ)
  simp [real_inner_comm]

/-- Rational scalars act through their canonical embedding into the real scalars. -/
noncomputable local instance ratModule : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)

/-- The restricted rational action is compatible with the real scalar action. -/
local instance ratRealIsScalarTower : IsScalarTower ℚ ℝ E :=
  ⟨fun q r x ↦ mul_smul (q : ℝ) r x⟩

/-- The canonical rational-linear map from the scalar extension of a real lattice to its
ambient space. -/
noncomputable def ratModelMap (L : Submodule ℤ E) : ℚ ⊗[ℤ] L →ₗ[ℚ] E :=
  L.subtype.liftBaseChange ℚ

@[simp]
theorem ratModelMap_tmul (q : ℚ) (x : L) :
    ratModelMap L (q ⊗ₜ[ℤ] x) = (q : ℝ) • (x : E) :=
  (IsScalarTower.algebraMap_smul ℝ q (x : E)).symm

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The canonical rational-linear map of a full real lattice is injective. -/
theorem ratModelMap_injective : Function.Injective (ratModelMap L) := by
  let := ZLattice.module_free ℝ L
  let := ZLattice.module_finite ℝ L
  let b := Free.chooseBasis ℤ L
  apply (LinearMap.liftBaseChange_injective_iff L.subtype b).mpr
  have h := (b.ofZLatticeBasis ℝ L).linearIndependent.restrict_scalars' ℚ
  convert h using 1
  funext i
  exact (b.ofZLatticeBasis_apply ℝ L i).symm

/-- The rational lattice obtained from the integer-valued inner product on a full real lattice. -/
noncomputable def ratModel (hL : ZLattice.IsIntegral L) : IntegralLattice (ℚ ⊗[ℤ] L) := by
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  exact IntegralLattice.ofIntegralForm (integralForm hL) (isSymm_integralForm hL)

/-- The rational form is the scalar extension of the integer-valued inner product. -/
@[simp]
theorem ratModel_form (hL : ZLattice.IsIntegral L) :
    (ratModel hL).form = (integralForm hL).baseChange ℚ := by
  exact IntegralLattice.ofIntegralForm_form _ _

/-- The rational form agrees with the real inner product under the canonical embedding. -/
theorem ratModel_form_eq_inner (hL : ZLattice.IsIntegral L) (x y : ℚ ⊗[ℤ] L) :
    ((ratModel hL).form x y : ℝ) = ⟪ratModelMap L x, ratModelMap L y⟫ := by
  rw [ratModel_form]
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, Rat.cast_add, inner_add_left, hx, hz]
  | tmul q x =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, Rat.cast_add, inner_add_right, hy, hz]
    | tmul r y =>
      simp [LinearMap.BilinForm.baseChange_tmul, inner_smul_left, inner_smul_right,
        integralForm_cast, mul_assoc, mul_comm, mul_left_comm]

/-- The original real lattice is canonically equivalent to the integral carrier of its
rational model. -/
noncomputable def ratModelCarrierEquiv (hL : ZLattice.IsIntegral L) : L ≃ₗ[ℤ] ratModel hL := by
  letI := ZLattice.module_free ℝ L
  letI := ZLattice.module_finite ℝ L
  exact IntegralLattice.ofIntegralForm.carrierEquiv _ _

@[simp]
theorem coe_ratModelCarrierEquiv (hL : ZLattice.IsIntegral L) (x : L) :
    (ratModelCarrierEquiv hL x : ℚ ⊗[ℤ] L) = 1 ⊗ₜ[ℤ] x := by
  exact IntegralLattice.ofIntegralForm.coe_carrierEquiv_apply _ _ _

/-- The carrier equivalence preserves the integer-valued forms. -/
@[simp]
theorem integralForm_ratModelCarrierEquiv (hL : ZLattice.IsIntegral L) (x y : L) :
    (ratModel hL).integralForm (ratModelCarrierEquiv hL x) (ratModelCarrierEquiv hL y) =
      integralForm hL x y := by
  exact IntegralLattice.ofIntegralForm.integralForm_carrierEquiv _ _ _ _

/-- Under the rational embedding, the integral carrier is exactly the original lattice. -/
@[simp]
theorem ratModelMap_mem_iff (hL : ZLattice.IsIntegral L) (x : ℚ ⊗[ℤ] L) :
    ratModelMap L x ∈ L ↔ x ∈ (ratModel hL).carrier := by
  constructor
  · intro hx
    have heq : x = 1 ⊗ₜ[ℤ] (⟨ratModelMap L x, hx⟩ : L) :=
      ratModelMap_injective (by simp)
    rw [heq]
    simpa only [coe_ratModelCarrierEquiv] using
      (ratModelCarrierEquiv hL ⟨ratModelMap L x, hx⟩).property
  · intro hx
    obtain ⟨y, hy⟩ := (ratModelCarrierEquiv hL).surjective ⟨x, hx⟩
    have heq := congrArg (fun z : ratModel hL ↦ (z : ℚ ⊗[ℤ] L)) hy
    have heq' : (ratModelCarrierEquiv hL y : ℚ ⊗[ℤ] L) = x := heq
    rw [← heq', coe_ratModelCarrierEquiv, ratModelMap_tmul]
    simp

/-- The rational model of an integral real lattice is positive definite. -/
theorem isPosDef_ratModel (hL : ZLattice.IsIntegral L) : (ratModel hL).IsPosDef := by
  apply (ratModel hL).isPosDef_iff.mpr
  intro x hx
  have hne : ratModelMap L x ≠ 0 := by
    exact fun h ↦ hx (ratModelMap_injective (h.trans (map_zero _).symm))
  have hpos := real_inner_self_pos.mpr hne
  rw [← ratModel_form_eq_inner hL] at hpos
  exact_mod_cast hpos

/-- The rational model is nondegenerate. -/
instance instIsNondegenerateRatModel (hL : ZLattice.IsIntegral L) :
    (ratModel hL).IsNondegenerate :=
  ⟨((ratModel hL).isPosDef_iff_isPosSemidef_and_nondegenerate.mp (isPosDef_ratModel hL)).2⟩

/-- Evenness agrees between the real lattice and its rational model. -/
@[simp]
theorem isEven_ratModel_iff (hL : ZLattice.IsIntegral L) :
    (ratModel hL).IsEven ↔ ZLattice.IsEven L := by
  rw [(ratModel hL).isEven_iff_of_integralForm_equiv (integralForm hL)
    (ratModelCarrierEquiv hL) (fun x ↦ integralForm_ratModelCarrierEquiv hL x x),
    ZLattice.isEven_iff]
  constructor
  · intro h x hx
    obtain ⟨m, hm⟩ := even_iff_exists_two_mul.mp (h ⟨x, hx⟩)
    refine ⟨m, ?_⟩
    simpa only [integralForm_cast, real_inner_self_eq_norm_sq, Int.cast_mul,
      Int.cast_ofNat] using congrArg (Int.cast : ℤ → ℝ) hm
  · intro h x
    obtain ⟨m, hm⟩ := h x x.property
    apply even_iff_exists_two_mul.mpr
    refine ⟨m, Int.cast_injective (α := ℝ) ?_⟩
    simpa [integralForm_cast, real_inner_self_eq_norm_sq] using hm

/-- The rank of the rational model equals the real dimension of the ambient space. -/
@[simp]
theorem finrank_ratModel (hL : ZLattice.IsIntegral L) :
    finrank ℤ (ratModel hL) = finrank ℝ E :=
  (ratModelCarrierEquiv hL).symm.finrank_eq.trans (ZLattice.rank ℝ L)

variable [MeasurableSpace E] [BorelSpace E]

/-- The rational determinant equals the squared covolume of the real lattice. -/
@[simp]
theorem determinant_ratModel (hL : ZLattice.IsIntegral L) :
    ((ratModel hL).determinant : ℝ) = ZLattice.det L := by
  classical
  let := ZLattice.module_free ℝ L
  let := ZLattice.module_finite ℝ L
  let b := Free.chooseBasis ℤ L
  let e := ratModelCarrierEquiv hL
  let φ : ratModel hL →ₗ[ℤ] E := L.subtype.comp e.symm.toLinearMap
  have hφ (x y : ratModel hL) :
      ⟪φ x, φ y⟫ = (ratModel hL).integralForm x y := by
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    simp [φ, e]
  rw [ZLattice.det_eq_det_gram L b]
  simpa [φ] using
    (IntegralLattice.det_gram_comp_eq_determinant hφ (b.map e)).symm

/-- The rational discriminant equals the determinant of the real lattice. -/
@[simp]
theorem discriminant_ratModel (hL : ZLattice.IsIntegral L) :
    ((ratModel hL).discriminant : ℝ) = ZLattice.det L := by
  rw [IntegralLattice.discriminant_def, Nat.cast_natAbs, Int.cast_abs,
    determinant_ratModel, abs_of_pos (ZLattice.det_pos L)]

/-- Unimodularity agrees between the real lattice and its rational model. -/
theorem isUnimodular_ratModel_iff (hL : ZLattice.IsIntegral L) :
    (ratModel hL).IsUnimodular ↔ ZLattice.IsUnimodular L := by
  rw [(ratModel hL).isUnimodular_iff_discriminant_eq_one,
    hL.isUnimodular_iff_det_eq_one, ← discriminant_ratModel hL]
  exact_mod_cast (Iff.rfl : (ratModel hL).discriminant = 1 ↔
    (ratModel hL).discriminant = 1)

end TauCeti.ThetaSeries
