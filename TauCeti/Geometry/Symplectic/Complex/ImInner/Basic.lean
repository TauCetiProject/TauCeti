/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace
public import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
public import TauCeti.Geometry.Symplectic.Lagrangian.CompatibleMetric
public import TauCeti.Geometry.Symplectic.Lagrangian.Constructions

/-!
# The symplectic form `Im ⟪·, ·⟫` of a complex inner product space

A complex inner product space `E` is a real symplectic vector space for the form

`ω(v, w) = Im ⟪v, w⟫_ℂ` (`TauCeti.imInnerSymplecticForm`),

the form `⟪i v, w⟫_ℝ` of the orthogonal complex structure given by multiplication by `i`. It is
compatible with multiplication by `i`, and its compatible metric `ω(·, i ·)` is the real inner
product `Re ⟪·, ·⟫_ℂ`. A real subspace is Lagrangian exactly when `Im ⟪·, ·⟫_ℂ` vanishes on it and
its real dimension is half that of `E`, and exactly when its real orthogonal complement is its image
under multiplication by `i`.

On standard complex coordinate space `ℂⁿ = EuclideanSpace ℂ ι` this is the standard symplectic form
`ω₀ = Σ_j dx_j ∧ dy_j` in the coordinates `z_j = x_j + i y_j`. The real-linear identification

`(x, y) ↦ x + i y`,

the inverse of the real and imaginary parts `TauCeti.complexEuclideanEquivRealProd`, of the doubled
real space `ℝⁿ × ℝⁿ` with `ℂⁿ` carries the standard symplectic form `TauCeti.stdSymplecticForm` to
`Im ⟪·, ·⟫_ℂ`, the product complex structure `J₀(x, y) = (-y, x)` to multiplication by `i`, and the
sum of the real inner products of the two factors to `Re ⟪·, ·⟫_ℂ`. Being a continuous linear
equivalence, it is its own differential at every point (`ContinuousLinearEquiv.fderiv`). So a real
subspace of `ℂⁿ` is Lagrangian exactly when its image in `ℝⁿ × ℝⁿ` is Lagrangian for the standard
form. On `ℂⁿ` the form `Im ⟪·, ·⟫_ℂ` also agrees with the coordinate form
`TauCeti.stdComplexPiSymplecticForm` of `ι → ℂ`, and on `ℂ` with the area form
`TauCeti.stdComplexSymplecticForm`.

These are the conventions in which holomorphic discs in `ℂⁿ` with boundary on a Lagrangian
submanifold are studied; the corresponding statements for maps are in
`TauCeti.Geometry.Symplectic.Complex.ImInner.Manifold`.

The statements about Lagrangian subspaces specialise, through `TauCeti.imInnerSymplecticForm_def`,
those for an orthogonal almost complex structure `J` on a real inner product space
(`TauCeti.AlmostComplexStructure.orthogonal_symplecticForm` and
`TauCeti.AlmostComplexStructure.isLagrangian_symplecticForm_iff_orthogonal_eq`).

## Main declarations

* `TauCeti.imInnerSymplecticForm`: the symplectic form `Im ⟪·, ·⟫_ℂ`, with
  `TauCeti.imInnerSymplecticForm_def`,
  `TauCeti.imInnerSymplecticForm_compatible` and
  `TauCeti.imInnerSymplecticForm_associatedBilinForm_apply`.
* `TauCeti.isLagrangian_imInnerSymplecticForm_iff` and
  `TauCeti.isLagrangian_imInnerSymplecticForm_iff_orthogonal_eq`: its Lagrangian subspaces.
* `TauCeti.complexEuclideanEquivRealProd`: the real and imaginary parts `ℂⁿ ≃L[ℝ] ℝⁿ × ℝⁿ`.
* `TauCeti.isSymplectomorphism_complexEuclideanEquivRealProd_symm`,
  `TauCeti.isComplexLinearMap_complexEuclideanEquivRealProd_symm` and
  `TauCeti.real_inner_complexEuclideanEquivRealProd_symm`: `(x, y) ↦ x + i y` carries the standard
  compatible triple of `ℝⁿ × ℝⁿ` to that of `ℂⁿ`.
* `TauCeti.isLagrangian_imInnerSymplecticForm_iff_map`: Lagrangian subspaces of `ℂⁿ` in real
  coordinates.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Sections 2.1–2.3 (the standard structure of `ℂⁿ` and its Lagrangian subspaces).
-/

public section

namespace TauCeti

open Complex Module
open scoped InnerProductSpace

/-! ### The symplectic form of a complex inner product space -/

section InnerProductSpace

/- The real inner product `Re ⟪·, ·⟫_ℂ` of a complex inner product space is not a global instance
in Mathlib; it is used here, and appears in the statements about the compatible metric and the
real orthogonal complement. -/
attribute [local instance] InnerProductSpace.complexToReal

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The **symplectic form `Im ⟪·, ·⟫_ℂ`** of a complex inner product space, regarded as a real
vector space. It is the form `⟪i v, w⟫_ℝ` of multiplication by `i`
(`TauCeti.AlmostComplexStructure.symplecticForm`). -/
noncomputable def imInnerSymplecticForm : SymplecticForm E :=
  (AlmostComplexStructure.ofComplexModule E).symplecticForm
    AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule

/-- The symplectic form `Im ⟪·, ·⟫_ℂ` is the symplectic form of the orthogonal complex structure
given by multiplication by `i`. -/
theorem imInnerSymplecticForm_def :
    imInnerSymplecticForm E = (AlmostComplexStructure.ofComplexModule E).symplecticForm
      AlmostComplexStructure.real_inner_ofComplexModule_ofComplexModule :=
  (rfl)

variable {E}

/-- The symplectic form of a complex inner product space is the imaginary part of the inner
product. -/
@[simp]
theorem imInnerSymplecticForm_apply (v w : E) :
    imInnerSymplecticForm E v w = (⟪v, w⟫_ℂ).im := by
  simp [imInnerSymplecticForm, real_inner_eq_re_inner, inner_smul_left]

/-- The symplectic form `Im ⟪·, ·⟫_ℂ` is the form `⟪i ·, ·⟫_ℝ` of multiplication by `i`. -/
theorem imInnerSymplecticForm_apply_eq_real_inner (v w : E) :
    imInnerSymplecticForm E v w = ⟪Complex.I • v, w⟫_ℝ := by
  simp [imInnerSymplecticForm]

/-- The metric `ω(·, i ·)` associated with `Im ⟪·, ·⟫_ℂ` and multiplication by `i` is the real
inner product `Re ⟪·, ·⟫_ℂ`. -/
theorem imInnerSymplecticForm_associatedBilinForm_apply (v w : E) :
    (imInnerSymplecticForm E).associatedBilinForm (AlmostComplexStructure.ofComplexModule E) v w =
      ⟪v, w⟫_ℝ := by
  simp [real_inner_eq_re_inner, inner_smul_right]

/-- The symplectic form `Im ⟪·, ·⟫_ℂ` is compatible with multiplication by `i`. -/
theorem imInnerSymplecticForm_compatible :
    (imInnerSymplecticForm E).Compatible (AlmostComplexStructure.ofComplexModule E) := by
  refine .of_tames ((SymplecticForm.invariant_iff _ _).2 fun v w ↦ ?_) fun v hv ↦ ?_
  · simp [inner_smul_left, inner_smul_right, ← mul_assoc]
  · have h := (imInnerSymplecticForm_associatedBilinForm_apply v v).symm ▸
      real_inner_self_pos.2 hv
    simpa using h

/-- The symplectic complement of a real subspace `W` for `Im ⟪·, ·⟫_ℂ` is the real orthogonal
complement of `i W`. -/
theorem orthogonal_imInnerSymplecticForm (W : Submodule ℝ E) :
    (imInnerSymplecticForm E).orthogonal W =
      (W.map (AlmostComplexStructure.ofComplexModule E).toLinearMap)ᗮ :=
  AlmostComplexStructure.orthogonal_symplecticForm _ W

/-- A real subspace is isotropic for `Im ⟪·, ·⟫_ℂ` exactly when the imaginary part of the inner
product vanishes on it. -/
theorem isIsotropic_imInnerSymplecticForm_iff {W : Submodule ℝ E} :
    (imInnerSymplecticForm E).IsIsotropic W ↔ ∀ v ∈ W, ∀ w ∈ W, (⟪v, w⟫_ℂ).im = 0 := by
  simp [SymplecticForm.isIsotropic_iff]

/-- **Lagrangian subspaces of a complex inner product space.** In finite dimension, a real subspace
is Lagrangian for `Im ⟪·, ·⟫_ℂ` exactly when the imaginary part of the inner product vanishes on it
and its real dimension is half that of the space. -/
theorem isLagrangian_imInnerSymplecticForm_iff [FiniteDimensional ℂ E] {W : Submodule ℝ E} :
    (imInnerSymplecticForm E).IsLagrangian W ↔
      (∀ v ∈ W, ∀ w ∈ W, (⟪v, w⟫_ℂ).im = 0) ∧ 2 * finrank ℝ W = finrank ℝ E := by
  rw [← isIsotropic_imInnerSymplecticForm_iff]
  exact ⟨fun h ↦ ⟨h.isIsotropic, h.two_mul_finrank⟩,
    fun h ↦ h.1.isLagrangian_of_finrank h.2⟩

/-- In finite dimension, a real subspace `W` is Lagrangian for `Im ⟪·, ·⟫_ℂ` exactly when its real
orthogonal complement is `i W`. -/
theorem isLagrangian_imInnerSymplecticForm_iff_orthogonal_eq [FiniteDimensional ℂ E]
    {W : Submodule ℝ E} :
    (imInnerSymplecticForm E).IsLagrangian W ↔
      Wᗮ = W.map (AlmostComplexStructure.ofComplexModule E).toLinearMap :=
  AlmostComplexStructure.isLagrangian_symplecticForm_iff_orthogonal_eq _

/-- On the complex line, `Im ⟪·, ·⟫_ℂ` is the standard area form. -/
theorem imInnerSymplecticForm_complex : imInnerSymplecticForm ℂ = stdComplexSymplecticForm := by
  apply SymplecticForm.toBilinForm_injective
  ext z w
  simp [Complex.mul_im]
  ring

end InnerProductSpace

/-! ### Real coordinates of complex Euclidean space -/

section EuclideanSpace

variable (ι : Type*) [Fintype ι]

/-- The real and imaginary parts `z ↦ (Re z, Im z)` of complex Euclidean space, as a continuous
real-linear equivalence with the doubled real Euclidean space. Its inverse is the identification
`(x, y) ↦ x + i y`. -/
noncomputable def complexEuclideanEquivRealProd :
    EuclideanSpace ℂ ι ≃L[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ ι :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun z := (WithLp.toLp 2 fun i ↦ (z i).re, WithLp.toLp 2 fun i ↦ (z i).im)
      map_add' z w := by ext <;> simp
      map_smul' c z := by ext <;> simp
      invFun p := WithLp.toLp 2 fun i ↦ (p.1 i : ℂ) + p.2 i * Complex.I
      left_inv z := by ext i; apply Complex.ext <;> simp
      right_inv p := by ext <;> simp }

variable {ι}

/-- The first component of `TauCeti.complexEuclideanEquivRealProd` is the real part. -/
@[simp]
theorem complexEuclideanEquivRealProd_apply_fst (z : EuclideanSpace ℂ ι) (i : ι) :
    (complexEuclideanEquivRealProd ι z).1 i = (z i).re :=
  (rfl)

/-- The second component of `TauCeti.complexEuclideanEquivRealProd` is the imaginary part. -/
@[simp]
theorem complexEuclideanEquivRealProd_apply_snd (z : EuclideanSpace ℂ ι) (i : ι) :
    (complexEuclideanEquivRealProd ι z).2 i = (z i).im :=
  (rfl)

/-- The inverse of `TauCeti.complexEuclideanEquivRealProd` is `(x, y) ↦ x + i y`. -/
@[simp]
theorem complexEuclideanEquivRealProd_symm_apply
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (i : ι) :
    (complexEuclideanEquivRealProd ι).symm p i = p.1 i + p.2 i * Complex.I :=
  (rfl)

/-- **The standard symplectic form of `ℂⁿ`.** The identification `(x, y) ↦ x + i y` carries the
standard symplectic form `⟪x₁, y₂⟫ - ⟪y₁, x₂⟫` of the doubled real space to `Im ⟪·, ·⟫_ℂ`:
`Im ⟪x₁ + i y₁, x₂ + i y₂⟫_ℂ = Σ_j (x₁ⱼ y₂ⱼ - y₁ⱼ x₂ⱼ)`, the form `ω₀ = Σ_j dx_j ∧ dy_j`. -/
theorem isSymplectomorphism_complexEuclideanEquivRealProd_symm :
    SymplecticForm.IsSymplectomorphism stdSymplecticForm
      (imInnerSymplecticForm (EuclideanSpace ℂ ι))
      (complexEuclideanEquivRealProd ι).symm.toLinearEquiv := by
  refine SymplecticForm.isSymplectomorphism_iff.2 fun u w ↦ ?_
  simp only [ContinuousLinearEquiv.coe_toLinearEquiv, imInnerSymplecticForm_apply,
    PiLp.inner_apply, complexEuclideanEquivRealProd_symm_apply, stdSymplecticForm_apply,
    Complex.im_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Complex.mul_im]
  ring

/-- The identification `(x, y) ↦ x + i y` carries the product complex structure
`J₀(x, y) = (-y, x)` of the doubled real space to multiplication by `i`. -/
theorem isComplexLinearMap_complexEuclideanEquivRealProd_symm :
    IsComplexLinearMap (AlmostComplexStructure.product (EuclideanSpace ℝ ι))
      (AlmostComplexStructure.ofComplexModule (EuclideanSpace ℂ ι))
      (complexEuclideanEquivRealProd ι).symm.toLinearEquiv.toLinearMap := by
  refine LinearMap.ext fun p ↦ ?_
  ext i
  apply Complex.ext <;> simp

/-- The identification `(x, y) ↦ x + i y` carries the sum of the real inner products of the two
factors to the real inner product `Re ⟪·, ·⟫_ℂ`. -/
theorem real_inner_complexEuclideanEquivRealProd_symm
    (u w : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :
    ⟪(complexEuclideanEquivRealProd ι).symm u, (complexEuclideanEquivRealProd ι).symm w⟫_ℝ =
      ⟪u.1, w.1⟫_ℝ + ⟪u.2, w.2⟫_ℝ := by
  simp only [PiLp.inner_apply, complexEuclideanEquivRealProd_symm_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Complex.inner, Complex.mul_re]

/-- On `ℂⁿ`, the symplectic form `Im ⟪·, ·⟫_ℂ` agrees with the coordinate form
`TauCeti.stdComplexPiSymplecticForm` of `ι → ℂ`. -/
theorem imInnerSymplecticForm_euclideanSpace_apply (v w : EuclideanSpace ℂ ι) :
    imInnerSymplecticForm (EuclideanSpace ℂ ι) v w =
      stdComplexPiSymplecticForm ι (WithLp.ofLp v) (WithLp.ofLp w) := by
  simp only [imInnerSymplecticForm_apply, PiLp.inner_apply, Complex.im_sum,
    stdComplexPiSymplecticForm_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [Complex.mul_im]
  ring

/-- **Lagrangian subspaces of `ℂⁿ` in real coordinates.** A real subspace of `ℂⁿ` is Lagrangian for
`Im ⟪·, ·⟫_ℂ` exactly when the subspace of `ℝⁿ × ℝⁿ` formed by the real and imaginary parts of its
vectors is Lagrangian for the standard symplectic form. -/
theorem isLagrangian_imInnerSymplecticForm_iff_map {W : Submodule ℝ (EuclideanSpace ℂ ι)} :
    (imInnerSymplecticForm (EuclideanSpace ℂ ι)).IsLagrangian W ↔
      stdSymplecticForm.IsLagrangian
        (W.map (complexEuclideanEquivRealProd ι).toLinearEquiv.toLinearMap) := by
  set e := (complexEuclideanEquivRealProd ι).toLinearEquiv
  have h : stdSymplecticForm.transport e.symm = imInnerSymplecticForm (EuclideanSpace ℂ ι) :=
    SymplecticForm.isSymplectomorphism_iff_transport_eq.1
      isSymplectomorphism_complexEuclideanEquivRealProd_symm
  have hW : (W.map e.toLinearMap).map e.symm.toLinearMap = W := by
    ext x
    simp
  rw [← SymplecticForm.isLagrangian_map_transport_iff (e := e.symm), h, hW]

end EuclideanSpace

end TauCeti
