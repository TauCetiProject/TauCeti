/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Jacobian
public import TauCeti.LinearAlgebra.Matrix.Cholesky.Equiv
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The Cholesky change of variables on the symmetric matrices

Every positive-definite symmetric matrix is `L * Lᵀ` for a unique lower-triangular `L` with
positive diagonal, so the on-or-below-diagonal entries of `L` are free coordinates on the
positive-definite cone. This file transports `TauCeti.symmetricLebesgue` through that
parametrization: on the cone it is the pushforward of Lebesgue measure on the region where every
diagonal coordinate is positive, weighted by the Jacobian `2 ^ p * ∏ i, (L i i) ^ (p - i)` of
`L ↦ L * Lᵀ`.

That weight is a product of powers of the diagonal coordinates alone, so the resulting coordinate
integral splits into independent one-dimensional integrals. This is how the cone integral
defining the multivariate Gamma function, and with it the Wishart normalizing constant, is
evaluated.

The symmetric matrices carry the on-or-above-diagonal coordinates `TauCeti.symmetricCoordinates`,
whereas the Cholesky Jacobian is computed in the on-or-below-diagonal coordinates. Transposing
positions relabels one coordinate system into the other, and the resulting chart
`TauCeti.symmetricLowerCoordinates` carries the same Lebesgue normalization.

## Main declarations

* `TauCeti.symmetricLowerCoordinates` — the on-or-below-diagonal chart on the symmetric matrices.
* `TauCeti.lowerTriangleGram` — the symmetric matrix `L * Lᵀ` built from coordinates for `L`.
* `TauCeti.posDiagLowerRegion` — the coordinate region cut out by a positive diagonal.
* `TauCeti.choleskyJacobianDensity` — the Jacobian weight of the change of variables.
* `TauCeti.map_cholesky_symmetricLebesgue` — the change of variables.
* `TauCeti.setLIntegral_posDef_symmetricLebesgue` and
  `TauCeti.setIntegral_posDef_symmetricLebesgue` — its integral forms.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, Theorem 2.1.9.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal Matrix

namespace TauCeti

variable (p : ℕ)

/-! ### The on-or-below-diagonal chart -/

/-- Transposing a position matches the on-or-below-diagonal positions of a `p × p` matrix with
the on-or-above-diagonal ones. -/
def lowerTriangleEquivUpperTriangle : lowerTriangle p ≃ upperTriangle p where
  toFun ij := ⟨ij.1.swap, ij.2⟩
  invFun ij := ⟨ij.1.swap, ij.2⟩
  left_inv _ := (rfl)
  right_inv _ := (rfl)

@[simp]
theorem lowerTriangleEquivUpperTriangle_apply_coe (ij : lowerTriangle p) :
    (lowerTriangleEquivUpperTriangle p ij : Fin p × Fin p) = ij.1.swap :=
  (rfl)

/-- The continuous linear equivalence reading off the on-or-below-diagonal entries of a symmetric
matrix. It is `TauCeti.symmetricCoordinates` relabelled by transposing positions, so the Lebesgue
measure it induces is again `TauCeti.symmetricLebesgue`. -/
def symmetricLowerCoordinates :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ≃L[ℝ] (lowerTriangle p → ℝ) :=
  (symmetricCoordinates p).trans
    (LinearEquiv.toContinuousLinearEquiv
      (LinearEquiv.funCongrLeft ℝ ℝ (lowerTriangleEquivUpperTriangle p)))

@[simp]
theorem symmetricLowerCoordinates_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (ij : lowerTriangle p) :
    symmetricLowerCoordinates p A ij = (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 := by
  simp only [symmetricLowerCoordinates, ContinuousLinearEquiv.trans_apply,
    LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.funCongrLeft_apply,
    LinearMap.funLeft_apply, symmetricCoordinates_apply,
    lowerTriangleEquivUpperTriangle_apply_coe, Prod.fst_swap, Prod.snd_swap]
  exact selfAdjoint.coe_apply_comm A ij.1.2 ij.1.1

@[simp]
theorem coe_symmetricLowerCoordinates_symm_apply_of_ge (x : lowerTriangle p → ℝ) {i j : Fin p}
    (h : j ≤ i) :
    ((symmetricLowerCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(i, j), h⟩ := by
  have hx := symmetricLowerCoordinates_apply p ((symmetricLowerCoordinates p).symm x) ⟨(i, j), h⟩
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  exact hx.symm

@[simp]
theorem coe_symmetricLowerCoordinates_symm_apply_of_le (x : lowerTriangle p → ℝ) {i j : Fin p}
    (h : i ≤ j) :
    ((symmetricLowerCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(j, i), h⟩ := by
  rw [selfAdjoint.coe_apply_comm, coe_symmetricLowerCoordinates_symm_apply_of_ge p x h]

/-- The measurable equivalence induced by `TauCeti.symmetricLowerCoordinates`. -/
def symmetricLowerCoordinatesMeasurableEquiv :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ≃ᵐ (lowerTriangle p → ℝ) :=
  (symmetricLowerCoordinates p).toHomeomorph.toMeasurableEquiv

@[simp]
theorem symmetricLowerCoordinatesMeasurableEquiv_coe :
    (symmetricLowerCoordinatesMeasurableEquiv p : _ → lowerTriangle p → ℝ) =
      symmetricLowerCoordinates p :=
  (rfl)

@[simp]
theorem symmetricLowerCoordinatesMeasurableEquiv_symm_coe :
    ((symmetricLowerCoordinatesMeasurableEquiv p).symm : (lowerTriangle p → ℝ) → _) =
      (symmetricLowerCoordinates p).symm :=
  (rfl)

/-- The on-or-below-diagonal chart carries `TauCeti.symmetricLebesgue` to Lebesgue measure on the
coordinate space: relabelling coordinates by a bijection of index types preserves product
Lebesgue measure. -/
theorem measurePreserving_symmetricLowerCoordinates :
    MeasurePreserving (symmetricLowerCoordinates p) (symmetricLebesgue p) volume := by
  have hrelabel : MeasurePreserving
      (fun y : upperTriangle p → ℝ => fun ij : lowerTriangle p =>
        y (lowerTriangleEquivUpperTriangle p ij)) volume volume := by
    have hfun : (fun y : upperTriangle p → ℝ => fun ij : lowerTriangle p =>
          y (lowerTriangleEquivUpperTriangle p ij)) =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : upperTriangle p => ℝ)
          (lowerTriangleEquivUpperTriangle p)).symm := by
      funext y ij
      exact (Equiv.piCongrLeft_symm_apply (P := fun _ : upperTriangle p => ℝ)
        (e := lowerTriangleEquivUpperTriangle p) y ij).symm
    rw [hfun]
    exact (volume_measurePreserving_piCongrLeft (fun _ : upperTriangle p => ℝ)
      (lowerTriangleEquivUpperTriangle p)).symm _
  exact hrelabel.comp (measurePreserving_symmetricCoordinates p)

/-- The chart reconstruction carries Lebesgue measure on the coordinate space to
`TauCeti.symmetricLebesgue`. -/
theorem measurePreserving_symmetricLowerCoordinates_symm :
    MeasurePreserving (symmetricLowerCoordinates p).symm volume (symmetricLebesgue p) :=
  (measurePreserving_symmetricLowerCoordinates p).symm
    (symmetricLowerCoordinatesMeasurableEquiv p)

/-! ### The Gram map and the positive-diagonal region -/

/-- The symmetric matrix `L * Lᵀ`, where `L` is the lower-triangular matrix whose
on-or-below-diagonal entries are `x`. On the positive-diagonal region this is Cholesky
reconstruction. -/
def lowerTriangleGram (x : lowerTriangle p → ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ, by
    have h := Matrix.isHermitian_mul_conjTranspose_self (lowerTriangleMatrix p x)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact Matrix.isHermitian_iff_isSelfAdjoint.mp h⟩

@[simp]
theorem coe_lowerTriangleGram (x : lowerTriangle p → ℝ) :
    (lowerTriangleGram p x : Matrix (Fin p) (Fin p) ℝ) =
      lowerTriangleMatrix p x * (lowerTriangleMatrix p x)ᵀ :=
  (rfl)

theorem continuous_lowerTriangleGram : Continuous (lowerTriangleGram p) :=
  continuous_induced_rng.2
    (continuous_lowerTriangleMatrix.matrix_mul continuous_lowerTriangleMatrix.matrix_transpose)

@[fun_prop]
theorem measurable_lowerTriangleGram : Measurable (lowerTriangleGram p) :=
  (continuous_lowerTriangleGram p).measurable

/-- Reading the on-or-below-diagonal entries of `L * Lᵀ` is the coordinate form of Cholesky
reconstruction. -/
@[simp]
theorem symmetricLowerCoordinates_lowerTriangleGram (x : lowerTriangle p → ℝ) :
    symmetricLowerCoordinates p (lowerTriangleGram p x) =
      choleskyReconstructionCoordinates p x := by
  funext ij
  rw [symmetricLowerCoordinates_apply, coe_lowerTriangleGram,
    choleskyReconstructionCoordinates_apply]
  simp [Matrix.mul_apply, Matrix.transpose_apply]

/-- The Gram map factors through the chart: it reconstructs a symmetric matrix from the
coordinate form of Cholesky reconstruction. -/
theorem lowerTriangleGram_eq_symm_apply (x : lowerTriangle p → ℝ) :
    lowerTriangleGram p x =
      (symmetricLowerCoordinates p).symm (choleskyReconstructionCoordinates p x) := by
  rw [← symmetricLowerCoordinates_lowerTriangleGram, ContinuousLinearEquiv.symm_apply_apply]

/-- The region of the lower-triangular coordinates with positive diagonal: the set underlying
`TauCeti.PosDiagLowerCoordinates`, and the set of coordinates of Cholesky factors. -/
def posDiagLowerRegion : Set (lowerTriangle p → ℝ) :=
  {x | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩}

/-- The positive-diagonal region spelled out as a set of coordinate vectors, for rewriting an
integral stated in that spelling into the named one. -/
theorem posDiagLowerRegion_def :
    posDiagLowerRegion p = {x : lowerTriangle p → ℝ | ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩} :=
  (rfl)

@[simp]
theorem mem_posDiagLowerRegion {x : lowerTriangle p → ℝ} :
    x ∈ posDiagLowerRegion p ↔ ∀ i : Fin p, 0 < x ⟨(i, i), le_rfl⟩ :=
  Iff.rfl

theorem isOpen_posDiagLowerRegion : IsOpen (posDiagLowerRegion p) := by
  have h : posDiagLowerRegion p =
      ⋂ i : Fin p, (fun x : lowerTriangle p → ℝ => x ⟨(i, i), le_rfl⟩) ⁻¹' Set.Ioi 0 := by
    ext x
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioi.preimage (continuous_apply _)

theorem measurableSet_posDiagLowerRegion : MeasurableSet (posDiagLowerRegion p) :=
  (isOpen_posDiagLowerRegion p).measurableSet

/-- The positive-diagonal lower-triangular matrix whose on-or-below-diagonal entries are the
coordinates `x` of a point of the positive-diagonal region. -/
private def posDiagOfMem {x : lowerTriangle p → ℝ} (hx : x ∈ posDiagLowerRegion p) :
    PosDiagLowerTriangular p :=
  (lowerTriangleCoordinatesHomeomorph p).symm ⟨x, hx⟩

private theorem coe_posDiagOfMem {x : lowerTriangle p → ℝ} (hx : x ∈ posDiagLowerRegion p) :
    (posDiagOfMem p hx).1 = lowerTriangleMatrix p x :=
  lowerTriangleCoordinatesHomeomorph_symm_apply_coe p ⟨x, hx⟩

private theorem coe_choleskyReconstruction_posDiagOfMem {x : lowerTriangle p → ℝ}
    (hx : x ∈ posDiagLowerRegion p) :
    ((choleskyReconstruction (posDiagOfMem p hx)).1 :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) = lowerTriangleGram p x :=
  Subtype.ext <| by
    rw [choleskyReconstruction_coe, coe_lowerTriangleGram, coe_posDiagOfMem]

/-- The Gram map sends the positive-diagonal region onto the positive-definite cone: a
positive-diagonal lower-triangular matrix has positive-definite Gram matrix, and conversely every
positive-definite matrix is the Gram matrix of its Cholesky factor. -/
theorem lowerTriangleGram_image_posDiagLowerRegion :
    lowerTriangleGram p '' posDiagLowerRegion p =
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  ext A
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← coe_choleskyReconstruction_posDiagOfMem p hx]
    exact (choleskyReconstruction (posDiagOfMem p hx)).2
  · intro hA
    refine ⟨fun ij => (cholesky ⟨A, hA⟩).1 ij.1.1 ij.1.2, fun i => (cholesky ⟨A, hA⟩).2.2 i, ?_⟩
    refine Subtype.ext ?_
    rw [coe_lowerTriangleGram, lowerTriangleMatrix_entries (cholesky ⟨A, hA⟩).2.1]
    exact cholesky_mul_transpose ⟨A, hA⟩

/-- Cholesky factors are unique, so the Gram map is injective on the positive-diagonal region. -/
theorem injOn_lowerTriangleGram : Set.InjOn (lowerTriangleGram p) (posDiagLowerRegion p) := by
  intro x hx y hy h
  have hrec : choleskyReconstruction (posDiagOfMem p hx) =
      choleskyReconstruction (posDiagOfMem p hy) :=
    Subtype.ext <| by
      rw [coe_choleskyReconstruction_posDiagOfMem p hx,
        coe_choleskyReconstruction_posDiagOfMem p hy, h]
  have hL : posDiagOfMem p hx = posDiagOfMem p hy :=
    Function.LeftInverse.injective cholesky_choleskyReconstruction hrec
  have hxy : (⟨x, hx⟩ : PosDiagLowerCoordinates p) = ⟨y, hy⟩ := by
    simpa [posDiagOfMem] using congrArg (lowerTriangleCoordinatesHomeomorph p) hL
  exact congrArg Subtype.val hxy

/-- The coordinate form of Cholesky reconstruction is injective on the positive-diagonal region:
it is the Gram map read through a chart. -/
theorem injOn_choleskyReconstructionCoordinates :
    Set.InjOn (choleskyReconstructionCoordinates p) (posDiagLowerRegion p) := by
  intro x hx y hy h
  refine injOn_lowerTriangleGram p hx hy ?_
  rw [lowerTriangleGram_eq_symm_apply, lowerTriangleGram_eq_symm_apply, h]

/-! ### The change of variables -/

/-- The Jacobian weight of the Cholesky change of variables, in lower-triangular coordinates:
`ENNReal.ofReal (2 ^ p * ∏ i, (L i i) ^ (p - i))`. On `TauCeti.posDiagLowerRegion`, where the
diagonal coordinates are positive, this is the absolute determinant of the derivative of
`L ↦ L * Lᵀ`; elsewhere the product can be negative, and the weight then truncates to `0`. The
change of variables below uses the weight only on that region. -/
def choleskyJacobianDensity (x : lowerTriangle p → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1))

theorem choleskyJacobianDensity_def (x : lowerTriangle p → ℝ) :
    choleskyJacobianDensity p x =
      ENNReal.ofReal (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1)) :=
  (rfl)

@[fun_prop]
theorem measurable_choleskyJacobianDensity : Measurable (choleskyJacobianDensity p) :=
  ENNReal.measurable_ofReal.comp <| measurable_const.mul <|
    Finset.measurable_prod _ fun _ _ => (measurable_pi_apply _).pow_const _

/-- **The Cholesky change of variables.** Lebesgue measure on the symmetric matrices, restricted
to the positive-definite cone, is the image of the positive-diagonal coordinate region under
`L ↦ L * Lᵀ`, weighted by the Cholesky Jacobian. -/
theorem map_cholesky_symmetricLebesgue :
    ((volume.restrict (posDiagLowerRegion p)).withDensity
          (choleskyJacobianDensity p)).map (lowerTriangleGram p) =
      (symmetricLebesgue p).restrict
        {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef} := by
  -- On the positive-diagonal region the Jacobian weight is the absolute determinant of the
  -- derivative, which is what Mathlib's change-of-variables formula asks for.
  have hdens : (volume.restrict (posDiagLowerRegion p)).withDensity
        (choleskyJacobianDensity p) =
      (volume.restrict (posDiagLowerRegion p)).withDensity
        fun x => ENNReal.ofReal |(fderivCholeskyReconstructionCoordinates p x).det| := by
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem (measurableSet_posDiagLowerRegion p)] with x hx
    rw [choleskyJacobianDensity_def, ← fderiv_choleskyReconstructionCoordinates,
      abs_det_fderiv_choleskyReconstructionCoordinates x hx]
  have hjac := map_withDensity_abs_det_fderiv_eq_addHaar
    (μ := (volume : Measure (lowerTriangle p → ℝ)))
    (measurableSet_posDiagLowerRegion p).nullMeasurableSet
    (f' := fderivCholeskyReconstructionCoordinates p)
    (fun x _ => (hasFDerivAt_choleskyReconstructionCoordinates x).hasFDerivWithinAt)
    (injOn_choleskyReconstructionCoordinates p)
  -- The chart reconstruction carries Lebesgue measure on the coordinates to `symmetricLebesgue`,
  -- so it is enough to run the change of variables in the coordinates.
  have hmap : (volume : Measure (lowerTriangle p → ℝ)).map
      ⇑(symmetricLowerCoordinatesMeasurableEquiv p).symm = symmetricLebesgue p := by
    rw [symmetricLowerCoordinatesMeasurableEquiv_symm_coe]
    exact (measurePreserving_symmetricLowerCoordinates_symm p).map_eq
  have hcomp : lowerTriangleGram p =
      ⇑(symmetricLowerCoordinatesMeasurableEquiv p).symm ∘
        choleskyReconstructionCoordinates p :=
    funext (lowerTriangleGram_eq_symm_apply p)
  rw [hdens, hcomp, ← Measure.map_map (symmetricLowerCoordinatesMeasurableEquiv p).symm.measurable
      (differentiable_choleskyReconstructionCoordinates (p := p)).continuous.measurable,
    hjac, ← hmap,
    (symmetricLowerCoordinatesMeasurableEquiv p).symm.measurableEmbedding.restrict_map]
  congr 1
  rw [← lowerTriangleGram_image_posDiagLowerRegion p, hcomp, Set.image_comp,
    Set.preimage_image_eq _ (symmetricLowerCoordinatesMeasurableEquiv p).symm.injective]

/-- On the positive-diagonal region the Jacobian weight is nonnegative, so it agrees with the
real number `2 ^ p * ∏ i, (L i i) ^ (p - i)` it truncates. -/
@[simp]
theorem toReal_choleskyJacobianDensity {x : lowerTriangle p → ℝ}
    (hx : x ∈ posDiagLowerRegion p) :
    (choleskyJacobianDensity p x).toReal =
      2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1) :=
  ENNReal.toReal_ofReal <| mul_nonneg (by positivity) <|
    Finset.prod_nonneg fun i _ => pow_nonneg (hx i).le _

/-- The integral form of the Cholesky change of variables: an integral over the positive-definite
cone becomes a weighted integral over the positive-diagonal coordinate region. -/
theorem setLIntegral_posDef_symmetricLebesgue
    {f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}, f A ∂symmetricLebesgue p =
      ∫⁻ x in posDiagLowerRegion p,
        choleskyJacobianDensity p x * f (lowerTriangleGram p x) := by
  have hg : Measurable fun x => f (lowerTriangleGram p x) :=
    hf.comp (measurable_lowerTriangleGram p)
  rw [← map_cholesky_symmetricLebesgue, lintegral_map hf (measurable_lowerTriangleGram p),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_choleskyJacobianDensity p) hg]
  rfl

/-- The Bochner-integral form of the Cholesky change of variables: an integral over the
positive-definite cone becomes a Jacobian-weighted integral over the positive-diagonal
coordinate region. -/
theorem setIntegral_posDef_symmetricLebesgue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) → E}
    (hf : AEStronglyMeasurable f ((symmetricLebesgue p).restrict
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef})) :
    ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).PosDef}, f A ∂symmetricLebesgue p =
      ∫ x in posDiagLowerRegion p,
        (2 ^ p * ∏ i : Fin p, x ⟨(i, i), le_rfl⟩ ^ (p - i.1)) • f (lowerTriangleGram p x) := by
  have hmap := map_cholesky_symmetricLebesgue p
  calc ∫ A in {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
          (A : Matrix (Fin p) (Fin p) ℝ).PosDef}, f A ∂symmetricLebesgue p
      = ∫ A, f A ∂(((volume.restrict (posDiagLowerRegion p)).withDensity
          (choleskyJacobianDensity p)).map (lowerTriangleGram p)) := by rw [hmap]
    _ = ∫ x, f (lowerTriangleGram p x) ∂((volume.restrict (posDiagLowerRegion p)).withDensity
          (choleskyJacobianDensity p)) :=
        integral_map (measurable_lowerTriangleGram p).aemeasurable (hmap ▸ hf)
    _ = ∫ x in posDiagLowerRegion p,
          (choleskyJacobianDensity p x).toReal • f (lowerTriangleGram p x) :=
        integral_withDensity_eq_integral_toReal_smul (measurable_choleskyJacobianDensity p)
          (.of_forall fun _ => ENNReal.ofReal_lt_top) _
    _ = _ :=
        setIntegral_congr_fun (measurableSet_posDiagLowerRegion p) fun x hx => by
          rw [toReal_choleskyJacobianDensity p hx]

end TauCeti
