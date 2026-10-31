/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar
public import TauCeti.Analysis.Matrix.Exponential.Log
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Topology.Homotopy.Basic

/-!
# Smooth polar deformation of the general linear group

For the polar decomposition `A = P U` over `ℝ` or `ℂ`, the map
`Matrix.GeneralLinearGroup.polarDeformation A t = P ^ (1 - t) U` contracts the positive factor.
It is jointly smooth in time and the invertible matrix, starts at `A`, ends at the native polar
unitary factor, and fixes every unitary matrix throughout. The resulting relative homotopy
`Matrix.GeneralLinearGroup.polarHomotopy` is a strong deformation onto the unitary subgroup
(the orthogonal subgroup over `ℝ`). The deformation is equivariant under unitary multiplication
on both sides and preserves determinant one.

Smoothness is for the native manifold structure on units of the matrix algebra, using the
Euclidean operator norm, which induces the usual matrix topology. It follows from the smooth
positive-definite logarithm in `TauCeti.Analysis.Matrix.Exponential.Log` and the identity
`P ^ s = exp (s • log P)`. The factorization and equivariance use `Units.polarUnitary` and the
uniqueness API in `TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Polar`.

## References

* Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition, Graduate Texts
  in Mathematics 222, Springer, 2015, Section 2.5.
-/

public section

noncomputable section

open scoped Manifold ContDiff MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace Matrix.GeneralLinearGroup

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- The positive polar factor is a smooth function of the invertible matrix. -/
theorem contMDiff_sqrt_mul_star {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Matrix n n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) k
      (fun A : GL n 𝕜 ↦ CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜))) := by
  have hstar := (starL' ℝ : Matrix n n 𝕜 ≃L[ℝ] Matrix n n 𝕜).contDiff (n := k)
  refine ((Matrix.contDiffOn_sqrt (n := n) (𝕜 := 𝕜) (k := k)).restrict_scalars ℝ).contMDiffOn
    |>.comp_contMDiff
    (contDiff_mul.comp_contMDiff
      (Units.contMDiff_val.prodMk_space (hstar.comp_contMDiff Units.contMDiff_val))) ?_
  intro A
  exact isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_mul_star A)

/-- The unitary polar factor, viewed as a matrix, is a smooth real map. -/
theorem contMDiff_coe_polarUnitary {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Matrix n n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) k
      (fun A : GL n 𝕜 ↦ (A.polarUnitary : Matrix n n 𝕜)) := by
  have hinv := ((Matrix.contDiffOn_rpow (n := n) (𝕜 := 𝕜) (-1) (k := k)).restrict_scalars
    ℝ).contMDiffOn
    |>.comp_contMDiff contMDiff_sqrt_mul_star (fun A ↦ posDef_sqrt_mul_star A)
  refine (contDiff_mul.comp_contMDiff (hinv.prodMk_space Units.contMDiff_val)).congr fun A ↦ ?_
  rw [Units.coe_polarUnitary,
    CFC.inverse_eq_rpow_neg_one (Units.isStrictlyPositive_sqrt_mul_star A)]
  rfl

/-- The unitary polar factor, included in the general linear group, is smooth. -/
theorem contMDiff_toUnits_polarUnitary {k : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Matrix n n 𝕜) 𝓘(ℝ, Matrix n n 𝕜) k
      (fun A : GL n 𝕜 ↦ Unitary.toUnits A.polarUnitary) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  exact contMDiff_coe_polarUnitary

/-- Contract the positive factor in `A = P U` by `P ^ (1 - t) U`. It is defined for every real
time, and stays invertible even outside the homotopy interval. -/
def polarDeformation (A : GL n 𝕜) (t : ℝ) : GL n 𝕜 :=
  (IsStrictlyPositive.rpow _ (1 - t) (Units.isStrictlyPositive_sqrt_mul_star A)).isUnit.unit *
    Unitary.toUnits A.polarUnitary

/-- The matrix formula for the polar deformation. -/
theorem coe_polarDeformation (A : GL n 𝕜) (t : ℝ) :
    (polarDeformation A t : Matrix n n 𝕜) =
      CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) ^ (1 - t) * A.polarUnitary := by
  simp [polarDeformation]

/-- At time zero the polar deformation is the identity. -/
@[simp]
theorem polarDeformation_zero (A : GL n 𝕜) : polarDeformation A 0 = A := by
  apply Units.ext
  simp only [coe_polarDeformation, sub_zero,
    CFC.rpow_one _ (posDef_sqrt_mul_star A).posSemidef.nonneg,
    Units.sqrt_mul_star_mul_polarUnitary]

/-- At time one the polar deformation reaches the unitary factor. -/
@[simp]
theorem polarDeformation_one (A : GL n 𝕜) :
    polarDeformation A 1 = Unitary.toUnits A.polarUnitary := by
  apply Units.ext
  simp only [coe_polarDeformation, sub_self,
    CFC.rpow_zero _ (posDef_sqrt_mul_star A).posSemidef.nonneg, one_mul]
  rfl

/-- The polar deformation fixes each unitary matrix at every time. -/
@[simp]
theorem polarDeformation_toUnits (t : ℝ) (U : unitaryGroup n 𝕜) :
    polarDeformation (Unitary.toUnits U) t = Unitary.toUnits U := by
  apply Units.ext
  simp [coe_polarDeformation, Unitary.mul_star_self_of_mem U.2]

/-- The positive polar factor of the deformation is the corresponding power of the original
positive polar factor. -/
@[simp]
theorem sqrt_mul_star_polarDeformation (A : GL n 𝕜) (t : ℝ) :
    CFC.sqrt ((polarDeformation A t : Matrix n n 𝕜) *
      star (polarDeformation A t : Matrix n n 𝕜)) =
        CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) ^ (1 - t) :=
  Units.sqrt_mul_star_eq_of_mul_eq _ CFC.rpow_nonneg (coe_polarDeformation A t).symm

/-- The unitary polar factor is unchanged throughout the deformation. -/
@[simp]
theorem polarUnitary_polarDeformation (t : ℝ) (A : GL n 𝕜) :
    (polarDeformation A t).polarUnitary = A.polarUnitary :=
  Units.polarUnitary_eq_of_mul_eq _ CFC.rpow_nonneg (coe_polarDeformation A t).symm

/-- The polar deformation is jointly smooth in time and matrix, including at both endpoints. -/
theorem contMDiff_polarDeformation {k : ℕ∞ω} :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Matrix n n 𝕜)) 𝓘(ℝ, Matrix n n 𝕜) k
      (fun p : ℝ × GL n 𝕜 ↦ polarDeformation p.2 p.1) := by
  have hlog := ((Matrix.contDiffOn_cfc_log (n := n) (𝕜 := 𝕜) (k := k)).restrict_scalars
    ℝ).contMDiffOn
    |>.comp_contMDiff contMDiff_sqrt_mul_star (fun A ↦ posDef_sqrt_mul_star A)
  have hexp : ContDiff ℝ k (NormedSpace.exp : Matrix n n 𝕜 → Matrix n n 𝕜) :=
    contDiff_iff_contDiffAt.2 fun X ↦
      ((NormedSpace.exp_analytic (𝕂 := ℝ) X).contDiffAt).of_le le_top
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  have htime : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Matrix n n 𝕜)) 𝓘(ℝ, ℝ) k
      (fun p : ℝ × GL n 𝕜 ↦ 1 - p.1) := contMDiff_const.sub contMDiff_fst
  have hpow := hexp.comp_contMDiff (htime.smul (hlog.comp contMDiff_snd))
  refine (contDiff_mul.comp_contMDiff
    (hpow.prodMk_space (contMDiff_coe_polarUnitary.comp contMDiff_snd))).congr fun p ↦ ?_
  exact (coe_polarDeformation p.2 p.1).trans
    (congrArg (· * (p.2.polarUnitary : Matrix n n 𝕜))
      ((posDef_sqrt_mul_star p.2).rpow_eq_exp_smul_cfc_log (1 - p.1)))

/-- The polar deformation is equivariant under multiplication by unitary matrices on either
side. In particular it is equivariant under the central sign action. -/
theorem polarDeformation_unitary_mul_mul_unitary (t : ℝ) (A : GL n 𝕜)
    (U V : unitaryGroup n 𝕜) :
    polarDeformation (Unitary.toUnits U * A * Unitary.toUnits V) t =
      Unitary.toUnits U * polarDeformation A t * Unitary.toUnits V := by
  apply Units.ext
  rw [coe_polarDeformation, Units.sqrt_unitary_mul_mul_unitary,
    CFC.rpow_unitary_mul_mul_star, Units.polarUnitary_unitary_mul_mul_unitary]
  simp only [Units.val_mul, Unitary.val_toUnits_apply, coe_polarDeformation, Submonoid.coe_mul]
  calc
    _ = U * CFC.sqrt ((A : Matrix n n 𝕜) * star (A : Matrix n n 𝕜)) ^ (1 - t) *
        (star (U : Matrix n n 𝕜) * U) * A.polarUnitary * V := by noncomm_ring
    _ = _ := by rw [Unitary.star_mul_self_of_mem U.2, mul_one]; simp only [mul_assoc]

/-- The polar deformation preserves the determinant-one locus for every real time. -/
theorem det_polarDeformation_of_det_eq_one {A : GL n 𝕜}
    (hA : (A : Matrix n n 𝕜).det = 1) (t : ℝ) :
    (polarDeformation A t : Matrix n n 𝕜).det = 1 := by
  rw [coe_polarDeformation, det_mul, det_rpow_sqrt_mul_star_of_det_eq_one A hA,
    det_polarUnitary_of_det_eq_one A hA, mul_one]

variable (n 𝕜) in
/-- The polar homotopy from the identity to the unitary retraction, relative to the unitary
subgroup. Its real-time extension `polarDeformation` is jointly smooth. -/
def polarHomotopy :
    ContinuousMap.HomotopyRel (ContinuousMap.id (GL n 𝕜))
      ⟨fun A ↦ Unitary.toUnits A.polarUnitary,
        (contMDiff_toUnits_polarUnitary (k := ∞)).continuous⟩
      (Set.range (Unitary.toUnits : unitaryGroup n 𝕜 → GL n 𝕜)) where
  toFun := fun p : unitInterval × GL n 𝕜 ↦ polarDeformation p.2 (p.1 : ℝ)
  continuous_toFun := by
    have h : Continuous (fun p : ℝ × GL n 𝕜 ↦ polarDeformation p.2 p.1) :=
      (contMDiff_polarDeformation (k := ∞)).continuous
    have hinc : Continuous (fun p : unitInterval × GL n 𝕜 ↦ ((p.1 : ℝ), p.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    simpa only [Function.comp_def] using h.comp hinc
  map_zero_left := polarDeformation_zero
  map_one_left := polarDeformation_one
  prop' := by
    rintro t _ ⟨U, rfl⟩
    exact polarDeformation_toUnits t U

/-- The relative homotopy evaluates to the polar deformation. -/
@[simp]
theorem polarHomotopy_apply (t : unitInterval) (A : GL n 𝕜) :
    polarHomotopy n 𝕜 (t, A) = polarDeformation A t :=
  (rfl)

end Matrix.GeneralLinearGroup
