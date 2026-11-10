/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Iwasawa
public import TauCeti.Geometry.Lie.Subgroup.Unitary
public import TauCeti.Geometry.Lie.Subgroup.Diagonal
public import TauCeti.Geometry.Lie.Subgroup.UpperUnitriangular
public import TauCeti.Analysis.Matrix.Normed
public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.Instances.GeneralLinearGroup
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Smooth matrix Iwasawa decomposition

The multiplication map from the unitary, positive real diagonal, and upper-unitriangular
subgroups to `GL n 𝕜` is a real smooth diffeomorphism, for every `RCLike` field `𝕜` and every
natural number `n`, including zero. For `𝕜 = ℝ` the unitary factor is orthogonal, while for
`𝕜 = ℂ` it is unitary. The diagonal factor consists of real matrices in both cases.

The equivalence is exactly `TauCeti.iwasawaHomeomorph`. Its unitary factor is the normalized
Gram–Schmidt frame of the columns. The triangular remainder has positive diagonal entries
equal to the norms of the unnormalized Gram–Schmidt residuals. All smoothness is over `ℝ`;
no holomorphic dependence of the complex unitary factor is asserted.

The factors carry the closed-subgroup smooth structures, modelled on their Lie subalgebras
in the ambient real general linear groups. Their inclusions are smooth embeddings. Matrices
use the operator norm and `Matrix.linftyOpTopologicalSpace`. Select the local instance
`NormedAddCommGroup.toSeminormedAddCommGroup` before that topology instance when using
these native matrix Lie groups.

## Main declarations

* `TauCeti.iwasawaDiffeomorph`: the smooth matrix Iwasawa decomposition.
* `TauCeti.iwasawaDiffeomorph_apply`, `TauCeti.iwasawaDiffeomorph_symm_apply`: its multiplication
  and factorization formulas.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition, Birkhäuser (1996), §VI.4,
  Example, pp.311–312: the Gram–Schmidt construction of the Iwasawa diffeomorphism for
  `SL(m, ℂ)`. Here the same construction is used for `GL n 𝕜` over a `RCLike` field.
-/

public section

open Matrix InnerProductSpace Module Manifold Set Topology
open scoped ComplexOrder ContDiff Manifold Matrix.Norms.Operator

-- Use the normed scalar instance's seminormed parent consistently in native matrix models.
attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup

attribute [local instance] Matrix.linftyOpTopologicalSpace Matrix.linftyOpContinuousStar

noncomputable section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

private def cols (g : GL (Fin n) 𝕜) (j : Fin n) : EuclideanSpace 𝕜 (Fin n) :=
  (WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm ((g : Matrix (Fin n) (Fin n) 𝕜).col j)

private lemma cols_independent (g : GL (Fin n) 𝕜) : LinearIndependent 𝕜 (cols g) := by
  exact (linearIndependent_col_iff_isUnit.mpr g.isUnit).map'
    (WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm.toLinearMap
    (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 𝕜 (Fin n → 𝕜)).symm.injective)

private def frame (g : GL (Fin n) 𝕜) :
    OrthonormalBasis (Fin n) 𝕜 (EuclideanSpace 𝕜 (Fin n)) :=
  gramSchmidtOrthonormalBasis (by simp) (cols g)

private lemma frame_apply (g : GL (Fin n) 𝕜) (j : Fin n) :
    frame g j = gramSchmidtNormed 𝕜 (cols g) j := by
  exact gramSchmidtOrthonormalBasis_apply (by simp)
    ((gramSchmidtNormed_linearIndependent (cols_independent g)).ne_zero j)

private def qMatrix (g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix (frame g)

private lemma qMatrix_unitary (g : GL (Fin n) 𝕜) : qMatrix g ∈ unitaryGroup (Fin n) 𝕜 :=
  (EuclideanSpace.basisFun (Fin n) 𝕜).toMatrix_orthonormalBasis_mem_unitary (frame g)

private def q (g : GL (Fin n) 𝕜) : GL (Fin n) 𝕜 :=
  Unitary.toUnits ⟨qMatrix g, qMatrix_unitary g⟩

private lemma coe_q (g : GL (Fin n) 𝕜) :
    (q g : Matrix (Fin n) (Fin n) 𝕜) = qMatrix g := rfl

private lemma coordinate_columns (g : GL (Fin n) 𝕜) :
    (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix (cols g) =
      (g : Matrix (Fin n) (Fin n) 𝕜) := by
  ext i j
  simp [Basis.toMatrix_apply, cols, Matrix.col_apply]

private lemma coe_remainder (g : GL (Fin n) 𝕜) :
    (((q g)⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) =
      (frame g).toBasis.toMatrix (cols g) := by
  have hmul : qMatrix g * (frame g).toBasis.toMatrix (cols g) =
      (g : Matrix (Fin n) (Fin n) 𝕜) := by
    simpa only [qMatrix, OrthonormalBasis.coe_toBasis, coordinate_columns] using
      (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix_mul_toMatrix
        (frame g).toBasis (cols g)
  rw [Units.val_mul, ← hmul, ← coe_q]
  simp [← Matrix.mul_assoc]

private lemma remainder_triangular (g : GL (Fin n) 𝕜) :
    ((((q g)⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜)).IsUpperTriangular := by
  rw [coe_remainder]
  exact gramSchmidtOrthonormalBasis_inv_isUpperTriangular (by simp) (cols g)

private lemma remainder_diag (g : GL (Fin n) 𝕜) (j : Fin n) :
    (((q g)⁻¹ * g : GL (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜) j j =
      (‖gramSchmidt 𝕜 (cols g) j‖ : 𝕜) := by
  rw [coe_remainder]
  simp only [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, frame_apply, inner_gramSchmidtNormed_eq_norm]

private lemma q_member (g : GL (Fin n) 𝕜) : q g ∈ unitarySubgroup (GL (Fin n) 𝕜) := by
  apply TauCeti.mem_unitarySubgroup_GL_iff_mem_unitaryGroup.mpr
  rw [coe_q]
  exact qMatrix_unitary g

private lemma q_is_iwasawa (g : GL (Fin n) 𝕜) :
    (((TauCeti.iwasawaHomeomorph 𝕜 n).symm g).1 : GL (Fin n) 𝕜) = q g := by
  apply (TauCeti.iwasawaHomeomorph_symm_unitary_eq_iff g (q g) (q_member g)).mpr
  refine ⟨remainder_triangular g, fun j ↦ ?_⟩
  rw [remainder_diag, RCLike.ofReal_pos]
  exact norm_pos_iff.mpr (gramSchmidt_ne_zero j (cols_independent g))

private def coordEquiv :
    (Fin n → EuclideanSpace 𝕜 (Fin n)) ≃L[ℝ] Matrix (Fin n) (Fin n) 𝕜 :=
  LinearEquiv.toContinuousLinearEquiv
    ((EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrixEquiv.restrictScalars ℝ)

private lemma coordEquiv_apply (c : Fin n → EuclideanSpace 𝕜 (Fin n)) :
    coordEquiv c = (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix c := by
  -- Restriction of scalars and conversion to a continuous linear equivalence preserve the map.
  rfl

private lemma cols_eq_coord (g : GL (Fin n) 𝕜) : cols g = (coordEquiv (𝕜 := 𝕜)).symm g := by
  apply (coordEquiv (𝕜 := 𝕜)).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, coordEquiv_apply]
  exact coordinate_columns g

private lemma smooth_cols :
    ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜)
      𝓘(ℝ, Fin n → EuclideanSpace 𝕜 (Fin n)) ∞ (cols : GL (Fin n) 𝕜 → _) :=
  ((coordEquiv (𝕜 := 𝕜)).symm.contDiff.contMDiff.comp
    Units.contMDiff_val).congr fun g ↦ cols_eq_coord g

private lemma qMatrix_eq_coord (g : GL (Fin n) 𝕜) :
    qMatrix g = coordEquiv (gramSchmidtNormed 𝕜 (cols g)) := by
  rw [coordEquiv_apply]
  apply congrArg (EuclideanSpace.basisFun (Fin n) 𝕜).toBasis.toMatrix
  funext j
  exact frame_apply g j

private lemma smooth_qMatrix :
    ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) ∞
      (qMatrix : GL (Fin n) 𝕜 → _) := by
  have hh : ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜)
      𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) ∞
      (fun g : GL (Fin n) 𝕜 ↦ coordEquiv (gramSchmidtNormed 𝕜 (cols g))) := by
    intro g
    have hs : ContDiffAt ℝ ∞
        (fun c : Fin n → EuclideanSpace 𝕜 (Fin n) ↦ gramSchmidtNormed 𝕜 c) (cols g) := by
      apply contDiffAt_pi.mpr
      intro j
      exact ContDiffAt.gramSchmidtNormed
        (fun i ↦ (ContinuousLinearMap.proj i :
          (Fin n → EuclideanSpace 𝕜 (Fin n)) →L[ℝ] EuclideanSpace 𝕜 (Fin n)).contDiff.contDiffAt)
        (cols_independent g) j
    have h := (coordEquiv (𝕜 := 𝕜)).contDiff.contDiffAt.comp (cols g) hs
    exact h.contMDiffAt.comp g (smooth_cols g)
  exact hh.congr fun g ↦ qMatrix_eq_coord g

private lemma smooth_q :
    ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) ∞
      (q : GL (Fin n) 𝕜 → _) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  simpa only [Function.comp_def, coe_q] using smooth_qMatrix (𝕜 := 𝕜) (n := n)

private def diagonalRealCLM : Matrix (Fin n) (Fin n) 𝕜 →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toContinuousLinearMap <|
    (Matrix.diagonalLinearMap (Fin n) ℝ ℝ).comp (LinearMap.pi fun i ↦
      RCLike.reCLM.toLinearMap.comp (Matrix.entryLinearMap ℝ 𝕜 i i))

private lemma diagonalRealCLM_apply (M : Matrix (Fin n) (Fin n) 𝕜) :
    diagonalRealCLM M = diagonal (fun i ↦ RCLike.re (M i i)) := by
  -- The continuous linear map is the composition of the entry maps, real part and diagonal map.
  rfl

private lemma smooth_diagonal :
    ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ) ∞
      (fun g : GL (Fin n) 𝕜 ↦
        (((TauCeti.iwasawaHomeomorph 𝕜 n).symm g).2.1 : GL (Fin n) ℝ)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  have ht := Units.contMDiff_val.comp ((smooth_q (𝕜 := 𝕜) (n := n)).inv.mul contMDiff_id)
  have hd := (diagonalRealCLM (𝕜 := 𝕜) (n := n)).contDiff.contMDiff.comp ht
  refine hd.congr fun g ↦ ?_
  simp only [Function.comp_apply, diagonalRealCLM_apply]
  rw [TauCeti.coe_iwasawaHomeomorph_symm_diagonal, q_is_iwasawa]
  simp only [Pi.mul_apply, id_eq]

private lemma smooth_unitriangular :
    ContMDiff 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜) ∞
      (fun g : GL (Fin n) 𝕜 ↦
        (((TauCeti.iwasawaHomeomorph 𝕜 n).symm g).2.2 : GL (Fin n) 𝕜)) := by
  have h := ((GeneralLinearGroup.contMDiff_map_real (𝕜 := 𝕜) (n := Fin n)).comp
    (smooth_diagonal (𝕜 := 𝕜) (n := n))).inv.mul
    ((smooth_q (𝕜 := 𝕜) (n := n)).inv.mul contMDiff_id)
  refine h.congr fun g ↦ ?_
  rw [TauCeti.coe_iwasawaHomeomorph_symm_unitriangular, q_is_iwasawa]
  simp only [Pi.mul_apply, Function.comp_apply, id_eq]


local notation "KM" => LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
  (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜)) (unitarySubgroup (GL (Fin n) 𝕜)))
local notation "AM" => LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
  (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) ℝ)) (TauCeti.posDiagonalSubgroup (Fin n) ℝ))
local notation "NM" => LieSubalgebra.toSubmodule (TauCeti.Lie.lieSubalgebraOfSubgroup
  (I := 𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜)) (TauCeti.upperUnitriangularGroup (Fin n) 𝕜))

variable (𝕜 n) in
/-- The real smooth multiplication diffeomorphism `K × A × N → GL (Fin n) 𝕜`, where `K` is
unitary, `A` is positive real diagonal, and `N` is upper-unitriangular. Its underlying equivalence
is `iwasawaHomeomorph 𝕜 n`. -/
def iwasawaDiffeomorph :
    Diffeomorph (𝓘(ℝ, KM).prod (𝓘(ℝ, AM).prod 𝓘(ℝ, NM)))
      𝓘(ℝ, Matrix (Fin n) (Fin n) 𝕜)
      (unitarySubgroup (GL (Fin n) 𝕜) × posDiagonalSubgroup (Fin n) ℝ ×
        upperUnitriangularGroup (Fin n) 𝕜) (GL (Fin n) 𝕜) ∞ := by
  refine { toEquiv := (iwasawaHomeomorph 𝕜 n).toEquiv
           contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · have hk := (Lie.matrixUnitaryEmbeddedLieSubgroupData (n := Fin n)
      (𝕜 := 𝕜)).contMDiff_subtypeVal
    have ha := (Lie.posDiagonalEmbeddedLieSubgroupData (n := Fin n)).contMDiff_subtypeVal
    have hu := (Lie.upperUnitriangularEmbeddedLieSubgroupData (n := Fin n)
      (𝕜 := 𝕜)).contMDiff_subtypeVal
    have hf := ((hk.comp contMDiff_fst).mul
      ((GeneralLinearGroup.contMDiff_map_real (𝕜 := 𝕜) (n := Fin n)).comp
        (ha.comp (contMDiff_fst.comp contMDiff_snd)))).mul
      (hu.comp (contMDiff_snd.comp contMDiff_snd))
    exact hf.congr fun p ↦ iwasawaHomeomorph_apply p
  · apply ContMDiff.prodMk
    · have hk := (Lie.matrixUnitaryEmbeddedLieSubgroupData (n := Fin n)
        (𝕜 := 𝕜)).isSmoothEmbedding_subtypeVal
      apply hk.contMDiff_iff_comp.mpr
      exact (smooth_q (𝕜 := 𝕜) (n := n)).congr fun g ↦ q_is_iwasawa g
    · apply ContMDiff.prodMk
      · have ha := (Lie.posDiagonalEmbeddedLieSubgroupData
          (n := Fin n)).isSmoothEmbedding_subtypeVal
        exact ha.contMDiff_iff_comp.mpr smooth_diagonal
      · have hu := (Lie.upperUnitriangularEmbeddedLieSubgroupData (n := Fin n)
          (𝕜 := 𝕜)).isSmoothEmbedding_subtypeVal
        exact hu.contMDiff_iff_comp.mpr smooth_unitriangular

/-- The smooth Iwasawa decomposition multiplies its three factors. -/
@[simp]
theorem iwasawaDiffeomorph_apply
    (p : unitarySubgroup (GL (Fin n) 𝕜) × posDiagonalSubgroup (Fin n) ℝ ×
      upperUnitriangularGroup (Fin n) 𝕜) :
    iwasawaDiffeomorph 𝕜 n p = (p.1 : GL (Fin n) 𝕜) *
      GeneralLinearGroup.map (algebraMap ℝ 𝕜) (p.2.1 : GL (Fin n) ℝ) * (p.2.2 : GL (Fin n) 𝕜) :=
  iwasawaHomeomorph_apply p

/-- The inverse of `iwasawaDiffeomorph` agrees with the inverse of `iwasawaHomeomorph`. -/
@[simp]
theorem iwasawaDiffeomorph_symm_apply (g : GL (Fin n) 𝕜) :
    (iwasawaDiffeomorph 𝕜 n).symm g = (iwasawaHomeomorph 𝕜 n).symm g := by
  simp only [iwasawaDiffeomorph, Diffeomorph.symm]
  -- The underlying equivalence is `(iwasawaHomeomorph 𝕜 n).toEquiv`, so the inverse function
  -- is definitionally the homeomorphism's inverse.
  rfl

end TauCeti
