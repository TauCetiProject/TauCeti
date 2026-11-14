/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.PosUpperTriangular.Basic
public import TauCeti.Geometry.Lie.Subgroup.Differential
public import TauCeti.Geometry.Lie.Subgroup.Units
public import TauCeti.Analysis.Matrix.Exponential.Triangular.Log
public import Mathlib.Topology.Homotopy.Contractible
import TauCeti.Geometry.Lie.Exponential.Smoothness
import TauCeti.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Geometry.Lie.Exponential.OneParameter
import TauCeti.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Convex.Contractible

/-!
# Global exponential coordinates for the positive triangular group

The native Lie exponential of the positive upper-triangular group is a global smooth
diffeomorphism. Its inverse is the recursive matrix logarithm, transported through the
differential of the existing subgroup inclusion. The subgroup retains its original subspace
topology and closed-subgroup smooth structure. The construction works over real and complex
scalars, includes empty matrices, and permits repeated diagonal entries.

The inclusion Lie map has precisely the upper-triangular matrices with real diagonal as its
range. No separate matrix Lie-algebra carrier is introduced.

The inclusion formulas allow arbitrary finite linearly ordered indices; the recursive global
coordinates use `Fin n`.

## Main results

* `posUpperTriangularLieAlgebraMap`, `posUpperTriangularLieAlgebraMap_apply` and
  `posUpperTriangularLieAlgebraMap_injective`: the native inclusion differential in matrices.
* `mem_range_posUpperTriangularLieAlgebraMap_iff`: its exact range.
* `unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_posUpperTriangular_iff`:
  membership in the native model space in unit matrix coordinates.
* `coe_lieExp_posUpperTriangular`: comparison of native and matrix exponentials.
* `posUpperTriangularLog` and `posUpperTriangularLieAlgebraMap_posUpperTriangularLog`:
  the native logarithm and its matrix coordinates.
* `lieExp_posUpperTriangularLog`, `posUpperTriangularLog_lieExp` and
  `posUpperTriangularLog_one`: the global inverse and identity laws.
* `contMDiff_posUpperTriangularLog` and `posUpperTriangularExpDiffeomorph`: smooth global
  exponential coordinates, with characteristic forward and inverse application lemmas.
* `lieExp_posUpperTriangular_injective` and `lieExp_posUpperTriangular_bijective`:
  global injectivity and bijectivity.
* `posUpperTriangularContractibleSpace`: contractibility in the existing subgroup topology.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, first edition (1996), Chapter VI,
  Section 4, Example, pp.311–312, for the positive triangular factor.
* J. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012),
  Section 14.4, Theorem 14.4.8, for the general exponential-diffeomorphism context.
-/

public noncomputable section

open Matrix Manifold NormedSpace
open scoped ContDiff Manifold Matrix.Norms.Operator ComplexOrder

attribute [local instance] NormedAddCommGroup.toSeminormedAddCommGroup
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.normedAlgebraRatOfReal

namespace TauCeti.Lie

section Inclusion

variable (ι : Type*) [Fintype ι] [LinearOrder ι] {𝕜 : Type*} [RCLike 𝕜]

local notation "Mat" => Matrix ι ι 𝕜
local notation "AN" => posUpperTriangularGroup ι 𝕜
local notation "AmbientLie" => LeftInvariantDerivation 𝓘(ℝ, Mat) (GL ι 𝕜)
local notation "Model" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Mat)) AN)
local notation "Alg" => LeftInvariantDerivation 𝓘(ℝ, Model) AN
local notation "dataAN" => posUpperTriangularEmbeddedLieSubgroupData (ι := ι) (𝕜 := 𝕜)
local notation "nativeEquiv" =>
  EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup
    (posUpperTriangularEmbeddedLieSubgroupData (ι := ι) (𝕜 := 𝕜))
local notation "matrixEquiv" => unitsLieAlgebraLieEquiv (R := Mat)

/-- In unit matrix coordinates, the Lie algebra of the positive triangular subgroup consists
exactly of upper-triangular matrices with real diagonal. -/
theorem unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_posUpperTriangular_iff (A : Mat) :
    (matrixEquiv).symm A ∈ lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Mat)) AN ↔
      A.IsUpperTriangular ∧ ∀ i, RCLike.im (A i i) = 0 := by
  rw [unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff
    (isClosed_posUpperTriangularGroup ι 𝕜)]
  constructor
  · intro h
    have hc (t : ℝ) := PosUpperTriangularGroup.mem_iff.mp (h t)
    simp only [expUnit_coe] at hc
    have htri : A ∈ (Matrix.blockTriangularSubalgebra ℝ 𝕜 id).toSubmodule :=
      TauCeti.mem_of_forall_exp_smul_mem (x := A)
        isClosed_setOfPred_blockTriangular (fun t ↦ (hc t).1)
    refine ⟨htri, fun i ↦ ?_⟩
    let f : Mat →L[ℝ] ℝ :=
      (RCLike.imCLM : 𝕜 →L[ℝ] ℝ).comp
        (entryLinearMap ℝ 𝕜 i i).toContinuousLinearMap
    have hf (B : Mat) : f B = RCLike.im (B i i) := by simp [f]
    have hmem := TauCeti.mem_of_forall_exp_smul_mem
      (S := LinearMap.ker f.toLinearMap) (x := A) f.isClosed_ker (fun t ↦ by
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hf]
        exact (RCLike.pos_iff.mp ((hc t).2 i)).2)
    simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hf] using hmem
  · rintro ⟨hA, hreal⟩ t
    apply PosUpperTriangularGroup.mem_iff.mpr
    simp only [expUnit_coe]
    have ht : (t • A).IsUpperTriangular :=
      (blockTriangularSubalgebra ℝ 𝕜 id).smul_mem hA t
    refine ⟨ht.exp, fun i ↦ ht.exp_apply_diag_pos i ?_⟩
    simp only [Matrix.smul_apply, RCLike.smul_im, hreal, mul_zero]

/-- The native inclusion Lie map of the positive triangular group, in matrix coordinates. -/
def posUpperTriangularLieAlgebraMap : Alg →ₗ⁅ℝ⁆ Mat :=
  (matrixEquiv).toLieHom.comp (dataAN).lieMapSubtypeVal

/-- The matrix coordinate map evaluates the native inclusion differential in unit coordinates. -/
theorem posUpperTriangularLieAlgebraMap_apply (X : Alg) :
    posUpperTriangularLieAlgebraMap ι X = unitsLieAlgebraEquiv ((dataAN).lieMapSubtypeVal X) := by
  simp only [posUpperTriangularLieAlgebraMap, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    unitsLieAlgebraLieEquiv_apply]

/-- The inclusion Lie map in matrix coordinates is injective. -/
theorem posUpperTriangularLieAlgebraMap_injective :
    Function.Injective (posUpperTriangularLieAlgebraMap (𝕜 := 𝕜) ι) :=
  (matrixEquiv).injective.comp (dataAN).injective_lieMapSubtypeVal

private theorem matrixMap_nativeEquiv_symm (Y : Model) :
    posUpperTriangularLieAlgebraMap ι ((nativeEquiv).symm Y) = matrixEquiv (Y : AmbientLie) := by
  simp only [posUpperTriangularLieAlgebraMap, LieHom.comp_apply, LieEquiv.coe_toLieHom]
  rw [← (dataAN).lieEquivLieSubalgebraOfSubgroup_apply, LieEquiv.apply_symm_apply]

/-- The range of the native inclusion differential is exactly the upper-triangular matrices
with real diagonal. -/
-- Normalize this range before the general existential membership rule.
@[simp 1100]
theorem mem_range_posUpperTriangularLieAlgebraMap_iff (A : Mat) :
    A ∈ Set.range (posUpperTriangularLieAlgebraMap (𝕜 := 𝕜) ι) ↔
      A.IsUpperTriangular ∧ ∀ i, RCLike.im (A i i) = 0 := by
  constructor
  · rintro ⟨X, rfl⟩
    apply (unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_posUpperTriangular_iff ι _).mp
    rw [posUpperTriangularLieAlgebraMap_apply, ← unitsLieAlgebraLieEquiv_apply,
      LieEquiv.symm_apply_apply]
    exact (dataAN).lieMapSubtypeVal_mem_lieSubalgebraOfSubgroup X
  · intro hA
    let Y : Model := ⟨(matrixEquiv).symm A,
      (unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_posUpperTriangular_iff ι A).mpr hA⟩
    exact ⟨(nativeEquiv).symm Y, (matrixMap_nativeEquiv_symm ι Y).trans
      ((matrixEquiv).apply_symm_apply A)⟩

private theorem matrixMap_mem (X : Alg) :
    (posUpperTriangularLieAlgebraMap ι X).IsUpperTriangular ∧
      ∀ i, RCLike.im (posUpperTriangularLieAlgebraMap ι X i i) = 0 :=
  (mem_range_posUpperTriangularLieAlgebraMap_iff ι _).mp ⟨X, rfl⟩

/-- The native Lie exponential becomes the ordinary matrix exponential under inclusion. -/
@[simp]
theorem coe_lieExp_posUpperTriangular (X : Alg) :
    (((lieExp X : AN) : GL ι 𝕜) : Mat) = exp (posUpperTriangularLieAlgebraMap ι X) := by
  simpa only [posUpperTriangularLieAlgebraMap_apply, one_smul,
    EmbeddedLieSubgroupData.subtypeVal_apply] using (dataAN).coe_lieExp_smul X 1

end Inclusion

section Logarithm

variable (n : ℕ) {𝕜 : Type*} [RCLike 𝕜]

local notation "Mat" => Matrix (Fin n) (Fin n) 𝕜
local notation "AN" => posUpperTriangularGroup (Fin n) 𝕜
local notation "AmbientLie" => LeftInvariantDerivation 𝓘(ℝ, Mat) (GL (Fin n) 𝕜)
local notation "Model" => LieSubalgebra.toSubmodule
  (lieSubalgebraOfSubgroup (I := 𝓘(ℝ, Mat)) AN)
local notation "Alg" => LeftInvariantDerivation 𝓘(ℝ, Model) AN
local notation "dataAN" => posUpperTriangularEmbeddedLieSubgroupData (ι := Fin n) (𝕜 := 𝕜)
local notation "nativeEquiv" =>
  EmbeddedLieSubgroupData.lieEquivLieSubalgebraOfSubgroup
    (posUpperTriangularEmbeddedLieSubgroupData (ι := Fin n) (𝕜 := 𝕜))
local notation "matrixEquiv" => unitsLieAlgebraLieEquiv (R := Mat)

private local instance finiteDimAmbientLie : FiniteDimensional ℝ AmbientLie :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

private local instance finiteDimNativeLie : FiniteDimensional ℝ Alg :=
  finiteDimensional_leftInvariantDerivation BoundarylessManifold.isInteriorPoint

private def posUpperTriangularLogModel (g : AN) : Model :=
  ⟨(matrixEquiv).symm (Matrix.triangularLog n ((g : GL (Fin n) 𝕜) : Mat)),
    (unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_posUpperTriangular_iff (Fin n) _).mpr
      ⟨Matrix.isUpperTriangular_triangularLog n _, Matrix.im_triangularLog_apply_diag n _⟩⟩

private theorem posUpperTriangularLogModel_coe (g : AN) :
    (posUpperTriangularLogModel n g : AmbientLie) =
      (matrixEquiv).symm (Matrix.triangularLog n ((g : GL (Fin n) 𝕜) : Mat)) := rfl

/-- The global logarithm of the positive triangular group, valued in its native Lie algebra. -/
def posUpperTriangularLog (g : AN) : Alg :=
  (nativeEquiv).symm (posUpperTriangularLogModel n g)

/-- The native logarithm has the recursive triangular matrix logarithm as its coordinates. -/
@[simp]
theorem posUpperTriangularLieAlgebraMap_posUpperTriangularLog (g : AN) :
    posUpperTriangularLieAlgebraMap (Fin n) (posUpperTriangularLog n g) =
      Matrix.triangularLog n ((g : GL (Fin n) 𝕜) : Mat) := by
  rw [posUpperTriangularLog, matrixMap_nativeEquiv_symm, posUpperTriangularLogModel_coe]
  exact (matrixEquiv).apply_symm_apply _

/-- The native exponential of the positive triangular group is injective globally. -/
theorem lieExp_posUpperTriangular_injective : Function.Injective (lieExp : Alg → AN) := by
  intro X Y h
  apply posUpperTriangularLieAlgebraMap_injective (Fin n)
  have he : exp (posUpperTriangularLieAlgebraMap (Fin n) X) =
      exp (posUpperTriangularLieAlgebraMap (Fin n) Y) :=
    (coe_lieExp_posUpperTriangular (Fin n) X).symm.trans
      ((congrArg (fun g : AN ↦ ((g : GL (Fin n) 𝕜) : Mat)) h).trans
        (coe_lieExp_posUpperTriangular (Fin n) Y))
  exact (Matrix.bijOn_exp_upperTriangular_realDiagonal n).injOn
    (matrixMap_mem (Fin n) X) (matrixMap_mem (Fin n) Y) he

/-- Exponentiating the native logarithm recovers every positive triangular matrix. -/
@[simp]
theorem lieExp_posUpperTriangularLog (g : AN) : lieExp (posUpperTriangularLog n g) = g := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_lieExp_posUpperTriangular, posUpperTriangularLieAlgebraMap_posUpperTriangularLog]
  have hg := PosUpperTriangularGroup.mem_iff.mp g.property
  exact Matrix.exp_triangularLog hg.1 (fun i ↦ (RCLike.pos_iff.mp (hg.2 i)).2)
    (fun i ↦ (RCLike.pos_iff.mp (hg.2 i)).1)

/-- The native logarithm recovers every native Lie-algebra element from its exponential. -/
@[simp]
theorem posUpperTriangularLog_lieExp (X : Alg) :
    posUpperTriangularLog n (lieExp X) = X :=
  lieExp_posUpperTriangular_injective n (lieExp_posUpperTriangularLog n (lieExp X))

/-- The native logarithm of the identity is zero. -/
@[simp]
theorem posUpperTriangularLog_one : posUpperTriangularLog (𝕜 := 𝕜) n 1 = 0 := by
  simpa only [lieExp_zero] using posUpperTriangularLog_lieExp n (0 : Alg)

private def projectModel : AmbientLie →L[ℝ] Model :=
  ((Model).projectionOnto (Classical.choose (Model).exists_isCompl)
    (Classical.choose_spec (Model).exists_isCompl)).toContinuousLinearMap

private theorem projectModel_apply (Y : Model) : projectModel (𝕜 := 𝕜) n (Y : AmbientLie) = Y := by
  rw [projectModel, LinearMap.coe_toContinuousLinearMap']
  exact Submodule.projectionOnto_apply_left _ Y

private def modelToNative : Model →L[ℝ] Alg :=
  (nativeEquiv).symm.toLinearEquiv.toLinearMap.toContinuousLinearMap

@[simp]
private theorem modelToNative_apply (Y : Model) :
    modelToNative (𝕜 := 𝕜) n Y = (nativeEquiv).symm Y := rfl

private def matrixToAmbient : Mat →L[ℝ] AmbientLie :=
  (matrixEquiv).symm.toLinearEquiv.toLinearMap.toContinuousLinearMap

@[simp]
private theorem matrixToAmbient_apply (A : Mat) :
    matrixToAmbient (𝕜 := 𝕜) n A = (matrixEquiv).symm A := rfl

private def logExtension : Mat → Alg :=
  ((modelToNative (𝕜 := 𝕜) n).comp
    ((projectModel (𝕜 := 𝕜) n).comp (matrixToAmbient (𝕜 := 𝕜) n))) ∘
      Matrix.triangularLog n

private theorem log_eq_extension (g : AN) :
    posUpperTriangularLog n g = logExtension (𝕜 := 𝕜) n ((g : GL (Fin n) 𝕜) : Mat) := by
  simp only [posUpperTriangularLog, logExtension, Function.comp_apply,
    ContinuousLinearMap.comp_apply, matrixToAmbient_apply,
    ← posUpperTriangularLogModel_coe n g, projectModel_apply, modelToNative_apply]

private theorem contDiffAt_logExtension (g : AN) :
    ContDiffAt ℝ ∞ (logExtension (𝕜 := 𝕜) n) ((g : GL (Fin n) 𝕜) : Mat) := by
  have hg := PosUpperTriangularGroup.mem_iff.mp g.property
  have hlog : ContDiffAt ℝ ∞ (Matrix.triangularLog (𝕜 := 𝕜) n)
      ((g : GL (Fin n) 𝕜) : Mat) :=
    Matrix.contDiffAt_triangularLog ∞ (fun i ↦
      ne_of_gt (RCLike.pos_iff.mp (hg.2 i)).1)
  let F : Mat →L[ℝ] Alg := (modelToNative (𝕜 := 𝕜) n).comp
    ((projectModel (𝕜 := 𝕜) n).comp (matrixToAmbient (𝕜 := 𝕜) n))
  exact F.contDiff.contDiffAt.comp _ hlog

/-- The global native logarithm of the positive triangular group is smooth. -/
theorem contMDiff_posUpperTriangularLog :
    ContMDiff 𝓘(ℝ, Model) 𝓘(ℝ, Alg) ∞ (posUpperTriangularLog (𝕜 := 𝕜) n) := by
  have heq : posUpperTriangularLog (𝕜 := 𝕜) n =
      logExtension (𝕜 := 𝕜) n ∘ (fun g : AN ↦ ((g : GL (Fin n) 𝕜) : Mat)) :=
    funext (log_eq_extension n)
  rw [heq]
  intro g
  exact (contDiffAt_logExtension n g).contMDiffAt.comp g
    ((Units.contMDiff_val.comp (dataAN).contMDiff_subtypeVal) g)

/-- The native exponential is a global diffeomorphism onto the positive triangular group. -/
def posUpperTriangularExpDiffeomorph : Diffeomorph 𝓘(ℝ, Alg) 𝓘(ℝ, Model) Alg AN ∞ where
  toEquiv :=
    { toFun := lieExp
      invFun := posUpperTriangularLog n
      left_inv := posUpperTriangularLog_lieExp n
      right_inv := lieExp_posUpperTriangularLog n }
  contMDiff_toFun := contMDiff_lieExp
  contMDiff_invFun := contMDiff_posUpperTriangularLog n

/-- The exponential diffeomorphism is the native Lie exponential. -/
@[simp]
theorem posUpperTriangularExpDiffeomorph_apply (X : Alg) :
    posUpperTriangularExpDiffeomorph (𝕜 := 𝕜) n X = lieExp X := by rfl

/-- The inverse exponential diffeomorphism is the native triangular logarithm. -/
@[simp]
theorem posUpperTriangularExpDiffeomorph_symm_apply (g : AN) :
    (posUpperTriangularExpDiffeomorph (𝕜 := 𝕜) n).symm g = posUpperTriangularLog n g := by rfl

/-- The native Lie exponential of the positive triangular group is globally bijective. -/
theorem lieExp_posUpperTriangular_bijective : Function.Bijective (lieExp : Alg → AN) :=
  (posUpperTriangularExpDiffeomorph (𝕜 := 𝕜) n).toEquiv.bijective

/-- The positive triangular group is contractible in its existing subgroup topology. -/
instance posUpperTriangularContractibleSpace : ContractibleSpace AN :=
  (posUpperTriangularExpDiffeomorph (𝕜 := 𝕜) n).toHomeomorph.symm.contractibleSpace

end Logarithm

end TauCeti.Lie
