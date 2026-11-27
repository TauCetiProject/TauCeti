/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Regular.Euclidean
public import TauCeti.Geometry.Manifold.Instances.Unitary
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Geometry.Manifold.ContMDiff.FiniteDimension
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality

/-!
# Orthogonal action on a negative Clifford algebra

The orthogonal group acts by algebra automorphisms extending its action on generators.
This action preserves the scalar-part metric. Smoothness follows by induction on Clifford elements,
using the generator formula and continuous bilinearity of Clifford multiplication.
-/

public noncomputable section

open TauCeti
open scoped Manifold ContDiff CliffordAlgebra.NegativeMetric

namespace Unitary

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

local notation "C" => CliffordAlgebra (negNormSqForm V)

section Algebra

variable [CompleteSpace V]

/-- The Clifford algebra automorphism extending an orthogonal transformation. -/
def cliffordAlgEquiv (g : unitary (V →L[ℝ] V)) : C ≃ₐ[ℝ] C :=
  CliffordAlgebra.equivOfIsometry (linearIsometryEquiv g).negNormSqFormIsometryEquiv

/-- The orthogonal automorphism is induced by the corresponding quadratic isometry. -/
theorem cliffordAlgEquiv_def (g : unitary (V →L[ℝ] V)) :
    cliffordAlgEquiv g =
      CliffordAlgebra.equivOfIsometry (linearIsometryEquiv g).negNormSqFormIsometryEquiv := (rfl)

@[simp]
theorem cliffordAlgEquiv_ι (g : unitary (V →L[ℝ] V)) (v : V) :
    cliffordAlgEquiv g (CliffordAlgebra.ι (negNormSqForm V) v) =
      CliffordAlgebra.ι (negNormSqForm V) (g • v) := by
  have hv : linearIsometryEquiv g v = g • v :=
    congrArg (fun f : V →L[ℝ] V ↦ f v) (coe_linearIsometryEquiv_apply g)
  simp only [cliffordAlgEquiv_def, CliffordAlgebra.equivOfIsometry_ι,
    LinearIsometryEquiv.negNormSqFormIsometryEquiv_apply, hv]

private theorem cliffordAlgEquiv_one : cliffordAlgEquiv (1 : unitary (V →L[ℝ] V)) =
    AlgEquiv.refl := by
  simp [cliffordAlgEquiv_def, LinearIsometryEquiv.one_def]

private theorem cliffordAlgEquiv_mul (g h : unitary (V →L[ℝ] V)) :
    cliffordAlgEquiv (g * h) = (cliffordAlgEquiv h).trans (cliffordAlgEquiv g) := by
  simp [cliffordAlgEquiv_def, LinearIsometryEquiv.mul_def]

/-- The orthogonal group acts by semiring automorphisms extending its action on generators. -/
instance instMulSemiringActionCliffordAlgebra : MulSemiringAction (unitary (V →L[ℝ] V)) C where
  smul g x := cliffordAlgEquiv g x
  smul_zero g := map_zero (cliffordAlgEquiv g)
  smul_add g := map_add (cliffordAlgEquiv g)
  smul_one g := map_one (cliffordAlgEquiv g)
  smul_mul g := map_mul (cliffordAlgEquiv g)
  one_smul x := by exact DFunLike.congr_fun cliffordAlgEquiv_one x
  mul_smul g h x := by exact DFunLike.congr_fun (cliffordAlgEquiv_mul g h) x

/-- A Clifford algebra action by orthogonal transformations commutes with real scalars. -/
instance instSMulCommClassCliffordAlgebra : SMulCommClass (unitary (V →L[ℝ] V)) ℝ C where
  smul_comm g r x := (cliffordAlgEquiv g).toLinearMap.map_smul r x

/-- The action on Clifford elements is the induced algebra automorphism. -/
theorem smul_clifford_eq (g : unitary (V →L[ℝ] V)) (x : C) :
    g • x = cliffordAlgEquiv g x := (rfl)

end Algebra

variable [FiniteDimensional ℝ V]

/-- The orthogonal action preserves the Euclidean Clifford norm. -/
instance instIsIsometricSMulCliffordAlgebra : IsIsometricSMul (unitary (V →L[ℝ] V)) C where
  isometry_smul g := AddMonoidHomClass.isometry_of_norm (cliffordAlgEquiv g) fun x ↦ by
    simp only [CliffordAlgebra.NegativeMetric.norm_eq_regularNorm]
    exact CliffordAlgebra.regularNorm_equivOfIsometry (negNormSqForm V)
      (linearIsometryEquiv g).negNormSqFormIsometryEquiv x

private theorem contMDiff_cliffordAlgEquiv_apply (x : C) :
    ContMDiff (model (V →L[ℝ] V)) 𝓘(ℝ, C) ∞ (fun g ↦ cliffordAlgEquiv g x) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => simpa only [AlgEquiv.commutes] using contMDiff_const
  | ι v =>
    simp only [cliffordAlgEquiv_ι]
    exact (CliffordAlgebra.ι (negNormSqForm V)).toContinuousLinearMap.contMDiff.comp
      ((contMDiff_val (R := V →L[ℝ] V)).clm_apply (contMDiff_const (c := v)))
  | mul x y hx hy =>
    simp only [map_mul]
    exact ((CliffordAlgebra.NegativeMetric.mulCLM V).isBoundedBilinearMap.contDiff.comp_contMDiff
      (hx.prodMk_space hy)).congr fun _ ↦ (CliffordAlgebra.NegativeMetric.mulCLM_apply V _ _).symm
  | add x y hx hy =>
    exact (hx.add hy).congr fun g ↦ map_add (cliffordAlgEquiv g) x y

/-- The orthogonal action on the Euclidean Clifford algebra is smooth. -/
instance instContMDiffSMulCliffordAlgebra :
    ContMDiffSMul (model (V →L[ℝ] V)) 𝓘(ℝ, C) ∞ (unitary (V →L[ℝ] V)) C where
  contMDiff_smul := by
    let ρ : unitary (V →L[ℝ] V) → C →L[ℝ] C :=
      fun g ↦ (cliffordAlgEquiv g).toLinearMap.toContinuousLinearMap
    have hρ : ContMDiff (model (V →L[ℝ] V)) 𝓘(ℝ, C →L[ℝ] C) ∞ ρ := by
      intro g
      exact TauCeti.contMDiffAt_clm_apply.mpr fun x ↦
        (contMDiff_cliffordAlgEquiv_apply x).contMDiffAt
    exact (hρ.comp contMDiff_fst).clm_apply contMDiff_snd

/-- The smooth orthogonal action is continuous in the Euclidean Clifford topology. -/
instance instContinuousSMulCliffordAlgebra : ContinuousSMul (unitary (V →L[ℝ] V)) C :=
  ⟨(contMDiff_smul (I := model (V →L[ℝ] V)) (I' := 𝓘(ℝ, C)) (n := ∞)).continuous⟩

end Unitary
