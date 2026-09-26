/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The first Bianchi identity

For a torsion-free smooth connection on the tangent bundle, curvature satisfies
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`.

Together with the skew-adjointness of metric curvature, this identity gives the
pair-interchange symmetry of the Riemann tensor and symmetry of its Ricci contraction.

The sign convention and identity follow J. M. Lee, *Introduction to Riemannian
Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7 (curvature symmetries).
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureOperator (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The first Bianchi identity for smooth vector fields and a torsion-free smooth
connection on the tangent bundle. -/
theorem curvatureOperator_cyclic_eq_zero
    (ht : cov.IsTorsionFree)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) :
    curvature X Y Z x + curvature Y Z X x +
      curvature Z X Y x = 0 := by
  have ht'free : ∀ {U V : Π y : M, TangentSpace I y} {y : M},
      MDiffAt (T% U) y → MDiffAt (T% V) y →
        cov V y (U y) - cov U y (V y) = mlieBracket I U V y :=
    (isTorsionFree_iff cov).mp ht
  let _ : IsManifold I (minSmoothness ℝ 3) M :=
    IsManifold.of_le (m := minSmoothness ℝ 3) (n := ∞) (by simp)
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
    IsManifold.of_le (m := (∞ : ℕ∞ω) + 1) (n := ∞) (by simp)
  have hbr {U V : Π y : M, TangentSpace I y}
      (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) :
      CMDiff ∞ (T% (mlieBracket I U V)) :=
    ContDiff.mlieBracket_vectorField (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) hU hV (by
      simp [minSmoothness_of_isRCLikeNormedField])
  have ht' {U V : Π y : M, TangentSpace I y}
      (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) :
      mlieBracket I U V x = cov V x (U x) - cov U x (V x) :=
    (ht'free (hU.mdifferentiable (by simp) x) (hV.mdifferentiable (by simp) x)).symm
  have hj := leibniz_identity_mlieBracket_apply
    (hX.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt
    (hY.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt
    (hZ.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt (x := x)
  rw [ht' hX (hbr hY hZ), ht' (hbr hX hY) hZ, ht' hY (hbr hX hZ),
    cov.covariantDerivative_mlieBracket_apply_eq_sub_of_torsion_free ht hY hZ x (X x),
    cov.covariantDerivative_mlieBracket_apply_eq_sub_of_torsion_free ht hX hY x (Z x),
    cov.covariantDerivative_mlieBracket_apply_eq_sub_of_torsion_free ht hX hZ x (Y x)] at hj
  simp only [curvatureOperator_apply]
  rw [mlieBracket_swap_apply (V := Z) (W := X), map_neg]
  convert sub_eq_zero.mpr hj using 1
  abel

variable [FiniteDimensional ℝ E] [T2Space M]

local notation "tensor" => cov.curvatureTensor

/-- The first Bianchi identity on tangent vectors. It applies in particular to the
Levi-Civita connection, which has zero torsion. -/
theorem curvatureTensor_cyclic_eq_zero (ht : cov.torsion = 0)
    (x : M) (u v w : TangentSpace I x) :
    tensor x u v w + tensor x v w u + tensor x w u v = 0 := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  rw [curvatureTensor_apply cov x hX hY hZ,
    curvatureTensor_apply cov x hY hZ hX,
    curvatureTensor_apply cov x hZ hX hY]
  exact curvatureOperator_cyclic_eq_zero
    ((isTorsionFree_iff_torsion_eq_zero cov).mpr ht) hX hY hZ x

end CovariantDerivative
