/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The first Bianchi identity

For a torsion-free smooth connection on the tangent bundle, curvature satisfies
`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`. We prove this on smooth vector fields and then
on individual tangent vectors. No metric or fibre norm is required.

Together with the skew-adjointness of metric curvature, this identity gives the
pair-interchange symmetry of the Riemann tensor and symmetry of its Ricci contraction.
The proof uses the Jacobi identity for vector fields and the torsion-free equation
`∇_X Y - ∇_Y X = [X,Y]`.

The sign convention and identity follow J. M. Lee, *Introduction to Riemannian
Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7 (curvature symmetries).
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [ContMDiffCovariantDerivative cov ∞]

private theorem apply_mlieBracket_of_torsion_eq_zero (ht : cov.torsion = 0)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) (u : TangentSpace I x) :
    cov (mlieBracket I Y Z) x u =
      cov (fun y ↦ cov Z y (Y y)) x u - cov (fun y ↦ cov Y y (Z y)) x u := by
  have hYZ := cov.contMDiff_apply (V := TangentSpace I) hY hZ
  have hZY := cov.contMDiff_apply (V := TangentSpace I) hZ hY
  have heq : mlieBracket I Y Z =
      (fun y ↦ cov Z y (Y y)) - fun y ↦ cov Y y (Z y) := by
    funext y
    exact (cov.torsion_eq_zero_iff.mp ht
      (hY.mdifferentiable (by simp) y) (hZ.mdifferentiable (by simp) y)).symm
  have hb : CMDiff ∞ (T% (mlieBracket I Y Z)) := by
    rw [heq]
    exact hYZ.sub_section hZY
  have ha : (fun y ↦ cov Z y (Y y)) =
      mlieBracket I Y Z + fun y ↦ cov Y y (Z y) := by
    rw [heq, sub_add_cancel]
  have hd := congrArg (fun s ↦ cov s x u) ha
  rw [cov.isCovariantDerivativeOn.add (hb.mdifferentiable (by simp) x)
    (hZY.mdifferentiable (by simp) x)] at hd
  exact eq_sub_of_add_eq hd.symm

local notation "curvature" => cov.curvatureOperator (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The first Bianchi identity for smooth vector fields and a torsion-free smooth
connection on the tangent bundle. -/
theorem curvatureOperator_cyclic_eq_zero (ht : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (x : M) :
    curvature X Y Z x + curvature Y Z X x +
      curvature Z X Y x = 0 := by
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
    (cov.torsion_eq_zero_iff.mp ht
      (hU.mdifferentiable (by simp) x) (hV.mdifferentiable (by simp) x)).symm
  have hj := leibniz_identity_mlieBracket_apply
    (hX.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt
    (hY.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt
    (hZ.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt (x := x)
  rw [ht' hX (hbr hY hZ), ht' (hbr hX hY) hZ, ht' hY (hbr hX hZ),
    apply_mlieBracket_of_torsion_eq_zero ht hY hZ,
    apply_mlieBracket_of_torsion_eq_zero ht hX hY,
    apply_mlieBracket_of_torsion_eq_zero ht hX hZ] at hj
  simp only [curvatureOperator_apply]
  rw [mlieBracket_swap_apply (V := Z) (W := X), map_neg]
  convert sub_eq_zero.mpr hj using 1
  abel

variable [T2Space M]

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
  exact curvatureOperator_cyclic_eq_zero ht hX hY hZ x

end CovariantDerivative
