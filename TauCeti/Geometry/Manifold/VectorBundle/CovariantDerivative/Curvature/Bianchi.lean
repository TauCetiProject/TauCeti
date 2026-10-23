/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorField.LieBracket

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
  have ht' {U V : Π y : M, TangentSpace I y}
      (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V)) :
      mlieBracket I U V x = cov V x (U x) - cov U x (V x) :=
    (ht'free (hU.mdifferentiable (by simp) x) (hV.mdifferentiable (by simp) x)).symm
  have hj := leibniz_identity_mlieBracket_apply
    (hX.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt
    (hY.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt
    (hZ.of_le (by simp [minSmoothness_of_isRCLikeNormedField])).contMDiffAt (x := x)
  rw [ht' hX (contMDiff_mlieBracket hY hZ), ht' (contMDiff_mlieBracket hX hY) hZ,
    ht' hY (contMDiff_mlieBracket hX hZ),
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

section Riemannian

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- The metric-lowered curvature tensor of a metric-compatible torsion-free connection is
unchanged when its two pairs of arguments are interchanged. -/
theorem IsMetricCompatible.inner_curvatureTensor_swap_pairs
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v w z : TangentSpace I x) :
    inner ℝ (cov.curvatureTensor x u v w) z =
      inner ℝ (cov.curvatureTensor x w z u) v := by
  let R : TangentSpace I x → TangentSpace I x → TangentSpace I x →
      TangentSpace I x → ℝ := fun a b c d ↦ inner ℝ (cov.curvatureTensor x a b c) d
  have hfirst (a b c d : TangentSpace I x) : R a b c d = -R b a c d := by
    simp only [R, cov.curvatureTensor_antisymm x a b, LinearMap.neg_apply, inner_neg_left]
  have hlast (a b c d : TangentSpace I x) : R a b c d = -R a b d c := by
    simpa only [R, real_inner_comm] using hcov.inner_curvatureTensor_eq_neg x a b c d
  have hbianchi (a b c d : TangentSpace I x) :
      R a b c d + R b c a d + R c a b d = 0 := by
    simpa only [R, inner_add_left, inner_zero_left] using
      congrArg (fun q ↦ inner ℝ q d) (cov.curvatureTensor_cyclic_eq_zero ht x a b c)
  have h₁ := hbianchi u v w z
  have h₂ := hbianchi v u z w
  have h₃ := hbianchi w z u v
  have h₄ := hbianchi v w z u
  rw [hfirst v u z w, hlast u v z w] at h₂
  rw [hlast z u w v, hfirst z u v w, hlast u w z v,
    hfirst u w v z] at h₃
  rw [hlast v w z u, hlast w z v u, hlast z v w u] at h₄
  dsimp only [R] at h₁ h₂ h₃ h₄ ⊢
  linarith

end Riemannian

end CovariantDerivative
