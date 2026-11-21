/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# Connection forms of orthonormal frames of rank two

Let `(s₀, s₁)` be an orthonormal local frame of a rank-two bundle with a metric connection. Its
diagonal connection one-forms vanish (`IsLocalFrameOn.connectionForm_self_eq_zero`), so the
quadratic terms of Cartan's second structure equation vanish too: the exterior derivative of the
connection one-form `Aˡⱼ`, the coefficient of `∇sⱼ` along `sₗ`, is the corresponding curvature
coefficient.

For the tangent bundle of a surface with an orthonormal frame `(e₀, e₁)`, the one-form
`ω = A¹₀`, `ω(X) = ⟪e₁, ∇_X e₀⟫`, therefore satisfies `dω(e₀, e₁) = -K`, where `K` is the
sectional curvature, with the curvature convention
`R(X, Y)Z = ∇_X∇_Y Z - ∇_Y∇_X Z - ∇_[X,Y] Z`. All frame hypotheses are local to an open subset
of the manifold.

## Main results

* `IsLocalFrameOn.mextDeriv_connectionForm_eq_coeff_curvatureOperator`: `dAˡⱼ = Fˡⱼ` in an
  orthonormal frame of rank two.
* `IsLocalFrameOn.mextDeriv_connectionForm_eq_neg_sectionalCurvature`: `dA¹₀(e₀, e₁) = -K` for an
  orthonormal tangent frame of a surface.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer, 2018, Chapters 7
  and 9.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace IsLocalFrameOn

section Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 2 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {n : ℕ∞ω} {s : Fin 2 → Π x, V x} {u : Set M}
  {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivativeOn F 1 cov.toFun u]

/-- **Cartan's structure equation in rank two.** For a metric connection and a `C²` local frame
of rank two, orthonormal on its open domain, the exterior derivative of an off-diagonal
connection one-form is the corresponding curvature coefficient: `dAˡⱼ(X, Y) = Fˡⱼ(X, Y)`. -/
theorem mextDeriv_connectionForm_eq_coeff_curvatureOperator (hs : IsLocalFrameOn I F n s u)
    (hn : 2 ≤ n) (hu : IsOpen u) (ho : ∀ y ∈ u, Orthonormal ℝ (fun i ↦ s i y))
    (hcov : cov.IsMetricCompatible) {x : M} (hx : x ∈ u) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiff[u] 1 (T% X)) (hY : CMDiff[u] 1 (T% Y)) (j l : Fin 2) :
    TauCeti.mextDeriv (hs.connectionForm cov j l) x ![X x, Y x] =
      hs.coeff l x (cov.curvatureOperator X Y (s j) x) := by
  have hn₁ : 1 ≤ n := one_le_two.trans hn
  rw [hs.coeff_curvatureOperator_eq_mextDeriv_add_wedge cov hn hu hx hX hY j l]
  have hterm (m : Fin 2) :
      ((hs.connectionForm cov m l).wedge (hs.connectionForm cov j m)) x ![X x, Y x] = 0 := by
    rcases eq_or_ne m l with rfl | hml
    · simp [hs.connectionForm_self_eq_zero hn₁ hu ho hcov]
    rcases eq_or_ne m j with rfl | hmj
    · simp [hs.connectionForm_self_eq_zero hn₁ hu ho hcov]
    obtain rfl : j = l := by omega
    rw [hs.connectionForm_swap hn₁ hu ho hcov m j, TauCeti.RoughForm.wedge_apply_one_one]
    simp only [Pi.neg_apply, ContinuousAlternatingMap.neg_apply]
    ring
  simp [hterm]

end Bundle

section Surface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {s : Fin 2 → Π x : M, TangentSpace I x} {u : Set M}
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov 1] [ContMDiffCovariantDerivative cov ∞]

/-- **The structure equation of a surface.** For a metric connection on the tangent bundle and a
smooth local frame `(e₀, e₁)`, orthonormal on its open domain, the connection one-form
`ω = A¹₀`, `ω(X) = ⟪e₁, ∇_X e₀⟫`, satisfies `dω(e₀, e₁) = -K`, where `K` is the sectional
curvature of the plane `span (e₀, e₁)`. -/
theorem mextDeriv_connectionForm_eq_neg_sectionalCurvature (hs : IsLocalFrameOn I E ∞ s u)
    (hu : IsOpen u) (ho : ∀ y ∈ u, Orthonormal ℝ (fun i ↦ s i y))
    (hcov : IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov) {x : M} (hx : x ∈ u) :
    TauCeti.mextDeriv (hs.connectionForm cov 0 1) x ![s 0 x, s 1 x] =
      -cov.sectionalCurvature hcov x (s 0 x) (s 1 x) := by
  have : ContMDiffCovariantDerivativeOn E 1 cov.toFun u :=
    cov.contMDiffCovariantDerivativeOn_of_isOpen (n := 1) hu
  have h := hs.mextDeriv_connectionForm_eq_coeff_curvatureOperator (by simp) hu ho hcov hx
    ((hs.contMDiffOn 0).of_le (by simp)) ((hs.contMDiffOn 1).of_le (by simp)) 0 1
  rw [hs.coeff_eq_inner hx (ho x hx),
    ← cov.curvatureTensor_apply_of_contMDiffOn x hu hx (hs.contMDiffOn 0)
      (hs.contMDiffOn 1) (hs.contMDiffOn 0)] at h
  have hpair : Orthonormal ℝ ![s 0 x, s 1 x] := by
    convert ho x hx using 1
    ext i
    fin_cases i <;> rfl
  rw [cov.sectionalCurvature_eq_of_orthonormal hcov x _ _ hpair, h]
  have hskew := hcov.inner_curvatureTensor_eq_neg x (s 0 x) (s 1 x) (s 1 x) (s 0 x)
  linarith

end Surface

end IsLocalFrameOn
