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

If a second frame `(t₀, t₁)` is orthonormal, `s₀` is a unit vector `z₀ t₀ + z₁ t₁` and the
matrix of `s` in `t` has determinant one (for instance if `s₁ = -z₁ t₀ + z₀ t₁`, so that `s` is
the rotation of `t` by `z`), the change of frame formula `A(s) = P⁻¹ dP + P⁻¹ A(t) P` reduces to
`A¹₀(s) = A¹₀(t) + z₀ dz₁ - z₁ dz₀`: the connection forms differ by the pullback of the angle
form of the circle, locally `dθ` for `z = (cos θ, sin θ)`.

## Main results

* `IsLocalFrameOn.mextDeriv_connectionForm_eq_coeff_curvatureOperator`: `dAˡⱼ = Fˡⱼ` in an
  orthonormal frame of rank two.
* `IsLocalFrameOn.connectionForm_zero_one_eq_add_smul_sub_smul`: the connection forms of two
  frames of rank two related by a rotation differ by `z₀ dz₁ - z₁ dz₀`.
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

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {n n' : ℕ∞ω} {s t : Fin 2 → Π x, V x} {u u' : Set M} {cov : CovariantDerivative I F V}

/-- **The connection forms of two frames of rank two related by a rotation.** Let `(t₀, t₁)` be a
`C¹` local frame orthonormal on its open domain, and `(s₀, s₁)` a local frame. At a point `x` of
both domains write `zₖ = ⟪tₖ, s₀⟫`, and assume that `s₀` is a unit vector and that the matrix of
`s` in `t` has determinant one, `z₀ ⟪t₁, s₁⟫ - z₁ ⟪t₀, s₁⟫ = 1`; for instance `s` may be the
rotation `s₁ = -z₁ t₀ + z₀ t₁` of `t` by the unit vector `z = (z₀, z₁)`. If `s₀` is
differentiable at `x`, then for a metric connection the connection forms `A¹₀`,
`ω(X) = ⟪s₁, ∇_X s₀⟫` for orthonormal `s`, differ at `x` by the pullback `z₀ dz₁ - z₁ dz₀` of the
angle form of the circle:

`A¹₀(s) = A¹₀(t) + z₀ dz₁ - z₁ dz₀`.

Writing `z = (cos θ, sin θ)` locally, this is the classical `ω(s) = ω(t) + dθ`. -/
theorem connectionForm_zero_one_eq_add_smul_sub_smul (hs : IsLocalFrameOn I F n s u)
    (ht : IsLocalFrameOn I F n' t u') (hn' : 1 ≤ n') (hu' : IsOpen u')
    (hot : ∀ y ∈ u', Orthonormal ℝ (fun i ↦ t i y)) (hcov : cov.IsMetricCompatible) {x : M}
    (hx : x ∈ u) (hx' : x ∈ u') (hs₀ : MDiffAt (T% (s 0)) x) (hnorm : ‖s 0 x‖ = 1)
    (hdet : inner ℝ (t 0 x) (s 0 x) * inner ℝ (t 1 x) (s 1 x) -
      inner ℝ (t 1 x) (s 0 x) * inner ℝ (t 0 x) (s 1 x) = 1) :
    hs.connectionForm cov 0 1 x = ht.connectionForm cov 0 1 x +
      inner ℝ (t 0 x) (s 0 x) •
        TauCeti.mextDeriv (TauCeti.RoughForm.ofFunction I fun y ↦ inner ℝ (t 1 y) (s 0 y)) x -
      inner ℝ (t 1 x) (s 0 x) •
        TauCeti.mextDeriv (TauCeti.RoughForm.ofFunction I fun y ↦ inner ℝ (t 0 y) (s 0 y)) x := by
  set z₀ := inner ℝ (t 0 x) (s 0 x)
  set z₁ := inner ℝ (t 1 x) (s 0 x)
  set a := inner ℝ (t 0 x) (s 1 x)
  set b := inner ℝ (t 1 x) (s 1 x)
  -- On the domain of `t`, the coefficients of `s₀` in `t` are the inner products `⟪tₘ, s₀⟫`.
  have hP (m : Fin 2) : (fun y ↦ ht.coeff m y (s 0 y)) =ᶠ[𝓝 x]
      fun y ↦ inner ℝ (t m y) (s 0 y) := by
    filter_upwards [hu'.mem_nhds hx'] with y hy
    exact ht.coeff_eq_inner hy (hot y hy) m (s 0 y)
  have hPd (m : Fin 2) : MDiffAt (fun y ↦ ht.coeff m y (s 0 y)) x :=
    (MDifferentiableAt.inner_bundle ((((ht.contMDiffOn m).contMDiffAt (hu'.mem_nhds hx')).of_le
      hn').mdifferentiableAt one_ne_zero) hs₀).congr_of_eventuallyEq (hP m)
  have hdP (m : Fin 2) :
      TauCeti.mextDeriv (TauCeti.RoughForm.ofFunction I fun y ↦ ht.coeff m y (s 0 y)) x =
        TauCeti.mextDeriv (TauCeti.RoughForm.ofFunction I fun y ↦ inner ℝ (t m y) (s 0 y)) x :=
    TauCeti.mextDeriv_congr_of_eventuallyEq ((hP m).mono fun y hy ↦ by
      ext v
      simp [hy])
  -- At `x`, `s₀ = z₀ t₀ + z₁ t₁` and `s₁ = a t₀ + b t₁` with `z₀ b - z₁ a = 1`; inverting this
  -- matrix expresses `t` in `s`, and `z₀² + z₁² = 1` since `s₀` is a unit vector.
  have hs₀x : s 0 x = z₀ • t 0 x + z₁ • t 1 x := by
    simpa [Fin.sum_univ_two] using (ht.sum_inner_smul_eq hx' (hot x hx') (s 0 x)).symm
  have hs₁x : s 1 x = a • t 0 x + b • t 1 x := by
    simpa [Fin.sum_univ_two] using (ht.sum_inner_smul_eq hx' (hot x hx') (s 1 x)).symm
  have hz : z₀ ^ 2 + z₁ ^ 2 = 1 := by
    simpa [Fin.sum_univ_two, hnorm] using ht.sum_sq_norm_inner hx' (hot x hx') (s 0 x)
  have ht₀ : t 0 x = b • s 0 x - z₁ • s 1 x := by
    rw [hs₀x, hs₁x]
    linear_combination (norm := module) (-hdet) • t 0 x
  have ht₁ : t 1 x = -a • s 0 x + z₀ • s 1 x := by
    rw [hs₀x, hs₁x]
    linear_combination (norm := module) (-hdet) • t 1 x
  have hc₀ : hs.coeff 1 x (t 0 x) = -z₁ := by
    rw [ht₀, map_sub, map_smul, map_smul, hs.coeff_apply_self hx, hs.coeff_apply_self hx]
    simp
  have hc₁ : hs.coeff 1 x (t 1 x) = z₀ := by
    rw [ht₁, map_add, map_smul, map_smul, hs.coeff_apply_self hx, hs.coeff_apply_self hx]
    simp
  have hP₀ : ht.coeff 0 x (s 0 x) = z₀ := ht.coeff_eq_inner hx' (hot x hx') 0 (s 0 x)
  have hP₁ : ht.coeff 1 x (s 0 x) = z₁ := ht.coeff_eq_inner hx' (hot x hx') 1 (s 0 x)
  rw [hs.connectionForm_eq_sum_coeff_smul cov ht hn' (hu'.mem_nhds hx') 0 hPd 1]
  simp only [Fin.sum_univ_two, hdP, hc₀, hc₁, hP₀, hP₁,
    ht.connectionForm_self_eq_zero hn' hu' hot hcov, ht.connectionForm_swap hn' hu' hot hcov 1 0,
    Pi.neg_apply]
  linear_combination (norm := module) hz • ht.connectionForm cov 0 1 x

end Rotation

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
