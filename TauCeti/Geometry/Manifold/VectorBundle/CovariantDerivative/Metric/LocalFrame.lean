/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame.Orthonormal
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionForm

/-!
# Metric connections in orthonormal local frames

In an orthonormal local frame `s`, the coefficient of `∇_v sⱼ` along `sᵢ` is `⟪sᵢ, ∇_v sⱼ⟫`
(`IsLocalFrameOn.coeff_eq_inner`). For a metric-compatible connection these coefficients form a
skew-symmetric matrix, because the inner products `⟪sᵢ, sⱼ⟫` are constant
(`IsLocalFrameOn.coeff_covariantDerivative_add_eq_zero`); in particular the diagonal entries vanish
(`IsLocalFrameOn.coeff_covariantDerivative_self_eq_zero`). The frame and its orthonormality are
required only on an open set containing the point, and the direction `v` is an arbitrary tangent
vector there. The coefficients are zero off the domain, so the identities hold globally.

These coefficients are the values of the connection one-forms `IsLocalFrameOn.connectionForm`,
which are therefore skew-symmetric too (`IsLocalFrameOn.connectionForm_add_connectionForm_swap`)
with vanishing diagonal (`IsLocalFrameOn.connectionForm_self_eq_zero`).
For an orthonormal frame `(e₁, e₂)` of a surface they reduce to a single one-form `ω` with
`∇e₁ = ω ⊗ e₂` and `∇e₂ = -ω ⊗ e₁`.

## Main results

* `IsLocalFrameOn.coeff_covariantDerivative_add_eq_zero`: the connection matrix of a metric
  connection in an orthonormal local frame is skew-symmetric.
* `IsLocalFrameOn.coeff_covariantDerivative_self_eq_zero`: its diagonal entries vanish.
* `IsLocalFrameOn.connectionForm_add_connectionForm_swap`: the connection one-forms of such a
  frame are skew-symmetric.
* `IsLocalFrameOn.connectionForm_self_eq_zero`: the diagonal connection one-forms vanish.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4.
-/

public section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace IsLocalFrameOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I] [IsContMDiffRiemannianBundle I 1 F V]
  {ι : Type*} {n : ℕ∞ω} {s : ι → Π x, V x} {u : Set M}
  (hs : IsLocalFrameOn I F n s u) (hn : 1 ≤ n) (hu : IsOpen u)
  (ho : ∀ y ∈ u, Orthonormal ℝ (fun i ↦ s i y))
  {cov : CovariantDerivative I F V} (hcov : cov.IsMetricCompatible)

include hn hu ho hcov in
/-- **The connection matrix in an orthonormal frame is skew-symmetric.** For a metric-compatible
connection and a `C¹` local frame orthonormal on its open domain, the coefficient of `∇_v sⱼ`
along `sᵢ` is minus the coefficient of `∇_v sᵢ` along `sⱼ`, for every tangent vector `v`. -/
theorem coeff_covariantDerivative_add_eq_zero (x : M) (i j : ι)
    (v : TangentSpace I x) :
    hs.coeff i x (cov (s j) x v) + hs.coeff j x (cov (s i) x v) = 0 := by
  classical
  by_cases hx : x ∈ u
  · let : Fintype ι := hs.fintypeOfFiniteDimensional hx
    have hframe (k : ι) : MDiffAt (T% (s k)) x :=
      ((hs.contMDiffAt hu hx k).of_le hn).mdifferentiableAt one_ne_zero
    have hconstant : (fun y ↦ inner ℝ (s i y) (s j y)) =ᶠ[𝓝 x]
        fun _ ↦ if i = j then 1 else 0 := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact (orthonormal_iff_ite.mp (ho y hy)) i j
    have hmetric := hcov.inner_apply_add_inner_apply_eq_zero_of_eventuallyEq_const
      (hframe i) (hframe j) hconstant v
    rw [real_inner_comm (s j x) (cov (s i) x v)] at hmetric
    rw [hs.coeff_eq_inner hx (ho x hx), hs.coeff_eq_inner hx (ho x hx)]
    linarith
  · simp [hs.coeff_apply_of_notMem hx]

include hn hu ho hcov in
/-- Swapping the indices of a connection coefficient in an orthonormal frame negates it. -/
theorem coeff_covariantDerivative_swap (x : M) (i j : ι) (v : TangentSpace I x) :
    hs.coeff i x (cov (s j) x v) = -hs.coeff j x (cov (s i) x v) :=
  eq_neg_of_add_eq_zero_left (hs.coeff_covariantDerivative_add_eq_zero hn hu ho hcov x i j v)

include hn hu ho hcov in
/-- The diagonal entries of the connection matrix of a metric connection in an orthonormal local
frame vanish: `∇_v sᵢ` has no component along `sᵢ`. -/
@[simp]
theorem coeff_covariantDerivative_self_eq_zero (x : M) (i : ι)
    (v : TangentSpace I x) : hs.coeff i x (cov (s i) x v) = 0 := by
  have h := hs.coeff_covariantDerivative_add_eq_zero hn hu ho hcov x i i v
  linarith

include hn hu ho hcov in
/-- **The connection forms of an orthonormal frame are skew-symmetric.** For a metric-compatible
connection and a `C¹` local frame orthonormal on its open domain, the totalized connection
one-forms satisfy `Aˡⱼ + Aʲₗ = 0`. -/
theorem connectionForm_add_connectionForm_swap [FiniteDimensional ℝ E] (j l : ι) :
    hs.connectionForm cov j l + hs.connectionForm cov l j = 0 := by
  ext x v
  simpa using hs.coeff_covariantDerivative_add_eq_zero hn hu ho hcov x l j (v 0)

include hn hu ho hcov in
/-- Swapping the indices of a connection one-form in an orthonormal frame negates it. -/
theorem connectionForm_swap [FiniteDimensional ℝ E] (j l : ι) :
    hs.connectionForm cov j l = -hs.connectionForm cov l j :=
  eq_neg_of_add_eq_zero_left (hs.connectionForm_add_connectionForm_swap hn hu ho hcov j l)

include hn hu ho hcov in
/-- The diagonal connection forms of a metric connection in a `C¹` orthonormal local frame
vanish: `Aⁱᵢ = 0` as a totalized one-form. -/
@[simp]
theorem connectionForm_self_eq_zero [FiniteDimensional ℝ E] (i : ι) :
    hs.connectionForm cov i i = 0 := by
  ext x v
  simpa using hs.coeff_covariantDerivative_self_eq_zero hn hu ho hcov x i (v 0)

end IsLocalFrameOn
