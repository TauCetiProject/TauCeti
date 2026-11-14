/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Einstein

/-!
# Schur's theorem

Let `∇` be a smooth metric-compatible torsion-free connection on the tangent bundle of a
Riemannian manifold `M` of dimension `n ≥ 3`, such as its Levi-Civita connection. Suppose that
at every point `x` all tangent two-planes have the same sectional curvature `κ x`, so that the
curvature tensor is `R(w, u)v = κ(x) (⟨u, v⟩ w - ⟨w, v⟩ u)`. Schur's theorem states that the
function `κ` is then locally constant, hence constant when `M` is connected.

Schur's theorem is derived from the Ricci tensor. Under the constant-curvature form the Ricci
tensor is `(n - 1) κ g`, and Einstein's constancy theorem
(`CovariantDerivative.mfderiv_eq_zero_of_ricciTensor_eq_smul_inner`) makes `(n - 1) κ` locally
constant when `n ≠ 2`; since `n - 1 ≠ 0` for `n ≥ 3`, `κ` is locally constant. In dimension two
every tangent space has a single two-plane, so the curvature is pointwise isotropic for every
metric, and the conclusion fails for any surface whose Gaussian curvature is not constant.

## Main results

* `CovariantDerivative.mfderiv_eq_zero_of_curvatureTensor_eq_smul_inner_sub`: the local form of
  Schur's theorem, `dκ(x) = 0` in dimension at least three when the curvature has
  constant-curvature form near `x`.
* `CovariantDerivative.eq_of_forall_hasSectionalCurvatureAt` and
  `CovariantDerivative.hasConstantSectionalCurvature_of_forall_hasSectionalCurvatureAt`:
  **Schur's theorem** on a preconnected manifold.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience
  (1963), Chapter V, Section 2 (Schur's theorem).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- **Schur's theorem**, local form. Let a metric-compatible torsion-free connection have
curvature tensor of the pointwise constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)`
at every point `y` near `x`, in dimension at least three. Then `dκ` vanishes at `x`. No
differentiability of `κ` is assumed: near `x`, `κ` is the smooth scalar curvature divided by
`n (n - 1)`. -/
theorem mfderiv_eq_zero_of_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : 3 ≤ Module.finrank ℝ E) {κ : M → ℝ} {x : M}
    (hκ : ∀ᶠ y in 𝓝 x, ∀ (w u v : TangentSpace I y),
      curvature y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u)) :
    mfderiv I 𝓘(ℝ) κ x = 0 := by
  have hκx := cov.mdifferentiableAt_of_eventually_curvatureTensor_eq_smul_inner_sub (by omega) hκ
  -- Near `x` the Ricci tensor is `(n - 1) κ g`, so Einstein's constancy theorem applies.
  have hn : ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by
    have : (3 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdim
    linarith
  have h := mfderiv_eq_zero_of_ricciTensor_eq_smul_inner hcov ht (by omega)
    (a := ((Module.finrank ℝ E : ℝ) - 1) • κ) (x := x)
    (hκ.mono fun y hy ↦ by
      rw [cov.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub y (κ y) hy]
      rw [Pi.smul_apply, smul_eq_mul, TauCeti.finrank_tangentSpace (I := I) (𝕜 := ℝ) y])
  rw [(hκx.hasMFDerivAt.const_smul _).mfderiv] at h
  exact (smul_eq_zero.1 h).resolve_left hn

/-- **Schur's theorem.** Let a metric-compatible torsion-free connection on a preconnected
manifold of dimension at least three have, at every point `x`, the same sectional curvature `κ x`
on all tangent two-planes at `x`. Then `κ` is constant. -/
theorem eq_of_forall_hasSectionalCurvatureAt [PreconnectedSpace M]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : 3 ≤ Module.finrank ℝ E) {κ : M → ℝ}
    (hκ : ∀ x, cov.HasSectionalCurvatureAt hcov x (κ x)) (x y : M) : κ x = κ y := by
  have hform (z : M) : ∀ᶠ y in 𝓝 z, ∀ (w u v : TangentSpace I y),
      curvature y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) :=
    .of_forall fun y ↦ (hκ y).curvatureTensor_eq_smul_inner_sub ht
  exact MDifferentiable.apply_eq_of_mfderiv_eq_zero
    (fun z ↦ cov.mdifferentiableAt_of_eventually_curvatureTensor_eq_smul_inner_sub (by omega)
      (hform z))
    (fun z ↦ mfderiv_eq_zero_of_curvatureTensor_eq_smul_inner_sub hcov ht hdim (hform z)) x y

/-- **Schur's theorem**, global form. If a metric-compatible torsion-free connection on a
preconnected manifold of dimension at least three has, at every point `x`, the same sectional
curvature `κ x` on all tangent two-planes at `x`, then it has constant sectional curvature
`κ x₀` for any point `x₀`. -/
theorem hasConstantSectionalCurvature_of_forall_hasSectionalCurvatureAt [PreconnectedSpace M]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : 3 ≤ Module.finrank ℝ E) {κ : M → ℝ}
    (hκ : ∀ x, cov.HasSectionalCurvatureAt hcov x (κ x)) (x₀ : M) :
    cov.HasConstantSectionalCurvature hcov (κ x₀) :=
  (cov.hasConstantSectionalCurvature_iff hcov _).2 fun x ↦
    eq_of_forall_hasSectionalCurvatureAt hcov ht hdim hκ x x₀ ▸ hκ x

end CovariantDerivative
