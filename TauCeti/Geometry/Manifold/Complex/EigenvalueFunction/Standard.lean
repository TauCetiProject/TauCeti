/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.EigenvalueFunction
public import TauCeti.Analysis.Complex.LeviForm.Laplacian
public import TauCeti.Geometry.Symplectic.Complex.ImInner.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The standard Hermitian metric and the flat complex Laplacian

On a complex inner product space `V`, regarded as a complex manifold modelled on itself, the
**standard Hermitian metric** `TauCeti.standardHermitianMetric V` is the constant real two-form
`ω(u, v) = Im ⟪u, v⟫`; on `ℂⁿ` it is `Σ_j dx_j ∧ dy_j`. Its Hermitian form is the inner product
(`TauCeti.twoFormHermitianForm_standardHermitianMetric`), and it is a Hermitian metric: it is
compatible with multiplication by `i` (`TauCeti.compatible_standardHermitianMetric`).

Relative to it, the eigenvalue function of `i ∂∂bar φ` is the relative eigenvalue vector of
`2 L_φ(x)` for the inner product, and the complex Laplacian is half the Euclidean Laplacian,
`Δ_ω φ = Δ φ / 2` (`TauCeti.complexLaplacian_standardHermitianMetric`), where `Δ` is the Laplacian
for the real inner product `Re ⟪·, ·⟫`; on `ℂⁿ` this is
`Δ_ω φ = (1/2)·Σ_j (∂²φ/∂x_j² + ∂²φ/∂y_j²)`.

## Main definitions

* `TauCeti.standardHermitianMetric V`: the constant two-form `ω(u, v) = Im ⟪u, v⟫`.

## Main results

* `TauCeti.twoFormHermitianForm_standardHermitianMetric`: `H_ω = ⟪·, ·⟫`.
* `TauCeti.compatible_standardHermitianMetric`: `ω` is a Hermitian metric.
* `TauCeti.relEigenvalueFunction_standardHermitianMetric`: `λ_ω[i ∂∂bar φ](x)` is the relative
  eigenvalue vector of `2 L_φ(x)` for the inner product.
* `TauCeti.complexLaplacian_standardHermitianMetric_eq_sum`: `Δ_ω φ = 2·Σ_j Re L_φ(b_j, b_j)` for
  any orthonormal basis `b`.
* `TauCeti.complexLaplacian_standardHermitianMetric`: `Δ_ω φ = Δ φ / 2` for `φ` of class `C²`.
-/

public section

open Complex Module
open scoped ContDiff Manifold InnerProductSpace Laplacian

noncomputable section

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

variable (V) in
/-- The **standard Hermitian metric** `ω(u, v) = Im ⟪u, v⟫` of a complex inner product space `V`,
as a constant smooth two-form on `V`: the symplectic form `TauCeti.imInnerSymplecticForm V`, made
constant by `SymplecticForm.constSmooth`. On `ℂⁿ` it is `Σ_j dx_j ∧ dy_j`, so that `ω(1, i) = 1`
on `ℂ`. Its Hermitian form is the inner product. -/
def standardHermitianMetric : SmoothTwoForm 𝓘(ℝ, V) V :=
  (imInnerSymplecticForm V).constSmooth

variable (V) in
/-- The standard Hermitian metric is the symplectic form `TauCeti.imInnerSymplecticForm V` made
constant, so the `SymplecticForm.constSmooth` API (closedness, nondegeneracy) applies to it. -/
theorem standardHermitianMetric_eq_constSmooth :
    standardHermitianMetric V = (imInnerSymplecticForm V).constSmooth := (rfl)

/-- The standard Hermitian metric evaluates as `ω(u, v) = Im ⟪u, v⟫`. -/
@[simp]
theorem standardHermitianMetric_apply (x u v : V) :
    (standardHermitianMetric V).val x ![u, v] = (⟪u, v⟫_ℂ).im :=
  ((SmoothBundleForm.eval₂_apply _ x u v).symm.trans
    ((imInnerSymplecticForm V).constSmooth_apply x u v)).trans (imInnerSymplecticForm_apply u v)

/-- **The Hermitian form of the standard metric is the inner product**:
`H_ω(u, v) = ω(u, i v) + i·ω(u, v) = ⟪u, v⟫`. -/
@[simp]
theorem twoFormHermitianForm_standardHermitianMetric (x u v : V) :
    twoFormHermitianForm V (standardHermitianMetric V).val x u v = ⟪u, v⟫_ℂ := by
  rw [twoFormHermitianForm_def, standardHermitianMetric_apply, standardHermitianMetric_apply]
  apply Complex.ext <;> simp [inner_smul_right]

/-- **The standard metric is a Hermitian metric**: it is invariant under, and tames,
multiplication by `i`. -/
theorem compatible_standardHermitianMetric :
    (standardHermitianMetric V).Compatible
      (SmoothAlmostComplexStructure.ofComplexManifold V V) := by
  rw [SmoothAlmostComplexStructure.ofComplexManifold_self_eq_constSmooth,
    standardHermitianMetric_eq_constSmooth]
  exact SymplecticForm.compatible_constSmooth_iff.2 imInnerSymplecticForm_compatible

variable {φ : V → ℝ} {x : V}

/-- **The eigenvalue function of `i ∂∂bar φ` relative to the standard metric** is the relative
eigenvalue vector of `2 L_φ(x)` for the inner product. -/
theorem relEigenvalueFunction_standardHermitianMetric (h : ((2 : ℂ) • leviForm φ x).IsSymm) :
    relEigenvalueFunction V (standardHermitianMetric V) 0 φ x = h.relEigenvalues rfl := by
  refine compatible_standardHermitianMetric.relEigenvalueFunction_eq_of_isRelEigenvalueVector
    (fun _ _ ↦ by simp) ?_ (h.relEigenvalues_antitone rfl)
  have hD : ddbarHermitianForm V 0 φ x = fun u v ↦ ((2 : ℂ) • leviForm φ x) u v := by
    ext u v
    simp [manifoldLeviForm_eq_leviForm]
  rw [funext₂ (twoFormHermitianForm_standardHermitianMetric x), hD]
  exact h.isRelEigenvalueVector_relEigenvalues

section Laplacian

/-- **The complex Laplacian of the standard metric in an orthonormal basis**: for `φ` of class
`C²` at `x` and any orthonormal basis `b`, `Δ_ω φ(x) = 2·Σ_j Re L_φ(x)(b_j, b_j)`. -/
theorem complexLaplacian_standardHermitianMetric_eq_sum (hφ : ContDiffAt ℝ 2 φ x)
    (b : OrthonormalBasis (Fin (finrank ℂ V)) ℂ V) :
    complexLaplacian V (standardHermitianMetric V) φ x =
      2 * ∑ j, (leviForm φ x (b j) (b j)).re := by
  rw [compatible_standardHermitianMetric.complexLaplacian_eq_two_mul_sum
    (contMDiffAt_iff_contDiffAt.2 hφ) b fun i j ↦ by
      rw [twoFormHermitianForm_standardHermitianMetric, b.inner_eq_ite]]
  simp only [manifoldLeviForm_eq_leviForm]

attribute [local instance] InnerProductSpace.complexToReal

/-- **The complex Laplacian of the standard metric is half the Laplacian**: for `φ` of class `C²`
at `x`, `Δ_ω φ(x) = Δ φ(x) / 2`, where `Δ` is the Laplacian for the real inner product
`Re ⟪·, ·⟫`. On `ℂⁿ` this is `Δ_ω φ = (1/2)·Σ_j (∂²φ/∂x_j² + ∂²φ/∂y_j²)`. -/
theorem complexLaplacian_standardHermitianMetric (hφ : ContDiffAt ℝ 2 φ x) :
    complexLaplacian V (standardHermitianMetric V) φ x = Δ φ x / 2 := by
  rw [complexLaplacian_standardHermitianMetric_eq_sum hφ (stdOrthonormalBasis ℂ V),
    sum_re_leviForm_apply_self (stdOrthonormalBasis ℂ V)]
  ring

end Laplacian

end TauCeti
