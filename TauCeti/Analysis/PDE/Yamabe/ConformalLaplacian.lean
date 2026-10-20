/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Geometry.Manifold.Riemannian.Laplacian.Conformal

/-!
# The conformal Laplacian

On a Riemannian manifold `(M, g)` of dimension `n`, the *conformal Laplacian* is the second-order
operator

`L_g u = aₙ Δ⁺_g u + Scal_g u`,

where `aₙ = 4 (n - 1) / (n - 2)` (`TauCeti.Yamabe.conformalCoefficient`), `Δ⁺_g = -Δ_g` is the
nonnegative Laplacian (`TauCeti.Manifold.laplaceBeltrami` is `Δ_g = div ∘ grad`) and `Scal_g` is
the scalar curvature of the Levi-Civita connection. It is the operator of the Yamabe problem: for
`n > 2` and `u > 0`, the metric `u ^ (4 / (n - 2)) g` has scalar curvature
`u ^ (-(n + 2) / (n - 2)) L_g u`, so `u` gives a metric of constant scalar curvature `λ` exactly
when `L_g u = λ u ^ (pₙ - 1)`. That transformation law is not proved here; only its second-order
part, the transformation of the Laplacian, is.

The definition is total in the dimension; at `n = 2` the coefficient `aₙ` is `0` by the
convention for division by zero, and the operator has its classical meaning only for `n > 2`.
The metric is the `RiemannianBundle` instance of the tangent bundle, as for
`TauCeti.Manifold.laplaceBeltrami`. This file develops the operator itself and its two basic
examples:

* on Euclidean space, which is flat, `L u = aₙ (-Δ u)` for Mathlib's Laplacian `Δ`, so the
  bubble equation `aₙ (-Δ U) = n (n - 1) U ^ (pₙ - 1)` says that every bubble `U` solves the
  Yamabe equation `L U = n (n - 1) U ^ (pₙ - 1)` of the unit round sphere;
* under multiplication of the metric by a positive constant `c`, both `Δ` and `Scal` are
  multiplied by `c⁻¹`, so `L_{c g} = c⁻¹ L_g`.

For the Yamabe metric `ĝ = u ^ (4 / (n - 2)) g` of a positive function `u`, the Laplacian
transforms by `Δ_ĝ v = u ^ (-(n + 2) / (n - 2)) (Δ_g (u v) - v Δ_g u)`.

## Main declarations

* `TauCeti.Yamabe.conformalLaplacian`: the conformal Laplacian `L_g`.
* `TauCeti.Yamabe.conformalLaplacian_add`, `TauCeti.Yamabe.conformalLaplacian_smul`: linearity
  on `C²` functions; `TauCeti.Yamabe.conformalLaplacian_const`: `L_g c = c Scal_g`.
* `TauCeti.Yamabe.contMDiff_conformalLaplacian`: `L_g` maps `C^(k + 2)` functions to `C^k`
  functions.
* `TauCeti.Yamabe.conformalLaplacian_eq_conformalCoefficient_mul_neg_laplacian`: on Euclidean
  space, `L u = aₙ (-Δ u)`.
* `TauCeti.Yamabe.conformalLaplacian_bubble`: the bubbles solve `L U = n (n - 1) U ^ (pₙ - 1)`.
* `TauCeti.Yamabe.conformalLaplacian_rescale_const`: `L_{c g} = c⁻¹ L_g` for a constant `c > 0`.
* `TauCeti.Yamabe.laplaceBeltrami_rescale_rpow_four_div_finrank_sub_two`: the Laplacian of
  `u ^ (4 / (n - 2)) g`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2 (the
  conformal Laplacian and its conventions) and §3 (the Euclidean bubbles).
-/

public section

open Bundle InnerProductSpace Laplacian Module TauCeti.Manifold
open scoped ContDiff Manifold Gradient

noncomputable section

namespace TauCeti.Yamabe

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The **conformal Laplacian** `L_g u = aₙ Δ⁺_g u + Scal_g u` of a function `u` on a smooth
Riemannian manifold of dimension `n`, where `aₙ = 4 (n - 1) / (n - 2)`, `Δ⁺_g = -Δ_g` is the
nonnegative Laplacian and `Scal_g` is the scalar curvature. -/
def conformalLaplacian (u : M → ℝ) (x : M) : ℝ :=
  conformalCoefficient (finrank ℝ E) * -laplaceBeltrami I u x +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x

/-- Unfolding lemma for `TauCeti.Yamabe.conformalLaplacian`. -/
theorem conformalLaplacian_def (u : M → ℝ) (x : M) :
    conformalLaplacian I u x =
      conformalCoefficient (finrank ℝ E) * -laplaceBeltrami I u x +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x :=
  (rfl)

/-- The conformal Laplacian of a constant `c` is `c` times the scalar curvature. -/
@[simp]
theorem conformalLaplacian_const (c : ℝ) (x : M) :
    conformalLaplacian I (fun _ ↦ c) x =
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * c := by
  simp [conformalLaplacian_def]

/-- The conformal Laplacian of the zero function vanishes. -/
@[simp]
theorem conformalLaplacian_zero (x : M) : conformalLaplacian I (0 : M → ℝ) x = 0 := by
  simp [conformalLaplacian_def]

/-- The conformal Laplacian is additive on `C²` functions. -/
theorem conformalLaplacian_add {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (x : M) :
    conformalLaplacian I (u + v) x = conformalLaplacian I u x + conformalLaplacian I v x := by
  simp only [conformalLaplacian_def, laplaceBeltrami_add I hu hv x, Pi.add_apply]
  ring

/-- The conformal Laplacian commutes with multiplication by a real constant on `C²` functions. -/
theorem conformalLaplacian_smul (c : ℝ) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (x : M) :
    conformalLaplacian I (c • u) x = c * conformalLaplacian I u x := by
  simp only [conformalLaplacian_def, laplaceBeltrami_smul I c hu x, Pi.smul_apply, smul_eq_mul]
  ring

variable {I} in
/-- The conformal Laplacian of a `C^(k + 2)` function is `C^k`. -/
theorem contMDiff_conformalLaplacian {k : ℕ∞ω} (hk : k ≤ ∞) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) (k + 2) u) :
    ContMDiff I 𝓘(ℝ) k (conformalLaplacian I u) := by
  have hk₂ : k + 2 ≤ ∞ := by
    lift k to ℕ∞ using ne_top_of_le_ne_top (by simp) hk
    exact WithTop.coe_le_coe.2 le_top
  have hk₁ : k + 1 ≤ ∞ := le_trans (by gcongr; norm_num) hk₂
  have hΔ := contMDiff_laplaceBeltrami (I := I) (M := M) hk₂ hk₁ hu
  have hScal := ((CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature).of_le hk
  have hu' := hu.of_le (le_add_of_nonneg_right (by norm_num))
  exact (contMDiff_const.mul hΔ.neg).add (hScal.mul hu')

end Manifold

section Euclidean

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **The conformal Laplacian of Euclidean space.** Euclidean space is flat, so its conformal
Laplacian is `L u = aₙ (-Δ u)`, for Mathlib's Laplacian `Δ`, at every point where the gradient
of `u` is differentiable. -/
theorem conformalLaplacian_eq_conformalCoefficient_mul_neg_laplacian {u : F → ℝ} {x : F}
    (hu : DifferentiableAt ℝ (∇ u) x) :
    conformalLaplacian (modelWithCornersSelf ℝ F) u x =
      conformalCoefficient (finrank ℝ F) * -Δ u x := by
  rw [conformalLaplacian_def, laplaceBeltrami_eq_laplacian hu,
    scalarCurvature_leviCivitaConnection_model_space, zero_mul, add_zero]

/-- **The bubbles solve the Yamabe equation of the sphere.** In dimension `n ≠ 2`, every bubble
`U = U_{t,b}` of positive scale satisfies `L U = n (n - 1) U ^ (pₙ - 1)` for the conformal
Laplacian `L` of Euclidean space. -/
theorem conformalLaplacian_bubble (hn : finrank ℝ F ≠ 2) {t : ℝ} (ht : 0 < t) (b x : F) :
    conformalLaplacian (modelWithCornersSelf ℝ F) (bubble t b) x =
      (finrank ℝ F : ℝ) * (finrank ℝ F - 1) *
        bubble t b x ^ (criticalExponent (finrank ℝ F) - 1) := by
  have hgrad : DifferentiableAt ℝ (∇ (bubble t b)) x :=
    (((contDiff_bubble ht.ne' b (m := 2)).gradient_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) x
  rw [conformalLaplacian_eq_conformalCoefficient_mul_neg_laplacian hgrad,
    conformalCoefficient_mul_neg_laplacian_bubble hn ht]

end Euclidean

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **Scaling of the conformal Laplacian.** Multiplying a smooth metric `g` by a positive
constant `c` multiplies its conformal Laplacian by `c⁻¹` on `C²` functions:
`L_{c g} u = c⁻¹ L_g u`. -/
theorem conformalLaplacian_rescale_const
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) {c : ℝ} (hc : 0 < c)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).toRiemannianMetric⟩;
      conformalLaplacian I u x) =
    c⁻¹ * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      conformalLaplacian I u x) := by
  simp only [conformalLaplacian_def]
  rw [g.laplaceBeltrami_rescale_const (by simp) hc hu x,
    ← (g.rescale (fun _ ↦ c) contMDiff_const fun _ ↦ hc).scalarCurvature_def x,
    ← g.scalarCurvature_def x, g.scalarCurvature_rescale_const hc x]
  ring

end Rescale

section ConformalChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {n : ℕ∞ω}

/-- **The Laplacian of a Yamabe metric.** In real dimension `N ≠ 2`, let `u` be a positive `C²`
function and `ĝ = u ^ (4 / (N - 2)) g`. Then the Laplace–Beltrami operator of `ĝ` on a `C²`
function `v` is `Δ_ĝ v = u ^ (-(N + 2) / (N - 2)) (Δ_g (u v) - v Δ_g u)`. This is the
second-order part of the conformal covariance `L_ĝ v = u ^ (-(N + 2) / (N - 2)) L_g (u v)` of
the conformal Laplacian. -/
theorem laplaceBeltrami_rescale_rpow_four_div_finrank_sub_two (hN : finrank ℝ E ≠ 2)
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) n fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {v : M → ℝ} (hv : ContMDiff I 𝓘(ℝ) 2 v) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale _ hf fun x ↦ Real.rpow_pos_of_pos (hu_pos x) _).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      laplaceBeltrami I v x) =
    u x ^ (-((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2)) *
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
          IsContMDiffRiemannianBundle.of_le hn;
        laplaceBeltrami I (u * v) x - v x * laplaceBeltrami I u x) := by
  rw [g.laplaceBeltrami_rescale_rpow hn hu_pos (hu.mdifferentiableAt (by simp)) hv]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  have hN' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hN)
  have hux := hu_pos x
  have hexp : -((finrank ℝ E : ℝ) + 2) / ((finrank ℝ E : ℝ) - 2) =
      -(4 / ((finrank ℝ E : ℝ) - 2)) - 1 := by
    field_simp
    ring
  rw [laplaceBeltrami_mul I hu hv x, hexp, Real.rpow_sub_one hux.ne']
  field_simp
  ring

end ConformalChange

end TauCeti.Yamabe
