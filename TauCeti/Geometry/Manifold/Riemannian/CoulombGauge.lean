/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.DeRham.Harmonic
import TauCeti.Geometry.Manifold.Riemannian.Poisson.Smooth
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# The global Coulomb gauge for one-forms on a closed Riemannian manifold

On an oriented Riemannian manifold `M` of dimension `m ≥ 1`, write `d*` for the codifferential
(`TauCeti.SmoothForm.codifferential`). This file proves that on a closed connected manifold every
smooth one-form `a` is, uniquely, an exact form plus a coclosed form:

`a = df + b`,   `d*b = 0`,

with `f` smooth and of integral zero. The degree-general facts it rests on, for a `(k + 1)`-form
`a` and a `k`-form `α` in place of `f` on any boundaryless manifold with compactly supported
data, are in `TauCeti.Geometry.Manifold.DeRham.Harmonic`: exact forms are `L²`-orthogonal to
coclosed forms, the coclosed summand of `a = dα + (a - dα)` is unique
(`TauCeti.SmoothForm.mextDerivₗ_eq_of_codifferential_sub_eq_zero`), both summands have `L²` norm
at most that of `a`
(`TauCeti.SmoothForm.integralTopForm_inner_self_eq_add_of_codifferential_sub_eq_zero`), and
`∫_M d*a vol = 0` for a one-form `a`
(`TauCeti.SmoothForm.integralTopForm_codifferential_smul_riemannianVolumeForm_eq_zero`).

* **The codifferential of a one-form has integral zero** against the Riemannian volume measure
  (`TauCeti.SmoothForm.integral_codifferential_eq_zero`).
* **Existence and uniqueness**: on a closed connected manifold, `d*a` is therefore a smooth
  function of integral zero, so the equation `Δ⁺f = d*df = d*a` (where `Δ⁺ = -div grad = -Δ` is
  the nonnegative Laplacian) has a unique smooth solution `f` of integral zero by the smooth
  Poisson solver
  (`TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`),
  yielding both existence (`TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero`) and
  uniqueness (`TauCeti.SmoothForm.existsUnique_codifferential_sub_mextDerivₗ_eq_zero`) of `f` with
  `∫ f = 0` and `d*(a - df) = 0`.

In abelian gauge theory, for a `U(1)` connection `A₀ + a` with `a = i b` imaginary, a gauge
transformation `u = exp (i ξ)` acting on the determinant connection by `A ↦ A - 2 u⁻¹ du` changes
`b` to `b - 2 dξ`. Taking `ξ = f / 2` for the function `f` of `b` above puts the connection in the
**global Coulomb gauge** `d*(A - A₀) = 0`, the gauge condition of the Seiberg–Witten equations,
through a gauge transformation in the identity component, unique up to constant phases.

## Main results

* `TauCeti.SmoothForm.integral_codifferential_eq_zero`: `∫_M d*a = 0` against the Riemannian
  measure.
* `TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero`: every one-form on a closed
  connected manifold is `df` plus a coclosed form, with `f` of integral zero.
* `TauCeti.SmoothForm.existsUnique_codifferential_sub_mextDerivₗ_eq_zero`: the function `f` of
  integral zero is unique.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), Chapter 6 (the Hodge decomposition).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press (1996) (the global Coulomb
  gauge).
-/

public section

noncomputable section

open Bundle MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m l : ℕ} (o : Manifold.Orientation I M (Fin m))

/-! ### Integrals against the Riemannian measure -/

-- The Riemannian volume measure is stated for a continuous metric.
local instance instIsContinuousRiemannianBundleCoulombGauge :
    IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := ∞)

section Measure

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] [MeasurableSpace M]
  [BorelSpace M] (hkl : 0 + 1 + l = m)

/-- **The codifferential of a one-form has integral zero**: on an oriented boundaryless Riemannian
manifold, the function `d*a` of a compactly supported smooth one-form `a` has integral zero
against the Riemannian volume measure. -/
theorem integral_codifferential_eq_zero {a : SmoothForm I M ℝ 1}
    (ha : a ∈ compactlySupportedForms I M 1) :
    ∫ x, (codifferential o hkl a).val x 0 ∂riemannianVolume I M = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  -- `d*a` is compactly supported; evaluate it on the empty tuple.
  have hda : HasCompactSupport (β := E [⋀^Fin 0]→L[ℝ] ℝ) (codifferential o hkl a).val :=
    (mem_compactlySupportedForms I).1 (codifferential_mem_compactlySupportedForms o hkl ha)
  have hsupp : HasCompactSupport fun x ↦ (codifferential o hkl a).val x 0 :=
    hda.comp_left (g := fun T : E [⋀^Fin 0]→L[ℝ] ℝ ↦ T 0) (by simp)
  rw [← integralTopForm_smul_riemannianVolumeForm o
    (contMDiff_apply_zero (codifferential o hkl a)).continuous hsupp]
  exact integralTopForm_codifferential_smul_riemannianVolumeForm_eq_zero o hkl ha

end Measure

/-! ### Existence and uniqueness on a closed connected manifold -/

/-- Evaluating `d*df` on a smooth `0`-form `f` gives `Δ⁺f = -Δf`, where `Δ = div grad` is the
Laplace–Beltrami operator. -/
private theorem codifferential_mextDerivₗ_apply_zero (hkl : 0 + 1 + l = m)
    (f : SmoothForm I M ℝ 0) (x : M) :
    (codifferential o hkl (mextDerivₗ I 0 f)).val x 0 =
      -Manifold.laplaceBeltrami I (fun y ↦ f.val y 0) x := by
  have h := congrArg (fun φ : RoughForm I M ℝ 0 ↦ φ x 0)
    (hodgeLaplacian_eq_ofFunction_neg_laplaceBeltrami o (show 0 + (l + 1) = m by omega) f)
  simpa only [hodgeLaplacian_zero_add_one o (show 0 + (l + 1) = m by omega) hkl,
    RoughForm.ofFunction_apply, Pi.neg_apply] using h

/-- The Coulomb gauge condition `d*(a - df) = 0` is equivalent to the pointwise Poisson equation
`Δ⁺f = -Δf = d*a`. -/
private theorem codifferential_sub_mextDerivₗ_eq_zero_iff (hkl : 0 + 1 + l = m)
    (a : SmoothForm I M ℝ 1) (f : SmoothForm I M ℝ 0) :
    codifferential o hkl (a - mextDerivₗ I 0 f) = 0 ↔
      ∀ x, -Manifold.laplaceBeltrami I (fun y ↦ f.val y 0) x =
        (codifferential o hkl a).val x 0 := by
  rw [map_sub, sub_eq_zero, eq_comm]
  refine ⟨fun h x ↦ ?_, fun h ↦ Subtype.ext (funext fun x ↦ ?_)⟩
  · rw [← codifferential_mextDerivₗ_apply_zero o hkl f x, h]
  · ext v
    rw [Subsingleton.elim v 0, codifferential_mextDerivₗ_apply_zero o hkl f x, h x]

section Closed

variable [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  (hkl : 0 + 1 + l = m)

/-- **Uniqueness and existence of the global Coulomb gauge**: on a closed connected oriented
Riemannian manifold of positive dimension, for every smooth one-form `a` there is a unique smooth
function `f` of integral zero with `d*(a - df) = 0`. The function `f` is the unique mean-zero
solution of `Δ⁺f = d*a` (where `Δ⁺ = -div grad`) from the smooth Poisson equation. -/
theorem existsUnique_codifferential_sub_mextDerivₗ_eq_zero [PreconnectedSpace M]
    (a : SmoothForm I M ℝ 1) :
    ∃! f : SmoothForm I M ℝ 0, ∫ x, f.val x 0 ∂riemannianVolume I M = 0 ∧
      codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨u, ⟨hu, hu0, huΔ⟩, huniq⟩ :=
    Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
      (contMDiff_apply_zero (codifferential o hkl a))
      (integral_codifferential_eq_zero o hkl (by simp [compactlySupportedForms_eq_top]))
  let u₀ : C^∞⟮I, M; ℝ⟯ := ⟨u, hu⟩
  have hu₀ : (fun x ↦ (ofFunction u₀).val x 0) = u := ofFunction_apply_zero u₀
  refine ⟨ofFunction u₀, ⟨?_, ?_⟩, fun g ⟨hg₀, hg⟩ ↦ ?_⟩
  · rw [hu₀]
    exact hu0
  · rw [codifferential_sub_mextDerivₗ_eq_zero_iff, hu₀]
    exact huΔ
  · have hgu : (fun x ↦ g.val x 0) = u :=
      huniq _ ⟨contMDiff_apply_zero g, hg₀,
        (codifferential_sub_mextDerivₗ_eq_zero_iff o hkl a g).1 hg⟩
    refine Subtype.ext (funext fun x ↦ ?_)
    ext v
    rw [Subsingleton.elim v 0, congrFun hu₀ x, congrFun hgu x]

/-- **The global Coulomb gauge for one-forms**: on a closed connected oriented Riemannian manifold
of positive dimension, every smooth one-form `a` is `df` plus a coclosed form, `d*(a - df) = 0`,
for a smooth function `f` of integral zero. -/
theorem exists_codifferential_sub_mextDerivₗ_eq_zero [PreconnectedSpace M]
    (a : SmoothForm I M ℝ 1) :
    ∃ f : SmoothForm I M ℝ 0, ∫ x, f.val x 0 ∂riemannianVolume I M = 0 ∧
      codifferential o hkl (a - mextDerivₗ I 0 f) = 0 :=
  (existsUnique_codifferential_sub_mextDerivₗ_eq_zero o hkl a).exists

end Closed

end TauCeti.SmoothForm
