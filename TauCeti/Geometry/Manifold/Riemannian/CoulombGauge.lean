/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Codifferential
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DeRham.Harmonic
import TauCeti.Geometry.Manifold.Riemannian.Poisson.Smooth
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
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
* **Existence**: on a closed connected manifold, `d*a` is therefore a smooth function of integral
  zero, so it is `Δf = d*df` for a smooth function `f` of integral zero, by the smooth Poisson
  equation (`TauCeti.Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq`),
  and then `d*(a - df) = 0` (`TauCeti.SmoothForm.exists_codifferential_sub_mextDerivₗ_eq_zero`).
* **Uniqueness**: if `a - df` and `a - dg` are both coclosed, then `df = dg`, so on a connected
  manifold `f - g` is constant, hence zero when `f` and `g` both have integral zero
  (`TauCeti.SmoothForm.existsUnique_codifferential_sub_mextDerivₗ_eq_zero`).

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

section Closed

variable [I.Boundaryless] [CompactSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M]
  (hkl : 0 + 1 + l = m)

/-- **The global Coulomb gauge for one-forms**: on a closed connected oriented Riemannian manifold
of positive dimension, every smooth one-form `a` is `df` plus a coclosed form, `d*(a - df) = 0`,
for a smooth function `f` of integral zero. The function `f` solves `Δf = d*a`, by the smooth
Poisson equation. -/
theorem exists_codifferential_sub_mextDerivₗ_eq_zero [PreconnectedSpace M]
    (a : SmoothForm I M ℝ 1) :
    ∃ f : SmoothForm I M ℝ 0, ∫ x, f.val x 0 ∂riemannianVolume I M = 0 ∧
      codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨u, ⟨hu_smooth, hu₀, hu⟩, _⟩ :=
    Manifold.existsUnique_contMDiff_integral_eq_zero_and_neg_laplaceBeltrami_eq
      (contMDiff_apply_zero (codifferential o hkl a))
      (integral_codifferential_eq_zero o hkl (by simp [compactlySupportedForms_eq_top]))
  let u₀ : C^∞⟮I, M; ℝ⟯ := ⟨u, hu_smooth⟩
  refine ⟨ofFunction u₀, by rwa [ofFunction_apply_zero], ?_⟩
  -- `d*df = Δf = -div grad u = d*a`.
  have hΔ : codifferential o hkl (mextDerivₗ I 0 (ofFunction u₀)) = codifferential o hkl a := by
    rw [← hodgeLaplacian_zero_add_one o (show 0 + (l + 1) = m by omega) hkl]
    apply Subtype.ext
    rw [hodgeLaplacian_eq_ofFunction_neg_laplaceBeltrami, ofFunction_apply_zero,
      RoughForm.eq_ofFunction (codifferential o hkl a).val]
    congr 1
    funext x
    exact hu x
  rw [map_sub, hΔ, sub_self]

/-- **Uniqueness of the global Coulomb gauge**: on a closed connected oriented Riemannian manifold
of positive dimension, for every smooth one-form `a` there is exactly one smooth function `f` of
integral zero with `d*(a - df) = 0`. -/
theorem existsUnique_codifferential_sub_mextDerivₗ_eq_zero [PreconnectedSpace M]
    (a : SmoothForm I M ℝ 1) :
    ∃! f : SmoothForm I M ℝ 0, ∫ x, f.val x 0 ∂riemannianVolume I M = 0 ∧
      codifferential o hkl (a - mextDerivₗ I 0 f) = 0 := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨f, hf₀, hf⟩ := exists_codifferential_sub_mextDerivₗ_eq_zero o hkl a
  refine ⟨f, ⟨hf₀, hf⟩, fun g ⟨hg₀, hg⟩ ↦ ?_⟩
  have hd := mextDerivₗ_eq_of_codifferential_sub_eq_zero o hkl hg hf
    (by simp [compactlySupportedForms_eq_top])
  -- `g - f` is closed, hence constant, and has integral zero.
  obtain ⟨c, hc⟩ := ((mem_closedForms_zero_iff I (g - f)).1 (by
    rw [mem_closedForms_iff_mextDerivₗ_eq_zero, map_sub, hd, sub_self])).exists_eq_const
  have hgf (x : M) : (g - f).val x 0 = c := congrFun hc x
  have hint (φ : SmoothForm I M ℝ 0) : Integrable (fun x ↦ φ.val x 0) (riemannianVolume I M) :=
    (contMDiff_apply_zero φ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h₀ : ∫ x, (g - f).val x 0 ∂riemannianVolume I M = 0 := by
    simp only [Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply]
    rw [integral_sub (hint g) (hint f), hg₀, hf₀, sub_zero]
  rw [← sub_eq_zero]
  refine Subtype.ext (funext fun x ↦ ?_)
  -- The constant `c` vanishes, since `M` has positive volume.
  have hvol : (riemannianVolume I M).real Set.univ ≠ 0 :=
    (ENNReal.toReal_pos (isOpen_univ.measure_pos _ ⟨x, Set.mem_univ x⟩).ne'
      (measure_ne_top _ _)).ne'
  have hc₀ : c = 0 := by
    simpa only [hgf, integral_const, smul_eq_mul, mul_eq_zero, hvol, false_or] using h₀
  ext v
  rw [Subsingleton.elim v 0, hgf, hc₀]
  simp

end Closed

end TauCeti.SmoothForm
