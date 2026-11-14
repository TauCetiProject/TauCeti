/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Geometry.Manifold.DifferentialForm.ParametricIntegral
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Averaging differential forms over a compact group action

Let a group `G` act on a manifold `M` and let `μ` be a measure on `G`. The average of a
differential form `φ` on `M` is the form

`(averageForm μ φ)_x (v₁, …, vₖ) = ∫ φ_{a • x}(d(a •)_x v₁, …, d(a •)_x vₖ) dμ(a)`,

that is, the integral `∫ (a •)^* φ dμ(a)` of the pullbacks of `φ` by the action maps
(`TauCeti.averageForm`, `TauCeti.averageForm_apply`). For a compact Lie group, possibly
disconnected, acting smoothly on a boundaryless manifold, and its normalized Haar measure
`TauCeti.haarProb`, this is the classical averaging of tensors which produces invariant forms.

* Regularity: if the action is jointly `C^(n+1)` and `φ` is `C^n`, the pullbacks form a jointly
  `C^n` family (`TauCeti.contMDiff_mpullback_smul_form`), so the average is `C^n`
  (`TauCeti.IsSmoothForm.averageForm`).
* Invariance: for a right-invariant measure every action map preserves the average
  (`TauCeti.mpullback_smul_averageForm`); a probability measure fixes invariant forms
  (`TauCeti.averageForm_eq_self`), so these are exactly the fixed points of averaging
  (`TauCeti.averageForm_eq_self_iff`) and averaging is idempotent.
* Exterior derivative: averaging commutes with `d` (`TauCeti.mextDeriv_averageForm`), so the
  average of a closed form is closed.
* Vanishing along invariant subsets: a form vanishing at every point of an invariant subset has
  an average vanishing there (`TauCeti.averageForm_apply_eq_zero`), and if in addition its
  coordinate expressions have zero derivative at these points, so do those of the average
  (`TauCeti.hasFDerivAt_inChartAt_averageForm_zero`). Thus averaging preserves vanishing of the
  value and of the first jet along an invariant submanifold.

These are the properties of averaging used for the equivariant normal forms of Hamiltonian
actions of compact groups, where symplectic forms and their differences are averaged over a
compact stabilizer. The analogous averaging of Riemannian metrics is
`TauCeti.measureAverageRiemannianMetric`.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI, for averaging tensor fields over compact group actions.
* V. Guillemin and S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press
  (1984), § 22 and § 41, for averaging forms in the equivariant Darboux and normal-form theorems.
-/

public section

noncomputable section

open Bundle Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M EG HG G F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  (J : ModelWithCorners ℝ EG HG)
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

section SMul

variable [SMul G M]

section Defs

variable [MeasurableSpace G] {μ : Measure G}

variable (μ) in
/-- The average `∫ (a •)^* φ dμ(a)` of a form `φ` over the action of a group `G` against a
measure `μ` on `G`. -/
def averageForm (φ : RoughForm I M F k) : RoughForm I M F k :=
  parametricIntegralForm μ fun a : G ↦ mpullback I I (a • ·) φ

theorem averageForm_def (φ : RoughForm I M F k) :
    averageForm μ φ = parametricIntegralForm μ fun a : G ↦ mpullback I I (a • ·) φ :=
  (rfl)

/-- **Averaging preserves vanishing on invariant sets.** If a form vanishes at every point of a
subset `s` preserved by the action, so does its average. -/
theorem averageForm_apply_eq_zero {φ : RoughForm I M F k} {s : Set M}
    (hs : ∀ a : G, ∀ x ∈ s, a • x ∈ s) (hφ : ∀ x ∈ s, φ x = 0) {x : M} (hx : x ∈ s) :
    averageForm μ φ x = 0 := by
  have h (a : G) : mpullback I I (a • ·) φ x = 0 := mpullback_apply_eq_zero (hφ _ (hs a x hx))
  simp only [averageForm_def, parametricIntegralForm_def, h]
  exact integral_zero G (E [⋀^Fin k]→L[ℝ] F)

/-- **Averaging fixes invariant forms.** The average over a probability measure of a form
preserved by every action map is the form itself. -/
theorem averageForm_eq_self [CompleteSpace F] [IsProbabilityMeasure μ] {φ : RoughForm I M F k}
    (hφ : ∀ a : G, mpullback I I (a • ·) φ = φ) : averageForm μ φ = φ := by
  funext x
  simp only [averageForm_def, parametricIntegralForm_def, hφ]
  exact (integral_const (E := E [⋀^Fin k]→L[ℝ] F) _).trans
    (by rw [probReal_univ]; exact one_smul ℝ _)

end Defs

variable [TopologicalSpace G] [ChartedSpace HG G] [IsManifold I 1 M] [IsManifold J 1 G]

/-- **Pullbacks along a smooth action form a smooth family.** If `G` acts jointly `C^n` on `M`
and the form `φ` is `C^m`, with `m + 1 ≤ n`, then the pullbacks `(a •)^* φ` are jointly `C^m` in
`(a, x)`. -/
theorem contMDiff_mpullback_smul_form {m n : WithTop ℕ∞} [ContMDiffSMul J I n G M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I m φ) (hmn : m + 1 ≤ n) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun p : G × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2
        (mpullback I I (p.1 • ·) φ p.2)) := by
  have hsmul : ContMDiff ((J.prod I).prod I) I n
      (Function.uncurry fun (q : G × M) (y : M) ↦ q.1 • y) :=
    (contMDiff_smul (I := J) (I' := I)).comp
      ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)
  exact fun p ↦ ContMDiffAt.mpullback_form_family (hφ.contMDiff _)
    (f := fun q : G × M ↦ (q.1 • ·)) (g := Prod.snd) hsmul.contMDiffAt contMDiffAt_snd hmn

variable [MeasurableSpace G] [OpensMeasurableSpace G] [CompactSpace G] {μ : Measure G}
  [IsFiniteMeasure μ] [CompleteSpace F]

include J

/-- The average of a continuous form under a `C¹` action of a compact group, evaluated on tangent
vectors, is the integral of the values of the pulled-back forms. -/
theorem averageForm_apply [ContMDiffSMul J I 1 G M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I 0 φ) (x : M) (v : Fin k → TangentSpace I x) :
    averageForm μ φ x v = ∫ a, φ (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) ∂μ :=
  (parametricIntegralForm_apply
    (contMDiff_mpullback_smul_form J (G := G) (n := 1) hφ (by simp)) x v).trans
    (by simp only [mpullback_apply])

/-- **Averages of smooth forms are smooth.** For a compact group acting jointly `C^(n+1)` on a
boundaryless manifold, the average of a `C^n` form is `C^n`. -/
theorem IsSmoothForm.averageForm [I.Boundaryless] {n : ℕ∞} [IsManifold I n M] [IsManifold J n G]
    [T2Space G] [ContMDiffSMul J I (n + 1) G M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) : IsSmoothForm I n (averageForm μ φ) :=
  IsSmoothForm.parametricIntegralForm (contMDiff_mpullback_smul_form J (G := G) hφ le_rfl)


/-- **Averaging commutes with the exterior derivative.** For a compact boundaryless group acting
jointly `C²` on a boundaryless `C²` manifold, the average of the exterior derivative of a `C¹`
form is the exterior derivative of its average. -/
theorem mextDeriv_averageForm [I.Boundaryless] [J.Boundaryless] [IsManifold I 2 M]
    [ContMDiffSMul J I 2 G M] {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) :
    mextDeriv (averageForm μ φ) = averageForm μ (mextDeriv φ) := by
  rw [averageForm_def, mextDeriv_parametricIntegralForm
    (contMDiff_mpullback_smul_form J (G := G) (n := 2) hφ (by norm_num)), averageForm_def]
  congr 1
  funext a
  exact (mpullback_mextDeriv (ContMDiffSMul.contMDiff_const_smul (I := J) a)
    ((isSmoothBundleForm_def 1 _).mpr hφ.contMDiff)).symm

/-- **Averaging preserves vanishing first jets on invariant sets.** Let `s` be a subset preserved
by a compact boundaryless group acting jointly `C²` on a boundaryless `C²` manifold. If a `C¹`
form vanishes on `s` and its coordinate expression in the chart at each point of `s` has zero
derivative there, then the coordinate expression of its average in the chart at each point of
`s` also has zero derivative there. -/
theorem hasFDerivAt_inChartAt_averageForm_zero [I.Boundaryless] [J.Boundaryless]
    [IsManifold I 2 M] [ContMDiffSMul J I 2 G M] {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ)
    {s : Set M} (hs : ∀ a : G, ∀ x ∈ s, a • x ∈ s) (hφs : ∀ x ∈ s, φ x = 0)
    (hdφs : ∀ x ∈ s, HasFDerivAt (φ.inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (extChartAt I x x))
    {x : M} (hx : x ∈ s) :
    HasFDerivAt ((averageForm μ φ).inChartAt x) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (extChartAt I x x) := by
  have h := hasFDerivAt_inChartAt_parametricIntegralForm (μ := μ)
    (η := fun a : G ↦ mpullback I I (a • ·) φ)
    (contMDiff_mpullback_smul_form J (G := G) (n := 2) hφ (by norm_num)) x
  -- Each pulled-back form has a vanishing first jet at `x`.
  have h0 (a : G) : fderiv ℝ ((mpullback I I (a • ·) φ).inChartAt x) (extChartAt I x x) = 0 := by
    have hd := hdφs _ (hs a x hx)
    rw [← hasFDerivWithinAt_univ, ← I.range_eq_univ] at hd
    have h1 := hasFDerivWithinAt_inChartAt_mpullback_zero
      (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) (n := 2) a).contMDiffAt
      (hφs _ (hs a x hx)) hd
    rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h1
    exact h1.fderiv
  simp only [h0] at h
  rwa [integral_zero] at h

end SMul

section Invariance

variable [Group G] [MulAction G M] [TopologicalSpace G] [ChartedSpace HG G] [IsManifold I 1 M]
  [IsManifold J 1 G] [MeasurableSpace G] [OpensMeasurableSpace G] [CompactSpace G]
  {μ : Measure G} [IsFiniteMeasure μ] [CompleteSpace F]

variable [ContMDiffSMul J I 1 G M] [MeasurableMul G] [μ.IsMulRightInvariant]
  {φ : RoughForm I M F k}

include J

/-- **Averages are invariant.** For a right-invariant measure on a compact group acting by `C¹`
maps, every action map preserves the average of a continuous form. -/
theorem mpullback_smul_averageForm (hφ : IsSmoothForm I 0 φ) (b : G) :
    mpullback I I (b • ·) (averageForm μ φ) = averageForm μ φ := by
  have hfam := contMDiff_mpullback_smul_form J (G := G) (n := 1) hφ (by simp)
  have hd (a : G) : MDifferentiable I I (a • · : M → M) :=
    (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) (n := 1) a).mdifferentiable
      one_ne_zero
  funext x
  ext v
  -- Pulling back by `b` turns the integrand at `a` into the integrand at `a * b`.
  have hcomp (a : G) : mpullback I I (a • ·) φ (b • x) (fun i ↦ mfderiv I I (b • ·) x (v i)) =
      mpullback I I ((a * b) • ·) φ x v := by
    have hab : ((a * b) • · : M → M) = (a • ·) ∘ (b • ·) := funext fun y ↦ mul_smul a b y
    rw [hab, mpullback_comp_at (hd b x) (hd a (b • x)), mpullback_apply, mpullback_apply,
      mpullback_apply]
  rw [mpullback_apply, averageForm_def, parametricIntegralForm_apply hfam,
    parametricIntegralForm_apply hfam]
  simp only [hcomp]
  exact integral_mul_right_eq_self (fun a ↦ mpullback I I (a • ·) φ x v) b

variable [IsProbabilityMeasure μ]

/-- For a right-invariant probability measure, the continuous forms fixed by averaging are
exactly the invariant ones. -/
theorem averageForm_eq_self_iff (hφ : IsSmoothForm I 0 φ) :
    averageForm μ φ = φ ↔ ∀ a : G, mpullback I I (a • ·) φ = φ := by
  refine ⟨fun h a ↦ ?_, averageForm_eq_self⟩
  rw [← h]
  exact mpullback_smul_averageForm J hφ a

/-- Averaging a continuous form twice over a right-invariant probability measure gives the same
invariant form. -/
theorem averageForm_idempotent (hφ : IsSmoothForm I 0 φ) :
    averageForm μ (averageForm μ φ) = averageForm μ φ :=
  averageForm_eq_self (mpullback_smul_averageForm J hφ)

end Invariance

end TauCeti
