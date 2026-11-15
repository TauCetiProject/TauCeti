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
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Averaging differential forms over a compact group action

Let a group `G` act on a manifold `M` and let `μ` be a measure on `G`. The average of a
differential form `φ` on `M` is the form `x ↦ ∫ ((a •)^* φ)_x dμ(a)`, the fibrewise integral of the
pullbacks of `φ` by the action maps (`TauCeti.averageForm`). It is linear in `φ`
(`TauCeti.averageForm_smul`, `TauCeti.averageForm_add`, …). When `G` is compact, `μ` is finite, `φ`
is continuous and the action is jointly `C¹`, it is evaluated on tangent vectors by

`(averageForm μ φ)_x (v₁, …, vₖ) = ∫ φ_{a • x}(d(a •)_x v₁, …, d(a •)_x vₖ) dμ(a)`

(`TauCeti.averageForm_apply`). For a compact Lie group, possibly disconnected, acting smoothly on
a boundaryless manifold, and its normalized Haar measure `TauCeti.haarProb`, this is the classical
averaging of tensors which produces invariant forms.

* Regularity: if the action is jointly `C^(n+1)` and `φ` is `C^n`, the pullbacks form a jointly
  `C^n` family (`TauCeti.contMDiff_mpullback_smul_form`), so for a compact group, a finite measure
  and a boundaryless manifold the average is `C^n` (`TauCeti.IsSmoothForm.averageForm`).
* Invariance: for a right-invariant measure and an action by differentiable maps, every action
  map preserves the average (`TauCeti.mpullback_smul_averageForm`); a probability measure fixes
  invariant forms (`TauCeti.averageForm_eq_self`), so these are exactly the fixed points of
  averaging (`TauCeti.averageForm_eq_self_iff`) and averaging is idempotent.
* Naturality: averaging commutes with pullback along differentiable equivariant maps
  (`TauCeti.mpullback_averageForm`).
* Exterior derivative: for a compact group acting jointly `C²` on a boundaryless `C²` manifold
  and a finite measure, averaging commutes with `d` (`TauCeti.mextDeriv_averageForm`), so the
  average of a closed form is closed.
* Vanishing along invariant subsets: a form vanishing at every point of an invariant subset has
  an average vanishing there (`TauCeti.averageForm_apply_eq_zero`), and if in addition its
  coordinate expressions have zero derivative at these points, so do those of the average
  (`TauCeti.hasFDerivAt_inChartAt_averageForm_zero`, under the hypotheses of the previous item).
  Thus averaging preserves vanishing of the value and of the first jet along an invariant
  submanifold.

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

variable {E H M E' H' M' EG HG G F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
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

/-- The average of the zero form is zero. -/
@[simp]
theorem averageForm_zero : averageForm μ (0 : RoughForm I M F k) = 0 := by
  simp only [averageForm_def, mpullback_zero, parametricIntegralForm_zero]

/-- Averaging commutes with scalar multiplication. -/
@[simp]
theorem averageForm_smul (c : ℝ) (φ : RoughForm I M F k) :
    averageForm μ (c • φ) = c • averageForm μ φ := by
  simp only [averageForm_def, mpullback_smul, parametricIntegralForm_smul]

/-- Averaging commutes with negation. -/
@[simp]
theorem averageForm_neg (φ : RoughForm I M F k) : averageForm μ (-φ) = -averageForm μ φ := by
  rw [← neg_one_smul ℝ φ, averageForm_smul, neg_one_smul]

/-- **Averaging preserves vanishing on invariant sets.** If a form vanishes at every point of a
subset `s` preserved by the action, so does its average. -/
theorem averageForm_apply_eq_zero {φ : RoughForm I M F k} {s : Set M}
    (hs : ∀ a : G, ∀ x ∈ s, a • x ∈ s) (hφ : ∀ x ∈ s, φ x = 0) {x : M} (hx : x ∈ s) :
    averageForm μ φ x = 0 :=
  parametricIntegralForm_apply_eq_zero fun a ↦ mpullback_apply_eq_zero (hφ _ (hs a x hx))

/-- **Averaging fixes invariant forms.** The average over a probability measure of a form
preserved by every action map is the form itself. -/
theorem averageForm_eq_self [CompleteSpace F] [IsProbabilityMeasure μ] {φ : RoughForm I M F k}
    (hφ : ∀ a : G, mpullback I I (a • ·) φ = φ) : averageForm μ φ = φ := by
  simp only [averageForm_def, hφ, parametricIntegralForm_const, probReal_univ, one_smul]

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
  [IsFiniteMeasure μ]

include J

/-- For a compact group acting jointly `C¹` and a finite measure, the pullbacks of a continuous
form at a point are integrable. -/
theorem integrable_mpullback_smul [ContMDiffSMul J I 1 G M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I 0 φ) (x : M) :
    Integrable (fun a : G ↦ @id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I (a • ·) φ x)) μ :=
  integrable_family_apply (contMDiff_mpullback_smul_form J (n := 1) hφ (by simp)) x

/-- Averaging is additive on continuous forms, for a compact group acting jointly `C¹` and a
finite measure. -/
theorem averageForm_add [ContMDiffSMul J I 1 G M] {φ ψ : RoughForm I M F k}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    averageForm μ (φ + ψ) = averageForm μ φ + averageForm μ ψ := by
  simp only [averageForm_def, mpullback_add]
  exact parametricIntegralForm_add (integrable_mpullback_smul J hφ)
    (integrable_mpullback_smul J hψ)

/-- Averaging is subtractive on continuous forms, for a compact group acting jointly `C¹` and a
finite measure. -/
theorem averageForm_sub [ContMDiffSMul J I 1 G M] {φ ψ : RoughForm I M F k}
    (hφ : IsSmoothForm I 0 φ) (hψ : IsSmoothForm I 0 ψ) :
    averageForm μ (φ - ψ) = averageForm μ φ - averageForm μ ψ := by
  simp only [averageForm_def, mpullback_sub]
  exact parametricIntegralForm_sub (integrable_mpullback_smul J hφ)
    (integrable_mpullback_smul J hψ)

variable [CompleteSpace F]

/-- The average of a continuous form under a jointly `C¹` action of a compact group and a finite
measure, evaluated on tangent vectors, is the integral of the values of the pulled-back forms. -/
theorem averageForm_apply [ContMDiffSMul J I 1 G M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I 0 φ) (x : M) (v : Fin k → TangentSpace I x) :
    averageForm μ φ x v = ∫ a, φ (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) ∂μ :=
  (parametricIntegralForm_apply (integrable_mpullback_smul J hφ x) v).trans
    (by simp only [mpullback_apply])

/-- **Averages of smooth forms are smooth.** For a compact Hausdorff group acting jointly
`C^(n+1)` on a boundaryless manifold and a finite measure, the average of a `C^n` form is
`C^n`. -/
theorem IsSmoothForm.averageForm [I.Boundaryless] {n : ℕ∞} [IsManifold I n M] [IsManifold J n G]
    [T2Space G] [ContMDiffSMul J I (n + 1) G M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) : IsSmoothForm I n (averageForm μ φ) :=
  IsSmoothForm.parametricIntegralForm (contMDiff_mpullback_smul_form J (G := G) hφ le_rfl)

/-- **Averaging commutes with the exterior derivative.** For a compact group acting jointly `C²`
on a boundaryless `C²` manifold and a finite measure, the average of the exterior derivative of a
`C¹` form is the exterior derivative of its average. -/
theorem mextDeriv_averageForm [I.Boundaryless] [IsManifold I 2 M]
    [ContMDiffSMul J I 2 G M] {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) :
    mextDeriv (averageForm μ φ) = averageForm μ (mextDeriv φ) := by
  rw [averageForm_def, mextDeriv_parametricIntegralForm
    (contMDiff_mpullback_smul_form J (G := G) (n := 2) hφ (by norm_num)), averageForm_def]
  congr 1
  funext a
  exact (mpullback_mextDeriv (ContMDiffSMul.contMDiff_const_smul (I := J) a)
    ((isSmoothBundleForm_def 1 _).mpr hφ.contMDiff)).symm

/-- **Averaging preserves vanishing first jets on invariant sets.** Let `s` be a subset preserved
by a compact group acting jointly `C²` on a boundaryless `C²` manifold, and let `μ` be finite. If
a `C¹` form vanishes on `s` and its coordinate expression in the chart at each point of `s` has
zero derivative there, then the coordinate expression of its average in the chart at each point
of `s` also has zero derivative there. -/
theorem hasFDerivAt_inChartAt_averageForm_zero [I.Boundaryless]
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
  have h0 (a : G) : fderiv ℝ ((mpullback I I (a • ·) φ).inChartAt x) (extChartAt I x x) = 0 :=
    (RoughForm.hasFDerivAt_inChartAt_mpullback_zero
      ((ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) (n := 2) a).contMDiffAt.of_le
        one_le_two) (hφs _ (hs a x hx)) (hdφs _ (hs a x hx))).fderiv
  simp only [h0, integral_zero] at h
  exact h

/-- **Averaging is natural for equivariant maps.** For a compact group acting jointly `C¹` on `M`
and by differentiable maps on `M'`, and a finite measure, pulling the average of a continuous form
back along a differentiable equivariant map `f : M' → M` is the average of the pullback. -/
theorem mpullback_averageForm [SMul G M'] [ContMDiffSMul J I 1 G M] {f : M' → M}
    (hf : MDifferentiable I' I f) (hd : ∀ a : G, MDifferentiable I' I' (a • · : M' → M'))
    (hfe : ∀ (a : G) (y : M'), f (a • y) = a • f y) {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I 0 φ) :
    mpullback I' I f (averageForm μ φ) = averageForm μ (mpullback I' I f φ) := by
  have hda (a : G) : MDifferentiable I I (a • · : M → M) :=
    (ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) (n := 1) a).mdifferentiable
      one_ne_zero
  rw [averageForm_def, averageForm_def,
    mpullback_parametricIntegralForm fun y ↦ integrable_mpullback_smul J hφ (f y)]
  congr 1
  funext a
  -- Both sides are pullbacks along `(a •) ∘ f = f ∘ (a •)`.
  have hfa : ((a • ·) ∘ f : M' → M) = f ∘ (a • ·) := funext fun y ↦ (hfe a y).symm
  funext y
  rw [← mpullback_comp_at (hf y) (hda a _), hfa, mpullback_comp_at (hd a y) (hf _)]

end SMul

section Invariance

variable [Group G] [MulAction G M] [MeasurableSpace G] [MeasurableMul G] {μ : Measure G}
  [μ.IsMulRightInvariant] {φ : RoughForm I M F k}

/-- **Averages are invariant.** For a right-invariant measure and an action by differentiable
maps, every action map preserves the average of a form. -/
theorem mpullback_smul_averageForm (hd : ∀ a : G, MDifferentiable I I (a • · : M → M)) (b : G) :
    mpullback I I (b • ·) (averageForm μ φ) = averageForm μ φ := by
  funext x
  -- The differential `D` of `b •` at `x` is invertible, with inverse the differential `D'` of
  -- `b⁻¹ •` at `b • x`. Tangent spaces are read as the model space `E`.
  set D : E →L[ℝ] E := mfderiv I I (b • ·) x
  set D' : E →L[ℝ] E := mfderiv I I (b⁻¹ • ·) (b • x)
  have h₁ : D'.comp D = .id ℝ E := by
    have h := mfderiv_comp x (hd b⁻¹ (b • x)) (hd b x)
    rw [show ((b⁻¹ • ·) ∘ (b • ·) : M → M) = id from funext (inv_smul_smul b), mfderiv_id] at h
    exact h.symm
  have h₂ : D.comp D' = .id ℝ E := by
    have h := mfderiv_comp (b • x) (hd b (b⁻¹ • b • x)) (hd b⁻¹ (b • x))
    rw [show ((b • ·) ∘ (b⁻¹ • ·) : M → M) = id from funext (smul_inv_smul b), mfderiv_id] at h
    have hD : (mfderiv I I (b • ·) (b⁻¹ • b • x) : E →L[ℝ] E) = D := by rw [inv_smul_smul]
    rw [← hD]
    exact h.symm
  -- Precomposition with `D` is a continuous linear equivalence, so it commutes with the integral.
  let L := (ContinuousLinearEquiv.equivOfInverse' D' D h₁ h₂).continuousAlternatingMapCongrLeft
    (ι := Fin k) (F := F)
  -- Pulling back by `b` turns the integrand at `a` into the integrand at `a * b`.
  have hcomp (a : G) : L (@id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I (a • ·) φ (b • x))) =
      @id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I ((a * b) • ·) φ x) := by
    have hab : ((a * b) • · : M → M) = (a • ·) ∘ (b • ·) := funext fun y ↦ mul_smul a b y
    rw [hab, mpullback_comp_at (hd b x) (hd a (b • x))]
    exact (mpullback_apply_eq_compContinuousLinearMapCLM _ _ x).symm
  calc @id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I (b • ·) (averageForm μ φ) x)
      = L (∫ a, @id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I (a • ·) φ (b • x)) ∂μ) := by
        rw [mpullback_apply_eq_compContinuousLinearMapCLM, averageForm_def,
          parametricIntegralForm_def]
        rfl
    _ = ∫ a, @id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I ((a * b) • ·) φ x) ∂μ := by
        rw [← L.integral_comp_comm]
        exact integral_congr_ae (Eventually.of_forall hcomp)
    _ = @id (E [⋀^Fin k]→L[ℝ] F) (averageForm μ φ x) := by
        rw [averageForm_def, parametricIntegralForm_def]
        exact integral_mul_right_eq_self (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F)
          (mpullback I I (a • ·) φ x)) b

variable [IsProbabilityMeasure μ] [CompleteSpace F]

/-- For a right-invariant probability measure and an action by differentiable maps, the forms
fixed by averaging are exactly the invariant ones. -/
theorem averageForm_eq_self_iff (hd : ∀ a : G, MDifferentiable I I (a • · : M → M)) :
    averageForm μ φ = φ ↔ ∀ a : G, mpullback I I (a • ·) φ = φ := by
  refine ⟨fun h a ↦ ?_, averageForm_eq_self⟩
  rw [← h]
  exact mpullback_smul_averageForm hd a

/-- For a right-invariant probability measure and an action by differentiable maps, averaging a
form twice gives the same invariant form. -/
theorem averageForm_idempotent (hd : ∀ a : G, MDifferentiable I I (a • · : M → M)) :
    averageForm μ (averageForm μ φ) = averageForm μ φ :=
  averageForm_eq_self (mpullback_smul_averageForm hd)

end Invariance

end TauCeti
