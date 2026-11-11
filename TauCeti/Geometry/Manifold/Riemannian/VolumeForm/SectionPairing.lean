/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic
import TauCeti.Analysis.InnerProductSpace.Orientation
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity

/-!
# The `L²` pairing of sections of a metric vector bundle

Let `M` be a manifold with a Riemannian metric and an orientation `o`, and let `V → M` be a real
vector bundle with a bundle metric `h`. The `L²` pairing of two sections `ξ` and `η` of `V` is the
integral of their pointwise inner product against the Riemannian volume form,

`⟪ξ, η⟫ = ∫_M h(ξ, η) vol`,

computed by `TauCeti.integralTopForm`. On a surface with an almost complex structure `j` and a
compatible metric, if `o` is the orientation for which every frame `(v, j v)` is positive, the
volume form is the area form `dA(u, v) = g(j u, v)`, by
`TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_eq_inner`; for the opposite
orientation it is `-dA`. For a complex bundle
with a Hermitian metric, `h` is the real part of the Hermitian product, so this is the pairing
`∫_Σ Re⟨ξ, η⟩ dA` against which McDuff–Salamon define the formal adjoint of a real
Cauchy–Riemann operator (Lemma C.1.9).

The pairing is symmetric, additive in each argument for continuous sections when the other one is
compactly supported, homogeneous without any hypothesis, nonnegative on the diagonal, and definite
on continuous compactly supported sections. A section `ξ` is compactly supported when the closure
of `{x | ξ x ≠ 0}` is compact. No boundary condition is involved, and the base may have boundary.

## Main declarations

* `Bundle.ContMDiffRiemannianMetric.l2Pairing`: the pairing `∫_M h(ξ, η) vol`, with defining
  equation `Bundle.ContMDiffRiemannianMetric.l2Pairing_def`.
* `Bundle.ContMDiffRiemannianMetric.l2Pairing_comm`,
  `Bundle.ContMDiffRiemannianMetric.l2Pairing_add_left`,
  `Bundle.ContMDiffRiemannianMetric.l2Pairing_smul_left` and their right-hand versions: it is
  symmetric and bilinear.
* `Bundle.ContMDiffRiemannianMetric.l2Pairing_self_nonneg` and
  `Bundle.ContMDiffRiemannianMetric.l2Pairing_self_eq_zero_iff`: it is positive definite on
  continuous compactly supported sections.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Proposition 16.6 (positivity of integration).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} {m : ℕ}

/-- **The `L²` pairing of sections.** For an orientation `o` of a Riemannian manifold `M` and a
bundle metric `h` on `V`, the pairing `∫_M h(ξ, η) vol` of two sections of `V`, integrating against
the Riemannian volume form. It is zero when the integrand is not integrable. -/
def l2Pairing (h : ContMDiffRiemannianMetric I n F V) (o : Manifold.Orientation I M (Fin m))
    (ξ η : ∀ x, V x) : ℝ :=
  integralTopForm o fun x ↦ h.inner x (ξ x) (η x) • riemannianVolumeForm o x

variable (h : ContMDiffRiemannianMetric I n F V) (o : Manifold.Orientation I M (Fin m))

/-- The `L²` pairing is the integral of the pointwise inner product against the volume form. -/
theorem l2Pairing_def (ξ η : ∀ x, V x) :
    h.l2Pairing o ξ η =
      integralTopForm o fun x ↦ h.inner x (ξ x) (η x) • riemannianVolumeForm o x :=
  (rfl)

/-- The `L²` pairing is symmetric. -/
theorem l2Pairing_comm (ξ η : ∀ x, V x) : h.l2Pairing o ξ η = h.l2Pairing o η ξ := by
  simp only [l2Pairing, h.symm]

/-- The `L²` pairing with the zero section on the left vanishes. -/
@[simp]
theorem l2Pairing_zero_left (η : ∀ x, V x) : h.l2Pairing o 0 η = 0 := by
  rw [l2Pairing, ← integralTopForm_zero o]
  congr 1
  funext x
  simp

/-- The `L²` pairing with the zero section on the right vanishes. -/
@[simp]
theorem l2Pairing_zero_right (ξ : ∀ x, V x) : h.l2Pairing o ξ 0 = 0 := by
  rw [l2Pairing_comm, l2Pairing_zero_left]

/-- The `L²` pairing is homogeneous in its first argument. -/
theorem l2Pairing_smul_left (c : ℝ) (ξ η : ∀ x, V x) :
    h.l2Pairing o (c • ξ) η = c * h.l2Pairing o ξ η := by
  rw [l2Pairing, l2Pairing, ← integralTopForm_smul]
  congr 1
  funext x
  simp [mul_smul]

/-- The `L²` pairing is homogeneous in its second argument. -/
theorem l2Pairing_smul_right (c : ℝ) (ξ η : ∀ x, V x) :
    h.l2Pairing o ξ (c • η) = c * h.l2Pairing o ξ η := by
  rw [l2Pairing_comm, l2Pairing_smul_left, l2Pairing_comm]

/-- The integrand of the pairing vanishes outside the support of the first section. -/
private theorem tsupport_metricInner_smul_riemannianVolumeForm_subset (ξ η : ∀ x, V x) :
    _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ)
        (fun x ↦ h.inner x (ξ x) (η x) • riemannianVolumeForm o x) ⊆
      closure {x | ξ x ≠ 0} :=
  closure_mono fun x hx hξ ↦ hx (by simp [show ξ x = 0 by simpa using hξ] :
    h.inner x (ξ x) (η x) • riemannianVolumeForm o x = 0)

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- The integrand of the pairing of continuous sections is a continuous top form. -/
private theorem isSmoothForm_metricInner_smul_riemannianVolumeForm {ξ η : ∀ x, V x}
    (hξ : Continuous fun x ↦ TotalSpace.mk' F x (ξ x))
    (hη : Continuous fun x ↦ TotalSpace.mk' F x (η x)) :
    IsSmoothForm I 0 fun x ↦ h.inner x (ξ x) (η x) • riemannianVolumeForm o x := by
  have : IsManifold I (0 + 1) M := by rw [zero_add]; infer_instance
  exact (isSmoothForm_riemannianVolumeForm (n := 0) o).fun_smul
    (contMDiff_zero_iff.2 (h.continuous_inner_of_continuous hξ hη))

/-- **Additivity of the `L²` pairing** in its first argument, for continuous sections when the
second section is compactly supported. -/
theorem l2Pairing_add_left {ξ₁ ξ₂ η : ∀ x, V x}
    (hξ₁ : Continuous fun x ↦ TotalSpace.mk' F x (ξ₁ x))
    (hξ₂ : Continuous fun x ↦ TotalSpace.mk' F x (ξ₂ x))
    (hη : Continuous fun x ↦ TotalSpace.mk' F x (η x)) (hc : IsCompact (closure {x | η x ≠ 0})) :
    h.l2Pairing o (ξ₁ + ξ₂) η = h.l2Pairing o ξ₁ η + h.l2Pairing o ξ₂ η := by
  have hcpt (ξ : ∀ x, V x) : IsCompact (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ)
      (fun x ↦ h.inner x (ξ x) (η x) • riemannianVolumeForm o x)) := by
    refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
    simpa only [h.symm] using tsupport_metricInner_smul_riemannianVolumeForm_subset h o η ξ
  rw [l2Pairing, l2Pairing, l2Pairing, ← integralTopForm_add o
    (isSmoothForm_metricInner_smul_riemannianVolumeForm h o hξ₁ hη)
    (isSmoothForm_metricInner_smul_riemannianVolumeForm h o hξ₂ hη) (hcpt ξ₁) (hcpt ξ₂)]
  congr 1
  funext x
  simp [add_smul]

/-- **Additivity of the `L²` pairing** in its second argument, for continuous sections when the
first section is compactly supported. -/
theorem l2Pairing_add_right {ξ η₁ η₂ : ∀ x, V x}
    (hξ : Continuous fun x ↦ TotalSpace.mk' F x (ξ x))
    (hη₁ : Continuous fun x ↦ TotalSpace.mk' F x (η₁ x))
    (hη₂ : Continuous fun x ↦ TotalSpace.mk' F x (η₂ x))
    (hc : IsCompact (closure {x | ξ x ≠ 0})) :
    h.l2Pairing o ξ (η₁ + η₂) = h.l2Pairing o ξ η₁ + h.l2Pairing o ξ η₂ := by
  rw [l2Pairing_comm, l2Pairing_add_left h o hη₁ hη₂ hξ hc, l2Pairing_comm, l2Pairing_comm h o η₂]

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousConstSMul ℝ (V x)]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` pairing of a section with itself is nonnegative. -/
theorem l2Pairing_self_nonneg [NeZero m] (ξ : ∀ x, V x) : 0 ≤ h.l2Pairing o ξ ξ := by
  refine integralTopForm_nonneg o fun x c hc ↦ ?_
  let := o.fact_finrank_tangentSpace x
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, riemannianVolumeForm_apply]
  exact mul_nonneg (h.inner_self_nonneg x (ξ x))
    (Orientation.volumeForm_apply_pos_iff.2 hc).le

/-- **The `L²` pairing is definite**: a continuous compactly supported section `ξ` has
`∫_M h(ξ, ξ) vol = 0` exactly when it vanishes. -/
theorem l2Pairing_self_eq_zero_iff [NeZero m] {ξ : ∀ x, V x}
    (hξ : Continuous fun x ↦ TotalSpace.mk' F x (ξ x)) (hc : IsCompact (closure {x | ξ x ≠ 0})) :
    h.l2Pairing o ξ ξ = 0 ↔ ξ = 0 := by
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · by_contra hne
    obtain ⟨x, hx⟩ : ∃ x, ξ x ≠ 0 := by
      by_contra! h'
      exact hne (funext h')
    -- A positively oriented orthonormal basis at `x`, on which the integrand is `h(ξ, ξ) > 0`.
    let := o.fact_finrank_tangentSpace x
    let b := (o.orientationAt x).finOrthonormalBasis (NeZero.pos m) Fact.out
    have hb : b.toBasis.orientation = o.orientationAt x := by simp [b]
    refine (integralTopForm_pos o (isSmoothForm_metricInner_smul_riemannianVolumeForm h o hξ hξ)
      (hc.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_metricInner_smul_riemannianVolumeForm_subset h o ξ ξ))
      (fun y c hc ↦ ?_) ⟨x, b.toBasis, hb, ?_⟩).ne' h0
    · let := o.fact_finrank_tangentSpace y
      rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, riemannianVolumeForm_apply]
      exact mul_nonneg (h.inner_self_nonneg y (ξ y))
        (Orientation.volumeForm_apply_pos_iff.2 hc).le
    · rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis,
        riemannianVolumeForm_apply_orthonormal o x b hb, mul_one]
      exact h.pos x _ hx
  · subst h0
    exact h.l2Pairing_zero_left o 0

end Bundle.ContMDiffRiemannianMetric
