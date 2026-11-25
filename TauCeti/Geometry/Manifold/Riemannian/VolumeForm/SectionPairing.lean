/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure
import TauCeti.Topology.VectorBundle.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# The `L²` pairing of sections of a metric vector bundle

For a real vector bundle with continuous metric `h` over a Riemannian manifold, `h.l2Pairing I ξ η`
is the Bochner integral of `h.inner x (ξ x) (η x)` against `TauCeti.riemannianVolume`.
It applies to integrable sections with noncompact support as well as compactly supported sections.
The base carries its Borel measurable structure and is Lindelöf, as required by the canonical
Riemannian volume measure; its Riemannian metric is continuous. Boundary models are allowed.

The pairing is symmetric and homogeneous. Additivity requires integrability of the two scalar
integrands. The diagonal is nonnegative and vanishes exactly for almost-everywhere zero sections
when its integrand is integrable. For continuous sections this is equivalent to pointwise zero,
because Riemannian volume has full support. Continuous sections with either factor compactly
supported have integrable scalar pairing.

On an oriented manifold, for continuous compactly supported scalar pairing, this equals the
integral of `h(ξ, η) vol` through `TauCeti.integralTopForm`. The Riemannian measure is independent
of the orientation, so `l2Pairing` needs no orientation parameter. On a surface with a compatible
metric, the positive volume form is the area form `dA(u, v) = g(j u, v)` by
`TauCeti.SmoothAlmostComplexStructure.riemannianVolumeForm_apply_eq_inner`. For a Hermitian
bundle, `h` is the real part of the Hermitian product, giving the pairing
`∫_Σ Re⟨ξ, η⟩ dA` used to define the formal adjoint in McDuff–Salamon Lemma C.1.9.

## Main declarations

* `Bundle.ContinuousRiemannianMetric.l2Pairing`: the measure integral of the scalar pairing.
* `Bundle.ContinuousRiemannianMetric.l2Pairing_add_left` and the right-hand and subtraction
  versions: bilinearity under integrability.
* `Bundle.ContinuousRiemannianMetric.l2Pairing_self_eq_zero_iff_ae` and
  `Bundle.ContinuousRiemannianMetric.l2Pairing_self_eq_zero_iff`: definiteness almost everywhere
  and for continuous sections.
* `Bundle.ContinuousRiemannianMetric.integrable_inner_of_isCompact_closure`: integrability for
  continuous sections with either factor compactly supported.
* `Bundle.ContinuousRiemannianMetric.l2Pairing_eq_integralTopForm`: agreement with the oriented
  top-form integral on continuous compactly supported scalar pairings.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 2.44.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold

namespace Bundle.ContinuousRiemannianMetric

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (I) in
/-- The `L²` pairing of bundle sections, integrating their scalar inner product against the
Riemannian volume measure. As for the Bochner integral, it is zero if the integrand is not
integrable. There is no compact-support requirement. -/
def l2Pairing (h : ContinuousRiemannianMetric F V) (ξ η : ∀ x, V x) : ℝ :=
  ∫ x, h.inner x (ξ x) (η x) ∂riemannianVolume I M

variable (h : ContinuousRiemannianMetric F V)

/-- The defining integral of the `L²` pairing. -/
theorem l2Pairing_def (ξ η : ∀ x, V x) :
    h.l2Pairing I ξ η = ∫ x, h.inner x (ξ x) (η x) ∂riemannianVolume I M :=
  (rfl)

/-- The `L²` pairing is symmetric. -/
theorem l2Pairing_comm (ξ η : ∀ x, V x) :
    h.l2Pairing I ξ η = h.l2Pairing I η ξ := by
  simp only [l2Pairing, h.symm]

/-- The pairing with a zero first section vanishes. -/
@[simp]
theorem l2Pairing_zero_left (η : ∀ x, V x) : h.l2Pairing I 0 η = 0 := by
  simp [l2Pairing]

/-- The pairing with a zero second section vanishes. -/
@[simp]
theorem l2Pairing_zero_right (ξ : ∀ x, V x) : h.l2Pairing I ξ 0 = 0 := by
  simp [l2Pairing]

/-- The pairing is homogeneous in its first argument. -/
theorem l2Pairing_smul_left (c : ℝ) (ξ η : ∀ x, V x) :
    h.l2Pairing I (c • ξ) η = c * h.l2Pairing I ξ η := by
  simp only [l2Pairing, Pi.smul_apply, map_smul, smul_apply, smul_eq_mul, integral_const_mul]

/-- The pairing is homogeneous in its second argument. -/
theorem l2Pairing_smul_right (c : ℝ) (ξ η : ∀ x, V x) :
    h.l2Pairing I ξ (c • η) = c * h.l2Pairing I ξ η := by
  rw [l2Pairing_comm, l2Pairing_smul_left, l2Pairing_comm]

/-- Negating the first section negates the pairing. -/
@[simp]
theorem l2Pairing_neg_left (ξ η : ∀ x, V x) :
    h.l2Pairing I (-ξ) η = -h.l2Pairing I ξ η := by
  rw [← neg_one_smul ℝ ξ, l2Pairing_smul_left, neg_one_mul]

/-- Negating the second section negates the pairing. -/
@[simp]
theorem l2Pairing_neg_right (ξ η : ∀ x, V x) :
    h.l2Pairing I ξ (-η) = -h.l2Pairing I ξ η := by
  rw [l2Pairing_comm, l2Pairing_neg_left, l2Pairing_comm]

/-- Additivity in the first argument when the scalar pairings are integrable. -/
theorem l2Pairing_add_left {ξ₁ ξ₂ η : ∀ x, V x}
    (h₁ : Integrable (fun x ↦ h.inner x (ξ₁ x) (η x)) (riemannianVolume I M))
    (h₂ : Integrable (fun x ↦ h.inner x (ξ₂ x) (η x)) (riemannianVolume I M)) :
    h.l2Pairing I (ξ₁ + ξ₂) η =
      h.l2Pairing I ξ₁ η + h.l2Pairing I ξ₂ η := by
  simpa only [l2Pairing, Pi.add_apply, map_add, add_apply] using integral_add h₁ h₂

/-- Additivity in the second argument when the scalar pairings are integrable. -/
theorem l2Pairing_add_right {ξ η₁ η₂ : ∀ x, V x}
    (h₁ : Integrable (fun x ↦ h.inner x (ξ x) (η₁ x)) (riemannianVolume I M))
    (h₂ : Integrable (fun x ↦ h.inner x (ξ x) (η₂ x)) (riemannianVolume I M)) :
    h.l2Pairing I ξ (η₁ + η₂) =
      h.l2Pairing I ξ η₁ + h.l2Pairing I ξ η₂ := by
  simpa only [l2Pairing, Pi.add_apply, map_add] using integral_add h₁ h₂

/-- Subtractivity in the first argument when the scalar pairings are integrable. -/
theorem l2Pairing_sub_left {ξ₁ ξ₂ η : ∀ x, V x}
    (h₁ : Integrable (fun x ↦ h.inner x (ξ₁ x) (η x)) (riemannianVolume I M))
    (h₂ : Integrable (fun x ↦ h.inner x (ξ₂ x) (η x)) (riemannianVolume I M)) :
    h.l2Pairing I (ξ₁ - ξ₂) η =
      h.l2Pairing I ξ₁ η - h.l2Pairing I ξ₂ η := by
  simpa only [l2Pairing, Pi.sub_apply, map_sub, sub_apply] using integral_sub h₁ h₂

/-- Subtractivity in the second argument when the scalar pairings are integrable. -/
theorem l2Pairing_sub_right {ξ η₁ η₂ : ∀ x, V x}
    (h₁ : Integrable (fun x ↦ h.inner x (ξ x) (η₁ x)) (riemannianVolume I M))
    (h₂ : Integrable (fun x ↦ h.inner x (ξ x) (η₂ x)) (riemannianVolume I M)) :
    h.l2Pairing I ξ (η₁ - η₂) =
      h.l2Pairing I ξ η₁ - h.l2Pairing I ξ η₂ := by
  simpa only [l2Pairing, Pi.sub_apply, map_sub] using integral_sub h₁ h₂

/-- The diagonal pairing is nonnegative in every dimension. -/
theorem l2Pairing_self_nonneg (ξ : ∀ x, V x) : 0 ≤ h.l2Pairing I ξ ξ :=
  integral_nonneg fun x ↦ h.inner_self_nonneg x (ξ x)

/-- An integrable diagonal pairing vanishes exactly for almost-everywhere zero sections. -/
theorem l2Pairing_self_eq_zero_iff_ae {ξ : ∀ x, V x}
    (hi : Integrable (fun x ↦ h.inner x (ξ x) (ξ x)) (riemannianVolume I M)) :
    h.l2Pairing I ξ ξ = 0 ↔ ∀ᵐ x ∂riemannianVolume I M, ξ x = 0 := by
  rw [l2Pairing, integral_eq_zero_iff_of_nonneg (fun x ↦ h.inner_self_nonneg x (ξ x)) hi]
  refine Filter.eventually_congr (Filter.Eventually.of_forall fun x ↦ ?_)
  refine ⟨fun hz ↦ ?_, fun hz ↦ by simp [hz]⟩
  by_contra hx
  exact (h.pos x _ hx).ne' hz

/-- For a continuous section with integrable squared norm, the diagonal pairing vanishes exactly
when the section is zero. No compact-support or positive-dimension hypothesis is needed. -/
theorem l2Pairing_self_eq_zero_iff {ξ : ∀ x, V x}
    (hξ : Continuous fun x ↦ TotalSpace.mk' F x (ξ x))
    (hi : Integrable (fun x ↦ h.inner x (ξ x) (ξ x)) (riemannianVolume I M)) :
    h.l2Pairing I ξ ξ = 0 ↔ ξ = 0 := by
  refine ⟨fun h0 ↦ funext fun x ↦ ?_, fun h0 ↦ by simp [h0]⟩
  by_contra hx
  exact (integral_pos_of_integrable_nonneg_ne_zero (h.continuous_inner hξ hξ) hi
    (fun y ↦ h.inner_self_nonneg y (ξ y)) (h.pos x _ hx).ne').ne' h0

/-- Continuous sections have integrable scalar pairing when either factor is compactly
supported. -/
theorem integrable_inner_of_isCompact_closure {ξ η : ∀ x, V x}
    (hξ : Continuous fun x ↦ TotalSpace.mk' F x (ξ x))
    (hη : Continuous fun x ↦ TotalSpace.mk' F x (η x))
    (hc : IsCompact (closure {x | ξ x ≠ 0}) ∨ IsCompact (closure {x | η x ≠ 0})) :
    Integrable (fun x ↦ h.inner x (ξ x) (η x)) (riemannianVolume I M) :=
  (h.continuous_inner hξ hη).integrable_of_hasCompactSupport (h.hasCompactSupport_inner hc)

/-- On continuous sections with compactly supported scalar pairing, the measure integral agrees
with integration of the top form `h(ξ, η) vol` for any orientation. -/
theorem l2Pairing_eq_integralTopForm {m : ℕ} (o : Manifold.Orientation I M (Fin m))
    {ξ η : ∀ x, V x} (hξ : Continuous fun x ↦ TotalSpace.mk' F x (ξ x))
    (hη : Continuous fun x ↦ TotalSpace.mk' F x (η x))
    (hc : HasCompactSupport (fun x ↦ h.inner x (ξ x) (η x))) :
    h.l2Pairing I ξ η =
      integralTopForm o (fun x ↦ h.inner x (ξ x) (η x) • riemannianVolumeForm o x) :=
  (integralTopForm_smul_riemannianVolumeForm o (h.continuous_inner hξ hη) hc).symm

end Bundle.ContinuousRiemannianMetric
