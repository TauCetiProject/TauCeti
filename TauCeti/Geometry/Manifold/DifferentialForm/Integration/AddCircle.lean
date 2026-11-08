/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Parametrization
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.Orientation.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Integration of top forms over circles and two-tori

For a positive real `p`, the quotient map `ℝ → AddCircle p` is injective on every interval
`[a, a + p)` of length `p` and maps it onto the circle, with derivative `1` in the local real lifts
that are the charts of `AddCircle p`. So it is a positively oriented parametrization of the whole
circle for its positive orientation `AddCircle.orientation p`, and the integral of a top form `φ`
over `AddCircle p` is the Lebesgue integral of `t ↦ φ_[t](1)` over one period
(`AddCircle.integralTopForm_eq_setIntegral`). In particular the time form `dt_p`, which sends the
tangent vector `1` to `1`, integrates to the period `p` (`AddCircle.integralTopForm_timeForm`).

The same holds on the torus `AddCircle p × AddCircle q`, oriented as the product of the positive
orientations of its factors. The integral of a two-form `φ` is the Lebesgue integral of
`(s, t) ↦ φ_([s], [t])((1, 0), (0, 1))` over a fundamental rectangle `[a, a + p) × [b, b + q)`
(`AddCircle.integralTopForm_prod_eq_setIntegral`). In particular the area form `ds_p ∧ dt_q`, the
wedge of the time forms of the two factors, integrates to `p q`
(`AddCircle.integralTopForm_wedge_timeForm`).

## Main results

* `AddCircle.integralTopForm_eq_setIntegral`: the integral of a top form over `AddCircle p` is its
  integral over a period.
* `AddCircle.integralTopForm_timeForm`: `∫ dt_p = p`.
* `AddCircle.integralTopForm_prod_eq_setIntegral`: the integral of a two-form over
  `AddCircle p × AddCircle q` is its integral over a fundamental rectangle.
* `AddCircle.integralTopForm_wedge_timeForm`: `∫ ds_p ∧ dt_q = p q`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 16.8 (integration by parametrizations).
-/

public section

noncomputable section

open Set MeasureTheory TauCeti
open scoped Manifold

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

/-- **Integration over a circle.** The integral of an integrable top form `φ` over `AddCircle p`,
with its positive orientation, is the integral over one period `[a, a + p)` of the value of `φ` at
`[t]` on the positive unit tangent vector. -/
theorem integralTopForm_eq_setIntegral {φ : RoughForm 𝓘(ℝ) (AddCircle p) ℝ 1}
    (hφ : IntegrableTopForm φ) (a : ℝ) :
    integralTopForm (AddCircle.orientation p) φ =
      ∫ t in Ico a (a + p), φ t fun _ ↦ (1 : ℝ) := by
  obtain ⟨l, hl⟩ := (AddCircle.orientation p).exists_lift
  have h := integralTopForm_eq_oriented_parametrization l (Module.Basis.singleton (Fin 1) ℝ) φ hφ
    (Q := ((↑) : ℝ → AddCircle p)) (D := Ico a (a + p)) measurableSet_Ico finite_empty
    (by rw [compl_empty, coe_image_Ico_eq])
    (fun _ hs _ ht hst ↦ (coe_eq_coe_iff_of_mem_Ico hs ht).mp hst)
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ ℝ) (fun t _ ↦ hasMFDerivAt_coe p t)
    (fun t _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl, orientationAt_orientation]
      exact Equiv.congr_fun (Orientation.map_refl _) _)
  rw [← hl, h.2, Module.Basis.addHaar_singleton]
  simp only [Module.Basis.singleton_apply]
  -- The tangent vector `1` of `AddCircle p` at `[t]` is the real number `1`.
  rfl

/-- The time form `dt_p` integrates to the period `p` over `AddCircle p`. -/
theorem integralTopForm_timeForm :
    integralTopForm (AddCircle.orientation p) (timeForm p).1 = p := by
  have hc : IsCompact (_root_.tsupport (α := ℝ [⋀^Fin 1]→L[ℝ] ℝ) (timeForm p).1) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  rw [integralTopForm_eq_setIntegral p
    ((timeForm p).isSmoothForm.integrableTopForm hc (Module.Basis.singleton (Fin 1) ℝ)) 0,
    setIntegral_congr_fun (s := Ico (0 : ℝ) (0 + p)) measurableSet_Ico fun t _ ↦
    timeForm_apply p (t : AddCircle p) fun _ ↦ (1 : ℝ)]
  simp [(Fact.out : 0 < p).le]

variable (q : ℝ) [Fact (0 < q)]

/-- **Integration over a two-torus.** The integral of an integrable two-form `φ` over
`AddCircle p × AddCircle q`, oriented as the product of the positive orientations of the two
circles, is the integral over a fundamental rectangle `[a, a + p) × [b, b + q)` of the value of `φ`
at `([s], [t])` on the standard frame `((1, 0), (0, 1))`. -/
theorem integralTopForm_prod_eq_setIntegral
    {φ : RoughForm (𝓘(ℝ).prod 𝓘(ℝ)) (AddCircle p × AddCircle q) ℝ 2} (hφ : IntegrableTopForm φ)
    (a b : ℝ) :
    integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q)) φ =
      ∫ z in Ico a (a + p) ×ˢ Ico b (b + q),
        φ ((z.1 : AddCircle p), (z.2 : AddCircle q)) ![((1 : ℝ), (0 : ℝ)), (0, 1)] := by
  obtain ⟨l, hl⟩ := ((AddCircle.orientation p).prod (AddCircle.orientation q)).exists_lift
  have hd (z : ℝ × ℝ) : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ))
      (Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q)) z
      ((ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)).toContinuousLinearMap.comp
        (NormedSpace.fromTangentSpace z).toContinuousLinearMap) :=
    (hasMFDerivAt_prodMap_coe p q z).congr_mfderiv (ContinuousLinearMap.ext fun _ ↦ rfl)
  have h := integralTopForm_eq_oriented_parametrization l (Module.Basis.finTwoProd ℝ) φ hφ
    (Q := Prod.map ((↑) : ℝ → AddCircle p) ((↑) : ℝ → AddCircle q))
    (D := Ico a (a + p) ×ˢ Ico b (b + q))
    (measurableSet_Ico.prod measurableSet_Ico) finite_empty
    (by rw [compl_empty, prodMap_image_prod, coe_image_Ico_eq, coe_image_Ico_eq, univ_prod_univ])
    (InjOn.prodMap (fun _ hs _ ht hst ↦ (coe_eq_coe_iff_of_mem_Ico hs ht).mp hst)
      fun _ hs _ ht hst ↦ (coe_eq_coe_iff_of_mem_Ico hs ht).mp hst)
    (fun _ ↦ ContinuousLinearEquiv.refl ℝ (ℝ × ℝ)) (fun z _ ↦ hd z)
    (fun z _ ↦ by
      rw [← Manifold.Orientation.orientationAt_mk, hl, orientationAt_orientation_prod_orientation]
      exact Equiv.congr_fun (Orientation.map_refl _) _)
  rw [← hl, h.2, Module.Basis.addHaar_finTwoProd]
  refine setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ico) fun z _ ↦ ?_
  congr 1
  funext i
  -- The tangent spaces of the torus are `ℝ × ℝ`, so the standard frame is `((1, 0), (0, 1))`.
  fin_cases i <;> simp <;> rfl

/-- The area form `ds_p ∧ dt_q`, the wedge of the time forms of the two factors, integrates to
`p q` over `AddCircle p × AddCircle q`. -/
theorem integralTopForm_wedge_timeForm :
    integralTopForm ((AddCircle.orientation p).prod (AddCircle.orientation q))
      (SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (timeForm p))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm q))).1 = p * q := by
  have hval (x : AddCircle p × AddCircle q) :
      SmoothBundleForm.eval₂ (SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (timeForm p))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm q))) x
        ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) = 1 := by
    -- The tangent spaces of the torus are `ℝ × ℝ`, so the frame is stated in the model.
    refine (SmoothForm.eval₂_wedge_one_one _ _ x _ _).trans ?_
    simp only [SmoothForm.coe_mpullback, mpullback_apply, mfderiv_fst, mfderiv_snd,
      timeForm_apply, Matrix.cons_val]
    -- The two projections of the tangent vectors `(1, 0)` and `(0, 1)` are their coordinates.
    exact (by norm_num : (1 : ℝ) * 1 - 0 * 0 = 1)
  rw [integralTopForm_prod_eq_setIntegral p q
    ((SmoothForm.isSmoothForm _).integrableTopForm
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _))
      (Module.Basis.finTwoProd ℝ)) 0 0]
  calc _ = ∫ _ in Ico (0 : ℝ) (0 + p) ×ˢ Ico (0 : ℝ) (0 + q), (1 : ℝ) :=
        setIntegral_congr_fun (measurableSet_Ico.prod measurableSet_Ico) fun _ _ ↦
          (SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (hval _)
    _ = p * q := by
      simp [Measure.volume_eq_prod, (Fact.out : 0 < p).le, (Fact.out : 0 < q).le]

end AddCircle
