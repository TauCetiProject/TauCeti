/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.RectangleComparison
public import TauCeti.Analysis.Green.Comparison.ExteriorDerivative
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Operations
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Rectangle
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Interval.Basic

/-!
# Rectangle faces and the actual manifold integral

The rectangle is the product of Mathlib's two interval manifolds. Its four faces are actual
interval maps, with positive increasing orientations on the bottom and right and negative
increasing orientations on the top and left. Their rotated normals point out of the rectangle,
and their outward-first frames have the standard planar orientation.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- A horizontal face, as an actual oriented interval manifold, integrates the `dx`
coefficient. No regularity is required of the unused `dy` coefficient. -/
theorem integralTopForm_horizontal_face {a b : ℝ} [Fact (a < b)] (y : ℝ)
    (P Q : ℂ → ℝ) (hP : IntervalIntegrable (fun t ↦ P ⟨t, y⟩) volume a b) :
    IntegrableTopForm (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ)
      (fun t : Icc a b ↦ (⟨t, y⟩ : ℂ)) (manifoldOneForm P Q)) ∧
      integralTopForm (Manifold.Orientation.interval a b)
        (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ) (fun t : Icc a b ↦ (⟨t, y⟩ : ℂ))
          (manifoldOneForm P Q)) = ∫ t in a..b, P ⟨t, y⟩ := by
  have hd (t : ℝ) : deriv (fun s : ℝ ↦ (⟨s, y⟩ : ℂ)) t = 1 := by
    simpa [Function.comp_def, Complex.equivRealProdCLM_symm_apply, Complex.mk_eq_add_mul_I] using
      (Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))).deriv
  have he (t : ℝ) : manifoldOneForm P Q (⟨t, y⟩ : ℂ)
      (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (⟨t, y⟩ : ℂ)).symm
        (deriv (fun s : ℝ ↦ (⟨s, y⟩ : ℂ)) t)) = P ⟨t, y⟩ := by
    simp [manifoldOneForm_apply, hd, oneForm_apply]
  have hc : ContDiff ℝ 1 (fun t : ℝ ↦ (t, y)) := contDiff_id.prodMk contDiff_const
  have hγ := Complex.equivRealProdCLM.symm.contDiff.comp hc
  have h := integralTopForm_mpullback_curve_Icc (manifoldOneForm P Q)
    (fun t : ℝ ↦ (⟨t, y⟩ : ℂ))
    (by simpa only [Function.comp_def, Complex.equivRealProdCLM_symm_apply,
      Complex.mk_eq_add_mul_I] using hγ.contDiffOn) (by simpa only [he] using hP)
  simpa only [he] using h

/-- A vertical face, as an actual oriented interval manifold, integrates the `dy`
coefficient. No regularity is required of the unused `dx` coefficient. -/
theorem integralTopForm_vertical_face {c d : ℝ} [Fact (c < d)] (x : ℝ)
    (P Q : ℂ → ℝ) (hQ : IntervalIntegrable (fun t ↦ Q ⟨x, t⟩) volume c d) :
    IntegrableTopForm (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ)
      (fun t : Icc c d ↦ (⟨x, t⟩ : ℂ)) (manifoldOneForm P Q)) ∧
      integralTopForm (Manifold.Orientation.interval c d)
        (mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ) (fun t : Icc c d ↦ (⟨x, t⟩ : ℂ))
          (manifoldOneForm P Q)) = ∫ t in c..d, Q ⟨x, t⟩ := by
  have hd (t : ℝ) : deriv (fun s : ℝ ↦ (⟨x, s⟩ : ℂ)) t = Complex.I := by
    simpa [Function.comp_def, Complex.equivRealProdCLM_symm_apply, Complex.mk_eq_add_mul_I] using
      (Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv
  have he (t : ℝ) : manifoldOneForm P Q (⟨x, t⟩ : ℂ)
      (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (⟨x, t⟩ : ℂ)).symm
        (deriv (fun s : ℝ ↦ (⟨x, s⟩ : ℂ)) t)) = Q ⟨x, t⟩ := by
    simp [manifoldOneForm_apply, hd, oneForm_apply]
  have hc : ContDiff ℝ 1 (fun t : ℝ ↦ (x, t)) := contDiff_const.prodMk contDiff_id
  have hγ := Complex.equivRealProdCLM.symm.contDiff.comp hc
  have h := integralTopForm_mpullback_curve_Icc (manifoldOneForm P Q)
    (fun t : ℝ ↦ (⟨x, t⟩ : ℂ))
    (by simpa only [Function.comp_def, Complex.equivRealProdCLM_symm_apply,
      Complex.mk_eq_add_mul_I] using hγ.contDiffOn) (by simpa only [he] using hQ)
  simpa only [he] using h

/-- The four actual face-manifold integrals agree with the counterclockwise finite boundary
chain. The top and left faces carry the negative canonical interval orientation. Continuity
is required only on the rectangle, and all four intrinsic integrability predicates are proved. -/
theorem integralTopForm_rectangle_faces {a b c d : ℝ} [hab : Fact (a < b)]
    [hcd : Fact (c < d)] {P Q : ℂ → ℝ}
    (hP : ContinuousOn P (verticalRegion a b (fun _ ↦ c) (fun _ ↦ d)))
    (hQ : ContinuousOn Q (verticalRegion a b (fun _ ↦ c) (fun _ ↦ d))) :
    let B := mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ)
      (fun t : Icc a b ↦ (⟨t, c⟩ : ℂ)) (manifoldOneForm P Q)
    let R := mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ)
      (fun t : Icc c d ↦ (⟨b, t⟩ : ℂ)) (manifoldOneForm P Q)
    let T := mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ)
      (fun t : Icc a b ↦ (⟨t, d⟩ : ℂ)) (manifoldOneForm P Q)
    let L := mpullback (𝓡∂ 1) 𝓘(ℝ, ℂ)
      (fun t : Icc c d ↦ (⟨a, t⟩ : ℂ)) (manifoldOneForm P Q)
    let C := (Division.rectangleRe a b c d hab.out hcd.out).boundary
    IntegrableTopForm B ∧ IntegrableTopForm R ∧ IntegrableTopForm T ∧ IntegrableTopForm L ∧
      integralTopForm (Manifold.Orientation.interval a b) B +
        integralTopForm (Manifold.Orientation.interval c d) R +
        integralTopForm (-Manifold.Orientation.interval a b) T +
        integralTopForm (-Manifold.Orientation.interval c d) L =
      BoundaryChain.integral Complex.reCLM P C + BoundaryChain.integral Complex.imCLM Q C := by
  have hH (y : ℝ) (hy : y ∈ Icc c d) :
      IntervalIntegrable (fun t ↦ P ⟨t, y⟩) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab.out.le
    have hc : Continuous (fun t : ℝ ↦ (⟨t, y⟩ : ℂ)) := by
      simpa only [Function.comp_def, Complex.equivRealProdCLM_symm_apply,
        Complex.mk_eq_add_mul_I, id_eq] using
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_id.prodMk continuous_const)
    apply hP.comp hc.continuousOn
    intro t ht
    exact mem_verticalRegion.mpr ⟨ht, hy⟩
  have hV (x : ℝ) (hx : x ∈ Icc a b) :
      IntervalIntegrable (fun t ↦ Q ⟨x, t⟩) volume c d := by
    apply ContinuousOn.intervalIntegrable_of_Icc hcd.out.le
    have hc : Continuous (fun t : ℝ ↦ (⟨x, t⟩ : ℂ)) := by
      simpa only [Function.comp_def, Complex.equivRealProdCLM_symm_apply,
        Complex.mk_eq_add_mul_I, id_eq] using
        Complex.equivRealProdCLM.symm.continuous.comp (continuous_const.prodMk continuous_id)
    apply hQ.comp hc.continuousOn
    intro t ht
    exact mem_verticalRegion.mpr ⟨hx, ht⟩
  have hB := integralTopForm_horizontal_face c P Q (hH c ⟨le_rfl, hcd.out.le⟩)
  have hR := integralTopForm_vertical_face b P Q (hV b ⟨hab.out.le, le_rfl⟩)
  have hT := integralTopForm_horizontal_face d P Q (hH d ⟨hcd.out.le, le_rfl⟩)
  have hL := integralTopForm_vertical_face a P Q (hV a ⟨le_rfl, hab.out.le⟩)
  refine ⟨hB.1, hR.1, hT.1, hL.1, ?_⟩
  rw [integralTopForm_neg, integralTopForm_neg, hB.2, hR.2, hT.2, hL.2,
    (integral_rectangle_boundary hab.out hcd.out hP hQ).2.2]
  ring

/-- The actual complex area form on the rectangle manifold integrates against ordinary
coordinate rectangle area, with integrability retained by the comparison. -/
theorem integralTopForm_rectangle_areaForm {a b c d : ℝ}
    [Fact (a < b)] [Fact (c < d)] (f : ℂ → ℝ)
    (hi : IntegrableTopForm (mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
      (fun z ↦ f z • manifoldAreaForm z))) :
    IntegrableOn (fun x : ℝ × ℝ ↦ f ⟨x.1, x.2⟩) (Icc a b ×ˢ Icc c d) ∧
      integralTopForm
          ((Manifold.Orientation.interval a b).prod (Manifold.Orientation.interval c d))
          (mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
            (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
            (fun z ↦ f z • manifoldAreaForm z)) =
        ∫ x in Icc a b ×ˢ Icc c d, f ⟨x.1, x.2⟩ := by
  let L := Complex.equivRealProdCLM.symm
  let η := mpullback 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) L (fun z ↦ f z • manifoldAreaForm z)
  have hι := ((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).comp
    contMDiff_fst).prodMk_space ((contMDiff_subtypeVal_Icc (x := c) (y := d) (n := 1)).comp
      contMDiff_snd)
  have hL : MDifferentiable 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) L :=
    L.differentiable.mdifferentiable
  have hcomp : mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
      (fun z ↦ f z • manifoldAreaForm z) =
        mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ × ℝ)
          (fun x : Icc a b × Icc c d ↦ (x.1.val, x.2.val)) η := by
    exact mpullback_comp (hι.mdifferentiable one_ne_zero) hL _
  have hη (x : ℝ × ℝ) : η x (fun i ↦
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm (![(1, 0), (0, 1)] i)) =
        f ⟨x.1, x.2⟩ := by
    dsimp only [η]
    rw [mpullback_apply, mfderiv_eq_fderiv]
    -- Put the model-space tangent fibers in their canonical normed-space coordinates.
    change (f (L x) • manifoldAreaForm (L x))
      (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (L x)).symm
        (fderiv ℝ L x (![(1, 0), (0, 1)] i))) = _
    rw [L.hasFDerivAt.fderiv, ContinuousAlternatingMap.smul_apply,
      manifoldAreaForm_apply]
    simp only [ContinuousLinearEquiv.apply_symm_apply, smul_eq_mul]
    -- The two canonical tangent equivalences cancel; expose the resulting scalar coefficient.
    change f (L x) * Complex.orientation.volumeFormL
      (fun i : Fin 2 ↦ L (![(1, 0), (0, 1)] i)) = _
    have hv : (fun i : Fin 2 ↦ L (![(1, 0), (0, 1)] i)) = Complex.basisOneI := by
      funext i
      fin_cases i <;> simp [L, Complex.equivRealProdCLM_symm_apply, Complex.coe_basisOneI]
    rw [hv, Complex.coe_basisOneI, Orientation.volumeFormL_apply, complexAreaForm_one_I, mul_one]
    rfl
  rw [hcomp] at hi ⊢
  have h := integralTopForm_mpullback_rectangle η hi
  simpa only [hη] using h

/-- Continuity supplies the genuine intrinsic integrability needed for the rectangle area
comparison, including its corner points. -/
theorem _root_.ContinuousOn.integrableTopForm_rectangle_areaForm {a b c d : ℝ}
    [Fact (a < b)] [Fact (c < d)] {f : ℂ → ℝ}
    (hf : ContinuousOn f (verticalRegion a b (fun _ ↦ c) (fun _ ↦ d))) :
    IntegrableTopForm (mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
      (fun z ↦ f z • manifoldAreaForm z)) := by
  have hι := ((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).comp
    contMDiff_fst).prodMk_space ((contMDiff_subtypeVal_Icc (x := c) (y := d) (n := 1)).comp
      contMDiff_snd)
  have hιC : ContMDiff ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) 1
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ)) := by
    exact Complex.equivRealProdCLM.symm.contDiff.contMDiff.comp hι
  have harea : IsSmoothForm 𝓘(ℝ, ℂ) 0 manifoldAreaForm := by
    apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
    intro z
    rw [manifoldAreaForm_inChartAt]
    exact contDiffWithinAt_const
  have hscalar : Continuous (fun x : Icc a b × Icc c d ↦ f (⟨x.1, x.2⟩ : ℂ)) := by
    apply hf.comp_continuous hιC.continuous
    intro x
    exact mem_verticalRegion.mpr ⟨x.1.property, x.2.property⟩
  have hform := (harea.mpullback hιC).fun_smul (contMDiff_zero_iff.mpr hscalar)
  have he : mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
      (fun z ↦ f z • manifoldAreaForm z) =
    fun x ↦ f (⟨x.1, x.2⟩ : ℂ) • mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ)) manifoldAreaForm x := by
    ext x v
    simp only [mpullback_apply, ContinuousAlternatingMap.smul_apply]
  rw [he]
  exact hform.integrableTopForm (isClosed_tsupport _).isCompact
    (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv)

/-- Green on the actual product interval manifold agrees with the existing finite rectangle
boundary chain. The area integrand is the pullback of the actual manifold exterior derivative;
`integralTopForm_rectangle_faces` identifies the chain with the four outward-oriented faces. -/
theorem integralTopForm_rectangle_mextDeriv {a b c d : ℝ} [hab : Fact (a < b)]
    [hcd : Fact (c < d)] {P Q : ℂ → ℝ}
    (hP : ∀ z ∈ verticalRegion a b (fun _ ↦ c) (fun _ ↦ d), ContDiffAt ℝ 1 P z)
    (hQ : ∀ z ∈ verticalRegion a b (fun _ ↦ c) (fun _ ↦ d), ContDiffAt ℝ 1 Q z) :
    let ω := mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ)) (mextDeriv (manifoldOneForm P Q))
    let C := (Division.rectangleRe a b c d hab.out hcd.out).boundary
    IntegrableTopForm ω ∧
      integralTopForm
          ((Manifold.Orientation.interval a b).prod (Manifold.Orientation.interval c d)) ω =
        BoundaryChain.integral Complex.reCLM P C + BoundaryChain.integral Complex.imCLM Q C := by
  let R := verticalRegion a b (fun _ ↦ c) (fun _ ↦ d)
  have hcurl : ContinuousOn (curl P Q) R := by
    intro z hz
    exact (((ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).continuous.continuousAt.comp
      ((hQ z hz).continuousAt_fderiv one_ne_zero)).sub
      ((ContinuousLinearMap.apply ℝ ℝ Complex.I).continuous.continuousAt.comp
        ((hP z hz).continuousAt_fderiv one_ne_zero))).continuousWithinAt
  have hω : mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
      (mextDeriv (manifoldOneForm P Q)) =
    mpullback ((𝓡∂ 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
      (fun x : Icc a b × Icc c d ↦ (⟨x.1, x.2⟩ : ℂ))
      (fun z ↦ curl P Q z • manifoldAreaForm z) := by
    ext x v
    have hx : (⟨x.1, x.2⟩ : ℂ) ∈ R := mem_verticalRegion.mpr ⟨x.1.property, x.2.property⟩
    rw [mpullback_apply, mpullback_apply,
      DifferentiableAt.mextDeriv_manifoldOneForm_eq_smul_area
        ((hP _ hx).differentiableAt one_ne_zero) ((hQ _ hx).differentiableAt one_ne_zero)]
  dsimp only
  rw [hω]
  have hi := ContinuousOn.integrableTopForm_rectangle_areaForm hcurl
  refine ⟨hi, (integralTopForm_rectangle_areaForm (curl P Q) hi).2.trans ?_⟩
  let L := Complex.equivRealProdCLM.symm
  let f : ℝ × ℝ → ℝ := fun x ↦ Q (L x)
  let g : ℝ × ℝ → ℝ := fun x ↦ -P (L x)
  let f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fun x ↦ (fderiv ℝ Q (L x)).comp L.toContinuousLinearMap
  let g' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fun x ↦ -(fderiv ℝ P (L x)).comp L.toContinuousLinearMap
  have hmem (x : ℝ × ℝ) (hx : x ∈ Icc (a, c) (b, d)) : L x ∈ R := by
    apply mem_verticalRegion.mpr
    exact ⟨⟨hx.1.1, hx.2.1⟩, ⟨hx.1.2, hx.2.2⟩⟩
  have hf (x : ℝ × ℝ) (hx : x ∈ Icc (a, c) (b, d)) : HasFDerivAt f (f' x) x :=
    ((hQ (L x) (hmem x hx)).differentiableAt one_ne_zero).hasFDerivAt.comp x L.hasFDerivAt
  have hg (x : ℝ × ℝ) (hx : x ∈ Icc (a, c) (b, d)) : HasFDerivAt g (g' x) x :=
    (((hP (L x) (hmem x hx)).differentiableAt one_ne_zero).hasFDerivAt.comp x
      L.hasFDerivAt).neg
  have he (x : ℝ × ℝ) : f' x (1, 0) + g' x (0, 1) = curl P Q ⟨x.1, x.2⟩ := by
    simp [f', g', L, ContinuousLinearMap.comp_apply, Complex.equivRealProdCLM_symm_apply,
      Complex.mk_eq_add_mul_I, curl, sub_eq_add_neg]
  have hfg : IntegrableOn (fun x ↦ f' x (1, 0) + g' x (0, 1)) (Icc (a, c) (b, d)) := by
    simpa only [he, Icc_prod_eq] using
      (integralTopForm_rectangle_areaForm (curl P Q) hi).1
  have hsubset : Ioo a b ×ˢ Ioo c d ⊆ Icc (a, c) (b, d) := by
    rw [Icc_prod_eq]
    exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  have hD := integral_rectangle_boundary_eq_divergence f g f' g' (a, c) (b, d)
    hab.out hcd.out ∅ countable_empty
    (fun x hx ↦ ((hQ (L x) (hmem x hx)).continuousAt.comp L.continuousAt).continuousWithinAt)
    (fun x hx ↦ ((hP (L x) (hmem x hx)).continuousAt.comp
      L.continuousAt).neg.continuousWithinAt)
    (fun x hx ↦ hf x (hsubset hx.1)) (fun x hx ↦ hg x (hsubset hx.1)) hfg
  have hL (z : ℂ) : L (z.re, z.im) = z := by
    simp [L, Complex.equivRealProdCLM_symm_apply]
  simpa only [f, g, hL, neg_neg, he, Icc_prod_eq] using hD.2.2.symm

end TauCeti.Green
