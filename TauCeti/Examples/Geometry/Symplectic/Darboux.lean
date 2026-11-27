/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Darboux
public import TauCeti.Geometry.Symplectic.Prod.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Manifold.Plane

/-!
# Examples: Darboux charts in the plane and in `ℝ⁴`

Three explicit two-forms test the statement of Darboux's theorem
(`TauCeti.SmoothTwoForm.exists_darbouxChart_of_nondegenerate_of_isInteriorPoint`): a chart
centred at `x₀`, pulling a constant symplectic form back to the given form, exists around an
interior point `x₀` at which a closed two-form is nondegenerate.

* **The area form.** On the plane `ℝ × ℝ` the area form `dx ∧ dy` is the constant form of the
  standard symplectic form `stdSymplecticForm`, `(u, w) ↦ u₁ w₂ - u₂ w₁`, and the identity is a
  Darboux chart for it at the origin, with `dx ∧ dy` itself as the model form. Its standard model
  has `m = 1`: Darboux's theorem gives a chart into
  `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`
  (`exists_standardDarbouxChart_constSmooth_stdSymplecticForm`).
* **A Darboux chart need not be linear.** The form `eˣ dx ∧ dy` (`expAreaForm`) is closed, being
  of top degree, and the chart `(x, y) ↦ (eˣ - 1, y)` (`expChart`), a diffeomorphism of the plane
  onto the half-plane `u > -1` sending the origin to the origin, pulls `dx ∧ dy` back to it
  (`eval₂_expAreaForm_eq_mvfderiv_expChart`). So `eˣ dx ∧ dy` is symplectic
  (`isSymplectic_expAreaForm`). No linear map pulls a constant form back to `eˣ dx ∧ dy` on any
  neighbourhood of the origin, since pulled back by a linear map a constant form stays constant
  while `eˣ` does not (`not_exists_continuousLinearMap_eventually_eval₂_expAreaForm_eq`): a
  version of Darboux's theorem returning only linear charts would fail here.
* **Nondegeneracy at the point is needed.** On `ℝ⁴`, written `(ℝ × ℝ) × (ℝ × ℝ)` with coordinates
  `((x₁, x₂), (x₃, x₄))`, the form `x₁ dx₁ ∧ dx₂ + dx₃ ∧ dx₄` (`degenerateForm`) is closed: it is
  the pullback of the constant form `dy₁ ∧ dy₂ + dy₃ ∧ dy₄` along
  `((x₁, x₂), (x₃, x₄)) ↦ ((x₁² / 2, x₂), (x₃, x₄))`, since `d (x₁² / 2) = x₁ dx₁`. It is
  nondegenerate exactly off the hyperplane `x₁ = 0`
  (`nondegenerate_bilinFormAt_degenerateForm_iff`), so no Darboux chart exists around the origin
  (`not_exists_darbouxChart_degenerateForm`): a chart pulling back a constant symplectic form
  forces nondegeneracy on its source
  (`TauCeti.SmoothTwoForm.nondegenerate_bilinFormAt_of_darbouxChart`). Closedness alone does not
  suffice, and the pointwise nondegeneracy hypothesis excludes this form.
* **Odd dimensions.** The odd-dimensional space `ℝ × ℝ × ℝ` carries no nondegenerate two-form at
  all (`not_isNondegenerate_prod_prod`), since a symplectic vector space has even
  dimension.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser's argument and Darboux's theorem).
-/

public section

noncomputable section

open Filter Real Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Examples.Darboux

/-! ### The area form of the plane -/

/-- **The identity is a Darboux chart of `dx ∧ dy`.** The identity of the plane, whose source
contains the origin and which fixes it, pulls the area form `dx ∧ dy` back to its constant smooth
form. -/
theorem eval₂_constSmooth_stdSymplecticForm_eq_mvfderiv_refl (x : ℝ × ℝ)
    (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    (stdSymplecticForm (V := ℝ)).constSmooth.eval₂ x v w =
      stdSymplecticForm
        (mvfderiv 𝓘(ℝ, ℝ × ℝ) (Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞).toPartialDiffeomorph x v)
        (mvfderiv 𝓘(ℝ, ℝ × ℝ)
          (Diffeomorph.refl 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) ∞).toPartialDiffeomorph x w) := by
  rw [Diffeomorph.coe_toPartialDiffeomorph, Diffeomorph.coe_refl, mvfderiv_eq_fderiv, fderiv_id,
    ContinuousLinearMap.id_comp, ContinuousLinearEquiv.coe_coe,
    SymplecticForm.fromTangentSpace_constSmooth_apply]

/-- **The standard model of `dx ∧ dy` has `m = 1`.** Darboux's theorem in standard coordinates,
applied to the area form `dx ∧ dy` on the plane, gives a chart centred at the origin into
`EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)` pulling the standard symplectic form back to
`dx ∧ dy`. -/
theorem exists_standardDarbouxChart_constSmooth_stdSymplecticForm :
    ∃ chart : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) (ℝ × ℝ)
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ∞,
      (0 : ℝ × ℝ) ∈ chart.source ∧ chart 0 = 0 ∧
      ∀ x ∈ chart.source, ∀ v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x,
        (stdSymplecticForm (V := ℝ)).constSmooth.eval₂ x v w =
          stdSymplecticForm (mvfderiv 𝓘(ℝ, ℝ × ℝ) chart x v) (mvfderiv 𝓘(ℝ, ℝ × ℝ) chart x w) :=
  (SymplecticForm.isSymplectic_constSmooth _).exists_standardDarbouxChart_of_finrank_eq
    (by simp) 0

/-! ### The form `eˣ dx ∧ dy` and the chart `(x, y) ↦ (eˣ - 1, y)` -/

/-- The smooth function `(x, y) ↦ eˣ` on the plane. -/
private def expFst : C^∞⟮𝓘(ℝ, ℝ × ℝ), ℝ × ℝ; ℝ⟯ :=
  ⟨fun p ↦ exp p.1, (contDiff_exp.comp contDiff_fst).contMDiff⟩

private theorem expFst_apply (p : ℝ × ℝ) : expFst p = exp p.1 :=
  (rfl)

/-- The two-form `eˣ dx ∧ dy` on the plane. -/
def expAreaForm : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) :=
  SmoothForm.funSMulₗ expFst (stdSymplecticForm (V := ℝ)).constSmooth

/-- The form `eˣ dx ∧ dy` evaluates as `(v, w) ↦ eˣ (v₁ w₂ - v₂ w₁)` at `(x, y)`. -/
theorem eval₂_expAreaForm (x : ℝ × ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    expAreaForm.eval₂ x v w = exp x.1 * (v.1 * w.2 - v.2 * w.1) := by
  rw [SmoothBundleForm.eval₂_apply, expAreaForm, SmoothForm.coe_funSMulₗ]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [expFst_apply, ← SmoothBundleForm.eval₂_apply, eval₂_constSmooth_stdSymplecticForm]

/-- The form `eˣ dx ∧ dy` is closed, as every two-form on the plane is. -/
theorem isClosed_expAreaForm : expAreaForm.IsClosed :=
  SmoothForm.isClosed_of_finrank_le (by simp) _

/-- The chart `(x, y) ↦ (eˣ - 1, y)` of the plane onto the half-plane `u > -1`, with inverse
`(u, v) ↦ (log (1 + u), v)`. -/
def expChart : PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) (ℝ × ℝ) ∞ where
  toFun p := (exp p.1 - 1, p.2)
  invFun q := (log (1 + q.1), q.2)
  source := univ
  target := Ioi (-1) ×ˢ univ
  map_source' p _ := ⟨by simp [exp_pos], trivial⟩
  map_target' _ _ := trivial
  left_inv' p _ := by simp
  right_inv' q hq := by
    have hq : 0 < 1 + q.1 := by linarith [hq.1.out]
    simp [exp_log hq]
  open_source := isOpen_univ
  open_target := isOpen_Ioi.prod isOpen_univ
  contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.2 <|
    (((contDiff_exp.comp contDiff_fst).sub contDiff_const).prodMk contDiff_snd).contDiffOn
  contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.2 <|
    ((contDiff_const.add contDiff_fst).contDiffOn.log fun q hq ↦ by
      linarith [hq.1.out]).prodMk contDiff_snd.contDiffOn

@[simp]
theorem expChart_apply (p : ℝ × ℝ) : expChart p = (exp p.1 - 1, p.2) :=
  (rfl)

@[simp]
theorem expChart_source : expChart.source = univ :=
  (rfl)

@[simp]
theorem expChart_target : expChart.target = Ioi (-1) ×ˢ univ :=
  (rfl)

/-- The chart `(x, y) ↦ (eˣ - 1, y)` fixes the origin. -/
theorem expChart_zero : expChart 0 = 0 := by
  simp

/-- The differential of the chart `(x, y) ↦ (eˣ - 1, y)` at `(x, y)` is `v ↦ (eˣ v₁, v₂)`. -/
theorem mvfderiv_expChart_apply (x : ℝ × ℝ) (v : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    mvfderiv 𝓘(ℝ, ℝ × ℝ) expChart x v = (exp x.1 * v.1, v.2) := by
  have h : HasFDerivAt (fun p : ℝ × ℝ ↦ (exp p.1 - 1, p.2))
      ((exp x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (((hasDerivAt_exp x.1).comp_hasFDerivAt x hasFDerivAt_fst).sub_const 1).prodMk
      hasFDerivAt_snd
  have hc : ⇑expChart = fun p : ℝ × ℝ ↦ (exp p.1 - 1, p.2) := funext expChart_apply
  rw [hc, mvfderiv_eq_fderiv, h.fderiv, ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    ContinuousLinearEquiv.coe_coe]
  rw [NormedSpace.fromTangentSpace_apply]

/-- **`(x, y) ↦ (eˣ - 1, y)` is a Darboux chart of `eˣ dx ∧ dy`.** It pulls the area form
`dx ∧ dy` back to `eˣ dx ∧ dy` at every point of the plane. -/
theorem eval₂_expAreaForm_eq_mvfderiv_expChart (x : ℝ × ℝ) (v w : TangentSpace 𝓘(ℝ, ℝ × ℝ) x) :
    expAreaForm.eval₂ x v w =
      stdSymplecticForm (mvfderiv 𝓘(ℝ, ℝ × ℝ) expChart x v)
        (mvfderiv 𝓘(ℝ, ℝ × ℝ) expChart x w) := by
  rw [eval₂_expAreaForm, mvfderiv_expChart_apply, mvfderiv_expChart_apply,
    stdSymplecticForm_real_apply]
  ring

/-- The form `eˣ dx ∧ dy` is symplectic: it is closed, and nondegenerate since the Darboux chart
`(x, y) ↦ (eˣ - 1, y)` pulls the area form back to it. -/
theorem isSymplectic_expAreaForm : expAreaForm.IsSymplectic :=
  ⟨isClosed_expAreaForm, SmoothTwoForm.isNondegenerate_iff_separatingLeft.2 fun x v hv ↦
    (SmoothTwoForm.nondegenerate_bilinFormAt_of_darbouxChart (by simp)
      (fun y _ ↦ eval₂_expAreaForm_eq_mvfderiv_expChart y) (mem_univ x)).1 v fun w ↦ by
        simpa only [SmoothForm.bilinFormAt_apply] using hv w⟩

/-- **No linear Darboux chart for `eˣ dx ∧ dy`.** No continuous linear map pulls a constant
symplectic form back to `eˣ dx ∧ dy` on a neighbourhood of the origin: the pulled-back form would
be constant, whereas `eˣ dx ∧ dy` takes the values `1` and `eᵗ` on the pair `(1, 0), (0, 1)` at the
origin and at `(t, 0)`. -/
theorem not_exists_continuousLinearMap_eventually_eval₂_expAreaForm_eq :
    ¬ ∃ (L : (ℝ × ℝ) →L[ℝ] ℝ × ℝ) (ω₀ : SymplecticForm (ℝ × ℝ)),
      ∀ᶠ x in 𝓝 (0 : ℝ × ℝ), ∀ v w : ℝ × ℝ, expAreaForm.eval₂ x v w = ω₀ (L v) (L w) := by
  rintro ⟨L, ω₀, h⟩
  have hcurve : Tendsto (fun t : ℝ ↦ ((t, 0) : ℝ × ℝ)) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.prodMk continuous_const).tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, ht0⟩ := ((hcurve.eventually h).and self_mem_nhdsWithin).exists
  have h0 := (eval₂_expAreaForm 0 (1, 0) (0, 1)).symm.trans (h.self_of_nhds (1, 0) (0, 1))
  have h1 := (eval₂_expAreaForm (t, 0) (1, 0) (0, 1)).symm.trans (ht (1, 0) (0, 1))
  have : exp t = exp 0 := by simpa using h1.trans h0.symm
  exact ht0.ne' (exp_injective this)

/-! ### A closed form on `ℝ⁴` degenerating at the origin -/

/-- The two-form `x₁ dx₁ ∧ dx₂ + dx₃ ∧ dx₄` on `ℝ⁴ = (ℝ × ℝ) × (ℝ × ℝ)`, built as the pullback of
the constant form `dy₁ ∧ dy₂ + dy₃ ∧ dy₄` along `((x₁, x₂), (x₃, x₄)) ↦ ((x₁² / 2, x₂), (x₃, x₄))`;
its values are recorded in `eval₂_degenerateForm`. -/
def degenerateForm : SmoothTwoForm 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) :=
  SmoothForm.mpullback (fun x : (ℝ × ℝ) × (ℝ × ℝ) ↦ ((x.1.1 ^ 2 / 2, x.1.2), x.2))
    (by fun_prop : ContDiff ℝ ∞ fun x : (ℝ × ℝ) × (ℝ × ℝ) ↦ ((x.1.1 ^ 2 / 2, x.1.2), x.2)).contMDiff
    ((stdSymplecticForm (V := ℝ)).prod (stdSymplecticForm (V := ℝ))).constSmooth

/-- The form `degenerateForm` is `x₁ dx₁ ∧ dx₂ + dx₃ ∧ dx₄`: at `x` it evaluates as
`(v, w) ↦ x₁ (v₁ w₂ - v₂ w₁) + (v₃ w₄ - v₄ w₃)`. -/
theorem eval₂_degenerateForm (x : (ℝ × ℝ) × (ℝ × ℝ))
    (v w : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) x) :
    degenerateForm.eval₂ x v w =
      x.1.1 * (v.1.1 * w.1.2 - v.1.2 * w.1.1) + (v.2.1 * w.2.2 - v.2.2 * w.2.1) := by
  set f : (ℝ × ℝ) × (ℝ × ℝ) → (ℝ × ℝ) × (ℝ × ℝ) := fun x ↦ ((x.1.1 ^ 2 / 2, x.1.2), x.2)
  have h : HasFDerivAt f (((x.1.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ)).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).prodMap (ContinuousLinearMap.id ℝ (ℝ × ℝ))) x := by
    refine ((((hasDerivAt_pow 2 x.1.1).div_const 2).comp_hasFDerivAt x
      (hasFDerivAt_fst.comp x hasFDerivAt_fst)).prodMk
      (hasFDerivAt_snd.comp x hasFDerivAt_fst)).prodMk hasFDerivAt_snd |>.congr_fderiv ?_
    ext <;> simp
  have hd (u : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) x) :
      mvfderiv 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) f x u = ((x.1.1 * u.1.1, u.1.2), u.2) := by
    rw [mvfderiv_eq_fderiv, h.fderiv, ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearMap.coe_prodMap', Prod.map, ContinuousLinearMap.prod_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_id', id_eq, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe]
    rw [NormedSpace.fromTangentSpace_apply]
  refine (SmoothForm.eval₂_mpullback _ _ _ x v w).trans <|
    (SymplecticForm.eval₂_constSmooth_mfderiv_eq _ f x v w).trans ?_
  rw [hd, hd, SymplecticForm.prod_apply, stdSymplecticForm_real_apply,
    stdSymplecticForm_real_apply]
  ring

/-- The form `x₁ dx₁ ∧ dx₂ + dx₃ ∧ dx₄` is closed, as the pullback of a constant form. -/
theorem isClosed_degenerateForm : degenerateForm.IsClosed :=
  (SymplecticForm.isClosed_constSmooth _).mpullback _ _

/-- The form `x₁ dx₁ ∧ dx₂ + dx₃ ∧ dx₄` is nondegenerate exactly off the hyperplane `x₁ = 0`. -/
theorem nondegenerate_bilinFormAt_degenerateForm_iff (x : (ℝ × ℝ) × (ℝ × ℝ)) :
    (degenerateForm.bilinFormAt x).Nondegenerate ↔ x.1.1 ≠ 0 := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (SmoothForm.isAlt_bilinFormAt degenerateForm x).isRefl).trans ?_
  simp only [LinearMap.SeparatingLeft, SmoothForm.bilinFormAt_apply]
  constructor
  · -- At a point of the hyperplane, `∂₁` lies in the null space of the form.
    intro h hx
    have h1 := h ((1, 0), (0, 0)) fun w ↦
      (eval₂_degenerateForm x _ w).trans (by simp [hx])
    exact one_ne_zero (congrArg (fun u : (ℝ × ℝ) × (ℝ × ℝ) ↦ u.1.1) h1)
  · -- Off it, pairing with the four coordinate vectors recovers the four coordinates.
    intro hx v hv
    have hv' (w : TangentSpace 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) x) :
        x.1.1 * (v.1.1 * w.1.2 - v.1.2 * w.1.1) + (v.2.1 * w.2.2 - v.2.2 * w.2.1) = 0 :=
      (eval₂_degenerateForm x v w).symm.trans (hv w)
    have h1 := hv' ((0, 1), (0, 0))
    have h2 := hv' ((1, 0), (0, 0))
    have h3 := hv' ((0, 0), (0, 1))
    have h4 := hv' ((0, 0), (1, 0))
    simp only [mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add] at h1 h2 h3 h4
    have hv1 : v.1.1 = 0 := (mul_eq_zero.1 h1).resolve_left hx
    have hv2 : v.1.2 = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h hx
      · linarith
    exact Prod.ext (Prod.ext hv1 hv2) (Prod.ext h3 (neg_eq_zero.1 h4))

/-- **No Darboux chart for `x₁ dx₁ ∧ dx₂ + dx₃ ∧ dx₄` around the origin.** No partial
diffeomorphism whose source contains the origin pulls a constant symplectic form back to this
closed form, which degenerates at the origin. -/
theorem not_exists_darbouxChart_degenerateForm :
    ¬ ∃ (chart : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ))
        ((ℝ × ℝ) × (ℝ × ℝ)) ((ℝ × ℝ) × (ℝ × ℝ)) ∞) (form₀ : SymplecticForm ((ℝ × ℝ) × (ℝ × ℝ))),
      0 ∈ chart.source ∧ ∀ x ∈ chart.source, ∀ v w : (ℝ × ℝ) × (ℝ × ℝ),
        degenerateForm.eval₂ x v w =
          form₀ (mvfderiv 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) chart x v)
            (mvfderiv 𝓘(ℝ, (ℝ × ℝ) × (ℝ × ℝ)) chart x w) := by
  rintro ⟨chart, form₀, h0, hchart⟩
  exact (nondegenerate_bilinFormAt_degenerateForm_iff 0).1
    (SmoothTwoForm.nondegenerate_bilinFormAt_of_darbouxChart (by simp) hchart h0) rfl

/-! ### Odd dimensions -/

/-- **`ℝ³` carries no nondegenerate two-form.** A nondegenerate two-form would make each tangent
space a symplectic vector space, of even dimension, while `ℝ × ℝ × ℝ` has dimension three. -/
theorem not_isNondegenerate_prod_prod (form : SmoothTwoForm 𝓘(ℝ, ℝ × ℝ × ℝ) (ℝ × ℝ × ℝ)) :
    ¬ form.IsNondegenerate := fun h ↦ by
  have h3 : Module.finrank ℝ (ℝ × ℝ × ℝ) = 3 := by simp
  have := (h.symplecticFormAt 0).even_finrank
  -- `TangentSpace 𝓘(ℝ, E) x` is `E` by definition, so `h3` computes its dimension.
  rw [show Module.finrank ℝ (TangentSpace 𝓘(ℝ, ℝ × ℝ × ℝ) (0 : ℝ × ℝ × ℝ)) = 3 from h3] at this
  exact Nat.not_even_iff_odd.2 (by decide) this

end TauCeti.Examples.Darboux
