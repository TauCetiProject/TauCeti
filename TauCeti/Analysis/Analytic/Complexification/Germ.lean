/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.Germ
public import TauCeti.Analysis.Analytic.Complexification.Basic

/-!
# Complexification of analytic germs

Restriction to real points is injective on holomorphic germs at a real point. The convergent
extension theorem `AnalyticAt.exists_complexification` therefore defines a canonical ring
homomorphism from real analytic germs to holomorphic germs. Its characteristic equation says
that restriction recovers the original real germ, with its values included in `ℂ`.

The representative formula identifies any convergent holomorphic extension with this canonical
complexification. Its image consists exactly of holomorphic germs whose restriction to real
points is real valued; equivalently, those germs commute with conjugation. This comparison
allows arithmetic and analytic changes of coordinates to be performed before or after local
complexification without making compatible choices of power series or radii.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2.
-/

public noncomputable section

open Filter Function Metric Topology

namespace TauCeti.analyticGerms

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {a : ι → ℝ}

/-- Restriction of a holomorphic germ at a real point to the real locus, retaining complex
values. -/
def realRestriction (a : ι → ℝ) :
    analyticGerms ℂ (fun i ↦ (a i : ℂ)) →+* Germ (𝓝 a) ℂ where
  toFun φ := (φ : Germ (𝓝 fun i ↦ (a i : ℂ)) ℂ).compTendsto
    (fun (x : ι → ℝ) i ↦ (x i : ℂ))
    (continuous_pi fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i)).continuousAt
  map_zero' := by rfl
  map_one' := by rfl
  map_add' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.2
    obtain ⟨g, hg, hψ⟩ := mem_analyticGerms_iff.1 ψ.2
    simp only [← hφ, ← hψ, Subring.coe_add, ← Germ.coe_add]
    rfl
  map_mul' φ ψ := by
    obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.2
    obtain ⟨g, hg, hψ⟩ := mem_analyticGerms_iff.1 ψ.2
    simp only [← hφ, ← hψ, Subring.coe_mul, ← Germ.coe_mul]
    rfl

theorem realRestriction_apply (φ : analyticGerms ℂ (fun i ↦ (a i : ℂ))) :
    realRestriction a φ = (φ : Germ (𝓝 fun i ↦ (a i : ℂ)) ℂ).compTendsto
      (fun (x : ι → ℝ) i ↦ (x i : ℂ))
      (continuous_pi fun i ↦
        Complex.continuous_ofReal.comp (continuous_apply i)).continuousAt.tendsto :=
  (rfl)

/-- Restricting a holomorphic function germ is composition with the real inclusion. -/
@[simp]
theorem realRestriction_ofAnalyticAt (F : (ι → ℂ) → ℂ)
    (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ))) :
    realRestriction a (ofAnalyticAt F hF) = (fun x : ι → ℝ ↦ F fun i ↦ (x i : ℂ)) := by
  rw [realRestriction_apply, coe_ofAnalyticAt, Germ.coe_compTendsto]
  rfl

/-- Holomorphic germs at a real point are determined by their restrictions to real points. -/
theorem realRestriction_injective (a : ι → ℝ) : Injective (realRestriction a) := by
  intro φ ψ h
  obtain ⟨F, hF, rfl⟩ := exists_ofAnalyticAt φ
  obtain ⟨G, hG, rfl⟩ := exists_ofAnalyticAt ψ
  rw [realRestriction_ofAnalyticAt, realRestriction_ofAnalyticAt, Germ.coe_eq] at h
  apply Subtype.ext
  rw [coe_ofAnalyticAt, coe_ofAnalyticAt, Germ.coe_eq]
  exact hF.eventuallyEq_of_eventually_real hG h

private theorem exists_complexify (φ : analyticGerms ℝ a) :
    ∃ ψ : analyticGerms ℂ (fun i ↦ (a i : ℂ)),
      realRestriction a ψ = Germ.map (fun t : ℝ ↦ (t : ℂ)) (φ : Germ (𝓝 a) ℝ) := by
  obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.2
  obtain ⟨r, hr, F, hF, hFr, _⟩ := hf.exists_complexification
  refine ⟨ofAnalyticAt F (hF _ (mem_ball_self hr)), ?_⟩
  rw [realRestriction_ofAnalyticAt, ← hφ, Germ.map_coe, Germ.coe_eq]
  filter_upwards [ball_mem_nhds a hr] with x hx using hFr x hx

/-- The canonical convergent complexification of real analytic germs, as a ring homomorphism.
It is characterized by `realRestriction_complexify`. -/
def complexify (a : ι → ℝ) :
    analyticGerms ℝ a →+* analyticGerms ℂ (fun i ↦ (a i : ℂ)) where
  toFun φ := (exists_complexify φ).choose
  map_zero' := by
    apply realRestriction_injective a
    rw [(exists_complexify 0).choose_spec, map_zero]
    rfl
  map_one' := by
    apply realRestriction_injective a
    rw [(exists_complexify 1).choose_spec, map_one]
    rfl
  map_add' φ ψ := by
    apply realRestriction_injective a
    rw [(exists_complexify (φ + ψ)).choose_spec, map_add,
      (exists_complexify φ).choose_spec, (exists_complexify ψ).choose_spec]
    obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.2
    obtain ⟨g, hg, hψ⟩ := mem_analyticGerms_iff.1 ψ.2
    simp only [Subring.coe_add, ← hφ, ← hψ, ← Germ.coe_add, Germ.map_coe]
    exact Germ.coe_eq.2 (.of_forall fun x ↦ Complex.ofReal_add _ _)
  map_mul' φ ψ := by
    apply realRestriction_injective a
    rw [(exists_complexify (φ * ψ)).choose_spec, map_mul,
      (exists_complexify φ).choose_spec, (exists_complexify ψ).choose_spec]
    obtain ⟨f, hf, hφ⟩ := mem_analyticGerms_iff.1 φ.2
    obtain ⟨g, hg, hψ⟩ := mem_analyticGerms_iff.1 ψ.2
    simp only [Subring.coe_mul, ← hφ, ← hψ, ← Germ.coe_mul, Germ.map_coe]
    exact Germ.coe_eq.2 (.of_forall fun x ↦ Complex.ofReal_mul _ _)

/-- Restricting the complexification to the real locus recovers the original germ. -/
@[simp]
theorem realRestriction_complexify (φ : analyticGerms ℝ a) :
    realRestriction a (complexify a φ) =
      Germ.map (fun t : ℝ ↦ (t : ℂ)) (φ : Germ (𝓝 a) ℝ) :=
  (exists_complexify φ).choose_spec

/-- Any holomorphic extension of a real analytic representative represents its canonical
complexification. The extension need agree only as a real germ. -/
theorem complexify_ofAnalyticAt (f : (ι → ℝ) → ℝ) (hf : AnalyticAt ℝ f a)
    (F : (ι → ℂ) → ℂ) (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ)))
    (hFr : ∀ᶠ x in 𝓝 a, F (fun i ↦ (x i : ℂ)) = (f x : ℂ)) :
    complexify a (ofAnalyticAt f hf) = ofAnalyticAt F hF := by
  apply realRestriction_injective a
  rw [realRestriction_complexify, realRestriction_ofAnalyticAt, coe_ofAnalyticAt,
    Germ.map_coe, Germ.coe_eq]
  exact Filter.EventuallyEq.symm hFr

/-- A holomorphic germ is the complexification of a real analytic germ exactly when it takes
real values on the real locus near its base point. -/
theorem exists_complexify_eq_iff_eventually_im_eq_zero {F : (ι → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ))) :
    (∃ φ, complexify a φ = ofAnalyticAt F hF) ↔
      ∀ᶠ x in 𝓝 a, (F fun i ↦ (x i : ℂ)).im = 0 := by
  constructor
  · rintro ⟨φ, hφ⟩
    have h := congrArg (realRestriction a) hφ
    obtain ⟨f, hf, hφf⟩ := mem_analyticGerms_iff.1 φ.2
    rw [realRestriction_complexify, realRestriction_ofAnalyticAt, ← hφf,
      Germ.map_coe, Germ.coe_eq] at h
    filter_upwards [h] with x hx
    rw [← hx]
    exact Complex.ofReal_im _
  · intro hreal
    let u : (ι → ℝ) →L[ℝ] (ι → ℂ) :=
      ContinuousLinearMap.piMap fun _ ↦ Complex.ofRealCLM
    have hf : AnalyticAt ℝ (fun x : ι → ℝ ↦ (F fun i ↦ (x i : ℂ)).re) a :=
      Complex.reCLM.analyticAt _ |>.comp
        ((hF.restrictScalars (𝕜 := ℝ)).compContinuousLinearMap (u := u))
    refine ⟨ofAnalyticAt _ hf, complexify_ofAnalyticAt _ hf F hF ?_⟩
    filter_upwards [hreal] with x hx
    exact Complex.ext (by simp) (by simp [hx])

/-- Complexification does not identify distinct real analytic germs. -/
theorem complexify_injective (a : ι → ℝ) : Injective (complexify a) := by
  intro φ ψ h
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  obtain ⟨g, hg, rfl⟩ := exists_ofAnalyticAt ψ
  have hr := congrArg (realRestriction a) h
  rw [realRestriction_complexify, realRestriction_complexify, coe_ofAnalyticAt,
    coe_ofAnalyticAt, Germ.map_coe, Germ.map_coe, Germ.coe_eq] at hr
  apply Subtype.ext
  rw [coe_ofAnalyticAt, coe_ofAnalyticAt, Germ.coe_eq]
  exact hr.mono fun x hx ↦ Complex.ofReal_injective hx

/-- Complexification commutes with pullback along any holomorphic extension of an analytic
map. Thus analytic coordinate changes act compatibly on real and complex germs. -/
theorem complexify_pullback {b : κ → ℝ} (g : (ι → ℝ) → κ → ℝ)
    (hg : AnalyticAt ℝ g a) (hga : g a = b) (G : (ι → ℂ) → κ → ℂ)
    (hG : AnalyticAt ℂ G (fun i ↦ (a i : ℂ)))
    (hGr : ∀ᶠ x in 𝓝 a, G (fun i ↦ (x i : ℂ)) = fun j ↦ (g x j : ℂ))
    (φ : analyticGerms ℝ b) :
    complexify a (pullback g hg hga φ) =
      pullback G hG (hGr.self_of_nhds.trans
        (congrArg (fun y : κ → ℝ ↦ fun j ↦ (y j : ℂ)) hga)) (complexify b φ) := by
  subst b
  obtain ⟨f, hf, rfl⟩ := exists_ofAnalyticAt φ
  obtain ⟨F, hF, hψ⟩ := exists_ofAnalyticAt (complexify (g a) (ofAnalyticAt f hf))
  have hFr : ∀ᶠ y in 𝓝 (g a), F (fun j ↦ (y j : ℂ)) = (f y : ℂ) := by
    have hr := realRestriction_complexify (ofAnalyticAt f hf)
    rw [← hψ, realRestriction_ofAnalyticAt, coe_ofAnalyticAt, Germ.map_coe, Germ.coe_eq] at hr
    exact hr
  rw [pullback_ofAnalyticAt, ← hψ, pullback_ofAnalyticAt]
  apply complexify_ofAnalyticAt
  filter_upwards [hGr, hg.continuousAt.eventually hFr] with x hx hy
  simpa only [Function.comp_apply, hx] using hy

/-- The holomorphic germs descending to real analytic germs are exactly those commuting
with conjugation near the real base point. -/
theorem exists_complexify_eq_iff_eventually_apply_star {F : (ι → ℂ) → ℂ}
    (hF : AnalyticAt ℂ F (fun i ↦ (a i : ℂ))) :
    (∃ φ, complexify a φ = ofAnalyticAt F hF) ↔
      ∀ᶠ z in 𝓝 (fun i ↦ (a i : ℂ)), F (star z) = star (F z) := by
  rw [exists_complexify_eq_iff_eventually_im_eq_zero]
  refine ⟨hF.eventually_apply_star, fun hstar ↦ ?_⟩
  have hreal := (continuous_pi fun i ↦
    Complex.continuous_ofReal.comp (continuous_apply i)).continuousAt.eventually hstar
  filter_upwards [hreal] with x hx
  have hxstar : star (fun i ↦ (x i : ℂ)) = fun i ↦ (x i : ℂ) := by
    ext i
    simp
  have h : (F fun i ↦ (x i : ℂ)).im = -(F fun i ↦ (x i : ℂ)).im := by
    simpa only [Function.comp_apply, hxstar, Complex.star_def, Complex.conj_im] using
      congrArg Complex.im hx
  linarith

end TauCeti.analyticGerms
