/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.Distribution.Horizontal
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Topology.Algebra.Module.Alternating.Basic

/-!
# Pullback of contact forms

Contactness is invariant under a change of coordinates: a smooth map whose differential is
bijective pulls a contact form back to a contact form. Pointwise the converse holds as well;
global reflection only needs surjectivity of the map. In particular diffeomorphisms preserve
and reflect contactness. The contact hyperplanes are the inverse images under the differential.

For a contact form, the differential carries the Reeb field of the pulled-back form to the
original Reeb field, and more generally a `C²` map with bijective differential at `x` that pulls
`β` back to `α` on a neighborhood of `x` sends `α.reebVectorField x` to `β.reebVectorField (f x)`
in arbitrary dimension (`TauCeti.IsContactFormAt.mfderiv_reebVectorField_eq`). Thus a strict
contact diffeomorphism intertwines the Reeb fields, rather than merely preserving the contact
hyperplanes. No compactness or completeness is needed for these statements, which concern vector
fields rather than their global flows.

A smooth map is horizontal for the kernel of a one-form exactly when it pulls the form back to
zero (`TauCeti.SmoothForm.isHorizontalMap_kerDistribution_iff_mpullback_eq_zero`).

The pointwise theorem applies to rough one-forms of class `C¹` at the image point and to
maps of class `C²` there. All exterior derivatives and pullbacks use the
existing differential-form calculus.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.1.
-/

public section

noncomputable section

open Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I 2 M] [IsManifold J 2 N]

/-- A map with bijective differential preserves and reflects the pointwise contact condition.
Only `C²` regularity of the map and `C¹` regularity of the one-form at the image are needed. -/
theorem isContactFormAt_mpullback_iff {f : M → N} {x : M} {α : RoughForm J N ℝ 1}
    (hf : ContMDiffAt I J 2 f x)
    (hα : ContMDiffAt J (J.prod 𝓘(ℝ, F [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun y ↦ Bundle.TotalSpace.mk' (F [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) (f x))
    (hdf : Function.Bijective (mfderiv I J f x)) :
    IsContactFormAt (mpullback I J f α) x ↔ IsContactFormAt α (f x) := by
  have hval (v : TangentSpace I x) :
      mpullback I J f α x ![v] = α (f x) ![mfderiv I J f x v] := by
    rw [mpullback_apply]
    congr 1
    ext i
    fin_cases i
    rfl
  have hker (v : TangentSpace I x) :
      v ∈ (mpullback I J f α).ker x ↔ mfderiv I J f x v ∈ α.ker (f x) := by
    simp only [RoughForm.mem_ker, hval]
  have hd (v w : TangentSpace I x) :
      mextDeriv (mpullback I J f α) x ![v, w] =
        mextDeriv α (f x) ![mfderiv I J f x v, mfderiv I J f x w] := by
    rw [← mpullback_mextDeriv_at hf hα, mpullback_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hzero : mpullback I J f α x = 0 ↔ α (f x) = 0 := by
    simpa only [mpullback_zero, Pi.zero_apply] using
      (mpullback_apply_eq_mpullback_apply_iff («ω» := α) (η := 0) hdf.2)
  constructor
  · intro h
    refine ⟨fun hz ↦ h.ne_zero (hzero.mpr hz), ?_⟩
    intro v hv hvw
    obtain ⟨u, rfl⟩ := hdf.2 v
    have hu : u = 0 := h.nondegenerate u ((hker u).mpr hv) fun w hw ↦ by
      rw [hd]
      exact hvw _ ((hker w).mp hw)
    simp [hu]
  · intro h
    refine ⟨fun hz ↦ h.ne_zero (hzero.mp hz), ?_⟩
    intro v hv hvw
    apply hdf.1
    rw [map_zero]
    refine h.nondegenerate _ ((hker v).mp hv) fun w hw ↦ ?_
    obtain ⟨u, rfl⟩ := hdf.2 w
    rw [← hd]
    exact hvw u ((hker u).mpr hw)

namespace SmoothForm

/-- The contact hyperplanes of a pulled-back one-form are the inverse images of the original
hyperplanes under the differential. This identity does not require contactness or invertibility. -/
@[simp]
theorem kerDistribution_mpullback (f : M → N) (hf : ContMDiff I J ∞ f)
    (α : SmoothForm J N ℝ 1) (x : M) :
    (mpullback f hf α).kerDistribution x =
      (α.kerDistribution (f x)).comap (mfderiv I J f x).toLinearMap := by
  ext v
  simp only [mem_kerDistribution, Submodule.mem_comap, ContinuousLinearMap.coe_coe,
    mpullback_apply]
  have hv : (fun i : Fin 1 ↦ mfderiv I J f x (![v] i)) = ![mfderiv I J f x v] := by
    ext i
    fin_cases i
    rfl
  rw [hv]

/-- **Horizontality is the vanishing of the pullback.** A smooth map is horizontal for the kernel
of a one-form `α` exactly when it pulls `α` back to zero. -/
theorem isHorizontalMap_kerDistribution_iff_mpullback_eq_zero {f : M → N}
    (α : SmoothForm J N ℝ 1) (hf : ContMDiff I J ∞ f) :
    IsHorizontalMap I α.kerDistribution f ↔ mpullback f hf α = 0 := by
  have h (x : M) : (mpullback f hf α).1 x = 0 ↔
      LinearMap.range (mfderiv I J f x).toLinearMap ≤ α.kerDistribution (f x) := by
    rw [LinearMap.range_le_iff_comap, ← kerDistribution_mpullback f hf α x, kerDistribution_eq_ker,
      RoughForm.ker_eq_top_iff]
  simp only [isHorizontalMap_iff_range_mfderiv_le, ← h, Subtype.ext_iff, funext_iff,
    ZeroMemClass.coe_zero, Pi.zero_apply]

/-- A smooth map horizontal for the kernel of a one-form `α` also pulls back `dα` to zero. -/
theorem mpullback_mextDerivₗ_eq_zero_of_isHorizontalMap {f : M → N}
    {α : SmoothForm J N ℝ 1} (hf : ContMDiff I J ∞ f)
    (hfα : IsHorizontalMap I α.kerDistribution f) :
    mpullback f hf (mextDerivₗ J 1 α) = 0 := by
  rw [← mextDerivₗ_mpullback, (isHorizontalMap_kerDistribution_iff_mpullback_eq_zero α hf).1 hfα,
    map_zero]

/-- Pullback by a smooth map with bijective differentials preserves contactness. -/
theorem IsContactForm.mpullback {α : SmoothForm J N ℝ 1} (hα : α.IsContactForm)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) :
    (mpullback f hf α).IsContactForm := by
  rw [isContactForm_iff_forall_isContactFormAt] at hα ⊢
  intro x
  rw [coe_mpullback, isContactFormAt_mpullback_iff (hf.of_le (by simp) x)
    (α.contMDiff.of_le (by simp) (f x)) (hdf x)]
  exact hα (f x)

/-- A surjective smooth map with bijective differentials preserves and reflects contactness. -/
theorem isContactForm_mpullback_iff {f : M → N} (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) (hsurj : Function.Surjective f)
    (α : SmoothForm J N ℝ 1) :
    (mpullback f hf α).IsContactForm ↔ α.IsContactForm := by
  constructor
  · intro h
    rw [isContactForm_iff_forall_isContactFormAt] at h ⊢
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    have hx := h x
    rw [coe_mpullback] at hx
    exact (isContactFormAt_mpullback_iff (hf.of_le (by simp) x)
      (α.contMDiff.of_le (by simp) (f x)) (hdf x)).mp hx
  · exact fun h ↦ h.mpullback f hf hdf

/-- Diffeomorphisms preserve and reflect contactness. -/
@[simp]
theorem _root_.Diffeomorph.isContactForm_mpullback_iff (e : M ≃ₘ⟮I, J⟯ N)
    (α : SmoothForm J N ℝ 1) :
    (mpullback e e.contMDiff α).IsContactForm ↔ α.IsContactForm :=
  SmoothForm.isContactForm_mpullback_iff e.contMDiff
    (fun _ ↦ (e.isInvertible_mfderiv (by simp)).bijective) e.surjective α

/-- If the pullback of a one-form along a smooth map `f : M → N` is a contact form and `M` is
nonempty, then the model space of `M` is finite-dimensional whenever that of `N` is. -/
theorem finiteDimensional_of_isContactForm_mpullback [FiniteDimensional ℝ F]
    {α : SmoothForm J N ℝ 1} {f : M → N} (hf : ContMDiff I J ∞ f)
    (hα : (mpullback f hf α).IsContactForm) (x : M) : FiniteDimensional ℝ E := by
  -- The differential of `f` is injective: a vector it kills lies in the kernel of the pullback
  -- and pairs to zero with everything under its exterior derivative.
  have hinj : Function.Injective (mfderiv I J f x) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    refine (isContactForm_iff.1 hα x).2 w ?_ fun w' _ ↦ ?_
    · rw [SmoothForm.mpullback_apply_one, hw, ← degreeOneEquiv_coe_apply, map_zero]
    · rw [mextDeriv_mpullback_apply_two, hw]
      exact (mextDeriv α.1 (f x)).map_coord_zero 0 rfl
  exact Module.Finite.of_injective (mfderiv I J f x : E →L[ℝ] F).toLinearMap hinj

/-- The differential of a smooth map with bijective differentials carries the Reeb field of
the pulled-back contact form to the original Reeb field. -/
theorem IsContactForm.mfderiv_reebVectorField_mpullback
    [FiniteDimensional ℝ E]
    {α : SmoothForm J N ℝ 1} (hα : α.IsContactForm)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) (x : M) :
    mfderiv I J f x ((SmoothForm.mpullback f hf α).reebVectorField x) =
      α.reebVectorField (f x) := by
  have : FiniteDimensional ℝ F := LinearEquiv.finiteDimensional
    (LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap (hdf x) :
      TangentSpace I x ≃ₗ[ℝ] TangentSpace J (f x))
  have hβ := hα.mpullback f hf hdf
  apply hα.eq_reebVectorField_iff.mpr
  constructor
  · have h := hβ.apply_reebVectorField x
    rw [SmoothForm.mpullback_apply] at h
    convert h using 2
    ext i
    fin_cases i
    rfl
  · intro w
    obtain ⟨v, rfl⟩ := (hdf x).2 w
    have h := hβ.mextDeriv_reebVectorField_left x v
    have hd := eval₂_mpullback f hf (mextDerivₗ J 1 α) x
      ((SmoothForm.mpullback f hf α).reebVectorField x) v
    rw [← mextDerivₗ_mpullback] at hd
    simp only [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply] at hd
    exact hd.symm.trans h

end SmoothForm

/-- **Local Reeb pushforward in arbitrary dimension.** If `f : M → N` is `C²` at `x` with bijective
differential at `x`, `β` is a smooth one-form on `N` that is contact at `f x`, and `f` pulls `β`
back to `α` on a neighborhood of `x`, then `mfderiv I J f x` sends `α.reebVectorField x` to
`β.reebVectorField (f x)`. Neither finite-dimensionality nor global contactness is needed. -/
theorem IsContactFormAt.mfderiv_reebVectorField_eq {α : SmoothForm I M ℝ 1}
    {β : SmoothForm J N ℝ 1} {f : M → N} {x : M} (hc : IsContactFormAt β.1 (f x))
    (hf : ContMDiffAt I J 2 f x) (hdf : Function.Bijective (mfderiv I J f x))
    (hpull : ∀ᶠ y in 𝓝 x, ∀ v : TangentSpace I y, β.1 (f y) ![mfderiv I J f y v] = α.1 y ![v]) :
    mfderiv I J f x (α.reebVectorField x) = β.reebVectorField (f x) := by
  have hev : ∀ᶠ y in 𝓝 x, α.1 y = mpullback I J f β.1 y :=
    hpull.mono fun y hy ↦ ContinuousAlternatingMap.ext_fin_one fun v ↦ by
      rw [mpullback_apply_one, hy v]
  have hc_α : IsContactFormAt α.1 x :=
    ((isContactFormAt_mpullback_iff hf (β.contMDiff.of_le (by simp) (f x)) hdf).2
      hc).congr_of_eventuallyEq hev
  have hval (u : TangentSpace I x) : α.1 x ![u] = β.1 (f x) ![mfderiv I J f x u] :=
    (hpull.self_of_nhds u).symm
  have hd (u w : TangentSpace I x) :
      mextDeriv α.1 x ![u, w] = mextDeriv β.1 (f x) ![mfderiv I J f x u, mfderiv I J f x w] := by
    rw [mextDeriv_congr_of_eventuallyEq hev,
      ← mpullback_mextDeriv_at hf (β.contMDiff.of_le (by simp) (f x)), mpullback_apply_pair]
  set a_β := (SmoothForm.degreeOneEquiv β (f x) : TangentSpace J (f x) →ₗ[ℝ] ℝ)
  set B_β := (mextDerivₗ J 1 β).bilinFormAt (f x)
  by_cases hex : ∃ r, a_β r = 1 ∧ ∀ w', a_β w' = 0 → B_β r w' = 0
  · obtain ⟨hr1, hr2⟩ := Module.Dual.reebVector_spec_of_exists hex
    rw [SmoothForm.degreeOneEquiv_coe_apply, ← SmoothForm.reebVectorField_def] at hr1
    obtain ⟨v, hv⟩ := hdf.2 (β.reebVectorField (f x))
    have hv_reeb : α.reebVectorField x = v :=
      hc_α.reebVectorField_eq_of_apply_eq_one (by rwa [hval, hv]) fun w hw ↦ by
        rw [hd, hv, SmoothForm.reebVectorField_def, SmoothForm.mextDeriv_eq_bilinFormAt]
        exact hr2 _ ((SmoothForm.degreeOneEquiv_coe_apply β (f x) _).trans ((hval w).symm.trans hw))
    rw [hv_reeb, hv]
  · have hex_α : ¬∃ r : TangentSpace I x,
        (SmoothForm.degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) r = 1 ∧
          ∀ w, (SmoothForm.degreeOneEquiv α x : TangentSpace I x →ₗ[ℝ] ℝ) w = 0 →
            (mextDerivₗ I 1 α).bilinFormAt x r w = 0 := by
      rintro ⟨r, hr1, hr2⟩
      refine hex ⟨mfderiv I J f x r, ?_, fun w' hw' ↦ ?_⟩
      · rwa [SmoothForm.degreeOneEquiv_coe_apply, ← hval, ← SmoothForm.degreeOneEquiv_coe_apply]
      · obtain ⟨w, rfl⟩ := hdf.2 w'
        rw [← SmoothForm.mextDeriv_eq_bilinFormAt, ← hd, SmoothForm.mextDeriv_eq_bilinFormAt]
        exact hr2 w ((SmoothForm.degreeOneEquiv_coe_apply α x w).trans
          ((hval w).trans ((SmoothForm.degreeOneEquiv_coe_apply β (f x) _).symm.trans hw')))
    rw [SmoothForm.reebVectorField_def, Module.Dual.reebVector_eq_zero_of_not_exists hex_α,
      map_zero, SmoothForm.reebVectorField_def, Module.Dual.reebVector_eq_zero_of_not_exists hex]

end TauCeti
