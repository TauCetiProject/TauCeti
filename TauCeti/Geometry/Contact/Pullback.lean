/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Pullback of contact forms

Contactness is invariant under a change of coordinates: a smooth map whose differential is
bijective pulls a contact form back to a contact form. Pointwise the converse holds as well;
global reflection only needs surjectivity of the map. In particular diffeomorphisms preserve
and reflect contactness. The contact hyperplanes are the inverse images under the differential.

For a contact form, the differential carries the Reeb field of the pulled-back form to the
original Reeb field. Thus a strict contact diffeomorphism intertwines the Reeb fields, rather
than merely preserving the contact hyperplanes. No compactness or completeness is needed for
these statements, which concern vector fields rather than their global flows.

The pointwise theorem applies to rough one-forms of class `C¹` at the image point and to
maps of class `C²` there. All exterior derivatives and pullbacks use the
existing differential-form calculus.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Sections 1.1 and 2.1.
-/

public section

noncomputable section

open scoped ContDiff Manifold

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

/-- The differential of a smooth map with bijective differentials carries the Reeb field of
the pulled-back contact form to the original Reeb field. -/
theorem IsContactForm.mfderiv_reebVectorField_mpullback
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {α : SmoothForm J N ℝ 1} (hα : α.IsContactForm)
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hdf : ∀ x, Function.Bijective (mfderiv I J f x)) (x : M) :
    mfderiv I J f x ((SmoothForm.mpullback f hf α).reebVectorField x) =
      α.reebVectorField (f x) := by
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

end TauCeti
