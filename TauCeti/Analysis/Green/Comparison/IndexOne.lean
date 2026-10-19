/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Loop
public import TauCeti.Analysis.Green.IndexOne

/-!
# Agreement of manifold boundary integration with index-one Green and flux

A positively oriented parametrization of an actual compact one-dimensional manifold computes
its canonical top-form integral. Under the geometric index-one hypothesis, this same integral
is the unweighted filled-hull area integral from AC Green. Applying the result to `(-Y,X)`
gives outward flux, including both genuine boundary and area integrability conclusions.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti.Green

local notation "E" => EuclideanSpace ℝ (Fin 1)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ, E) 1 N] [CompactSpace N]

/-- The canonical integral over an actual oriented manifold agrees with index-one Green on
its parametrized image. In particular, the induced outward-first boundary orientation may be
used for the lift. No equality of integrals is a hypothesis. -/
theorem integralTopForm_mpullback_eq_index_one_area
    (o : Manifold.Orientation 𝓘(ℝ, E) N (Fin 1)) {p : N} (q : Path p p)
    (f : N → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 f)
    (P Q : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U)
    (hqimage : q.extend '' Ioo (0 : ℝ) 1 = {p}ᶜ)
    (hqinj : InjOn q.extend (Ioo (0 : ℝ) 1))
    (e : ∀ z : E, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (q.extend (z 0)))
    (hqd : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ q.extend (z 0)) z
        ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          o.orientationAt (q.extend (z 0)))
    (hAC : AbsolutelyContinuousOnInterval (q.map hf.continuous).extend 0 1)
    (hHull : filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) ⊆ U)
    (hindex : ∀ z ∈ filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) \
        ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1),
      Contour.windingNumber (q.map hf.continuous).extend 0 1 z = 1) :
    IntegrableTopForm (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) ∧
      CurveIntegrable (oneForm P Q) (q.map hf.continuous) ∧
      IntegrableOn (curl P Q)
        (filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) \
          ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1)) ∧
      integralTopForm o
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
          ∫ z in filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) \
            ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1), curl P Q z := by
  have hrange : range f ⊆ U := by
    rintro z ⟨x, rfl⟩
    apply hHull
    apply subset_filledHull
    by_cases hx : x = p
    · subst x
      exact ⟨0, by simp, by simp⟩
    · have hm : x ∈ q.extend '' Ioo (0 : ℝ) 1 := by
        rw [hqimage]
        exact hx
      obtain ⟨t, ht, he⟩ := hm
      refine ⟨t, ?_, ?_⟩
      · simpa only [uIcc_of_le zero_le_one] using Ioo_subset_Icc_self ht
      · -- Path.map extends by applying f; expose that evaluation before rewriting the path point.
        change f (q.extend t) = f x
        rw [he]
  have hb := integralTopForm_mpullback_eq_curveIntegral o q f hf P Q U hU hrange
    hP.continuousOn hQ.continuousOn hqimage hqinj e hqd hqo
  have hclosed : (q.map hf.continuous).extend 0 = (q.map hf.continuous).extend 1 := by simp
  have hg := green_ac_index_one zero_lt_one hAC hclosed
    hU hHull hP hQ hindex
  refine ⟨hb.1, hb.2.1, hg.2.1, hb.2.2.trans ?_⟩
  rw [curveIntegral_oneForm_eq]
  exact hg.2.2

/-- Outward manifold flux agrees with the AC index-one divergence formula. The positive
boundary orientation is encoded by the actual derivative of the parametrization; the flux
one-form is `X dy - Y dx`. -/
theorem integralTopForm_mpullback_flux_eq_index_one_area
    (o : Manifold.Orientation 𝓘(ℝ, E) N (Fin 1)) {p : N} (q : Path p p)
    (f : N → ℂ) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) 1 f)
    (X Y : ℂ → ℝ) (U : Set ℂ) (hU : IsOpen U)
    (hX : ContDiffOn ℝ 1 X U) (hY : ContDiffOn ℝ 1 Y U)
    (hqimage : q.extend '' Ioo (0 : ℝ) 1 = {p}ᶜ)
    (hqinj : InjOn q.extend (Ioo (0 : ℝ) 1))
    (e : ∀ z : E, E ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (q.extend (z 0)))
    (hqd : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z : E ↦ q.extend (z 0)) z
        ((e z).toContinuousLinearMap.comp (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hqo : ∀ z : E, z 0 ∈ Ioo (0 : ℝ) 1 →
      Orientation.map (Fin 1) (e z).toLinearEquiv
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation =
          o.orientationAt (q.extend (z 0)))
    (hAC : AbsolutelyContinuousOnInterval (q.map hf.continuous).extend 0 1)
    (hHull : filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) ⊆ U)
    (hindex : ∀ z ∈ filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) \
        ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1),
      Contour.windingNumber (q.map hf.continuous).extend 0 1 z = 1) :
    IntegrableTopForm (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f
      (manifoldOneForm (fun z ↦ -Y z) X)) ∧
      CurveIntegrable (oneForm (fun z ↦ -Y z) X) (q.map hf.continuous) ∧
      IntegrableOn (fun z ↦ fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I)
        (filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) \
          ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1)) ∧
      integralTopForm o
        (mpullback 𝓘(ℝ, E) 𝓘(ℝ, ℂ) f (manifoldOneForm (fun z ↦ -Y z) X)) =
          ∫ z in filledHull ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1) \
            ((q.map hf.continuous).extend '' uIcc (0 : ℝ) 1),
              fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I := by
  have h := integralTopForm_mpullback_eq_index_one_area o q f hf (fun z ↦ -Y z) X U hU
    hY.neg hX hqimage hqinj e hqd hqo hAC hHull hindex
  have hd : curl (fun z ↦ -Y z) X =
      fun z ↦ fderiv ℝ X z 1 + fderiv ℝ Y z Complex.I := by
    funext z
    rw [curl]
    -- Pointwise negation of the coefficient function is the Pi.neg used by fderiv_neg.
    change fderiv ℝ X z 1 - fderiv ℝ (-Y) z Complex.I = _
    rw [fderiv_neg, neg_apply, sub_neg_eq_add]
  rwa [hd] at h

end TauCeti.Green
