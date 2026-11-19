/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.Sard.Basic
public import TauCeti.Geometry.Manifold.Sard.EqualDimension

/-!
# Null images of two-parameter maps

Let `F : ℝ × ℝ → M` be a map into a real manifold `M` modelled on a finite-dimensional space.
This file records two null sets attached to `F`, in the sense of `TauCeti.IsNullSet`.

* If `M` has dimension at least two and `F` is differentiable on the frontier of a closed
  rectangle, the image of that frontier is null. The frontier is the union of four segments, and
  each segment is mapped by a differentiable map from `ℝ`, so Sard's theorem for a source of
  smaller dimension applies. No injectivity or regularity of `F` is needed, and degenerate
  rectangles are allowed.
* If `M` has dimension two, the image of the points at which `F` is differentiable and the curve
  `s ↦ F (s, t)` has zero velocity is null. At such a point the differential of `F` kills the
  first coordinate vector, so it is not injective, and Sard's theorem in equal dimensions
  applies.

The manifold `M` may have boundary or corners.

## Main results

* `TauCeti.isNullSet_image_frontier_Icc_prod_Icc`: the image of the frontier of a rectangle is
  null.
* `TauCeti.isNullSet_image_of_curveVelocity_fst_eq_zero`: the image of the points of vanishing
  first partial velocity is null in dimension two.
-/

public section

open Module Set
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : ℝ × ℝ → M}

omit [FiniteDimensional ℝ E] in
/-- The image of the frontier of a closed rectangle under a map that is differentiable on the
frontier is null in every manifold of dimension at least two. -/
theorem isNullSet_image_frontier_Icc_prod_Icc {a b c d : ℝ} (hdim : 1 < finrank ℝ E)
    (hF : ∀ z ∈ frontier (Icc a b ×ˢ Icc c d), MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I F z) :
    IsNullSet I (F '' frontier (Icc a b ×ˢ Icc c d)) := by
  have hdim' : finrank ℝ ℝ < finrank ℝ E := by simpa using hdim
  have hvert (x : ℝ) :
      IsNullSet I ((fun t ↦ F (x, t)) '' {t | (x, t) ∈ frontier (Icc a b ×ˢ Icc c d)}) :=
    isNullSet_image_of_finrank_lt_finrank (I := 𝓘(ℝ)) hdim' fun t ht ↦ (hF _ ht).comp t
      ((contDiff_prodMk_right (n := 1) x).contMDiff.mdifferentiableAt one_ne_zero)
  have hhor (y : ℝ) :
      IsNullSet I ((fun t ↦ F (t, y)) '' {t | (t, y) ∈ frontier (Icc a b ×ˢ Icc c d)}) :=
    isNullSet_image_of_finrank_lt_finrank (I := 𝓘(ℝ)) hdim' fun t ht ↦ (hF _ ht).comp t
      ((contDiff_prodMk_left (n := 1) y).contMDiff.mdifferentiableAt one_ne_zero)
  refine (((hvert a).union (hvert b)).union ((hhor c).union (hhor d))).mono ?_
  rintro _ ⟨⟨x, y⟩, hz, rfl⟩
  have hz' := hz
  rw [(isClosed_Icc.prod isClosed_Icc).frontier_eq, interior_prod_eq, interior_Icc,
    interior_Icc] at hz'
  obtain ⟨⟨⟨hax, hxb⟩, hcy, hyd⟩, hint⟩ := hz'
  rcases hax.eq_or_lt with rfl | hax
  · exact Or.inl (Or.inl ⟨y, hz, rfl⟩)
  rcases hxb.eq_or_lt with rfl | hxb
  · exact Or.inl (Or.inr ⟨y, hz, rfl⟩)
  rcases hcy.eq_or_lt with rfl | hcy
  · exact Or.inr (Or.inl ⟨x, hz, rfl⟩)
  rcases hyd.eq_or_lt with rfl | hyd
  · exact Or.inr (Or.inr ⟨x, hz, rfl⟩)
  exact absurd ⟨⟨hax, hxb⟩, hcy, hyd⟩ hint

/-- For a map from two real parameters into a manifold of dimension two, the image of the points
at which the map is differentiable and its first partial velocity vanishes is null. -/
theorem isNullSet_image_of_curveVelocity_fst_eq_zero {A : Set (ℝ × ℝ)}
    (hdim : finrank ℝ E = 2) (hF : ∀ z ∈ A, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I F z)
    (hzero : ∀ z ∈ A, Manifold.curveVelocity I (fun s ↦ F (s, z.2)) z.1 = 0) :
    IsNullSet I (F '' A) := by
  have hdim' : finrank ℝ (ℝ × ℝ) = finrank ℝ E := by simp [hdim]
  refine isNullSet_image_of_not_isRegularPoint hdim' hF fun z hz hreg ↦ ?_
  have hvel := Manifold.curveVelocity_eq_mfderiv_fst (f := fun s t ↦ F (s, t))
    (u := z.1) (t := z.2) (by simpa only [Prod.mk.eta] using hF z hz)
  rw [hzero z hz] at hvel
  have h10 := (isRegularPoint_iff_injective_mfderiv hdim').1 hreg
    (hvel.symm.trans (map_zero _).symm)
  exact one_ne_zero (congrArg Prod.fst h10)

end TauCeti
