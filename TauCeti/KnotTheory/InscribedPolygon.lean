/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Polygon.Inscribed

/-!
# Inscribed polygons of a smooth knot

A smooth embedding of the circle into a real normed space, read through `Circle.exp`, has simple
inscribed polygons (`TauCeti.SmoothEmbedding.eventually_isSimple_inscribed`), and any two of them
with enough vertices are combinatorially equivalent
(`TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed`). So a smooth knot determines
a polygonal knot (`TauCeti.SimplePolygon`) up to combinatorial equivalence. The fine inscribed
polygons are moreover ambient isotopic to the smooth knot, as in Crowell and Fox, Appendix I
(`TauCeti.SmoothEmbedding.eventually_exists_ambientIsotopy_image_inscribed`): a smooth knot is tame.
The polygonal knot only depends on the smooth knot up to smooth isotopy through embeddings
(`TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed_of_smoothIsotopic`): the
isotopy, read through a smooth step in time, is a `C¹` isotopy of loops in the sense of
`Polygon.exists_combinatoriallyEquivalent_inscribed_of_isotopy`. That it only depends on the smooth
knot up to ambient isotopy is not proved here.

## Main results

* `TauCeti.SmoothEmbedding.eventually_isSimple_inscribed`: the inscribed polygons of a smooth
  embedding of the circle into a real normed space are eventually simple.
* `TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed`: any two of them with enough
  vertices are combinatorially equivalent.
* `TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed_of_smoothIsotopic`: so are
  fine inscribed polygons of two smoothly isotopic smooth knots.
* `TauCeti.SmoothEmbedding.eventually_exists_ambientIsotopy_image_inscribed`: an ambient isotopy of
  the ambient space carries a smooth knot onto each of its inscribed polygons with enough vertices.

## References

* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Springer GTM 57 (1977), Appendix I, for
  inscribed polygons of a knot of class `C¹`.
-/

public section

open Filter Function
open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ∞ω}

/-- A `C^n` embedding `K : S¹ → E`, `n ≥ 1`, read through `Circle.exp`, is a `C¹` loop of period
`2π`, injective modulo `2π`, with nowhere vanishing derivative. -/
private theorem comp_circleExp (K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) n Circle E) (hn : 1 ≤ n) :
    ContDiff ℝ 1 (K ∘ Circle.exp) ∧ Periodic (K ∘ Circle.exp) (2 * Real.pi) ∧
      (∀ s t, (K ∘ Circle.exp) s = (K ∘ Circle.exp) t → ∃ k : ℤ, s = t + k * (2 * Real.pi)) ∧
      ∀ t, deriv (K ∘ Circle.exp) t ≠ 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  exact ⟨(contMDiff_iff_contDiff.1 (K.contMDiff.comp contMDiff_circleExp)).of_le hn,
    fun t ↦ by simp only [comp_apply, Circle.periodic_exp t],
    fun s t hst ↦ Circle.exp_eq_exp.1 (K.isEmbedding.injective hst), fun t ↦
    (deriv_comp_circleExp_ne_zero_and_range_mfderiv (K.contMDiff.of_le hn)
      (K.isImmersion.mfderiv_injective hn0) t).1⟩

/-- **Inscribed polygons of a smooth knot are eventually simple.** For a `C^n` embedding
`K : S¹ → E`, `n ≥ 1`, of the circle into a real normed space, read through `Circle.exp` as a loop
of period `2π`, the polygon with vertices `K (exp (2πk / m))` is simple for all large `m`. For
`E = ℝ³` these are polygonal knots (`TauCeti.SimplePolygon`) inscribed in the smooth knot `K`. -/
theorem eventually_isSimple_inscribed (K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) n Circle E)
    (hn : 1 ≤ n) :
    ∀ᶠ m in atTop, (Polygon.inscribed (K ∘ Circle.exp) (2 * Real.pi) m).IsSimple ℝ :=
  have ⟨hγ, hper, hinj, hderiv⟩ := comp_circleExp K hn
  Polygon.eventually_isSimple_inscribed Real.two_pi_pos hγ hper hinj hderiv

/-- **Fine inscribed polygons of a smooth knot are combinatorially equivalent.** For a `C^n`
embedding `K : S¹ → E`, `n ≥ 1`, of the circle into a real normed space, read through `Circle.exp`
as a loop of period `2π`, the simple polygons inscribed in `K` with `m` and with `m'` vertices are
related by Δ-moves and subdivisions of edges for all large `m` and `m'`. So the smooth knot `K`
determines its inscribed polygonal knot up to combinatorial equivalence. -/
theorem exists_combinatoriallyEquivalent_inscribed
    (K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) n Circle E) (hn : 1 ≤ n) :
    ∃ N, ∀ m m' : ℕ, ∀ [NeZero m] [NeZero m'], N ≤ m → N ≤ m' →
      ∀ (hm : (Polygon.inscribed (K ∘ Circle.exp) (2 * Real.pi) m).IsSimple ℝ)
        (hm' : (Polygon.inscribed (K ∘ Circle.exp) (2 * Real.pi) m').IsSimple ℝ),
        SimplePolygon.CombinatoriallyEquivalent ⟨m, _, hm⟩ ⟨m', _, hm'⟩ :=
  have ⟨hγ, hper, hinj, hderiv⟩ := comp_circleExp K hn
  Polygon.exists_combinatoriallyEquivalent_inscribed Real.two_pi_pos hγ hper hinj hderiv

/-- **Fine inscribed polygons of smoothly isotopic knots are combinatorially equivalent.** Let
`K₀, K₁ : S¹ → E` be `C^n` embeddings, `n ≥ 1`, of the circle into a real normed space, joined by
a smooth isotopy through embeddings (`TauCeti.SmoothIsotopic`). Then for all large `m` and `m'` the
simple polygons inscribed in `K₀` with `m` vertices and in `K₁` with `m'` vertices, read through
`Circle.exp`, are related by Δ-moves and subdivisions of edges. So the polygonal knot inscribed in a
smooth knot only depends on its smooth isotopy class. -/
theorem exists_combinatoriallyEquivalent_inscribed_of_smoothIsotopic
    {K₀ K₁ : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) n Circle E} (hn : 1 ≤ n)
    (h : SmoothIsotopic K₀.toContMDiffMap K₁.toContMDiffMap) :
    ∃ N, ∀ m m' : ℕ, ∀ [NeZero m] [NeZero m'], N ≤ m → N ≤ m' →
      ∀ (hm : (Polygon.inscribed (K₀ ∘ Circle.exp) (2 * Real.pi) m).IsSimple ℝ)
        (hm' : (Polygon.inscribed (K₁ ∘ Circle.exp) (2 * Real.pi) m').IsSimple ℝ),
        SimplePolygon.CombinatoriallyEquivalent ⟨m, _, hm⟩ ⟨m', _, hm'⟩ := by
  obtain ⟨F⟩ := smoothIsotopic_def.1 h
  -- Run through the isotopy along the smooth step `σ` from time `0` to time `1`.
  set σ : ℝ → unitInterval := fun t ↦
    ⟨Real.smoothTransition t, Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
    with hσ
  set Γ : ℝ → ℝ → E := fun t s ↦ F (σ t, Circle.exp s) with hΓ_def
  have hΓ : ContDiff ℝ 1 (uncurry Γ) := by
    have hpair : ContMDiff 𝓘(ℝ, ℝ × ℝ) ((𝓡∂ 1).prod (𝓡 1)) 1
        (fun p : ℝ × ℝ ↦ (σ p.1, Circle.exp p.2)) :=
      (contDiff_fst.contMDiff.smoothTransition (by simp)).prodMk
        ((contMDiff_circleExp (m := 1)).comp contDiff_snd.contMDiff)
    have e : uncurry Γ = F ∘ fun p : ℝ × ℝ ↦ (σ p.1, Circle.exp p.2) := by
      funext p
      simp [uncurry_def, hΓ_def]
    rw [e]
    exact contMDiff_iff_contDiff.1 ((F.contMDiff.of_le hn).comp hpair)
  -- Each time slice is a smooth knot.
  have hslice (t : ℝ) := comp_circleExp (SmoothEmbedding.ofIsSmoothEmbedding _
    (F.isSmoothEmbedding (σ t))) hn
  simp only [coe_ofIsSmoothEmbedding] at hslice
  obtain ⟨N, hN⟩ := Polygon.exists_combinatoriallyEquivalent_inscribed_of_isotopy Real.two_pi_pos hΓ
    (fun t _ ↦ (hslice t).2.1) (fun t _ ↦ (hslice t).2.2.1) (fun t _ ↦ (hslice t).2.2.2)
  have hσ₀ : σ 0 = 0 := Subtype.ext (Real.smoothTransition.zero_of_nonpos le_rfl)
  have hσ₁ : σ 1 = 1 := Subtype.ext (Real.smoothTransition.one_of_one_le le_rfl)
  have hΓ₀ : Γ 0 = K₀ ∘ Circle.exp := by
    funext s
    simp [hΓ_def, hσ₀, F.apply_zero]
  have hΓ₁ : Γ 1 = K₁ ∘ Circle.exp := by
    funext s
    simp [hΓ_def, hσ₁, F.apply_one]
  rw [hΓ₀, hΓ₁] at hN
  exact ⟨N, hN⟩

/-- **A smooth knot is ambient isotopic to its fine inscribed polygons.** For a `C^n` embedding
`K : S¹ → E`, `n ≥ 1`, of the circle into a real normed space, read through `Circle.exp` as a loop
of period `2π`, for all large `m` some ambient isotopy of `E` carries the image of `K` onto the
polygon with vertices `K (exp (2πk / m))`. -/
theorem eventually_exists_ambientIsotopy_image_inscribed
    (K : SmoothEmbedding (𝓡 1) 𝓘(ℝ, E) n Circle E) (hn : 1 ≤ n) :
    ∀ᶠ m in atTop, ∃ Φ : AmbientIsotopy E,
      Φ.final '' Set.range K = (Polygon.inscribed (K ∘ Circle.exp) (2 * Real.pi) m).boundary ℝ := by
  have ⟨hγ, hper, hinj, hderiv⟩ := comp_circleExp K hn
  rw [← Circle.exp_surjective.range_comp]
  exact Polygon.eventually_exists_ambientIsotopy_image_inscribed Real.two_pi_pos hγ hper hinj hderiv

end TauCeti.SmoothEmbedding
