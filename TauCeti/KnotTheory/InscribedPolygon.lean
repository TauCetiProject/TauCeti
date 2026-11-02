/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Polygon.Inscribed

/-!
# Inscribed polygons of a smooth knot

A smooth embedding of the circle into a real normed space, read through `Circle.exp`, has simple
inscribed polygons (`TauCeti.SmoothEmbedding.eventually_isSimple_inscribed`), and any two of them
with enough vertices are combinatorially equivalent
(`TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed`). So a smooth knot determines
a polygonal knot (`TauCeti.SimplePolygon`) up to combinatorial equivalence. That the inscribed
polygons are ambient isotopic to the smooth knot, as in Crowell and Fox, Appendix I, and that the
polygonal knot only depends on the smooth knot up to isotopy, are not proved here.

## Main results

* `TauCeti.SmoothEmbedding.eventually_isSimple_inscribed`: the inscribed polygons of a smooth
  embedding of the circle into a real normed space are eventually simple.
* `TauCeti.SmoothEmbedding.exists_combinatoriallyEquivalent_inscribed`: any two of them with enough
  vertices are combinatorially equivalent.

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

end TauCeti.SmoothEmbedding
