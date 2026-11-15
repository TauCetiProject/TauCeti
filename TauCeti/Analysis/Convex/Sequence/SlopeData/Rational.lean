/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.SlopeData.Basic
public import TauCeti.Analysis.Convex.Sequence.Rationality
import Mathlib.Data.Set.Finite.Lattice

/-!
# Rational presentations of finite convex envelopes

A real height sequence has a unique finite rational unit-slope presentation exactly when
it is convex, its finite domain is nonempty and finite, and all its finite heights are
rational. The presentation uses the existing `FiniteSlopeData ℚ`; its real heights are
obtained by applying `WithTop.map` to the rational heights. Equality is equality of heights,
not a choice of subdivision.

In particular, the lower convex envelope of a nonempty finite set of rational points has
such a presentation. Coefficient points may be missing, and the envelope need not pass
through every given point. Length zero represents a singleton; the empty envelope has no
anchored presentation. Finiteness is essential: integral coefficient points can have an
irrational terminal ray.

The construction reuses real slope extraction and its uniqueness from
`FiniteSlopeData.exists_heights_eq_iff` and `FiniteSlopeData.heights_injective`, and the
contact-based rationality theorem for finite envelopes.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, Chapter IV §3.
-/

public section

namespace TauCeti

/-- A real height sequence has a unique rational finite slope presentation exactly when it
is convex with nonempty finite domain and rational finite heights. The initial abscissa is
absolute, and the length-zero case is included. -/
theorem FiniteSlopeData.existsUnique_rat_heights_eq_iff {h : ℕ → WithTop ℝ} :
    (∃! d : FiniteSlopeData ℚ,
      (fun n => WithTop.map ((↑) : ℚ → ℝ) (d.heights n)) = h) ↔
      IsConvexSeq h ∧ {n | h n ≠ ⊤}.Nonempty ∧ {n | h n ≠ ⊤}.Finite ∧
        ∀ n, h n ≠ ⊤ → ∃ q : ℚ, h n = ((q : ℝ) : WithTop ℝ) := by
  let f : ℚ →+o ℝ :=
    { (Rat.castHom ℝ).toAddMonoidHom with monotone' := Rat.cast_mono }
  have hmap (d : FiniteSlopeData ℚ) :
      (d.map f).heights = fun n => WithTop.map ((↑) : ℚ → ℝ) (d.heights n) := by
    funext n
    exact d.heights_map f n
  constructor
  · rintro ⟨d, hd, -⟩
    obtain ⟨hc, hne, hfin⟩ := exists_heights_eq_iff.mp ⟨d.map f, (hmap d).trans hd⟩
    refine ⟨hc, hne, hfin, fun n hn => ?_⟩
    have hdne : d.heights n ≠ ⊤ := by
      rw [← hd] at hn
      exact fun he => hn (by simp [he])
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hdne
    exact ⟨q, by simp only [← hd, ← hq, WithTop.map_coe]⟩
  · rintro ⟨hc, hne, hfin, hrat⟩
    obtain ⟨d, hd⟩ := exists_heights_eq_iff.mpr ⟨hc, hne, hfin⟩
    -- Descend the real anchor and each real increment to rational numbers.
    have hy : ∃ y : ℚ, (y : ℝ) = d.initialHeight := by
      obtain ⟨y, hy⟩ := hrat d.start (by rw [← hd, d.heights_start]; exact WithTop.coe_ne_top)
      rw [← hd, d.heights_start, WithTop.coe_eq_coe] at hy
      exact ⟨y, hy.symm⟩
    have hs : ∀ i : Fin d.length, ∃ q : ℚ, (q : ℝ) = d.slope i := by
      intro i
      have hn : d.heights (d.start + i) ≠ ⊤ := d.heights_ne_top_iff.mpr ⟨by omega, by omega⟩
      have hn' : d.heights (d.start + i + 1) ≠ ⊤ :=
        d.heights_ne_top_iff.mpr ⟨by omega, by omega⟩
      obtain ⟨q, hq⟩ := hrat (d.start + i) (hd ▸ hn)
      obtain ⟨q', hq'⟩ := hrat (d.start + i + 1) (hd ▸ hn')
      refine ⟨q' - q, ?_⟩
      rw [← d.unitSlope_heights i, unitSlope_def, hd, hq, hq']
      simp
    obtain ⟨y, hy⟩ := hy
    choose s hs using hs
    let e : FiniteSlopeData ℚ :=
      { start := d.start
        initialHeight := y
        length := d.length
        slope := s
        monotone := fun i j hij => Rat.cast_le.mp (by rw [hs i, hs j]; exact d.monotone hij) }
    -- Real slope extraction already supplies reconstruction; only descent is new.
    have he : e.map f = d := by
      apply ext_of_slope (by simp [e]) (by simpa [e, f] using hy) (by simp [e])
      intro i
      simpa [e, f] using hs (i.cast (by simp [e]))
    have heh : (fun n => WithTop.map ((↑) : ℚ → ℝ) (e.heights n)) = h := by
      rw [← hmap, he, hd]
    refine ⟨e, heh, fun e' he' => heights_injective ?_⟩
    funext n
    exact WithTop.map_injective Rat.cast_injective (congr_fun (he'.trans heh.symm) n)

/-- The lower convex envelope of a nonempty finite set of rational point heights is
represented by unique rational finite slope data. Intermediate envelope heights may be
nonintegral even when all input heights are integral. -/
theorem existsUnique_rat_heights_lowerConvexEnvelope {a : ℕ → WithTop ℝ}
    (hfin : {n | a n ≠ ⊤}.Finite) (hne : {n | a n ≠ ⊤}.Nonempty)
    (hrat : ∀ n, a n ≠ ⊤ → ∃ q : ℚ, a n = ((q : ℝ) : WithTop ℝ)) :
    ∃! d : FiniteSlopeData ℚ,
      (fun n => WithTop.map ((↑) : ℚ → ℝ) (d.heights n)) = lowerConvexEnvelope a := by
  obtain ⟨N, hN⟩ := hfin.bddAbove
  have htail : ∀ n, N < n → a n = ⊤ := by
    intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hN h)
  have ha := isAdmissible_of_forall_gt htail
  have hh := isLowerConvexEnvelope_lowerConvexEnvelope ha
  have hfinite : {n | lowerConvexEnvelope a n ≠ ⊤}.Finite := by
    apply (Set.finite_Iic N).subset
    intro n hn
    obtain ⟨i, -, j, hnj, -, hj⟩ := (lowerConvexEnvelope_ne_top_iff ha).mp hn
    exact hnj.trans (hN hj)
  apply FiniteSlopeData.existsUnique_rat_heights_eq_iff.mpr
  refine ⟨hh.isConvexSeq, ?_, hfinite, fun n hn => hh.exists_rat_height_of_finiteDomain
    hrat hfinite hn⟩
  obtain ⟨n, hn⟩ := hne
  exact ⟨n, ne_top_of_le_ne_top hn (hh.le n)⟩

end TauCeti
