/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Int.Basic

/-!
# Reconstruction of two-sided convex heights from supporting values

Every finite height of an integer-indexed convex sequence admits an affine supporting
line. Outside the finite domain, affine minorants can be tilted to become arbitrarily
high at a prescribed integer. Consequently all heights, including infinity, are the
supremum of the supporting lines. This recovers a two-sided lower convex envelope
from the supporting values of its input and characterises polygon comparison by
comparison of supporting values, without choosing a first point or a vertex walk.

The affine-minorant arguments extend those in `IsConvexSeq.exists_affine_minorant_eq`
and `IsConvexSeq.coe_le_iff_exists_affine_minorant` to integer indices.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

variable {a h g : ℤ → WithTop ℝ}

namespace IsIntConvexSeq

/-- Every finite height of a two-sided convex sequence has an affine supporting line.
This includes a singleton finite domain. -/
theorem exists_affine_minorant_eq (hh : IsIntConvexSeq h) {n : ℤ} (hn : h n ≠ ⊤) :
    ∃ c σ : ℝ, (∀ k : ℤ, ((c + σ * k : ℝ) : WithTop ℝ) ≤ h k) ∧
      c + σ * n = (h n).untop₀ := by
  have hedge {i : ℤ} (hi : h i ≠ ⊤) (hi' : h (i + 1) ≠ ⊤)
      (hin : i = n ∨ i + 1 = n) :
      ∃ c σ : ℝ, (∀ k : ℤ, ((c + σ * k : ℝ) : WithTop ℝ) ≤ h k) ∧
        c + σ * n = (h n).untop₀ := by
    let σ := (h (i + 1)).untop₀ - (h i).untop₀
    refine ⟨(h i).untop₀ - σ * i, σ, fun k => ?_, ?_⟩
    · convert hh.supportingLine_le hi hi' k using 2
      dsimp [σ]
      ring
    · rcases hin with rfl | rfl
      · ring
      · dsimp [σ]
        push_cast
        ring
  by_cases hnext : h (n + 1) ≠ ⊤
  · exact hedge hn hnext (.inl rfl)
  by_cases hprev : h (n - 1) ≠ ⊤
  · exact hedge hprev (by simpa using hn) (.inr (by omega))
  refine ⟨(h n).untop₀, 0, fun k => ?_, by simp⟩
  by_cases hk : h k = ⊤
  · simp [hk]
  have hkn : k = n := by
    rcases lt_trichotomy k n with hkn | hkn | hnk
    · exact False.elim (hprev (hh.ordConnected.out hk hn ⟨by omega, by omega⟩))
    · exact hkn
    · exact False.elim (hnext (hh.ordConnected.out hn hk ⟨by omega, by omega⟩))
  simp [hkn, WithTop.coe_untop₀_of_ne_top hn]

/-- A real number below a two-sided convex height is bounded above by an affine
minorant at that index. At a missing height the minorants are arbitrarily high. -/
theorem coe_le_iff_exists_affine_minorant (hh : IsIntConvexSeq h) (n : ℤ) (r : ℝ) :
    (r : WithTop ℝ) ≤ h n ↔
      ∃ c σ : ℝ, (∀ k : ℤ, ((c + σ * k : ℝ) : WithTop ℝ) ≤ h k) ∧
        r ≤ c + σ * n := by
  refine ⟨fun hr => ?_, fun ⟨c, σ, hline, hr⟩ =>
    (WithTop.coe_le_coe.mpr hr).trans (hline n)⟩
  by_cases hn : h n ≠ ⊤
  · obtain ⟨c, σ, hline, heq⟩ := hh.exists_affine_minorant_eq hn
    refine ⟨c, σ, hline, ?_⟩
    rw [heq]
    rwa [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe] at hr
  obtain ⟨d, m, hdm⟩ := isIntAdmissible_iff.mp hh.isIntAdmissible
  let δ := max 0 (r - (d + m * n))
  have hδ : 0 ≤ δ := le_max_left _ _
  have hrδ : r ≤ d + m * n + δ := by
    have := le_max_right 0 (r - (d + m * n))
    dsimp [δ]
    linarith
  by_cases hleft : ∃ i, i < n ∧ h i ≠ ⊤
  · -- The finite domain is strictly to the left, so tilt upwards.
    obtain ⟨i, hin, hi⟩ := hleft
    refine ⟨d - δ * ((n : ℝ) - 1), m + δ, fun k => ?_, by nlinarith⟩
    by_cases hk : h k = ⊤
    · simp [hk]
    have hkn : k < n := lt_of_not_ge fun hnk =>
      hn (hh.ordConnected.out hi hk ⟨hin.le, hnk⟩)
    have hkn' : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      linarith
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hdm k)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hkn')]
  · -- The finite domain is strictly to the right (or empty), so tilt downwards.
    refine ⟨d + δ * ((n : ℝ) + 1), m - δ, fun k => ?_, by nlinarith⟩
    by_cases hk : h k = ⊤
    · simp [hk]
    have hnk : n < k := by
      rcases lt_trichotomy k n with hkn | rfl | hnk
      · exact False.elim (hleft ⟨k, hkn, hk⟩)
      · exact False.elim (hn hk)
      · exact hnk
    have hnk' : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hdm k)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hnk')]

/-- A two-sided convex height sequence is the supremum of its supporting lines,
including at missing heights and for empty and singleton domains. -/
theorem iSup_intSupportingValue_add (hh : IsIntConvexSeq h) (n : ℤ) :
    (⨆ σ : ℝ, intSupportingValue h σ + ((σ * n : ℝ) : EReal)) =
      (h n).toEReal := by
  refine le_antisymm (iSup_le fun σ =>
    EReal.add_le_of_le_sub (intSupportingValue_le h σ n)) ?_
  by_contra hle
  obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real (lt_of_not_ge hle)
  have hrh : (r : WithTop ℝ) ≤ h n :=
    WithTop.toEReal_le_toEReal_iff.mp ((WithTop.toEReal_coe r).trans_le hr'.le)
  obtain ⟨c, σ, hline, hrc⟩ := (hh.coe_le_iff_exists_affine_minorant n r).mp hrh
  have hs : ((c + σ * n : ℝ) : EReal) ≤
      intSupportingValue h σ + ((σ * n : ℝ) : EReal) := by
    rw [EReal.coe_add]
    exact add_le_add (coe_le_intSupportingValue_iff.mpr hline) le_rfl
  exact (not_le_of_gt hr) ((EReal.coe_le_coe hrc).trans
    (hs.trans (le_iSup (fun σ : ℝ =>
      intSupportingValue h σ + ((σ * n : ℝ) : EReal)) σ)))

/-- Comparison of two-sided heights with a convex lower sequence is equivalent to
comparison of all supporting values. The upper sequence need not be convex. -/
theorem le_iff_forall_intSupportingValue_le (hh : IsIntConvexSeq h) :
    h ≤ a ↔ ∀ σ, intSupportingValue h σ ≤ intSupportingValue a σ := by
  refine ⟨fun hha σ => intSupportingValue_mono hha σ, fun hle n => ?_⟩
  rw [← WithTop.toEReal_le_toEReal_iff, ← hh.iSup_intSupportingValue_add n]
  exact iSup_le fun σ => (add_le_add (hle σ) le_rfl).trans
    (EReal.add_le_of_le_sub (intSupportingValue_le a σ n))

/-- Two convex integer-indexed height sequences agree exactly when their
supporting-value functions agree. -/
theorem eq_iff_intSupportingValue_eq (hh : IsIntConvexSeq h) (hg : IsIntConvexSeq g) :
    h = g ↔ intSupportingValue h = intSupportingValue g := by
  refine ⟨fun heq => congrArg intSupportingValue heq, fun heq => le_antisymm ?_ ?_⟩
  · exact hh.le_iff_forall_intSupportingValue_le.mpr fun σ => (congrFun heq σ).le
  · exact hg.le_iff_forall_intSupportingValue_le.mpr fun σ => (congrFun heq σ).ge

end IsIntConvexSeq

/-- The supporting values of an admissible two-sided sequence reconstruct its
lower convex envelope, not necessarily its original heights. -/
theorem iSup_intSupportingValue_add_eq_intLowerConvexEnvelope
    (ha : IsIntAdmissible a) (n : ℤ) :
    (⨆ σ : ℝ, intSupportingValue a σ + ((σ * n : ℝ) : EReal)) =
      (intLowerConvexEnvelope a n).toEReal := by
  rw [← intSupportingValue_intLowerConvexEnvelope ha]
  exact (isIntConvexSeq_intLowerConvexEnvelope a).iSup_intSupportingValue_add n

end TauCeti
