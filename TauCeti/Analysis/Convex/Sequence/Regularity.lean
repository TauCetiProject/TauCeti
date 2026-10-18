/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Regularity of supporting values

The real supporting value is concave on the slopes where the supporting value is not
negative infinity. For a nonempty height sequence, this is its finite-value domain
and is a lower interval of slopes. No convexity assumption on the heights is needed.
The real supporting value is continuous on the interior of this slope domain.
For the empty sequence, the real supporting value is the constant zero function.

For a nonempty finite point set, the supporting value is the minimum of finitely many
real affine functions on the whole slope line. For a convex height sequence, a finite
edge `[m, m+1]` gives the finite set of finite-height indices `n ≤ m`, which computes
every supporting value at slopes strictly below `unitSlope h m`, with no bounded-domain
assumption. Consequently the real supporting value is continuous there. The same finite
set works on every compact slope interval below that edge; no assertion is made at a
limiting terminal-ray slope.
These finite reductions are useful for identifying active coefficients and for local
piecewise-affine descriptions of Newton polygons.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Set Finset

namespace TauCeti

variable {a h : ℕ → WithTop ℝ}

/-- Slopes with supporting value above negative infinity form a convex set. For a
nonempty point sequence these are exactly the slopes with finite supporting value. -/
theorem convex_setOf_supportingValue_ne_bot (a : ℕ → WithTop ℝ) :
    Convex ℝ {σ | supportingValue a σ ≠ ⊥} := by
  rw [convex_iff_ordConnected]
  exact ⟨fun x _ y hy z hz =>
    ne_bot_of_le_ne_bot hy (supportingValue_antitone a hz.2)⟩

/-- The real supporting value is concave where the supporting value is not negative
infinity. For a nonempty height sequence this is its finite-value domain; for the empty
sequence the real supporting value is constant zero. No convexity or admissibility is required. -/
theorem concaveOn_supportingValue_toReal (a : ℕ → WithTop ℝ) :
    ConcaveOn ℝ {σ | supportingValue a σ ≠ ⊥}
      (fun σ => (supportingValue a σ).toReal) := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simpa using concaveOn_const (0 : ℝ) (convex_setOf_supportingValue_ne_bot ⊤)
  have hne : ∃ n, a n ≠ ⊤ := Function.ne_iff.mp ha
  refine ⟨convex_setOf_supportingValue_ne_bot a, ?_⟩
  intro x hx y hy u v hu hv huv
  have htop (σ : ℝ) : supportingValue a σ ≠ ⊤ :=
    ne_of_lt (supportingValue_lt_top_iff.mpr hne)
  have hline (σ : ℝ) (hσ : supportingValue a σ ≠ ⊥) :=
    coe_le_supportingValue_iff_untop₀.mp (EReal.coe_toReal_le hσ)
  have hxy : supportingValue a (u • x + v • y) ≠ ⊥ :=
    (convex_setOf_supportingValue_ne_bot a) hx hy hu hv huv
  apply EReal.coe_le_coe_iff.mp
  rw [EReal.coe_toReal (htop _) hxy]
  apply coe_le_supportingValue_iff_untop₀.mpr
  intro n hn
  have hx' := hline x hx n hn
  have hy' := hline y hy n hn
  simp only [smul_eq_mul]
  linarith [mul_le_mul_of_nonneg_left hx' hu, mul_le_mul_of_nonneg_left hy' hv,
    congrArg (fun t : ℝ => t * (a n).untop₀) huv]

/-- The real supporting value of any height sequence is continuous on the interior
of the slopes where its supporting value is not negative infinity. -/
theorem continuousOn_supportingValue_toReal (a : ℕ → WithTop ℝ) :
    ContinuousOn (fun σ => (supportingValue a σ).toReal)
      (interior {σ | supportingValue a σ ≠ ⊥}) :=
  (concaveOn_supportingValue_toReal a).continuousOn_interior

/-- On a nonempty finite point set, supporting values are the real minimum of the
finitely many tilted heights. Missing heights do not participate in the minimum. -/
theorem supportingValue_eq_coe_inf' {I : Finset ℕ} (hI : I.Nonempty)
    (hdom : ∀ n, a n ≠ ⊤ ↔ n ∈ I) (σ : ℝ) :
    supportingValue a σ =
      ((I.inf' hI (fun n => (a n).untop₀ - σ * n) : ℝ) : EReal) := by
  apply le_antisymm
  · obtain ⟨n, hn, heq⟩ := I.exists_mem_eq_inf' hI (fun n => (a n).untop₀ - σ * n)
    rw [heq]
    convert supportingValue_le a σ n using 1
    rw [← WithTop.coe_untop₀_of_ne_top ((hdom n).mpr hn), WithTop.toEReal_coe,
      EReal.coe_sub]
    simp
  · apply coe_le_supportingValue_iff_untop₀.mpr
    intro n hn
    have := I.inf'_le (fun n => (a n).untop₀ - σ * n) ((hdom n).mp hn)
    linarith

/-- The real supporting value of a finite point set is continuous at every
real slope. This does not require the original heights to be convex. -/
theorem continuous_supportingValue_toReal_of_finite
    (hfinite : {n | a n ≠ ⊤}.Finite) :
    Continuous (fun σ => (supportingValue a σ).toReal) := by
  classical
  obtain rfl | ha := eq_or_ne a ⊤
  · simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  have hne : {n | a n ≠ ⊤}.Nonempty := Function.ne_iff.mp ha
  let I := hfinite.toFinset
  have hI : I.Nonempty := hfinite.toFinset_nonempty.mpr hne
  have heq (σ : ℝ) : (supportingValue a σ).toReal =
      I.inf' hI (fun n => (a n).untop₀ - σ * n) := by
    rw [supportingValue_eq_coe_inf' hI (by simp [I]), EReal.toReal_coe]
  simp_rw [heq]
  fun_prop

/-- A later finite edge bounds the indices needed to compute all supporting values at
smaller slopes. One finite nonempty set works uniformly on the whole open half-line. -/
theorem IsConvexSeq.exists_finset_supportingValue_eq_inf' (hh : IsConvexSeq h)
    {m : ℕ} (hm : m ∈ finiteEdges h) :
    ∃ (I : Finset ℕ) (hI : I.Nonempty),
      (∀ n, n ∈ I ↔ n ≤ m ∧ h n ≠ ⊤) ∧
      ∀ σ < unitSlope h m, supportingValue h σ =
        ((I.inf' hI (fun n => (h n).untop₀ - σ * n) : ℝ) : EReal) := by
  classical
  let I := (range (m + 1)).filter (fun n => h n ≠ ⊤)
  have hmem (n : ℕ) : n ∈ I ↔ n ≤ m ∧ h n ≠ ⊤ := by
    simp [I]
  have hI : I.Nonempty := ⟨m, (hmem m).mpr ⟨le_rfl, (mem_finiteEdges.mp hm).1⟩⟩
  refine ⟨I, hI, hmem, fun σ hσ => ?_⟩
  obtain ⟨l, u, hf, hum⟩ := hh.exists_isFiniteFace_of_lt_unitSlope hm hσ
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  have hl : l ∈ supportingFace h σ c := hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  have hlfin : h l ≠ ⊤ := by
    rw [mem_supportingFace] at hl
    rw [hl]
    exact WithTop.coe_ne_top
  have hlreal : (h l).untop₀ - σ * l = c := by
    rw [mem_supportingFace] at hl
    rw [hl, WithTop.untop₀_coe]
    ring
  rw [supportingValue_eq_coe_of_mem_supportingFace hc hl, EReal.coe_eq_coe_iff]
  apply le_antisymm
  · apply le_inf'
    intro n hn
    have hcn := coe_le_supportingValue_iff_untop₀.mp (isSupportingLine_iff.mp hc)
      n ((hmem n).mp hn).2
    linarith
  · exact (I.inf'_le _ ((hmem l).mpr ⟨hf.left_le_right.trans hum, hlfin⟩)).trans_eq hlreal

/-- The real supporting value of a convex height sequence is continuous at all slopes
strictly below the slope of a specified finite edge, with no bounded-domain assumption. -/
theorem IsConvexSeq.continuousOn_supportingValue_toReal (hh : IsConvexSeq h)
    {m : ℕ} (hm : m ∈ finiteEdges h) :
    ContinuousOn (fun σ => (supportingValue h σ).toReal) (Iio (unitSlope h m)) := by
  obtain ⟨I, hI, _, heq⟩ := hh.exists_finset_supportingValue_eq_inf' hm
  apply (TauCeti.continuousOn_supportingValue_toReal h).mono
  apply isOpen_Iio.subset_interior_iff.mpr
  intro σ hσ
  simp only [Set.mem_ofPred_eq]
  rw [heq σ hσ]
  exact EReal.coe_ne_bot _

end TauCeti
