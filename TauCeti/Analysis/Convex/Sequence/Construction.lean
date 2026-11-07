/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.MinimalSlope
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The next contact in the finite minimal-slope construction

For a finite point set with first finite index `p`, the infimum of the slopes of
later secants is attained. The largest index attaining it is exactly the right
endpoint of the first face of the lower convex envelope. This selects the next
contact without retaining redundant collinear vertices. If there are further
points, restarting the construction at that contact gives a strictly larger
slope.

Finiteness of the point set is essential here: for an infinite point set, a
largest coefficient contact can lie on a terminal ray of the envelope.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

variable {a : ℕ → WithTop ℝ} {p b : ℕ}

/-- For a finite point set with a later finite point, the initial minimal slope
cuts out a nontrivial finite face starting at its first finite index. -/
theorem exists_isFiniteFace_sInf_secantSlopes (hfinite : {n | a n ≠ ⊤}.Finite)
    (hp : a p ≠ ⊤) (hfirst : ∀ n < p, a n = ⊤)
    (hne : (secantSlopes a p).Nonempty) :
    ∃ b, p < b ∧ IsFiniteFace (lowerConvexEnvelope a) (sInf (secantSlopes a p)) p b := by
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  have hlast : ∀ n, N < n → a n = ⊤ := by
    intro n hn
    by_contra h
    exact (not_le_of_gt hn) (hN h)
  have ha := isAdmissible_of_forall_gt hlast
  have hh := isLowerConvexEnvelope_lowerConvexEnvelope ha
  let σ := sInf (secantSlopes a p)
  let c := (a p).untop₀ - σ * p
  have hc : IsSupportingLine a σ c := isSupportingLine_sInf_secantSlopes ha hp hfirst
  have hpface : p ∈ supportingFace a σ c := by
    simp only [mem_supportingFace, c, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hp]
  have henvfinite : {n | lowerConvexEnvelope a n ≠ ⊤}.Finite := by
    refine (Set.finite_Iic N).subset fun n hn => ?_
    obtain ⟨i, hi, k, hnk, hai, hak⟩ := (lowerConvexEnvelope_ne_top_iff ha).mp hn
    exact hnk.trans (hN hak)
  obtain ⟨l, b, hf⟩ := hh.isConvexSeq.exists_isFiniteFace_of_finite_supportingFace
    (hh.isSupportingLine_iff.mpr hc)
    (henvfinite.subset fun n hn => ne_top_of_le_ne_top WithTop.coe_ne_top
      (le_of_eq (mem_supportingFace.mp hn)))
    ⟨p, hh.supportingFace_subset hc hpface⟩
  obtain ⟨d, hd, hface⟩ := hf.exists_intercept
  have hcd : c = d := EReal.coe_injective
    ((supportingValue_eq_coe_of_mem_supportingFace (hh.isSupportingLine_iff.mpr hc)
      (hh.supportingFace_subset hc hpface)).symm.trans
      (supportingValue_eq_coe_of_mem_supportingFace hd
        (hface.symm.subset ⟨le_rfl, hf.left_le_right⟩)))
  subst d
  have hp_least : IsLeast (supportingFace (lowerConvexEnvelope a) σ c) p :=
    (hh.isLeast_supportingFace_iff hc).mpr ⟨hpface, fun n hn => by
      by_contra h
      have := mem_supportingFace.mp hn
      rw [hfirst n (not_le.mp h)] at this
      exact WithTop.top_ne_coe this⟩
  have hlp : l = p := le_antisymm
    ((hface.subset hp_least.1).1) (hp_least.2 (hface.symm.subset ⟨le_rfl, hf.left_le_right⟩))
  subst l
  obtain ⟨k, hpk, hk, hmin⟩ := mem_secantSlopes.mp (hne.csInf_mem (finite_secantSlopes hfinite p))
  have hkface : k ∈ supportingFace a σ c :=
    (mem_supportingFace_iff_eq_or_secantSlope_eq hp hfirst _ k).mpr (Or.inr ⟨hpk, hk, hmin.symm⟩)
  exact ⟨b, hpk.trans_le (hface.subset (hh.supportingFace_subset hc hkface)).2, hf⟩

/-- On a finite point set, the right endpoint of the first face is characterised
by being the largest index attaining the minimal secant slope. -/
theorem isFiniteFace_sInf_secantSlopes_iff (hfinite : {n | a n ≠ ⊤}.Finite)
    (hp : a p ≠ ⊤) (hfirst : ∀ n < p, a n = ⊤)
    (hne : (secantSlopes a p).Nonempty) :
    IsFiniteFace (lowerConvexEnvelope a) (sInf (secantSlopes a p)) p b ↔
      IsGreatest {n | p < n ∧ a n ≠ ⊤ ∧
        ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p) =
          sInf (secantSlopes a p)} b := by
  obtain ⟨b₀, hpb₀, hf⟩ := exists_isFiniteFace_sInf_secantSlopes hfinite hp hfirst hne
  have ha := isAdmissible_of_lowerConvexEnvelope_ne_top hf.left_ne_top
  have hh := isLowerConvexEnvelope_lowerConvexEnvelope ha
  obtain ⟨c, hc, hpmin, hbmax⟩ :=
    hh.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hf
  have hc_eq : c = (a p).untop₀ - sInf (secantSlopes a p) * p := by
    have hp_eq := congrArg WithTop.untop₀ (mem_supportingFace.mp hpmin.1)
    rw [WithTop.untop₀_coe] at hp_eq
    linarith
  rw [hc_eq] at hbmax
  have hg : IsGreatest {n | p < n ∧ a n ≠ ⊤ ∧
      ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p) =
        sInf (secantSlopes a p)} b₀ := by
    refine ⟨?_, fun n hn => ?_⟩
    · exact ((mem_supportingFace_iff_eq_or_secantSlope_eq hp hfirst _ b₀).mp hbmax.1).resolve_left
        (ne_of_gt hpb₀)
    · exact hbmax.2 ((mem_supportingFace_iff_eq_or_secantSlope_eq hp hfirst _ n).mpr (Or.inr hn))
  constructor
  · intro hf'
    rwa [(hf'.unique hf).2]
  · intro hg'
    have hbb₀ : b = b₀ := le_antisymm (hg.2 hg'.1) (hg'.2 hg.1)
    rwa [hbb₀]

/-- Restarting the finite minimal-slope construction at the largest minimiser
strictly increases the slope, provided that a later finite point exists. -/
theorem sInf_secantSlopes_lt_sInf_tail_of_isGreatest
    (hfinite : {n | a n ≠ ⊤}.Finite) (hp : a p ≠ ⊤)
    (hfirst : ∀ n < p, a n = ⊤)
    (hb : IsGreatest {n | p < n ∧ a n ≠ ⊤ ∧
      ((a n).untop₀ - (a p).untop₀) / ((n : ℝ) - p) =
        sInf (secantSlopes a p)} b)
    (hlater : (secantSlopes (fun n => a (n + b)) 0).Nonempty) :
    sInf (secantSlopes a p) < sInf (secantSlopes (fun n => a (n + b)) 0) := by
  have hne := secantSlopes_nonempty_iff.mpr ⟨b, hb.1.1, hb.1.2.1⟩
  have hf := (isFiniteFace_sInf_secantSlopes_iff hfinite hp hfirst hne).mpr hb
  have ha := isAdmissible_of_lowerConvexEnvelope_ne_top hf.left_ne_top
  have hh := isLowerConvexEnvelope_lowerConvexEnvelope ha
  have hcontact := hh.eq_right_of_isFiniteFace hf
  obtain ⟨k, hk, hkb⟩ := secantSlopes_nonempty_iff.mp hlater
  have hnext : lowerConvexEnvelope a (b + 1) ≠ ⊤ :=
    hh.isConvexSeq.ne_top_of_le_of_le hf.right_ne_top
      (ne_top_of_le_ne_top hkb (hh.le (k + b))) (by omega) (by omega)
  have hlt := hf.lt_unitSlope hh.isConvexSeq
    (mem_finiteEdges.mpr ⟨hf.right_ne_top, hnext⟩) le_rfl
  rwa [hh.unitSlope_eq_sInf_secantSlopes_tail hcontact hb.1.2.1 hlater] at hlt

end TauCeti
