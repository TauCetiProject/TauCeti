/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Supporting
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.OrdConnectedLinear
import Mathlib.Tactic.Linarith

/-!
# Finite faces of convex height sequences

A supporting line of slope `σ` lies below every height of a sequence. Its supporting face is
the set of indices where equality holds. For a convex height sequence this contact set is order
connected. Consequently, whenever it is finite and nonempty it has unique absolute endpoints
and consists of every integer between them.

The predicate `IsFiniteFace h σ l u` records these endpoints while leaving the supporting
intercept implicit. The intercept is nevertheless unique, and equals the supporting value at
`σ`. In particular, every nonempty convex height sequence with bounded finite domain has a
finite face at every real slope. These absolute endpoints are the geometric interface later used
to identify extremal coefficients and count slope multiplicities.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

namespace TauCeti

/-- A real affine line of slope `σ` and intercept `c` supports `h` from below. -/
def IsSupportingLine (h : ℕ → WithTop ℝ) (σ c : ℝ) : Prop :=
  ∀ n : ℕ, (((c + σ * n : ℝ) : WithTop ℝ) ≤ h n)

/-- A line supports a height sequence exactly when its intercept is at most the
supporting value. -/
theorem isSupportingLine_iff {h : ℕ → WithTop ℝ} {σ c : ℝ} :
    IsSupportingLine h σ c ↔ (c : EReal) ≤ supportingValue h σ :=
  coe_le_supportingValue_iff.symm

/-- The supporting face cut out by a specified affine supporting line. -/
def supportingFace (h : ℕ → WithTop ℝ) (σ c : ℝ) : Set ℕ :=
  {n | h n = ((c + σ * n : ℝ) : WithTop ℝ)}

/-- Membership in a supporting face means equality with its affine line. -/
@[simp] theorem mem_supportingFace {h : ℕ → WithTop ℝ} {σ c : ℝ} {n : ℕ} :
    n ∈ supportingFace h σ c ↔ h n = ((c + σ * n : ℝ) : WithTop ℝ) :=
  Iff.rfl

/-- Contact with a supporting line identifies its intercept with the supporting value. -/
theorem supportingValue_eq_coe_of_mem_supportingFace {h : ℕ → WithTop ℝ} {σ c : ℝ}
    (hc : IsSupportingLine h σ c) {n : ℕ} (hn : n ∈ supportingFace h σ c) :
    supportingValue h σ = (c : EReal) := by
  apply le_antisymm
  · refine (supportingValue_le h σ n).trans_eq ?_
    rw [mem_supportingFace] at hn
    rw [hn, WithTop.toEReal_coe, ← EReal.coe_sub]
    congr 1
    ring
  · exact isSupportingLine_iff.mp hc

/-- The contact indices of a supporting line on a convex height sequence are order connected. -/
theorem IsConvexSeq.ordConnected_supportingFace {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {σ c : ℝ} (hc : IsSupportingLine h σ c) :
    (supportingFace h σ c).OrdConnected := by
  refine ⟨fun i hi k hk j hj ↦ ?_⟩
  rw [mem_supportingFace] at hi hk ⊢
  rcases eq_or_lt_of_le (hj.1.trans hj.2) with hik | hik
  · have hij : i = j := le_antisymm hj.1 (hik ▸ hj.2)
    subst j
    exact hi
  have hi_top : h i ≠ ⊤ := by rw [hi]; exact WithTop.coe_ne_top
  have hk_top : h k ≠ ⊤ := by rw [hk]; exact WithTop.coe_ne_top
  have hj_top := hh.ne_top_of_le_of_le hi_top hk_top hj.1 hj.2
  have hchord := hh.chord_inequality hi_top hk_top hj.1 hj.2
  have hi_real : (h i).untop₀ = c + σ * i := by
    rw [hi]
    exact WithTop.untop₀_coe _
  have hk_real : (h k).untop₀ = c + σ * k := by
    rw [hk]
    exact WithTop.untop₀_coe _
  rw [hi_real, hk_real] at hchord
  have hupper : (h j).untop₀ ≤ c + σ * j := by
    have hpos : (0 : ℝ) < k - i := sub_pos.mpr (Nat.cast_lt.mpr hik)
    nlinarith
  have hlower := hc j
  rw [← WithTop.coe_untop₀_of_ne_top hj_top, WithTop.coe_le_coe] at hlower
  rw [← WithTop.coe_untop₀_of_ne_top hj_top, WithTop.coe_eq_coe]
  exact le_antisymm hupper hlower

/-- A finite face of slope `σ` has absolute endpoints `l ≤ u`, and the contact set of
its supporting line is exactly the integer interval `[l, u]`. -/
def IsFiniteFace (h : ℕ → WithTop ℝ) (σ : ℝ) (l u : ℕ) : Prop :=
  l ≤ u ∧ ∃ c : ℝ,
    IsSupportingLine h σ c ∧ supportingFace h σ c = Set.Icc l u

namespace IsFiniteFace

variable {h : ℕ → WithTop ℝ} {σ : ℝ} {l u : ℕ}

/-- The left endpoint of a finite face is at most its right endpoint. -/
theorem left_le_right (hf : IsFiniteFace h σ l u) : l ≤ u :=
  hf.1

/-- A finite face admits a supporting intercept whose full contact set is its endpoint
interval. -/
theorem exists_intercept (hf : IsFiniteFace h σ l u) :
    ∃ c : ℝ, IsSupportingLine h σ c ∧ supportingFace h σ c = Set.Icc l u :=
  hf.2

/-- The intercept cutting out a finite face is unique. -/
theorem existsUnique_intercept (hf : IsFiniteFace h σ l u) :
    ∃! c : ℝ, IsSupportingLine h σ c ∧ supportingFace h σ c = Set.Icc l u := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  refine ⟨c, ⟨hc, hface⟩, fun d hd ↦ ?_⟩
  have hlc : l ∈ supportingFace h σ c := hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  have hld : l ∈ supportingFace h σ d := hd.2.symm.subset ⟨le_rfl, hf.left_le_right⟩
  have hcval := supportingValue_eq_coe_of_mem_supportingFace hc hlc
  have hdval := supportingValue_eq_coe_of_mem_supportingFace hd.1 hld
  exact_mod_cast hdval.symm.trans hcval

/-- A finite face's supporting value is its unique real intercept. -/
theorem existsUnique_supportingValue_eq (hf : IsFiniteFace h σ l u) :
    ∃! c : ℝ, supportingValue h σ = (c : EReal) := by
  obtain ⟨c, hc, hface⟩ := hf.existsUnique_intercept.exists
  have hl : l ∈ supportingFace h σ c := hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  refine ⟨c, supportingValue_eq_coe_of_mem_supportingFace hc hl, fun d hd ↦ ?_⟩
  exact_mod_cast hd.symm.trans (supportingValue_eq_coe_of_mem_supportingFace hc hl)

/-- A finite face has unique absolute endpoints. -/
theorem unique (hf : IsFiniteFace h σ l u) {l' u' : ℕ}
    (hf' : IsFiniteFace h σ l' u') : l = l' ∧ u = u' := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  obtain ⟨d, hd, hface'⟩ := hf'.exists_intercept
  have hlc : l ∈ supportingFace h σ c := hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  have hl'd : l' ∈ supportingFace h σ d := hface'.symm.subset ⟨le_rfl, hf'.left_le_right⟩
  have hcd : c = d := EReal.coe_injective
    ((supportingValue_eq_coe_of_mem_supportingFace hc hlc).symm.trans
      (supportingValue_eq_coe_of_mem_supportingFace hd hl'd))
  subst d
  exact (Set.Icc_eq_Icc_iff hf.left_le_right).mp (hface.symm.trans hface')

end IsFiniteFace

/-- A finite nonempty supporting face of a convex height sequence has absolute endpoints. -/
theorem IsConvexSeq.exists_isFiniteFace_of_finite_supportingFace {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {σ c : ℝ} (hc : IsSupportingLine h σ c)
    (hfinite : (supportingFace h σ c).Finite)
    (hne : (supportingFace h σ c).Nonempty) :
    ∃ l u : ℕ, IsFiniteFace h σ l u := by
  let s := supportingFace h σ c
  have hsconn : s.OrdConnected := hh.ordConnected_supportingFace hc
  have hsbdd : BddAbove s := hfinite.bddAbove
  have hseq : s = Set.Icc (sInf s) (sSup s) :=
    (hne.ordConnected_iff_of_bdd (OrderBot.bddBelow s) hsbdd).mp hsconn
  have hle : sInf s ≤ sSup s :=
    Nat.sInf_le (Nat.sSup_mem hne hsbdd)
  exact ⟨sInf s, sSup s, hle, c, hc, hseq⟩

/-- Every nonempty convex height sequence with a bounded finite domain has a finite face at
each real slope. The resulting endpoints are absolute indices in the original sequence. -/
theorem IsConvexSeq.exists_isFiniteFace_of_finiteDomain_eq_Icc {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {a b : ℕ} (hab : a ≤ b)
    (hdom : ∀ n : ℕ, h n ≠ ⊤ ↔ a ≤ n ∧ n ≤ b) (σ : ℝ) :
    ∃ l u : ℕ, IsFiniteFace h σ l u := by
  let values : Set ℝ :=
    (fun n : ℕ ↦ (h n).untop₀ - σ * n) '' Set.Icc a b
  have hvalues_finite : values.Finite := Set.finite_Icc a b |>.image _
  have hvalues_nonempty : values.Nonempty :=
    ⟨(h a).untop₀ - σ * a, a, ⟨le_rfl, hab⟩, rfl⟩
  have hvalues_bdd : BddBelow values := hvalues_finite.bddBelow
  let c := sInf values
  have hc_mem : c ∈ values := hvalues_nonempty.csInf_mem hvalues_finite
  have hc : IsSupportingLine h σ c := by
    intro n
    by_cases hn : a ≤ n ∧ n ≤ b
    · have hn_top : h n ≠ ⊤ := (hdom n).mpr hn
      rw [← WithTop.coe_untop₀_of_ne_top hn_top, WithTop.coe_le_coe]
      have hle : c ≤ (h n).untop₀ - σ * n :=
        csInf_le hvalues_bdd ⟨n, hn, rfl⟩
      linarith
    · have hn_top : h n = ⊤ := not_ne_iff.mp (mt (hdom n).mp hn)
      simp [hn_top]
  have hface_finite : (supportingFace h σ c).Finite := by
    refine Set.Finite.subset (Set.finite_Icc a b) fun n hn ↦ ?_
    rw [mem_supportingFace] at hn
    exact (hdom n).mp (by rw [hn]; exact WithTop.coe_ne_top)
  have hface_nonempty : (supportingFace h σ c).Nonempty := by
    obtain ⟨n, hn, hnc⟩ := hc_mem
    refine ⟨n, ?_⟩
    rw [mem_supportingFace]
    have hn_top : h n ≠ ⊤ := (hdom n).mpr hn
    rw [← WithTop.coe_untop₀_of_ne_top hn_top, WithTop.coe_eq_coe]
    dsimp [c] at hnc
    linarith
  exact hh.exists_isFiniteFace_of_finite_supportingFace hc hface_finite hface_nonempty

/-- Every nonempty convex height sequence with finite domain has a finite face at each real
slope. No endpoints for the finite domain need to be supplied. -/
theorem IsConvexSeq.exists_isFiniteFace_of_finiteDomain {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) (hfinite : {n | h n ≠ ⊤}.Finite)
    (hne : {n | h n ≠ ⊤}.Nonempty) (σ : ℝ) :
    ∃ l u : ℕ, IsFiniteFace h σ l u := by
  let s := {n | h n ≠ ⊤}
  have hsbdd : BddAbove s := hfinite.bddAbove
  have hseq : s = Set.Icc (sInf s) (sSup s) :=
    (hne.ordConnected_iff_of_bdd (OrderBot.bddBelow s) hsbdd).mp hh.ordConnected
  have hle : sInf s ≤ sSup s := Nat.sInf_le (Nat.sSup_mem hne hsbdd)
  apply hh.exists_isFiniteFace_of_finiteDomain_eq_Icc hle
  intro n
  change n ∈ s ↔ sInf s ≤ n ∧ n ≤ sSup s
  simpa only [Set.mem_Icc] using Set.ext_iff.mp hseq n

end TauCeti
