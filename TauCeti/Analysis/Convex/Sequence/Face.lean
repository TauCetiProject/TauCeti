/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import TauCeti.Analysis.Convex.Sequence.Supporting
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Nat
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
finite face at every real slope. A finite edge whose slope is strictly greater than `σ`
also guarantees a finite face of slope `σ`, with both endpoints at or before that edge.
Thus unbounded finite edge slopes guarantee finite faces at every real slope, even on an
unbounded domain.

The endpoints of a finite face of slope `σ` are read off from the finite unit slopes: the
finite edges before `l` are exactly those of slope less than `σ`, the edges inside the face
have slope `σ`, and the edges from `u` onwards have slope greater than `σ`. Hence, for a
sequence whose finite domain starts at `a`, the left endpoint is `a` plus the number of finite
unit slopes less than `σ`, the right endpoint is `a` plus the number at most `σ`, and the
multiplicity of `σ` is `u - l`. Conversely, these slope conditions characterise the face.
These absolute endpoints are the geometric interface later used to identify extremal
coefficients and count slope multiplicities.

## Main results

* `IsConvexSeq.ordConnected_supportingFace`: supporting faces of convex sequences are order
  connected.
* `IsFiniteFace.existsUnique_intercept`, `IsFiniteFace.unique`: a finite face determines its
  supporting intercept and its endpoints.
* `IsConvexSeq.exists_isFiniteFace_of_finiteDomain`,
  `IsConvexSeq.exists_isFiniteFace_of_lt_unitSlope`: existence of finite faces for bounded
  finite domains and below any strictly larger finite slope.
* `IsFiniteFace.unitSlope_lt_iff`, `IsFiniteFace.unitSlope_le_iff`,
  `IsFiniteFace.unitSlope_eq_iff`: the position of a finite edge relative to a finite face is
  determined by comparing its slope with `σ`.
* `IsFiniteFace.left_eq_add_ncard`, `IsFiniteFace.right_eq_add_ncard`: the face endpoints count
  the finite unit slopes less than, respectively at most, `σ`.
* `IsFiniteFace.ncard_setOf_unitSlope_eq`: the multiplicity of the slope `σ` is the horizontal
  length of the face.
* `IsConvexSeq.isFiniteFace_iff_unitSlope`: finite faces are characterised by these slope
  conditions.

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

/-- A line supports a height sequence exactly when it lies below every height. -/
theorem isSupportingLine_iff_forall {h : ℕ → WithTop ℝ} {σ c : ℝ} :
    IsSupportingLine h σ c ↔ ∀ n : ℕ, (((c + σ * n : ℝ) : WithTop ℝ) ≤ h n) :=
  Iff.rfl

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

/-- A finite face is given by ordered endpoints together with a supporting intercept whose
contact set is exactly the endpoint interval. -/
theorem isFiniteFace_iff {h : ℕ → WithTop ℝ} {σ : ℝ} {l u : ℕ} :
    IsFiniteFace h σ l u ↔
      l ≤ u ∧ ∃ c : ℝ, IsSupportingLine h σ c ∧ supportingFace h σ c = Set.Icc l u :=
  Iff.rfl

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
  simpa only [s, Set.mem_ofPred_eq, Set.mem_Icc] using Set.ext_iff.mp hseq n

/-- Contact with a supporting line of slope `σ` occurs at or before any finite edge
whose slope is strictly greater than `σ`. -/
theorem IsConvexSeq.supportingFace_subset_Iic_of_lt_unitSlope {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {σ c : ℝ} (hc : IsSupportingLine h σ c)
    {m : ℕ} (hm : m ∈ finiteEdges h) (hσ : σ < unitSlope h m) :
    supportingFace h σ c ⊆ Set.Iic m := by
  have hmf := mem_finiteEdges.mp hm
  intro n hn
  by_contra hnm
  have hmn : m < n := lt_of_not_ge hnm
  have hn_top : h n ≠ ⊤ := by
    rw [mem_supportingFace] at hn
    rw [hn]
    exact WithTop.coe_ne_top
  have hs := hh.mul_slope_le_sub hmf.1 hn_top hmf.1 hmf.2 hmn.le le_rfl
  rw [Nat.cast_sub hmn.le] at hs
  have hcm := hc m
  rw [← WithTop.coe_untop₀_of_ne_top hmf.1, WithTop.coe_le_coe] at hcm
  have hn_real : (h n).untop₀ = c + σ * n := by
    rw [mem_supportingFace] at hn
    rw [hn, WithTop.untop₀_coe]
  rw [hn_real] at hs
  nlinarith [mul_pos (sub_pos.mpr hσ)
    (sub_pos.mpr (Nat.cast_lt.mpr hmn) : (0 : ℝ) < n - m)]

/-- A finite edge of slope strictly greater than `σ` guarantees a finite nonempty face
of slope `σ`. Its right endpoint, and hence also its left endpoint, is at most the edge
index. The finite domain itself need not be bounded. -/
theorem IsConvexSeq.exists_isFiniteFace_of_lt_unitSlope {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {σ : ℝ} {m : ℕ} (hm : m ∈ finiteEdges h)
    (hσ : σ < unitSlope h m) :
    ∃ l u : ℕ, IsFiniteFace h σ l u ∧ u ≤ m := by
  have hmf := mem_finiteEdges.mp hm
  let s : Set ℕ := {n | n ≤ m ∧ h n ≠ ⊤}
  have hs : s.Finite := (Set.finite_Iic m).subset fun _ hn ↦ hn.1
  obtain ⟨i, hi, hmin⟩ := Set.exists_min_image s
    (fun n ↦ (h n).untop₀ - σ * n) hs ⟨m, le_rfl, hmf.1⟩
  let c := (h i).untop₀ - σ * i
  have hcm : c ≤ (h m).untop₀ - σ * m := hmin m ⟨le_rfl, hmf.1⟩
  have hc : IsSupportingLine h σ c := by
    intro n
    by_cases hn : h n = ⊤
    · simp [hn]
    rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe]
    by_cases hnm : n ≤ m
    · have hcn : c ≤ (h n).untop₀ - σ * n := hmin n ⟨hnm, hn⟩
      linarith
    · have hmn : m ≤ n := (lt_of_not_ge hnm).le
      have htail := hh.mul_slope_le_sub hmf.1 hn hmf.1 hmf.2 hmn le_rfl
      rw [Nat.cast_sub hmn] at htail
      have hprod := mul_nonneg (sub_nonneg.mpr hσ.le)
        (sub_nonneg.mpr (Nat.cast_le.mpr hmn) : (0 : ℝ) ≤ n - m)
      nlinarith
  have hcontact : i ∈ supportingFace h σ c := by
    rw [mem_supportingFace, ← WithTop.coe_untop₀_of_ne_top hi.2, WithTop.coe_eq_coe]
    dsimp [c]
    ring
  have hsub := hh.supportingFace_subset_Iic_of_lt_unitSlope hc hm hσ
  obtain ⟨l, u, hf⟩ := hh.exists_isFiniteFace_of_finite_supportingFace hc
    ((Set.finite_Iic m).subset hsub) ⟨i, hcontact⟩
  refine ⟨l, u, hf, ?_⟩
  obtain ⟨d, hd, hface⟩ := hf.exists_intercept
  exact hh.supportingFace_subset_Iic_of_lt_unitSlope hd hm hσ
    (hface.symm.subset ⟨hf.left_le_right, le_rfl⟩)

/-- Unbounded slopes on the finite edges of a convex height sequence guarantee a
finite nonempty face at every real slope. -/
theorem IsConvexSeq.exists_isFiniteFace_of_unbounded_unitSlope {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) (hunbounded : ¬ BddAbove (unitSlope h '' finiteEdges h))
    (σ : ℝ) : ∃ l u : ℕ, IsFiniteFace h σ l u := by
  obtain ⟨s, ⟨m, hm, rfl⟩, hσ⟩ := not_bddAbove_iff.mp hunbounded σ
  obtain ⟨l, u, hf, _⟩ := hh.exists_isFiniteFace_of_lt_unitSlope hm hσ
  exact ⟨l, u, hf⟩

/-! ### Face endpoints and unit slopes -/

namespace IsFiniteFace

variable {h : ℕ → WithTop ℝ} {σ : ℝ} {l u n : ℕ}

/-- The heights of a finite face lie on a line of slope `σ`, and every other finite height
lies strictly above that line. -/
private theorem exists_line (hf : IsFiniteFace h σ l u) :
    ∃ c : ℝ, (∀ n, l ≤ n → n ≤ u → h n ≠ ⊤ ∧ (h n).untop₀ = c + σ * n) ∧
      ∀ n, h n ≠ ⊤ → n < l ∨ u < n → c + σ * n < (h n).untop₀ := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  refine ⟨c, fun n hln hnu ↦ ?_, fun n hn hout ↦ ?_⟩
  · have hmem : n ∈ supportingFace h σ c := hface.symm.subset ⟨hln, hnu⟩
    rw [mem_supportingFace] at hmem
    rw [hmem, WithTop.untop₀_coe]
    exact ⟨WithTop.coe_ne_top, rfl⟩
  · have hle := hc n
    rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe] at hle
    refine hle.lt_of_ne fun heq ↦ ?_
    have hmem : n ∈ supportingFace h σ c := by
      rw [mem_supportingFace, ← WithTop.coe_untop₀_of_ne_top hn, heq]
    rw [hface, Set.mem_Icc] at hmem
    omega

/-- Every unit edge inside a finite face of slope `σ` has slope `σ`. -/
theorem unitSlope_eq (hf : IsFiniteFace h σ l u) (hln : l ≤ n) (hnu : n < u) :
    unitSlope h n = σ := by
  obtain ⟨c, hon, -⟩ := hf.exists_line
  rw [unitSlope_def, (hon (n + 1) (by omega) hnu).2, (hon n hln hnu.le).2]
  push_cast
  ring

/-- Every finite edge of a convex height sequence before a finite face of slope `σ` has slope
strictly less than `σ`. -/
theorem unitSlope_lt (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (hn : n ∈ finiteEdges h) (hnl : n < l) : unitSlope h n < σ := by
  obtain ⟨c, hon, habove⟩ := hf.exists_line
  have hn' := mem_finiteEdges.mp hn
  obtain ⟨hl, hl_eq⟩ := hon l le_rfl hf.left_le_right
  have hs := hh.mul_slope_le_sub hn'.1 hl hn'.1 hn'.2 hnl.le le_rfl
  rw [Nat.cast_sub hnl.le, hl_eq] at hs
  have hlt := habove n hn'.1 (.inl hnl)
  by_contra hσ
  nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hσ)
    (sub_nonneg.mpr (Nat.cast_le.mpr hnl.le) : (0 : ℝ) ≤ l - n)]

/-- Every finite edge of a convex height sequence starting at or after the right endpoint of a
finite face of slope `σ` has slope strictly greater than `σ`. -/
theorem lt_unitSlope (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (hn : n ∈ finiteEdges h) (hun : u ≤ n) : σ < unitSlope h n := by
  obtain ⟨c, hon, habove⟩ := hf.exists_line
  have hn' := mem_finiteEdges.mp hn
  obtain ⟨hu, hu_eq⟩ := hon u hf.left_le_right le_rfl
  have hs := hh.sub_le_mul_slope hu hn'.2 hn'.1 hn'.2 (by omega) le_rfl
  rw [Nat.cast_sub (by omega), hu_eq] at hs
  have hlt := habove (n + 1) hn'.2 (.inr (by omega))
  push_cast at hs hlt
  by_contra hσ
  nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hσ)
    (sub_nonneg.mpr (by exact_mod_cast (by omega : u ≤ n + 1)) : (0 : ℝ) ≤ n + 1 - u)]

/-- A finite edge of a convex height sequence has slope less than `σ` exactly when it lies
before the finite face of slope `σ`. -/
theorem unitSlope_lt_iff (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (hn : n ∈ finiteEdges h) : unitSlope h n < σ ↔ n < l := by
  refine ⟨fun hlt ↦ ?_, hf.unitSlope_lt hh hn⟩
  by_contra hln
  rcases lt_or_ge n u with hnu | hun
  · exact hlt.ne (hf.unitSlope_eq (le_of_not_gt hln) hnu)
  · exact (hf.lt_unitSlope hh hn hun).not_gt hlt

/-- A finite edge of a convex height sequence has slope at most `σ` exactly when it starts
before the right endpoint of the finite face of slope `σ`. -/
theorem unitSlope_le_iff (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (hn : n ∈ finiteEdges h) : unitSlope h n ≤ σ ↔ n < u := by
  refine ⟨fun hle ↦ ?_, fun hnu ↦ ?_⟩
  · by_contra hun
    exact (hf.lt_unitSlope hh hn (le_of_not_gt hun)).not_ge hle
  · rcases lt_or_ge n l with hnl | hln
    · exact (hf.unitSlope_lt hh hn hnl).le
    · exact (hf.unitSlope_eq hln hnu).le

/-- A finite edge of a convex height sequence has slope `σ` exactly when it lies inside the
finite face of slope `σ`. -/
theorem unitSlope_eq_iff (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (hn : n ∈ finiteEdges h) : unitSlope h n = σ ↔ l ≤ n ∧ n < u := by
  rw [le_antisymm_iff, hf.unitSlope_le_iff hh hn, ← not_lt, hf.unitSlope_lt_iff hh hn, not_lt,
    and_comm]

/-- The finite edges of slope `σ` of a convex height sequence are exactly the unit edges of its
finite face of slope `σ`. In particular, a singleton face carries no edge of slope `σ`. -/
theorem setOf_unitSlope_eq (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u) :
    {n ∈ finiteEdges h | unitSlope h n = σ} = Set.Ico l u := by
  ext n
  refine ⟨fun ⟨hn, heq⟩ ↦ (hf.unitSlope_eq_iff hh hn).mp heq, fun ⟨hln, hnu⟩ ↦ ?_⟩
  obtain ⟨c, hon, -⟩ := hf.exists_line
  exact ⟨mem_finiteEdges.mpr ⟨(hon n hln hnu.le).1, (hon (n + 1) (by omega) hnu).1⟩,
    hf.unitSlope_eq hln hnu⟩

/-- The multiplicity of the slope `σ` among the finite unit slopes of a convex height sequence
is the horizontal length `u - l` of its finite face of slope `σ`. -/
theorem ncard_setOf_unitSlope_eq (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u) :
    {n ∈ finiteEdges h | unitSlope h n = σ}.ncard = u - l := by
  rw [hf.setOf_unitSlope_eq hh, Set.ncard_Ico_nat]

variable {a : ℕ}

/-- For a convex height sequence whose finite domain starts at `a`, the finite edges of slope
less than `σ` are the unit edges from `a` to the left endpoint of the face of slope `σ`. -/
theorem setOf_unitSlope_lt (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (ha : IsLeast {n | h n ≠ ⊤} a) :
    {n ∈ finiteEdges h | unitSlope h n < σ} = Set.Ico a l := by
  ext n
  refine ⟨fun ⟨hn, hlt⟩ ↦ ⟨ha.2 (mem_finiteEdges.mp hn).1,
    (hf.unitSlope_lt_iff hh hn).mp hlt⟩, fun ⟨han, hnl⟩ ↦ ?_⟩
  obtain ⟨c, hon, -⟩ := hf.exists_line
  have hl := (hon l le_rfl hf.left_le_right).1
  have hn : n ∈ finiteEdges h := mem_finiteEdges.mpr
    ⟨hh.ne_top_of_le_of_le ha.1 hl han hnl.le, hh.ne_top_of_le_of_le ha.1 hl (by omega) hnl⟩
  exact ⟨hn, hf.unitSlope_lt hh hn hnl⟩

/-- For a convex height sequence whose finite domain starts at `a`, the finite edges of slope at
most `σ` are the unit edges from `a` to the right endpoint of the face of slope `σ`. -/
theorem setOf_unitSlope_le (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (ha : IsLeast {n | h n ≠ ⊤} a) :
    {n ∈ finiteEdges h | unitSlope h n ≤ σ} = Set.Ico a u := by
  ext n
  refine ⟨fun ⟨hn, hle⟩ ↦ ⟨ha.2 (mem_finiteEdges.mp hn).1,
    (hf.unitSlope_le_iff hh hn).mp hle⟩, fun ⟨han, hnu⟩ ↦ ?_⟩
  obtain ⟨c, hon, -⟩ := hf.exists_line
  have hu := (hon u hf.left_le_right le_rfl).1
  have hn : n ∈ finiteEdges h := mem_finiteEdges.mpr
    ⟨hh.ne_top_of_le_of_le ha.1 hu han hnu.le, hh.ne_top_of_le_of_le ha.1 hu (by omega) hnu⟩
  exact ⟨hn, (hf.unitSlope_le_iff hh hn).mpr hnu⟩

/-- The left endpoint of the finite face of slope `σ` of a convex height sequence whose finite
domain starts at `a` is `a` plus the number of finite unit slopes less than `σ`. -/
theorem left_eq_add_ncard (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (ha : IsLeast {n | h n ≠ ⊤} a) :
    l = a + {n ∈ finiteEdges h | unitSlope h n < σ}.ncard := by
  obtain ⟨c, hon, -⟩ := hf.exists_line
  have hal := ha.2 (hon l le_rfl hf.left_le_right).1
  rw [hf.setOf_unitSlope_lt hh ha, Set.ncard_Ico_nat]
  omega

/-- The right endpoint of the finite face of slope `σ` of a convex height sequence whose finite
domain starts at `a` is `a` plus the number of finite unit slopes at most `σ`. -/
theorem right_eq_add_ncard (hh : IsConvexSeq h) (hf : IsFiniteFace h σ l u)
    (ha : IsLeast {n | h n ≠ ⊤} a) :
    u = a + {n ∈ finiteEdges h | unitSlope h n ≤ σ}.ncard := by
  obtain ⟨c, hon, -⟩ := hf.exists_line
  have hau := ha.2 (hon u hf.left_le_right le_rfl).1
  rw [hf.setOf_unitSlope_le hh ha, Set.ncard_Ico_nat]
  omega

end IsFiniteFace

/-- Under the slope conditions characterising a finite face of slope `σ` with endpoints
`l ≤ u`, finite heights on `[l, u]` lie on the line of slope `σ` through `(l, h l)`, and all
other finite heights lie strictly above it. -/
private theorem IsConvexSeq.untop₀_cmp_of_unitSlope {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h)
    {σ : ℝ} {l u : ℕ} (hl : h l ≠ ⊤) (hu : h u ≠ ⊤) (hlu : l ≤ u)
    (H : ∀ n ∈ finiteEdges h, (unitSlope h n < σ ↔ n < l) ∧ (unitSlope h n ≤ σ ↔ n < u))
    {n : ℕ} (hn : h n ≠ ⊤) :
    (n < l → (h l).untop₀ - σ * l + σ * n < (h n).untop₀) ∧
      (l ≤ n → n ≤ u → (h n).untop₀ = (h l).untop₀ - σ * l + σ * n) ∧
      (u < n → (h l).untop₀ - σ * l + σ * n < (h n).untop₀) := by
  -- Edges between two finite heights are finite.
  have hedge {i j k : ℕ} (hi : h i ≠ ⊤) (hj : h j ≠ ⊤) (hik : i ≤ k) (hkj : k < j) :
      k ∈ finiteEdges h := mem_finiteEdges.mpr
    ⟨hh.ne_top_of_le_of_le hi hj hik hkj.le, hh.ne_top_of_le_of_le hi hj (by omega) hkj⟩
  -- On `[l, u]` the heights are affine of slope `σ`: the edge at `l` has slope at least `σ`
  -- and the edge ending at `k` has slope at most `σ`.
  have hon : ∀ k, l ≤ k → k ≤ u → (h k).untop₀ = (h l).untop₀ - σ * l + σ * k := by
    intro k hlk hku
    rcases eq_or_lt_of_le hlk with rfl | hlk'
    · ring
    have hk := hh.ne_top_of_le_of_le hl hu hlk hku
    have hel := hedge hl hu le_rfl (by omega : l < u)
    have hek := hedge hl hu (by omega : l ≤ k - 1) (by omega : k - 1 < u)
    have hlo := hh.mul_slope_le_sub hl hk (mem_finiteEdges.mp hel).1
      (mem_finiteEdges.mp hel).2 hlk le_rfl
    have hhi := hh.sub_le_mul_slope hl hk (mem_finiteEdges.mp hek).1
      (mem_finiteEdges.mp hek).2 hlk (by omega : k ≤ k - 1 + 1)
    have hsl : σ ≤ unitSlope h l :=
      le_of_not_gt fun h' ↦ absurd ((H l hel).1.mp h') (lt_irrefl l)
    have hsk : unitSlope h (k - 1) ≤ σ := (H (k - 1) hek).2.mpr (by omega)
    rw [Nat.cast_sub hlk] at hlo hhi
    have hpos : (0 : ℝ) ≤ k - l := sub_nonneg.mpr (Nat.cast_le.mpr hlk)
    nlinarith [mul_le_mul_of_nonneg_left hsl hpos, mul_le_mul_of_nonneg_left hsk hpos]
  refine ⟨fun hnl ↦ ?_, hon n, fun hun ↦ ?_⟩
  -- Before `l`, compare with the edge ending at `l`, of slope less than `σ`.
  · have he := hedge hn hl (by omega : n ≤ l - 1) (by omega : l - 1 < l)
    have hs := hh.sub_le_mul_slope hn hl (mem_finiteEdges.mp he).1 (mem_finiteEdges.mp he).2
      hnl.le (by omega : l ≤ l - 1 + 1)
    have hσ : unitSlope h (l - 1) < σ := (H (l - 1) he).1.mpr (by omega)
    rw [Nat.cast_sub hnl.le] at hs
    have hpos : (0 : ℝ) < l - n := sub_pos.mpr (Nat.cast_lt.mpr hnl)
    nlinarith [mul_lt_mul_of_pos_left hσ hpos]
  -- After `u`, compare with the edge starting at `u`, of slope greater than `σ`.
  · have he := hedge hu hn le_rfl hun
    have hs := hh.mul_slope_le_sub hu hn hu (mem_finiteEdges.mp he).2 hun.le le_rfl
    have hσ : σ < unitSlope h u :=
      lt_of_not_ge fun h' ↦ absurd ((H u he).2.mp h') (lt_irrefl u)
    rw [Nat.cast_sub hun.le, hon u hlu le_rfl] at hs
    have hpos : (0 : ℝ) < n - u := sub_pos.mpr (Nat.cast_lt.mpr hun)
    nlinarith [mul_lt_mul_of_pos_left hσ hpos]

/-- Two finite indices `l ≤ u` of a convex height sequence are the endpoints of its finite face
of slope `σ` exactly when the finite edges of slope less than `σ` are those before `l`, and the
finite edges of slope at most `σ` are those before `u`. -/
theorem IsConvexSeq.isFiniteFace_iff_unitSlope {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h)
    {σ : ℝ} {l u : ℕ} (hl : h l ≠ ⊤) (hu : h u ≠ ⊤) (hlu : l ≤ u) :
    IsFiniteFace h σ l u ↔ ∀ n ∈ finiteEdges h,
      (unitSlope h n < σ ↔ n < l) ∧ (unitSlope h n ≤ σ ↔ n < u) := by
  refine ⟨fun hf n hn ↦ ⟨hf.unitSlope_lt_iff hh hn, hf.unitSlope_le_iff hh hn⟩,
    fun H ↦ ⟨hlu, (h l).untop₀ - σ * l, fun n ↦ ?_, Set.ext fun n ↦ ?_⟩⟩
  · by_cases hn : h n = ⊤
    · simp [hn]
    rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe]
    obtain ⟨hlt, heq, hgt⟩ := hh.untop₀_cmp_of_unitSlope hl hu hlu H hn
    rcases lt_or_ge n l with hnl | hln
    · exact (hlt hnl).le
    rcases le_or_gt n u with hnu | hun
    · exact (heq hln hnu).ge
    · exact (hgt hun).le
  · rw [mem_supportingFace, Set.mem_Icc]
    refine ⟨fun hmem ↦ ?_, fun ⟨hln, hnu⟩ ↦ ?_⟩
    · have hn : h n ≠ ⊤ := by rw [hmem]; exact WithTop.coe_ne_top
      rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_eq_coe] at hmem
      obtain ⟨hlt, -, hgt⟩ := hh.untop₀_cmp_of_unitSlope hl hu hlu H hn
      by_contra hout
      rcases lt_or_ge n l with hnl | hln
      · exact (hlt hnl).ne' hmem
      · exact (hgt (by omega)).ne' hmem
    · have hn := hh.ne_top_of_le_of_le hl hu hln hnu
      rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_eq_coe]
      exact (hh.untop₀_cmp_of_unitSlope hl hu hlu H hn).2.1 hln hnu

end TauCeti
