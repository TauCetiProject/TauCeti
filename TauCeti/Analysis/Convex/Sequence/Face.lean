/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Supporting
public import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Order.Interval.Set.OrdConnectedLinear
import Mathlib.Tactic.Linarith

/-!
# Finite faces of convex height sequences

A supporting line of slope `σ` lies below every height of a sequence. Its supporting face is
the set of indices where equality holds. A sequence with a finite nonempty domain, convex or
not, touches a supporting line of every slope and has a least contact index with it. For a
convex height sequence the contact set is order connected. Consequently, whenever it is finite
and nonempty it has unique absolute endpoints and consists of every integer between them.

The predicate `IsFiniteFace h σ l u` records these endpoints while leaving the supporting
intercept implicit. The intercept is nevertheless unique, and equals the supporting value at
`σ`. In particular, every nonempty convex height sequence with bounded finite domain has a
finite face at every real slope. Without convexity, a sequence with only finitely many finite
heights still has no supporting value `⊥`. A finite edge whose slope is strictly greater than
`σ` also guarantees a finite face of slope `σ`, with both endpoints at or before that edge.
Thus unbounded finite edge slopes guarantee finite faces at every real slope, even on an
unbounded domain. Finite unit slopes before a finite face are strictly less than its slope,
on the face they equal its slope, and after it they are strictly greater. Consequently, on a
domain with a first finite index, a finite face's left and right endpoints count the unit
slopes respectively below and at most the face slope. These absolute endpoints are the
geometric interface later used to identify extremal coefficients and count slope multiplicities.

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

/-- A line through a finite height supports a convex sequence exactly when its slope
lies between the adjacent finite unit slopes. A missing adjacent edge imposes no bound. -/
theorem IsConvexSeq.isSupportingLine_iff_unitSlope {h : ℕ → WithTop ℝ}
    (hh : IsConvexSeq h) {n : ℕ} (hn : h n ≠ ⊤) (σ : ℝ) :
    IsSupportingLine h σ ((h n).untop₀ - σ * n) ↔
      (∀ i, i + 1 = n → h i ≠ ⊤ → unitSlope h i ≤ σ) ∧
      (h (n + 1) ≠ ⊤ → σ ≤ unitSlope h n) := by
  constructor
  · intro hc
    constructor
    · intro i hi hif
      have hb := hc i
      rw [← WithTop.coe_untop₀_of_ne_top hif, WithTop.coe_le_coe] at hb
      rw [unitSlope_def, hi]
      have hcast : (i : ℝ) + 1 = n := by exact_mod_cast hi
      rw [← hcast] at hb
      nlinarith
    · intro hn'
      have hb := hc (n + 1)
      rw [← WithTop.coe_untop₀_of_ne_top hn', WithTop.coe_le_coe] at hb
      simp only [unitSlope_def, Nat.cast_add, Nat.cast_one] at hb ⊢
      linarith
  · rintro ⟨hleft, hright⟩ k
    by_cases hk : h k = ⊤
    · simp [hk]
    rw [← WithTop.coe_untop₀_of_ne_top hk, WithTop.coe_le_coe]
    rcases lt_trichotomy k n with hkn | rfl | hnk
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have hi : h i ≠ ⊤ := hh.ne_top_of_le_of_le hk hn (by omega) (by omega)
      have hs := hh.sub_le_mul_slope hk hn hi hn hkn.le le_rfl
      have hb := hleft i rfl hi
      rw [Nat.cast_sub hkn.le] at hs
      have hdiff : (0 : ℝ) ≤ (i + 1 : ℕ) - (k : ℝ) :=
        sub_nonneg.mpr (Nat.cast_le.mpr hkn.le)
      nlinarith
    · simp
    · have hn' := hh.ne_top_of_le_of_le hn hk (Nat.le_succ n) hnk
      have hs := hh.mul_slope_le_sub hn hk hn hn' hnk.le le_rfl
      have hb := hright hn'
      rw [Nat.cast_sub hnk.le] at hs
      have hdiff : 0 ≤ (k : ℝ) - n := sub_nonneg.mpr (Nat.cast_le.mpr hnk.le)
      nlinarith

/-- The supporting face cut out by a specified affine supporting line. -/
def supportingFace (h : ℕ → WithTop ℝ) (σ c : ℝ) : Set ℕ :=
  {n | h n = ((c + σ * n : ℝ) : WithTop ℝ)}

/-- Membership in a supporting face means equality with its affine line. -/
@[simp] theorem mem_supportingFace {h : ℕ → WithTop ℝ} {σ c : ℝ} {n : ℕ} :
    n ∈ supportingFace h σ c ↔ h n = ((c + σ * n : ℝ) : WithTop ℝ) :=
  Iff.rfl

/-- The intercept of a line of slope `σ` through a point of a height sequence bounds its
supporting value of slope `σ`. The line need not be a supporting line. -/
theorem supportingValue_le_coe_of_mem_supportingFace {h : ℕ → WithTop ℝ} {σ c : ℝ} {n : ℕ}
    (hn : n ∈ supportingFace h σ c) : supportingValue h σ ≤ (c : EReal) := by
  refine (supportingValue_le h σ n).trans_eq ?_
  rw [mem_supportingFace] at hn
  rw [hn, WithTop.toEReal_coe, ← EReal.coe_sub]
  congr 1
  ring

/-- Contact with a supporting line identifies its intercept with the supporting value. -/
theorem supportingValue_eq_coe_of_mem_supportingFace {h : ℕ → WithTop ℝ} {σ c : ℝ}
    (hc : IsSupportingLine h σ c) {n : ℕ} (hn : n ∈ supportingFace h σ c) :
    supportingValue h σ = (c : EReal) :=
  le_antisymm (supportingValue_le_coe_of_mem_supportingFace hn) (isSupportingLine_iff.mp hc)

/-- A height sequence with a finite nonempty domain touches a supporting line of every slope,
and has a least contact index with it. The sequence need not be convex, so the contact set
need not be an interval. -/
theorem exists_isSupportingLine_isLeast_supportingFace {h : ℕ → WithTop ℝ}
    (hfinite : {n | h n ≠ ⊤}.Finite) (hne : {n | h n ≠ ⊤}.Nonempty) (σ : ℝ) :
    ∃ (c : ℝ) (i : ℕ), IsSupportingLine h σ c ∧ IsLeast (supportingFace h σ c) i := by
  obtain ⟨i, hi, hmin⟩ := hfinite.toFinset.exists_min_image (fun n => (h n).untop₀ - σ * n)
    (hfinite.toFinset_nonempty.mpr hne)
  rw [Set.Finite.mem_toFinset] at hi
  have hface : i ∈ supportingFace h σ ((h i).untop₀ - σ * i) := by
    rw [mem_supportingFace, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hi]
  refine ⟨(h i).untop₀ - σ * i, sInf (supportingFace h σ ((h i).untop₀ - σ * i)), fun n => ?_,
    Nat.sInf_mem ⟨i, hface⟩, fun k hk => Nat.sInf_le hk⟩
  by_cases hn : h n = ⊤
  · simp [hn]
  rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe]
  linarith [hmin n (hfinite.mem_toFinset.mpr hn)]

/-- A height sequence with only finitely many finite heights has no supporting value `⊥`. -/
theorem supportingValue_ne_bot_of_finite {h : ℕ → WithTop ℝ} (hfin : {n | h n ≠ ⊤}.Finite)
    (σ : ℝ) : supportingValue h σ ≠ ⊥ := by
  rcases Set.eq_empty_or_nonempty {n | h n ≠ ⊤} with hemp | hne
  · have htop : h = ⊤ := funext fun n => not_ne_iff.mp fun hn => by simpa using hemp.subset hn
    simp [htop]
  obtain ⟨c, -, hc, -⟩ := exists_isSupportingLine_isLeast_supportingFace hfin hne σ
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot c) (isSupportingLine_iff.mp hc)

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

/-- The line of the face slope through any point of a finite face supports the sequence. -/
theorem isSupportingLine_untop₀_sub (hf : IsFiniteFace h σ l u) {n : ℕ}
    (hn : n ∈ Set.Icc l u) : IsSupportingLine h σ ((h n).untop₀ - σ * n) := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  have hn' : h n = ((c + σ * n : ℝ) : WithTop ℝ) :=
    mem_supportingFace.mp (hface.symm.subset hn)
  rw [hn', WithTop.untop₀_coe, add_sub_cancel_right]
  exact hc

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

/-- The height at the left endpoint of a finite face is finite. -/
theorem left_ne_top (hf : IsFiniteFace h σ l u) : h l ≠ ⊤ := by
  obtain ⟨c, _, hface⟩ := hf.exists_intercept
  have hl : l ∈ supportingFace h σ c :=
    hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  rw [mem_supportingFace] at hl
  rw [hl]
  exact WithTop.coe_ne_top

/-- The height at the right endpoint of a finite face is finite. -/
theorem right_ne_top (hf : IsFiniteFace h σ l u) : h u ≠ ⊤ := by
  obtain ⟨c, _, hface⟩ := hf.exists_intercept
  have hu : u ∈ supportingFace h σ c :=
    hface.symm.subset ⟨hf.left_le_right, le_rfl⟩
  rw [mem_supportingFace] at hu
  rw [hu]
  exact WithTop.coe_ne_top

/-- A finite unit edge strictly before a finite face has slope strictly less than the
face slope. -/
theorem unitSlope_lt (hf : IsFiniteFace h σ l u) (hh : IsConvexSeq h)
    {i : ℕ} (hi : i ∈ finiteEdges h) (hil : i < l) : unitSlope h i < σ := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  have hif := mem_finiteEdges.mp hi
  have hl : l ∈ supportingFace h σ c :=
    hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
  have hl_real : (h l).untop₀ = c + σ * l := by
    rw [mem_supportingFace] at hl
    rw [hl, WithTop.untop₀_coe]
  have hi_lower := hc i
  rw [← WithTop.coe_untop₀_of_ne_top hif.1, WithTop.coe_le_coe] at hi_lower
  have hi_ne : (h i).untop₀ ≠ c + σ * i := by
    intro hi_eq
    have hi_mem : i ∈ supportingFace h σ c := by
      rw [mem_supportingFace, ← WithTop.coe_untop₀_of_ne_top hif.1,
        WithTop.coe_eq_coe, hi_eq]
    have := Set.mem_Icc.mp (hface ▸ hi_mem)
    omega
  have hi_strict : c + σ * i < (h i).untop₀ :=
    lt_of_le_of_ne hi_lower hi_ne.symm
  have hs := hh.mul_slope_le_sub hif.1 hf.left_ne_top hif.1 hif.2 hil.le le_rfl
  rw [hl_real, Nat.cast_sub hil.le] at hs
  have hil_real : (i : ℝ) < l := Nat.cast_lt.mpr hil
  nlinarith

/-- Every unit edge contained in a finite face has slope equal to the face slope. -/
theorem unitSlope_eq (hf : IsFiniteFace h σ l u) {i : ℕ}
    (hli : l ≤ i) (hiu : i < u) : unitSlope h i = σ := by
  obtain ⟨c, _, hface⟩ := hf.exists_intercept
  have hi : i ∈ supportingFace h σ c := hface.symm.subset ⟨hli, hiu.le⟩
  have hi' : i + 1 ∈ supportingFace h σ c :=
    hface.symm.subset ⟨hli.trans (Nat.le_succ i), hiu⟩
  rw [unitSlope_def]
  rw [mem_supportingFace] at hi hi'
  rw [hi, hi', WithTop.untop₀_coe, WithTop.untop₀_coe]
  push_cast
  ring

/-- A finite unit edge at or after the right endpoint of a finite face has slope strictly
greater than the face slope. -/
theorem lt_unitSlope (hf : IsFiniteFace h σ l u) (hh : IsConvexSeq h)
    {i : ℕ} (hi : i ∈ finiteEdges h) (hui : u ≤ i) : σ < unitSlope h i := by
  obtain ⟨c, hc, hface⟩ := hf.exists_intercept
  have hif := mem_finiteEdges.mp hi
  have hu : u ∈ supportingFace h σ c :=
    hface.symm.subset ⟨hf.left_le_right, le_rfl⟩
  have hu_real : (h u).untop₀ = c + σ * u := by
    rw [mem_supportingFace] at hu
    rw [hu, WithTop.untop₀_coe]
  have hi_lower := hc (i + 1)
  rw [← WithTop.coe_untop₀_of_ne_top hif.2, WithTop.coe_le_coe] at hi_lower
  push_cast at hi_lower
  have hi_ne : (h (i + 1)).untop₀ ≠ c + σ * (i + 1) := by
    intro hi_eq
    have hi_mem : i + 1 ∈ supportingFace h σ c := by
      rw [mem_supportingFace, ← WithTop.coe_untop₀_of_ne_top hif.2,
        WithTop.coe_eq_coe, hi_eq]
      norm_num
    have := Set.mem_Icc.mp (hface ▸ hi_mem)
    omega
  have hi_strict : c + σ * (i + 1) < (h (i + 1)).untop₀ :=
    lt_of_le_of_ne hi_lower hi_ne.symm
  have hs := hh.sub_le_mul_slope hf.right_ne_top hif.2 hif.1 hif.2
    (hui.trans (Nat.le_succ i)) le_rfl
  rw [hu_real, Nat.cast_sub (hui.trans (Nat.le_succ i))] at hs
  push_cast at hs
  have hui_real : (u : ℝ) ≤ i := Nat.cast_le.mpr hui
  have hui_succ_real : (u : ℝ) < i + 1 := by
    exact_mod_cast (lt_of_le_of_lt hui (Nat.lt_succ_self i))
  nlinarith

/-- A finite face's left endpoint is the first finite index plus the number of finite unit
slopes strictly below the face slope. The finite domain may be bounded or unbounded. -/
theorem left_eq_start_add_ncard_unitSlope_lt (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) {a : ℕ} (ha : h a ≠ ⊤)
    (hfirst : ∀ n, h n ≠ ⊤ → a ≤ n) :
    l = a + {i | i ∈ finiteEdges h ∧ unitSlope h i < σ}.ncard := by
  have hal : a ≤ l := hfirst l hf.left_ne_top
  have hset : {i | i ∈ finiteEdges h ∧ unitSlope h i < σ} = Set.Ico a l := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hi_edge, hslope⟩
      have hif := mem_finiteEdges.mp hi_edge
      refine ⟨hfirst i hif.1, ?_⟩
      by_contra hil
      have hli : l ≤ i := le_of_not_gt hil
      by_cases hiu : i < u
      · have heq := hf.unitSlope_eq hli hiu
        linarith
      · have hgt := hf.lt_unitSlope hh hi_edge (le_of_not_gt hiu)
        linarith
    · rintro ⟨hai, hil⟩
      have hi : h i ≠ ⊤ := hh.ne_top_of_le_of_le ha hf.left_ne_top hai hil.le
      have hi' : h (i + 1) ≠ ⊤ := hh.ne_top_of_le_of_le ha hf.left_ne_top
        (hai.trans (Nat.le_succ i)) (Nat.succ_le_iff.mpr hil)
      have hi_edge : i ∈ finiteEdges h := mem_finiteEdges.mpr ⟨hi, hi'⟩
      exact ⟨hi_edge, hf.unitSlope_lt hh hi_edge hil⟩
  rw [hset, Set.ncard_Ico_nat]
  omega

/-- A finite face's right endpoint is the first finite index plus the number of finite unit
slopes at most the face slope. The finite domain may be bounded or unbounded. -/
theorem right_eq_start_add_ncard_unitSlope_le (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) {a : ℕ} (ha : h a ≠ ⊤)
    (hfirst : ∀ n, h n ≠ ⊤ → a ≤ n) :
    u = a + {i | i ∈ finiteEdges h ∧ unitSlope h i ≤ σ}.ncard := by
  have hau : a ≤ u := hfirst u hf.right_ne_top
  have hset : {i | i ∈ finiteEdges h ∧ unitSlope h i ≤ σ} = Set.Ico a u := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · rintro ⟨hi_edge, hslope⟩
      have hif := mem_finiteEdges.mp hi_edge
      refine ⟨hfirst i hif.1, ?_⟩
      by_contra hiu
      have hgt := hf.lt_unitSlope hh hi_edge (le_of_not_gt hiu)
      linarith
    · rintro ⟨hai, hiu⟩
      have hi : h i ≠ ⊤ := hh.ne_top_of_le_of_le ha hf.right_ne_top hai hiu.le
      have hi' : h (i + 1) ≠ ⊤ := hh.ne_top_of_le_of_le ha hf.right_ne_top
        (hai.trans (Nat.le_succ i)) (Nat.succ_le_iff.mpr hiu)
      have hi_edge : i ∈ finiteEdges h := mem_finiteEdges.mpr ⟨hi, hi'⟩
      refine ⟨hi_edge, ?_⟩
      by_cases hil : i < l
      · exact (hf.unitSlope_lt hh hi_edge hil).le
      · exact (hf.unitSlope_eq (le_of_not_gt hil) hiu).le
  rw [hset, Set.ncard_Ico_nat]
  omega

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

end TauCeti
