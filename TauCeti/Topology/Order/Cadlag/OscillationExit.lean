/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.WithTop
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import TauCeti.Topology.Order.Cadlag
import Mathlib.Order.Interval.Set.Union
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Topology.Order.LeftRight

/-!
# Oscillation exit times and step approximations for càdlàg paths

For any path `f` into a pseudometric space and threshold `ε : ℝ`,
`TauCeti.oscillationExitAfter f ε u` takes the infimum of times strictly after `u` at which `f` or
its strict left limit deviates by at least `ε` from `f u.untopA` (or `⊤` when no such time
exists), and `TauCeti.oscillationExit f ε` iterates this operation from `⊥`. For a càdlàg path in
an order topology and `ε > 0`, each finite exit time lies strictly after the previous one and
attains the `ε`-deviation threshold; between consecutive times the path stays strictly within `ε` of
the left-endpoint value, and existence of left limits prevents infinitely many `ε`-exits from
accumulating below any finite horizon (`IsCadlag.tendsto_oscillationExit_top`). In a
second-countable order topology with a conditionally complete linear order with bottom, each
horizon `T` admits a single countable subset characterizing `{oscillationExitAfter ≤ ↑T}` via an
extended-distance supremum (`TauCeti.exists_countable_subset_Iic_oscillationExitAfter_le_coe_iff`).

Freezing `f` at each exit time `τ_n` on `[τ_n, τ_{n+1})` defines the deterministic step
approximation `TauCeti.oscillationApprox f ε` (falling back to `f t` outside their union), which
stays strictly within distance `ε` of `f` at every time for `ε > 0`
(`TauCeti.dist_oscillationApprox_lt`), converges uniformly to `f` as `ε → 0⁺`
(`TauCeti.tendstoUniformly_oscillationApprox`), and preserves the càdlàg property
(`IsCadlag.oscillationApprox`).

## References

* P. Billingsley, *Convergence of Probability Measures*, second edition, Wiley, 1999, §12, Lemma 1.
* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, Chapter IV, §64.
-/

public section

open Filter Function Set TopologicalSpace
open scoped ENNReal Topology

namespace TauCeti

section OscillationExit

section OneStep

variable {X E : Type*} [ConditionallyCompleteLinearOrder X] [Nonempty X] [PseudoMetricSpace E]

/-- The infimum of times `t` strictly after `u` at which `f t` or its strict left limit
`f.leftLim t` lies at distance at least `ε` from `f u.untopA`, or `⊤` when no such time exists
(in particular when `u = ⊤`). For arbitrary `f` and `ε`, this infimum need neither lie strictly
after `u` nor attain the threshold; for a càdlàg path in an order topology with `ε > 0`, it
advances strictly whenever `u ≠ ⊤` (`IsCadlag.lt_oscillationExitAfter`), and any finite value
attains the `ε`-deviation threshold in value or strict left limit
(`IsCadlag.lt_and_le_dist_of_oscillationExitAfter_eq_coe`). -/
noncomputable def oscillationExitAfter (f : X → E) (ε : ℝ) (u : WithTop X) : WithTop X :=
  open Classical in
  let A := {t : X | u < (t : WithTop X) ∧
    (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}
  if A.Nonempty then ↑(sInf A) else ⊤

@[simp]
theorem oscillationExitAfter_top (f : X → E) (ε : ℝ) :
    oscillationExitAfter f ε ⊤ = ⊤ := by
  simp [oscillationExitAfter]

/-- `oscillationExitAfter f ε u` equals `⊤` if and only if no strictly later time reaches
distance `ε` from `f u.untopA` in value or strict left limit. -/
theorem oscillationExitAfter_eq_top_iff {f : X → E} {ε : ℝ} {u : WithTop X} :
    oscillationExitAfter f ε u = ⊤ ↔
      ∀ t : X, u < (t : WithTop X) →
        dist (f t) (f u.untopA) < ε ∧ dist (f.leftLim t) (f u.untopA) < ε := by
  classical
  dsimp only [oscillationExitAfter]
  split_ifs with hne
  · simp only [WithTop.coe_ne_top, false_iff, not_forall, not_and_or, not_lt]
    obtain ⟨t, ht1, ht2⟩ := hne
    exact ⟨t, ht1, ht2⟩
  · simp only [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, not_and, not_or, not_le] at hne
    exact ⟨fun _ => hne, fun _ => rfl⟩

/-- When some time strictly after `u` attains the `ε`-deviation threshold in value or strict left
limit, `oscillationExitAfter f ε u` is the infimum of all such times. -/
theorem oscillationExitAfter_eq_coe_csInf {f : X → E} {ε : ℝ} {u : WithTop X}
    (hne : {t : X | u < (t : WithTop X) ∧
      (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}.Nonempty) :
    oscillationExitAfter f ε u =
      ↑(sInf {t : X | u < (t : WithTop X) ∧
        (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}) := by
  classical
  simp [oscillationExitAfter, hne]

/-- Any time strictly after `u` at which `f` or its strict left limit deviates by at least `ε` from
`f u.untopA` is an upper bound for `oscillationExitAfter f ε u`. -/
theorem oscillationExitAfter_le_coe_of_le_dist {f : X → E} {ε : ℝ} {u : WithTop X} {t : X}
    (hut : u < (t : WithTop X))
    (hdev : ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA)) :
    oscillationExitAfter f ε u ≤ (t : WithTop X) := by
  rw [oscillationExitAfter_eq_coe_csInf ⟨t, hut, hdev⟩, WithTop.coe_le_coe]
  cases u with
  | top => exact (not_top_lt hut).elim
  | coe a => exact csInf_le ⟨a, fun _ hs => (WithTop.coe_lt_coe.mp hs.1).le⟩ ⟨hut, hdev⟩

/-- The next oscillation exit time never precedes the starting time. -/
theorem le_oscillationExitAfter (f : X → E) (ε : ℝ) (u : WithTop X) :
    u ≤ oscillationExitAfter f ε u := by
  by_cases hne : {t : X | u < (t : WithTop X) ∧
      (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}.Nonempty
  · rw [oscillationExitAfter_eq_coe_csInf hne]
    cases u with
    | top => obtain ⟨t, ht, _⟩ := hne; exact (not_top_lt ht).elim
    | coe a =>
      exact WithTop.coe_le_coe.mpr
        (le_csInf hne fun t ht => (WithTop.coe_lt_coe.mp ht.1).le)
  · simp only [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, not_and, not_or, not_le] at hne
    rw [oscillationExitAfter_eq_top_iff.mpr hne]
    exact le_top

/-- For `ε > 0`, at any time `t` with `u ≤ t` strictly before `oscillationExitAfter f ε u`,
the path remains within strict distance `ε` of `f u.untopA`. -/
theorem dist_lt_of_lt_oscillationExitAfter {f : X → E} {ε : ℝ} (hε : 0 < ε)
    {u : WithTop X} {t : X} (hut : u ≤ (t : WithTop X))
    (hlt : (t : WithTop X) < oscillationExitAfter f ε u) :
    dist (f t) (f u.untopA) < ε := by
  rcases eq_or_lt_of_le hut with rfl | hut'
  · simpa using hε
  · by_contra! hge
    exact not_le_of_gt hlt (oscillationExitAfter_le_coe_of_le_dist hut' (Or.inl hge))

private noncomputable def stoppedEdist (f : X → E) (u : WithTop X) (t : X) : ℝ≥0∞ :=
  edist (f t) (f (min (t : WithTop X) u).untopA)

private theorem stoppedEdist_apply (f : X → E) (u : WithTop X) (t : X) :
    stoppedEdist f u t = edist (f t) (f (min (t : WithTop X) u).untopA) :=
  rfl

private theorem stoppedEdist_coe_apply (f : X → E) (a t : X) :
    stoppedEdist f a t = edist (f t) (f (min t a)) := by
  rw [stoppedEdist_apply, ← WithTop.coe_min]
  simp only [WithTop.untopA, WithTop.untopD_coe]

private theorem stoppedEdist_top (f : X → E) :
    stoppedEdist f ⊤ = fun _ => (0 : ℝ≥0∞) := by
  ext t
  simp [stoppedEdist]

variable [TopologicalSpace X] [OrderTopology X]

private theorem isCadlag_stoppedEdist {f : X → E} (hf : IsCadlag f) (u : WithTop X) :
    IsCadlag (stoppedEdist f u) := by
  cases u with
  | top =>
    rw [stoppedEdist_top]
    exact IsCadlag.const
  | coe a =>
    have heq : stoppedEdist f a = fun t => edist (f t) (f (min t a)) :=
      funext (stoppedEdist_coe_apply f a)
    rw [heq]
    exact hf.continuous_comp₂ (hf.comp_min_const a) continuous_edist

private theorem setOf_oscillation_eq_stoppedEdist {f : X → E} (hf : IsCadlag f) {ε : ℝ}
    (hε : 0 < ε) (u : WithTop X) :
    {t : X | u < (t : WithTop X) ∧
        (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))} =
      {t : X | ENNReal.ofReal ε ≤ stoppedEdist f u t ∨
        ENNReal.ofReal ε ≤ (stoppedEdist f u).leftLim t} := by
  ext t
  simp only [mem_ofPred_eq]
  have hε_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  cases u with
  | top =>
    simp [stoppedEdist_top, continuous_const.continuousWithinAt.leftLim_eq, not_le_of_gt hε_pos]
  | coe a =>
    rcases le_or_gt t a with hta | hat
    · have hval : stoppedEdist f a t = 0 := by
        rw [stoppedEdist_coe_apply, min_eq_left hta, edist_self]
      have hlim : (stoppedEdist f a).leftLim t = 0 := by
        rcases eq_or_neBot (𝓝[<] t) with hbot | _
        · rw [leftLim_eq_of_eq_bot _ hbot, hval]
        · refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [stoppedEdist_coe_apply, min_eq_left ((le_of_lt hs).trans hta), edist_self]
      simp [not_lt_of_ge (WithTop.coe_le_coe.mpr hta), hval, hlim, not_le_of_gt hε_pos]
    · have hval : stoppedEdist f a t = edist (f t) (f a) := by
        rw [stoppedEdist_coe_apply, min_eq_right hat.le]
      have hlim : (stoppedEdist f a).leftLim t = edist (f.leftLim t) (f a) := by
        rcases eq_or_neBot (𝓝[<] t) with hbot | _
        · rw [leftLim_eq_of_eq_bot _ hbot, leftLim_eq_of_eq_bot _ hbot, hval]
        · refine leftLim_eq_of_tendsto
            ((((continuous_id.edist continuous_const).tendsto (f.leftLim t)).comp
              (hf.tendsto_nhdsLT_leftLim t)).congr' ?_)
          filter_upwards [Ioo_mem_nhdsLT hat] with s hs
          rw [stoppedEdist_coe_apply, min_eq_right hs.1.le]
          simp only [Function.comp_apply, id_eq]
      simp [WithTop.coe_lt_coe.mpr hat, hval, hlim, edist_dist,
        ENNReal.ofReal_le_ofReal_iff dist_nonneg]

end OneStep

section Iterated

variable {X E : Type*} [ConditionallyCompleteLinearOrderBot X] [PseudoMetricSpace E]

/-- Iterated `ε`-oscillation exit times of a path `f`, obtained by iterating
`oscillationExitAfter f ε` starting from `⊥`. -/
noncomputable def oscillationExit (f : X → E) (ε : ℝ) : ℕ → WithTop X
  | 0 => (⊥ : X)
  | n + 1 => oscillationExitAfter f ε (oscillationExit f ε n)

@[simp]
theorem oscillationExit_zero (f : X → E) (ε : ℝ) :
    oscillationExit f ε 0 = ((⊥ : X) : WithTop X) :=
  (rfl)

@[simp]
theorem oscillationExit_succ (f : X → E) (ε : ℝ) (n : ℕ) :
    oscillationExit f ε (n + 1) = oscillationExitAfter f ε (oscillationExit f ε n) :=
  (rfl)

/-- Iterated oscillation exit times form a nondecreasing sequence. -/
theorem oscillationExit_mono (f : X → E) (ε : ℝ) : Monotone (oscillationExit f ε) :=
  monotone_nat_of_le_succ fun n => le_oscillationExitAfter f ε (oscillationExit f ε n)

end Iterated

end OscillationExit

end TauCeti

namespace IsCadlag

section OscillationExit

section OneStep

variable {X E : Type*} [ConditionallyCompleteLinearOrder X] [Nonempty X]
  [TopologicalSpace X] [OrderTopology X] [PseudoMetricSpace E]

/-- When a càdlàg path has a finite `ε`-oscillation exit time `s` after `u` (`ε > 0`), `s` lies
strictly after `u` and attains the `ε`-deviation threshold in value or strict left limit. -/
theorem lt_and_le_dist_of_oscillationExitAfter_eq_coe {f : X → E} (hf : IsCadlag f) {ε : ℝ}
    (hε : 0 < ε) {u : WithTop X} {s : X} (hs : TauCeti.oscillationExitAfter f ε u = s) :
    u < (s : WithTop X) ∧
      (ε ≤ dist (f s) (f u.untopA) ∨ ε ≤ dist (f.leftLim s) (f u.untopA)) := by
  let A := {t : X | u < (t : WithTop X) ∧
    (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}
  have hne : A.Nonempty := by
    by_contra h
    simp only [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, not_and, not_or, not_le, A] at h
    have htop := TauCeti.oscillationExitAfter_eq_top_iff.mpr h
    rw [hs] at htop
    exact WithTop.coe_ne_top htop
  have hbdd : BddBelow A := by
    cases u with
    | top => obtain ⟨t, ht, _⟩ := hne; exact (not_top_lt ht).elim
    | coe a => exact ⟨a, fun _ ht => (WithTop.coe_lt_coe.mp ht.1).le⟩
  have hs_eq : s = sInf A := by
    rw [TauCeti.oscillationExitAfter_eq_coe_csInf hne] at hs
    exact (WithTop.coe_eq_coe.mp hs).symm
  have hA_eq := TauCeti.setOf_oscillation_eq_stoppedEdist hf hε u
  have hmem : sInf A ∈ A := by
    dsimp only [A]
    rw [hA_eq]
    exact isClosed_Ici.csInf_mem_or_leftLim_mem_of_continuousWithinAt
      ((TauCeti.isCadlag_stoppedEdist hf u).isRightContinuous _) (hA_eq ▸ hne) (hA_eq ▸ hbdd)
  exact hs_eq ▸ hmem

/-- After any finite time `u`, the next `ε`-oscillation exit (`ε > 0`) of a càdlàg path occurs
strictly later, including when it is `⊤`. -/
theorem lt_oscillationExitAfter {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    {u : WithTop X} (hu : u ≠ ⊤) : u < TauCeti.oscillationExitAfter f ε u := by
  cases h : TauCeti.oscillationExitAfter f ε u with
  | top => exact lt_top_iff_ne_top.mpr hu
  | coe s => exact (hf.lt_and_le_dist_of_oscillationExitAfter_eq_coe hε h).1

/-- For a càdlàg path and `ε > 0`, the next `ε`-oscillation exit occurs by `T` if and only if an
actual `ε`-deviation in value or left limit occurs at some time in `(u, T]`. -/
theorem oscillationExitAfter_le_coe_iff {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    (u : WithTop X) (T : X) :
    TauCeti.oscillationExitAfter f ε u ≤ (T : WithTop X) ↔
      ∃ t ≤ T, u < (t : WithTop X) ∧
        (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA)) := by
  constructor
  · intro hle
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    have hmem := hf.lt_and_le_dist_of_oscillationExitAfter_eq_coe hε hs.symm
    exact ⟨s, WithTop.coe_le_coe.mp (hs ▸ hle), hmem⟩
  · rintro ⟨t, htT, hut, hdev⟩
    exact (TauCeti.oscillationExitAfter_le_coe_of_le_dist hut hdev).trans
      (WithTop.coe_le_coe.mpr htT)

end OneStep

end OscillationExit

end IsCadlag

namespace TauCeti

/-- In a second-countable order topology with a conditionally complete linear order with bottom,
each horizon `T` admits a single countable subset `S ⊆ (-∞, T]` that characterizes the sublevel
event `oscillationExitAfter f ε u ≤ T` for every càdlàg path `f`, threshold `ε > 0`, and starting
time `u` via a countable supremum of extended distances. -/
theorem exists_countable_subset_Iic_oscillationExitAfter_le_coe_iff
    {X E : Type*} [ConditionallyCompleteLinearOrderBot X] [TopologicalSpace X]
    [OrderTopology X] [SecondCountableTopology X] [PseudoMetricSpace E] (T : X) :
    ∃ S : Set X, S.Countable ∧ S ⊆ Iic T ∧
      ∀ ⦃f : X → E⦄, IsCadlag f → ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ (u : WithTop X),
        oscillationExitAfter f ε u ≤ (T : WithTop X) ↔
          ENNReal.ofReal ε ≤
            ⨆ s ∈ S, edist (f s) (f (min (s : WithTop X) u).untopA) := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_biSup_eq (α := ℝ≥0∞) T
  refine ⟨S, hSc, hST, fun f hf ε hε u => ?_⟩
  have hT : IsCompact (Iic T) := by
    rw [← Icc_bot]
    exact isCompact_Icc
  have hset := Set.ext_iff.mp (setOf_oscillation_eq_stoppedEdist hf hε u)
  simp only [mem_ofPred_eq] at hset
  rw [hf.oscillationExitAfter_le_coe_iff hε u T]
  simp_rw [hset]
  rw [(isCadlag_stoppedEdist hf u).exists_le_or_le_leftLim_iff_le_biSup hT (ENNReal.ofReal ε),
    ← hS fun t _ => (isCadlag_stoppedEdist hf u).isRightContinuous t]
  simp only [stoppedEdist_apply]

end TauCeti

namespace IsCadlag

section Iterated

variable {X E : Type*} [ConditionallyCompleteLinearOrderBot X] [TopologicalSpace X]
  [OrderTopology X] [PseudoMetricSpace E]

/-- A càdlàg path has only finitely many `ε`-oscillation exits (`ε > 0`) on `[⊥, T]`: its iterated
exit times eventually lie strictly beyond `T`. -/
theorem eventually_lt_oscillationExit {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    (T : X) : ∀ᶠ n in atTop, (T : WithTop X) < TauCeti.oscillationExit f ε n := by
  suffices ∃ N, (T : WithTop X) < TauCeti.oscillationExit f ε N by
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans_le (TauCeti.oscillationExit_mono f ε hn)
  -- Otherwise all exit times are finite, strictly increasing, and bounded above by `T`.
  by_contra! hle
  have hne_top (n : ℕ) : TauCeti.oscillationExit f ε n ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hle n)
  choose t ht using fun n => WithTop.ne_top_iff_exists.mp (hne_top n)
  have ht_le (n : ℕ) : t n ≤ T := WithTop.coe_le_coe.mp (ht n ▸ hle n)
  have ht_strict : StrictMono t := strictMono_nat_of_lt_succ fun n => by
    have hlt := hf.lt_oscillationExitAfter hε (hne_top n)
    rw [← TauCeti.oscillationExit_succ, ← ht n, ← ht (n + 1)] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  -- Their supremum `s ≤ T` is approached strictly from the left, where `f` tends to `f.leftLim s`.
  have hbdd : BddAbove (range t) := ⟨T, forall_mem_range.mpr ht_le⟩
  let s : X := ⨆ n, t n
  have ht_lt_s (n : ℕ) : t n < s := (ht_strict (Nat.lt_succ_self n)).trans_le (le_ciSup hbdd _)
  have ht_nhds : Tendsto t atTop (𝓝 s) := tendsto_atTop_ciSup ht_strict.monotone hbdd
  have ht_nhdsLT : Tendsto t atTop (𝓝[<] s) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ht_nhds
      (Eventually.of_forall ht_lt_s)
  have : (𝓝[<] s).NeBot := neBot_of_le ht_nhdsLT
  have hball : {x | dist (f x) (f.leftLim s) < ε / 3} ∈ 𝓝[<] s :=
    (hf.tendsto_nhdsLT_leftLim s).eventually
      ((continuous_id.dist continuous_const).isOpen_preimage _ isOpen_Iio |>.mem_nhds
        (by simp [div_pos hε zero_lt_three]))
  obtain ⟨u, hus, hu⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset' (ht_lt_s 0)).mp hball
  -- Once `t N ∈ (u, s)`, `f (t N)`, `f (t (N + 1))`, and `f.leftLim (t (N + 1))` all lie within
  -- `ε / 3` of `f.leftLim s`, contradicting the `ε`-threshold at `t (N + 1)`.
  obtain ⟨N, hN⟩ := (ht_nhds.eventually (Ioi_mem_nhds hus)).exists
  have hN_mem : t N ∈ Ioo u s := ⟨hN, ht_lt_s N⟩
  have hN1_mem : t (N + 1) ∈ Ioo u s := ⟨hN.trans (ht_strict (Nat.lt_succ_self N)), ht_lt_s _⟩
  have hd_N : dist (f (t N)) (f.leftLim s) < ε / 3 := hu hN_mem
  have hd_N1 : dist (f (t (N + 1))) (f.leftLim s) < ε / 3 := hu hN1_mem
  have hd_lim : dist (f.leftLim (t (N + 1))) (f.leftLim s) ≤ ε / 3 := by
    rcases eq_or_neBot (𝓝[<] (t (N + 1))) with hbot | _
    · rw [leftLim_eq_of_eq_bot f hbot]
      exact hd_N1.le
    · refine le_of_tendsto
        (((continuous_id.dist continuous_const).tendsto _).comp
          (hf.tendsto_nhdsLT_leftLim (t (N + 1)))) ?_
      filter_upwards [Ioo_mem_nhdsLT hN1_mem.1] with x hx
      exact (hu ⟨hx.1, hx.2.trans hN1_mem.2⟩).le
  have hexit : TauCeti.oscillationExitAfter f ε (t N) = t (N + 1) := by
    rw [ht N, ht (N + 1), TauCeti.oscillationExit_succ]
  rcases (hf.lt_and_le_dist_of_oscillationExitAfter_eq_coe hε hexit).2 with hval | hleft
  · simp only [WithTop.untopA, WithTop.untopD_coe] at hval
    have htri := dist_triangle_right (f (t (N + 1))) (f (t N)) (f.leftLim s)
    linarith
  · simp only [WithTop.untopA, WithTop.untopD_coe] at hleft
    have htri := dist_triangle_right (f.leftLim (t (N + 1))) (f (t N)) (f.leftLim s)
    linarith

/-- Iterated `ε`-oscillation exit times (`ε > 0`) of a càdlàg path tend to `⊤`. -/
theorem tendsto_oscillationExit_top {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (TauCeti.oscillationExit f ε) atTop (𝓝 ⊤) :=
  (WithTop.tendsto_nhds_top_iff _).mpr (hf.eventually_lt_oscillationExit hε)

end Iterated

end IsCadlag

namespace TauCeti

section Approx

variable {ι E : Type*} [ConditionallyCompleteLinearOrderBot ι] [PseudoMetricSpace E]

open scoped Classical in
/-- Piecewise-constant step approximation of `f` frozen at each iterated `ε`-oscillation exit
time `τ_n` on the half-open interval `[τ_n, τ_{n+1})`, and falling back to `f t` outside their
union. On càdlàg paths in an order topology for `ε > 0`, these intervals partition `ι`, so the
fallback value `f t` is never used. -/
noncomputable def oscillationApprox (f : ι → E) (ε : ℝ) (t : ι) : E :=
  if h : ∃ n, oscillationExit f ε n ≤ (t : WithTop ι) ∧
      (t : WithTop ι) < oscillationExit f ε (n + 1) then
    f (oscillationExit f ε h.choose).untopA
  else
    f t

/-- On the `n`-th half-open oscillation interval `[τ_n, τ_{n+1})`, `oscillationApprox f ε`
equals `f` evaluated at `τ_n`. -/
theorem oscillationApprox_eq_of_mem_Ico {f : ι → E} {ε : ℝ} {t : ι} {n : ℕ}
    (hle : oscillationExit f ε n ≤ (t : WithTop ι))
    (hlt : (t : WithTop ι) < oscillationExit f ε (n + 1)) :
    oscillationApprox f ε t = f (oscillationExit f ε n).untopA := by
  have hex : ∃ k, oscillationExit f ε k ≤ (t : WithTop ι) ∧
      (t : WithTop ι) < oscillationExit f ε (k + 1) := ⟨n, hle, hlt⟩
  have hchoose : hex.choose = n := by
    by_contra hne
    exact Set.disjoint_left.mp
      ((oscillationExit_mono f ε).pairwise_disjoint_on_Ico_succ hne)
      hex.choose_spec ⟨hle, hlt⟩
  simp only [oscillationApprox, hex, ↓reduceDIte, hchoose]

/-- Outside the half-open oscillation intervals `[τ_n, τ_{n+1})`, `oscillationApprox f ε` falls
back to `f`. -/
theorem oscillationApprox_eq_of_not_exists {f : ι → E} {ε : ℝ} {t : ι}
    (h : ¬ ∃ n, oscillationExit f ε n ≤ (t : WithTop ι) ∧
      (t : WithTop ι) < oscillationExit f ε (n + 1)) :
    oscillationApprox f ε t = f t := by
  simp only [oscillationApprox, h, ↓reduceDIte]

/-- At the initial time `⊥`, the oscillation step approximation agrees with `f`. -/
@[simp]
theorem oscillationApprox_bot (f : ι → E) (ε : ℝ) :
    oscillationApprox f ε ⊥ = f ⊥ := by
  by_cases hex : ∃ n, oscillationExit f ε n ≤ ((⊥ : ι) : WithTop ι) ∧
      ((⊥ : ι) : WithTop ι) < oscillationExit f ε (n + 1)
  · obtain ⟨n, hle, hlt⟩ := hex
    have hbot : oscillationExit f ε n = ((⊥ : ι) : WithTop ι) :=
      le_antisymm hle
        (oscillationExit_zero f ε ▸ oscillationExit_mono f ε (Nat.zero_le n))
    rw [oscillationApprox_eq_of_mem_Ico hle hlt, hbot]
    simp only [WithTop.untopA, WithTop.untopD_coe]
  · exact oscillationApprox_eq_of_not_exists hex

/-- For any path `f` and `ε > 0`, `oscillationApprox f ε` stays within strict distance `ε` of `f`
at every time. -/
theorem dist_oscillationApprox_lt (f : ι → E) {ε : ℝ} (hε : 0 < ε) (t : ι) :
    dist (f t) (oscillationApprox f ε t) < ε := by
  by_cases hex : ∃ n, oscillationExit f ε n ≤ (t : WithTop ι) ∧
      (t : WithTop ι) < oscillationExit f ε (n + 1)
  · obtain ⟨n, hle, hlt⟩ := hex
    rw [oscillationApprox_eq_of_mem_Ico hle hlt]
    rw [oscillationExit_succ] at hlt
    exact dist_lt_of_lt_oscillationExitAfter hε hle hlt
  · rw [oscillationApprox_eq_of_not_exists hex, dist_self]
    exact hε

/-- Along any filter of thresholds that are eventually positive and converge to `0`, the
oscillation step approximations converge uniformly to `f`. -/
theorem tendstoUniformly_oscillationApprox {κ : Type*} (f : ι → E) {p : Filter κ}
    {δ : κ → ℝ} (hpos : ∀ᶠ k in p, 0 < δ k) (hδ : Tendsto δ p (𝓝 0)) :
    TendstoUniformly (fun k ↦ oscillationApprox f (δ k)) f p := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hpos, hδ.eventually (Iio_mem_nhds hε)] with k hk_pos hk_lt t
  exact (dist_oscillationApprox_lt f hk_pos t).trans hk_lt

end Approx

end TauCeti

namespace IsCadlag

section Approx

variable {ι E : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  [OrderTopology ι] [PseudoMetricSpace E] {f : ι → E}

/-- Every time `t` lies in the half-open interval `[τ_n, τ_{n+1})` for some index `n` of the
iterated `ε`-oscillation exit times (`ε > 0`) of a càdlàg path. -/
theorem exists_mem_Ico_oscillationExit (hc : IsCadlag f) {ε : ℝ} (hε : 0 < ε) (t : ι) :
    ∃ n, TauCeti.oscillationExit f ε n ≤ (t : WithTop ι) ∧
      (t : WithTop ι) < TauCeti.oscillationExit f ε (n + 1) := by
  obtain ⟨N, hN⟩ := (hc.eventually_lt_oscillationExit hε t).exists
  obtain ⟨n, _, hle, hlt⟩ := mem_iUnion₂.mp (Ico_subset_biUnion_Ico N
    (TauCeti.oscillationExit f ε) ⟨TauCeti.oscillationExit_zero f ε ▸ bot_le, hN⟩)
  exact ⟨n, hle, hlt⟩

/-- For `ε > 0`, the oscillation step approximation of a càdlàg path is itself càdlàg. -/
theorem oscillationApprox (hc : IsCadlag f) {ε : ℝ} (hε : 0 < ε) :
    IsCadlag (TauCeti.oscillationApprox f ε) where
  isRightContinuous t := by
    -- On `[t, τ_{n+1})`, the step approximation is locally constant equal to `f (τ_n)`.
    obtain ⟨n, hle, hlt⟩ := hc.exists_mem_Ico_oscillationExit hε t
    let c := f (TauCeti.oscillationExit f ε n).untopA
    have hval : TauCeti.oscillationApprox f ε t = c :=
      TauCeti.oscillationApprox_eq_of_mem_Ico hle hlt
    refine (continuousWithinAt_const (b := c)).congr_of_eventuallyEq ?_ hval
    cases hnext : TauCeti.oscillationExit f ε (n + 1) with
    | top =>
      filter_upwards [self_mem_nhdsWithin] with s hs
      refine TauCeti.oscillationApprox_eq_of_mem_Ico
        (hle.trans (WithTop.coe_le_coe.mpr hs.le)) ?_
      rw [hnext]
      exact WithTop.coe_lt_top s
    | coe b =>
      have htb : t < b := WithTop.coe_lt_coe.mp (hnext ▸ hlt)
      filter_upwards [Ioo_mem_nhdsGT htb] with s hs
      refine TauCeti.oscillationApprox_eq_of_mem_Ico
        (hle.trans (WithTop.coe_le_coe.mpr hs.1.le)) ?_
      rw [hnext]
      exact WithTop.coe_lt_coe.mpr hs.2
  tendsto_nhdsLT t := by
    -- Left of `t`, the approximation is constant on `(τ_{n-1}, t)` if `t = τ_n` and on `(τ_n, t)`
    -- if `τ_n < t`.
    obtain ⟨n, hle, hlt⟩ := hc.exists_mem_Ico_oscillationExit hε t
    rcases eq_or_lt_of_le hle with heq | hlt_left
    · rcases n with _ | k
      · rw [TauCeti.oscillationExit_zero] at heq
        have ht : t = ⊥ := (WithTop.coe_eq_coe.mp heq).symm
        subst ht
        exact ⟨f ⊥, by simp⟩
      · have hne_top_succ : TauCeti.oscillationExit f ε (k + 1) ≠ ⊤ := by
          rw [heq]
          exact WithTop.coe_ne_top
        have hne_top_k : TauCeti.oscillationExit f ε k ≠ ⊤ := by
          intro htop
          apply hne_top_succ
          rw [TauCeti.oscillationExit_succ, htop, TauCeti.oscillationExitAfter_top]
        have hk_lt : TauCeti.oscillationExit f ε k < (t : WithTop ι) := by
          simpa only [← TauCeti.oscillationExit_succ, heq] using
            hc.lt_oscillationExitAfter hε hne_top_k
        obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne_top_k
        have hat : a < t := WithTop.coe_lt_coe.mp (ha ▸ hk_lt)
        refine ⟨f (TauCeti.oscillationExit f ε k).untopA, ?_⟩
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT hat] with s hs
        symm
        exact TauCeti.oscillationApprox_eq_of_mem_Ico
          (ha ▸ WithTop.coe_le_coe.mpr hs.1.le) (heq ▸ WithTop.coe_lt_coe.mpr hs.2)
    · obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt_left)
      have hat : a < t := WithTop.coe_lt_coe.mp (ha ▸ hlt_left)
      refine ⟨f (TauCeti.oscillationExit f ε n).untopA, ?_⟩
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hat] with s hs
      symm
      exact TauCeti.oscillationApprox_eq_of_mem_Ico
        (ha ▸ WithTop.coe_le_coe.mpr hs.1.le) ((WithTop.coe_lt_coe.mpr hs.2).trans hlt)

end Approx

end IsCadlag
