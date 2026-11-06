/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Basic
public import TauCeti.Analysis.BoundedVariation.Perimeter
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Ball
import TauCeti.MeasureTheory.Measure.Lebesgue.Steiner.Moment
import TauCeti.Analysis.BoundedVariation.Compactness
import TauCeti.Analysis.BoundedVariation.Convex
import TauCeti.MeasureTheory.Measure.InterBall
import TauCeti.MeasureTheory.OuterMeasure.SymmDiff

/-!
# Convergence of successive Steiner symmetrizations to a ball

For unit vectors `e 0, e 1, …`, the successive Steiner symmetrals of a set `s` are
`s, S_{e 0} s, S_{e 1} (S_{e 0} s), …` (`TauCeti.iterateSteinerSymmetrization`). They have the
volume of `s`, and the volume of their symmetric difference with any centered open ball `B` does
not increase along the sequence, since every symmetrization fixes `B` and contracts symmetric
differences.

The main theorem is that a suitable choice of directions makes these symmetrals converge to the
centered ball `B` with the volume of `s`, in the sense that `|S_{e (n-1)} ⋯ S_{e 0} s ∆ B| → 0`,
that is, in `L¹` of the indicators. We prove it for every set in a family `𝒞` that is closed under
all Steiner symmetrizations, consists of null-measurable sets contained in a fixed ball, and has
uniformly bounded perimeter
(`TauCeti.exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball_of_perimeter_le`).
Bounded convex sets form such a family, so the successive symmetrals of every bounded convex set
converge to the centered ball of the same volume
(`Convex.exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball`).

## Strategy

The proof is a compactness argument, going back to Gross for convex bodies, with the second
moment `M(t) = ∫_t ‖x‖²` as the functional that identifies the limit.

* **Limit identification.** Let `m` be the infimum of `M` over all successive symmetrals of `s`.
  The perimeter bound makes a minimizing sequence precompact in measure
  (`TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le`), with a limit `F` of the
  volume of `s` and with `M(F) = m`, because `M` is `R²`-Lipschitz for the volume of symmetric
  differences of sets in `ball 0 R`. If some symmetrization `S_e` moved `F`, it would strictly
  decrease its second moment (`TauCeti.lintegral_norm_sq_steinerSymmetrization_eq_iff`), and
  applying `S_e` along the minimizing sequence would go below `m`. So every symmetrization fixes
  `F` up to a null set, and `F` is a centered ball
  (`TauCeti.exists_ae_eq_ball_of_forall_steinerSymmetrization_ae_eq`). Hence finitely many
  symmetrizations bring `s` arbitrarily close to the ball `B` with its volume.
* **Concatenation.** The same holds for every successive symmetral of `s`, with the same ball.
  Choosing finitely many directions that bring the current symmetral within `1 / (j + 1)` of `B`,
  for `j = 0, 1, …` in turn, produces one sequence of directions along which the distance to `B`
  tends to zero, since it never increases
  (`TauCeti.exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball`).

## References

* W. Gross, *Die Minimaleigenschaft der Kugel*, Monatsh. Math. Phys. **28** (1917), 77–97, for
  the convergence of successive Steiner symmetrizations of convex bodies to a ball.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Successive Steiner symmetrizations -/

/-- The successive Steiner symmetrals of `s` along the unit vectors `e 0, e 1, …`:
`iterateSteinerSymmetrization e he s n` is obtained from `s` by symmetrizing along `e 0`, then
along `e 1`, and so on up to `e (n - 1)`. -/
def iterateSteinerSymmetrization (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1) (s : Set E) : ℕ → Set E
  | 0 => s
  | n + 1 => steinerSymmetrization (e n) (he n) (iterateSteinerSymmetrization e he s n)

variable (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1)

@[simp]
theorem iterateSteinerSymmetrization_zero (s : Set E) :
    iterateSteinerSymmetrization e he s 0 = s := (rfl)

@[simp]
theorem iterateSteinerSymmetrization_succ (s : Set E) (n : ℕ) :
    iterateSteinerSymmetrization e he s (n + 1) =
      steinerSymmetrization (e n) (he n) (iterateSteinerSymmetrization e he s n) := (rfl)

/-- The first `n` successive symmetrals only depend on the first `n` directions. -/
theorem iterateSteinerSymmetrization_congr {e' : ℕ → E} (he' : ∀ k, ‖e' k‖ = 1) (s : Set E)
    {n : ℕ} (h : ∀ k < n, e k = e' k) :
    iterateSteinerSymmetrization e he s n = iterateSteinerSymmetrization e' he' s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : e n = e' n := h n n.lt_succ_self
    rw [iterateSteinerSymmetrization_succ, iterateSteinerSymmetrization_succ,
      ih fun k hk => h k (hk.trans n.lt_succ_self)]
    congr 1

/-- Symmetrizing `n + m` times is symmetrizing `n` times, then `m` more times along the
remaining directions. -/
theorem iterateSteinerSymmetrization_add (s : Set E) (n m : ℕ) :
    iterateSteinerSymmetrization e he s (n + m) =
      iterateSteinerSymmetrization (fun k => e (n + k)) (fun k => he (n + k))
        (iterateSteinerSymmetrization e he s n) m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [← add_assoc, iterateSteinerSymmetrization_succ, ih]; rfl

/-- Directions can be spliced: some sequence of directions agrees with `e` before `N`, and from
there on symmetrizes the `N`-th symmetral along `e'`. -/
theorem exists_iterateSteinerSymmetrization_add_eq (N : ℕ) (e' : ℕ → E) (he' : ∀ k, ‖e' k‖ = 1) :
    ∃ (e'' : ℕ → E) (he'' : ∀ k, ‖e'' k‖ = 1), (∀ k < N, e'' k = e k) ∧
      ∀ s m, iterateSteinerSymmetrization e'' he'' s (N + m) =
        iterateSteinerSymmetrization e' he' (iterateSteinerSymmetrization e he s N) m := by
  refine ⟨fun k => if k < N then e k else e' (k - N), fun k => by
    by_cases hk : k < N <;> simp [hk, he, he'], fun k hk => ite_eq_left hk, fun s m => ?_⟩
  rw [iterateSteinerSymmetrization_add,
    iterateSteinerSymmetrization_congr _ _ he s fun k hk => ite_eq_left hk]
  exact iterateSteinerSymmetrization_congr _ _ he' _ fun k _ => by simp

theorem iterateSteinerSymmetrization_mono (n : ℕ) :
    Monotone fun s => iterateSteinerSymmetrization e he s n := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih => exact fun s u h => steinerSymmetrization_mono (e n) (he n) (ih h)

/-- Centered open balls are fixed by successive Steiner symmetrizations. -/
@[simp]
theorem iterateSteinerSymmetrization_ball_zero (r : ℝ) (n : ℕ) :
    iterateSteinerSymmetrization e he (ball (0 : E) r) n = ball 0 r := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterateSteinerSymmetrization_succ, ih, steinerSymmetrization_ball_zero]

/-- A family closed under Steiner symmetrizations contains all successive symmetrals of its
members. -/
private theorem iterateSteinerSymmetrization_mem {𝒞 : Set (Set E)}
    (hS : ∀ t ∈ 𝒞, ∀ (e : E) (he : ‖e‖ = 1), steinerSymmetrization e he t ∈ 𝒞) {s : Set E}
    (hs : s ∈ 𝒞) (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1) (n : ℕ) :
    iterateSteinerSymmetrization e he s n ∈ 𝒞 := by
  induction n with
  | zero => exact hs
  | succ n ih => exact hS _ ih _ _

variable [MeasurableSpace E] [BorelSpace E]

theorem measurableSet_iterateSteinerSymmetrization {s : Set E} (hs : MeasurableSet s) (n : ℕ) :
    MeasurableSet (iterateSteinerSymmetrization e he s n) := by
  induction n with
  | zero => exact hs
  | succ n ih => exact measurableSet_steinerSymmetrization (e n) (he n) ih

variable [FiniteDimensional ℝ E]

/-- Successive Steiner symmetrizations respect equality up to null sets. -/
theorem iterateSteinerSymmetrization_ae_eq {s u : Set E} (h : s =ᵐ[volume] u) (n : ℕ) :
    iterateSteinerSymmetrization e he s n =ᵐ[volume] iterateSteinerSymmetrization e he u n := by
  induction n with
  | zero => exact h
  | succ n ih => exact steinerSymmetrization_ae_eq (e n) (he n) ih

theorem nullMeasurableSet_iterateSteinerSymmetrization {s : Set E}
    (hs : NullMeasurableSet s volume) (n : ℕ) :
    NullMeasurableSet (iterateSteinerSymmetrization e he s n) volume := by
  induction n with
  | zero => exact hs
  | succ n ih => exact nullMeasurableSet_steinerSymmetrization (e n) (he n) ih

@[simp]
theorem volume_iterateSteinerSymmetrization {s : Set E} (hs : NullMeasurableSet s volume)
    (n : ℕ) : volume (iterateSteinerSymmetrization e he s n) = volume s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterateSteinerSymmetrization_succ, volume_steinerSymmetrization (e n) (he n)
      (nullMeasurableSet_iterateSteinerSymmetrization e he hs n), ih]

/-- Successive Steiner symmetrizations contract the volume of symmetric differences. -/
theorem volume_iterateSteinerSymmetrization_symmDiff_le {s u : Set E}
    (hs : NullMeasurableSet s volume) (hu : NullMeasurableSet u volume) (n : ℕ) :
    volume (iterateSteinerSymmetrization e he s n ∆ iterateSteinerSymmetrization e he u n) ≤
      volume (s ∆ u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (volume_steinerSymmetrization_symmDiff_le (e n) (he n)
      (nullMeasurableSet_iterateSteinerSymmetrization e he hs n)
      (nullMeasurableSet_iterateSteinerSymmetrization e he hu n)).trans ih

/-- The volume of the symmetric difference of the successive symmetrals with a centered open
ball does not increase. -/
theorem antitone_volume_iterateSteinerSymmetrization_symmDiff_ball {s : Set E}
    (hs : NullMeasurableSet s volume) (r : ℝ) :
    Antitone fun n => volume (iterateSteinerSymmetrization e he s n ∆ ball (0 : E) r) := by
  refine antitone_nat_of_succ_le fun n => ?_
  have h := volume_steinerSymmetrization_symmDiff_le (e n) (he n)
    (nullMeasurableSet_iterateSteinerSymmetrization e he hs n)
    measurableSet_ball.nullMeasurableSet (u := ball (0 : E) r)
  rwa [steinerSymmetrization_ball_zero, ← iterateSteinerSymmetrization_succ] at h

/-! ### Concatenating finitely many symmetrizations -/

/-- **Diagonal splicing.** If the stages `σ j` are sequences such that `σ (j + 1)` agrees with
`σ j` on its first `N j` terms, and `N` is strictly increasing, then a single sequence agrees with
every stage `σ j` on its first `N j` terms. -/
private theorem exists_forall_lt_eq_of_strictMono {α : Type*} (σ : ℕ → ℕ → α) {N : ℕ → ℕ}
    (hN : StrictMono N) (hσ : ∀ j, ∀ k < N j, σ (j + 1) k = σ j k) :
    ∃ e : ℕ → α, ∀ j, ∀ k < N j, e k = σ j k := by
  -- Later stages keep the terms of earlier stages.
  have hstable {j j' : ℕ} (hjj' : j ≤ j') {k : ℕ} (hk : k < N j) : σ j' k = σ j k := by
    induction j', hjj' using Nat.le_induction with
    | base => rfl
    | succ j' hjj' ih => exact (hσ j' k (hk.trans_le (hN.monotone hjj'))).trans ih
  refine ⟨fun k => σ (k + 1) k, fun j k hk => ?_⟩
  rcases le_total (k + 1) j with hkj | hjk
  · exact (hstable hkj ((Nat.lt_succ_self k).trans_le (hN.id_le (k + 1)))).symm
  · exact hstable hjk hk

/-- **Concatenation of finite approximations.** Suppose that from every successive Steiner
symmetral of a null-measurable set `s`, finitely many further symmetrizations reach sets
arbitrarily close in volume to the centered ball `B = ball 0 r`. Then a single sequence of
directions makes the successive symmetrals of `s` converge to `B`:
`|S_{e (n-1)} ⋯ S_{e 0} s ∆ B| → 0`. -/
theorem exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball [Nontrivial E]
    {s : Set E} (hs : NullMeasurableSet s volume) {r : ℝ}
    (h : ∀ (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1) (n : ℕ), ∀ ε > 0,
      ∃ (e' : ℕ → E) (he' : ∀ k, ‖e' k‖ = 1) (m : ℕ),
        volume (iterateSteinerSymmetrization e' he' (iterateSteinerSymmetrization e he s n) m ∆
          ball 0 r) < ε) :
    ∃ (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1),
      Tendsto (fun n => volume (iterateSteinerSymmetrization e he s n ∆ ball (0 : E) r))
        atTop (𝓝 0) := by
  -- Directions are sequences of unit vectors, and `d e n` is the distance to `B` after `n` steps.
  let D := {e : ℕ → E // ∀ k, ‖e k‖ = 1}
  let d : D → ℕ → ℝ≥0∞ := fun e n =>
    volume (iterateSteinerSymmetrization e.1 e.2 s n ∆ ball (0 : E) r)
  have h' (e : D) (n j : ℕ) : ∃ (e' : D) (m : ℕ),
      volume (iterateSteinerSymmetrization e'.1 e'.2 (iterateSteinerSymmetrization e.1 e.2 s n) m ∆
        ball 0 r) < ((j : ℝ≥0∞) + 1)⁻¹ := by
    obtain ⟨e', he', m, hm⟩ := h e.1 e.2 n ((j : ℝ≥0∞) + 1)⁻¹ (ENNReal.inv_pos.2 (by simp))
    exact ⟨⟨e', he'⟩, m, hm⟩
  choose f m hf using h'
  -- Splicing `e'` after the first `N` terms of `e`.
  have h'' (e : D) (N : ℕ) (e' : D) : ∃ e'' : D, (∀ k < N, e''.1 k = e.1 k) ∧
      ∀ m, iterateSteinerSymmetrization e''.1 e''.2 s (N + m) =
        iterateSteinerSymmetrization e'.1 e'.2 (iterateSteinerSymmetrization e.1 e.2 s N) m := by
    obtain ⟨e'', he'', h₁, h₂⟩ := exists_iterateSteinerSymmetrization_add_eq e.1 e.2 N e'.1 e'.2
    exact ⟨⟨e'', he''⟩, h₁, h₂ s⟩
  choose splice hsplice_lt hsplice_add using h''
  -- Stage `j` consists of directions `σ j` and a number `N j` of steps after which the distance
  -- to `B` is less than `1 / j`; stage `j + 1` appends the directions chosen from there.
  obtain ⟨e₀, he₀⟩ := exists_norm_eq E zero_le_one
  let step : ℕ → D × ℕ → D × ℕ := fun j p =>
    (splice p.1 p.2 (f p.1 p.2 j), p.2 + m p.1 p.2 j + 1)
  let σ : ℕ → D × ℕ := fun j => Nat.rec (motive := fun _ => D × ℕ) (⟨fun _ => e₀, fun _ => he₀⟩, 0)
    (fun j p => step j p) j
  have hσ (j : ℕ) : σ (j + 1) = step j (σ j) := rfl
  have hN : StrictMono fun j => (σ j).2 := strictMono_nat_of_lt_succ fun j => by
    rw [hσ]
    simp only [step]
    omega
  -- The diagonal sequence of directions agrees with stage `j` on its first `N j` terms.
  obtain ⟨e', he_eq⟩ := exists_forall_lt_eq_of_strictMono (fun j => (σ j).1.1) hN
    fun j k hk => by rw [hσ]; exact hsplice_lt _ _ _ k hk
  let e : D := ⟨e', fun k => by
    rw [he_eq (k + 1) k ((Nat.lt_succ_self k).trans_le (hN.id_le (k + 1)))]
    exact (σ (k + 1)).1.2 k⟩
  -- After the steps of stage `j + 1`, the distance to `B` is less than `1 / (j + 1)`.
  have hstep (j : ℕ) (p : D × ℕ) (q : D) (hq : ∀ k < (step j p).2, q.1 k = (step j p).1.1 k) :
      d q (step j p).2 < ((j : ℝ≥0∞) + 1)⁻¹ := by
    obtain ⟨e', N⟩ := p
    dsimp only [d, step] at hq ⊢
    rw [iterateSteinerSymmetrization_congr q.1 q.2 (splice e' N (f e' N j)).2 s hq, add_assoc,
      hsplice_add]
    exact (antitone_volume_iterateSteinerSymmetrization_symmDiff_ball _ _
      (nullMeasurableSet_iterateSteinerSymmetrization _ _ hs _) r (Nat.le_succ _)).trans_lt
        (hf e' N j)
  have hd_stage (j : ℕ) : d e (σ (j + 1)).2 < ((j : ℝ≥0∞) + 1)⁻¹ := by
    have := hstep j (σ j) e fun k hk => he_eq (j + 1) k (by rwa [hσ])
    rwa [← hσ] at this
  refine ⟨e.1, e.2, ENNReal.tendsto_atTop_zero.2 fun ε hε => ?_⟩
  obtain ⟨j, hj⟩ := ENNReal.exists_inv_nat_lt hε.ne'
  refine ⟨(σ (j + 1)).2, fun n hn => ?_⟩
  calc d e n ≤ d e (σ (j + 1)).2 :=
        antitone_volume_iterateSteinerSymmetrization_symmDiff_ball _ _ hs r hn
    _ ≤ ((j : ℝ≥0∞) + 1)⁻¹ := (hd_stage j).le
    _ ≤ (j : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
    _ ≤ ε := hj.le

/-! ### Limit identification -/

/-- **The limit of a minimizing sequence.** Let `O` be a family of null-measurable subsets of
`ball 0 R` that is closed under the symmetrization `S_e`, and let `t j ∈ O` be a sequence whose
second moments tend to the infimum of the second moment over `O`. If `t j` converges in volume of
symmetric differences to `F ⊆ ball 0 R`, then `S_e` does not decrease the second moment of `F`. -/
private theorem lintegral_norm_sq_le_steinerSymmetrization_of_tendsto {O : Set (Set E)} {R : ℝ}
    (hOm : ∀ t ∈ O, NullMeasurableSet t volume) (hOR : ∀ t ∈ O, t ⊆ ball 0 R) (e : E)
    (he : ‖e‖ = 1) (hOS : ∀ t ∈ O, steinerSymmetrization e he t ∈ O) {t : ℕ → Set E}
    (htO : ∀ j, t j ∈ O)
    (htM : Tendsto (fun j => ∫⁻ x in t j, ENNReal.ofReal (‖x‖ ^ 2)) atTop
      (𝓝 (sInf ((fun t => ∫⁻ x in t, ENNReal.ofReal (‖x‖ ^ 2)) '' O))))
    {F : Set E} (hFm : NullMeasurableSet F volume) (hFR : F ⊆ ball 0 R)
    (hlim : Tendsto (fun j => volume (t j ∆ F)) atTop (𝓝 0)) :
    ∫⁻ x in F, ENNReal.ofReal (‖x‖ ^ 2) ≤
      ∫⁻ x in steinerSymmetrization e he F, ENNReal.ofReal (‖x‖ ^ 2) := by
  let M : Set E → ℝ≥0∞ := fun t => ∫⁻ x in t, ENNReal.ofReal (‖x‖ ^ 2)
  -- The second moment is `R²`-Lipschitz, so its value at `F` is at most the infimum.
  have hclim : Tendsto (fun j => ENNReal.ofReal (R ^ 2) * volume (t j ∆ F)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)
  have hMF : M F ≤ sInf (M '' O) := by
    have h := htM.add hclim
    rw [add_zero] at h
    refine ge_of_tendsto' h fun j => ?_
    rw [symmDiff_comm]
    exact lintegral_norm_sq_le_add_of_subset_closedBall _ (hFR.trans ball_subset_closedBall)
  -- Symmetrizing along the sequence stays in `O`, and `S_e` contracts symmetric differences.
  have h := hclim.const_add (M (steinerSymmetrization e he F))
  rw [add_zero] at h
  refine hMF.trans (ge_of_tendsto' h fun j => ?_)
  calc sInf (M '' O) ≤ M (steinerSymmetrization e he (t j)) :=
        sInf_le (mem_image_of_mem M (hOS _ (htO j)))
    _ ≤ M (steinerSymmetrization e he F) + ENNReal.ofReal (R ^ 2) *
          volume (steinerSymmetrization e he (t j) ∆ steinerSymmetrization e he F) :=
        lintegral_norm_sq_le_add_of_subset_closedBall _
          ((hOR _ (hOS _ (htO j))).trans ball_subset_closedBall)
    _ ≤ M (steinerSymmetrization e he F) + ENNReal.ofReal (R ^ 2) * volume (t j ∆ F) := by
        gcongr _ + _ * ?_
        exact volume_steinerSymmetrization_symmDiff_le e he (hOm _ (htO j)) hFm

variable [Nontrivial E]

/-- **Limit identification.** Let `𝒞` be a family of null-measurable subsets of `ball 0 R` with
perimeters at most `C`, closed under every Steiner symmetrization. For `s ∈ 𝒞`, finitely many
symmetrizations bring `s` arbitrarily close in volume to the centered ball with the volume of
`s`. -/
private theorem exists_volume_ball_eq_and_forall_exists_lt {𝒞 : Set (Set E)} {R : ℝ} {C : ℝ≥0}
    (hS : ∀ t ∈ 𝒞, ∀ (e : E) (he : ‖e‖ = 1), steinerSymmetrization e he t ∈ 𝒞)
    (hm : ∀ t ∈ 𝒞, NullMeasurableSet t volume) (hR : ∀ t ∈ 𝒞, t ⊆ ball 0 R)
    (hP : ∀ t ∈ 𝒞, perimeter volume ⊤ t ≤ C) {s : Set E} (hs : s ∈ 𝒞) :
    ∃ r, volume (ball (0 : E) r) = volume s ∧ ∀ ε > 0,
      ∃ (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1) (n : ℕ),
        volume (iterateSteinerSymmetrization e he s n ∆ ball 0 r) < ε := by
  -- `M t` is the second moment and `O` the set of successive symmetrals of `s`.
  let M : Set E → ℝ≥0∞ := fun t => ∫⁻ x in t, ENNReal.ofReal (‖x‖ ^ 2)
  let O : Set (Set E) :=
    {t | ∃ (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1) (n : ℕ), iterateSteinerSymmetrization e he s n = t}
  have hO𝒞 {t : Set E} (ht : t ∈ O) : t ∈ 𝒞 := by
    obtain ⟨e, he, n, rfl⟩ := ht
    exact iterateSteinerSymmetrization_mem hS hs e he n
  have hOS {t : Set E} (ht : t ∈ O) (e : E) (he : ‖e‖ = 1) : steinerSymmetrization e he t ∈ O := by
    obtain ⟨e', he', n, rfl⟩ := ht
    obtain ⟨e'', he'', -, h⟩ :=
      exists_iterateSteinerSymmetrization_add_eq e' he' n (fun _ => e) fun _ => he
    exact ⟨e'', he'', n + 1, h s 1⟩
  obtain ⟨e₀, he₀⟩ := exists_norm_eq E zero_le_one
  have hsO : s ∈ O := ⟨fun _ => e₀, fun _ => he₀, 0, rfl⟩
  -- Take a minimizing sequence `t k` of the second moment on `O`.
  obtain ⟨u, -, hu, huO⟩ := exists_seq_tendsto_sInf (S := M '' O) ⟨M s, s, hsO, rfl⟩
    (OrderBot.bddBelow _)
  choose t htO htM using huO
  -- By compactness a subsequence converges in measure to some `F ⊆ ball 0 R`.
  obtain ⟨F₀, hF₀m, φ, hφ, hconv⟩ := exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le
    (μ := volume) (Ω := ⊤) (fun k => hm _ (hO𝒞 (htO k)))
    fun K _ _ => ⟨⊤, le_top, le_rfl, C, fun k => hP _ (hO𝒞 (htO k))⟩
  set F := F₀ ∩ ball (0 : E) R
  have hFm : NullMeasurableSet F volume := (hF₀m.inter measurableSet_ball).nullMeasurableSet
  have hFR : F ⊆ ball 0 R := inter_subset_right
  have hlim : Tendsto (fun j => volume (t (φ j) ∆ F)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hconv (closedBall 0 R) (isCompact_closedBall 0 R) (subset_univ _)) (fun _ => zero_le)
      fun j => measure_mono ?_
    -- Since `t (φ j) ⊆ ball 0 R`, cutting `F₀` by the ball cuts the symmetric difference by it.
    calc t (φ j) ∆ F = (t (φ j) ∆ F₀) ∩ ball 0 R := by
          rw [inter_symmDiff_distrib_right, inter_eq_left.2 (hR _ (hO𝒞 (htO (φ j))))]
      _ ⊆ (t (φ j) ∆ F₀) ∩ closedBall 0 R := inter_subset_inter_right _ ball_subset_closedBall
  -- The limit has the volume of `s`.
  have hvol (k : ℕ) : volume (t k) = volume s := by
    obtain ⟨e, he, n, hn⟩ := htO k
    rw [← hn, volume_iterateSteinerSymmetrization e he (hm s hs)]
  have hFvol : volume F = volume s :=
    MeasureTheory.measure_eq_of_tendsto_measure_symmDiff (Eventually.of_forall fun j => hvol (φ j))
      hlim
  have hFfin : volume F ≠ ∞ := ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hFR)
  have hMfin : M F ≠ ∞ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFfin)
    (lintegral_norm_sq_le_mul_of_subset_closedBall (hFR.trans ball_subset_closedBall))
  -- Hence every symmetrization fixes `F` up to a null set, and `F` is a centered ball.
  have hfix (e : E) (he : ‖e‖ = 1) : steinerSymmetrization e he F =ᵐ[volume] F :=
    ((lintegral_norm_sq_steinerSymmetrization_eq_iff e he hFm hMfin).1
      (le_antisymm (lintegral_norm_sq_steinerSymmetrization_le e he hFm)
        (lintegral_norm_sq_le_steinerSymmetrization_of_tendsto (fun t ht => hm t (hO𝒞 ht))
          (fun t ht => hR t (hO𝒞 ht)) e he (fun t ht => hOS ht e he) (fun j => htO (φ j))
          ((hu.comp hφ.tendsto_atTop).congr fun j => (htM (φ j)).symm) hFm hFR hlim))).symm
  obtain ⟨r, -, hr⟩ := exists_ae_eq_ball_of_forall_steinerSymmetrization_ae_eq hFm hFfin hfix
  refine ⟨r, by rw [← measure_congr hr, hFvol], fun ε hε => ?_⟩
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨e, he, n, hn⟩ := htO (φ j)
  refine ⟨e, he, n, ?_⟩
  rwa [hn, ← measure_congr (EventuallyEqSet.rfl.symmDiff hr)]

/-- **Convergence of successive Steiner symmetrizations to a ball.** Let `𝒞` be a family of
null-measurable subsets of a fixed ball `ball 0 R`, with perimeters at most `C`, closed under
every Steiner symmetrization. For every `s ∈ 𝒞` there are unit vectors `e 0, e 1, …` such that
the successive symmetrals `S_{e (n-1)} ⋯ S_{e 0} s` converge to the centered open ball `B` with
the volume of `s`, in the sense that `|S_{e (n-1)} ⋯ S_{e 0} s ∆ B| → 0`. -/
theorem exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball_of_perimeter_le
    {𝒞 : Set (Set E)} {R : ℝ} {C : ℝ≥0}
    (hS : ∀ t ∈ 𝒞, ∀ (e : E) (he : ‖e‖ = 1), steinerSymmetrization e he t ∈ 𝒞)
    (hm : ∀ t ∈ 𝒞, NullMeasurableSet t volume) (hR : ∀ t ∈ 𝒞, t ⊆ ball 0 R)
    (hP : ∀ t ∈ 𝒞, perimeter volume ⊤ t ≤ C) {s : Set E} (hs : s ∈ 𝒞) :
    ∃ r, volume (ball (0 : E) r) = volume s ∧ ∃ (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1),
      Tendsto (fun n => volume (iterateSteinerSymmetrization e he s n ∆ ball (0 : E) r))
        atTop (𝓝 0) := by
  obtain ⟨r, hr, -⟩ := exists_volume_ball_eq_and_forall_exists_lt hS hm hR hP hs
  refine ⟨r, hr, exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball (hm s hs)
    fun e he n ε hε => ?_⟩
  -- Limit identification from the `n`-th symmetral gives a centered ball of the same volume.
  have hn := iterateSteinerSymmetrization_mem hS hs e he n
  obtain ⟨r', hr', h⟩ := exists_volume_ball_eq_and_forall_exists_lt hS hm hR hP hn
  rw [volume_iterateSteinerSymmetrization e he (hm s hs), ← hr] at hr'
  have hball : ball (0 : E) r' =ᵐ[volume] ball 0 r := ball_ae_eq_ball_of_measure_eq hr'
  obtain ⟨e', he', m, hm'⟩ := h ε hε
  exact ⟨e', he', m, by rwa [← measure_congr (EventuallyEqSet.rfl.symmDiff hball)]⟩

/-- **Successive Steiner symmetrizations of a bounded convex set converge to a ball.** For every
bounded convex set `s` there are unit vectors `e 0, e 1, …` such that the successive Steiner
symmetrals `S_{e (n-1)} ⋯ S_{e 0} s` converge to the centered open ball `B` with the volume of
`s`, in the sense that `|S_{e (n-1)} ⋯ S_{e 0} s ∆ B| → 0`. -/
theorem _root_.Convex.exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball
    {s : Set E} (hs : Convex ℝ s) (hb : Bornology.IsBounded s) :
    ∃ r, volume (ball (0 : E) r) = volume s ∧ ∃ (e : ℕ → E) (he : ∀ k, ‖e k‖ = 1),
      Tendsto (fun n => volume (iterateSteinerSymmetrization e he s n ∆ ball (0 : E) r))
        atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hb.subset_ball 0
  -- Convex subsets of `ball 0 R` have perimeter at most that of the ball.
  have hP : perimeter volume ⊤ (ball (0 : E) R) ≠ ∞ :=
    ((convex_ball 0 R).perimeter_lt_top (μ := volume) isBounded_ball).ne
  refine exists_tendsto_volume_iterateSteinerSymmetrization_symmDiff_ball_of_perimeter_le
    (𝒞 := {t | Convex ℝ t ∧ t ⊆ ball 0 R}) (C := (perimeter volume ⊤ (ball (0 : E) R)).toNNReal)
    (fun t ht e he => ⟨convex_steinerSymmetrization e he ht.1, ?_⟩)
    (fun t ht => ht.1.nullMeasurableSet (μ := volume)) (fun t ht => ht.2) (fun t ht => ?_) ⟨hs, hR⟩
  · rw [← steinerSymmetrization_ball_zero e he R]
    exact steinerSymmetrization_mono e he ht.2
  · rw [ENNReal.coe_toNNReal hP]
    exact ht.1.perimeter_le_of_subset ht.2 measurableSet_ball.nullMeasurableSet
      measure_ball_lt_top.ne

end TauCeti
