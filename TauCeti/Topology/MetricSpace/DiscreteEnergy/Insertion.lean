/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.DiscreteEnergy.Refinement
public import TauCeti.Topology.MetricSpace.Length
import TauCeti.Algebra.BigOperators.Fin
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Data.Fin.Basic

/-!
# Geodesic insertion in discrete paths

A refinement of the time subdivision gives a refined vertex tuple by sampling a genuine
constant-speed minimizing segment along each coarse edge. This operation retains the old
vertices and preserves discrete energy exactly. A continuous choice of the segments gives
continuous maps between the strict energy sublevels, with vertex-forgetting as a left inverse.

This is the subdivision comparison for broken minimizing paths in J. Milnor,
*Morse Theory*, §16, with the energy normalized by a factor of `½`.
-/

public section

open scoped BigOperators

namespace TauCeti

variable {M : Type*} {m n : ℕ}

private noncomputable def insertionBlock (r : Fin (m + 2) ↪o Fin (n + 2))
    (h0 : r 0 = 0) (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (j : Fin (n + 2)) : Fin (m + 1) :=
  (exists_mem_Icc_castSucc_succ (a := (r : Fin (m + 2) → Fin (n + 2))) (x := j)
    (by omega) ⟨by rw [h0]; exact Fin.zero_le _, by rw [hlast]; exact Fin.le_last _⟩).choose

private theorem insertionBlock_spec (r : Fin (m + 2) ↪o Fin (n + 2))
    (h0 : r 0 = 0) (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (j : Fin (n + 2)) :
    r (insertionBlock r h0 hlast j).castSucc ≤ j ∧
      j ≤ r (insertionBlock r h0 hlast j).succ :=
  (exists_mem_Icc_castSucc_succ (a := (r : Fin (m + 2) → Fin (n + 2))) (x := j)
    (by omega) ⟨by rw [h0]; exact Fin.zero_le _, by rw [hlast]; exact Fin.le_last _⟩).choose_spec

/-- Sample the chosen coarse-edge curves at the fine subdivision times. The endpoint
conditions say that the selection `r` retains the first and last time. -/
noncomputable def discreteEnergyInsert (t : Fin (n + 2) → ℝ)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (γ : Fin (m + 1) → ℝ → M) (j : Fin (n + 2)) : M :=
  let i := insertionBlock r h0 hlast j
  γ i ((t j - t (r i.castSucc)) / (t (r i.succ) - t (r i.castSucc)))

/-- Insertion varies continuously with a parameter whenever each chosen segment does,
at each fixed time in `[0, 1]`. Joint continuity of the segment family implies this hypothesis. -/
@[fun_prop]
theorem continuous_discreteEnergyInsert {A : Type*} [TopologicalSpace A] [TopologicalSpace M]
    {t : Fin (n + 2) → ℝ} (ht : Monotone t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (γ : A → Fin (m + 1) → ℝ → M)
    (hγ : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun a ↦ γ a i u)) :
    Continuous (fun a ↦ discreteEnergyInsert t r h0 hlast (γ a)) := by
  unfold discreteEnergyInsert
  exact continuous_pi fun j ↦ hγ _ _
    (sub_div_sub_mem_Icc ⟨ht (insertionBlock_spec r h0 hlast j).1,
      ht (insertionBlock_spec r h0 hlast j).2⟩)

/-- On each coarse edge, insertion is evaluation of that edge's curve at
the normalized fine time. At a coarse vertex the adjacent formulas agree. -/
theorem discreteEnergyInsert_apply {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (x : Fin (m + 2) → M) (γ : Fin (m + 1) → ℝ → M)
    (hsource : ∀ i, γ i 0 = x i.castSucc) (htarget : ∀ i, γ i 1 = x i.succ)
    (i : Fin (m + 1)) (j : Fin (n + 2)) (hj : r i.castSucc ≤ j ∧ j ≤ r i.succ) :
    discreteEnergyInsert t r h0 hlast γ j =
      γ i ((t j - t (r i.castSucc)) / (t (r i.succ) - t (r i.castSucc))) := by
  let k := insertionBlock r h0 hlast j
  have hk := insertionBlock_spec r h0 hlast j
  have hd (a : Fin (m + 1)) : t (r a.succ) - t (r a.castSucc) ≠ 0 :=
    (sub_pos.mpr (ht (r.strictMono a.castSucc_lt_succ))).ne'
  have hdef : discreteEnergyInsert t r h0 hlast γ j =
      γ k ((t j - t (r k.castSucc)) / (t (r k.succ) - t (r k.castSucc))) := rfl
  rw [hdef]
  obtain hki | rfl | hik := lt_trichotomy k i
  · have hle : k.succ ≤ i.castSucc := by exact Nat.succ_le_of_lt hki
    have heq : r k.succ = r i.castSucc :=
      le_antisymm (r.monotone hle) (hj.1.trans hk.2)
    have hj' : j = r k.succ := le_antisymm hk.2 (heq ▸ hj.1)
    have hidx : k.succ = i.castSucc := r.injective heq
    rw [hj', div_self (hd k), htarget k, heq, sub_self, zero_div, hsource i, hidx]
  · rfl
  · have hle : i.succ ≤ k.castSucc := by exact Nat.succ_le_of_lt hik
    have heq : r i.succ = r k.castSucc :=
      le_antisymm (r.monotone hle) (hk.1.trans hj.2)
    have hj' : j = r i.succ := le_antisymm hj.2 (heq ▸ hk.1)
    have hidx : i.succ = k.castSucc := r.injective heq
    rw [hj', div_self (hd i), htarget i, heq, sub_self, zero_div, hsource k, hidx]

/-- Inserting samples of endpoint-compatible curves retains every coarse vertex. -/
theorem discreteEnergyInsert_comp {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (x : Fin (m + 2) → M) (γ : Fin (m + 1) → ℝ → M)
    (hsource : ∀ i, γ i 0 = x i.castSucc) (htarget : ∀ i, γ i 1 = x i.succ) :
    discreteEnergyInsert t r h0 hlast γ ∘ r = x := by
  funext j
  obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · rw [Function.comp_apply, discreteEnergyInsert_apply ht r h0 hlast x γ hsource htarget i _
      ⟨le_rfl, r.monotone i.castSucc_le_succ⟩]
    simp [hsource i]
  · rw [Function.comp_apply, ← Fin.succ_last,
      discreteEnergyInsert_apply ht r h0 hlast x γ hsource htarget (Fin.last m) _
        ⟨r.monotone (Fin.castSucc_le_succ _), le_rfl⟩]
    rw [div_self (sub_pos.mpr (ht (r.strictMono (Fin.castSucc_lt_succ (i := Fin.last m))))).ne',
      htarget (Fin.last m)]

/-- Reattaching the fixed endpoints to the inserted interior vertices recovers the full
inserted tuple. This equation lets callers use insertion without unfolding its construction. -/
theorem cons_snoc_discreteEnergyInsert {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (p q : M) (x : Fin m → M) (γ : Fin (m + 1) → ℝ → M)
    (hsource : ∀ i, γ i 0 = (Fin.cons p (Fin.snoc x q) : Fin (m + 2) → M) i.castSucc)
    (htarget : ∀ i, γ i 1 = (Fin.cons p (Fin.snoc x q) : Fin (m + 2) → M) i.succ) :
    Fin.cons p (Fin.snoc (fun j : Fin n ↦
      discreteEnergyInsert t r h0 hlast γ j.castSucc.succ) q) =
        discreteEnergyInsert t r h0 hlast γ := by
  have h := discreteEnergyInsert_comp ht r h0 hlast (Fin.cons p (Fin.snoc x q)) γ hsource htarget
  have hfirst := congrFun h 0
  have hfinal := congrFun h (Fin.last (m + 1))
  simp only [Function.comp_apply, h0, Fin.cons_zero] at hfirst
  simp only [Function.comp_apply, hlast] at hfinal
  rw [Fin.cons_last, Fin.snoc_last] at hfinal
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simpa using hfirst.symm
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · rw [Fin.cons_succ, Fin.snoc_last]
      exact hfinal.symm
    · simp

section Metric

variable [PseudoMetricSpace M]

/-- Sampling genuine constant-speed minimizing segments on any refinement preserves
exactly the discrete energy, including coarse edges with coincident endpoints. -/
theorem discreteEnergy_discreteEnergyInsert {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (x : Fin (m + 2) → M) (γ : Fin (m + 1) → ℝ → M)
    (hγ : ∀ i, IsGeodesicSegment (γ i) (x i.castSucc) (x i.succ)) :
    discreteEnergy t (discreteEnergyInsert t r h0 hlast γ) = discreteEnergy (t ∘ r) x := by
  let T : ℕ → ℝ := fun k ↦ t (Fin.ofNat (n + 2) k)
  let Y : ℕ → M := fun k ↦ discreteEnergyInsert t r h0 hlast γ (Fin.ofNat (n + 2) k)
  let e : ℕ → ℝ := fun k ↦ dist (Y k) (Y (k + 1)) ^ 2 / (T (k + 1) - T k)
  have hnat (j : Fin (n + 2)) : Fin.ofNat (n + 2) j.val = j := by simp
  -- On a coarse block, the refined edge energies are proportional to its fine time gaps.
  have hblock (i : Fin (m + 1)) :
      (∑ k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val, e k) =
        dist (x i.castSucc) (x i.succ) ^ 2 / (t (r i.succ) - t (r i.castSucc)) := by
    let d := t (r i.succ) - t (r i.castSucc)
    have hd : 0 < d := sub_pos.mpr (ht (r.strictMono i.castSucc_lt_succ))
    have hsample (j : Fin (n + 2)) (hj : r i.castSucc ≤ j ∧ j ≤ r i.succ) :
        Y j.val = γ i ((t j - t (r i.castSucc)) / d) := by
      simpa only [Y, hnat] using discreteEnergyInsert_apply ht r h0 hlast x γ
        (fun a ↦ (hγ a).source) (fun a ↦ (hγ a).target) i j hj
    have he (k : ℕ) (hk : k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val) :
        e k = (T (k + 1) - T k) * (dist (x i.castSucc) (x i.succ) ^ 2 / d ^ 2) := by
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
      let a : Fin (n + 2) := ⟨k, by have := (r i.succ).isLt; omega⟩
      let b : Fin (n + 2) := ⟨k + 1, by have := (r i.succ).isLt; omega⟩
      have ha : r i.castSucc ≤ a ∧ a ≤ r i.succ := ⟨hlo, by exact hhi.le⟩
      have hb : r i.castSucc ≤ b ∧ b ≤ r i.succ := ⟨by exact hlo.trans (Nat.le_succ _), hhi⟩
      have hab : a < b := by exact Nat.lt_succ_self _
      have hab' : 0 < t b - t a := sub_pos.mpr (ht hab)
      -- Constant speed turns the distance between samples into the normalized time gap.
      have hdist := (hγ i).dist_eq _ (sub_div_sub_mem_Icc ⟨ht.monotone ha.1, ht.monotone ha.2⟩)
        _ (sub_div_sub_mem_Icc ⟨ht.monotone hb.1, ht.monotone hb.2⟩)
      have hparam : (t a - t (r i.castSucc)) / d -
          (t b - t (r i.castSucc)) / d = -(t b - t a) / d := by ring
      have hY : dist (Y k) (Y (k + 1)) = (t b - t a) / d *
          dist (x i.castSucc) (x i.succ) := by
        rw [hsample a ha, hsample b hb, hdist, hparam, abs_div, abs_neg,
          abs_of_pos hab', abs_of_pos hd]
      have hTa : T k = t a := congrArg t (hnat a)
      have hTb : T (k + 1) = t b := congrArg t (hnat b)
      dsimp only [e]
      rw [hY, hTa, hTb]
      field_simp
    rw [Finset.sum_congr rfl he, ← Finset.sum_mul,
      Finset.sum_Ico_sub T (r.monotone i.castSucc_le_succ)]
    simp only [T, hnat]
    dsimp only [d]
    field_simp
  -- The coarse blocks partition the fine edges; their partial sums telescope.
  have hsum : (∑ i : Fin (m + 1),
      ∑ k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val, e k) =
      ∑ k ∈ Finset.range (n + 1), e k := by
    simp_rw [Finset.sum_Ico_eq_sub e (r.monotone (Fin.castSucc_le_succ _))]
    have h := Fin.sum_univ_succ_sub_castSucc
      (fun i ↦ ∑ k ∈ Finset.range (r i).val, e k)
    simpa only [h0, hlast, Fin.val_zero, Fin.val_last, Finset.range_zero,
      Finset.sum_empty, sub_zero] using h
  have he (i : Fin (n + 1)) : e i.val =
      dist (discreteEnergyInsert t r h0 hlast γ i.castSucc)
        (discreteEnergyInsert t r h0 hlast γ i.succ) ^ 2 /
        (t i.succ - t i.castSucc) := by
    have hsucc : Fin.ofNat (n + 2) (i.val + 1) = i.succ := hnat i.succ
    have hcast : Fin.ofNat (n + 2) i.val = i.castSucc := hnat i.castSucc
    simp only [e, Y, T, hsucc, hcast]
  simp_rw [hblock] at hsum
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  simp only [he] at hsum
  simpa only [discreteEnergy_def, Function.comp_apply] using
    congrArg (fun z : ℝ ↦ (1 / 2) * z) hsum.symm

/-- In a geodesic space every coarse tuple has an energy-preserving refinement that
retains all its specified vertices. No continuous choice of geodesics is asserted. -/
theorem exists_discreteEnergy_refinement [IsGeodesicSpace M]
    {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (m + 2) → M) :
    ∃ y : Fin (n + 2) → M, y ∘ r = x ∧ discreteEnergy t y = discreteEnergy (t ∘ r) x := by
  choose γ hγ using fun i : Fin (m + 1) ↦
    IsGeodesicSpace.exists_isGeodesicSegment (x i.castSucc) (x i.succ)
  exact ⟨discreteEnergyInsert t r h0 hlast γ, discreteEnergyInsert_comp ht r h0 hlast x γ
    (fun i ↦ (hγ i).source) (fun i ↦ (hγ i).target),
    discreteEnergy_discreteEnergyInsert ht r h0 hlast x γ hγ⟩

/-- A continuous choice of genuine geodesics along the coarse tuples induces a continuous
insertion map of strict energy sublevels. The choice is needed only on the source sublevel. -/
noncomputable def discreteEnergyInsertMap {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (p q : M) (c : ℝ)
    (γ : discreteEnergyStrictSublevel (t ∘ r) p q c → Fin (m + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.castSucc)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.succ))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u)) :
    C(discreteEnergyStrictSublevel (t ∘ r) p q c, discreteEnergyStrictSublevel t p q c) := by
  let f : discreteEnergyStrictSublevel (t ∘ r) p q c → Fin n → M :=
    fun x j ↦ discreteEnergyInsert t r h0 hlast (γ x) j.castSucc.succ
  have hf (x : discreteEnergyStrictSublevel (t ∘ r) p q c) :
      f x ∈ discreteEnergyStrictSublevel t p q c := by
    apply mem_discreteEnergyStrictSublevel.mpr
    rw [cons_snoc_discreteEnergyInsert ht r h0 hlast p q x (γ x)
      (fun i ↦ (hγ x i).source) (fun i ↦ (hγ x i).target),
      discreteEnergy_discreteEnergyInsert ht r h0 hlast
        (Fin.cons p (Fin.snoc (x : Fin m → M) q)) (γ x) (hγ x)]
    exact mem_discreteEnergyStrictSublevel.mp x.prop
  exact ⟨fun x ↦ ⟨f x, hf x⟩, (continuous_pi fun (j : Fin n) ↦
    (continuous_apply j.castSucc.succ).comp
      (continuous_discreteEnergyInsert ht.monotone r h0 hlast γ hcont)).subtype_mk _⟩

/-- The underlying interior tuple of the sublevel insertion is the sampled fine tuple. -/
@[simp]
theorem discreteEnergyInsertMap_apply {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (c : ℝ)
    (γ : discreteEnergyStrictSublevel (t ∘ r) p q c → Fin (m + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.castSucc)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.succ))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u))
    (x : discreteEnergyStrictSublevel (t ∘ r) p q c) :
    (discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont x : Fin n → M) =
      fun j ↦ discreteEnergyInsert t r h0 hlast (γ x) j.castSucc.succ := (rfl)

/-- Forgetting the newly inserted vertices is a left inverse to continuous geodesic insertion. -/
@[simp]
theorem discreteEnergyForgetMap_comp_insertMap {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (c : ℝ)
    (γ : discreteEnergyStrictSublevel (t ∘ r) p q c → Fin (m + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.castSucc)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.succ))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u)) :
    (discreteEnergyForgetMap ht r h0 hlast p q c).comp
        (discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont) =
      ContinuousMap.id (discreteEnergyStrictSublevel (t ∘ r) p q c) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  funext j
  rw [ContinuousMap.comp_apply, discreteEnergyForgetMap_apply,
    discreteEnergyInsertMap_apply, discreteEnergyForget_apply,
    cons_snoc_discreteEnergyInsert ht r h0 hlast p q x (γ x)
      (fun i ↦ (hγ x i).source) (fun i ↦ (hγ x i).target)]
  have h := congrFun (discreteEnergyInsert_comp ht r h0 hlast
    (Fin.cons p (Fin.snoc (x : Fin m → M) q)) (γ x)
    (fun i ↦ (hγ x i).source) (fun i ↦ (hγ x i).target)) j.castSucc.succ
  simpa using h

end Metric

end TauCeti
