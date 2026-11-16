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

J. Milnor, *Morse Theory*, §16 models broken minimizing geodesics as subspaces of
the ambient path space. Representing these carriers by vertex tuples turns coarse-to-fine
inclusion across refinements into the explicit insertion map here. Energy is normalized
by a factor of `½`.
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

/-- Read each coarse-edge curve `γ i` on `[0, 1]` and sample it at the normalized fine
time `(t j - t (r i.castSucc)) / (t (r i.succ) - t (r i.castSucc))`. The endpoint
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

/-- Insertion depends only on the curves restricted to their parameter interval `[0, 1]`. -/
theorem discreteEnergyInsert_congr {t : Fin (n + 2) → ℝ} (ht : Monotone t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    {γ₁ γ₂ : Fin (m + 1) → ℝ → M}
    (hγ : ∀ i, Set.EqOn (γ₁ i) (γ₂ i) (Set.Icc 0 1)) :
    discreteEnergyInsert t r h0 hlast γ₁ = discreteEnergyInsert t r h0 hlast γ₂ := by
  funext j
  exact hγ _ (sub_div_sub_mem_Icc ⟨ht (insertionBlock_spec r h0 hlast j).1,
    ht (insertionBlock_spec r h0 hlast j).2⟩)

/-- Insertion at the first fine time reads the first curve at parameter zero. -/
@[simp]
theorem discreteEnergyInsert_zero (t : Fin (n + 2) → ℝ)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (γ : Fin (m + 1) → ℝ → M) : discreteEnergyInsert t r h0 hlast γ 0 = γ 0 0 := by
  have hk := (insertionBlock_spec r h0 hlast 0).1
  have heq : insertionBlock r h0 hlast 0 = 0 := by
    have h := r.le_iff_le.mp (hk.trans_eq h0.symm)
    exact Fin.ext (by simpa using Nat.eq_zero_of_le_zero (Fin.le_iff_val_le_val.mp h))
  simp [discreteEnergyInsert, heq, h0]

/-- Insertion at the last fine time reads the last curve at parameter one. -/
@[simp]
theorem discreteEnergyInsert_last {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (γ : Fin (m + 1) → ℝ → M) :
    discreteEnergyInsert t r h0 hlast γ (Fin.last (n + 1)) = γ (Fin.last m) 1 := by
  have hk := (insertionBlock_spec r h0 hlast (Fin.last (n + 1))).2
  have heq : insertionBlock r h0 hlast (Fin.last (n + 1)) = Fin.last m := by
    have h := r.le_iff_le.mp (hlast.trans_le hk)
    apply Fin.ext
    have := Fin.le_iff_val_le_val.mp h
    have := (insertionBlock r h0 hlast (Fin.last (n + 1))).isLt
    simp only [Fin.val_last, Fin.val_succ] at *
    omega
  unfold discreteEnergyInsert
  rw [heq]
  rw [← hlast, ← Fin.succ_last]
  dsimp only
  have hd : t (r (Fin.last m).succ) - t (r (Fin.last m).castSucc) ≠ 0 :=
    (discreteEnergy_step_pos (ht.comp r.strictMono) (Fin.last m)).ne'
  rw [div_self hd]

/-- On each coarse edge, insertion evaluates its curve at the normalized fine time.
Only gluing of adjacent curves is needed for agreement at their shared vertices. -/
theorem discreteEnergyInsert_apply {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (γ : Fin (m + 1) → ℝ → M) (hγ : ∀ k : Fin m, γ k.castSucc 1 = γ k.succ 0)
    (i : Fin (m + 1)) (j : Fin (n + 2)) (hj : r i.castSucc ≤ j ∧ j ≤ r i.succ) :
    discreteEnergyInsert t r h0 hlast γ j =
      γ i ((t j - t (r i.castSucc)) / (t (r i.succ) - t (r i.castSucc))) := by
  let u (a : Fin (m + 1)) := (t j - t (r a.castSucc)) / (t (r a.succ) - t (r a.castSucc))
  have overlap (a b : Fin (m + 1)) (hab : a < b)
      (ha : r a.castSucc ≤ j ∧ j ≤ r a.succ)
      (hb : r b.castSucc ≤ j ∧ j ≤ r b.succ) : γ a (u a) = γ b (u b) := by
    have heq : r a.succ = r b.castSucc := le_antisymm
      (r.monotone (Fin.succ_le_castSucc_iff.mpr hab)) (hb.1.trans ha.2)
    have hj' : j = r a.succ := le_antisymm ha.2 (heq ▸ hb.1)
    have hidx := r.injective heq
    let c : Fin m := ⟨a.val, lt_of_lt_of_le (Fin.lt_def.mp hab)
      (Nat.le_of_lt_succ b.isLt)⟩
    have hca : c.castSucc = a := Fin.ext rfl
    have hcb : c.succ = b := Fin.ext (by
      have := congrArg Fin.val hidx
      simpa using this)
    dsimp only [u]
    have hd : t (r a.succ) - t (r a.castSucc) ≠ 0 :=
      (discreteEnergy_step_pos (ht.comp r.strictMono) a).ne'
    rw [hj', div_self hd,
      heq, sub_self, zero_div, ← hca, ← hcb]
    exact hγ c
  let k := insertionBlock r h0 hlast j
  -- Expand only the chosen-block evaluation, naming its normalized parameter by `u`.
  change γ k (u k) = γ i (u i)
  obtain hki | rfl | hik := lt_trichotomy k i
  · exact overlap k i hki (insertionBlock_spec r h0 hlast j) hj
  · rfl
  · exact (overlap i k hik hj (insertionBlock_spec r h0 hlast j)).symm

/-- Inserting endpoint-compatible curves retains the specified coarse vertex. -/
theorem discreteEnergyInsert_comp_apply {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (x : Fin (m + 2) → M) (γ : Fin (m + 1) → ℝ → M)
    (hsource : ∀ i, γ i 0 = x i.castSucc) (htarget : ∀ i, γ i 1 = x i.succ)
    (j : Fin (m + 2)) : discreteEnergyInsert t r h0 hlast γ (r j) = x j := by
  have hglue (k : Fin m) : γ k.castSucc 1 = γ k.succ 0 := by
    rw [htarget, hsource, Fin.castSucc_succ]
  obtain ⟨i, rfl⟩ | rfl := j.eq_castSucc_or_eq_last
  · rw [discreteEnergyInsert_apply ht r h0 hlast γ hglue i _
      ⟨le_rfl, r.monotone i.castSucc_le_succ⟩]
    simp [hsource i]
  · rw [hlast, discreteEnergyInsert_last ht, htarget, Fin.succ_last]

/-- Inserting samples of endpoint-compatible curves retains every coarse vertex. -/
theorem discreteEnergyInsert_comp {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (x : Fin (m + 2) → M) (γ : Fin (m + 1) → ℝ → M)
    (hsource : ∀ i, γ i 0 = x i.castSucc) (htarget : ∀ i, γ i 1 = x i.succ) :
    discreteEnergyInsert t r h0 hlast γ ∘ r = x := by
  funext j
  exact discreteEnergyInsert_comp_apply ht r h0 hlast x γ hsource htarget j

/-- Reattaching the fixed endpoints to the inserted interior vertices recovers the full
inserted tuple. This equation lets callers use insertion without unfolding its construction. -/
theorem cons_snoc_discreteEnergyInsert {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    {p q : M} {γ : Fin (m + 1) → ℝ → M}
    (hp : γ 0 0 = p) (hq : γ (Fin.last m) 1 = q) :
    Fin.cons p (Fin.snoc (fun j : Fin n ↦
      discreteEnergyInsert t r h0 hlast γ j.castSucc.succ) q) =
        discreteEnergyInsert t r h0 hlast γ := by
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j
  · simp [hp]
  · refine Fin.lastCases ?_ (fun j ↦ ?_) j
    · simpa [hq] using (discreteEnergyInsert_last ht r h0 hlast γ).symm
    · simp

/-- Forgetting inserted interior vertices recovers the original tuple, without metric
or continuity assumptions. -/
theorem discreteEnergyForget_discreteEnergyInsert {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1))
    (p q : M) (x : Fin m → M) (γ : Fin (m + 1) → ℝ → M)
    (hsource : ∀ i, γ i 0 = (Fin.cons p (Fin.snoc x q) : Fin (m + 2) → M) i.castSucc)
    (htarget : ∀ i, γ i 1 = (Fin.cons p (Fin.snoc x q) : Fin (m + 2) → M) i.succ) :
    discreteEnergyForget r p q
      (fun j ↦ discreteEnergyInsert t r h0 hlast γ j.castSucc.succ) = x := by
  funext j
  rw [discreteEnergyForget_apply, cons_snoc_discreteEnergyInsert ht r h0 hlast
    (by simpa using hsource 0) (by simpa using htarget (Fin.last m)),
    discreteEnergyInsert_comp_apply ht r h0 hlast _ γ hsource htarget]
  simp

section Metric

variable [PseudoMetricSpace M]

/-- Subdividing a constant-speed minimizing segment preserves its energy on a finite
interval of strictly increasing times. The sum omits the normalization `½`. -/
theorem IsGeodesicSegment.sum_Ico_dist_sq_div_eq {γ : ℝ → M} {x y : M}
    (hγ : IsGeodesicSegment γ x y) (t : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    (ht : StrictMonoOn t (Set.Icc a b)) :
    (∑ k ∈ Finset.Ico a b,
      dist (γ ((t k - t a) / (t b - t a)))
        (γ ((t (k + 1) - t a) / (t b - t a))) ^ 2 / (t (k + 1) - t k)) =
      dist x y ^ 2 / (t b - t a) := by
  obtain rfl | hab := hab.eq_or_lt
  · simp
  have hd : 0 < t b - t a := sub_pos.mpr (ht ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab)
  have he (k : ℕ) (hk : k ∈ Finset.Ico a b) :
      dist (γ ((t k - t a) / (t b - t a)))
          (γ ((t (k + 1) - t a) / (t b - t a))) ^ 2 / (t (k + 1) - t k) =
        (t (k + 1) - t k) * (dist x y ^ 2 / (t b - t a) ^ 2) := by
    obtain ⟨hak, hkb⟩ := Finset.mem_Ico.mp hk
    have hk' : k ∈ Set.Icc a b := ⟨hak, hkb.le⟩
    have hk1 : k + 1 ∈ Set.Icc a b := ⟨hak.trans (Nat.le_succ _), hkb⟩
    have hstep : 0 < t (k + 1) - t k := sub_pos.mpr (ht hk' hk1 (Nat.lt_succ_self _))
    have hdist := hγ.dist_eq _ (sub_div_sub_mem_Icc
      ⟨ht.monotoneOn ⟨le_rfl, hab.le⟩ hk' hak,
        ht.monotoneOn hk' ⟨hab.le, le_rfl⟩ hkb.le⟩) _ (sub_div_sub_mem_Icc
      ⟨ht.monotoneOn ⟨le_rfl, hab.le⟩ hk1 hk1.1,
        ht.monotoneOn hk1 ⟨hab.le, le_rfl⟩ hk1.2⟩)
    have hparam : (t k - t a) / (t b - t a) -
        (t (k + 1) - t a) / (t b - t a) = -(t (k + 1) - t k) / (t b - t a) := by ring
    rw [hdist, hparam, abs_div, abs_neg, abs_of_pos hstep, abs_of_pos hd]
    field_simp
  rw [Finset.sum_congr rfl he, ← Finset.sum_mul, Finset.sum_Ico_sub t hab.le]
  field_simp

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
  have hT : StrictMonoOn T (Set.Icc 0 (n + 1)) := by
    intro a ha b hb hab
    apply ht
    simpa only [T, Fin.lt_def, Fin.val_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le ha.2),
      Nat.mod_eq_of_lt (Nat.lt_succ_of_le hb.2)] using hab
  -- Apply the single-segment identity on each coarse block.
  have hblock (i : Fin (m + 1)) :
      (∑ k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val, e k) =
        dist (x i.castSucc) (x i.succ) ^ 2 / (t (r i.succ) - t (r i.castSucc)) := by
    have hab := Fin.le_iff_val_le_val.mp (r.monotone i.castSucc_le_succ)
    have hsample (k : ℕ) (hk : k ∈ Set.Icc (r i.castSucc).val (r i.succ).val) :
        Y k = γ i ((T k - T (r i.castSucc).val) /
          (T (r i.succ).val - T (r i.castSucc).val)) := by
      let j : Fin (n + 2) := ⟨k, hk.2.trans_lt (r i.succ).isLt⟩
      have hj : r i.castSucc ≤ j ∧ j ≤ r i.succ :=
        ⟨Fin.le_iff_val_le_val.mpr hk.1, Fin.le_iff_val_le_val.mpr hk.2⟩
      have hjnat : Fin.ofNat (n + 2) k = j := hnat j
      simpa only [T, Y, hjnat, hnat] using discreteEnergyInsert_apply ht r h0 hlast γ
        (fun a ↦ by rw [(hγ a.castSucc).target, (hγ a.succ).source, Fin.castSucc_succ]) i j hj
    have h := (hγ i).sum_Ico_dist_sq_div_eq T hab
      (hT.mono fun k hk ↦ ⟨Nat.zero_le _, hk.2.trans (r i.succ).is_le⟩)
    have he (k : ℕ) (hk : k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val) :
        e k = dist (γ i ((T k - T (r i.castSucc).val) /
          (T (r i.succ).val - T (r i.castSucc).val)))
          (γ i ((T (k + 1) - T (r i.castSucc).val) /
          (T (r i.succ).val - T (r i.castSucc).val))) ^ 2 / (T (k + 1) - T k) := by
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
      dsimp only [e]
      rw [hsample k ⟨hlo, hhi.le⟩,
        hsample (k + 1) ⟨hlo.trans (Nat.le_succ _), Nat.succ_le_of_lt hhi⟩]
    rw [Finset.sum_congr rfl he]
    simpa only [T, hnat] using h
  -- The coarse blocks partition the fine edges; their partial sums telescope.
  have hsum : (∑ i : Fin (m + 1),
      ∑ k ∈ Finset.Ico (r i.castSucc).val (r i.succ).val, e k) =
      ∑ k ∈ Finset.range (n + 1), e k := by
    simp_rw [Finset.sum_Ico_eq_sub e (Fin.le_iff_val_le_val.mp
      (r.monotone (Fin.castSucc_le_succ _)))]
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
theorem exists_comp_eq_and_discreteEnergy_eq [IsGeodesicSpace M]
    {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (x : Fin (m + 2) → M) :
    ∃ y : Fin (n + 2) → M, y ∘ r = x ∧ discreteEnergy t y = discreteEnergy (t ∘ r) x := by
  choose γ hγ using fun i : Fin (m + 1) ↦
    IsGeodesicSpace.exists_isGeodesicSegment (x i.castSucc) (x i.succ)
  exact ⟨discreteEnergyInsert t r h0 hlast γ, discreteEnergyInsert_comp ht r h0 hlast x γ
    (fun i ↦ (hγ i).source) (fun i ↦ (hγ i).target),
    discreteEnergy_discreteEnergyInsert ht r h0 hlast x γ hγ⟩

/-- A continuous choice of constant-speed minimizing segments along the coarse tuples induces
a continuous insertion map of strict energy sublevels. The choice is needed only on the source
sublevel. -/
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
    rw [cons_snoc_discreteEnergyInsert ht r h0 hlast
      (by simpa using (hγ x 0).source) (by simpa using (hγ x (Fin.last m)).target),
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

section Sublevel

variable {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (r : Fin (m + 2) ↪o Fin (n + 2)) (h0 : r 0 = 0)
    (hlast : r (Fin.last (m + 1)) = Fin.last (n + 1)) (p q : M) (c : ℝ)
    (γ : discreteEnergyStrictSublevel (t ∘ r) p q c → Fin (m + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.castSucc)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.succ))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u))

/-- Reattaching the fixed endpoints to sublevel insertion recovers the full sampled tuple. -/
theorem cons_snoc_discreteEnergyInsertMap (x : discreteEnergyStrictSublevel (t ∘ r) p q c) :
    Fin.cons p (Fin.snoc
      (discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont x : Fin n → M) q) =
      discreteEnergyInsert t r h0 hlast (γ x) := by
  rw [discreteEnergyInsertMap_apply]
  exact cons_snoc_discreteEnergyInsert ht r h0 hlast
    (by simpa using (hγ x 0).source) (by simpa using (hγ x (Fin.last m)).target)

/-- Continuous sublevel insertion preserves the energy functional exactly. -/
theorem discreteEnergy_cons_snoc_discreteEnergyInsertMap
    (x : discreteEnergyStrictSublevel (t ∘ r) p q c) :
    discreteEnergy t (Fin.cons p (Fin.snoc
      (discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont x : Fin n → M) q)) =
      discreteEnergy (t ∘ r) (Fin.cons p (Fin.snoc (x : Fin m → M) q)) := by
  rw [cons_snoc_discreteEnergyInsertMap]
  exact discreteEnergy_discreteEnergyInsert ht r h0 hlast _ (γ x) (hγ x)

/-- Sublevel insertion depends only on the chosen segments on `[0, 1]`. -/
theorem discreteEnergyInsertMap_congr
    (γ₂ : discreteEnergyStrictSublevel (t ∘ r) p q c → Fin (m + 1) → ℝ → M)
    (hγ₂ : ∀ x i, IsGeodesicSegment (γ₂ x i)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.castSucc)
      ((Fin.cons p (Fin.snoc (x : Fin m → M) q) : Fin (m + 2) → M) i.succ))
    (hcont₂ : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ₂ x i u))
    (heq : ∀ x i, Set.EqOn (γ x i) (γ₂ x i) (Set.Icc 0 1)) :
    discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont =
      discreteEnergyInsertMap ht r h0 hlast p q c γ₂ hγ₂ hcont₂ := by
  ext x j
  exact congrFun (discreteEnergyInsert_congr ht.monotone r h0 hlast (heq x)) j.castSucc.succ

/-- Forgetting newly inserted vertices recovers the original sublevel point. -/
@[simp]
theorem discreteEnergyForgetMap_discreteEnergyInsertMap
    (x : discreteEnergyStrictSublevel (t ∘ r) p q c) :
    discreteEnergyForgetMap ht r h0 hlast p q c
      (discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont x) = x := by
  apply Subtype.ext
  rw [discreteEnergyForgetMap_apply, discreteEnergyInsertMap_apply]
  exact discreteEnergyForget_discreteEnergyInsert ht r h0 hlast p q x (γ x)
    (fun i ↦ (hγ x i).source) (fun i ↦ (hγ x i).target)

/-- Forgetting the newly inserted vertices is a left inverse to continuous geodesic insertion. -/
@[simp]
theorem discreteEnergyForgetMap_comp_discreteEnergyInsertMap :
    (discreteEnergyForgetMap ht r h0 hlast p q c).comp
        (discreteEnergyInsertMap ht r h0 hlast p q c γ hγ hcont) =
      ContinuousMap.id (discreteEnergyStrictSublevel (t ∘ r) p q c) := by
  ext x
  simp

end Sublevel

/-- Insertion for the identity selection is the identity on the strict energy sublevel. -/
@[simp]
theorem discreteEnergyInsertMap_refl {t : Fin (n + 2) → ℝ} (ht : StrictMono t)
    (p q : M) (c : ℝ)
    (γ : discreteEnergyStrictSublevel t p q c → Fin (n + 1) → ℝ → M)
    (hγ : ∀ x i, IsGeodesicSegment (γ x i)
      ((Fin.cons p (Fin.snoc (x : Fin n → M) q) : Fin (n + 2) → M) i.castSucc)
      ((Fin.cons p (Fin.snoc (x : Fin n → M) q) : Fin (n + 2) → M) i.succ))
    (hcont : ∀ i u, u ∈ Set.Icc (0 : ℝ) 1 → Continuous (fun x ↦ γ x i u)) :
    discreteEnergyInsertMap ht (RelEmbedding.refl (· ≤ ·)) (by simp) (by simp)
      p q c γ hγ hcont = ContinuousMap.id (discreteEnergyStrictSublevel t p q c) := by
  apply ContinuousMap.ext
  intro x
  have h := discreteEnergyForgetMap_discreteEnergyInsertMap ht
    (RelEmbedding.refl (· ≤ ·)) (by simp) (by simp) p q c γ hγ hcont x
  rw [discreteEnergyForgetMap_refl] at h
  exact h

end Metric

end TauCeti
