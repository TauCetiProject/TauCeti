/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Grids separating a finite set of reals

A finite set `C` of real numbers can be separated by a bi-infinite arithmetic progression
`a q = t + q h`, `q ∈ ℤ`: choose the step `h` smaller than the distance between any two points
of `C`, so that each closed interval `[a q, a (q + 1)]` contains at most one point of `C`, and
choose the offset `t` outside the countable set `C - hℤ`, so that no grid point lies in `C`
(`Set.Finite.exists_strictMono_notMem_subsingleton_inter_Icc`).

For the critical values of a function this is a sequence of regular values whose consecutive
bands each contain at most one critical value; the sublevels at these values filter the space by
its critical levels.

The remaining two results hold for a finite set `C` in any linear order, respectively in any
densely ordered linear order. Between two points `a₀ < a₁` of `C`, the points of `C ∩ [a₀, a₁]`
can be listed in increasing order `a₀ = d 0 < ⋯ < d (m + 1) = a₁`, with no point of `C` between
two consecutive ones (`Set.Finite.exists_strictMono_fin_consecutive`). There is also a finite
version with exactly one point of `C` in each band: points `b 0 < ⋯ < b m` chosen strictly between
consecutive points of `C ∩ [a₀, a₁]` avoid `C`, and `[a₀, b 0]`, each `[b i, b (i + 1)]` and
`[b m, a₁]` contain exactly one point of `C`
(`Set.Finite.exists_strictMono_notMem_inter_Icc_eq_singleton`). For the actions of the periodic
orbits of a Hamiltonian, these are the values at which a breaking sequence of Floer
trajectories is normalized, one between each pair of consecutive orbit actions.
-/

public section

open Filter Set Topology

/-- **A grid separating a finite set of reals.** For a finite set `C ⊆ ℝ` there is a strictly
increasing sequence `a : ℤ → ℝ`, tending to `-∞` and to `∞`, which avoids `C` and whose
consecutive closed intervals `[a q, a (q + 1)]` each contain at most one point of `C`. -/
theorem Set.Finite.exists_strictMono_notMem_subsingleton_inter_Icc {C : Set ℝ} (hC : C.Finite) :
    ∃ a : ℤ → ℝ, StrictMono a ∧ Tendsto a atBot atBot ∧ Tendsto a atTop atTop ∧
      (∀ q, a q ∉ C) ∧ ∀ q, (C ∩ Icc (a q) (a (q + 1))).Subsingleton := by
  -- A step `h` smaller than the distance between any two distinct points of `C`.
  obtain ⟨h, hsep, hh⟩ : ∃ h : ℝ, (∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → h < |c - c'|) ∧ 0 < h := by
    have : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → h < |c - c'| := by
      refine (eventually_all_finite hC).2 fun c _ ↦ (eventually_all_finite hC).2 fun c' _ ↦ ?_
      by_cases hcc : c = c'
      · exact Eventually.of_forall fun _ hne ↦ absurd hcc hne
      · filter_upwards [nhdsWithin_le_nhds
          (eventually_lt_nhds (abs_pos.2 (sub_ne_zero.2 hcc)))] with _ hlt _ using hlt
    exact (this.and self_mem_nhdsWithin).exists
  -- The offsets `t` for which the grid `t + q h` meets `C` form a countable set.
  have hbad : (⋃ c ∈ C, range fun q : ℤ ↦ c - q * h).Countable :=
    hC.countable.biUnion fun _ _ ↦ countable_range _
  obtain ⟨t, ht⟩ := (hbad.dense_compl ℝ).nonempty
  refine ⟨fun q ↦ t + q * h, fun q q' hqq' ↦ ?_, ?_, ?_, fun q hq ↦ ?_, fun q ↦ ?_⟩
  · have : (q : ℝ) < q' := Int.cast_lt.2 hqq'
    dsimp only
    nlinarith
  · exact tendsto_atBot_add_const_left _ t
      ((tendsto_intCast_atBot_iff.2 tendsto_id).atBot_mul_const hh)
  · exact tendsto_atTop_add_const_left _ t (tendsto_intCast_atTop_atTop.atTop_mul_const hh)
  · exact ht (mem_biUnion hq ⟨q, by ring⟩)
  · rintro x ⟨hx, hx₁, hx₂⟩ y ⟨hy, hy₁, hy₂⟩
    by_contra hxy
    push_cast at hx₂ hy₂
    have := hsep x hx y hy hxy
    have : |x - y| ≤ h := abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
    linarith

/-- **Listing the points of a finite set between two of its points.** Let `C` be a finite subset
of a linear order and let `a₀ < a₁` be two of its points. The points of `C` in `[a₀, a₁]` can
be listed in increasing order `a₀ = d 0 < d 1 < ⋯ < d (m + 1) = a₁`, and no point of `C` lies
strictly between two consecutive ones. -/
theorem Set.Finite.exists_strictMono_fin_consecutive {α : Type*} [LinearOrder α] {C : Set α}
    (hC : C.Finite) {a₀ a₁ : α} (h₀ : a₀ ∈ C) (h₁ : a₁ ∈ C) (h : a₀ < a₁) :
    ∃ m : ℕ, ∃ d : Fin (m + 2) → α, StrictMono d ∧ (∀ j, d j ∈ C) ∧ d 0 = a₀ ∧
      d (Fin.last (m + 1)) = a₁ ∧
      ∀ (i : Fin (m + 1)) {x : α}, x ∈ C → d i.castSucc < x → x < d i.succ → False := by
  set s := (hC.inter_of_left (Icc a₀ a₁)).toFinset with hs
  have hmem {x : α} : x ∈ s ↔ x ∈ C ∧ x ∈ Icc a₀ a₁ := by simp [hs]
  have hcard : 2 ≤ s.card := by
    have hsub : ({a₀, a₁} : Finset α) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hmem.2 ⟨h₀, le_rfl, h.le⟩
      · rw [Finset.mem_singleton.1 hx]
        exact hmem.2 ⟨h₁, h.le, le_rfl⟩
    simpa [Finset.card_pair h.ne] using Finset.card_le_card hsub
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 2 := ⟨s.card - 2, by omega⟩
  set d := s.orderEmbOfFin hm
  have hdI (j : Fin (m + 2)) : d j ∈ Icc a₀ a₁ := (hmem.1 (s.orderEmbOfFin_mem hm j)).2
  -- Every point of `C` in `[a₀, a₁]` is some `d j`.
  have hd {x : α} (hx : x ∈ C) (hxI : x ∈ Icc a₀ a₁) : ∃ j, d j = x := by
    have hx' : x ∈ Set.range d := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (hmem.2 ⟨hx, hxI⟩)
    exact Set.mem_range.1 hx'
  refine ⟨m, d, d.strictMono, fun j ↦ (hmem.1 (s.orderEmbOfFin_mem hm j)).1, ?_, ?_,
    fun i x hx hx₁ hx₂ ↦ ?_⟩
  · obtain ⟨j, hj⟩ := hd h₀ ⟨le_rfl, h.le⟩
    exact le_antisymm (hj ▸ d.monotone (Fin.zero_le j)) (hdI 0).1
  · obtain ⟨j, hj⟩ := hd h₁ ⟨h.le, le_rfl⟩
    exact le_antisymm (hdI _).2 (hj ▸ d.monotone (Fin.le_last j))
  · obtain ⟨j, rfl⟩ := hd hx ⟨(hdI _).1.trans hx₁.le, hx₂.le.trans (hdI _).2⟩
    have h₁ := d.lt_iff_lt.1 hx₁
    have h₂ := d.lt_iff_lt.1 hx₂
    rw [Fin.lt_def, Fin.val_castSucc] at h₁
    rw [Fin.lt_def, Fin.val_succ] at h₂
    omega

/-- **Finitely many points separating a finite set between two of its points.** Let `C` be a
finite subset of a densely ordered linear order and let `a₀ < a₁` be two of its points. There are
strictly increasing points `b 0 < ⋯ < b m` in `(a₀, a₁)`, none of them in `C`, such that `a₀`
is the only point of `C` in `[a₀, b 0]`, `a₁` is the only point of `C` in `[b m, a₁]`, and each
`[b i, b (i + 1)]` contains exactly one point of `C`. -/
theorem Set.Finite.exists_strictMono_notMem_inter_Icc_eq_singleton {α : Type*} [LinearOrder α]
    [DenselyOrdered α] {C : Set α} (hC : C.Finite) {a₀ a₁ : α} (h₀ : a₀ ∈ C) (h₁ : a₁ ∈ C)
    (h : a₀ < a₁) :
    ∃ m : ℕ, ∃ b : Fin (m + 1) → α, StrictMono b ∧ (∀ i, b i ∉ C) ∧ a₀ < b 0 ∧
      b (Fin.last m) < a₁ ∧ C ∩ Icc a₀ (b 0) = {a₀} ∧ C ∩ Icc (b (Fin.last m)) a₁ = {a₁} ∧
      ∀ i : Fin m, ∃ c, C ∩ Icc (b i.castSucc) (b i.succ) = {c} := by
  -- The points of `C` in `[a₀, a₁]`, in increasing order `a₀ = d 0 < d 1 < ⋯ < d (m + 1) = a₁`.
  obtain ⟨m, d, hdm, hdC, hd0, hdl, hgap⟩ := hC.exists_strictMono_fin_consecutive h₀ h₁ h
  -- `b i` lies strictly between `d i` and `d (i + 1)`.
  choose b hbl hbu using fun i : Fin (m + 1) ↦ exists_between (hdm (Fin.castSucc_lt_succ (i := i)))
  have hb0 : a₀ < b 0 := by simpa [hd0] using hbl 0
  have hbm : b (Fin.last m) < a₁ := by simpa [hdl] using hbu (Fin.last m)
  -- `d (i + 1)` lies strictly between `b i` and `b (i + 1)`.
  have hbd (i : Fin m) : b i.castSucc < d i.succ.castSucc ∧ d i.succ.castSucc < b i.succ :=
    ⟨Fin.succ_castSucc i ▸ hbu i.castSucc, hbl i.succ⟩
  refine ⟨m, b, Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_, fun i hi ↦ hgap i hi (hbl i) (hbu i),
    hb0, hbm, ?_, ?_, fun i ↦ ?_⟩
  · exact (hbd i).1.trans (hbd i).2
  · refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨h₀, le_rfl, hb0.le⟩, fun x ⟨hx, hx₁, hx₂⟩ ↦ ?_⟩
    by_contra hne
    exact hgap 0 hx (by simpa [hd0] using lt_of_le_of_ne hx₁ (Ne.symm hne))
      (hx₂.trans_lt (hbu 0))
  · refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨h₁, hbm.le, le_rfl⟩, fun x ⟨hx, hx₁, hx₂⟩ ↦ ?_⟩
    by_contra hne
    exact hgap (Fin.last m) hx ((hbl _).trans_le hx₁)
      (by simpa [hdl] using lt_of_le_of_ne hx₂ hne)
  · -- The only point of `C` in `[b i, b (i + 1)]` is `d (i + 1)`.
    refine ⟨d i.succ.castSucc, Set.eq_singleton_iff_unique_mem.2
      ⟨⟨hdC _, (hbd i).1.le, (hbd i).2.le⟩, fun x ⟨hx, hx₁, hx₂⟩ ↦ ?_⟩⟩
    rcases lt_trichotomy x (d i.succ.castSucc) with hlt' | heq | hgt
    · exact (hgap i.castSucc hx ((hbl _).trans_le hx₁)
        (by rw [Fin.succ_castSucc]; exact hlt')).elim
    · exact heq
    · exact (hgap i.succ hx hgt (hx₂.trans_lt (hbu _))).elim
