/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Subsequences converging in `Lᵖ` on compact subsets

Let `Ω` be an open subset of a second-countable locally compact Hausdorff space. If a sequence of
functions is relatively compact in `Lᵖ(K)` for every compact `K ⊆ Ω`, then a single subsequence
converges in `Lᵖ(K)` for every such `K`, to the restrictions of one function `v`
(`TauCeti.exists_subseq_tendsto_eLpNorm_sub_of_isCompact_closure`). This is the diagonal
argument which turns compactness on each compact subset into sequential compactness in
`Lᵖ_loc(Ω)`, as used by compactness theorems for Sobolev and bounded variation functions.

The subsequence is extracted at once from the countable product of the spaces `Lᵖ(L m)` over a
compact exhaustion `L` of `Ω`, a product which is first countable, so that its compact subsets
are sequentially compact. The limits on the sets `L m` agree almost everywhere where they
overlap, and are glued along the exhaustion
(`TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter`).

## Main results

* `TauCeti.exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter`: functions on a sequence of
  measurable sets which agree almost everywhere on the pairwise intersections glue to a single
  function.
* `TauCeti.exists_subseq_tendsto_eLpNorm_sub_of_isCompact_closure`: a sequence relatively compact
  in `Lᵖ(K)` for every compact `K ⊆ Ω` has a subsequence converging in `Lᵖ_loc(Ω)`.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Gluing along a sequence of sets.** If `L` is a sequence of measurable sets and the functions
`a m` are compatible, in the sense that `a k = a m` almost everywhere on `L k ∩ L m`, then a single
function agrees almost everywhere on each `L m` with `a m`. -/
theorem exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter {Y : Type*} {L : ℕ → Set X}
    (hL : ∀ m, MeasurableSet (L m)) {a : ℕ → X → Y}
    (ha : ∀ k m, a k =ᵐ[μ.restrict (L k ∩ L m)] a m) :
    ∃ v : X → Y, ∀ m, v =ᵐ[μ.restrict (L m)] a m := by
  classical
  -- On the points of `⋃ k, L k`, take `v = a k` for the least `k` with the point in `L k`.
  refine ⟨fun y => if h : ∃ m, y ∈ L m then a (Nat.find h) y else a 0 y, fun m => ?_⟩
  have hall : ∀ᵐ y ∂μ.restrict (L m), ∀ k, y ∈ L k → a k y = a m y := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [ae_restrict_of_ae ((ae_restrict_iff' ((hL k).inter (hL m))).1 (ha k m)),
      ae_restrict_mem (hL m)] with y hy hym hyk using hy ⟨hyk, hym⟩
  filter_upwards [hall, ae_restrict_mem (hL m)] with y hy hym
  have h : ∃ m, y ∈ L m := ⟨m, hym⟩
  rw [dite_eq_left h]
  exact hy _ (Nat.find_spec h)

variable {F : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [OpensMeasurableSpace X] [NormedAddCommGroup F] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {Ω : Set X} {u : ℕ → X → F}

/-- **Sequential compactness in `Lᵖ_loc`.** Let `Ω` be open, and let `u n` be a sequence of
functions in `Lᵖ(K)` for every compact `K ⊆ Ω` whose classes form a relatively compact subset of
`Lᵖ(K)` for every such `K`. Then there are a function `v`, in `Lᵖ(K)` for every compact `K ⊆ Ω`,
and a subsequence `u ∘ φ` converging to `v` in `Lᵖ(K)` for every compact `K ⊆ Ω`. -/
theorem exists_subseq_tendsto_eLpNorm_sub_of_isCompact_closure (hΩ : IsOpen Ω)
    (hu : ∀ n K, IsCompact K → K ⊆ Ω → MemLp (u n) p (μ.restrict K))
    (hcpt : ∀ K, IsCompact K → K ⊆ Ω →
      IsCompact (closure {f : Lp F p (μ.restrict K) | ∃ n, f =ᵐ[μ.restrict K] u n})) :
    ∃ v : X → F, (∀ K, IsCompact K → K ⊆ Ω → MemLp v p (μ.restrict K)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K, IsCompact K → K ⊆ Ω →
        Tendsto (fun j => eLpNorm (u (φ j) - v) p (μ.restrict K)) atTop (𝓝 0) := by
  -- A compact exhaustion `L` of `Ω`.
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let Kx : CompactExhaustion Ω := CompactExhaustion.choice Ω
  let L : ℕ → Set X := fun m => (↑) '' Kx m
  have hLc (m : ℕ) : IsCompact (L m) := (Kx.isCompact m).image continuous_subtype_val
  have hLm (m : ℕ) : MeasurableSet (L m) := (hLc m).isClosed.measurableSet
  have hLΩ (m : ℕ) : L m ⊆ Ω := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hLmono : Monotone L := fun m m' h => image_mono (Kx.subset h)
  have hLsup (K : Set X) (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ m, K ⊆ L m := by
    have hK' : IsCompact (((↑) : Ω → X) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
    obtain ⟨m, hm⟩ := Kx.exists_superset_of_isCompact hK'
    exact ⟨m, fun x hx => ⟨⟨x, hKΩ hx⟩, hm hx, rfl⟩⟩
  -- A single subsequence converges in every `Lᵖ(L m)`, by sequential compactness of the
  -- product of the compact sets given by `hcpt`.
  let x : ℕ → ∀ m, Lp F p (μ.restrict (L m)) := fun n m =>
    (hu n (L m) (hLc m) (hLΩ m)).toLp (u n)
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi fun m => hcpt (L m) (hLc m) (hLΩ m)).tendsto_subseq (x := x)
      fun n m _ => subset_closure ⟨n, MemLp.coeFn_toLp _⟩
  have hconv (m : ℕ) :
      Tendsto (fun j => eLpNorm (u (φ j) - ⇑(a m)) p (μ.restrict (L m))) atTop (𝓝 0) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun j => x (φ j) m) (a m)).1
      (tendsto_pi_nhds.1 hlim m)).congr fun j =>
        eLpNorm_congr_ae ((MemLp.coeFn_toLp (hu (φ j) (L m) (hLc m) (hLΩ m))).sub .rfl)
  -- The limits are compatible: `a k = a m` almost everywhere on `L k` for `k ≤ m`.
  have hcompat_le {k m : ℕ} (hkm : k ≤ m) : (a k : X → F) =ᵐ[μ.restrict (L k)] a m := by
    have hle (j : ℕ) : eLpNorm (⇑(a k) - ⇑(a m)) p (μ.restrict (L k)) ≤
        eLpNorm (u (φ j) - ⇑(a k)) p (μ.restrict (L k)) +
          eLpNorm (u (φ j) - ⇑(a m)) p (μ.restrict (L m)) := by
      calc eLpNorm (⇑(a k) - ⇑(a m)) p (μ.restrict (L k))
          = eLpNorm ((u (φ j) - ⇑(a m)) - (u (φ j) - ⇑(a k))) p (μ.restrict (L k)) := by
            rw [sub_sub_sub_cancel_left]
        _ ≤ eLpNorm (u (φ j) - ⇑(a m)) p (μ.restrict (L k)) +
              eLpNorm (u (φ j) - ⇑(a k)) p (μ.restrict (L k)) := eLpNorm_sub_le Fact.out
        _ ≤ _ := by
            rw [add_comm]
            gcongr
            exact hLmono hkm
    have h0 : eLpNorm (⇑(a k) - ⇑(a m)) p (μ.restrict (L k)) = 0 :=
      le_antisymm (ge_of_tendsto' (by simpa using (hconv k).add (hconv m)) hle) zero_le
    filter_upwards [(eLpNorm_eq_zero_iff (zero_lt_one.trans_le Fact.out).ne').1 h0] with y hy
    simpa [sub_eq_zero] using hy
  have hcompat (k m : ℕ) : (a k : X → F) =ᵐ[μ.restrict (L k ∩ L m)] a m := by
    rcases le_total k m with hkm | hmk
    · rw [inter_eq_left.2 (hLmono hkm)]
      exact hcompat_le hkm
    · rw [inter_eq_right.2 (hLmono hmk)]
      exact (hcompat_le hmk).symm
  -- Glue the limits along the exhaustion.
  obtain ⟨v, hva⟩ := exists_forall_ae_eq_restrict_of_ae_eq_restrict_inter (μ := μ) hLm hcompat
  refine ⟨v, fun K hK hKΩ => ?_, φ, hφ, fun K hK hKΩ => ?_⟩ <;>
    obtain ⟨m, hKm⟩ := hLsup K hK hKΩ
  · exact ((Lp.memLp (a m)).ae_eq (hva m).symm).mono_measure
      (Measure.restrict_mono hKm le_rfl)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hconv m)
      (fun _ => zero_le) fun j => ?_
    calc eLpNorm (u (φ j) - v) p (μ.restrict K)
        ≤ eLpNorm (u (φ j) - v) p (μ.restrict (L m)) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono hKm le_rfl)
      _ = eLpNorm (u (φ j) - ⇑(a m)) p (μ.restrict (L m)) :=
          eLpNorm_congr_ae (EventuallyEq.rfl.sub (hva m))

end TauCeti
