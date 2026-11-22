/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.WithBot

import Mathlib.Order.SuccPred.Nat
import TauCeti.Order.SuccPred.IntermediateValue

/-!
# Diagonal indices and floor cutoffs along `atTop`

If for every `k` a property `P k n` holds for all large `n`, then an index `κ n` tending to
infinity can be chosen so slowly that `P (κ n) n` holds for all large `n`
(`TauCeti.exists_tendsto_atTop_of_forall_eventually`). This is the diagonal step of constructions
that must meet countably many eventual requirements at once with a single sequence, such as a
recovery sequence built from a countable neighbourhood basis. It complements Mathlib's
`Filter.extraction_forall_of_eventually`, which meets the requirements along a subsequence
instead.

The second statement is diagonal extraction for countably many properties of extractions
(`TauCeti.extraction_forall`): if every extraction has, for each `j`, a further extraction with
the property `P j`, then one extraction is, for every `j`, eventually a subsequence of an
extraction with the property `P j`. In particular, a single subsequence makes countably many
sequences converge at once when every subsequence of each of them has a convergent further
subsequence (`TauCeti.extraction_forall_exists_tendsto`). This is the compactness step of the
Arzelà–Ascoli theorem. For finitely many properties of extractions, each preserved by further
extraction, the same holds one property at a time (`TauCeti.extraction_forall_mem_finset`).

Finally, a sequence converges along `atTop` exactly when it does so along real (or other floor
semiring) cutoffs `x ↦ u ⌊x⌋₊` (`TauCeti.tendsto_comp_natFloor_iff`). This compares limits of
partial sums `∑ n ≤ x` taken over real and over natural cutoffs. More generally, a reindexing
`g : ℕ → ℕ` that tends to infinity and eventually never increases by more than one at a time
takes every large value, so `map g atTop = atTop` (`TauCeti.map_atTop_eq_of_le_add_one`) and
`u ∘ g` converges exactly when `u` does (`TauCeti.tendsto_comp_iff_of_le_add_one`). For instance,
a partial product over the primes `p ≤ n` is a function of the prime count `π n`, which moves in
steps of at most one.

In a ring of characteristic zero without zero divisors, `a + k * b` vanishes for all large natural
numbers `k` exactly when `a = b = 0`, and otherwise it is nonzero for all large `k`
(`TauCeti.eventually_add_mul_eq_zero_iff`): it vanishes for at most one `k` unless `b = 0`. In an
Archimedean ordered semiring, truncating a finite `WithTop` element at natural casts eventually
stabilizes (`WithTop.eventually_min_natCast_eq`).
-/

public section

open Filter

namespace TauCeti

/-- If for every `k` the property `P k n` holds for all large `n`, then there is an index `κ n`
tending to infinity with `P (κ n) n` for all large `n`. -/
theorem exists_tendsto_atTop_of_forall_eventually {P : ℕ → ℕ → Prop}
    (h : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ κ : ℕ → ℕ, Tendsto κ atTop atTop ∧ ∀ᶠ n in atTop, P (κ n) n := by
  classical
  choose N hN using fun k ↦ eventually_atTop.1 (h k)
  -- `κ n` is the largest `k ≤ n` such that `N j ≤ n` for every `j ≤ k`.
  refine ⟨fun n ↦ Nat.findGreatest (fun k ↦ ∀ j ≤ k, N j ≤ n) n, tendsto_atTop.2 fun k ↦ ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop k, (eventually_all_finset (Finset.range (k + 1))).2
      fun j _ ↦ eventually_ge_atTop (N j)] with n hkn hn
    exact Nat.le_findGreatest hkn fun j hj ↦ hn j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    refine hN _ _ (Nat.findGreatest_spec (P := fun k ↦ ∀ j ≤ k, N j ≤ n) (Nat.zero_le n)
      (fun j hj ↦ ?_) _ le_rfl)
    rwa [Nat.le_zero.1 hj]

/-- **Diagonal extraction for countably many properties.** Let `P j` be properties of extractions
`ψ : ℕ → ℕ`, for `j ∈ ℕ`. If every extraction has, for each `j`, a further extraction with property
`P j`, then there is one extraction `D` which for every `j` is, from the index `j` on, a
subsequence of an extraction `ψ` with property `P j`: each `D n` with `j ≤ n` is a term `ψ k` with
`n ≤ k`. So `D` is eventually a reindexing of `ψ` along a map tending to infinity
(`TauCeti.exists_tendsto_eventuallyEq_comp_of_eq_apply_of_le`), and properties of the form
`∀ᶠ n in atTop, Q (ψ n)` pass from `ψ` to `D` (`TauCeti.eventually_of_eq_apply_of_le`). -/
theorem extraction_forall {P : ℕ → (ℕ → ℕ) → Prop}
    (h : ∀ j (ψ : ℕ → ℕ), StrictMono ψ → ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ P j (ψ ∘ ψ')) :
    ∃ D : ℕ → ℕ, StrictMono D ∧
      ∀ j, ∃ ψ : ℕ → ℕ, P j ψ ∧ ∀ n, j ≤ n → ∃ k, n ≤ k ∧ D n = ψ k := by
  choose ψ' hψ' hP using h
  -- `θ j` is the extraction with the properties `P 0, …, P j`, each refining the previous one.
  let θ : ℕ → {ψ : ℕ → ℕ // StrictMono ψ} := fun j ↦ Nat.rec
    ⟨ψ' 0 id strictMono_id, hψ' 0 id strictMono_id⟩
    (fun j θj ↦ ⟨θj.val ∘ ψ' (j + 1) θj.val θj.property, θj.property.comp (hψ'
        (j + 1) θj.val θj.property)⟩) j
  have hθ0 : (θ 0).val = ψ' 0 id strictMono_id := rfl
  have hθsucc j : (θ (j + 1)).val = (θ j).val ∘ ψ' (j + 1) (θ j).val (θ j).property := rfl
  have hθ j : P j (θ j).val := by
    cases j with
    | zero => exact hθ0 ▸ hP 0 id strictMono_id
    | succ j => exact (hθsucc j) ▸ hP (j + 1) (θ j).val (θ j).property
  -- Every later `θ n` is a subsequence of `θ j`.
  have hsub j n (hjn : j ≤ n) a : ∃ b, a ≤ b ∧ (θ n).val a = (θ j).val b := by
    induction n, hjn using Nat.le_induction generalizing a with
    | base => exact ⟨a, le_rfl, rfl⟩
    | succ n _ ih =>
      obtain ⟨b, hab, hb⟩ := ih (ψ' (n + 1) (θ n).val (θ n).property a)
      exact ⟨b, ((hψ' _ _ _).id_le a).trans hab, by rw [hθsucc]; exact hb⟩
  -- The diagonal extraction `n ↦ θ n n`.
  refine ⟨fun n ↦ (θ n).val n, strictMono_nat_of_lt_succ fun n ↦ ?_,
    fun j ↦ ⟨(θ j).val, hθ j, fun n hjn ↦ hsub j n hjn n⟩⟩
  rw [hθsucc]
  exact (θ n).property.monotone ((hψ' _ _ _).id_le _) |>.trans_lt' ((θ n).property n.lt_succ_self)

/-- A sequence `D` whose terms from some index on are terms `ψ k` with `k ≥ n` is eventually the
reindexing `ψ ∘ f` of `ψ` along a map `f` tending to infinity. This is how the properties of the
extractions given by `TauCeti.extraction_forall` pass to the diagonal. -/
theorem exists_tendsto_eventuallyEq_comp_of_eq_apply_of_le {ψ D : ℕ → ℕ} {m : ℕ}
    (hD : ∀ n, m ≤ n → ∃ k, n ≤ k ∧ D n = ψ k) :
    ∃ f : ℕ → ℕ, Tendsto f atTop atTop ∧ D =ᶠ[atTop] ψ ∘ f := by
  choose! f hf using hD
  have hev : ∀ᶠ n in atTop, n ≤ f n ∧ D n = ψ (f n) := (eventually_ge_atTop m).mono hf
  exact ⟨f, tendsto_atTop_mono' atTop (hev.mono fun _ h ↦ h.1) tendsto_id, hev.mono fun _ h ↦ h.2⟩

/-- A property eventually true along a sequence `ψ` is eventually true along a sequence `D` whose
terms from some index on are terms `ψ k` with `k ≥ n`. -/
theorem eventually_of_eq_apply_of_le {p : ℕ → Prop} {ψ D : ℕ → ℕ} {m : ℕ}
    (hD : ∀ n, m ≤ n → ∃ k, n ≤ k ∧ D n = ψ k) (h : ∀ᶠ k in atTop, p (ψ k)) :
    ∀ᶠ n in atTop, p (D n) := by
  obtain ⟨f, hf, hDf⟩ := exists_tendsto_eventuallyEq_comp_of_eq_apply_of_le hD
  filter_upwards [hDf, hf.eventually h] with n hn hp
  rwa [hn]

/-- **Diagonal extraction.** Let `x j : ℕ → X` be countably many sequences and `l y` the filter of
a convergence to `y` on `X`. If every subsequence of every `x j` has a further subsequence
converging to some point, then one subsequence makes every `x j` converge. -/
theorem extraction_forall_exists_tendsto {X : Type*} {l : X → Filter X} {x : ℕ → ℕ → X}
    (h : ∀ j (ψ : ℕ → ℕ), StrictMono ψ →
      ∃ y, ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ Tendsto (fun n ↦ x j (ψ (ψ' n))) atTop (l y)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ j, ∃ y, Tendsto (fun n ↦ x j (ψ n)) atTop (l y) := by
  obtain ⟨D, hD, hP⟩ := extraction_forall
    (P := fun j ψ ↦ ∃ y, Tendsto (fun n ↦ x j (ψ n)) atTop (l y)) fun j ψ hψ ↦ by
      obtain ⟨y, ψ', hψ', hy⟩ := h j ψ hψ
      exact ⟨ψ', hψ', y, hy⟩
  refine ⟨D, hD, fun j ↦ ?_⟩
  obtain ⟨ψ, ⟨z, hz⟩, hψD⟩ := hP j
  obtain ⟨f, hf, hDf⟩ := exists_tendsto_eventuallyEq_comp_of_eq_apply_of_le hψD
  exact ⟨z, (hz.comp hf).congr' (hDf.fun_comp (x j)).symm⟩

/-- **Common extraction for finitely many properties.** Let `P i` be properties of extractions
`ψ : ℕ → ℕ`, for `i` in a finite set `s`, each preserved by passing to a further extraction. If
every extraction has, for each `i ∈ s`, a further extraction with property `P i`, then a single
extraction has every property `P i`, `i ∈ s`. -/
theorem extraction_forall_mem_finset {ι : Type*} {s : Finset ι} {P : ι → (ℕ → ℕ) → Prop}
    (h : ∀ i ∈ s, ∀ ψ : ℕ → ℕ, StrictMono ψ → ∃ ψ' : ℕ → ℕ, StrictMono ψ' ∧ P i (ψ ∘ ψ'))
    (hP : ∀ i ∈ s, ∀ ψ ψ' : ℕ → ℕ, StrictMono ψ' → P i ψ → P i (ψ ∘ ψ')) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ i ∈ s, P i ψ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, by simp⟩
  | insert a s _ ih =>
    obtain ⟨ψ, hψ, hs⟩ := ih (fun i hi ↦ h i (Finset.mem_insert_of_mem hi))
      fun i hi ↦ hP i (Finset.mem_insert_of_mem hi)
    obtain ⟨ψ', hψ', ha⟩ := h a (Finset.mem_insert_self a s) ψ hψ
    exact ⟨ψ ∘ ψ', hψ.comp hψ', (Finset.forall_mem_insert _ _ _).2
      ⟨ha, fun i hi ↦ hP i (Finset.mem_insert_of_mem hi) ψ ψ' hψ' (hs i hi)⟩⟩

/-- A sequence `u` converges along `atTop` if and only if its values `u ⌊x⌋₊` at the natural
floors of `x` converge as `x → ∞` in a floor semiring such as `ℝ`. -/
theorem tendsto_comp_natFloor_iff {R X : Type*} [Semiring R] [LinearOrder R]
    [FloorSemiring R] {u : ℕ → X} {l : Filter X} :
    Tendsto (fun x : R ↦ u ⌊x⌋₊) atTop l ↔ Tendsto u atTop l := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp ?_⟩
  · have hcast : Tendsto (fun n : ℕ ↦ (n : R)) atTop atTop :=
      tendsto_atTop_atTop.2 fun x ↦
        ⟨⌈x⌉₊, fun n hn ↦ Nat.le_of_ceil_le hn⟩
    simpa [Function.comp_def] using h.comp hcast
  · exact tendsto_atTop_atTop.2 fun n ↦ ⟨n, fun x hx ↦ Nat.le_floor hx⟩

/-- A map `g : ℕ → ℕ` that tends to infinity and eventually increases by at most one at each step
takes every large value, so it pushes `atTop` forward to `atTop`. -/
theorem map_atTop_eq_of_le_add_one {g : ℕ → ℕ} (hg : Tendsto g atTop atTop)
    (hle : ∀ᶠ n in atTop, g (n + 1) ≤ g n + 1) : map g atTop = atTop := by
  refine le_antisymm hg (le_map fun s hs ↦ ?_)
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((eventually_mem_set.2 hs).and hle)
  -- Every value `m ≥ g K` is attained at some index `n ≥ K`.
  suffices h : ∀ m, g K ≤ m → ∃ n, K ≤ n ∧ g n = m from mem_atTop_sets.2 ⟨g K, fun m hm ↦ by
    obtain ⟨n, hn, rfl⟩ := h m hm
    exact ⟨n, (hK n hn).1, rfl⟩⟩
  intro m hm
  obtain ⟨A, hA⟩ := (hg.eventually_ge_atTop m).exists_forall_of_atTop
  obtain ⟨n, hn, hgn⟩ := Nat.exists_mem_Icc_eq_of_le_succ (le_max_left K A)
    (fun i hKi _ ↦ (hK i hKi).2) hm (hA (max K A) (le_max_right K A))
  exact ⟨n, hn.1, hgn⟩

/-- If `g : ℕ → ℕ` tends to infinity and eventually increases by at most one at each step, then
`u ∘ g` converges along `atTop` exactly when `u` does. -/
theorem tendsto_comp_iff_of_le_add_one {X : Type*} {g : ℕ → ℕ} (hg : Tendsto g atTop atTop)
    (hle : ∀ᶠ n in atTop, g (n + 1) ≤ g n + 1) {u : ℕ → X} {l : Filter X} :
    Tendsto (u ∘ g) atTop l ↔ Tendsto u atTop l := by
  rw [← tendsto_map'_iff, map_atTop_eq_of_le_add_one hg hle]

/-- In a ring of characteristic zero without zero divisors, `a + k * b` vanishes for all large
natural numbers `k` exactly when `a = b = 0`, and otherwise it is nonzero for all large `k`. -/
theorem eventually_add_mul_eq_zero_iff {R : Type*} [Ring R] [NoZeroDivisors R] [CharZero R]
    (a b : R) : ∀ᶠ k : ℕ in atTop, (a + k * b = 0 ↔ a = 0 ∧ b = 0) := by
  by_cases h : ∃ k₀ : ℕ, a + k₀ * b = 0
  · obtain ⟨k₀, hk₀⟩ := h
    filter_upwards [eventually_gt_atTop k₀] with k hk
    refine ⟨fun hk' ↦ ?_, fun ⟨ha, hb⟩ ↦ by simp [ha, hb]⟩
    -- Two vanishing values `k₀ < k` force `(k - k₀) * b = 0`, hence `b = 0`.
    have hb : b = 0 := by
      have : ((k : R) - k₀) * b = 0 := by
        rw [sub_mul, ← add_sub_add_left_eq_sub _ _ a, hk', hk₀, sub_zero]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (Nat.cast_injective.ne hk.ne'))
    exact ⟨by simpa [hb] using hk', hb⟩
  · push Not at h
    exact .of_forall fun k ↦ iff_of_false (h k) fun ⟨ha, hb⟩ ↦ h 0 (by simp [ha, hb])

end TauCeti

namespace WithTop

/-- Truncating a finite extended element at `(n : ι)` eventually leaves it unchanged. -/
theorem eventually_min_natCast_eq {ι : Type*} [Semiring ι] [LinearOrder ι] [IsOrderedRing ι]
    [Archimedean ι] {τ : WithTop ι} (hfin : τ ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, min ((n : ι) : WithTop ι) τ = τ := by
  cases τ with
  | top => exact absurd rfl hfin
  | coe s =>
    obtain ⟨N, hN⟩ := exists_nat_ge s
    filter_upwards [eventually_ge_atTop N] with n hn
    exact min_eq_right (WithTop.coe_le_coe.mpr (hN.trans (Nat.mono_cast hn)))

end WithTop
