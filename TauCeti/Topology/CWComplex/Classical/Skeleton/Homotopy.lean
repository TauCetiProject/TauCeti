/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.CWComplex

/-!
# Homotoping maps out of a relative CW complex skeleton by skeleton

Let `C` be a relative CW complex with base `D`. Several classical theorems homotope a map
`f : C → Y` to a map with better behaviour on each skeleton, one skeleton at a time: the cellular
approximation theorem homotopes a map of CW complexes to a cellular one, and the compression lemma
homotopes a map of pairs `(C, D) → (Y, B)` into `B`. This file supplies the two steps they share.

* **One dimension at a time.** Homotopies of the maps `f ∘ Φⱼ` on the closed unit ball, one for
  each `n`-cell `j` with characteristic map `Φⱼ` and each relative to the boundary sphere, are the
  restrictions of a single homotopy of `f` relative to `skeletonLT C n`
  (`TauCeti.exists_homotopicRel_cellMap`). The cell homotopies glue over the closed `n`-cells
  (`TauCeti.exists_continuousMap_prod_skeletonLT_succ`) to a homotopy on
  `skeletonLT C (n + 1)`, which the homotopy extension property of that skeleton
  (`TauCeti.hasHomotopyExtensionProperty_skeletonLT`) extends over `C`.
* **All dimensions.** Let `S n` be sets of `Y`, and suppose that every map sending
  `skeletonLT C n` into `S n` is homotopic relative to `skeletonLT C n` to a map that also sends
  `skeletonLT C (n + 1)` into `S (n + 1)`. Then every map sending the base `D` into `S 0` is
  homotopic relative to `D` to a map sending `skeletonLT C n` into `S n` for every `n`
  (`TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT`). The `n`-th of the successive
  homotopies is performed during the time interval `[1 - 2⁻ⁿ, 1 - 2⁻ⁿ⁻¹]`. The resulting single
  homotopy is continuous because on `skeletonLT C n` all the later homotopies are stationary, so
  there it is a finite concatenation, and a map out of `I × C` is continuous as soon as it is
  continuous on `I` times every skeleton
  (`TauCeti.exists_continuousMap_prod_complex_of_skeletonLT`).

## Main results

* `TauCeti.exists_homotopicRel_cellMap`: homotopies of the closed `n`-cells relative to their
  boundaries extend to a homotopy of the complex relative to `skeletonLT C n`.
* `TauCeti.exists_homotopicRel_forall_mapsTo_skeletonLT`: the infinite concatenation of homotopies
  improving a map one skeleton at a time.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, the proofs of Lemma 4.6 (the compression lemma) and Theorem 4.8 (cellular
  approximation).
* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter II.
-/

public section

noncomputable section

open Metric Set Topology Topology.RelCWComplex unitInterval

namespace TauCeti

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
  {Y : Type v} [TopologicalSpace Y]

section Step

/-- **Homotoping a map one dimension at a time.** Let `f : C → Y` be a map out of a relative CW
complex, and for every `n`-cell `j` let `f ∘ Φⱼ` be homotopic, relative to the boundary sphere, to
a map `ψ j` of the closed unit ball, where `Φⱼ` is the characteristic map of `j`. Then `f` is
homotopic relative to `skeletonLT C n` to a map `g` with `g ∘ Φⱼ = ψ j` for every `n`-cell `j`. -/
theorem exists_homotopicRel_cellMap (n : ℕ) (f : C(C, Y))
    (ψ : cell C n → C(closedBall (0 : Fin n → ℝ) 1, Y))
    (hψ : ∀ j, (f.comp (cellMap j)).HomotopicRel (ψ j) {y | (y : Fin n → ℝ) ∈ sphere 0 1}) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ skeletonLT C n} ∧
      ∀ j y, g (cellMap j y) = ψ j y := by
  let H (j : cell C n) := (hψ j).some
  -- Glue the cell homotopies over the closed `n`-cells, stationary on `skeletonLT C n`.
  obtain ⟨F, hFG, hFH⟩ := exists_continuousMap_prod_skeletonLT_succ (Z := I) (n := n)
    (f.comp ⟨fun p : I × (skeletonLT C n : Set X) ↦ ⟨p.2, (skeletonLT C n).subset_complex p.2.2⟩,
      by fun_prop⟩)
    (fun j ↦ (H j).toContinuousMap) (fun j t y hy ↦ ((H j).eq_fst t hy).trans (by
      rw [ContinuousMap.comp_apply, cellMap_apply]; rfl))
  -- `F` starts at `f`.
  have hF₀ (x : X) (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
      F (0, ⟨x, hx⟩) = f ⟨x, (skeletonLT C _).subset_complex hx⟩ := by
    obtain hx' | ⟨j, y, hy, rfl⟩ := mem_skeletonLT_or_exists_map hx
    · exact hFG 0 x hx'
    · rw [hFH j 0 ⟨y, mem_closedBall_zero_iff.2 hy.le⟩,
        ContinuousMap.HomotopyWith.coe_toContinuousMap, (H j).apply_zero,
        ContinuousMap.comp_apply, cellMap_apply]
  -- Extend `F` over `C` by the homotopy extension property of `skeletonLT C (n + 1)`.
  have hHEP := hasHomotopyExtensionProperty_skeletonLT (C := C) (n + 1)
  obtain ⟨G, hG₀, hGF⟩ := hHEP.exists_extension_of_isClosed hHEP.isClosed f
    (F.comp ⟨fun p ↦ (p.1, ⟨p.2.1, p.2.2⟩), by fun_prop⟩) fun a ↦ hF₀ a.1.1 a.2
  refine ⟨⟨fun x ↦ G (1, x), by fun_prop⟩, ⟨⟨⟨G, hG₀, fun _ ↦ rfl⟩, fun t x hx ↦ ?_⟩⟩,
    fun j y ↦ ?_⟩
  · exact (hGF t ⟨x, skeletonLT_mono (by exact_mod_cast n.le_succ) hx⟩).trans (hFG t x.1 hx)
  · rw [cellMap_apply]
    exact (hGF 1 ⟨_, map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2)⟩).trans
      ((hFH j 1 y).trans ((H j).apply_one y))

end Step

section Induction

variable (S : ℕ → Set Y)
  (step : ∀ (n : ℕ) (g : C(C, Y)), MapsTo g {x : C | (x : X) ∈ skeletonLT C n} (S n) →
    ∃ g' : C(C, Y), g.HomotopicRel g' {x : C | (x : X) ∈ skeletonLT C n} ∧
      MapsTo g' {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)} (S (n + 1)))
  (f : C(C, Y)) (hf : MapsTo f {x : C | (x : X) ∈ D} (S 0))

/-- The successive improvements of `f`: the `m`-th one sends `skeletonLT C m` into `S m`, and is
obtained from the previous one by `step`. -/
private def approx : (m : ℕ) →
    {g : C(C, Y) // MapsTo g {x : C | (x : X) ∈ skeletonLT C m} (S m)}
  | 0 => ⟨f, by simpa only [Nat.cast_zero, ← SetLike.mem_coe, skeletonLT_zero_eq_base] using hf⟩
  | m + 1 => ⟨(step m _ (approx m).2).choose, (step m _ (approx m).2).choose_spec.2⟩

/-- The homotopy from the `m`-th to the `(m + 1)`-st improvement of `f`, stationary on
`skeletonLT C m`. -/
private def approxHomotopy (m : ℕ) :
    (approx S step f hf m).1.HomotopyRel (approx S step f hf (m + 1)).1
      {x : C | (x : X) ∈ skeletonLT C m} :=
  (step m _ (approx S step f hf m).2).choose_spec.1.some

/-- The time `1 - 2⁻ᵐ` at which the homotopy from the `m`-th to the `(m + 1)`-st improvement
starts. -/
private def stageTime (m : ℕ) : ℝ := 1 - 2⁻¹ ^ m

private lemma stageTime_lt_succ (m : ℕ) : stageTime m < stageTime (m + 1) := by
  simp only [stageTime, pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2⁻¹) m]

private lemma stageTime_nonneg (m : ℕ) : 0 ≤ stageTime m := by
  simp only [stageTime, sub_nonneg]
  exact pow_le_one₀ (by norm_num) (by norm_num)

private lemma stageTime_le_one (m : ℕ) : stageTime m ≤ 1 := by
  simp only [stageTime, sub_le_self_iff]
  positivity

/-- The time reparametrisation running the `m`-th homotopy during
`[stageTime m, stageTime (m + 1)]`. -/
private def stageParam (m : ℕ) : C(I, I) :=
  ⟨fun t ↦ projIcc 0 1 zero_le_one (2 ^ (m + 1) * ((t : ℝ) - stageTime m)),
    continuous_projIcc.comp (by fun_prop)⟩

private lemma stageParam_of_le {m : ℕ} {t : I} (ht : (t : ℝ) ≤ stageTime m) :
    stageParam m t = 0 :=
  projIcc_of_le_left zero_le_one (mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 ht))

private lemma stageParam_of_ge {m : ℕ} {t : I} (ht : stageTime (m + 1) ≤ t) :
    stageParam m t = 1 := by
  refine projIcc_of_right_le zero_le_one ?_
  have h : (2 : ℝ) ^ (m + 1) * (stageTime (m + 1) - stageTime m) = 1 := by
    rw [show stageTime (m + 1) - stageTime m = 2⁻¹ ^ (m + 1) by
      simp only [stageTime, pow_succ]; ring, ← mul_pow]
    norm_num
  rw [← h]
  gcongr

/-- The concatenation of the first `m` homotopies between successive improvements of `f`, the
`k`-th one run during `[stageTime k, stageTime (k + 1)]`, followed by the constant homotopy at
the `m`-th improvement. -/
private def approxConcat : (m : ℕ) → {Φ : C(I × C, Y) //
    ∀ (t : I) x, stageTime m ≤ t → Φ (t, x) = (approx S step f hf m).1 x}
  | 0 => ⟨(approx S step f hf 0).1.comp .snd, fun _ _ _ ↦ rfl⟩
  | m + 1 => ⟨⟨fun p ↦ if (p.1 : ℝ) ≤ stageTime m then (approxConcat m).1 p
      else approxHomotopy S step f hf m (stageParam m p.1, p.2),
      (approxConcat m).1.continuous.if_le (by fun_prop) (by fun_prop) continuous_const
        fun p hp ↦ by
          rw [(approxConcat m).2 _ _ hp.ge, stageParam_of_le hp.le,
            (approxHomotopy S step f hf m).apply_zero]⟩,
    fun t x ht ↦ by
      have ht' : ¬ (t : ℝ) ≤ stageTime m := (stageTime_lt_succ m).trans_le ht |>.not_ge
      simp only [ContinuousMap.coe_mk, ht', ↓reduceIte, stageParam_of_ge ht,
        ContinuousMap.HomotopyWith.apply_one]⟩

private lemma approxConcat_zero (m : ℕ) (x : C) :
    (approxConcat S step f hf m).1 (0, x) = f x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [approxConcat, ContinuousMap.coe_mk, Icc.coe_zero, stageTime_nonneg, ↓reduceIte, ih]

private lemma approxConcat_succ_of_mem {m : ℕ} (t : I) {x : C}
    (hx : (x : X) ∈ (skeletonLT C m : Set X)) :
    (approxConcat S step f hf (m + 1)).1 (t, x) = (approxConcat S step f hf m).1 (t, x) := by
  simp only [approxConcat, ContinuousMap.coe_mk]
  split_ifs with ht
  · rfl
  · rw [(approxHomotopy S step f hf m).eq_fst _ hx, (approxConcat S step f hf m).2 _ _
      (not_le.1 ht).le]

include step hf in
/-- **Homotoping a map skeleton by skeleton.** Let `S n` be sets of `Y` such that every map
`C → Y` sending `skeletonLT C n` into `S n` is homotopic, relative to `skeletonLT C n`, to a map
that also sends `skeletonLT C (n + 1)` into `S (n + 1)`. Then every map `f : C → Y` sending the
base `D` into `S 0` is homotopic, relative to `D`, to a map sending `skeletonLT C n` into `S n`
for every `n`. -/
theorem exists_homotopicRel_forall_mapsTo_skeletonLT :
    ∃ g : C(C, Y), (∀ n : ℕ, MapsTo g {x : C | (x : X) ∈ skeletonLT C n} (S n)) ∧
      f.HomotopicRel g {x : C | (x : X) ∈ D} := by
  -- Glue the concatenations of the first `m` homotopies over the skeleta.
  obtain ⟨G, hG⟩ := exists_continuousMap_prod_complex_of_skeletonLT (C := C) (Z := I) (k := 0)
    (fun m ↦ (approxConcat S step f hf m).1.comp
      ⟨fun p : I × (skeletonLT C ((0 + m : ℕ) : ℕ∞) : Set X) ↦
        (p.1, ⟨p.2, (skeletonLT C _).subset_complex p.2.2⟩), by fun_prop⟩)
    fun m t x hx ↦ approxConcat_succ_of_mem S step f hf t (by simpa using hx)
  have hG' (m : ℕ) (t : I) (x : C) (hx : (x : X) ∈ (skeletonLT C m : Set X)) :
      G (t, x) = (approxConcat S step f hf m).1 (t, x) :=
    hG m t x (by simpa using hx)
  refine ⟨⟨fun x ↦ G (1, x), by fun_prop⟩, fun n x hx ↦ ?_,
    ⟨⟨⟨G, fun x ↦ ?_, fun _ ↦ rfl⟩, fun t x hx ↦ ?_⟩⟩⟩
  · -- On `skeletonLT C n` the final map is the `n`-th improvement.
    have h := hG' n 1 x hx
    rw [(approxConcat S step f hf n).2 1 x (stageTime_le_one n)] at h
    exact h ▸ (approx S step f hf n).2 hx
  · obtain ⟨m, hm⟩ := exists_mem_skeletonLT_add 0 x.2
    exact (hG' m 0 x (by simpa using hm)).trans (approxConcat_zero S step f hf m x)
  · -- On the base `D = skeletonLT C 0` the homotopy is stationary.
    exact hG' 0 t x (by rw [Nat.cast_zero, skeletonLT_zero_eq_base]; exact hx)

end Induction

end TauCeti
