/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Foelner
public import TauCeti.GroupTheory.Amenable.LevelSet
public import TauCeti.Topology.Algebra.InfiniteSum.Constructions

/-!
# Følner sets from almost invariant finitely supported functions

Let a group `G` act on a type `X`, and translate functions by `(g • p) x = p (g⁻¹ • x)`. If a
nonnegative finitely supported function `p : X → ℝ` is almost invariant under a finite set
`K ⊆ G` in `ℓ¹`, in the sense that

```text
∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x,
```

then some finite nonempty set `F ⊆ X` satisfies

```text
∑_{g ∈ K} |g • F ∆ F| < ε · |F|.
```

Such a set is found among the superlevel sets `{x | t < p x}`, `t ≥ 0`.

This passes from Reiter's condition (almost invariant finitely supported probabilities) to Følner's
condition (almost invariant finite sets). The finite layer-cake identities
`TauCeti.exists_finsupp_layerCake` express the mass of `p` and each translation distance as
weighted sums of level-set cardinalities and boundaries. A strict inequality between the
weighted sums holds at some level, giving the desired set without measure-theoretic arguments.

## Main results

* `TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt`: a finite nonempty set whose
  total boundary `∑_{g ∈ K} |g • F ∆ F|` is less than `ε |F|`.
* `TauCeti.exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt`: the same set satisfies
  `|g • F ∆ F| < ε |F|` for each `g ∈ K`.
* `TauCeti.exists_finsupp_sum_tsum_lt_of_tsum_eq_one` and
  `TauCeti.exists_finset_sum_card_smul_symmDiff_lt_of_tsum_eq_one`: truncating a summable
  probability density with small `ℓ¹` translation variation on `K` produces a finitely supported
  almost invariant density, hence a finite nonempty set `F` with `∑_{g ∈ K} |g • F ∆ F| < ε |F|`.
* `TauCeti.tsum_abs_tsum_fiber_smul_sub_le` and
  `TauCeti.exists_finset_card_smul_symmDiff_lt_of_equivariant`: fiberwise summation along any
  `G`-equivariant map `π : X → Y` contracts `ℓ¹` translation variation and pushes Reiter functions
  forward to Følner sets on `Y`.
* `TauCeti.hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt`: a group satisfying Reiter's
  condition, for its left regular action, has Følner sets.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1 and the proof of
  Proposition G.5.2.
* A. Garrido, *An introduction to amenable groups*, Theorem 3.6.
-/

public section

open Filter Finset Function
open scoped Pointwise symmDiff Topology

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- **Reiter implies Følner, summed form.** If a nonnegative finitely supported function `p` on
`X` satisfies `∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`, then some finite nonempty set
`F ⊆ X` has total boundary `∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
theorem exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt {p : X → ℝ} (hp : 0 ≤ p)
    (hfin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  classical
  obtain ⟨w, hw, -, hmass, hboundary⟩ := exists_finsupp_layerCake (G := G) hp hfin
  let F (t : ℝ) := hfin.toFinset.filter (fun x => t < p x)
  -- Both sides use the same nonnegative widths, so one level satisfies the strict inequality.
  have h' : (∑ t ∈ w.support, w t * ∑ g ∈ K, (#((g • F t) ∆ F t) : ℝ)) <
      ∑ t ∈ w.support, w t * (ε * #(F t)) := by
    simp only [hboundary, hmass, Finsupp.sum] at h
    rw [sum_comm] at h
    simpa only [F, ← mul_sum, mul_sum, mul_left_comm] using h
  obtain ⟨t, -, ht⟩ := exists_lt_of_sum_lt h'
  have hlt : ∑ g ∈ K, (#((g • F t) ∆ F t) : ℝ) < ε * #(F t) :=
    lt_of_mul_lt_mul_left ht (hw t)
  refine ⟨F t, ?_, hlt⟩
  by_contra hn
  simp [not_nonempty_iff_eq_empty.1 hn] at hlt

/-- **Reiter implies Følner.** If a nonnegative finitely supported function `p` on `X` satisfies
`∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`, then some finite nonempty set `F ⊆ X` satisfies
`|g • F ∆ F| < ε |F|` for every `g ∈ K`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt {p : X → ℝ} (hp : 0 ≤ p)
    (hfin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  obtain ⟨F, hF, hlt⟩ := exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt hp hfin h
  exact ⟨F, hF, fun g hg ↦ (single_le_sum (f := fun g ↦ (#((g • F) ∆ F) : ℝ))
    (fun _ _ ↦ Nat.cast_nonneg _) hg).trans_lt hlt⟩

omit [DecidableEq X] in
/-- **Summable Reiter density truncation.** Truncating a nonnegative summable probability density
`q : X → ℝ` with small `ℓ¹` translation error on `K` to a large finite set produces a finitely
supported nonnegative density `p` supported inside `{x | q x ≠ 0}` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x`. -/
theorem exists_finsupp_sum_tsum_lt_of_tsum_eq_one {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq_sum : Summable q) (hq1 : ∑' x, q x = 1) (K : Finset G) {ε : ℝ} (hε : 0 < ε)
    (hvar : ∀ g ∈ K, ∑' x, |q (g⁻¹ • x) - q x| ≤ ε / (4 * (#K + 1))) :
    ∃ p : X → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ (∀ x, p x ≠ 0 → q x ≠ 0) ∧
      ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x := by
  classical
  -- Truncate `q` to a finite set `T` capturing at least `1 - δ` of its mass.
  set η : ℝ := ε / (8 * (#K + 1))
  have hη : 0 < η := by positivity
  set δ : ℝ := min (1 / 4) η
  have hδ : 0 < δ := lt_min (by norm_num) hη
  have hev : ∀ᶠ T : Finset X in atTop, 1 - δ < ∑ x ∈ T, q x := by
    have htend : Tendsto (fun T : Finset X ↦ ∑ x ∈ T, q x) atTop (𝓝 1) :=
      hq1 ▸ hq_sum.hasSum
    exact htend.eventually (lt_mem_nhds (by linarith))
  obtain ⟨T, hT⟩ := hev.exists
  let p : X → ℝ := (T : Set X).indicator q
  let r : X → ℝ := fun x ↦ q x - p x
  have hp0 (x : X) : 0 ≤ p x := Set.indicator_apply_nonneg fun _ ↦ hq0 x
  have hp_le (x : X) : p x ≤ q x := by
    by_cases hx : x ∈ (T : Set X) <;> simp [p, hx, hq0 x]
  have hr0 (x : X) : 0 ≤ r x := sub_nonneg.mpr (hp_le x)
  have hr_le (x : X) : r x ≤ q x := sub_le_self _ (hp0 x)
  have hp_sum : Summable p := .of_nonneg_of_le hp0 hp_le hq_sum
  have hr_sum : Summable r := .of_nonneg_of_le hr0 hr_le hq_sum
  have hp_fin : p.HasFiniteSupport := T.finite_toSet.subset Set.support_indicator_subset
  have hp_tsum : ∑' x, p x = ∑ x ∈ T, q x := by
    rw [tsum_eq_sum (s := T) fun x hx ↦ Set.indicator_of_notMem hx q]
    exact sum_congr rfl fun x hx ↦ Set.indicator_of_mem hx q
  have hr_tsum : ∑' x, r x < δ := by
    have hsub : ∑' x, r x = ∑' x, q x - ∑' x, p x := hq_sum.tsum_sub hp_sum
    linarith [hT]
  have hp_half : 1 / 2 < ∑' x, p x := by
    have hδ4 : δ ≤ 1 / 4 := min_le_left _ _
    linarith [hT, hp_tsum]
  refine ⟨p, hp0, hp_fin, fun x hx hqx ↦ hx (by simp [p, hqx]), ?_⟩
  -- Control the `ℓ¹` variation of `p` by that of `q` plus twice the tail mass `∑' x, r x < δ`.
  have hg_bound (g : G) (hg : g ∈ K) :
      ∑' x, |p (g⁻¹ • x) - p x| ≤ ε / (4 * (#K + 1)) + 2 * δ := by
    have hq_diff_sum : Summable (fun x ↦ |q (g⁻¹ • x) - q x|) := by
      have h1 : Summable (fun x ↦ q (g⁻¹ • x)) := (MulAction.toPerm g⁻¹).summable_iff.mpr hq_sum
      exact (h1.sub hq_sum).abs
    have hr_perm_sum : Summable (fun x ↦ r (g⁻¹ • x)) :=
      (MulAction.toPerm g⁻¹).summable_iff.mpr hr_sum
    have hr_perm_tsum : ∑' x, r (g⁻¹ • x) = ∑' x, r x :=
      (MulAction.toPerm g⁻¹).tsum_eq r
    have hp_diff_le (x : X) :
        |p (g⁻¹ • x) - p x| ≤ |q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x := by
      have heq : p (g⁻¹ • x) - p x = (q (g⁻¹ • x) - q x) - r (g⁻¹ • x) + r x := by
        simp only [r]
        ring
      rw [heq]
      calc |(q (g⁻¹ • x) - q x) - r (g⁻¹ • x) + r x|
          ≤ |(q (g⁻¹ • x) - q x) - r (g⁻¹ • x)| + |r x| := abs_add_le _ _
        _ ≤ |q (g⁻¹ • x) - q x| + |r (g⁻¹ • x)| + |r x| := by
            gcongr
            exact abs_sub _ _
        _ = |q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x := by
            rw [abs_of_nonneg (hr0 _), abs_of_nonneg (hr0 _)]
    have hmaj : Summable (fun x ↦ |q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x) :=
      (hq_diff_sum.add hr_perm_sum).add hr_sum
    have hp_diff_sum : Summable (fun x ↦ |p (g⁻¹ • x) - p x|) :=
      .of_nonneg_of_le (fun _ ↦ abs_nonneg _) hp_diff_le hmaj
    calc ∑' x, |p (g⁻¹ • x) - p x|
        ≤ ∑' x, (|q (g⁻¹ • x) - q x| + r (g⁻¹ • x) + r x) :=
          hp_diff_sum.tsum_le_tsum hp_diff_le hmaj
      _ = (∑' x, |q (g⁻¹ • x) - q x| + ∑' x, r (g⁻¹ • x)) + ∑' x, r x := by
          rw [(hq_diff_sum.add hr_perm_sum).tsum_add hr_sum, hq_diff_sum.tsum_add hr_perm_sum]
      _ ≤ ε / (4 * (#K + 1)) + 2 * δ := by
          linarith [hvar g hg, hr_perm_tsum, hr_tsum]
  have hδη : δ ≤ η := min_le_right _ _
  have : (0 : ℝ) < #K + 1 := by positivity
  have hstep : ε / (4 * (#K + 1)) + 2 * δ ≤ ε / (2 * (#K + 1)) := by
    have heq : ε / (4 * (#K + 1)) + 2 * η = ε / (2 * (#K + 1)) := by
      simp only [η]
      field_simp
      ring
    linarith
  calc ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x|
      ≤ ∑ _g ∈ K, (ε / (2 * (#K + 1))) :=
        sum_le_sum fun g hg ↦ (hg_bound g hg).trans hstep
    _ = #K * (ε / (2 * (#K + 1))) := by simp
    _ ≤ (#K + 1) * (ε / (2 * (#K + 1))) := by
        gcongr
        linarith
    _ = ε / 2 := by
        field_simp
    _ < ε * ∑' x, p x := by
        nlinarith

/-- **Summable Reiter density implies Følner, summed form.** If a nonnegative summable probability
density `q : X → ℝ` satisfies `∑_x |q (g⁻¹ • x) - q x| ≤ ε / (4 * (#K + 1))` for all `g ∈ K`, then
some finite nonempty set `F ⊆ X` has total boundary `∑_{g ∈ K} |g • F ∆ F| < ε |F|`. -/
theorem exists_finset_sum_card_smul_symmDiff_lt_of_tsum_eq_one {q : X → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq_sum : Summable q) (hq1 : ∑' x, q x = 1) (K : Finset G) {ε : ℝ} (hε : 0 < ε)
    (hvar : ∀ g ∈ K, ∑' x, |q (g⁻¹ • x) - q x| ≤ ε / (4 * (#K + 1))) :
    ∃ F : Finset X, F.Nonempty ∧ ∑ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  obtain ⟨p, hp0, hp_fin, -, hp_lt⟩ :=
    exists_finsupp_sum_tsum_lt_of_tsum_eq_one hq0 hq_sum hq1 K hε hvar
  exact exists_finset_sum_card_smul_symmDiff_lt_of_sum_tsum_lt hp0 hp_fin hp_lt

omit [DecidableEq X] in
/-- **Equivariant fiberwise `ℓ¹` variation contraction.** For any `G`-equivariant map `π : X → Y`
and summable function `p : X → ℝ`, fiberwise summation `y ↦ ∑' x : π ⁻¹' {y}, p x` contracts the
`ℓ¹` translation variation under every `g : G`. -/
theorem tsum_abs_tsum_fiber_smul_sub_le {Y : Type*} [MulAction G Y] {π : X → Y}
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) {p : X → ℝ} (hp : Summable p) (g : G) :
    (∑' y : Y, |(∑' x : π ⁻¹' {g⁻¹ • y}, p x) - ∑' x : π ⁻¹' {y}, p x|) ≤
      ∑' x : X, |p (g⁻¹ • x) - p x| := by
  have hp_inv : Summable (fun x ↦ p (g⁻¹ • x)) := (MulAction.toPerm g⁻¹).summable_iff.mpr hp
  have hdiff : Summable (fun x ↦ |p (g⁻¹ • x) - p x|) := (hp_inv.sub hp).abs
  have hfib_hasSum : HasSum (fun y : Y ↦ ∑' x : π ⁻¹' {y}, |p (g⁻¹ • x) - p x|)
      (∑' x : X, |p (g⁻¹ • x) - p x|) :=
    hdiff.hasSum.tsum_fiberwise π
  have hbound (y : Y) :
      |(∑' x : π ⁻¹' {g⁻¹ • y}, p x) - ∑' x : π ⁻¹' {y}, p x| ≤
        ∑' x : π ⁻¹' {y}, |p (g⁻¹ • x) - p x| := by
    let e : π ⁻¹' {y} ≃ π ⁻¹' {g⁻¹ • y} :=
      { toFun x := ⟨g⁻¹ • x.val, by
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ]
          exact congrArg (g⁻¹ • ·) x.property⟩
        invFun z := ⟨g • z.val, by
          have hz : π z.val = g⁻¹ • y := z.property
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hπ, hz, smul_inv_smul]⟩
        left_inv x := Subtype.ext (smul_inv_smul g x.val)
        right_inv z := Subtype.ext (inv_smul_smul g z.val) }
    have hshift : (∑' z : π ⁻¹' {g⁻¹ • y}, p z) = ∑' x : π ⁻¹' {y}, p (g⁻¹ • x) :=
      (e.tsum_eq fun z ↦ p z).symm
    have hd : Summable (fun x : π ⁻¹' {y} ↦ p (g⁻¹ • x) - p x) :=
      (hp_inv.subtype _).sub (hp.subtype _)
    have hsub : (∑' x : π ⁻¹' {y}, p (g⁻¹ • x)) - ∑' x : π ⁻¹' {y}, p x =
        ∑' x : π ⁻¹' {y}, (p (g⁻¹ • x) - p x) :=
      ((hp_inv.subtype _).tsum_sub (hp.subtype _)).symm
    rw [hshift, hsub, abs_le]
    refine ⟨?_, hd.tsum_le_tsum (fun _ ↦ le_abs_self _) (hdiff.subtype _)⟩
    rw [← tsum_neg]
    exact (hdiff.subtype _).neg.tsum_le_tsum (fun _ ↦ neg_abs_le _) hd
  have hlhs_sum :
      Summable (fun y : Y ↦ |(∑' x : π ⁻¹' {g⁻¹ • y}, p x) - ∑' x : π ⁻¹' {y}, p x|) :=
    .of_nonneg_of_le (fun _ ↦ abs_nonneg _) hbound hfib_hasSum.summable
  exact (hlhs_sum.tsum_le_tsum hbound hfib_hasSum.summable).trans_eq hfib_hasSum.tsum_eq

omit [DecidableEq X] in
/-- **Equivariant Reiter pushforward.** Pushing a nonnegative finitely supported Reiter function
`p : X → ℝ` with `∑_{g ∈ K} ∑_x |p (g⁻¹ • x) - p x| < ε · ∑_x p x` forward by fiberwise summation
along a `G`-equivariant map `π : X → Y` yields a finite nonempty set `F ⊆ Y` with
`|g • F ∆ F| < ε |F|` for all `g ∈ K`. -/
theorem exists_finset_card_smul_symmDiff_lt_of_equivariant {Y : Type*} [MulAction G Y]
    [DecidableEq Y] {π : X → Y} (hπ : ∀ (g : G) x, π (g • x) = g • π x) {p : X → ℝ} (hp0 : 0 ≤ p)
    (hp_fin : p.HasFiniteSupport) {K : Finset G} {ε : ℝ}
    (h : ∑ g ∈ K, ∑' x, |p (g⁻¹ • x) - p x| < ε * ∑' x, p x) :
    ∃ F : Finset Y, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  have hp_sum : Summable p := summable_of_hasFiniteSupport hp_fin
  let q : Y → ℝ := fun y ↦ ∑' x : π ⁻¹' {y}, p x
  have hq0 : 0 ≤ q := fun _ ↦ tsum_nonneg fun x ↦ hp0 x.val
  have hq_fin : q.HasFiniteSupport := hp_fin.tsum_fiber π
  have hq_mass : ∑' y, q y = ∑' x, p x := (hp_sum.hasSum.tsum_fiberwise π).tsum_eq
  have hsum_q : ∑ g ∈ K, ∑' y, |q (g⁻¹ • y) - q y| < ε * ∑' y, q y := by
    rw [hq_mass]
    exact (sum_le_sum fun g _ ↦ tsum_abs_tsum_fiber_smul_sub_le hπ hp_sum g).trans_lt h
  exact exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt hq0 hq_fin hsum_q

/-- A group satisfying **Reiter's condition** has Følner sets: if for every finite `K` and
`ε > 0` there is a finitely supported probability density `p` with
`∑_{g ∈ K} ∑_x |p (g⁻¹ x) - p x| < ε`, then `G` has Følner sets. -/
theorem hasFoelnerSets_of_forall_exists_sum_tsum_abs_sub_lt
    (h : ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ p : G → ℝ, 0 ≤ p ∧ p.HasFiniteSupport ∧ ∑' x, p x = 1 ∧
        ∑ g ∈ K, ∑' x, |p (g⁻¹ * x) - p x| < ε) :
    HasFoelnerSets G := by
  classical
  refine hasFoelnerSets_iff.2 fun K ε hε ↦ ?_
  obtain ⟨p, hp0, hpfin, hp1, hp⟩ := h K ε hε
  exact exists_finset_card_smul_symmDiff_lt_of_sum_tsum_lt hp0 hpfin (by simpa [hp1] using hp)

end TauCeti
