/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.PValuation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Uniform

/-!
# The canonical valuation of a uniform pro-`p` group

Give the layer `λ_n \ λ_{n+1}` of the lower `p`-series weight `n + 1` at odd primes
and `n + 2` at `2`. The finite superlevel subgroups recover the lower `p`-series,
so this construction needs no choice of ordered generators. The valuation is
saturated. Its root maps on the power subgroups are the continuous inverses of the
power maps between consecutive terms.

## References

* P. Schneider, *p-Adic Lie Groups*, §26.
* P. Schneider and J. Teitelbaum, *Algebras of p-adic distributions and admissible
  representations*, §4, the remark following condition (HYP).
-/

public section

open Filter
open scoped ENNReal Topology commutatorElement

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The smallest allowed integer weight of a `p`-valuation, namely `1` at odd
primes and `2` at `p = 2`. -/
def uniformValuationOffset (p : ℕ) : ℕ :=
  if p = 2 then 2 else 1

@[simp]
theorem uniformValuationOffset_two : uniformValuationOffset 2 = 2 :=
  (rfl)

@[simp]
theorem uniformValuationOffset_of_ne_two (hp : p ≠ 2) : uniformValuationOffset p = 1 := by
  simp [uniformValuationOffset, hp]

/-- The weight attached to the lower `p`-series before checking the valuation axioms. -/
private noncomputable def uniformWeight (p : ℕ) (x : G) : ℝ≥0∞ := by
  classical
  exact ⨆ n : ℕ, if x ∈ pLowerCentralSeries p G n then ↑(n + uniformValuationOffset p) else 0

private theorem cast_add_offset_le_uniformWeight {n : ℕ} {x : G}
    (hx : x ∈ pLowerCentralSeries p G n) :
    ((n + uniformValuationOffset p : ℕ) : ℝ≥0∞) ≤ uniformWeight p x := by
  classical
  simpa [uniformWeight, hx] using
    (le_iSup (fun i : ℕ ↦ if x ∈ pLowerCentralSeries p G i
      then (↑(i + uniformValuationOffset p) : ℝ≥0∞) else 0) n)

private theorem uniformWeight_one (p : ℕ) : uniformWeight p (1 : G) = ⊤ := by
  classical
  refine iSup_eq_top.mpr fun r hr ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hr.ne
  refine ⟨n, hn.trans_le ?_⟩
  simpa only [ite_eq_left (one_mem (pLowerCentralSeries p G n))] using
    (Nat.cast_le.mpr (Nat.le_add_right n (uniformValuationOffset p)) :
      (n : ℝ≥0∞) ≤ ↑(n + uniformValuationOffset p))

private theorem uniformWeight_eq_of_mem_of_notMem {n : ℕ} {x : G}
    (hx : x ∈ pLowerCentralSeries p G n) (hx' : x ∉ pLowerCentralSeries p G (n + 1)) :
    uniformWeight p x = ↑(n + uniformValuationOffset p) := by
  classical
  refine le_antisymm (iSup_le fun i ↦ ?_) (cast_add_offset_le_uniformWeight hx)
  split_ifs with hi
  · have hi' : i ≤ n := by
      by_contra! h
      exact hx' (pLowerCentralSeries_antitone h hi)
    exact Nat.cast_le.mpr (Nat.add_le_add_right hi' _)
  · exact zero_le

variable [hp : Fact p.Prime] [CompactSpace G] [TotallyDisconnectedSpace G]

private theorem exists_uniformWeight_layer (hG : IsUniform p G) {x : G} (hx : x ≠ 1) :
    ∃ n, x ∈ pLowerCentralSeries p G n ∧ x ∉ pLowerCentralSeries p G (n + 1) := by
  classical
  have h : ∃ n, x ∉ pLowerCentralSeries p G (n + 1) := by
    by_contra! hall
    apply hx
    apply Subgroup.mem_bot.mp
    rw [← hG.isProP.iInf_pLowerCentralSeries_eq_bot hp.out, Subgroup.mem_iInf]
    exact fun n ↦ pLowerCentralSeries_succ_le n (hall n)
  refine ⟨Nat.find h, ?_, Nat.find_spec h⟩
  rcases Nat.eq_zero_or_pos (Nat.find h) with hzero | hpos
  · rw [hzero]
    exact mem_pLowerCentralSeries_zero p x
  · have hmin := Nat.find_min h (m := Nat.find h - 1) (by omega)
    rwa [Nat.sub_add_cancel hpos, not_not] at hmin

private theorem uniformWeight_eq_top_iff (hG : IsUniform p G) (x : G) :
    uniformWeight p x = ⊤ ↔ x = 1 := by
  by_cases hx : x = 1
  · simp [hx, uniformWeight_one]
  obtain ⟨n, hn, hn'⟩ := exists_uniformWeight_layer hG hx
  simp [hx, uniformWeight_eq_of_mem_of_notMem hn hn']

private theorem cast_add_offset_le_uniformWeight_iff (hG : IsUniform p G) (n : ℕ) (x : G) :
    ((n + uniformValuationOffset p : ℕ) : ℝ≥0∞) ≤ uniformWeight p x ↔
      x ∈ pLowerCentralSeries p G n := by
  refine ⟨fun h ↦ ?_, cast_add_offset_le_uniformWeight⟩
  by_cases hx : x = 1
  · simp [hx]
  obtain ⟨m, hm, hm'⟩ := exists_uniformWeight_layer hG hx
  rw [uniformWeight_eq_of_mem_of_notMem hm hm', Nat.cast_le] at h
  exact pLowerCentralSeries_antitone (Nat.le_of_add_le_add_right h) hm

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem inv_lt_uniformWeight (x : G) :
    (↑(p - 1 : ℕ) : ℝ≥0∞)⁻¹ < uniformWeight p x := by
  refine lt_of_lt_of_le ?_ (cast_add_offset_le_uniformWeight (mem_pLowerCentralSeries_zero p x))
  simp only [zero_add, uniformValuationOffset]
  split_ifs with h
  · subst p
    norm_num
  · rw [Nat.cast_one, ENNReal.inv_lt_one, ← Nat.cast_one (R := ℝ≥0∞)]
    exact Nat.cast_lt.mpr (by have := hp.out.two_le; omega)

private theorem min_le_uniformWeight_mul_inv (hG : IsUniform p G) (x y : G) :
    min (uniformWeight p x) (uniformWeight p y) ≤ uniformWeight p (x * y⁻¹) := by
  by_cases hx : x = 1
  · subst x
    by_cases hy : y = 1
    · simp [hy]
    obtain ⟨j, hj, hj'⟩ := exists_uniformWeight_layer hG hy
    simpa only [uniformWeight_one, min_top_left, one_mul, uniformWeight_eq_of_mem_of_notMem hj hj']
      using cast_add_offset_le_uniformWeight (inv_mem hj)
  by_cases hy : y = 1
  · simp [hy, uniformWeight_one]
  obtain ⟨i, hi, hi'⟩ := exists_uniformWeight_layer hG hx
  obtain ⟨j, hj, hj'⟩ := exists_uniformWeight_layer hG hy
  have hm : Monotone (fun n : ℕ ↦ (n : ℝ≥0∞)) := fun _ _ h ↦ Nat.cast_le.mpr h
  rw [uniformWeight_eq_of_mem_of_notMem hi hi', uniformWeight_eq_of_mem_of_notMem hj hj',
    ← hm.map_min, min_add_add_right]
  exact cast_add_offset_le_uniformWeight
    (mul_mem (pLowerCentralSeries_antitone (min_le_left _ _) hi)
      (inv_mem (pLowerCentralSeries_antitone (min_le_right _ _) hj)))

private theorem uniformWeight_pow (hG : IsUniform p G) (x : G) :
    uniformWeight p (x ^ p) = uniformWeight p x + 1 := by
  by_cases hx : x = 1
  · simp [hx, uniformWeight_one]
  obtain ⟨n, hn, hn'⟩ := exists_uniformWeight_layer hG hx
  rw [uniformWeight_eq_of_mem_of_notMem (pow_mem_pLowerCentralSeries hn)
    (mt hG.pow_mem_pLowerCentralSeries_succ_iff.mp hn'),
    uniformWeight_eq_of_mem_of_notMem hn hn', Nat.add_right_comm n 1, Nat.cast_add, Nat.cast_one]

private theorem add_le_uniformWeight_commutator (hG : IsUniform p G) (x y : G) :
    uniformWeight p x + uniformWeight p y ≤ uniformWeight p ⁅x, y⁆ := by
  by_cases hx : x = 1
  · simp [hx, uniformWeight_one]
  by_cases hy : y = 1
  · simp [hy, uniformWeight_one]
  obtain ⟨i, hi, hi'⟩ := exists_uniformWeight_layer hG hx
  obtain ⟨j, hj, hj'⟩ := exists_uniformWeight_layer hG hy
  have hmem : ⁅x, y⁆ ∈ pLowerCentralSeries p G (i + j + uniformValuationOffset p) := by
    unfold uniformValuationOffset
    split_ifs with hp'
    · subst p
      exact hG.isPowerful.commutator_mem_pLowerCentralSeries_of_two
        hG.isProP hG.isTopologicallyFinitelyGenerated hi hj
    · exact commutator_mem_pLowerCentralSeries hi hj
  calc
    uniformWeight p x + uniformWeight p y =
        (↑(i + j + uniformValuationOffset p + uniformValuationOffset p) : ℝ≥0∞) := by
      rw [uniformWeight_eq_of_mem_of_notMem hi hi', uniformWeight_eq_of_mem_of_notMem hj hj',
        ← Nat.cast_add]
      congr 1
      omega
    _ ≤ uniformWeight p ⁅x, y⁆ := cast_add_offset_le_uniformWeight hmem

private theorem hasBasis_uniformWeight (hG : IsUniform p G) :
    (𝓝 (1 : G)).HasBasis (fun r : ℝ≥0∞ ↦ r ≠ ⊤) fun r ↦ {x | r ≤ uniformWeight p x} := by
  refine (hG.isProP.hasAntitoneBasis_nhds_one_pLowerCentralSeries
    hG.isTopologicallyFinitelyGenerated hp.out).toHasBasis.to_hasBasis ?_ ?_
  · intro n _
    refine ⟨↑(n + uniformValuationOffset p), ENNReal.natCast_ne_top _, fun x hx ↦ ?_⟩
    exact (cast_add_offset_le_uniformWeight_iff hG n x).mp hx
  · intro r hr
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hr
    refine ⟨n, trivial, fun x hx ↦ hn.le.trans ?_⟩
    exact (Nat.cast_le.mpr (Nat.le_add_right n _)).trans (cast_add_offset_le_uniformWeight hx)

/-- The canonical `p`-valuation on a uniform group. An element in the `n`-th layer
of the lower `p`-series has weight `n + uniformValuationOffset p`. -/
noncomputable def IsUniform.pValuation (hG : IsUniform p G) : PValuation p G where
  toFun := uniformWeight p
  eq_top_iff' := uniformWeight_eq_top_iff hG
  inv_lt' := inv_lt_uniformWeight
  min_le_mul_inv' := min_le_uniformWeight_mul_inv hG
  add_le_commutator' := add_le_uniformWeight_commutator hG
  map_pow' := uniformWeight_pow hG
  hasBasis_nhds_one' := hasBasis_uniformWeight hG
  completeSpace := by
    let _ := IsTopologicalGroup.rightUniformSpace G
    exact completeSpace_of_isComplete_univ isCompact_univ.isComplete

/-- The superlevel subgroups at the canonical thresholds are the terms of the lower
`p`-series. -/
@[simp]
theorem IsUniform.filtration_pValuation (hG : IsUniform p G) (n : ℕ) :
    hG.pValuation.filtration (↑n + ↑(uniformValuationOffset p)) = pLowerCentralSeries p G n := by
  ext x
  rw [PValuation.mem_filtration, ← Nat.cast_add]
  exact cast_add_offset_le_uniformWeight_iff hG n x

/-- The exact weight of an element in a layer of the lower `p`-series. -/
theorem IsUniform.pValuation_apply_eq (hG : IsUniform p G) {n : ℕ} {x : G}
    (hx : x ∈ pLowerCentralSeries p G n) (hx' : x ∉ pLowerCentralSeries p G (n + 1)) :
    hG.pValuation x = ↑(n + uniformValuationOffset p) :=
  uniformWeight_eq_of_mem_of_notMem hx hx'

/-- The canonical valuation of a uniform group is saturated at every prime. -/
theorem IsUniform.isSaturated_pValuation (hG : IsUniform p G) :
    hG.pValuation.IsSaturated := by
  rw [PValuation.isSaturated_iff]
  intro x hx
  have hp' : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hthreshold : (uniformValuationOffset p : ℝ≥0∞) ≤
      (p : ℝ≥0∞) / (↑(p - 1 : ℕ) : ℝ≥0∞) := by
    unfold uniformValuationOffset
    split_ifs with h
    · subst p
      norm_num
    · rw [Nat.cast_one, ENNReal.le_div_iff_mul_le (.inl (by exact_mod_cast hp'))
        (.inl (ENNReal.natCast_ne_top _)), one_mul]
      exact Nat.cast_le.mpr (Nat.sub_le _ _)
  have hmem : x ∈ pLowerCentralSeries p G 1 := by
    by_contra hx'
    rw [hG.pValuation_apply_eq (mem_pLowerCentralSeries_zero p x) hx', zero_add] at hx
    exact (not_lt_of_ge hthreshold) hx
  let a : pLowerCentralSeries p G 1 := ⟨x, hmem⟩
  exact ⟨(hG.powHomeomorph 0).symm a, hG.coe_powHomeomorph_symm_apply_pow 0 a⟩

/-- The sum of any two canonical weights exceeds the saturation threshold.
In particular, the weights of basis lifts satisfy Schneider–Teitelbaum's condition (HYP). -/
theorem IsUniform.div_lt_pValuation_add (hG : IsUniform p G) (x y : G) :
    (p : ℝ≥0∞) / (↑(p - 1 : ℕ) : ℝ≥0∞) < hG.pValuation x + hG.pValuation y := by
  have hweight (z : G) : (uniformValuationOffset p : ℝ≥0∞) ≤ hG.pValuation z := by
    have hz : z ∈ hG.pValuation.filtration (↑(0 : ℕ) + ↑(uniformValuationOffset p)) := by
      rw [hG.filtration_pValuation]
      exact mem_pLowerCentralSeries_zero p z
    simpa only [PValuation.mem_filtration, Nat.cast_zero, zero_add] using hz
  refine lt_of_lt_of_le ?_ (add_le_add (hweight x) (hweight y))
  by_cases h : p = 2
  · subst p
    norm_num
  · have hp2 := hp.out.two_le
    have hden : p - 1 ≠ 0 := by omega
    rw [ENNReal.div_lt_iff (.inl (by exact_mod_cast hden)) (.inl (ENNReal.natCast_ne_top _)),
      uniformValuationOffset_of_ne_two h, ← Nat.cast_add, ← Nat.cast_mul, Nat.cast_lt]
    omega

end TauCeti
