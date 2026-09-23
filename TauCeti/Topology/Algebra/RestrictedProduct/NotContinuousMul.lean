/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.RestrictedProduct.Sum
public import TauCeti.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Topology.Instances.Rat

/-!
# Restricted products with non-open reference subgroups

Mathlib makes a restricted product of topological groups a topological group only when every
reference subgroup is open (`RestrictedProduct.isTopologicalGroup`, under
`Fact (∀ i, IsOpen (A i))`). This file shows that the hypothesis cannot be dropped: the restricted
product `Πʳ n : ℕ, [Multiplicative ℚ, ⊥]` of copies of `ℚ`, with the topology of `ℚ ⊆ ℝ` and the
trivial reference subgroup in every factor, does not have continuous multiplication. Additively it
is the space of finitely supported rational sequences with the final topology over the
finite-dimensional stages, and a final topology need not be compatible with products. That a strict
inductive limit of topological groups need not be a topological group in the inductive-limit
topology is classical; see Tatsuuma, Shimomura and Hirai.

The witness is the set `W = {x | ∀ n ≥ 1, |x n| < |x 0 - √2 / (n + 1)|}`, written additively. It is
open, because on each stage only finitely many coordinates are free and the right-hand sides never
vanish at a rational `x 0`, and it contains `0`. But every neighbourhood of `0` contains `t • e₀`
for all rational `t` of small absolute value and `s • eₙ` for all rational `s` of small absolute
value, and for `n` large and `t` rational close to `√2 / (n + 1)` the sum `t • e₀ + s • eₙ`
escapes `W`.

Multiplication on this space factors through the inverse of the splitting `restrictedProductSum` of
the restricted product over `ℕ ⊕ ℕ` into two restricted products, followed by the coordinatewise
product of the two halves, which is continuous for every family. So that inverse is not continuous
for this family either (`not_continuous_restrictedProductSum_symm`), although
`continuous_restrictedProductSum_symm` makes it continuous once the reference subgroups are open;
openness is a fact about the topology, not a limitation of that proof.

The openness of the witness is checked stage by stage with `isOpen_restrictedProduct_iff`, and the
neighbourhood argument uses `continuous_restrictedProduct_mulSingle`.

## References

* N. Bourbaki, *General Topology*.
* N. Tatsuuma, H. Shimomura, T. Hirai, *On group topologies and unitary representations of
  inductive limits of topological groups and the case of the group of diffeomorphisms*,
  J. Math. Kyoto Univ. 38 (1998), 551–578.
* A. Weil, *Basic Number Theory*.
-/
public section

namespace TauCeti

open Filter Multiplicative
open scoped RestrictedProduct

section Witness

/-- The `n`-th coordinate of an element of a restricted product of copies of `Multiplicative ℚ`,
read as a real number. -/
private def realCoord {𝓕 : Filter ℕ} (n : ℕ)
    (x : Πʳ _ : ℕ, [Multiplicative ℚ, ((⊥ : Subgroup (Multiplicative ℚ)) :
      Set (Multiplicative ℚ))]_[𝓕]) : ℝ :=
  ((toAdd (x n) : ℚ) : ℝ)

private theorem continuous_realCoord {𝓕 : Filter ℕ} (n : ℕ) :
    Continuous (realCoord (𝓕 := 𝓕) n) :=
  Rat.continuous_coe_real.comp (continuous_toAdd.comp (RestrictedProduct.continuous_eval n))

private theorem realCoord_inclusion {𝓕 𝓖 : Filter ℕ} (h : 𝓕 ≤ 𝓖) (n : ℕ)
    (x : Πʳ _ : ℕ, [Multiplicative ℚ, ((⊥ : Subgroup (Multiplicative ℚ)) :
      Set (Multiplicative ℚ))]_[𝓖]) :
    realCoord n (RestrictedProduct.inclusion _ _ h x) = realCoord n x := by
  simp [realCoord]

private theorem realCoord_one {𝓕 : Filter ℕ} (n : ℕ) :
    realCoord (𝓕 := 𝓕) n 1 = 0 := by
  simp [realCoord]

private theorem realCoord_mul {𝓕 : Filter ℕ} (n : ℕ)
    (x y : Πʳ _ : ℕ, [Multiplicative ℚ, ((⊥ : Subgroup (Multiplicative ℚ)) :
      Set (Multiplicative ℚ))]_[𝓕]) :
    realCoord n (x * y) = realCoord n x + realCoord n y := by
  simp [realCoord]

private theorem realCoord_mulSingle_same (n : ℕ) (t : ℚ) :
    realCoord n (RestrictedProduct.mulSingle (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℚ)))
      n (ofAdd t)) = t := by
  simp [realCoord]

private theorem realCoord_mulSingle_of_ne {m n : ℕ} (h : m ≠ n) (t : ℚ) :
    realCoord m (RestrictedProduct.mulSingle (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℚ)))
      n (ofAdd t)) = 0 := by
  simp [realCoord, Pi.mulSingle_eq_of_ne h]

/-- The open neighbourhood of the identity in `Πʳ n : ℕ, [Multiplicative ℚ, ⊥]` that contains no
product of two neighbourhoods of the identity: additively, the sequences `x` with
`|x n| < |x 0 - √2 / (n + 1)|` for every `n ≥ 1`. -/
private def escapeSet :
    Set (Πʳ _ : ℕ, [Multiplicative ℚ, ((⊥ : Subgroup (Multiplicative ℚ)) :
      Set (Multiplicative ℚ))]) :=
  {x | ∀ n : ℕ, 1 ≤ n → |realCoord n x| < |realCoord 0 x - √2 / (n + 1)|}

private theorem mem_escapeSet_iff
    (x : Πʳ _ : ℕ, [Multiplicative ℚ, ((⊥ : Subgroup (Multiplicative ℚ)) :
      Set (Multiplicative ℚ))]) :
    x ∈ escapeSet ↔ ∀ n : ℕ, 1 ≤ n → |realCoord n x| < |realCoord 0 x - √2 / (n + 1)| := by
  rfl

private theorem one_mem_escapeSet : (1 : Πʳ _ : ℕ, [Multiplicative ℚ,
    ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))]) ∈ escapeSet := by
  rw [mem_escapeSet_iff]
  intro n _
  rw [realCoord_one, realCoord_one, abs_zero, zero_sub, abs_neg]
  positivity

/-- The set `escapeSet` is open in the restricted-product topology. -/
private theorem isOpen_escapeSet : IsOpen escapeSet := by
  rw [isOpen_restrictedProduct_iff]
  intro S hS
  have hfin : (Sᶜ : Set ℕ).Finite := mem_cofinite.mp (le_principal_iff.mp hS)
  have hopen : IsOpen (⋂ n ∈ Sᶜ, {y : Πʳ _ : ℕ, [Multiplicative ℚ,
      ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))]_[𝓟 S] |
        1 ≤ n → |realCoord n y| < |realCoord 0 y - √2 / (n + 1)|}) := by
    refine hfin.isOpen_biInter fun n _ ↦ ?_
    by_cases hn : 1 ≤ n
    · simp only [hn, true_implies]
      exact isOpen_lt (continuous_realCoord n).abs
        ((continuous_realCoord 0).sub continuous_const).abs
    · simp [hn]
  convert hopen using 1
  ext y
  simp only [Set.mem_preimage, mem_escapeSet_iff, realCoord_inclusion, Set.mem_iInter,
    Set.mem_ofPred_eq]
  refine ⟨fun h n _ hn ↦ h n hn, fun h n hn ↦ ?_⟩
  by_cases hnS : n ∈ S
  · have hy : y n = 1 := Subgroup.mem_bot.1 (eventually_principal.1 y.2 n hnS)
    have hirr : Irrational (√2 / ((n : ℝ) + 1)) := by
      exact_mod_cast irrational_sqrt_two.div_natCast (Nat.succ_ne_zero n)
    simp only [realCoord, hy, toAdd_one, Rat.cast_zero, abs_zero, abs_pos, sub_ne_zero]
    exact (hirr.ne_rat _).symm
  · exact h n hnS hn

/-- Every open neighbourhood of the identity contains the element `ofAdd t` inserted at the `n`-th
coordinate, for all rationals `t` of small enough absolute value. -/
private theorem exists_pos_mulSingle_mem {V : Set (Πʳ _ : ℕ, [Multiplicative ℚ,
      ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))])}
    (hV : IsOpen V) (h1 : 1 ∈ V) (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℚ, |(t : ℝ)| < δ →
      RestrictedProduct.mulSingle (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℚ))) n (ofAdd t)
        ∈ V := by
  have hpre : IsOpen ((fun t : ℚ ↦ RestrictedProduct.mulSingle
      (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℚ))) n (ofAdd t)) ⁻¹' V) :=
    hV.preimage ((continuous_restrictedProduct_mulSingle _ n).comp continuous_ofAdd)
  have h0 : (0 : ℚ) ∈ (fun t : ℚ ↦ RestrictedProduct.mulSingle
      (fun _ : ℕ ↦ (⊥ : Subgroup (Multiplicative ℚ))) n (ofAdd t)) ⁻¹' V := by
    simpa using h1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hpre 0 h0
  refine ⟨δ, hδ, fun t ht ↦ hball ?_⟩
  rw [Metric.mem_ball, Rat.dist_eq]
  simpa using ht

/-- Given `δ > 0` and positive `ε n`, some `n ≥ 1` admits rationals `t` and `s` with `|t| < δ`,
`|s| < ε n` and `|t - √2 / (n + 1)| ≤ |s|`. -/
private theorem exists_rat_escape {δ : ℝ} (hδ : 0 < δ) {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ t s : ℚ, |(t : ℝ)| < δ ∧ |(s : ℝ)| < ε n ∧
      |(t : ℝ) - √2 / (n + 1)| ≤ |(s : ℝ)| := by
  obtain ⟨n, hn⟩ := exists_nat_gt (√2 / δ)
  rw [div_lt_iff₀ hδ] at hn
  refine ⟨n + 1, by omega, ?_⟩
  set c : ℝ := √2 / ((n + 1 : ℕ) + 1) with hc
  have hc0 : 0 < c := by positivity
  have hcδ : c < δ := by
    rw [hc, div_lt_iff₀ (by positivity)]
    push_cast
    nlinarith
  obtain ⟨t, ht₁, ht₂⟩ := exists_rat_btwn (max_lt hc0 (by linarith [hε (n + 1)]) :
    max 0 (c - ε (n + 1)) < c)
  rw [max_lt_iff] at ht₁
  have htc : |(t : ℝ) - c| < ε (n + 1) := by
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  obtain ⟨s, hs₁, hs₂⟩ := exists_rat_btwn htc
  refine ⟨t, s, ?_, ?_, ?_⟩
  · rw [abs_lt]
    constructor <;> linarith
  · rw [abs_lt]
    constructor <;> linarith [abs_nonneg ((t : ℝ) - c)]
  · rw [abs_of_pos (lt_of_le_of_lt (abs_nonneg _) hs₁)]
    exact hs₁.le

end Witness

/-- Multiplication on the restricted product `Πʳ n : ℕ, [Multiplicative ℚ, ⊥]` is not continuous:
with the topology of `ℚ ⊆ ℝ` on each factor and the trivial, non-open, reference subgroup at every
index, the restricted-product topology is not compatible with the group structure. -/
theorem not_continuousMul_restrictedProduct_rat_bot :
    ¬ ContinuousMul (Πʳ _ : ℕ, [Multiplicative ℚ,
      ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))]) := by
  intro h
  have hW := continuous_mul.isOpen_preimage _ isOpen_escapeSet
  obtain ⟨V, V', hV, hV', h1V, h1V', hVV'⟩ :=
    isOpen_prod_iff.1 hW 1 1 (Set.mem_preimage.2 (by rw [mul_one]; exact one_mem_escapeSet))
  obtain ⟨δ, hδ, hδV⟩ := exists_pos_mulSingle_mem hV h1V 0
  choose ε hε hεV' using fun n ↦ exists_pos_mulSingle_mem hV' h1V' n
  obtain ⟨n, hn, t, s, ht, hs, hts⟩ := exists_rat_escape hδ hε
  have hmem := (mem_escapeSet_iff _).1 (hVV' (Set.mk_mem_prod (hδV t ht) (hεV' n s hs))) n hn
  rw [realCoord_mul, realCoord_mul, realCoord_mulSingle_same, realCoord_mulSingle_same,
    realCoord_mulSingle_of_ne (by omega), realCoord_mulSingle_of_ne (by omega), zero_add,
    add_zero] at hmem
  exact absurd hmem (not_lt.2 hts)

/-- The restricted product `Πʳ n : ℕ, [Multiplicative ℚ, ⊥]` is not a topological group: the
hypothesis `Fact (∀ i, IsOpen (A i))` of Mathlib's `RestrictedProduct.isTopologicalGroup` cannot be
dropped. -/
theorem not_isTopologicalGroup_restrictedProduct_rat_bot :
    ¬ IsTopologicalGroup (Πʳ _ : ℕ, [Multiplicative ℚ,
      ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))]) :=
  fun h ↦ not_continuousMul_restrictedProduct_rat_bot h.toContinuousMul

/-- Multiplying the two halves of the splitting of `Πʳ k : ℕ ⊕ ℕ, [Multiplicative ℚ, ⊥]` is
continuous, although multiplication on `Πʳ n : ℕ, [Multiplicative ℚ, ⊥]` itself is not. -/
private theorem continuous_mul_restrictedProductSum_rat_bot :
    Continuous fun z : Πʳ _ : ℕ ⊕ ℕ, [Multiplicative ℚ,
        ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))] ↦
      (restrictedProductSum (fun _ ↦ ⊥) z).1 * (restrictedProductSum (fun _ ↦ ⊥) z).2 := by
  rw [RestrictedProduct.continuous_dom]
  intro T hT
  -- The stage of `ℕ` on which both halves of the stage `T` are integral.
  have hT' : cofinite ≤ 𝓟 {n : ℕ | Sum.inl n ∈ T ∧ Sum.inr n ∈ T} := by
    rw [le_principal_iff]
    have h := eventually_mem_set.2 (le_principal_iff.1 hT)
    filter_upwards [Sum.inl_injective.tendsto_cofinite.eventually h,
      Sum.inr_injective.tendsto_cofinite.eventually h] with n hl hr using ⟨hl, hr⟩
  -- The coordinatewise product between the two stages, through which the composite factors.
  let g : (Πʳ _ : ℕ ⊕ ℕ, [Multiplicative ℚ,
      ((⊥ : Subgroup (Multiplicative ℚ)) : Set (Multiplicative ℚ))]_[𝓟 T]) →
        Πʳ _ : ℕ, [Multiplicative ℚ, ((⊥ : Subgroup (Multiplicative ℚ)) :
          Set (Multiplicative ℚ))]_[𝓟 {n : ℕ | Sum.inl n ∈ T ∧ Sum.inr n ∈ T}] :=
    fun z ↦ RestrictedProduct.mk (fun n ↦ z (Sum.inl n) * z (Sum.inr n)) (by
      rw [eventually_principal]
      intro n hn
      exact mul_mem (eventually_principal.1 z.2 _ hn.1) (eventually_principal.1 z.2 _ hn.2))
  have hg : Continuous g := by
    refine RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun n ↦ ?_)
    exact (RestrictedProduct.continuous_eval (Sum.inl n)).mul
      (RestrictedProduct.continuous_eval (Sum.inr n))
  refine ((RestrictedProduct.continuous_inclusion hT').comp hg).congr fun z ↦ ?_
  ext n : 1
  simp only [Function.comp_apply, RestrictedProduct.inclusion_apply, RestrictedProduct.mul_apply,
    restrictedProductSum_apply_inl, restrictedProductSum_apply_inr, RestrictedProduct.mk_apply, g]

/-- The inverse of the splitting `restrictedProductSum` of a restricted product over a sum of index
types is not continuous in general: for `Πʳ k : ℕ ⊕ ℕ, [Multiplicative ℚ, ⊥]`, with the trivial,
non-open, reference subgroup at every index, it is a discontinuous bijection. The openness
hypothesis of `continuous_restrictedProductSum_symm` therefore cannot be dropped. -/
theorem not_continuous_restrictedProductSum_symm :
    ¬ Continuous (restrictedProductSum (G := fun _ : ℕ ⊕ ℕ ↦ Multiplicative ℚ)
      fun _ ↦ (⊥ : Subgroup (Multiplicative ℚ))).symm := by
  intro h
  refine not_continuousMul_restrictedProduct_rat_bot
    ⟨(continuous_mul_restrictedProductSum_rat_bot.comp h).congr fun p ↦ ?_⟩
  simp

end TauCeti
