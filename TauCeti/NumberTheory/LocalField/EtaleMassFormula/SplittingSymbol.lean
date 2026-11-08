/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import TauCeti.Data.Multiset.Filter
public import TauCeti.RepresentationTheory.Symmetric.ClassSize

/-!
# Splitting symbols and their automorphism weights

An étale algebra of degree `n` over a nonarchimedean local field is a product of field extensions
`L_i`, and its *splitting symbol* records the pair `(f_i, e_i)` of residue degree and ramification
index of each factor: a multiset `σ` of pairs of positive integers with `∑ f_i e_i = n`
[Bhargava 2007, (2.1)]. This file develops the purely combinatorial side of Bhargava's mass
formulas for these symbols.

* `TauCeti.splittingSymbolAut σ` is `#Aut(σ)`, the product of the residue degrees `f_i` times the
  number of permutations of the factors preserving `σ`.
* `TauCeti.ramificationPartition σ` repeats each `e_i - 1` exactly `f_i` times and drops zeros. The
  symbol has degree `n = k + #π + n₀`, where `k` is the sum of its ramification partition `π` and
  `n₀` the total residue degree of its unramified factors
  (`TauCeti.sum_map_mul_eq_sum_ramificationPartition_add`).

The main result is `TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition`: for a partition
`π` of `k` into at most `n - k` parts, the splitting symbols of degree `n` with ramification
partition `π` satisfy `∑ 1 / #Aut(σ) = 1`. This is the combinatorial core of
[Bhargava 2007, Prop. 2.2], the mass formula for a fixed ramification partition, which says the
étale algebras with ramification partition `π` have mass `q ^ (-k)`.

The proof is the general identity `TauCeti.tsum_one_div_splittingSymbolAut_eq_one`. Fix a finite
set `S` of ramification indices and, for each `e ∈ S`, a total residue degree `m e`. Grouping the
factors of a symbol by their ramification index identifies the symbols with these totals with the
families of partitions of the `m e`, that is, with the conjugacy classes of
`∏_{e ∈ S} Sym(m e)`. Under this identification `#Aut(σ)` is the order of the centralizer,
`∏_e z_{μ_e}`, so the sum factors into the normalisations `∑_μ 1 / z_μ = 1`
(`TauCeti.sum_inv_zPart`). For a ramification partition `π` the indices are `1, …, k + 1`, the
index `t + 1` carrying the parts of `π` equal to `t` and the index `1` the remaining degree
`n - k - #π`.

The sums are taken in `ℝ≥0∞`, the convention of the mass formulas, although only finitely many
symbols occur.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN 2007, rnm052, §2.
-/

public section

open scoped Nat ENNReal NNReal

namespace TauCeti

/-! ### The automorphism count and the ramification partition -/

/-- The order `#Aut(σ)` of the automorphism group of a splitting symbol `σ`, a multiset of pairs
`(f, e)` of residue degrees and ramification indices [Bhargava 2007, §2]: the product of the
residue degrees, times the number `∏ₓ (count x)!` of permutations of the factors that preserve
`σ`. -/
def splittingSymbolAut (σ : Multiset (ℕ × ℕ)) : ℕ :=
  (σ.map Prod.fst).prod * ∏ x ∈ σ.toFinset, (σ.count x)!

/-- The ramification partition of a splitting symbol `σ` [Bhargava 2007, §2]: each `e - 1`
repeated `f` times, over the factors `(f, e)` of `σ`, with the zeros dropped. For a symbol of degree
`n` whose ramification partition has sum `k`, it is a partition of `k` into at most `n - k`
parts. -/
def ramificationPartition (σ : Multiset (ℕ × ℕ)) : Multiset ℕ :=
  (σ.bind fun x => Multiset.replicate x.1 (x.2 - 1)).filter (· ≠ 0)

/-- The defining formula of `splittingSymbolAut`. -/
theorem splittingSymbolAut_def (σ : Multiset (ℕ × ℕ)) :
    splittingSymbolAut σ = (σ.map Prod.fst).prod * ∏ x ∈ σ.toFinset, (σ.count x)! :=
  (rfl)

/-- The defining formula of `ramificationPartition`. -/
theorem ramificationPartition_def (σ : Multiset (ℕ × ℕ)) :
    ramificationPartition σ =
      (σ.bind fun x => Multiset.replicate x.1 (x.2 - 1)).filter (· ≠ 0) :=
  (rfl)

/-- `#Aut(σ)` as a product over any finite set of pairs containing the factors of `σ`: the factor
`(f, e)` contributes `f ^ m * m !`, where `m` is its multiplicity in `σ`. -/
theorem splittingSymbolAut_eq_prod_of_subset (σ : Multiset (ℕ × ℕ)) {s : Finset (ℕ × ℕ)}
    (hs : σ.toFinset ⊆ s) :
    splittingSymbolAut σ = ∏ x ∈ s, x.1 ^ σ.count x * (σ.count x)! := by
  rw [splittingSymbolAut, Finset.prod_multiset_map_count, ← Finset.prod_mul_distrib]
  refine Finset.prod_subset hs fun x _ hx => ?_
  rw [Multiset.count_eq_zero_of_notMem (by simpa using hx)]
  simp

/-- `#Aut(σ)` is positive when every residue degree is. -/
theorem splittingSymbolAut_pos {σ : Multiset (ℕ × ℕ)} (hσ : ∀ x ∈ σ, 0 < x.1) :
    0 < splittingSymbolAut σ :=
  Nat.mul_pos (Multiset.prod_pos fun a ha => by
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 ha
      exact hσ x hx)
    (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

/-- The parts of the ramification partition are the `e - 1 ≠ 0` for the factors `(f, e)` of `σ`
with `f ≠ 0`. -/
@[simp]
theorem mem_ramificationPartition {σ : Multiset (ℕ × ℕ)} {t : ℕ} :
    t ∈ ramificationPartition σ ↔ t ≠ 0 ∧ ∃ x ∈ σ, x.1 ≠ 0 ∧ x.2 - 1 = t := by
  simp only [ramificationPartition, Multiset.mem_filter, Multiset.mem_bind,
    Multiset.mem_replicate]
  constructor
  · rintro ⟨⟨x, hx, h1, rfl⟩, ht⟩
    exact ⟨ht, x, hx, h1, rfl⟩
  · rintro ⟨ht, x, hx, h1, rfl⟩
    exact ⟨⟨x, hx, h1, rfl⟩, ht⟩

/-- The multiplicity of a positive part `t` in the ramification partition is the total residue
degree of the factors with ramification index `t + 1`. -/
theorem count_ramificationPartition (σ : Multiset (ℕ × ℕ)) {t : ℕ} (ht : t ≠ 0) :
    (ramificationPartition σ).count t =
      (σ.map fun x => if x.2 = t + 1 then x.1 else 0).sum := by
  rw [ramificationPartition, Multiset.count_filter_of_pos (p := (· ≠ 0)) ht, Multiset.count_bind]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  rw [Multiset.count_replicate]
  split_ifs <;> omega

/-- The sum of the ramification partition is `∑ f (e - 1)` over the factors `(f, e)` of `σ`. -/
@[simp]
theorem sum_ramificationPartition (σ : Multiset (ℕ × ℕ)) :
    (ramificationPartition σ).sum = (σ.map fun x => x.1 * (x.2 - 1)).sum := by
  rw [ramificationPartition, Multiset.filter_bind, Multiset.sum_bind]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  by_cases h : x.2 - 1 = 0
  · rw [Multiset.filter_eq_nil.2 fun a ha => by simp [Multiset.eq_of_mem_replicate ha, h], h]
    simp
  · rw [Multiset.filter_eq_self.2 fun a ha => by simpa [Multiset.eq_of_mem_replicate ha] using h]
    simp

/-- The number of parts of the ramification partition is the total residue degree of the ramified
factors, those with `2 ≤ e`. -/
@[simp]
theorem card_ramificationPartition (σ : Multiset (ℕ × ℕ)) :
    Multiset.card (ramificationPartition σ) =
      (σ.map fun x => if 2 ≤ x.2 then x.1 else 0).sum := by
  rw [ramificationPartition, Multiset.filter_bind, Multiset.card_bind]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  by_cases h : 2 ≤ x.2
  · rw [Function.comp_apply, Multiset.filter_eq_self.2 fun a ha => by
      rw [Multiset.eq_of_mem_replicate ha]; omega, Multiset.card_replicate]
    simp only [h, ↓reduceIte]
  · rw [Function.comp_apply, Multiset.filter_eq_nil.2 fun a ha => by
      rw [Multiset.eq_of_mem_replicate ha]; omega, Multiset.card_zero]
    simp only [h, ↓reduceIte]

/-- **The degree of a splitting symbol** with positive ramification indices is `k + #π + n₀`, where
`π` is its ramification partition, `k` the sum of `π`, and `n₀` the total residue degree of the
unramified factors. -/
theorem sum_map_mul_eq_sum_ramificationPartition_add (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.2) :
    (σ.map fun x => x.1 * x.2).sum =
      (ramificationPartition σ).sum + Multiset.card (ramificationPartition σ) +
        (σ.map fun x => if x.2 = 1 then x.1 else 0).sum := by
  rw [sum_ramificationPartition, card_ramificationPartition, ← Multiset.sum_map_add,
    ← Multiset.sum_map_add]
  refine congrArg _ (Multiset.map_congr rfl fun x hx => ?_)
  obtain ⟨e, he⟩ : ∃ e, x.2 = e + 1 := ⟨x.2 - 1, by have := hσ x hx; omega⟩
  rw [he]
  rcases e with _ | e
  · simp
  · simp only [Nat.add_sub_cancel, show 2 ≤ e + 1 + 1 by omega, show e + 1 + 1 ≠ 1 by omega,
      ↓reduceIte]
    ring

/-! ### Grouping the factors by ramification index -/

section Grouping

variable {S : Finset ℕ}

/-- The splitting symbols whose ramification indices lie in `S`, with total residue degree `m e`
at each `e ∈ S`, are the families of partitions of the `m e`: group the factors by their
ramification index. -/
private def symbolEquiv (S : Finset ℕ) (m : ℕ → ℕ) :
    {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ x.2 ∈ S) ∧
        ∀ e ∈ S, (σ.map fun x => if x.2 = e then x.1 else 0).sum = m e} ≃
      ((e : S) → (m e).Partition) where
  toFun σ e :=
    { parts := (σ.1.filter (·.2 = (e : ℕ))).map Prod.fst
      parts_pos := fun {a} ha => by
        obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 ha
        exact (σ.2.1 x (Multiset.mem_of_mem_filter hx)).1
      parts_sum := by rw [Multiset.sum_map_filter]; exact σ.2.2 e e.2 }
  invFun μ := ⟨∑ e : S, (μ e).parts.map fun a => (a, (e : ℕ)), by
    refine ⟨fun x hx => ?_, fun e he => ?_⟩
    · obtain ⟨e, _, hx⟩ := Multiset.mem_sum.1 hx
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
      exact ⟨(μ e).parts_pos ha, e.2⟩
    · rw [← Multiset.sum_map_filter,
        Multiset.map_fst_filter_sum_map_prodMk (fun e => (μ e).parts) Subtype.val_injective ⟨e, he⟩]
      exact (μ ⟨e, he⟩).parts_sum⟩
  left_inv σ := Subtype.ext <| Multiset.ext.2 fun ⟨f, e⟩ => by
    by_cases he : e ∈ S
    · exact (Multiset.count_sum_map_prodMk_of_injective _ Subtype.val_injective f ⟨e, he⟩).trans
        (Multiset.count_map_fst_filter_snd_eq σ.1 f e)
    · rw [Multiset.count_sum_map_prodMk_of_notMem_range _ f (by simpa using he),
        Multiset.count_eq_zero_of_notMem fun hx => he (σ.2.1 _ hx).2]
  right_inv μ := funext fun e => Nat.Partition.ext
    (Multiset.map_fst_filter_sum_map_prodMk (fun e => (μ e).parts) Subtype.val_injective e)

private theorem coe_symbolEquiv_symm (S : Finset ℕ) (m : ℕ → ℕ) (μ : (e : S) → (m e).Partition) :
    ((symbolEquiv S m).symm μ : Multiset (ℕ × ℕ)) =
      ∑ e : S, (μ e).parts.map fun a => (a, (e : ℕ)) :=
  rfl

/-- Grouped by ramification index, `#Aut(σ)` is the product of the centralizer orders `z_μ` of the
partitions of the groups. -/
private theorem splittingSymbolAut_sum_map_prodMk {m : ℕ → ℕ} (μ : (e : S) → (m e).Partition) :
    splittingSymbolAut (∑ e : S, (μ e).parts.map fun a => (a, (e : ℕ))) =
      ∏ e : S, zPart (μ e) := by
  classical
  set A : Finset ℕ := Finset.univ.biUnion fun e => (μ e).parts.toFinset
  have hA : ∀ e, (μ e).parts.toFinset ⊆ A := fun e =>
    Finset.subset_biUnion_of_mem (fun e => (μ e).parts.toFinset) (Finset.mem_univ e)
  rw [splittingSymbolAut_eq_prod_of_subset _ (s := A ×ˢ S), Finset.prod_product_right,
    ← Finset.prod_coe_sort S]
  · refine Finset.prod_congr rfl fun e _ => ?_
    rw [zPart_eq_prod_of_subset (μ e) (hA e)]
    refine Finset.prod_congr rfl fun f _ => ?_
    rw [Multiset.count_sum_map_prodMk_of_injective (fun e => (μ e).parts) Subtype.val_injective f
      e]
  · intro x hx
    obtain ⟨e, _, hx⟩ := Multiset.mem_sum.1 (Multiset.mem_toFinset.1 hx)
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
    exact Finset.mem_product.2 ⟨hA e (Multiset.mem_toFinset.2 ha), e.2⟩

end Grouping

/-! ### The automorphism weights -/

/-- **The automorphism weights of the splitting symbols with prescribed residue degrees add up to
one.** Fix a finite set `S` of ramification indices and a total residue degree `m e` for each
`e ∈ S`. The splitting symbols whose factors `(f, e)` have `0 < f` and `e ∈ S`, and whose factors
with ramification index `e` have residue degrees adding up to `m e`, satisfy
`∑ 1 / #Aut(σ) = 1`: they correspond to the conjugacy classes of `∏_{e ∈ S} Sym(m e)`, with
`#Aut(σ)` the order of the centralizer. -/
theorem tsum_one_div_splittingSymbolAut_eq_one (S : Finset ℕ) (m : ℕ → ℕ) :
    ∑' σ : {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ x.2 ∈ S) ∧
        ∀ e ∈ S, (σ.map fun x => if x.2 = e then x.1 else 0).sum = m e},
      1 / (splittingSymbolAut σ : ℝ≥0∞) = 1 := by
  rw [← (symbolEquiv S m).symm.tsum_eq, tsum_fintype]
  have key : ∀ μ : (e : S) → (m e).Partition,
      1 / (splittingSymbolAut ((symbolEquiv S m).symm μ : Multiset (ℕ × ℕ)) : ℝ≥0∞) =
        ((∏ e : S, ((zPart (μ e) : ℝ≥0))⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    intro μ
    have hne : (∏ e : S, (zPart (μ e) : ℝ≥0)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun e _ => by exact_mod_cast (zPart_pos (μ e)).ne'
    rw [coe_symbolEquiv_symm, splittingSymbolAut_sum_map_prodMk, Finset.prod_inv_distrib,
      ENNReal.coe_inv hne, one_div, Nat.cast_prod, ENNReal.ofNNReal_finsetProd]
    simp
  have hprod : ∏ e : S, ∑ μ : (m e).Partition, ((zPart μ : ℝ≥0))⁻¹ = 1 := by
    simp [sum_inv_zPart]
  rw [Fintype.prod_sum] at hprod
  simp_rw [key]
  rw [← ENNReal.ofNNReal_finsetSum, hprod, ENNReal.coe_one]

section RamificationPartition

variable {n k : ℕ} {π : k.Partition}

/-- The total residue degree at ramification index `e` of a splitting symbol of degree `n` with
ramification partition `π`: the multiplicity of `e - 1` in `π` for `e ≠ 1`, and the remaining
degree `n - k - #π` for `e = 1`. -/
private def residueDegreeTotal (n : ℕ) (π : k.Partition) (e : ℕ) : ℕ :=
  if e = 1 then n - k - Multiset.card π.parts else π.parts.count (e - 1)

/-- A splitting symbol of degree `n` with ramification partition `π` has ramification indices in
`[1, k + 1]` and the residue degree totals `residueDegreeTotal n π`. -/
private theorem forall_sum_eq_residueDegreeTotal {σ : Multiset (ℕ × ℕ)}
    (hpos : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hdeg : (σ.map fun x => x.1 * x.2).sum = n)
    (hram : ramificationPartition σ = π.parts) :
    (∀ x ∈ σ, 0 < x.1 ∧ x.2 ∈ Finset.Icc 1 (k + 1)) ∧
      ∀ e ∈ Finset.Icc 1 (k + 1),
        (σ.map fun x => if x.2 = e then x.1 else 0).sum = residueDegreeTotal n π e := by
  have hdeg' := sum_map_mul_eq_sum_ramificationPartition_add σ fun x hx => (hpos x hx).2
  rw [hram, π.parts_sum, hdeg] at hdeg'
  refine ⟨fun x hx => ⟨(hpos x hx).1, Finset.mem_Icc.2 ⟨(hpos x hx).2, ?_⟩⟩, fun e he => ?_⟩
  · -- a ramification index `e ≥ 2` contributes the part `e - 1 ≤ k` to `π`
    by_contra hlt
    have hmem : x.2 - 1 ∈ π.parts := hram ▸
      mem_ramificationPartition.2 ⟨by omega, x, hx, (hpos x hx).1.ne', rfl⟩
    have := Nat.Partition.le_of_mem_parts hmem
    omega
  · obtain ⟨he1, -⟩ := Finset.mem_Icc.1 he
    by_cases he' : e = 1
    · subst he'
      simp only [residueDegreeTotal, ↓reduceIte]
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, e = t + 1 := ⟨e - 1, by omega⟩
      simp only [residueDegreeTotal, he', ↓reduceIte, Nat.add_sub_cancel]
      rw [← hram, count_ramificationPartition σ (by omega)]

/-- Conversely, a symbol with positive residue degrees, ramification indices in `[1, k + 1]` and
the residue degree totals `residueDegreeTotal n π` has ramification partition `π` and, when `π`
has at most `n - k` parts, degree `n`. -/
private theorem ramificationPartition_eq_and_sum_eq {σ : Multiset (ℕ × ℕ)}
    (hπ : Multiset.card π.parts ≤ n - k) (hpos : ∀ x ∈ σ, 0 < x.1 ∧ x.2 ∈ Finset.Icc 1 (k + 1))
    (hsum : ∀ e ∈ Finset.Icc 1 (k + 1),
      (σ.map fun x => if x.2 = e then x.1 else 0).sum = residueDegreeTotal n π e) :
    (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts := by
  have hk := π.parts_sum
  have hkn : k ≤ n := by
    by_contra h
    rw [Multiset.card_eq_zero.1 (show Multiset.card π.parts = 0 by omega), Multiset.sum_zero] at hk
    omega
  have hram : ramificationPartition σ = π.parts := by
    refine Multiset.ext.2 fun t => ?_
    rcases eq_or_ne t 0 with rfl | ht
    · rw [Multiset.count_eq_zero_of_notMem fun h => (mem_ramificationPartition.1 h).1 rfl,
        Multiset.count_eq_zero_of_notMem fun h => (π.parts_pos h).ne' rfl]
    rw [count_ramificationPartition σ ht]
    by_cases htk : t ≤ k
    · rw [hsum (t + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)]
      simp only [residueDegreeTotal, show t + 1 ≠ 1 by omega, ↓reduceIte, Nat.add_sub_cancel]
    · -- both sides vanish: the ramification indices are at most `k + 1`, the parts at most `k`
      rw [Multiset.count_eq_zero_of_notMem fun h => htk (Nat.Partition.le_of_mem_parts h)]
      refine Multiset.sum_eq_zero fun a ha => ?_
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 ha
      have := (Finset.mem_Icc.1 (hpos x hx).2).2
      simp only [show x.2 ≠ t + 1 by omega, ↓reduceIte]
  refine ⟨?_, hram⟩
  rw [sum_map_mul_eq_sum_ramificationPartition_add σ fun x hx => (Finset.mem_Icc.1 (hpos x hx).2).1,
    hram, hk, hsum 1 (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)]
  simp only [residueDegreeTotal, ↓reduceIte]
  omega

/-- **The splitting symbols with a given ramification partition have total automorphism weight
one** ([Bhargava 2007, proof of Prop. 2.2]). For a partition `π` of `k` into at most `n - k`
parts, the splitting symbols `σ` of degree `n` (pairs `(f, e)` of positive integers with
`∑ f e = n`) whose ramification partition is `π` satisfy `∑ 1 / #Aut(σ) = 1`. -/
theorem tsum_one_div_splittingSymbolAut_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : Multiset.card π.parts ≤ n - k) :
    ∑' σ : {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
        (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts},
      1 / (splittingSymbolAut σ : ℝ≥0∞) = 1 := by
  have key : ∀ σ : Multiset (ℕ × ℕ), ((∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
      (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts) ↔
      ((∀ x ∈ σ, 0 < x.1 ∧ x.2 ∈ Finset.Icc 1 (k + 1)) ∧
        ∀ e ∈ Finset.Icc 1 (k + 1),
          (σ.map fun x => if x.2 = e then x.1 else 0).sum = residueDegreeTotal n π e) :=
    fun σ => ⟨fun ⟨hpos, hdeg, hram⟩ => forall_sum_eq_residueDegreeTotal hpos hdeg hram,
      fun ⟨hpos, hsum⟩ => ⟨fun x hx => ⟨(hpos x hx).1, (Finset.mem_Icc.1 (hpos x hx).2).1⟩,
        ramificationPartition_eq_and_sum_eq hπ hpos hsum⟩⟩
  have h := (Equiv.subtypeEquivRight key).tsum_eq fun σ => 1 / (splittingSymbolAut σ.1 : ℝ≥0∞)
  rw [tsum_one_div_splittingSymbolAut_eq_one] at h
  exact h

end RamificationPartition

end TauCeti
