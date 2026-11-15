/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.TransitiveMass
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Sum

/-!
# Bhargava's mass formulas for étale algebras over a nonarchimedean local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`. This file proves
Bhargava's three mass formulas for degree-`n` étale `K`-algebras — formulated both on labelled
Galois sets (`TauCeti.etaleMass`) and directly over isomorphism classes of étale `K`-algebras:

1. **Fixed splitting symbol** (`TauCeti.etaleMass_splittingSymbol`, [Bhargava 2007, Prop. 2.1]):
   for any splitting symbol `σ` of degree `n` (pairs `(f_i, e_i)` of positive integers with
   `∑ f_i e_i = n`), the Galois sets of size `n` with splitting symbol `σ` have mass
   `1 / (#Aut(σ) · q ^ (∑ f_i (e_i - 1)))`.
2. **Fixed ramification partition** (`TauCeti.etaleMass_ramificationPartition`,
   [Bhargava 2007, Prop. 2.2]): for any partition `π` of `k` into at most `n - k` parts, the Galois
   sets of size `n` whose splitting symbol has ramification partition `π` have mass `q ^ (-k)`.
3. **Total étale mass** (`TauCeti.etaleMass_eq` and `TauCeti.tsum_etaleDiscriminantExponent_eq`,
   [Bhargava 2007, Thm. 1.1, Prop. 2.3, and §8]):
   `M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`,
   where `q(k, m)` is the number of partitions of `k` into at most `m` parts.

## Proof outline

* Proposition 2.1 is proved by induction on the number of factors of `σ`: when `n > 0`, peeling off
  the unique orbit containing `0 : Fin n` identifies Galois sets with splitting symbol `σ` with
  choices of a distinct factor `x = (f, e) ∈ σ`, an `(f * e)`-element subset of `Fin n` containing
  `0`, a transitive Galois set of symbol `{x}` on that subset, and a Galois set of symbol
  `σ.erase x` on the complement (`TauCeti.GaloisSet.sumCongrEquiv`). Applying
  `TauCeti.etaleMass_isTransitive_splittingSymbol`, the inductive hypothesis, and the identity
  `C(n - 1, m - 1) · m! · (n - m)! = m · (n - 1)!`, the sum over `x ∈ σ.toFinset` collapses via
  `∑ count(x) · f · e = n` and `#Aut(σ) = f · count(x) · #Aut(σ.erase x)`.
* Proposition 2.2 sums Proposition 2.1 over splitting symbols with ramification partition `π`, using
  `TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition` (`∑ 1 / #Aut(σ) = 1`).
* Theorem 1.1 sums Proposition 2.2 over all pairs `(k, π)` with `k ≤ n` and `#π ≤ n - k`, and
  combines with `TauCeti.tsum_etaleDiscriminantExponent` for families of étale `K`-algebras.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1, §2, and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal Nat

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Subset decomposition helpers -/

/-- Canonical bijection `Fin m ⊕ Fin (n - m) ≃ Fin n` sending `Fin m` order-isomorphically onto an
`m`-element subset `S ⊆ Fin n` and `Fin (n - m)` order-isomorphically onto `Sᶜ`. -/
private def subsetSumEquiv {m n : ℕ} (S : Finset (Fin n)) (hS : S.card = m) :
    Fin m ⊕ Fin (n - m) ≃ Fin n :=
  have hSc : (Sᶜ).card = n - m := by rw [Finset.card_compl, Fintype.card_fin, hS]
  ((S.orderIsoOfFin hS).toEquiv.sumCongr
    (((Sᶜ).orderIsoOfFin hSc).toEquiv.trans
      (Equiv.subtypeEquivRight fun _ ↦ Finset.mem_compl))).trans
    (Equiv.sumCompl (· ∈ S))

private theorem range_subsetSumEquiv_inl {m n : ℕ} (S : Finset (Fin n)) (hS : S.card = m) :
    Set.range (subsetSumEquiv S hS ∘ Sum.inl) = (S : Set (Fin n)) := by
  ext x
  simp only [Set.mem_range, Function.comp_apply, Finset.mem_coe]
  constructor
  · rintro ⟨j, rfl⟩
    exact (S.orderIsoOfFin hS j).2
  · intro hx
    refine ⟨(S.orderIsoOfFin hS).symm ⟨x, hx⟩, ?_⟩
    simp [subsetSumEquiv]

private theorem mul_inv_mul_cancel_left {a b : ℝ≥0∞} (ha0 : a ≠ 0) (hat : a ≠ ⊤) :
    a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, ENNReal.mul_inv_cancel ha0 hat, one_mul]

/-! ### Mass formula for a fixed splitting symbol -/

/-- **Mass formula for a fixed splitting type** ([Bhargava 2007, Prop. 2.1]): for a splitting symbol
`σ` of degree `n` whose pairs `(f, e)` have positive entries and satisfy `∑ f e = n`, the labelled
Galois sets of size `n` with splitting symbol `σ` have mass
`1 / (#Aut(σ) · q ^ splittingSymbolExponent σ)`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  suffices ∀ r n : ℕ, ∀ σ : Multiset (ℕ × ℕ), Multiset.card σ = r →
      (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) → (σ.map fun x => x.1 * x.2).sum = n →
      (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        1 / ((splittingSymbolAut σ : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) from
    this (Multiset.card σ) n σ rfl hσ hn
  intro r
  induction r with
  | zero =>
    intro n σ hr _ hn
    obtain rfl : σ = 0 := Multiset.card_eq_zero.1 hr
    simp only [Multiset.map_zero, Multiset.sum_zero] at hn
    subst hn
    have huniq : Unique {ρ : GaloisSet K 0 // ρ.splittingSymbol = 0} :=
      { default := ⟨GaloisSet.trivial K 0, by simp⟩
        uniq := fun ρ ↦ Subtype.ext (Subsingleton.elim _ _) }
    rw [tsum_eq_single huniq.default fun ρ hρ ↦ (hρ (huniq.uniq ρ)).elim]
    simp
  | succ r ih =>
    intro n σ hr hσ hn
    have hσ_ne : σ ≠ 0 := by
      rintro rfl
      simp at hr
    obtain ⟨x₁, hx₁⟩ := Multiset.exists_mem_of_ne_zero hσ_ne
    have hn_pos : 0 < n := by
      have hx₁_pos : 0 < x₁.1 * x₁.2 := Nat.mul_pos (hσ x₁ hx₁).1 (hσ x₁ hx₁).2
      have hle : x₁.1 * x₁.2 ≤ (σ.map fun x => x.1 * x.2).sum :=
        Multiset.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (Multiset.mem_map_of_mem _ hx₁)
      omega
    let i₀ : Fin n := ⟨0, hn_pos⟩
    set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
    -- Subsets of `Fin n` of size `m` containing the base point `i₀`.
    let T (m : ℕ) : Finset (Finset (Fin n)) :=
      ((Finset.univ : Finset (Fin n)).powersetCard m).filter ({i₀} ⊆ ·)
    let Fib (x : σ.toFinset) : Type u :=
      {ρ₁ : GaloisSet K (x.1.1 * x.1.2) // ρ₁.splittingSymbol = {x.1}} ×
        {ρ₂ : GaloisSet K (n - x.1.1 * x.1.2) // ρ₂.splittingSymbol = σ.erase x.1}
    let Ψ : (Σ (x : σ.toFinset) (_ : T (x.1.1 * x.1.2)), Fib x) →
        {ρ : GaloisSet K n // ρ.splittingSymbol = σ} :=
      fun ⟨x, S, p⟩ ↦
        have hScard : S.1.card = x.1.1 * x.1.2 :=
          (Finset.mem_powersetCard.1 (Finset.mem_filter.1 S.2).1).2
        ⟨GaloisSet.sumCongr (subsetSumEquiv S.1 hScard) p.1.1 p.2.1, by
          rw [GaloisSet.splittingSymbol_sumCongr, p.1.2, p.2.2, Multiset.singleton_add,
            Multiset.cons_erase (Multiset.mem_toFinset.1 x.2)]⟩
    -- Key recovery property: `Ψ ⟨x, S, p⟩` has `i₀`-orbit equal to `S` and `i₀`-factor `x`.
    have hΨ_recover : ∀ (x : σ.toFinset) (S : T (x.1.1 * x.1.2)) (p : Fib x),
        let ρ := (Ψ ⟨x, S, p⟩).1
        (letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀) =
            (S.1 : Set (Fin n)) ∧
          (letI := ρ.mulAction
           let F := IntermediateField.fixedField
             (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)
           (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) = x.1 := by
      intro x S p
      have hScard : S.1.card = x.1.1 * x.1.2 :=
        (Finset.mem_powersetCard.1 (Finset.mem_filter.1 S.2).1).2
      have hi₀ : i₀ ∈ (S.1 : Set (Fin n)) :=
        Finset.mem_coe.2 (Finset.singleton_subset_iff.1 (Finset.mem_filter.1 S.2).2)
      let e := subsetSumEquiv S.1 hScard
      have hrange : Set.range (e ∘ Sum.inl) = (S.1 : Set (Fin n)) :=
        range_subsetSumEquiv_inl S.1 hScard
      obtain ⟨j₀, hj₀⟩ : ∃ j₀, e (Sum.inl j₀) = i₀ := Set.mem_range.1 (hrange.symm ▸ hi₀)
      have htr : p.1.1.IsTransitive :=
        GaloisSet.isTransitive_of_splittingSymbol_eq_singleton p.1.2
      refine ⟨?_, ?_⟩
      · change (letI := (GaloisSet.sumCongr e p.1.1 p.2.1).mulAction
          MulAction.orbit Gal(SeparableClosure K/K) i₀) = (S.1 : Set (Fin n))
        rw [← hj₀, GaloisSet.orbit_sumCongr_inl_of_isTransitive e htr p.2.1 j₀, hrange]
      · change (letI := (GaloisSet.sumCongr e p.1.1 p.2.1).mulAction
          let F := IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)) = x.1
        rw [← hj₀, GaloisSet.stabilizer_sumCongr_inl e p.1.1 p.2.1 j₀]
        have hsym := p.1.1.splittingSymbol_of_isTransitive htr j₀
        rw [p.1.2, Multiset.singleton_inj] at hsym
        exact hsym.symm
    have hΨ_bij : Function.Bijective Ψ := by
      refine ⟨?_, ?_⟩
      · rintro ⟨x, S, p⟩ ⟨x', S', p'⟩ h
        have hρ : (Ψ ⟨x, S, p⟩).1 = (Ψ ⟨x', S', p'⟩).1 := congrArg Subtype.val h
        obtain ⟨horb, hfac⟩ := hΨ_recover x S p
        obtain ⟨horb', hfac'⟩ := hΨ_recover x' S' p'
        have hx_eq : x = x' := Subtype.ext (by rw [← hfac, ← hfac', hρ])
        subst hx_eq
        have hS_eq : S = S' := Subtype.ext (Finset.coe_inj.1 (by rw [← horb, ← horb', hρ]))
        subst hS_eq
        have hScard : S.1.card = x.1.1 * x.1.2 :=
          (Finset.mem_powersetCard.1 (Finset.mem_filter.1 S.2).1).2
        dsimp only [Ψ] at hρ
        have hp : (p.1.1, p.2.1) = (p'.1.1, p'.2.1) :=
          GaloisSet.sumCongr_injective (subsetSumEquiv S.1 hScard) hρ
        have hp_eq : p = p' :=
          Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))
        subst hp_eq
        rfl
      · rintro ⟨ρ, hρ⟩
        let := ρ.mulAction
        let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)
        let x₀ : ℕ × ℕ := (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)
        have hx₀_mem : x₀ ∈ σ := hρ ▸ ρ.mem_splittingSymbol_of_fixedField_stabilizer i₀
        let x : σ.toFinset := ⟨x₀, Multiset.mem_toFinset.2 hx₀_mem⟩
        let S₀ : Finset (Fin n) :=
          open Classical in (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset
        have hS₀_coe : (S₀ : Set (Fin n)) = MulAction.orbit Gal(SeparableClosure K/K) i₀ := by
          classical exact Set.coe_toFinset _
        have hS₀_card : S₀.card = x₀.1 * x₀.2 := by
          classical
          rw [Set.toFinset_card, ← Nat.card_eq_fintype_card,
            ← ρ.finrank_fixedField_stabilizer i₀]
          exact (Nat.mul_div_cancel' F.inertiaDegree_dvd_finrank).symm
        have hi₀_S₀ : {i₀} ⊆ S₀ := by
          rw [Finset.singleton_subset_iff, ← Finset.mem_coe, hS₀_coe]
          exact MulAction.mem_orbit_self i₀
        let S : T (x.1.1 * x.1.2) :=
          ⟨S₀, Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hS₀_card⟩,
            hi₀_S₀⟩⟩
        let e := subsetSumEquiv S₀ hS₀_card
        have hrange : Set.range (e ∘ Sum.inl) = MulAction.orbit Gal(SeparableClosure K/K) i₀ :=
          (range_subsetSumEquiv_inl S₀ hS₀_card).trans hS₀_coe
        have hmaps : ∀ τ, Set.MapsTo (ρ.val τ) (Set.range (e ∘ Sum.inl))
            (Set.range (e ∘ Sum.inl)) := by
          intro τ y hy
          rw [hrange] at hy ⊢
          obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hy
          exact MulAction.mem_orbit_iff.2 ⟨τ * g, by rw [mul_smul, ρ.smul_def]⟩
        let pq := (GaloisSet.sumCongrEquiv e).symm ⟨ρ, hmaps⟩
        have hpq : GaloisSet.sumCongr e pq.1 pq.2 = ρ := by
          rw [← GaloisSet.coe_sumCongrEquiv_apply e pq,
            (GaloisSet.sumCongrEquiv e).apply_symm_apply]
        obtain ⟨j₀, hj₀⟩ : ∃ j₀, e (Sum.inl j₀) = i₀ :=
          Set.mem_range.1 (hrange.symm ▸ MulAction.mem_orbit_self i₀)
        have hstab₁ : (letI := pq.1.mulAction
            MulAction.stabilizer Gal(SeparableClosure K/K) j₀) =
            MulAction.stabilizer Gal(SeparableClosure K/K) i₀ := by
          rw [← GaloisSet.stabilizer_sumCongr_inl e pq.1 pq.2 j₀, hpq, hj₀]
        have htr₁ : pq.1.IsTransitive := by
          rw [pq.1.isTransitive_iff_finrank_fixedField_stabilizer j₀, hstab₁]
          exact (Nat.mul_div_cancel' F.inertiaDegree_dvd_finrank).symm
        have hsym₁ : pq.1.splittingSymbol = {x₀} := by
          rw [pq.1.splittingSymbol_of_isTransitive htr₁ j₀, hstab₁]
        have hsym₂ : pq.2.splittingSymbol = σ.erase x₀ := by
          have hadd : {x₀} + pq.2.splittingSymbol = {x₀} + σ.erase x₀ :=
            calc {x₀} + pq.2.splittingSymbol
                = pq.1.splittingSymbol + pq.2.splittingSymbol := by rw [hsym₁]
              _ = (GaloisSet.sumCongr e pq.1 pq.2).splittingSymbol :=
                  (GaloisSet.splittingSymbol_sumCongr e pq.1 pq.2).symm
              _ = σ := by rw [hpq, hρ]
              _ = {x₀} + σ.erase x₀ := by
                  rw [Multiset.singleton_add, Multiset.cons_erase hx₀_mem]
          exact add_left_cancel hadd
        exact ⟨⟨x, S, ⟨pq.1, hsym₁⟩, ⟨pq.2, hsym₂⟩⟩, Subtype.ext hpq⟩
    -- Reindex the sum along `Ψ` and evaluate each fibre by the transitive mass formula and `ih`.
    have htsum :
        (∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / q ^ ρ.1.discriminantExponent) =
        (n ! : ℝ≥0∞) *
          (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) := by
      rw [← (Equiv.ofBijective Ψ hΨ_bij).tsum_eq]
      have hterm : ∀ z : (Σ (x : σ.toFinset) (_ : T (x.1.1 * x.1.2)), Fib x),
          1 / q ^ (Ψ z).1.discriminantExponent =
            (1 / q ^ z.2.2.1.1.discriminantExponent) *
              (1 / q ^ z.2.2.2.1.discriminantExponent) := by
        rintro ⟨x, S, p⟩
        have hqt₁ : q ^ p.1.1.discriminantExponent ≠ ⊤ :=
          ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
        have hqt₂ : q ^ p.2.1.discriminantExponent ≠ ⊤ :=
          ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
        change 1 / q ^ (GaloisSet.sumCongr _ p.1.1 p.2.1).discriminantExponent = _
        rw [GaloisSet.discriminantExponent_sumCongr, pow_add, one_div, one_div, one_div,
          ENNReal.mul_inv (.inr hqt₂) (.inl hqt₁)]
      simp_rw [Equiv.ofBijective_apply, hterm]
      rw [tsum_sigma', tsum_fintype]
      dsimp only
      have hfib : ∀ x : σ.toFinset,
          (∑' z : (Σ (_ : T (x.1.1 * x.1.2)), Fib x),
            (1 / q ^ z.2.1.1.discriminantExponent) *
              (1 / q ^ z.2.2.1.discriminantExponent)) =
          ((σ.count x.1 * (x.1.1 * x.1.2) : ℕ) : ℝ≥0∞) * ((n - 1)! : ℝ≥0∞) *
            (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) := by
        intro x
        have hx : x.1 ∈ σ := Multiset.mem_toFinset.1 x.2
        obtain ⟨hf, he⟩ := hσ x.1 hx
        set m := x.1.1 * x.1.2
        have hm_pos : 0 < m := Nat.mul_pos hf he
        have hm_le : m ≤ n := by
          rw [← hn]
          exact Multiset.single_le_sum (fun _ _ ↦ Nat.zero_le _) _ (Multiset.mem_map_of_mem _ hx)
        have hdeg_erase : ((σ.erase x.1).map fun y => y.1 * y.2).sum = n - m := by
          have hcons := congrArg (fun τ : Multiset (ℕ × ℕ) ↦ (τ.map fun y => y.1 * y.2).sum)
            (Multiset.cons_erase hx)
          rw [Multiset.map_cons, Multiset.sum_cons, hn] at hcons
          change m + ((σ.erase x.1).map fun y => y.1 * y.2).sum = n at hcons
          omega
        have hcard_erase : Multiset.card (σ.erase x.1) = r := by
          rw [Multiset.card_erase_of_mem hx, hr]
          rfl
        have hpos_erase : ∀ y ∈ σ.erase x.1, 0 < y.1 ∧ 0 < y.2 :=
          fun y hy ↦ hσ y (Multiset.mem_of_mem_erase hy)
        have h₁ := etaleMass_isTransitive_splittingSymbol (K := K) x.1.1 x.1.2 hf he
        have h₁' :
            (∑' ρ₁ : {ρ₁ : GaloisSet K (x.1.1 * x.1.2) // ρ₁.splittingSymbol = {x.1}},
              1 / q ^ ρ₁.1.discriminantExponent) =
            (m ! : ℝ≥0∞) * (1 / ((x.1.1 : ℝ≥0∞) * q ^ (x.1.1 * (x.1.2 - 1)))) := by
          have hmf0 : (m ! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
          have hmft : (m ! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          have := congrArg ((m ! : ℝ≥0∞) * ·) h₁
          rwa [mul_inv_mul_cancel_left hmf0 hmft] at this
        have h₂ := ih (n - m) (σ.erase x.1) hcard_erase hpos_erase hdeg_erase
        have h₂' :
            (∑' ρ₂ : {ρ₂ : GaloisSet K (n - (x.1.1 * x.1.2)) //
                ρ₂.splittingSymbol = σ.erase x.1},
              1 / q ^ ρ₂.1.discriminantExponent) =
            ((n - m)! : ℝ≥0∞) *
              (1 / ((splittingSymbolAut (σ.erase x.1) : ℝ≥0∞) *
                q ^ splittingSymbolExponent (σ.erase x.1))) := by
          have hlf0 : ((n - m)! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
          have hlft : ((n - m)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
          have := congrArg (((n - m)! : ℝ≥0∞) * ·) h₂
          rwa [mul_inv_mul_cancel_left hlf0 hlft] at this
        have hTcard : (T (x.1.1 * x.1.2)).card = Nat.choose (n - 1) (m - 1) := by
          have hsub := Finset.card_filter_powersetCard_subset {i₀}
            (Finset.univ : Finset (Fin n)) m (Finset.subset_univ _)
            (by rw [Finset.card_singleton]; exact hm_pos)
          simpa [T, m] using hsub
        have hchoose : Nat.choose (n - 1) (m - 1) * m ! * (n - m)! = m * (n - 1)! := by
          have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le_sub_right hm_le 1)
          rw [show n - 1 - (m - 1) = n - m by omega] at h1
          calc Nat.choose (n - 1) (m - 1) * m ! * (n - m)!
              = m * (Nat.choose (n - 1) (m - 1) * (m - 1)! * (n - m)!) := by
                  rw [← Nat.mul_factorial_pred hm_pos.ne']; ring
            _ = m * (n - 1)! := by rw [h1]
        rw [tsum_sigma', tsum_fintype]
        dsimp only [Fib]
        have hprod :
            (∑' z : {ρ₁ : GaloisSet K (x.1.1 * x.1.2) // ρ₁.splittingSymbol = {x.1}} ×
                {ρ₂ : GaloisSet K (n - x.1.1 * x.1.2) // ρ₂.splittingSymbol = σ.erase x.1},
              (1 / q ^ z.1.1.discriminantExponent) * (1 / q ^ z.2.1.discriminantExponent)) =
            ((m ! : ℝ≥0∞) * (1 / ((x.1.1 : ℝ≥0∞) * q ^ (x.1.1 * (x.1.2 - 1))))) *
              (((n - m)! : ℝ≥0∞) *
                (1 / ((splittingSymbolAut (σ.erase x.1) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x.1)))) := by
          rw [tsum_prod']
          simp_rw [ENNReal.tsum_mul_left, h₂']
          rw [ENNReal.tsum_mul_right, h₁']
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hTcard, nsmul_eq_mul, hprod]
        have hAut_erase := splittingSymbolAut_eq_mul_erase hx
        have hexp_erase :
            splittingSymbolExponent σ =
              x.1.1 * (x.1.2 - 1) + splittingSymbolExponent (σ.erase x.1) := by
          conv_lhs => rw [← Multiset.cons_erase hx, ← Multiset.singleton_add]
          rw [splittingSymbolExponent_add, splittingSymbolExponent_singleton]
        set D₁ : ℝ≥0∞ := (x.1.1 : ℝ≥0∞) * q ^ (x.1.1 * (x.1.2 - 1))
        set D₂ : ℝ≥0∞ :=
          (splittingSymbolAut (σ.erase x.1) : ℝ≥0∞) * q ^ splittingSymbolExponent (σ.erase x.1)
        have hD₁t : D₁ ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
            (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
        have hD₂t : D₂ ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
            (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
        have hc0 : (σ.count x.1 : ℝ≥0∞) ≠ 0 :=
          Nat.cast_ne_zero.2 (Multiset.count_pos.2 hx).ne'
        have hct : (σ.count x.1 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        have hdenom :
            (splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ =
              (σ.count x.1 : ℝ≥0∞) * (D₁ * D₂) := by
          simp only [D₁, D₂, hAut_erase, hexp_erase, pow_add, Nat.cast_mul]
          ring
        have hinv :
            1 / D₁ * (1 / D₂) =
              (σ.count x.1 : ℝ≥0∞) *
                (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) := by
          rw [hdenom, one_div, one_div, one_div,
            ENNReal.mul_inv (.inl hc0) (.inl hct),
            ENNReal.mul_inv (.inr hD₂t) (.inl hD₁t), mul_inv_mul_cancel_left hc0 hct]
        have hnum :
            (Nat.choose (n - 1) (m - 1) : ℝ≥0∞) * (m ! : ℝ≥0∞) * ((n - m)! : ℝ≥0∞) =
              (m : ℝ≥0∞) * ((n - 1)! : ℝ≥0∞) := by
          exact_mod_cast hchoose
        calc
          (Nat.choose (n - 1) (m - 1) : ℝ≥0∞) *
              ((m ! : ℝ≥0∞) * (1 / D₁) * (((n - m)! : ℝ≥0∞) * (1 / D₂)))
            = ((Nat.choose (n - 1) (m - 1) : ℝ≥0∞) * (m ! : ℝ≥0∞) * ((n - m)! : ℝ≥0∞)) *
                (1 / D₁ * (1 / D₂)) := by ring
          _ = (m : ℝ≥0∞) * ((n - 1)! : ℝ≥0∞) *
                ((σ.count x.1 : ℝ≥0∞) *
                  (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ))) := by
              rw [hnum, hinv]
          _ = ((σ.count x.1 * m : ℕ) : ℝ≥0∞) * ((n - 1)! : ℝ≥0∞) *
                (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) := by
              dsimp only [m]; push_cast; ring
      simp_rw [hfib, ← Finset.sum_mul]
      have hcount_sum :
          (∑ x ∈ σ.toFinset.attach,
              ((σ.count x.1 * (x.1.1 * x.1.2) : ℕ) : ℝ≥0∞)) = (n : ℝ≥0∞) := by
        rw [Finset.sum_attach σ.toFinset fun y ↦ ((σ.count y * (y.1 * y.2) : ℕ) : ℝ≥0∞),
          ← Nat.cast_sum]
        congr 1
        have hmap := Finset.sum_multiset_map_count σ fun y ↦ y.1 * y.2
        simpa [smul_eq_mul, hn] using hmap.symm
      change (∑ x ∈ σ.toFinset.attach,
          ((σ.count x.1 * (x.1.1 * x.1.2) : ℕ) : ℝ≥0∞)) * ((n - 1)! : ℝ≥0∞) *
          (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) = _
      rw [hcount_sum, ← Nat.cast_mul, Nat.mul_factorial_pred hn_pos.ne']
    have hnf0 : (n ! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hnft : (n ! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [htsum, ← mul_assoc, ENNReal.inv_mul_cancel hnf0 hnft, one_mul]

/-! ### Mass formula for a fixed ramification partition -/

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the labelled Galois sets of size `n` whose
splitting symbol has ramification partition `π` have mass `1 / q ^ k`. -/
theorem etaleMass_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : Multiset.card π.parts ≤ n - k) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  let Sym := {σ : Multiset (ℕ × ℕ) //
    (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
      (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let Φ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → Sym :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol, fun _ hx ↦ ρ.1.pos_of_mem_splittingSymbol hx,
      ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩
  rw [← tsum_fiberwise _ Φ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ σ : Sym,
      (n ! : ℝ≥0∞)⁻¹ *
          (∑' ρ : Φ ⁻¹' {σ}, 1 / q ^ ρ.1.1.discriminantExponent) =
        (1 / (splittingSymbolAut σ.1 : ℝ≥0∞)) * (1 / q ^ k) := by
    intro σ
    let ε : Φ ⁻¹' {σ} ≃ {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
      { toFun := fun ρ ↦ ⟨ρ.1.1, congrArg Subtype.val ρ.2⟩
        invFun := fun ρ ↦ ⟨⟨ρ.1, by rw [ρ.2, σ.2.2.2]⟩, Subtype.ext ρ.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hsum :
        (∑' ρ : Φ ⁻¹' {σ}, 1 / q ^ ρ.1.1.discriminantExponent) =
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1},
            1 / q ^ ρ.1.discriminantExponent :=
      ε.tsum_eq fun ρ ↦ 1 / q ^ ρ.1.discriminantExponent
    have hexp : splittingSymbolExponent σ.1 = k := by
      rw [splittingSymbolExponent_eq_sum_ramificationPartition, σ.2.2.2, π.parts_sum]
    have hAut0 : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 (splittingSymbolAut_pos fun x hx ↦ (σ.2.1 x hx).1).ne'
    have hAutt : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [hsum, etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1, hexp,
      one_div, one_div, one_div, ENNReal.mul_inv (.inl hAut0) (.inl hAutt)]
  rw [tsum_congr hfib, ENNReal.tsum_mul_right,
    tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

/-! ### Bhargava's mass formula -/

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, and §8]): for any
nonarchimedean local field `K` with residue cardinality `q`,
`M_n(K) = ∑_{k ≤ n} q(k, n - k) / q ^ k`,
where `q(k, m)` is the number of partitions of `k` into at most `m` parts. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter
            fun π => Multiset.card π.parts ≤ n - k).card : ℝ≥0∞) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  classical
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  let P := Σ k : Finset.range (n + 1),
    {π : (k : ℕ).Partition // Multiset.card π.parts ≤ n - (k : ℕ)}
  let Ψ : GaloisSet K n → P := fun ρ ↦
    let σ := ρ.splittingSymbol
    have hdeg := sum_map_mul_eq_sum_ramificationPartition_add σ
      fun x hx ↦ (ρ.pos_of_mem_splittingSymbol hx).2
    have hsum_le :
        (ramificationPartition σ).sum + Multiset.card (ramificationPartition σ) ≤ n := by
      rw [ρ.sum_map_mul_splittingSymbol] at hdeg
      omega
    ⟨⟨(ramificationPartition σ).sum, Finset.mem_range.2 (by omega)⟩,
      ⟨{ parts := ramificationPartition σ
         parts_pos := fun {t} ht ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ht).1
         parts_sum := rfl }, by dsimp; omega⟩⟩
  rw [etaleMass_def, ← tsum_fiberwise _ Ψ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ p : P,
      (n ! : ℝ≥0∞)⁻¹ * (∑' ρ : Ψ ⁻¹' {p}, 1 / q ^ ρ.1.discriminantExponent) =
        1 / q ^ (p.1 : ℕ) := by
    rintro ⟨⟨k, hk⟩, ⟨π, hπ⟩⟩
    let ε : Ψ ⁻¹' {⟨⟨k, hk⟩, ⟨π, hπ⟩⟩} ≃
        {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} :=
      { toFun := fun ρ ↦ ⟨ρ.1, by
          have h2 : (Ψ ρ.1).2.1.parts = π.parts := by
            rw [ρ.2]
          exact h2⟩
        invFun := fun ρ ↦ ⟨ρ.1, by
          rcases hΨ : Ψ ρ.1 with ⟨⟨k', hk'⟩, ⟨π', hπ'⟩⟩
          rw [Set.mem_preimage, Set.mem_singleton_iff, hΨ]
          have hparts : π'.parts = π.parts :=
            (congrArg (fun p : P ↦ p.2.1.parts) hΨ).symm.trans ρ.2
          have hk_eq : k' = k := by
            simpa using
              π'.parts_sum.symm.trans ((congrArg Multiset.sum hparts).trans π.parts_sum)
          subst hk_eq
          exact Sigma.ext rfl (heq_of_eq (Subtype.ext (Nat.Partition.ext hparts)))⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hsum :
        (∑' ρ : Ψ ⁻¹' {⟨⟨k, hk⟩, ⟨π, hπ⟩⟩}, 1 / q ^ ρ.1.discriminantExponent) =
          ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
            1 / q ^ ρ.1.discriminantExponent :=
      ε.tsum_eq fun ρ ↦ 1 / q ^ ρ.1.discriminantExponent
    rw [hsum, etaleMass_ramificationPartition n k π hπ]
  rw [tsum_congr hfib, tsum_fintype, Fintype.sum_sigma]
  dsimp only
  have hinner : ∀ x : Finset.range (n + 1),
      (∑ _y : {π : (x : ℕ).Partition // Multiset.card π.parts ≤ n - (x : ℕ)},
          (1 / q ^ (x : ℕ))) =
        (((Finset.univ : Finset (x : ℕ).Partition).filter
            fun π => Multiset.card π.parts ≤ n - (x : ℕ)).card : ℝ≥0∞) /
          q ^ (x : ℕ) := fun x ↦ by
    have hcard :
        Fintype.card {π : (x : ℕ).Partition // Multiset.card π.parts ≤ n - (x : ℕ)} =
          ((Finset.univ : Finset (x : ℕ).Partition).filter
            fun π => Multiset.card π.parts ≤ n - (x : ℕ)).card :=
      Fintype.card_of_subtype
        ((Finset.univ : Finset (x : ℕ).Partition).filter
          fun π => Multiset.card π.parts ≤ n - (x : ℕ))
        fun π ↦ by simp
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one_div]
  simp_rw [hinner]
  exact Finset.sum_coe_sort (Finset.range (n + 1)) fun k ↦
    (((Finset.univ : Finset k.Partition).filter
        fun π => Multiset.card π.parts ≤ n - k).card : ℝ≥0∞) / q ^ k

variable (K) in
/-- **Bhargava's mass formula over étale algebras** ([Bhargava 2007, Thm. 1.1 and §8]): for any
family `A` of étale `K`-algebras of degree `n` containing one representative of each `K`-isomorphism
class,
`∑_i 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k ≤ n} q(k, n - k) / q ^ k`. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter
            fun π => Multiset.card π.parts ≤ n - k).card : ℝ≥0∞) /
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

end TauCeti
