/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleWeight
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.TransitiveMass
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra

/-!
# Bhargava's mass formulas for étale algebras over a local field

Let `K` be a nonarchimedean local field with `q` residue classes. This file proves Bhargava's mass
formulas for labelled Galois sets and finite étale algebras of degree `n` over `K`, stratified by
splitting symbol, by ramification partition, and in total:

* **Fixed splitting symbol** (`TauCeti.etaleMass_splittingSymbol`, [Bhargava 2007, Prop. 2.1]):
  for a splitting symbol `σ` of degree `n`, the Galois sets with splitting symbol `σ` have mass
  `1 / (#Aut(σ) · q ^ (∑ f_i(e_i - 1)))`. Peeling off the orbit of a base label via
  `GaloisSet.orbitCardEquiv` reduces the sum inductively to the transitive mass
  `TauCeti.etaleMass_isTransitive_splittingSymbol`.
* **Fixed ramification partition** (`TauCeti.etaleMass_ramificationPartition`,
  [Bhargava 2007, Prop. 2.2]): for a partition `π` of `k` into at most `n - k` parts, the Galois
  sets of size `n` whose splitting symbol has ramification partition `π` have mass `q ^ (-k)`, by
  summing `TauCeti.etaleMass_splittingSymbol` against
  `TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition`.
* **Total étale mass** (`TauCeti.etaleMass_eq` and `TauCeti.tsum_etaleDiscriminantExponent_eq`,
  [Bhargava 2007, Theorem 1.1, Prop. 2.3, and §8]):
  `M_n(K) = ∑_{k ≤ n} q(k, n - k) q ^ (-k)`, where `q(k, m)` is the number of partitions of `k`
  into at most `m` parts. Because `M_n(K)` is identified with Bhargava's automorphism-weighted sum
  over `K`-isomorphism classes of étale algebras of degree `n` by
  `TauCeti.tsum_etaleDiscriminantExponent`, the same formula evaluates
  `∑_{[A]} 1 / (#Aut_K(A) · q ^ d(A))`, including in equal characteristic where infinitely many
  isomorphism classes may occur.

## Main results

* `TauCeti.etaleMass_splittingSymbol`: mass of Galois sets with prescribed splitting symbol.
* `TauCeti.etaleMass_ramificationPartition`: mass of Galois sets with prescribed ramification
  partition.
* `TauCeti.etaleMass_eq`: Bhargava's formula for `etaleMass K n`.
* `TauCeti.tsum_etaleDiscriminantExponent_eq`: Bhargava's mass formula over `K`-isomorphism classes
  of étale `K`-algebras of degree `n`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1, Propositions 2.1–2.3, and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped Nat ENNReal

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Mass formula for a fixed splitting symbol -/

/-- Pointwise decomposition of the splitting-symbol indicator on a disjoint union `ρ₁ ⊕ ρ₂` in
which `ρ₁` is transitive on a nonempty `Fin m`: `ρ₁.splittingSymbol` is a singleton `{y}` with
`y.1 * y.2 = m`, so `ρ₁.splittingSymbol + ρ₂.splittingSymbol = σ` holds for at most one
`x ∈ σ.toFinset` with `x.1 * x.2 = m`, namely `x = y` with `ρ₂.splittingSymbol = σ.erase x`. -/
private theorem indicator_splittingSymbol_add_eq_sum {m k : ℕ} (hm : 0 < m)
    (σ : Multiset (ℕ × ℕ)) (ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive})
    (ρ₂ : GaloisSet K k) (a b : ℝ≥0∞) :
    (if ρ₁.1.splittingSymbol + ρ₂.splittingSymbol = σ then a * b else 0) =
      ∑ x ∈ σ.toFinset with x.1 * x.2 = m,
        (if ρ₁.1.splittingSymbol = {x} then a else 0) *
          (if ρ₂.splittingSymbol = σ.erase x then b else 0) := by
  classical
  have hy := ρ₁.1.splittingSymbol_of_isTransitive ρ₁.2 ⟨0, hm⟩
  set y : ℕ × ℕ :=
    letI := ρ₁.1.mulAction
    let F := IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) (⟨0, hm⟩ : Fin m))
    (F.inertiaDegree, m / F.inertiaDegree)
  have hy_deg : y.1 * y.2 = m := by
    have h := ρ₁.1.sum_map_mul_splittingSymbol
    rwa [hy, Multiset.map_singleton, Multiset.sum_singleton] at h
  rw [hy]
  by_cases h : {y} + ρ₂.splittingSymbol = σ
  · simp only [h, ↓reduceIte]
    have hcons : y ::ₘ ρ₂.splittingSymbol = σ := by simpa using h
    have hy_mem : y ∈ σ := hcons ▸ Multiset.mem_cons_self y _
    have hy_erase : ρ₂.splittingSymbol = σ.erase y := by
      rw [← hcons, Multiset.erase_cons_head]
    have hy_filt : y ∈ σ.toFinset.filter (fun x ↦ x.1 * x.2 = m) :=
      Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hy_mem, hy_deg⟩
    symm
    rw [Finset.sum_eq_single y (fun x _ hxy ↦ ?_) (fun hnot ↦ (hnot hy_filt).elim)]
    · simp only [↓reduceIte, hy_erase]
    · have hne : ({y} : Multiset (ℕ × ℕ)) ≠ {x} :=
        fun heq ↦ hxy (Multiset.singleton_inj.1 heq).symm
      simp only [hne, ↓reduceIte, zero_mul]
  · simp only [h, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero fun x hx ↦ ?_
    by_cases hx₁ : ({y} : Multiset (ℕ × ℕ)) = {x}
    · have hxy : y = x := Multiset.singleton_inj.1 hx₁
      subst hxy
      have hx₂ : ρ₂.splittingSymbol ≠ σ.erase y := by
        intro her
        apply h
        have hy_mem : y ∈ σ := Multiset.mem_toFinset.1 (Finset.mem_filter.1 hx).1
        simpa [her] using Multiset.cons_erase hy_mem
      simp only [hx₂, ↓reduceIte, mul_zero]
    · simp only [hx₁, ↓reduceIte, zero_mul]

/-- The unrestricted `tsum` over transitive Galois sets of size `f * e` with indicator
`ρ.splittingSymbol = {(f, e)}` equals the subtype `tsum`. -/
private theorem tsum_isTransitive_indicator_splittingSymbol {f e : ℕ} :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
        (if ρ.1.splittingSymbol = {(f, e)} then
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent else 0) =
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent := by
  classical
  let ε : {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} //
      ρ.1.splittingSymbol = {(f, e)}} ≃
      {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun ρ : GaloisSet K (f * e) ↦ ρ.IsTransitive)
      (fun ρ ↦ ρ.splittingSymbol = {(f, e)})).trans
      (Equiv.subtypeEquivRight fun ρ ↦
        ⟨And.right, fun h ↦
          ⟨ρ.isTransitive_of_card_splittingSymbol_le_one (by rw [h]; simp), h⟩⟩)
  have hsub := (_root_.tsum_subtype
    (s := {ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} | ρ.1.splittingSymbol = {(f, e)}})
    (fun ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive} ↦
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)).symm
  exact (tsum_congr fun ρ ↦ (Set.indicator_apply _ _ ρ).symm).trans
    (hsub.trans (ε.tsum_eq fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent))

/-- Elementary binomial-factorial identity used when peeling off an `m`-element orbit containing a
fixed label: `((n - 1).choose (m - 1)) * m! * (n - m)! = m * (n - 1)!` for `1 ≤ m ≤ n`. -/
private theorem choose_pred_mul_factorial_mul_factorial {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (n - 1).choose (m - 1) * m ! * (n - m)! = m * (n - 1)! := by
  have hm_fac : m ! = m * (m - 1)! := (Nat.mul_factorial_pred (by omega)).symm
  have hsub : n - 1 - (m - 1) = n - m := by omega
  have hchoose := Nat.choose_mul_factorial_mul_factorial (show m - 1 ≤ n - 1 by omega)
  rw [hsub] at hchoose
  calc (n - 1).choose (m - 1) * m ! * (n - m)!
      = m * ((n - 1).choose (m - 1) * (m - 1)! * (n - m)!) := by rw [hm_fac]; ring
    _ = m * (n - 1)! := by rw [hchoose]

/-- **Mass formula for a fixed splitting type** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n`, the labelled Galois sets with splitting symbol `σ` have mass
`1 / (#Aut(σ) · q ^ (∑ f_i(e_i - 1)))`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  classical
  set r := Multiset.card σ with hr_def
  clear_value r
  induction r generalizing n σ with
  | zero =>
    have hσ0 : σ = 0 := Multiset.card_eq_zero.1 hr_def.symm
    subst hσ0
    simp only [Multiset.map_zero, Multiset.sum_zero] at hn
    subst hn
    let ρ₀ : {ρ : GaloisSet K 0 // ρ.splittingSymbol = 0} :=
      ⟨GaloisSet.trivial K 0, GaloisSet.splittingSymbol_zero _⟩
    rw [tsum_eq_single ρ₀ fun ρ hρ ↦ (hρ (Subtype.ext (Subsingleton.elim _ _))).elim]
    simp [ρ₀]
  | succ r ih =>
    -- `σ` is nonempty, so `0 < n` and `i₀ = ⟨0, hn_pos⟩` is a valid base label.
    have hcard_ne : Multiset.card σ ≠ 0 := hr_def ▸ Nat.succ_ne_zero r
    obtain ⟨x₀, hx₀⟩ := Multiset.exists_mem_of_ne_zero (mt Multiset.card_eq_zero.2 hcard_ne)
    have hn_pos : 0 < n := by
      have hx₀_pos : 0 < x₀.1 * x₀.2 := Nat.mul_pos (hσ x₀ hx₀).1 (hσ x₀ hx₀).2
      have hx₀_le : x₀.1 * x₀.2 ≤ n :=
        hn ▸ Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun x : ℕ × ℕ ↦ x.1 * x.2) hx₀)
      omega
    let i₀ : Fin n := ⟨0, hn_pos⟩
    set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
    have hq0 : q ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne _)
    -- Rewrite the subtype `tsum` as an unrestricted `tsum` over `GaloisSet K n` and fiber by the
    -- orbit size `m` of `i₀`.
    have hsub : ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / q ^ ρ.1.discriminantExponent =
        ∑' ρ : GaloisSet K n,
          if ρ.splittingSymbol = σ then 1 / q ^ ρ.discriminantExponent else 0 := by
      have h := _root_.tsum_subtype (s := {ρ : GaloisSet K n | ρ.splittingSymbol = σ})
        (fun ρ : GaloisSet K n ↦ 1 / q ^ ρ.discriminantExponent)
      exact h.trans (tsum_congr fun ρ ↦ Set.indicator_apply _ _ ρ)
    let orbCard : GaloisSet K n → ℕ := fun ρ ↦
      letI := ρ.mulAction
      (MulAction.orbit Gal(SeparableClosure K/K) i₀).ncard
    let e_orb (m : ℕ) :
        (↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)) ×
          {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K (n - m)) ≃
          orbCard ⁻¹' {m} :=
      (GaloisSet.orbitCardEquiv (K := K) i₀ m).trans
        (Equiv.subtypeEquivRight fun _ ↦ Set.mem_singleton_iff).symm
    rw [hsub, ← tsum_fiberwise _ orbCard]
    -- Restrict `m` to `[1, n]`; outside this range no `m`-subset of `Fin n` contains `i₀`.
    rw [tsum_eq_sum (s := Finset.Icc 1 n) fun m hm ↦ by
      have hempty : IsEmpty ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)) :=
        ⟨fun s ↦ hm <| Finset.mem_Icc.2 <| by
          have hs_card : s.1.card = m := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 s.2).1).2
          have hi₀ : i₀ ∈ s.1 := (Finset.mem_filter.1 s.2).2
          have hle : s.1.card ≤ n := by simpa using Finset.card_le_univ s.1
          have hpos : 0 < s.1.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
          omega⟩
      rw [← (e_orb m).tsum_eq]
      exact tsum_empty]
    -- Evaluate each fiber `m ∈ [1, n]` via `orbitCardEquiv`, the transitive mass, and `ih`.
    have hfiber : ∀ m ∈ Finset.Icc 1 n,
        (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : orbCard ⁻¹' {m},
            (if ρ.1.splittingSymbol = σ then 1 / q ^ ρ.1.discriminantExponent else 0) =
        ∑ x ∈ σ.toFinset with x.1 * x.2 = m,
          (((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) / (n : ℝ≥0∞)) *
            (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) := by
      intro m hm_mem
      obtain ⟨hm₁, hmn⟩ := Finset.mem_Icc.1 hm_mem
      have hm_pos : 0 < m := by omega
      -- Reindex `orbCard ⁻¹' {m}` along `e_orb m`.
      rw [← (e_orb m).tsum_eq]
      -- Split the product `S_m × Trans(m) × GaloisSet(n - m)` and sum the `S_m` factor.
      have hterm : ∀ (s : ↥((Finset.univ.powersetCard m).filter (i₀ ∈ ·)))
          (ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive}) (ρ₂ : GaloisSet K (n - m)),
          (if (e_orb m (s, ρ₁, ρ₂)).1.splittingSymbol = σ then
            1 / q ^ (e_orb m (s, ρ₁, ρ₂)).1.discriminantExponent
          else 0) =
          (if ρ₁.1.splittingSymbol + ρ₂.splittingSymbol = σ then
            (1 / q ^ ρ₁.1.discriminantExponent) * (1 / q ^ ρ₂.discriminantExponent)
          else 0) := by
        intro s ρ₁ ρ₂
        have hcoe : (e_orb m (s, ρ₁, ρ₂)).1 =
            (GaloisSet.orbitCardEquiv i₀ m (s, ρ₁, ρ₂) : GaloisSet K n) := rfl
        rw [hcoe, GaloisSet.coe_orbitCardEquiv_apply, GaloisSet.splittingSymbol_sumCongr,
          GaloisSet.discriminantExponent_sumCongr, pow_add, one_div, one_div, one_div,
          ENNReal.mul_inv (.inl (pow_ne_zero _ hq0)) (.inr (pow_ne_zero _ hq0))]
      rw [tsum_prod', tsum_fintype]
      simp_rw [tsum_prod', hterm, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]
      -- Count the `m`-subsets containing `i₀`: `((n - 1).choose (m - 1))`.
      have hcard_S : ((Finset.univ.powersetCard m).filter (i₀ ∈ ·)).card =
          (n - 1).choose (m - 1) := by
        have hfilt : (Finset.univ.powersetCard m).filter (i₀ ∈ ·) =
            (Finset.univ.powersetCard m).filter ({i₀} ⊆ ·) := by
          ext s
          simp [Finset.singleton_subset_iff]
        rw [hfilt, Finset.card_filter_powersetCard_subset {i₀} Finset.univ m
          (Finset.subset_univ _) (by simpa using hm₁)]
        simp
      rw [hcard_S]
      -- Expand the splitting-symbol indicator over `x ∈ σ.toFinset` with `x.1 * x.2 = m`,
      -- interchange `∑'` with the finite sum, and factor the two independent sums.
      have dinner : (∑' ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive},
            ∑' ρ₂ : GaloisSet K (n - m),
              if ρ₁.1.splittingSymbol + ρ₂.splittingSymbol = σ then
                (1 / q ^ ρ₁.1.discriminantExponent) * (1 / q ^ ρ₂.discriminantExponent)
              else 0) =
          ∑ x ∈ σ.toFinset with x.1 * x.2 = m,
            (∑' ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive},
              if ρ₁.1.splittingSymbol = {x} then 1 / q ^ ρ₁.1.discriminantExponent else 0) *
            (∑' ρ₂ : GaloisSet K (n - m),
              if ρ₂.splittingSymbol = σ.erase x then 1 / q ^ ρ₂.discriminantExponent else 0) := by
        simp_rw [indicator_splittingSymbol_add_eq_sum hm_pos σ]
        simp_rw [Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      rw [dinner, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx_filt ↦ ?_
      obtain ⟨hx_fin, hxm⟩ := Finset.mem_filter.1 hx_filt
      have hx : x ∈ σ := Multiset.mem_toFinset.1 hx_fin
      obtain ⟨hf_pos, he_pos⟩ := hσ x hx
      -- Factor 1: transitive mass at `x = (x.1, x.2)` with `x.1 * x.2 = m`.
      have hfac₁ : (∑' ρ₁ : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive},
            if ρ₁.1.splittingSymbol = {x} then 1 / q ^ ρ₁.1.discriminantExponent else 0) =
          (m ! : ℝ≥0∞) * (1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)))) := by
        subst hxm
        rcases x with ⟨f, e⟩
        rw [tsum_isTransitive_indicator_splittingSymbol]
        have htr := etaleMass_isTransitive_splittingSymbol (K := K) f e hf_pos he_pos
        have hm0 : ((f * e)! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
        have hmtop : ((f * e)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        calc ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
              1 / q ^ ρ.1.discriminantExponent
            = ((f * e)! : ℝ≥0∞) * (((f * e)! : ℝ≥0∞)⁻¹ *
                ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
                  1 / q ^ ρ.1.discriminantExponent) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hm0 hmtop, one_mul]
          _ = ((f * e)! : ℝ≥0∞) * (1 / ((f : ℝ≥0∞) * q ^ (f * (e - 1)))) := by rw [htr]
      -- Factor 2: induction hypothesis on `σ.erase x` of degree `n - m`.
      have hdeg_er : ((σ.erase x).map fun y ↦ y.1 * y.2).sum = n - m := by
        have hcons : ((x ::ₘ σ.erase x).map fun y ↦ y.1 * y.2).sum = n := by
          rwa [Multiset.cons_erase hx]
        rw [Multiset.map_cons, Multiset.sum_cons, hxm] at hcons
        omega
      have hcard_er : r = Multiset.card (σ.erase x) := by
        have := Multiset.card_erase_of_mem hx
        rw [this, Nat.pred_eq_sub_one]
        omega
      have hpos_er : ∀ y ∈ σ.erase x, 0 < y.1 ∧ 0 < y.2 :=
        fun y hy ↦ hσ y (Multiset.mem_of_mem_erase hy)
      have hih := ih (n - m) (σ.erase x) hpos_er hdeg_er hcard_er
      have hfac₂ : (∑' ρ₂ : GaloisSet K (n - m),
            if ρ₂.splittingSymbol = σ.erase x then 1 / q ^ ρ₂.discriminantExponent else 0) =
          ((n - m)! : ℝ≥0∞) *
            (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              q ^ splittingSymbolExponent (σ.erase x))) := by
        have hsub₂ : (∑' ρ₂ : GaloisSet K (n - m),
              if ρ₂.splittingSymbol = σ.erase x then 1 / q ^ ρ₂.discriminantExponent else 0) =
            ∑' ρ₂ : {ρ₂ : GaloisSet K (n - m) // ρ₂.splittingSymbol = σ.erase x},
              1 / q ^ ρ₂.1.discriminantExponent := by
          have h := (_root_.tsum_subtype
            (s := {ρ₂ : GaloisSet K (n - m) | ρ₂.splittingSymbol = σ.erase x})
            (fun ρ₂ : GaloisSet K (n - m) ↦ 1 / q ^ ρ₂.discriminantExponent)).symm
          exact (tsum_congr fun ρ₂ ↦ (Set.indicator_apply _ _ ρ₂).symm).trans h
        have hnm0 : ((n - m)! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
        have hnmtop : ((n - m)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        rw [hsub₂]
        calc ∑' ρ₂ : {ρ₂ : GaloisSet K (n - m) // ρ₂.splittingSymbol = σ.erase x},
              1 / q ^ ρ₂.1.discriminantExponent
            = ((n - m)! : ℝ≥0∞) * (((n - m)! : ℝ≥0∞)⁻¹ *
                ∑' ρ₂ : {ρ₂ : GaloisSet K (n - m) // ρ₂.splittingSymbol = σ.erase x},
                  1 / q ^ ρ₂.1.discriminantExponent) := by
              rw [← mul_assoc, ENNReal.mul_inv_cancel hnm0 hnmtop, one_mul]
          _ = ((n - m)! : ℝ≥0∞) *
                (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x))) := by rw [hih]
      rw [hfac₁, hfac₂]
      -- Combine the factorials and `#Aut(σ) = x.1 * σ.count x * #Aut(σ.erase x)`.
      have hcomb : ((n ! : ℝ≥0∞)⁻¹ *
            (((n - 1).choose (m - 1) : ℝ≥0∞) * ((m ! : ℝ≥0∞) * ((n - m)! : ℝ≥0∞)))) =
          (m : ℝ≥0∞) / (n : ℝ≥0∞) := by
        have hnat := choose_pred_mul_factorial_mul_factorial hm₁ hmn
        have hn_fac : n ! = n * (n - 1)! := (Nat.mul_factorial_pred hn_pos.ne').symm
        have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn_pos.ne'
        have hn10 : ((n - 1)! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
        have hn1top : ((n - 1)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        have hcast : (((n - 1).choose (m - 1) : ℝ≥0∞) * ((m ! : ℝ≥0∞) * ((n - m)! : ℝ≥0∞))) =
            (m : ℝ≥0∞) * ((n - 1)! : ℝ≥0∞) := by
          rw [← mul_assoc]
          exact_mod_cast hnat
        rw [hcast, hn_fac, Nat.cast_mul, ENNReal.mul_inv (.inl hn0) (.inr hn10),
          mul_assoc (n : ℝ≥0∞)⁻¹, mul_comm (m : ℝ≥0∞), ← mul_assoc ((n - 1)! : ℝ≥0∞)⁻¹,
          ENNReal.inv_mul_cancel hn10 hn1top, one_mul, mul_comm, div_eq_mul_inv]
      have haut_eq := splittingSymbolAut_erase hx
      have hexp_eq := splittingSymbolExponent_erase hx
      have hc0 : (σ.count x : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.2 (Multiset.count_pos.2 hx).ne'
      have hctop : (σ.count x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hx10 : (x.1 : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hf_pos.ne'
      have haut_er0 : (splittingSymbolAut (σ.erase x) : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.2 (splittingSymbolAut_pos fun y hy ↦ (hpos_er y hy).1).ne'
      have hw_combine : (1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)))) *
            (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              q ^ splittingSymbolExponent (σ.erase x))) =
          (σ.count x : ℝ≥0∞) *
            (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ)) := by
        have hden : ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ) =
            (σ.count x : ℝ≥0∞) *
              (((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))) *
                ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x))) := by
          rw [← haut_eq, ← hexp_eq, pow_add]
          push_cast
          ring
        have hA0 : ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))) ≠ 0 :=
          mul_ne_zero hx10 (pow_ne_zero _ hq0)
        have hB0 : ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
            q ^ splittingSymbolExponent (σ.erase x)) ≠ 0 :=
          mul_ne_zero haut_er0 (pow_ne_zero _ hq0)
        rw [hden, one_div, one_div, one_div,
          ENNReal.mul_inv (.inl hc0) (.inr (mul_ne_zero hA0 hB0)),
          ← mul_assoc (σ.count x : ℝ≥0∞), ENNReal.mul_inv_cancel hc0 hctop, one_mul,
          ENNReal.mul_inv (.inl hA0) (.inr hB0)]
      have hrearr : (n ! : ℝ≥0∞)⁻¹ *
            (((n - 1).choose (m - 1) : ℝ≥0∞) *
              (((m ! : ℝ≥0∞) * (1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))))) *
                (((n - m)! : ℝ≥0∞) *
                  (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                    q ^ splittingSymbolExponent (σ.erase x)))))) =
          ((n ! : ℝ≥0∞)⁻¹ *
            (((n - 1).choose (m - 1) : ℝ≥0∞) * ((m ! : ℝ≥0∞) * ((n - m)! : ℝ≥0∞)))) *
            ((1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)))) *
              (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                q ^ splittingSymbolExponent (σ.erase x)))) := by
        ring
      rw [hrearr, hcomb, hw_combine, ← hxm]
      simp only [div_eq_mul_inv, one_mul]
      push_cast
      ring
    -- Sum over `m ∈ [1, n]`: `∑_m ∑_{x : x.1 * x.2 = m}` collapses to `∑_{x ∈ σ.toFinset}`,
    -- and `∑_x count(x) * x.1 * x.2 = n` cancels `(n : ℝ≥0∞)⁻¹`.
    rw [Finset.mul_sum, Finset.sum_congr rfl hfiber]
    simp_rw [← Finset.sum_mul]
    have hmaps : ∀ x ∈ σ.toFinset, x.1 * x.2 ∈ Finset.Icc 1 n := by
      intro x hx_fin
      have hx := Multiset.mem_toFinset.1 hx_fin
      have hpos : 1 ≤ x.1 * x.2 := Nat.mul_pos (hσ x hx).1 (hσ x hx).2
      have hle : x.1 * x.2 ≤ n :=
        hn ▸ Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y : ℕ × ℕ ↦ y.1 * y.2) hx)
      exact Finset.mem_Icc.2 ⟨hpos, hle⟩
    rw [Finset.sum_fiberwise_of_maps_to hmaps]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have hsum_deg : (∑ x ∈ σ.toFinset, ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞)) = (n : ℝ≥0∞) := by
      rw [← Nat.cast_sum]
      congr 1
      have hcount := Finset.sum_multiset_map_count σ (fun x ↦ x.1 * x.2)
      simpa only [smul_eq_mul] using hcount.symm.trans hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn_pos.ne'
    have hntop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [hsum_deg, ENNReal.mul_inv_cancel hn0 hntop, one_mul]

/-! ### Mass formula for a fixed ramification partition -/

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the labelled Galois sets of size `n` whose
splitting symbol has ramification partition `π` have mass `q ^ (-k)`. -/
theorem etaleMass_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : π.parts.card ≤ n - k) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  let SymType := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let Φ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → SymType :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol, fun _ hx ↦ ρ.1.pos_of_mem_splittingSymbol hx,
      ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩
  rw [← tsum_fiberwise _ Φ, ← ENNReal.tsum_mul_left]
  have hfib : ∀ σ : SymType,
      (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : Φ ⁻¹' {σ}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent =
      (1 / (splittingSymbolAut σ.1 : ℝ≥0∞)) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) := by
    intro σ
    let e_fib : Φ ⁻¹' {σ} ≃ {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
      { toFun := fun ρ ↦ ⟨ρ.1.1,
          congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 ρ.2))⟩
        invFun := fun ρ ↦
          ⟨⟨ρ.1, by rw [ρ.2]; exact σ.2.2.2⟩,
            Set.mem_preimage.2 (Set.mem_singleton_iff.2 (Subtype.ext ρ.2))⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e_fib.symm.tsum_eq]
    have heq : (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (e_fib.symm ρ).1.1.discriminantExponent =
        1 / ((splittingSymbolAut σ.1 : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ.1) :=
      etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1
    have hexp : splittingSymbolExponent σ.1 = k := by
      rw [splittingSymbolExponent_def, ← sum_ramificationPartition, σ.2.2.2, π.parts_sum]
    have haut0 : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.2 (splittingSymbolAut_pos fun x hx ↦ (σ.2.1 x hx).1).ne'
    have hq0 : ((Nat.card 𝓀[K] : ℝ≥0∞) ^ k) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne _))
    rw [heq, hexp, one_div, one_div, one_div, ENNReal.mul_inv (.inl haut0) (.inr hq0)]
  rw [tsum_congr hfib, ENNReal.tsum_mul_right,
    tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

/-! ### Bhargava's mass formula -/

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Theorem 1.1, Prop. 2.3, and §8]): for every `n`,
`M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q` is the residue cardinality of `K` and
`q(k, m)` is the number of partitions of `k` into at most `m` parts. For `n ≥ 1` the `k = n` term
vanishes (`q(n, 0) = 0`), matching Bhargava's `∑_{k < n}`, while for `n = 0` both sides equal
`1`. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π => π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  classical
  -- Map each `ρ : GaloisSet K n` to `(k, π)` where `π = ramificationPartition ρ.splittingSymbol`
  -- is a partition of `k ≤ n` into at most `n - k` parts.
  let PartIdx := Σ k : Fin (n + 1), {π : (k : ℕ).Partition // π.parts.card ≤ n - (k : ℕ)}
  let Ψ : GaloisSet K n → PartIdx := fun ρ ↦
    let σ := ρ.splittingSymbol
    let k := (ramificationPartition σ).sum
    have hdeg := (sum_map_mul_eq_sum_ramificationPartition_add σ
      fun x hx ↦ (ρ.pos_of_mem_splittingSymbol hx).2).symm.trans ρ.sum_map_mul_splittingSymbol
    ⟨⟨k, by omega⟩,
      ⟨{ parts := ramificationPartition σ
         parts_pos := fun {a} ha ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ha).1
         parts_sum := rfl },
       by dsimp only; omega⟩⟩
  rw [etaleMass_def, ← tsum_fiberwise _ Ψ, ← ENNReal.tsum_mul_left, tsum_fintype,
    Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hfib : ∀ π : {π : (k : ℕ).Partition // π.parts.card ≤ n - (k : ℕ)},
      (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : Ψ ⁻¹' {⟨k, π⟩}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (k : ℕ) := by
    intro π
    let e_fib : Ψ ⁻¹' {⟨k, π⟩} ≃
        {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.1.parts} :=
      { toFun := fun ρ ↦ ⟨ρ.1,
          congrArg (fun p : PartIdx ↦ p.2.1.parts)
            (Set.mem_singleton_iff.1 (Set.mem_preimage.1 ρ.2))⟩
        invFun := fun ρ ↦ ⟨ρ.1, Set.mem_preimage.2 <| Set.mem_singleton_iff.2 <| by
          have hsum : (ramificationPartition ρ.1.splittingSymbol).sum = (k : ℕ) := by
            rw [ρ.2, π.1.parts_sum]
          have hsigma : ∀ {p₁ p₂ : PartIdx}, p₁.1 = p₂.1 → p₁.2.1.parts = p₂.2.1.parts →
              p₁ = p₂ := by
            rintro ⟨k₁, π₁⟩ ⟨k₂, π₂⟩ hk hparts
            dsimp only at hk hparts
            subst hk
            exact congrArg (Sigma.mk k₁) (Subtype.ext (Nat.Partition.ext hparts))
          exact hsigma (Fin.ext hsum) ρ.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e_fib.symm.tsum_eq]
    exact etaleMass_ramificationPartition n (k : ℕ) π.1 π.2
  rw [Finset.sum_congr rfl fun π _ ↦ hfib π, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_subtype, mul_one_div]

variable (K) in
/-- **Bhargava's mass formula for étale algebras** ([Bhargava 2007, Theorem 1.1 and §8]): for a
family `A` of étale `K`-algebras of degree `n` containing exactly one member of each
`K`-isomorphism class of étale algebras of degree `n`,
`∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π => π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

end TauCeti
