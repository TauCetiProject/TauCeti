/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Mass
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol.Basic
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol.GaloisSet
import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SubfieldCount

/-!
# Mass formulas for prescribed splitting symbols and ramification partitions

Let `K` be a nonarchimedean local field whose residue field has `q` elements. This file proves the
three intermediate mass formulas of [Bhargava 2007, §2] for labelled Galois sets over `K`:

1. **The transitive mass** (`TauCeti.etaleMass_isTransitive_splittingSymbol`): for `f, e ≥ 1`, the
   labelled Galois sets of size `f * e` with splitting symbol `{(f, e)}` have mass
   `1 / (f · q ^ (f(e - 1)))`. Such Galois sets are transitive, and their stabilizers fix
   subextensions of degree `f * e` and residue degree `f`, so the transitive bridge
   `TauCeti.GaloisSet.tsum_isTransitive` and Serre's formula over `K_f`
   (`TauCeti.tsum_inertiaDegree_eq`) evaluate the sum.
2. **Fixed splitting type** (`TauCeti.etaleMass_splittingSymbol`, [Bhargava 2007, Prop. 2.1]): for
   a splitting symbol `σ` of degree `n` with positive residue degrees and ramification indices, the
   labelled Galois sets with splitting symbol `σ` have mass
   `1 / (#Aut(σ) · q ^ (∑ f_i(e_i - 1)))`. Peeling off the orbit of the base label `0` via
   `TauCeti.GaloisSet.orbitSumEquiv` expresses the sum recursively in terms of the transitive mass
   and `σ.erase x`.
3. **Fixed ramification partition** (`TauCeti.etaleMass_ramificationPartition`,
   [Bhargava 2007, Prop. 2.2]): for a partition `π` of `k` into at most `n - k` parts, the labelled
   Galois sets of size `n` whose splitting symbol has ramification partition `π` have mass
   `q ^ (-k)`, by summing `TauCeti.etaleMass_splittingSymbol` over `σ` and applying the automorphism
   identity `TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition`.

## Main results

* `TauCeti.etaleMass_isTransitive_splittingSymbol`: mass of transitive Galois sets of symbol
  `{(f, e)}`.
* `TauCeti.etaleMass_splittingSymbol`: mass of Galois sets of splitting symbol `σ`
  ([Bhargava 2007, Prop. 2.1]).
* `TauCeti.etaleMass_ramificationPartition`: mass of Galois sets with ramification partition `π`
  ([Bhargava 2007, Prop. 2.2]).

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Propositions 2.1 and 2.2, §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
* J.-P. Serre, *Une « formule de masse » pour les extensions totalement ramifiées de degré donné
  d'un corps local*, C. R. Acad. Sci. Paris Sér. A **286** (1978), 1031–1036.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal Nat

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### The transitive mass by residue degree -/

/-- Factorial-cleared form of `etaleMass_isTransitive_splittingSymbol`: the labelled Galois sets of
size `f * e` with splitting symbol `{(f, e)}` have total weight
`(f * e)! / (f · q ^ (f(e - 1)))`. -/
private theorem tsum_splittingSymbol_singleton (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ((f * e)! : ℝ≥0∞) /
        ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  classical
  have hfe : 0 < f * e := Nat.mul_pos hf he
  set i₀ : Fin (f * e) := ⟨0, hfe⟩
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  let g : IntermediateField K (SeparableClosure K) → ℝ≥0∞ :=
    fun L ↦ if L.inertiaDegree = f then 1 / q ^ L.discriminantExponent else 0
  let S₁ : Set {ρ : GaloisSet K (f * e) // ρ.IsTransitive} :=
    {ρ | (letI := ρ.1.mulAction;
      (IntermediateField.fixedField
        (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree) = f}
  let e₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}} ≃ S₁ :=
    (Equiv.subtypeEquivRight fun ρ ↦
      (ρ.splittingSymbol_eq_singleton_iff i₀ f e).trans
        (and_congr_right fun htrans ↦
          and_iff_right (ρ.finrank_fixedField_stabilizer_of_isTransitive htrans i₀))).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm
  have hsum₁ :
      ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / q ^ ρ.1.discriminantExponent =
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.IsTransitive},
          (letI := ρ.1.mulAction
          g (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) := by
    rw [← e₁.symm.tsum_eq]
    have hcongr : ∀ r : S₁, 1 / q ^ (e₁.symm r).1.discriminantExponent =
        1 / q ^ r.1.1.discriminantExponent := fun _ ↦ rfl
    rw [tsum_congr hcongr, _root_.tsum_subtype S₁ fun ρ ↦ 1 / q ^ ρ.1.discriminantExponent]
    refine tsum_congr fun ρ ↦ ?_
    by_cases hρ : ρ ∈ S₁
    · rw [Set.indicator_of_mem hρ, ρ.1.discriminantExponent_of_isTransitive ρ.2 i₀]
      have hρ' : (letI := ρ.1.mulAction;
          (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree) = f := hρ
      simp [g, hρ']
    · rw [Set.indicator_of_notMem hρ]
      have hρ' : (letI := ρ.1.mulAction;
          (IntermediateField.fixedField
            (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)).inertiaDegree) ≠ f := hρ
      simp [g, hρ']
  let S₂ : Set {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e} :=
    {L | L.1.inertiaDegree = f}
  let e₂ : S₂ ≃ {L : IntermediateField K (SeparableClosure K) //
      Module.finrank K L = f * e ∧ L.inertiaDegree = f} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun L : IntermediateField K (SeparableClosure K) ↦ Module.finrank K L = f * e)
      (fun L ↦ L.inertiaDegree = f)
  have hsum₂ :
      ∑' L : {L : IntermediateField K (SeparableClosure K) // Module.finrank K L = f * e}, g L.1 =
        (e : ℝ≥0∞) / q ^ (f * (e - 1)) := by
    have hind : (fun L : {L : IntermediateField K (SeparableClosure K) //
          Module.finrank K L = f * e} ↦ g L.1) =
        S₂.indicator fun L ↦ 1 / q ^ L.1.discriminantExponent := by
      ext L
      by_cases hL : L ∈ S₂
      · have hL' : L.1.inertiaDegree = f := hL
        simp [S₂, g, hL']
      · have hL' : L.1.inertiaDegree ≠ f := hL
        simp [S₂, g, hL']
    rw [hind, ← _root_.tsum_subtype S₂ fun L ↦ 1 / q ^ L.1.discriminantExponent,
      ← e₂.symm.tsum_eq]
    exact tsum_inertiaDegree_eq hf.ne' e
  rw [hsum₁, GaloisSet.tsum_isTransitive i₀ g, hsum₂]
  have hfac : (f * e)! = f * ((f * e - 1)! * e) := by
    rw [← Nat.mul_factorial_pred hfe.ne']
    ring
  have hf0 : (f : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  have hft : (f : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top f
  calc ((f * e - 1)! : ℝ≥0∞) * ((e : ℝ≥0∞) / q ^ (f * (e - 1)))
      = (((f : ℝ≥0∞) * (f : ℝ≥0∞)⁻¹) * (((f * e - 1)! : ℝ≥0∞) * (e : ℝ≥0∞))) *
          (q ^ (f * (e - 1)))⁻¹ := by
        rw [ENNReal.mul_inv_cancel hf0 hft, one_mul, div_eq_mul_inv]
        ring
    _ = ((f * e)! : ℝ≥0∞) / ((f : ℝ≥0∞) * q ^ (f * (e - 1))) := by
        rw [hfac, Nat.cast_mul, Nat.cast_mul, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl hf0) (Or.inl hft)]
        ring

/-- **The transitive mass by residue degree**: for `f, e ≥ 1`, the labelled Galois sets of size
`f * e` with splitting symbol `{(f, e)}` have mass `1 / (f · q ^ (f(e - 1)))`, where `q` is the
residue cardinality of `K`. -/
theorem etaleMass_isTransitive_splittingSymbol (f e : ℕ) (hf : 0 < f) (he : 0 < e) :
    ((f * e)! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1))) := by
  have hfac0 : ((f * e)! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfact : ((f * e)! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [tsum_splittingSymbol_singleton f e hf he, div_eq_mul_inv, ← mul_assoc,
    ENNReal.inv_mul_cancel hfac0 hfact, one_mul, one_div]

/-! ### Mass formula for a fixed splitting type -/

/-- Decompose the Galois sets of size `n` with splitting symbol `σ` in which a base label `i₀` has
orbit `s` (of size `m = x.1 * x.2`) and `(f, e)` pair `x ∈ σ` into pairs of a Galois set on `Fin m`
with symbol `{x}` and a Galois set on `Fin l` with symbol `σ.erase x`. -/
private def orbitSplittingSymbolEquiv {n m l : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx : x ∈ σ) {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)] (hi₀ : i₀ ∈ s)
    (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s}) :
    {ρ₁ : GaloisSet K m // ρ₁.splittingSymbol = {x}} ×
        {ρ₂ : GaloisSet K l // ρ₂.splittingSymbol = σ.erase x} ≃
      {ρ : GaloisSet K n //
        (letI := ρ.mulAction; MulAction.orbit Gal(SeparableClosure K/K) i₀ = s) ∧
          (letI := ρ.mulAction;
            (fun F : IntermediateField K (SeparableClosure K) ↦
              (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
              (IntermediateField.fixedField
                (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) = x ∧
          ρ.splittingSymbol = σ} := by
  let a₀ : Fin m := e₁.symm ⟨i₀, hi₀⟩
  let e : Fin m ⊕ Fin l ≃ Fin n := (Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))
  have ha₀ : e (Sum.inl a₀) = i₀ := by simp [e, a₀]
  -- Pair a transitive `ρ₁` and arbitrary `ρ₂` with `orbitSumEquiv`, then match the two predicates.
  have hpair : ∀ p : {ρ₁ : GaloisSet K m // ρ₁.IsTransitive} × GaloisSet K l,
      (p.1.1.splittingSymbol = {x} ∧ p.2.splittingSymbol = σ.erase x) ↔
        ((letI := (GaloisSet.orbitSumEquiv hi₀ e₁ e₂ p : GaloisSet K n).mulAction;
          (fun F : IntermediateField K (SeparableClosure K) ↦
            (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
            (IntermediateField.fixedField
              (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) = x ∧
          (GaloisSet.orbitSumEquiv hi₀ e₁ e₂ p : GaloisSet K n).splittingSymbol = σ) := by
    intro p
    rw [GaloisSet.coe_orbitSumEquiv_apply]
    have hstab :
        (letI := (GaloisSet.sum p.1.1 p.2 e).mulAction;
          MulAction.stabilizer Gal(SeparableClosure K/K) i₀) =
          (letI := p.1.1.mulAction;
            MulAction.stabilizer Gal(SeparableClosure K/K) a₀) := by
      rw [← ha₀]
      exact GaloisSet.stabilizer_sum_inl p.1.1 p.2 e a₀
    have hsym₁ := p.1.1.splittingSymbol_of_isTransitive p.1.2 a₀
    rw [← hstab] at hsym₁
    rw [GaloisSet.splittingSymbol_sum, hsym₁, Multiset.singleton_inj]
    constructor
    · rintro ⟨hpx, hp₂⟩
      rw [hpx, hp₂, Multiset.singleton_add, Multiset.cons_erase hx]
      exact ⟨rfl, rfl⟩
    · rintro ⟨hpx, hsum⟩
      refine ⟨hpx, ?_⟩
      rw [hpx, Multiset.singleton_add, ← Multiset.cons_erase hx, Multiset.cons_inj_right] at hsum
      exact hsum
  have htrans_iff : ∀ ρ₁ : GaloisSet K m,
      ρ₁.splittingSymbol = {x} ↔ ρ₁.IsTransitive ∧ ρ₁.splittingSymbol = {x} :=
    fun ρ₁ ↦ ⟨fun h ↦ ⟨((ρ₁.splittingSymbol_eq_singleton_iff a₀ x.1 x.2).1 h).1, h⟩, And.right⟩
  exact
    ((Equiv.prodCongr
        ((Equiv.subtypeEquivRight htrans_iff).trans
          (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
        (Equiv.refl _)).trans
      { toFun := fun q ↦ ⟨(q.1.1, q.2.1), q.1.2, q.2.2⟩
        invFun := fun q ↦ (⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }).trans
      ((Equiv.subtypeEquiv (GaloisSet.orbitSumEquiv hi₀ e₁ e₂) hpair).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _))

/-- The underlying Galois set of `orbitSplittingSymbolEquiv` is `GaloisSet.sum`. -/
private theorem coe_orbitSplittingSymbolEquiv_apply {n m l : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx : x ∈ σ) {i₀ : Fin n} {s : Set (Fin n)} [DecidablePred (· ∈ s)] (hi₀ : i₀ ∈ s)
    (e₁ : Fin m ≃ s) (e₂ : Fin l ≃ {j : Fin n // j ∉ s})
    (q : {ρ₁ : GaloisSet K m // ρ₁.splittingSymbol = {x}} ×
      {ρ₂ : GaloisSet K l // ρ₂.splittingSymbol = σ.erase x}) :
    (orbitSplittingSymbolEquiv hx hi₀ e₁ e₂ q : GaloisSet K n) =
      GaloisSet.sum q.1.1 q.2.1 ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ s))) := by
  simp [orbitSplittingSymbolEquiv]

/-- Factorial-cleared form of `etaleMass_splittingSymbol` for splitting symbols `σ` of degree `n`
with `Multiset.card σ = c`. -/
private theorem tsum_splittingSymbol_eq :
    ∀ (c n : ℕ) (σ : Multiset (ℕ × ℕ)), Multiset.card σ = c →
      (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) → (σ.map fun x ↦ x.1 * x.2).sum = n →
      ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
        (n ! : ℝ≥0∞) / ((splittingSymbolAut σ : ℝ≥0∞) *
          (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ)
  | 0, n, σ, hc, _, hn => by
    obtain rfl : σ = 0 := Multiset.card_eq_zero.1 hc
    simp only [Multiset.map_zero, Multiset.sum_zero] at hn
    subst hn
    have huniq : ∀ ρ : {ρ : GaloisSet K 0 // ρ.splittingSymbol = 0},
        ρ = ⟨GaloisSet.trivial K 0, by simp⟩ :=
      fun ρ ↦ Subtype.ext (Subsingleton.elim _ _)
    rw [tsum_eq_single ⟨GaloisSet.trivial K 0, by simp⟩ fun ρ hρ ↦ (hρ (huniq ρ)).elim]
    simp
  | c + 1, n, σ, hc, hσ, hn => by
    classical
    obtain ⟨x₀, hx₀⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card σ)
    have hn_pos : 0 < n := by
      have hx₀_pos : 0 < x₀.1 * x₀.2 := Nat.mul_pos (hσ x₀ hx₀).1 (hσ x₀ hx₀).2
      have hle : x₀.1 * x₀.2 ≤ (σ.map fun x ↦ x.1 * x.2).sum :=
        Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun x : ℕ × ℕ ↦ x.1 * x.2) hx₀)
      omega
    set i₀ : Fin n := ⟨0, hn_pos⟩
    set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
    have hq0 : q ≠ 0 := Nat.cast_ne_zero.mpr (Finite.card_pos (α := 𝓀[K])).ne'
    -- Classify `ρ` by the `(f, e)` pair `x` and punctured orbit `T` of `i₀`.
    let Idx := Σ x : σ.toFinset,
      (Finset.univ.erase i₀).powersetCard (x.1.1 * x.1.2 - 1)
    let Φ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ} → Idx := fun ρ ↦
      let pair : ℕ × ℕ :=
        letI := ρ.1.mulAction
        (fun F : IntermediateField K (SeparableClosure K) ↦
          (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
          (IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))
      have hpair : pair ∈ σ.toFinset :=
        Multiset.mem_toFinset.2 (ρ.2 ▸ ρ.1.mem_splittingSymbol_of_label i₀)
      let O : Finset (Fin n) :=
        letI := ρ.1.mulAction
        (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset
      have hi₀_O : i₀ ∈ O := by
        let := ρ.1.mulAction
        exact Set.mem_toFinset.2 (MulAction.mem_orbit_self i₀)
      have hO_card : O.card = pair.1 * pair.2 := by
        let := ρ.1.mulAction
        rw [Set.toFinset_card, ← Nat.card_eq_fintype_card,
          ← ρ.1.finrank_fixedField_stabilizer i₀]
        exact (Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)).symm
      ⟨⟨pair, hpair⟩, ⟨O.erase i₀, Finset.mem_powersetCard.2
        ⟨Finset.erase_subset_erase i₀ (Finset.subset_univ O), by
          rw [Finset.card_erase_of_mem hi₀_O, hO_card]⟩⟩⟩
    -- Compute the `tsum` over each fibre `Φ ⁻¹' {⟨x, T⟩}`.
    have hfib : ∀ (x : σ.toFinset)
        (T : (Finset.univ.erase i₀).powersetCard (x.1.1 * x.1.2 - 1)),
        ∑' r : Φ ⁻¹' {⟨x, T⟩}, 1 / q ^ r.1.1.discriminantExponent =
          ((x.1.1 * x.1.2)! : ℝ≥0∞) /
              ((x.1.1 : ℝ≥0∞) * q ^ (x.1.1 * (x.1.2 - 1))) *
            (((n - x.1.1 * x.1.2)! : ℝ≥0∞) /
              ((splittingSymbolAut (σ.erase x.1) : ℝ≥0∞) *
                q ^ splittingSymbolExponent (σ.erase x.1))) := by
      intro ⟨x, hx_fin⟩ ⟨T, hT⟩
      dsimp only at hT ⊢
      have hx : x ∈ σ := Multiset.mem_toFinset.1 hx_fin
      have hx1 : 0 < x.1 := (hσ x hx).1
      have hx2 : 0 < x.2 := (hσ x hx).2
      let m := x.1 * x.2
      have hm_pos : 0 < m := Nat.mul_pos hx1 hx2
      have hm_le : m ≤ n := by
        rw [← hn]
        exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y : ℕ × ℕ ↦ y.1 * y.2) hx)
      obtain ⟨hT_sub, hT_card⟩ := Finset.mem_powersetCard.1 hT
      have hi₀_notMem_T : i₀ ∉ T := fun h ↦ Finset.notMem_erase i₀ Finset.univ (hT_sub h)
      set S : Finset (Fin n) := insert i₀ T
      have hi₀_S : i₀ ∈ (S : Set (Fin n)) := Finset.mem_coe.2 (Finset.mem_insert_self i₀ T)
      have hS_card : S.card = m := by
        rw [Finset.card_insert_of_notMem hi₀_notMem_T, hT_card]
        omega
      have hSc_card : Fintype.card {j : Fin n // j ∉ (S : Set (Fin n))} = n - m := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin]
        simp [hS_card]
      let e₁ : Fin m ≃ (S : Set (Fin n)) :=
        (Fintype.equivFinOfCardEq (by simp [hS_card])).symm
      let e₂ : Fin (n - m) ≃ {j : Fin n // j ∉ (S : Set (Fin n))} :=
        (Fintype.equivFinOfCardEq hSc_card).symm
      -- Identify `Φ ⁻¹' {⟨⟨x, hx_fin⟩, ⟨T, hT⟩⟩}` with the target of `orbitSplittingSymbolEquiv`.
      let efib :
          {ρ : GaloisSet K n //
            (letI := ρ.mulAction;
              MulAction.orbit Gal(SeparableClosure K/K) i₀ = (S : Set (Fin n))) ∧
              (letI := ρ.mulAction;
                (fun F : IntermediateField K (SeparableClosure K) ↦
                  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
                  (IntermediateField.fixedField
                    (MulAction.stabilizer Gal(SeparableClosure K/K) i₀))) = x ∧
              ρ.splittingSymbol = σ} ≃
          Φ ⁻¹' {⟨⟨x, hx_fin⟩, ⟨T, hT⟩⟩} :=
        { toFun := fun ρ ↦ ⟨⟨ρ.1, ρ.2.2.2⟩, by
            rw [Set.mem_preimage, Set.mem_singleton_iff]
            let := ρ.1.mulAction
            have hO : (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset = S := by
              ext j
              simp [ρ.2.1]
            have hT' : (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset.erase i₀ = T := by
              rw [hO]
              exact Finset.erase_insert hi₀_notMem_T
            have hfst : (Φ ⟨ρ.1, ρ.2.2.2⟩).1 = ⟨x, hx_fin⟩ := Subtype.ext ρ.2.2.1
            have hsnd : (Φ ⟨ρ.1, ρ.2.2.2⟩).2.1 = T := hT'
            rcases hΦ : Φ ⟨ρ.1, ρ.2.2.2⟩ with ⟨x', T', hT'_mem⟩
            rw [hΦ] at hfst hsnd
            cases hfst
            cases hsnd
            rfl⟩
          invFun := fun r ↦ ⟨r.1.1, by
            let := r.1.1.mulAction
            have hΦ : Φ r.1 = ⟨⟨x, hx_fin⟩, ⟨T, hT⟩⟩ := r.2
            have hpair_eq :
                (fun F : IntermediateField K (SeparableClosure K) ↦
                  (F.inertiaDegree, Module.finrank K F / F.inertiaDegree))
                  (IntermediateField.fixedField
                    (MulAction.stabilizer Gal(SeparableClosure K/K) i₀)) = x :=
              congrArg (fun p : Idx ↦ p.1.1) hΦ
            have hT_eq :
                (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset.erase i₀ = T :=
              congrArg (fun p : Idx ↦ p.2.1) hΦ
            have hi₀_orb : i₀ ∈ (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset :=
              Set.mem_toFinset.2 (MulAction.mem_orbit_self i₀)
            have horb_fin : (MulAction.orbit Gal(SeparableClosure K/K) i₀).toFinset = S := by
              rw [← Finset.insert_erase hi₀_orb, hT_eq]
            have horb : MulAction.orbit Gal(SeparableClosure K/K) i₀ = (S : Set (Fin n)) := by
              rw [← horb_fin, Set.coe_toFinset]
            exact ⟨horb, hpair_eq, r.1.2⟩⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      let E := (orbitSplittingSymbolEquiv hx hi₀_S e₁ e₂).trans efib
      rw [← E.tsum_eq]
      have hw : ∀ p : {ρ₁ : GaloisSet K m // ρ₁.splittingSymbol = {x}} ×
            {ρ₂ : GaloisSet K (n - m) // ρ₂.splittingSymbol = σ.erase x},
          1 / q ^ (E p).1.1.discriminantExponent =
            (1 / q ^ p.1.1.discriminantExponent) * (1 / q ^ p.2.1.discriminantExponent) := by
        intro p
        have hE : (E p).1.1 = GaloisSet.sum p.1.1 p.2.1
            ((Equiv.sumCongr e₁ e₂).trans (Equiv.sumCompl (· ∈ (S : Set (Fin n))))) :=
          coe_orbitSplittingSymbolEquiv_apply hx hi₀_S e₁ e₂ p
        rw [hE, GaloisSet.discriminantExponent_sum, pow_add]
        simp only [one_div]
        exact ENNReal.mul_inv (Or.inl (pow_ne_zero _ hq0))
          (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
      rw [tsum_congr hw, _root_.tsum_prod']
      dsimp only
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right, tsum_splittingSymbol_singleton x.1 x.2 hx1 hx2,
        tsum_splittingSymbol_eq c (n - m) (σ.erase x)
          (by rw [Multiset.card_erase_of_mem hx, hc]; rfl)
          (fun y hy ↦ hσ y (Multiset.mem_of_mem_erase hy))
          (by
            have hcons : ((x ::ₘ σ.erase x).map fun y ↦ y.1 * y.2).sum = n := by
              rwa [Multiset.cons_erase hx]
            rw [Multiset.map_cons, Multiset.sum_cons] at hcons
            omega)]
    -- Sum `hfib` over `T` and `x`.
    rw [← tsum_fiberwise _ Φ, tsum_fintype, Fintype.sum_sigma]
    have hx_term : ∀ x : σ.toFinset,
        ∑ T : (Finset.univ.erase i₀).powersetCard (x.1.1 * x.1.2 - 1),
            ∑' r : Φ ⁻¹' {⟨x, T⟩}, 1 / q ^ r.1.1.discriminantExponent =
          (((n - 1)! * (σ.count x.1 * (x.1.1 * x.1.2)) : ℕ) : ℝ≥0∞) /
            ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ) := by
      rintro ⟨x, hx_fin⟩
      have hx : x ∈ σ := Multiset.mem_toFinset.1 hx_fin
      have hx1 : 0 < x.1 := (hσ x hx).1
      have hx2 : 0 < x.2 := (hσ x hx).2
      set m := x.1 * x.2
      have hm_pos : 0 < m := Nat.mul_pos hx1 hx2
      have hm_le : m ≤ n := by
        rw [← hn]
        exact Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y : ℕ × ℕ ↦ y.1 * y.2) hx)
      have hcard_T :
          Fintype.card ((Finset.univ.erase i₀).powersetCard (m - 1)) =
            (n - 1).choose (m - 1) := by
        rw [Fintype.card_coe, Finset.card_powersetCard,
          Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
      -- Constant inner sum over `T`.
      simp_rw [hfib ⟨x, hx_fin⟩]
      rw [Finset.sum_const, Finset.card_univ, hcard_T, nsmul_eq_mul]
      -- Combine numerators `(n - 1).choose (m - 1) * m! * (n - m)! = (n - 1)! * m`.
      have hnum : (n - 1).choose (m - 1) * m ! * (n - m)! = (n - 1)! * m := by
        have hsub : n - 1 - (m - 1) = n - m := by omega
        have hchoose := Nat.choose_mul_factorial_mul_factorial (by omega : m - 1 ≤ n - 1)
        rw [hsub] at hchoose
        have hm_fac : m ! = m * (m - 1)! := (Nat.mul_factorial_pred hm_pos.ne').symm
        calc (n - 1).choose (m - 1) * m ! * (n - m)!
            = ((n - 1).choose (m - 1) * (m - 1)! * (n - m)!) * m := by rw [hm_fac]; ring
          _ = (n - 1)! * m := by rw [hchoose]
      -- Combine denominators and multiply numerator & denominator by `σ.count x > 0`.
      have hcnt_pos : 0 < σ.count x := Multiset.count_pos.2 hx
      have hcnt0 : (σ.count x : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hcnt_pos.ne'
      have hcntt : (σ.count x : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hd1_0 : (x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.mpr hx1.ne') (pow_ne_zero _ hq0)
      have hd1_t : (x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)) ≠ ⊤ :=
        ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
          (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      have hden :
          (σ.count x : ℝ≥0∞) *
              (((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))) *
                ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x))) =
            (splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ := by
        rw [splittingSymbolAut_eq_mul_erase hx, splittingSymbolExponent_eq_add_erase hx,
          Nat.cast_mul, Nat.cast_mul, pow_add]
        ring
      calc ((n - 1).choose (m - 1) : ℝ≥0∞) *
            (((m ! : ℝ≥0∞) / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)))) *
              (((n - m)! : ℝ≥0∞) /
                ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x))))
          = (((n - 1).choose (m - 1) * m ! * (n - m)! : ℕ) : ℝ≥0∞) *
              (((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))) *
                ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x)))⁻¹ := by
            rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hd1_0) (Or.inl hd1_t),
              Nat.cast_mul, Nat.cast_mul]
            ring
        _ = ((((n - 1)! * m : ℕ) : ℝ≥0∞) * ((σ.count x : ℝ≥0∞) * (σ.count x : ℝ≥0∞)⁻¹)) *
              (((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))) *
                ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                  q ^ splittingSymbolExponent (σ.erase x)))⁻¹ := by
            rw [hnum, ENNReal.mul_inv_cancel hcnt0 hcntt, mul_one]
        _ = (((n - 1)! * (σ.count x * m) : ℕ) : ℝ≥0∞) *
              ((σ.count x : ℝ≥0∞) *
                (((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))) *
                  ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                    q ^ splittingSymbolExponent (σ.erase x))))⁻¹ := by
            rw [ENNReal.mul_inv (Or.inl hcnt0) (Or.inl hcntt)]
            push_cast [m]
            ring
        _ = (((n - 1)! * (σ.count x * m) : ℕ) : ℝ≥0∞) /
              ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ) := by
            rw [hden, ← div_eq_mul_inv]
    simp_rw [hx_term, div_eq_mul_inv]
    rw [← Finset.sum_mul,
      Finset.sum_coe_sort σ.toFinset (fun x ↦
        (((n - 1)! * (σ.count x * (x.1 * x.2)) : ℕ) : ℝ≥0∞)),
      ← Nat.cast_sum, ← Finset.mul_sum]
    have hsum_deg : ∑ x ∈ σ.toFinset, σ.count x * (x.1 * x.2) = n := by
      have h := Finset.sum_multiset_map_count σ (fun x ↦ x.1 * x.2)
      simpa only [smul_eq_mul, hn] using h.symm
    have hfac_n : (n - 1)! * n = n ! := by
      rw [mul_comm]
      exact Nat.mul_factorial_pred hn_pos.ne'
    rw [hsum_deg, hfac_n, ← div_eq_mul_inv]

/-- **Mass formula for a fixed splitting type** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n` whose factors `(f, e)` are positive, the labelled Galois sets with
splitting symbol `σ` have mass `1 / (#Aut(σ) · q ^ (∑ f_i(e_i - 1)))`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x ↦ x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  have hfac0 : (n ! : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hfact : (n ! : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [tsum_splittingSymbol_eq (Multiset.card σ) n σ rfl hσ hn, div_eq_mul_inv, ← mul_assoc,
    ENNReal.inv_mul_cancel hfac0 hfact, one_mul, one_div]

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
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  let Sym := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x ↦ x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let Ψ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → Sym :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol,
      ⟨fun x hx ↦ ρ.1.pos_of_mem_splittingSymbol hx, ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩⟩
  rw [← tsum_fiberwise _ Ψ, ← ENNReal.tsum_mul_left]
  have hσ_term : ∀ σ : Sym,
      (n ! : ℝ≥0∞)⁻¹ * ∑' r : Ψ ⁻¹' {σ}, 1 / q ^ r.1.1.discriminantExponent =
        (1 / (splittingSymbolAut σ.1 : ℝ≥0∞)) * (1 / q ^ k) := by
    intro σ
    let efib : Ψ ⁻¹' {σ} ≃ {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
      { toFun := fun r ↦ ⟨r.1.1, congrArg Subtype.val r.2⟩
        invFun := fun ρ ↦ ⟨⟨ρ.1, ρ.2.symm ▸ σ.2.2.2⟩, Subtype.ext ρ.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hcongr : ∀ r : Ψ ⁻¹' {σ},
        1 / q ^ r.1.1.discriminantExponent = 1 / q ^ (efib r).1.discriminantExponent :=
      fun _ ↦ rfl
    have hexp : splittingSymbolExponent σ.1 = k := by
      rw [← sum_ramificationPartition_eq_splittingSymbolExponent, σ.2.2.2, π.parts_sum]
    have haut0 : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr (splittingSymbolAut_pos fun x hx ↦ (σ.2.1 x hx).1).ne'
    have hautt : (splittingSymbolAut σ.1 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [tsum_congr hcongr, efib.tsum_eq fun ρ ↦ 1 / q ^ ρ.1.discriminantExponent,
      etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1, hexp]
    simp only [one_div]
    exact ENNReal.mul_inv (Or.inl haut0) (Or.inl hautt)
  simp_rw [hσ_term]
  rw [ENNReal.tsum_mul_right, tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ,
    one_mul]

end TauCeti
