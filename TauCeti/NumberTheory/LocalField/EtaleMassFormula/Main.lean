/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleAlgebra
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.Transitive
import Mathlib.Data.Nat.Choose.Basic

/-!
# Bhargava's mass formulas for étale algebras over a local field

For a nonarchimedean local field `K` with residue field of cardinality `q`, this file proves
Bhargava's mass formulas for labelled Galois sets and étale `K`-algebras of degree `n`
[Bhargava 2007, Theorem 1.1, Propositions 2.1–2.3, and §8]:

* **By splitting symbol** (`TauCeti.etaleMass_splittingSymbol`): for a splitting symbol `σ` of
  degree `n` whose entries `(f, e)` have positive components, the Galois sets of size `n` with
  splitting symbol `σ` have mass `1 / (#Aut(σ) · q ^ (∑ f (e - 1)))`.
* **By ramification partition** (`TauCeti.etaleMass_ramificationPartition`): for a partition `π` of
  `k` into at most `n - k` parts, the Galois sets of size `n` whose splitting symbol has
  ramification partition `π` have mass `q ^ (-k)`.
* **Total mass** (`TauCeti.etaleMass_eq`, `TauCeti.etaleMass_eq_of_pos`, `TauCeti.etaleMass_ne_top`,
  `TauCeti.etaleMass_two`): `M_n(K) = ∑_{k=0}^n q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the
  number of partitions of `k` into at most `m` parts; in particular `M_n(K)` is always finite and
  `M_2(K) = 1 + 1 / q`, while for `n ≥ 1` the `k = n` summand vanishes, giving the sum over `k < n`.
* **Étale algebras** (`TauCeti.tsum_etaleDiscriminantExponent_eq`): for any family `A` of étale
  `K`-algebras of degree `n` containing one representative of each `K`-isomorphism class,
  `∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k=0}^n q(k, n - k) · q ^ (-k)`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1, §2, and §8.
* K. S. Kedlaya, *Mass formulas for local Galois representations*, IMRN **2007**, rnm021.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal NNReal Nat

namespace TauCeti

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Mass formula for a fixed splitting symbol -/

section SplittingSymbol

private theorem ite_add_splittingSymbol_eq_sum {m b : ℕ} (hm : 0 < m)
    (ρ₁ : GaloisSet K m) (hρ₁ : ρ₁.IsTransitive) (ρ₂ : GaloisSet K b)
    (σ : Multiset (ℕ × ℕ)) (W₁ W₂ : ℝ≥0∞) :
    (if ρ₁.splittingSymbol + ρ₂.splittingSymbol = σ then W₁ * W₂ else 0) =
      ∑ x ∈ σ.toFinset,
        if x.1 * x.2 = m then
          (if ρ₁.splittingSymbol = {x} then W₁ else 0) *
            (if ρ₂.splittingSymbol = σ.erase x then W₂ else 0)
        else 0 := by
  classical
  have hsym := ρ₁.splittingSymbol_of_isTransitive hρ₁ ⟨0, hm⟩
  set y : ℕ × ℕ :=
    letI := ρ₁.mulAction
    let F := IntermediateField.fixedField
      (MulAction.stabilizer Gal(SeparableClosure K/K) (⟨0, hm⟩ : Fin m))
    (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)
  have hy_deg : y.1 * y.2 = m := by
    have hdeg := ρ₁.sum_map_mul_splittingSymbol
    simpa [hsym] using hdeg
  by_cases h : ρ₁.splittingSymbol + ρ₂.splittingSymbol = σ
  · have hcons : y ::ₘ ρ₂.splittingSymbol = σ := by simpa [hsym] using h
    have hy_mem : y ∈ σ.toFinset := Multiset.mem_toFinset.2 (hcons ▸ Multiset.mem_cons_self y _)
    have hy_er : ρ₂.splittingSymbol = σ.erase y := by
      rw [← hcons, Multiset.erase_cons_head]
    simp only [h, ↓reduceIte]
    rw [Finset.sum_eq_single y]
    · simp [hy_deg, hsym, hy_er]
    · intro x _ hxy
      simp [hsym, hxy.symm]
    · intro hy_not
      exact (hy_not hy_mem).elim
  · simp only [h, ↓reduceIte]
    refine (Finset.sum_eq_zero fun x hx ↦ ?_).symm
    by_cases hxm : x.1 * x.2 = m
    · simp only [hxm, ↓reduceIte]
      by_cases hx₁ : ρ₁.splittingSymbol = {x}
      · have hx₂ : ρ₂.splittingSymbol ≠ σ.erase x := fun h₂ ↦ h <| by
          rw [hx₁, h₂, Multiset.singleton_add, Multiset.cons_erase (Multiset.mem_toFinset.1 hx)]
        simp [hx₂]
      · simp [hx₁]
    · simp [hxm]

private theorem tsum_galoisSet_subtype {m : ℕ} (P : GaloisSet K m → Prop) [DecidablePred P] :
    ∑' ρ : {ρ : GaloisSet K m // P ρ},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ∑' ρ : GaloisSet K m,
        if P ρ then 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent else 0 := by
  let S : Set (GaloisSet K m) := {ρ | P ρ}
  let E : {ρ : GaloisSet K m // P ρ} ≃ S :=
    ⟨fun ρ ↦ ⟨ρ.1, ρ.2⟩, fun ρ ↦ ⟨ρ.1, ρ.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  have hE : ∑' ρ : {ρ : GaloisSet K m // P ρ},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      ∑' ρ : S, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent :=
    E.tsum_eq fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent
  rw [hE, tsum_subtype S fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent]
  exact tsum_congr fun ρ ↦ by
    by_cases h : P ρ
    · have hm : ρ ∈ S := h
      simp [Set.indicator_of_mem hm, h]
    · have hm : ρ ∉ S := h
      simp [Set.indicator_of_notMem hm, h]

private theorem tsum_orbit_slice_splittingSymbol {n : ℕ} (i₀ : Fin n) (m : Finset.Icc 1 n)
    (σ : Multiset (ℕ × ℕ)) :
    ∑' (S : (Finset.univ.powersetCard m.1).filter (i₀ ∈ ·))
        (ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive}) (ρ₂ : GaloisSet K (n - m.1)),
        (if ((GaloisSet.orbitDecompositionEquiv (K := K) i₀).symm ⟨m, S, ρ₁, ρ₂⟩).splittingSymbol =
            σ then
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
            ((GaloisSet.orbitDecompositionEquiv (K := K) i₀).symm
              ⟨m, S, ρ₁, ρ₂⟩).discriminantExponent
        else 0) =
      (Nat.choose (n - 1) (m.1 - 1) : ℝ≥0∞) *
        ∑ x ∈ σ.toFinset,
          if x.1 * x.2 = m.1 then
            (∑' ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.splittingSymbol = {x}},
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
            (∑' ρ₂ : {ρ₂ : GaloisSet K (n - m.1) // ρ₂.splittingSymbol = σ.erase x},
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent)
          else 0 := by
  classical
  have hm1 : 1 ≤ m.1 := (Finset.mem_Icc.1 m.2).1
  have hpow (a b : ℕ) :
      (1 : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (a + b) =
        (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ a) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ b) := by
    rw [one_div, one_div, one_div, pow_add,
      ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
        (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
  have hS_card : ((Finset.univ.powersetCard m.1).filter (i₀ ∈ ·)).card =
      Nat.choose (n - 1) (m.1 - 1) := by
    have hfilt : (Finset.univ.powersetCard m.1).filter (i₀ ∈ ·) =
        (Finset.univ.powersetCard m.1).filter ({i₀} ⊆ ·) :=
      Finset.filter_congr fun _ _ ↦ Finset.singleton_subset_iff.symm
    rw [hfilt, Finset.card_filter_powersetCard_subset {i₀} Finset.univ m.1
      (Finset.subset_univ _) (by simpa using hm1), Finset.card_univ, Fintype.card_fin,
      Finset.card_singleton]
  simp_rw [GaloisSet.orbitDecompositionEquiv_symm_apply, GaloisSet.splittingSymbol_ofSum,
    GaloisSet.discriminantExponent_ofSum, hpow]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hS_card, nsmul_eq_mul]
  congr 1
  simp_rw [ite_add_splittingSymbol_eq_sum hm1 _ (Subtype.prop _) _ σ]
  rw [tsum_congr fun _ ↦ Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable,
    Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hxm : x.1 * x.2 = m.1
  · simp only [hxm, ↓reduceIte]
    simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    congr 1
    · symm
      let E : {ρ₁ : GaloisSet K m.1 // ρ₁.splittingSymbol = {x}} ≃
          {ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive} | ρ₁.1.splittingSymbol = {x}} :=
        { toFun := fun ρ₁ ↦
            ⟨⟨ρ₁.1, (ρ₁.1.isTransitive_iff_card_splittingSymbol_eq_one hm1).2 (by simp [ρ₁.2])⟩,
              ρ₁.2⟩
          invFun := fun ρ₁ ↦ ⟨ρ₁.1.1, ρ₁.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
      have hE : ∑' ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.splittingSymbol = {x}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent =
          ∑' ρ₁ : {ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive} | ρ₁.1.splittingSymbol = {x}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.1.discriminantExponent :=
        E.tsum_eq fun ρ₁ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.1.discriminantExponent
      rw [hE, tsum_subtype
        {ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive} | ρ₁.1.splittingSymbol = {x}}
        fun ρ₁ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent]
      exact tsum_congr fun ρ₁ ↦ by
        by_cases h : ρ₁.1.splittingSymbol = {x} <;> simp [h]
    · exact (tsum_galoisSet_subtype (fun ρ₂ ↦ ρ₂.splittingSymbol = σ.erase x)).symm
  · simp [hxm]

private theorem splittingSymbol_coeff_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hσ : ∀ y ∈ σ, 0 < y.1 ∧ 0 < y.2) (hx : x ∈ σ) (hfe_le : x.1 * x.2 ≤ n) :
    (n ! : ℝ≥0∞)⁻¹ * (Nat.choose (n - 1) (x.1 * x.2 - 1) : ℝ≥0∞) * ((x.1 * x.2)! : ℝ≥0∞) *
        (x.1 : ℝ≥0∞)⁻¹ * ((n - x.1 * x.2)! : ℝ≥0∞) *
        (splittingSymbolAut (σ.erase x) : ℝ≥0∞)⁻¹ =
      ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
        (splittingSymbolAut σ : ℝ≥0∞)⁻¹ := by
  have ⟨hf, he⟩ := hσ x hx
  have hfe_pos : 0 < x.1 * x.2 := Nat.mul_pos hf he
  have hn_pos : 0 < n := hfe_pos.trans_le hfe_le
  have hAut_er : 0 < splittingSymbolAut (σ.erase x) :=
    splittingSymbolAut_pos fun y hy ↦ (hσ y (Multiset.mem_of_mem_erase hy)).1
  have hAut : 0 < splittingSymbolAut σ := splittingSymbolAut_pos fun y hy ↦ (hσ y hy).1
  -- Clear denominators in `ℕ` using `(n - 1).choose (k - 1) * k! * (n - k)! = k * (n - 1)!`.
  have hnat :
      Nat.choose (n - 1) (x.1 * x.2 - 1) * (x.1 * x.2)! * (n - x.1 * x.2)! *
          (n * splittingSymbolAut σ) =
        σ.count x * (x.1 * x.2) * (n ! * x.1 * splittingSymbolAut (σ.erase x)) := by
    have hchoose :
        Nat.choose (n - 1) (x.1 * x.2 - 1) * (x.1 * x.2)! * (n - x.1 * x.2)! =
          x.1 * x.2 * (n - 1)! := by
      have hsub : n - 1 - (x.1 * x.2 - 1) = n - x.1 * x.2 := by omega
      calc
        _ = x.1 * x.2 * (Nat.choose (n - 1) (x.1 * x.2 - 1) * (x.1 * x.2 - 1)! *
              ((n - 1) - (x.1 * x.2 - 1))!) := by
          rw [hsub, ← Nat.mul_factorial_pred hfe_pos.ne']
          ring
        _ = x.1 * x.2 * (n - 1)! := by
          rw [Nat.choose_mul_factorial_mul_factorial (by omega)]
    rw [hchoose, splittingSymbolAut_eq_mul_erase hx, (Nat.mul_factorial_pred hn_pos.ne').symm]
    ring
  -- Divide in `ℝ≥0` and cast to `ℝ≥0∞`.
  have hnnr :
      ((Nat.choose (n - 1) (x.1 * x.2 - 1) * (x.1 * x.2)! * (n - x.1 * x.2)! : ℕ) : ℝ≥0) /
          ((n ! * x.1 * splittingSymbolAut (σ.erase x) : ℕ) : ℝ≥0) =
        ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0) / ((n * splittingSymbolAut σ : ℕ) : ℝ≥0) := by
    rw [div_eq_div_iff
      (Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero n.factorial_ne_zero hf.ne')
        hAut_er.ne'))
      (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hn_pos.ne' hAut.ne'))]
    exact_mod_cast hnat
  have hcoe := congrArg ((↑) : ℝ≥0 → ℝ≥0∞) hnnr
  rw [ENNReal.coe_div
      (Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.mul_ne_zero n.factorial_ne_zero hf.ne')
        hAut_er.ne')),
    ENNReal.coe_div (Nat.cast_ne_zero.2 (Nat.mul_ne_zero hn_pos.ne' hAut.ne'))] at hcoe
  simp only [Nat.cast_mul, ENNReal.coe_mul, ENNReal.coe_natCast, div_eq_mul_inv] at hcoe
  rw [ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _))
      (.inl (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))),
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _))] at hcoe
  calc
    (n ! : ℝ≥0∞)⁻¹ * (Nat.choose (n - 1) (x.1 * x.2 - 1) : ℝ≥0∞) * ((x.1 * x.2)! : ℝ≥0∞) *
        (x.1 : ℝ≥0∞)⁻¹ * ((n - x.1 * x.2)! : ℝ≥0∞) *
        (splittingSymbolAut (σ.erase x) : ℝ≥0∞)⁻¹ =
      (Nat.choose (n - 1) (x.1 * x.2 - 1) : ℝ≥0∞) * ((x.1 * x.2)! : ℝ≥0∞) *
        ((n - x.1 * x.2)! : ℝ≥0∞) *
        ((n ! : ℝ≥0∞)⁻¹ * (x.1 : ℝ≥0∞)⁻¹ * (splittingSymbolAut (σ.erase x) : ℝ≥0∞)⁻¹) := by ring
    _ = ((σ.count x : ℝ≥0∞) * ((x.1 : ℝ≥0∞) * (x.2 : ℝ≥0∞))) *
        ((n : ℝ≥0∞)⁻¹ * (splittingSymbolAut σ : ℝ≥0∞)⁻¹) := hcoe
    _ = ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
        (splittingSymbolAut σ : ℝ≥0∞)⁻¹ := by
      simp only [Nat.cast_mul]
      ring

private theorem splittingSymbol_term_eq {n : ℕ} {σ : Multiset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hσ : ∀ y ∈ σ, 0 < y.1 ∧ 0 < y.2) (hx : x ∈ σ) (hfe_le : x.1 * x.2 ≤ n) (q : ℝ≥0∞)
    (hq : q ≠ ⊤) :
    (n ! : ℝ≥0∞)⁻¹ *
        ((Nat.choose (n - 1) (x.1 * x.2 - 1) : ℝ≥0∞) *
          ((((x.1 * x.2)! : ℝ≥0∞) * (1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1))))) *
            (((n - x.1 * x.2)! : ℝ≥0∞) *
              (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                q ^ splittingSymbolExponent (σ.erase x)))))) =
      ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) *
        ((n : ℝ≥0∞)⁻¹ *
          (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ))) := by
  rw [splittingSymbolExponent_eq_add_erase hx, pow_add, one_div, one_div, one_div,
    ENNReal.mul_inv (.inr (ENNReal.pow_ne_top hq)) (.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (.inr (ENNReal.pow_ne_top hq)) (.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (.inr (ENNReal.mul_ne_top (ENNReal.pow_ne_top hq) (ENNReal.pow_ne_top hq)))
      (.inl (ENNReal.natCast_ne_top _)),
    ENNReal.mul_inv (.inr (ENNReal.pow_ne_top hq)) (.inl (ENNReal.pow_ne_top hq))]
  calc
    (n ! : ℝ≥0∞)⁻¹ *
        ((Nat.choose (n - 1) (x.1 * x.2 - 1) : ℝ≥0∞) *
          ((((x.1 * x.2)! : ℝ≥0∞) * ((x.1 : ℝ≥0∞)⁻¹ * (q ^ (x.1 * (x.2 - 1)))⁻¹)) *
            (((n - x.1 * x.2)! : ℝ≥0∞) *
              ((splittingSymbolAut (σ.erase x) : ℝ≥0∞)⁻¹ *
                (q ^ splittingSymbolExponent (σ.erase x))⁻¹)))) =
      ((n ! : ℝ≥0∞)⁻¹ * (Nat.choose (n - 1) (x.1 * x.2 - 1) : ℝ≥0∞) * ((x.1 * x.2)! : ℝ≥0∞) *
          (x.1 : ℝ≥0∞)⁻¹ * ((n - x.1 * x.2)! : ℝ≥0∞) *
          (splittingSymbolAut (σ.erase x) : ℝ≥0∞)⁻¹) *
        ((q ^ (x.1 * (x.2 - 1)))⁻¹ * (q ^ splittingSymbolExponent (σ.erase x))⁻¹) := by ring
    _ = (((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ *
          (splittingSymbolAut σ : ℝ≥0∞)⁻¹) *
        ((q ^ (x.1 * (x.2 - 1)))⁻¹ * (q ^ splittingSymbolExponent (σ.erase x))⁻¹) := by
      rw [splittingSymbol_coeff_eq hσ hx hfe_le]
    _ = ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) *
        ((n : ℝ≥0∞)⁻¹ *
          ((splittingSymbolAut σ : ℝ≥0∞)⁻¹ *
            ((q ^ (x.1 * (x.2 - 1)))⁻¹ * (q ^ splittingSymbolExponent (σ.erase x))⁻¹))) := by ring

/-- **Mass formula for a fixed splitting symbol** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n` whose entries `(f, e)` have positive components, the labelled Galois sets
of size `n` with splitting symbol `σ` have mass `1 / (#Aut(σ) · q ^ (∑ f (e - 1)))`. -/
theorem etaleMass_splittingSymbol (n : ℕ) (σ : Multiset (ℕ × ℕ))
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x ↦ x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  classical
  set c := Multiset.card σ with hc_def
  clear_value c
  induction c generalizing n σ with
  | zero =>
    have hσ0 : σ = 0 := Multiset.card_eq_zero.1 hc_def.symm
    subst hσ0
    simp only [Multiset.map_zero, Multiset.sum_zero] at hn
    subst hn
    let ρ₀ : {ρ : GaloisSet K 0 // ρ.splittingSymbol = 0} := ⟨GaloisSet.trivial K 0, by simp⟩
    rw [tsum_eq_single ρ₀ fun ρ hρ ↦ (hρ (Subtype.ext (Subsingleton.elim _ _))).elim]
    simp [ρ₀]
  | succ c ih =>
    -- Peel off the orbit of `0 : Fin n` using `GaloisSet.orbitDecompositionEquiv`.
    obtain ⟨x₀, hx₀⟩ := (Multiset.card_pos_iff_exists_mem (s := σ)).1 (by omega)
    have hn_pos : 0 < n := (Nat.mul_pos (hσ x₀ hx₀).1 (hσ x₀ hx₀).2).trans_le
      (hn ▸ Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun x : ℕ × ℕ ↦ x.1 * x.2) hx₀))
    let i₀ : Fin n := ⟨0, hn_pos⟩
    rw [tsum_galoisSet_subtype (fun ρ ↦ ρ.splittingSymbol = σ),
      ← (GaloisSet.orbitDecompositionEquiv (K := K) i₀).symm.tsum_eq,
      tsum_sigma', tsum_fintype]
    have hslice : ∀ m ∈ (Finset.univ : Finset (Finset.Icc 1 n)),
        (∑' p : ((Finset.univ.powersetCard m.1).filter (i₀ ∈ ·)) ×
            {ρ₁ : GaloisSet K m.1 // ρ₁.IsTransitive} × GaloisSet K (n - m.1),
          if ((GaloisSet.orbitDecompositionEquiv (K := K) i₀).symm ⟨m, p⟩).splittingSymbol = σ then
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^
              ((GaloisSet.orbitDecompositionEquiv (K := K) i₀).symm ⟨m, p⟩).discriminantExponent
          else 0) =
        ∑ x ∈ σ.toFinset,
          (Nat.choose (n - 1) (m.1 - 1) : ℝ≥0∞) *
            (if x.1 * x.2 = m.1 then
              (∑' ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.splittingSymbol = {x}},
                1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
              (∑' ρ₂ : {ρ₂ : GaloisSet K (n - m.1) // ρ₂.splittingSymbol = σ.erase x},
                1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent)
            else 0) := fun m _ ↦ by
      rw [tsum_prod', tsum_congr fun _ ↦ tsum_prod',
        tsum_orbit_slice_splittingSymbol i₀ m σ, Finset.mul_sum]
    rw [Finset.sum_congr rfl hslice, Finset.sum_comm, Finset.mul_sum]
    set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
    -- For each distinct factor `x ∈ σ`, only `m = x.1 * x.2` contributes; apply the transitive
    -- mass formula to `ρ₁` and the induction hypothesis to `ρ₂`.
    have hterm : ∀ x ∈ σ.toFinset,
        (n ! : ℝ≥0∞)⁻¹ * ∑ m : Finset.Icc 1 n,
            (Nat.choose (n - 1) (m.1 - 1) : ℝ≥0∞) *
              (if x.1 * x.2 = m.1 then
                (∑' ρ₁ : {ρ₁ : GaloisSet K m.1 // ρ₁.splittingSymbol = {x}},
                  1 / q ^ ρ₁.1.discriminantExponent) *
                (∑' ρ₂ : {ρ₂ : GaloisSet K (n - m.1) // ρ₂.splittingSymbol = σ.erase x},
                  1 / q ^ ρ₂.1.discriminantExponent)
              else 0) =
          ((σ.count x * (x.1 * x.2) : ℕ) : ℝ≥0∞) *
            ((n : ℝ≥0∞)⁻¹ *
              (1 / ((splittingSymbolAut σ : ℝ≥0∞) * q ^ splittingSymbolExponent σ))) := by
      intro x hx_fin
      have hx : x ∈ σ := Multiset.mem_toFinset.1 hx_fin
      have ⟨hf, he⟩ := hσ x hx
      have hfe_le : x.1 * x.2 ≤ n :=
        hn ▸ Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y : ℕ × ℕ ↦ y.1 * y.2) hx)
      let m₀ : Finset.Icc 1 n := ⟨x.1 * x.2, Finset.mem_Icc.2 ⟨Nat.mul_pos hf he, hfe_le⟩⟩
      rw [Finset.sum_eq_single m₀
          (fun m _ hm ↦ by
            have hne : x.1 * x.2 ≠ m.1 := fun h ↦ hm (Subtype.ext h.symm)
            simp [hne])
          (fun hm₀ ↦ (hm₀ (Finset.mem_univ m₀)).elim)]
      simp only [m₀, ↓reduceIte]
      have h₁ : ∑' ρ₁ : {ρ₁ : GaloisSet K (x.1 * x.2) // ρ₁.splittingSymbol = {x}},
            1 / q ^ ρ₁.1.discriminantExponent =
          ((x.1 * x.2)! : ℝ≥0∞) * (1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)))) := by
        calc
          _ = (((x.1 * x.2)! : ℝ≥0∞) * ((x.1 * x.2)! : ℝ≥0∞)⁻¹) * _ := by
            rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 (x.1 * x.2).factorial_ne_zero)
              (ENNReal.natCast_ne_top _), one_mul]
          _ = ((x.1 * x.2)! : ℝ≥0∞) * (1 / ((x.1 : ℝ≥0∞) * q ^ (x.1 * (x.2 - 1)))) := by
            rw [mul_assoc, etaleMass_isTransitive_splittingSymbol x.1 x.2 hf he]
      have h₂ : ∑' ρ₂ : {ρ₂ : GaloisSet K (n - x.1 * x.2) // ρ₂.splittingSymbol = σ.erase x},
            1 / q ^ ρ₂.1.discriminantExponent =
          ((n - x.1 * x.2)! : ℝ≥0∞) *
            (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
              q ^ splittingSymbolExponent (σ.erase x))) := by
        have hc_er : c = Multiset.card (σ.erase x) := by
          rw [Multiset.card_erase_of_mem hx, ← hc_def, Nat.pred_succ]
        have hn_er : ((σ.erase x).map fun y ↦ y.1 * y.2).sum = n - x.1 * x.2 := by
          have hcons := hn
          rw [← Multiset.cons_erase hx, Multiset.map_cons, Multiset.sum_cons] at hcons
          omega
        have hih := ih (n - x.1 * x.2) (σ.erase x)
          (fun y hy ↦ hσ y (Multiset.mem_of_mem_erase hy)) hn_er hc_er
        calc
          _ = (((n - x.1 * x.2)! : ℝ≥0∞) * ((n - x.1 * x.2)! : ℝ≥0∞)⁻¹) * _ := by
            rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 (n - x.1 * x.2).factorial_ne_zero)
              (ENNReal.natCast_ne_top _), one_mul]
          _ = ((n - x.1 * x.2)! : ℝ≥0∞) *
              (1 / ((splittingSymbolAut (σ.erase x) : ℝ≥0∞) *
                q ^ splittingSymbolExponent (σ.erase x))) := by
            rw [mul_assoc, hih]
      rw [h₁, h₂]
      exact splittingSymbol_term_eq hσ hx hfe_le q (ENNReal.natCast_ne_top _)
    -- Sum `σ.count x * (x.1 * x.2)` over `x ∈ σ.toFinset` to cancel `n`.
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Nat.cast_sum]
    have hsum_n : ∑ x ∈ σ.toFinset, σ.count x * (x.1 * x.2) = n := by
      simpa only [smul_eq_mul, hn] using (Finset.sum_multiset_map_count σ fun x ↦ x.1 * x.2).symm
    rw [hsum_n, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hn_pos.ne') (ENNReal.natCast_ne_top _), one_mul]

end SplittingSymbol

/-! ### Mass formula for a fixed ramification partition -/

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the labelled Galois sets of size `n` whose
splitting symbol has ramification partition `π` have mass `q ^ (-k)`. -/
theorem etaleMass_ramificationPartition (n k : ℕ) (π : k.Partition)
    (hπ : Multiset.card π.parts ≤ n - k) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  set q : ℝ≥0∞ := (Nat.card 𝓀[K] : ℝ≥0∞)
  let Sym := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x ↦ x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let proj : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → Sym :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol, fun _ hx ↦ ρ.1.pos_of_mem_splittingSymbol hx,
      ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩
  rw [← (Equiv.sigmaFiberEquiv proj).tsum_eq, tsum_sigma', ← ENNReal.tsum_mul_left]
  have hfib : ∀ σ : Sym,
      (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : {ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} //
              proj ρ = σ},
            1 / q ^ (Equiv.sigmaFiberEquiv proj ⟨σ, ρ⟩).1.discriminantExponent =
        (1 / (splittingSymbolAut σ.1 : ℝ≥0∞)) * (1 / q ^ k) := by
    intro σ
    let E : {ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} //
          proj ρ = σ} ≃ {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
      { toFun := fun ρ ↦ ⟨ρ.1.1, congrArg Subtype.val ρ.2⟩
        invFun := fun ρ ↦ ⟨⟨ρ.1, ρ.2.symm ▸ σ.2.2.2⟩, Subtype.ext ρ.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hE : ∑' ρ : {ρ : {ρ : GaloisSet K n //
            ramificationPartition ρ.splittingSymbol = π.parts} // proj ρ = σ},
          1 / q ^ (Equiv.sigmaFiberEquiv proj ⟨σ, ρ⟩).1.discriminantExponent =
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1},
          1 / q ^ ρ.1.discriminantExponent :=
      E.tsum_eq fun ρ ↦ 1 / q ^ ρ.1.discriminantExponent
    have hexp : splittingSymbolExponent σ.1 = k := by
      rw [splittingSymbolExponent_eq_sum_ramificationPartition, σ.2.2.2, π.parts_sum]
    rw [hE, etaleMass_splittingSymbol n σ.1 σ.2.1 σ.2.2.1, hexp, one_div, one_div, one_div,
      ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
        (.inl (ENNReal.natCast_ne_top _))]
  rw [tsum_congr hfib, ENNReal.tsum_mul_right,
    tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ, one_mul]

/-! ### Bhargava's mass formulas -/

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, and §8]): for every `n`, the
étale mass of `K` equals `∑_{k=0}^n q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of
partitions of `k` into at most `m` parts and `q` is the residue cardinality of `K`. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ Multiset.card π.parts ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  classical
  rw [etaleMass_def]
  have hpart : ∀ ρ : GaloisSet K n,
      (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent : ℝ≥0∞) =
        ∑ k ∈ Finset.range (n + 1),
          ∑ π ∈ (Finset.univ : Finset k.Partition).filter
              (fun π ↦ Multiset.card π.parts ≤ n - k),
            if ramificationPartition ρ.splittingSymbol = π.parts then
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent else 0 := by
    intro ρ
    have hdeg := (sum_map_mul_eq_sum_ramificationPartition_add ρ.splittingSymbol
      fun _ hx ↦ (ρ.pos_of_mem_splittingSymbol hx).2).symm.trans ρ.sum_map_mul_splittingSymbol
    let k₀ := (ramificationPartition ρ.splittingSymbol).sum
    let π₀ : k₀.Partition :=
      ⟨ramificationPartition ρ.splittingSymbol,
        fun ht ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ht).1, rfl⟩
    have hk₀ : k₀ ∈ Finset.range (n + 1) := Finset.mem_range.2 (by dsimp [k₀]; omega)
    have hπ₀ : π₀ ∈ (Finset.univ : Finset k₀.Partition).filter
        (fun π ↦ Multiset.card π.parts ≤ n - k₀) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, by dsimp [π₀, k₀]; omega⟩
    refine (Finset.sum_eq_single k₀ ?_ (fun h ↦ (h hk₀).elim) |>.trans ?_).symm
    · intro k _ hk_ne
      refine Finset.sum_eq_zero fun π _ ↦ ?_
      have hne : ramificationPartition ρ.splittingSymbol ≠ π.parts := fun h ↦
        hk_ne (π.parts_sum.symm.trans (congrArg Multiset.sum h.symm))
      simp [hne]
    · rw [Finset.sum_eq_single π₀
        (fun π _ hne ↦ by
          have hp : ramificationPartition ρ.splittingSymbol ≠ π.parts :=
            fun h ↦ hne (Nat.Partition.ext h.symm)
          simp [hp])
        (fun h ↦ (h hπ₀).elim)]
      simp [π₀]
  rw [tsum_congr hpart, Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable, Finset.mul_sum]
  have hπ_sum : ∀ π ∈ (Finset.univ : Finset k.Partition).filter
        (fun π ↦ Multiset.card π.parts ≤ n - k),
      (n ! : ℝ≥0∞)⁻¹ * ∑' ρ : GaloisSet K n,
          (if ramificationPartition ρ.splittingSymbol = π.parts then
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent else 0) =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := fun π hπ ↦ by
    rw [← tsum_galoisSet_subtype (fun ρ ↦ ramificationPartition ρ.splittingSymbol = π.parts),
      etaleMass_ramificationPartition n k π (Finset.mem_filter.1 hπ).2]
  rw [Finset.sum_congr rfl hπ_sum, Finset.sum_const, nsmul_eq_mul, mul_one_div]

variable (K) in
/-- For `n ≥ 1`, the `k = n` summand in `TauCeti.etaleMass_eq` vanishes, giving Bhargava's sum over
`0 ≤ k < n` ([Bhargava 2007, Prop. 2.3]). -/
theorem etaleMass_eq_of_pos {n : ℕ} (hn : 0 < n) :
    etaleMass K n =
      ∑ k ∈ Finset.range n,
        (((Finset.univ : Finset k.Partition).filter fun π ↦ Multiset.card π.parts ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  have hemp : ((Finset.univ : Finset n.Partition).filter
      fun π ↦ Multiset.card π.parts ≤ n - n) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro π _ hle
    have h0 : π.parts = 0 := Multiset.card_eq_zero.1 (by omega)
    have hsum := π.parts_sum
    rw [h0, Multiset.sum_zero] at hsum
    omega
  rw [etaleMass_eq, Finset.sum_range_succ, hemp]
  simp

variable (K) in
/-- For every `n`, the étale mass `etaleMass K n` is finite (even in equal characteristic `p > 0`,
where infinitely many Galois sets of size `n ≥ p` exist). -/
theorem etaleMass_ne_top (n : ℕ) : etaleMass K n ≠ ⊤ := by
  rw [etaleMass_eq]
  exact ENNReal.sum_ne_top.2 fun k _ ↦ ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (pow_ne_zero k (Nat.cast_ne_zero.2 Nat.card_pos.ne'))

variable (K) in
/-- **Bhargava's mass formula for étale algebras** ([Bhargava 2007, Thm. 1.1 and §8]): for a family
`A` of étale `K`-algebras of degree `n` containing one representative of each `K`-isomorphism
class, `∑ 1 / (#Aut_K(A i) · q ^ d(A i)) = ∑_{k=0}^n q(k, n - k) · q ^ (-k)`. -/
theorem tsum_etaleDiscriminantExponent_eq (n : ℕ) {ι : Type*} (A : ι → Type u)
    [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, Algebra.Etale K (A i)]
    (hdeg : ∀ i, Module.finrank K (A i) = n)
    (hinj : ∀ i j, Nonempty (A i ≃ₐ[K] A j) → i = j)
    (hsurj : ∀ (B : Type u) [CommRing B] [Algebra K B] [Algebra.Etale K B],
      Module.finrank K B = n → ∃ i, Nonempty (B ≃ₐ[K] A i)) :
    ∑' i, 1 / ((Nat.card (A i ≃ₐ[K] A i) : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ etaleDiscriminantExponent K (A i)) =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π ↦ Multiset.card π.parts ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k :=
  (tsum_etaleDiscriminantExponent K n A hdeg hinj hsurj).trans (etaleMass_eq K n)

variable (K) in
/-- The étale mass of degree `2` over `K` is `1 + 1 / q`, where `q` is the residue cardinality of
`K`. -/
theorem etaleMass_two : etaleMass K 2 = 1 + 1 / (Nat.card 𝓀[K] : ℝ≥0∞) := by
  have h2 := (etaleMass_eq_of_pos K zero_lt_two).trans
    (Finset.sum_range_succ
      (fun k ↦ (((Finset.univ : Finset k.Partition).filter
        fun π ↦ Multiset.card π.parts ≤ 2 - k).card : ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) 1)
  rw [h2, Finset.sum_range_one]
  simp

end TauCeti
