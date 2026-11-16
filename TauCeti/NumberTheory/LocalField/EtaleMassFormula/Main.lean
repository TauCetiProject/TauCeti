/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.GaloisSplitting
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.SplittingSymbol

/-!
# Bhargava's mass formulas for étale algebras over local fields

This file proves Bhargava's mass formulas for étale algebras of degree `n` over a nonarchimedean
local field `K` with residue field cardinality `q`, in the labelled Galois-set formulation
`M_n(K) = (1 / n!) ∑_ρ q ^ (-d(ρ))` (`TauCeti.etaleMass`):

1. **Mass by splitting symbol** ([Bhargava 2007, Prop. 2.1], `TauCeti.etaleMass_splittingSymbol`):
   for every splitting symbol `σ` of degree `n` (a multiset of pairs `(f, e)` of positive integers
   with `∑ f e = n`),
   `(1 / n!) ∑_{ρ.splittingSymbol = σ} q ^ (-d(ρ)) = 1 / (#Aut(σ) · q ^ (∑ f (e - 1)))`.
2. **Mass by ramification partition** ([Bhargava 2007, Prop. 2.2],
   `TauCeti.etaleMass_ramificationPartition`): for every partition `π` of `k` into at most `n - k`
   parts,
   `(1 / n!) ∑_{ramificationPartition ρ.splittingSymbol = π.parts} q ^ (-d(ρ)) = q ^ (-k)`.
3. **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, §8], `TauCeti.etaleMass_eq`):
   `M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of partitions of `k`
   into at most `m` parts.

## Proof overview

The mass by splitting symbol is proved by induction on `σ`. The empty symbol `σ = 0` is trivial.
For `σ = (f, e) ::ₘ τ` with `m = f * e` and `n = ∑_{(f', e') ∈ τ} f' * e'`, we double-count the
weighted pairs `(ρ, A)` where `ρ` is a labelled Galois set of size `m + n` with splitting symbol
`(f, e) ::ₘ τ` and `A ⊆ Fin (m + n)` is an orbit of `ρ` of type `(f, e)`:

* Summing over `ρ` first, each `ρ` has `τ.count (f, e) + 1` orbits of type `(f, e)`.
* Summing over `A` first, every such orbit has cardinality `m`, so there are `(m + n).choose m`
  choices of `A`. Fixing an equivalence `Fin m ⊕ Fin n ≃ Fin (m + n)` identifying `Fin m` with `A`,
  `TauCeti.GaloisSet.sumEquiv` identifies the fiber at `A` with pairs `(ρ₁, ρ₂)` of splitting
  symbols `{(f, e)}` and `τ`, and `TauCeti.GaloisSet.discriminantExponent_ofSumEquiv` factors the
  weight.

Dividing by `(m + n)!` and applying `TauCeti.etaleMass_isTransitive_splittingSymbol` together with
the induction hypothesis yields the formula. Summing over splitting symbols with a fixed
ramification partition `π` uses `TauCeti.tsum_one_div_splittingSymbolAut_ramificationPartition` to
obtain `TauCeti.etaleMass_ramificationPartition`, and summing over all `k ≤ n` and partitions `π` of
`k` into at most `n - k` parts yields `TauCeti.etaleMass_eq`.

## Main results

* `TauCeti.etaleMass_splittingSymbol`: Bhargava's mass formula for a fixed splitting symbol.
* `TauCeti.etaleMass_ramificationPartition`: Bhargava's mass formula for a fixed ramification
  partition.
* `TauCeti.etaleMass_eq`: Bhargava's mass formula for étale algebras of degree `n`.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Thm. 1.1, Prop. 2.1–2.3, §8.
-/

public section

noncomputable section

open ValuativeRel
open scoped ENNReal Nat

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section SplittingSymbolMass

/-- `A` is an orbit of `ρ` whose point-stabilizer fixed fields have residue degree `f` and
ramification index `e`. -/
private def IsOrbitOfType {k : ℕ} (ρ : GaloisSet K k) (A : Finset (Fin k)) (f e : ℕ) : Prop :=
  letI := ρ.mulAction
  ∃ x : Fin k, (A : Set (Fin k)) = MulAction.orbit Gal(SeparableClosure K/K) x ∧
    let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) x)
    (F.inertiaDegree, Module.finrank K F / F.inertiaDegree) = (f, e)

/-- An orbit of type `(f, e)` has cardinality `f * e`. -/
private theorem card_eq_of_isOrbitOfType {k f e : ℕ} {ρ : GaloisSet K k} {A : Finset (Fin k)}
    (hA : IsOrbitOfType ρ A f e) : A.card = f * e := by
  let := ρ.mulAction
  obtain ⟨x, hx, hfe⟩ := hA
  have hcard : A.card = Nat.card (MulAction.orbit Gal(SeparableClosure K/K) x) := by
    rw [← hx, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard, ← ρ.finrank_fixedField_stabilizer x,
    ← Nat.mul_div_cancel' (IntermediateField.inertiaDegree_dvd_finrank _)]
  have hf := congrArg Prod.fst hfe
  have he := congrArg Prod.snd hfe
  dsimp only at hf he
  rw [he, hf]

/-- The number of orbits of `ρ` of type `(f, e)` equals the multiplicity of `(f, e)` in
`ρ.splittingSymbol`. -/
private theorem card_isOrbitOfType_eq_count {k f e : ℕ} (ρ : GaloisSet K k)
    [Fintype {A : Finset (Fin k) // IsOrbitOfType ρ A f e}] :
    Fintype.card {A : Finset (Fin k) // IsOrbitOfType ρ A f e} =
      ρ.splittingSymbol.count (f, e) := by
  classical
  let := ρ.mulAction
  have := Fintype.ofFinite (MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k))
  let pairFn : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k) → ℕ × ℕ :=
    fun O ↦
      let F := IntermediateField.fixedField (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)
      (F.inertiaDegree, Module.finrank K F / F.inertiaDegree)
  let toOrb : {O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k) //
      pairFn O = (f, e)} → {A : Finset (Fin k) // IsOrbitOfType ρ A f e} :=
    fun O ↦ ⟨(MulAction.orbit Gal(SeparableClosure K/K) O.1.out).toFinset,
      ⟨O.1.out, by simp, O.2⟩⟩
  have hbij : Function.Bijective toOrb := by
    refine ⟨?_, ?_⟩
    · intro O₁ O₂ h
      have hset : MulAction.orbit Gal(SeparableClosure K/K) O₁.1.out =
          MulAction.orbit Gal(SeparableClosure K/K) O₂.1.out := by
        have := congrArg (fun A : {A : Finset (Fin k) // IsOrbitOfType ρ A f e} ↦
          (A.1 : Set (Fin k))) h
        simpa [toOrb] using this
      obtain ⟨σ, hσ⟩ : O₁.1.out ∈ MulAction.orbit Gal(SeparableClosure K/K) O₂.1.out := by
        rw [← hset]
        exact MulAction.mem_orbit_self _
      have hq : (Quotient.mk'' (σ • O₂.1.out) :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k)) =
          Quotient.mk'' O₂.1.out :=
        Quotient.sound ⟨σ, rfl⟩
      dsimp only at hσ
      rw [hσ, Quotient.out_eq', Quotient.out_eq'] at hq
      exact Subtype.ext hq
    · rintro ⟨A, x, hx, hfe⟩
      let O : MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k) := Quotient.mk'' x
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_out_eq (rfl : (Quotient.mk'' x :
        MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k)) = O)
      have hO : pairFn O = (f, e) := by
        have hf := inertiaDegree_fixedField_stabilizer_out (K := K) (rfl : (Quotient.mk'' x :
          MulAction.orbitRel.Quotient Gal(SeparableClosure K/K) (Fin k)) = O)
        have hd : Module.finrank K (IntermediateField.fixedField
              (MulAction.stabilizer Gal(SeparableClosure K/K) O.out)) =
            Module.finrank K (IntermediateField.fixedField
              (MulAction.stabilizer Gal(SeparableClosure K/K) x)) := by
          rw [ρ.finrank_fixedField_stabilizer, ρ.finrank_fixedField_stabilizer,
            ← hσ, MulAction.orbit_smul]
        refine (Prod.ext hf ?_).trans hfe
        dsimp only [pairFn]
        rw [hf, hd]
      refine ⟨⟨O, hO⟩, Subtype.ext ?_⟩
      apply Finset.coe_injective
      rw [Set.coe_toFinset, hx]
      exact MulAction.orbit_eq_iff.2 ⟨σ⁻¹, by dsimp only; rw [← hσ, inv_smul_smul]⟩
  have hcnt : ∀ {α β : Type} [Fintype α] [DecidableEq β] (g : α → β) (b : β)
      [DecidablePred fun a ↦ g a = b],
      Fintype.card {a : α // g a = b} = ((Finset.univ : Finset α).val.map g).count b := by
    intro α β _ _ g b _
    rw [Fintype.card_subtype, Multiset.count_map, ← Finset.filter_val, Finset.card_val]
    exact congrArg Finset.card (Finset.filter_congr fun _ _ ↦ eq_comm)
  rw [Fintype.card_eq_nat_card, ← Nat.card_congr (Equiv.ofBijective toOrb hbij),
    ← Fintype.card_eq_nat_card, ρ.splittingSymbol_eq_map Quotient.out (fun O ↦ Quotient.out_eq' O)]
  exact hcnt pairFn (f, e)

/-- Given an equivalence `eA : Fin (f * e) ⊕ Fin n ≃ Fin (f * e + n)` identifying the left summand
with `A`, the labelled Galois sets of size `f * e + n` with splitting symbol `(f, e) ::ₘ τ` having
`A` as an orbit of type `(f, e)` are in bijection with pairs of labelled Galois sets of splitting
symbols `{(f, e)}` and `τ`. -/
private def sumSplittingSymbolEquiv {f e n : ℕ} (hf : 0 < f) (he : 0 < e) (τ : Multiset (ℕ × ℕ))
    (A : Finset (Fin (f * e + n))) (eA : Fin (f * e) ⊕ Fin n ≃ Fin (f * e + n))
    (hrange : Set.range (eA ∘ Sum.inl) = (A : Set (Fin (f * e + n)))) :
    {ρ₁ : GaloisSet K (f * e) // ρ₁.splittingSymbol = {(f, e)}} ×
        {ρ₂ : GaloisSet K n // ρ₂.splittingSymbol = τ} ≃
      {ρ : GaloisSet K (f * e + n) //
        ρ.splittingSymbol = (f, e) ::ₘ τ ∧ IsOrbitOfType ρ A f e} where
  toFun p :=
    ⟨GaloisSet.ofSumEquiv eA p.1.1 p.2.1, by
      refine ⟨?_, ?_⟩
      · rw [GaloisSet.splittingSymbol_ofSumEquiv, p.1.2, p.2.2, Multiset.singleton_add]
      · let i₀ : Fin (f * e) := ⟨0, Nat.mul_pos hf he⟩
        obtain ⟨hρ₁, hdeg⟩ := (p.1.1.splittingSymbol_eq_singleton_iff i₀).1 p.1.2
        refine ⟨eA (.inl i₀), ?_, ?_⟩
        · rw [GaloisSet.orbit_ofSumEquiv_inl]
          let := p.1.1.mulAction
          have : MulAction.IsPretransitive Gal(SeparableClosure K/K) (Fin (f * e)) :=
            p.1.1.isTransitive_def.1 hρ₁
          rw [MulAction.orbit_eq_univ, Set.image_univ, hrange]
        · dsimp only
          rw [GaloisSet.stabilizer_ofSumEquiv_inl]
          have hfin := p.1.1.finrank_fixedField_stabilizer_of_isTransitive hρ₁ i₀
          exact Prod.ext hdeg (by rw [hdeg, hfin, Nat.mul_div_right e hf])⟩
  invFun ρ :=
    have hinv : ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin (f * e + n)),
        x ∈ Set.range (eA ∘ Sum.inl) → ρ.1.val σ x ∈ Set.range (eA ∘ Sum.inl) := by
      obtain ⟨x₀, hx₀, _⟩ := ρ.2.2
      intro σ x hx
      rw [hrange, hx₀] at hx ⊢
      let := ρ.1.mulAction
      obtain ⟨τ₀, rfl⟩ := hx
      exact ⟨σ * τ₀, mul_smul σ τ₀ x₀⟩
    let p := (GaloisSet.sumEquiv eA).symm ⟨ρ.1, hinv⟩
    have hp : GaloisSet.ofSumEquiv eA p.1 p.2 = ρ.1 :=
      (GaloisSet.coe_sumEquiv_apply eA p).symm.trans
        (congrArg Subtype.val ((GaloisSet.sumEquiv eA).apply_symm_apply ⟨ρ.1, hinv⟩))
    have hp₁ : p.1.splittingSymbol = {(f, e)} := by
      obtain ⟨x₀, hx₀, hfe⟩ := ρ.2.2
      have htr : p.1.IsTransitive :=
        (GaloisSet.exists_orbit_ofSumEquiv_eq_range_inl_iff eA p.1 p.2 (Nat.mul_pos hf he)).1
          ⟨x₀, by rw [hp, hrange, hx₀]⟩
      have hx₀_mem : x₀ ∈ Set.range (eA ∘ Sum.inl) := by
        rw [hrange, hx₀]
        let := ρ.1.mulAction
        exact MulAction.mem_orbit_self x₀
      obtain ⟨i₀, hi₀⟩ := hx₀_mem
      dsimp only [Function.comp_apply] at hi₀
      rw [p.1.splittingSymbol_eq_singleton_iff i₀]
      refine ⟨htr, ?_⟩
      have hstab := GaloisSet.stabilizer_ofSumEquiv_inl eA p.1 p.2 i₀
      rw [hp, hi₀] at hstab
      have hf' := congrArg Prod.fst hfe
      dsimp only at hf'
      rw [← hstab, hf']
    have hp₂ : p.2.splittingSymbol = τ := by
      have hsum : p.1.splittingSymbol + p.2.splittingSymbol = (f, e) ::ₘ τ := by
        rw [← GaloisSet.splittingSymbol_ofSumEquiv eA, hp, ρ.2.1]
      rw [hp₁, Multiset.singleton_add] at hsum
      exact (Multiset.cons_inj_right (f, e)).1 hsum
    (⟨p.1, hp₁⟩, ⟨p.2, hp₂⟩)
  left_inv p := by
    have h : ∀ hinv,
        (⟨GaloisSet.ofSumEquiv eA p.1.1 p.2.1, hinv⟩ :
          {ρ : GaloisSet K (f * e + n) //
            ∀ (σ : Gal(SeparableClosure K/K)) (x : Fin (f * e + n)),
              x ∈ Set.range (eA ∘ Sum.inl) → ρ.val σ x ∈ Set.range (eA ∘ Sum.inl)}) =
          GaloisSet.sumEquiv eA (p.1.1, p.2.1) :=
      fun _ ↦ Subtype.ext (GaloisSet.coe_sumEquiv_apply eA (p.1.1, p.2.1)).symm
    dsimp only
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · dsimp only
      rw [h, (GaloisSet.sumEquiv eA).symm_apply_apply]
    · dsimp only
      rw [h, (GaloisSet.sumEquiv eA).symm_apply_apply]
  right_inv ρ :=
    Subtype.ext <| (GaloisSet.coe_sumEquiv_apply eA _).symm.trans
      (congrArg Subtype.val ((GaloisSet.sumEquiv eA).apply_symm_apply ⟨ρ.1, _⟩))

/-- For any fixed `(f * e)`-element subset `A ⊆ Fin (f * e + n)`, the weighted sum over labelled
Galois sets of splitting symbol `(f, e) ::ₘ τ` having `A` as an orbit of type `(f, e)` factors into
the product of the weighted sums for `{(f, e)}` and `τ`. -/
private theorem tsum_isOrbitOfType_eq_mul {f e n : ℕ} (hf : 0 < f) (he : 0 < e)
    (τ : Multiset (ℕ × ℕ)) (A : Finset (Fin (f * e + n))) (hA : A.card = f * e) :
    ∑' ρ : {ρ : GaloisSet K (f * e + n) //
        ρ.splittingSymbol = (f, e) ::ₘ τ ∧ IsOrbitOfType ρ A f e},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      (∑' ρ₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
      (∑' ρ₂ : {ρ : GaloisSet K n // ρ.splittingSymbol = τ},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
  -- Choose an equivalence `Fin (f * e) ⊕ Fin n ≃ Fin (f * e + n)` mapping the left summand
  -- onto `A`.
  let e₁ : Fin (f * e) ≃ (A : Set (Fin (f * e + n))) :=
    (Fintype.equivFinOfCardEq (by simp [hA])).symm
  let e₂ : Fin n ≃ ((A : Set (Fin (f * e + n)))ᶜ : Set (Fin (f * e + n))) :=
    (Fintype.equivFinOfCardEq (by
      have hcard : Fintype.card {x : Fin (f * e + n) // x ∉ A} = (Finset.univ \ A).card := by
        rw [Fintype.card_subtype, Finset.sdiff_eq_filter]
      have hcompl : Fintype.card ((A : Set (Fin (f * e + n)))ᶜ : Set (Fin (f * e + n))) =
          Fintype.card {x : Fin (f * e + n) // x ∉ A} := rfl
      rw [hcompl, hcard, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin, hA, Nat.add_sub_cancel_left])).symm
  let eA : Fin (f * e) ⊕ Fin n ≃ Fin (f * e + n) :=
    (Equiv.sumCongr e₁ e₂).trans (Equiv.Set.sumCompl (A : Set (Fin (f * e + n))))
  have hrange : Set.range (eA ∘ Sum.inl) = (A : Set (Fin (f * e + n))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e₁ i).2
    · intro hx
      exact ⟨e₁.symm ⟨x, hx⟩, congrArg Subtype.val (e₁.apply_symm_apply ⟨x, hx⟩)⟩
  let Φ := sumSplittingSymbolEquiv (K := K) hf he τ A eA hrange
  rw [← Φ.tsum_eq]
  calc
    ∑' p : {ρ₁ : GaloisSet K (f * e) // ρ₁.splittingSymbol = {(f, e)}} ×
        {ρ₂ : GaloisSet K n // ρ₂.splittingSymbol = τ},
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (Φ p).1.discriminantExponent
      = ∑' p : {ρ₁ : GaloisSet K (f * e) // ρ₁.splittingSymbol = {(f, e)}} ×
          {ρ₂ : GaloisSet K n // ρ₂.splittingSymbol = τ},
          (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent) *
            (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.2.1.discriminantExponent) := by
        refine tsum_congr fun p ↦ ?_
        have hΦ : (Φ p).1 = GaloisSet.ofSumEquiv eA p.1.1 p.2.1 := rfl
        rw [hΦ, GaloisSet.discriminantExponent_ofSumEquiv, pow_add, one_div, one_div, one_div,
          ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
            (.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
    _ = (∑' ρ₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
        (∑' ρ₂ : {ρ : GaloisSet K n // ρ.splittingSymbol = τ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
        rw [tsum_prod']
        simp_rw [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right]

/-- Double-counting recurrence for the unnormalized mass of a splitting symbol `(f, e) ::ₘ τ`:
multiplying by the multiplicity `τ.count (f, e) + 1` of `(f, e)` equals `choose (m + n) m` times
the product of the unnormalized masses for `{(f, e)}` and `τ`. -/
private theorem count_mul_tsum_splittingSymbol_cons {f e n : ℕ} (hf : 0 < f) (he : 0 < e)
    (τ : Multiset (ℕ × ℕ)) :
    ((τ.count (f, e) + 1 : ℕ) : ℝ≥0∞) *
        ∑' ρ : {ρ : GaloisSet K (f * e + n) // ρ.splittingSymbol = (f, e) ::ₘ τ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      (((f * e + n).choose (f * e) : ℕ) : ℝ≥0∞) *
        (∑' ρ₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
        (∑' ρ₂ : {ρ : GaloisSet K n // ρ.splittingSymbol = τ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
  classical
  let P := Σ ρ : {ρ : GaloisSet K (f * e + n) // ρ.splittingSymbol = (f, e) ::ₘ τ},
    {A : Finset (Fin (f * e + n)) // IsOrbitOfType ρ.1 A f e}
  let Q := Σ A : {A : Finset (Fin (f * e + n)) // A.card = f * e},
    {ρ : GaloisSet K (f * e + n) // ρ.splittingSymbol = (f, e) ::ₘ τ ∧ IsOrbitOfType ρ A.1 f e}
  let swap : P ≃ Q :=
    { toFun p := ⟨⟨p.2.1, card_eq_of_isOrbitOfType p.2.2⟩, ⟨p.1.1, p.1.2, p.2.2⟩⟩
      invFun q := ⟨⟨q.2.1, q.2.2.1⟩, ⟨q.1.1, q.2.2.2⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  -- Side 1: sum over `ρ` first, where each fiber has cardinality `τ.count (f, e) + 1`.
  have h1 :
      ∑' p : P, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent =
        ((τ.count (f, e) + 1 : ℕ) : ℝ≥0∞) *
          ∑' ρ : {ρ : GaloisSet K (f * e + n) // ρ.splittingSymbol = (f, e) ::ₘ τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent := by
    rw [tsum_sigma', ← ENNReal.tsum_mul_left]
    refine tsum_congr fun ρ ↦ ?_
    rw [tsum_fintype]
    dsimp only
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      card_isOrbitOfType_eq_count ρ.1, ρ.2, Multiset.count_cons_self]
  -- Side 2: swap to sum over `A` first, where each fiber factors into symbols `{(f, e)}` and `τ`.
  have h2 :
      ∑' q : Q, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ q.2.1.discriminantExponent =
        (((f * e + n).choose (f * e) : ℕ) : ℝ≥0∞) *
          (∑' ρ₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
          (∑' ρ₂ : {ρ : GaloisSet K n // ρ.splittingSymbol = τ},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by
    rw [tsum_sigma']
    simp_rw [fun A : {A : Finset (Fin (f * e + n)) // A.card = f * e} ↦
      tsum_isOrbitOfType_eq_mul (K := K) hf he τ A.1 A.2]
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    have hcard : Fintype.card {A : Finset (Fin (f * e + n)) // A.card = f * e} =
        (f * e + n).choose (f * e) := by
      have hset : (Finset.univ.filter fun A : Finset (Fin (f * e + n)) ↦ A.card = f * e) =
          (Finset.univ : Finset (Fin (f * e + n))).powersetCard (f * e) := by
        ext A
        simp
      rw [Fintype.card_subtype, hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
    rw [hcard]
  have hswap :
      ∑' p : P, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ p.1.1.discriminantExponent =
        ∑' q : Q, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ q.2.1.discriminantExponent :=
    swap.tsum_eq (fun q ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ q.2.1.discriminantExponent)
  rw [← h1, hswap, h2]

end SplittingSymbolMass

/-- **Mass formula for a fixed splitting symbol** ([Bhargava 2007, Prop. 2.1]): for a splitting
symbol `σ` of degree `n` (a multiset of pairs `(f, e)` of positive integers with `∑ f e = n`), the
labelled Galois sets of size `n` with splitting symbol `σ` have mass
`1 / (#Aut(σ) · q ^ (∑ f (e - 1)))`, where `q` is the residue cardinality of `K`. -/
theorem etaleMass_splittingSymbol {n : ℕ} {σ : Multiset (ℕ × ℕ)}
    (hσ : ∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) (hn : (σ.map fun x => x.1 * x.2).sum = n) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / ((splittingSymbolAut σ : ℝ≥0∞) *
        (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent σ) := by
  subst hn
  induction σ using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero]
    rw [tsum_eq_single ⟨GaloisSet.trivial K 0, by simp⟩
      (fun ρ hρ ↦ absurd (Subtype.ext (GaloisSet.ext fun _ i ↦ Fin.elim0 i)) hρ)]
    simp
  | cons x τ ih =>
    rcases x with ⟨f, e⟩
    have hf : 0 < f := (hσ (f, e) (Multiset.mem_cons_self _ _)).1
    have he : 0 < e := (hσ (f, e) (Multiset.mem_cons_self _ _)).2
    have hih := ih fun y hy ↦ hσ y (Multiset.mem_cons_of_mem hy)
    have htr := etaleMass_isTransitive_splittingSymbol (K := K) hf he
    set n := (τ.map fun y => y.1 * y.2).sum
    have hsum : (((f, e) ::ₘ τ).map fun y => y.1 * y.2).sum = f * e + n := by simp [n]
    rw [hsum]
    have hfac_inv :
        (((f * e + n)! : ℕ) : ℝ≥0∞)⁻¹ * (((f * e + n).choose (f * e) : ℕ) : ℝ≥0∞) =
          ((f * e)! : ℝ≥0∞)⁻¹ * (n ! : ℝ≥0∞)⁻¹ := by
      have hch : (f * e + n)! = (f * e + n).choose (f * e) * ((f * e)! * n !) := by
        simpa [Nat.add_sub_cancel_left, mul_assoc] using
          (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right (f * e) n)).symm
      rw [hch, Nat.cast_mul,
        ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
        mul_right_comm, ENNReal.inv_mul_cancel
          (by exact_mod_cast (Nat.choose_pos (Nat.le_add_right (f * e) n)).ne')
          (ENNReal.natCast_ne_top _),
        one_mul, Nat.cast_mul,
        ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _))]
    have hmul :
        ((τ.count (f, e) + 1 : ℕ) : ℝ≥0∞) *
            ((((f * e + n)! : ℕ) : ℝ≥0∞)⁻¹ *
              ∑' ρ : {ρ : GaloisSet K (f * e + n) // ρ.splittingSymbol = (f, e) ::ₘ τ},
                1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) =
          (1 / ((f : ℝ≥0∞) * (Nat.card 𝓀[K] : ℝ≥0∞) ^ (f * (e - 1)))) *
            (1 / ((splittingSymbolAut τ : ℝ≥0∞) *
              (Nat.card 𝓀[K] : ℝ≥0∞) ^ splittingSymbolExponent τ)) := by
      rw [mul_left_comm, count_mul_tsum_splittingSymbol_cons (K := K) (n := n) hf he τ,
        ← mul_assoc, ← mul_assoc, hfac_inv]
      calc
        ((f * e)! : ℝ≥0∞)⁻¹ * (n ! : ℝ≥0∞)⁻¹ *
            (∑' ρ₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
            (∑' ρ₂ : {ρ : GaloisSet K n // ρ.splittingSymbol = τ},
              1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent)
          = (((f * e)! : ℝ≥0∞)⁻¹ *
              ∑' ρ₁ : {ρ : GaloisSet K (f * e) // ρ.splittingSymbol = {(f, e)}},
                1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₁.1.discriminantExponent) *
            ((n ! : ℝ≥0∞)⁻¹ *
              ∑' ρ₂ : {ρ : GaloisSet K n // ρ.splittingSymbol = τ},
                1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ₂.1.discriminantExponent) := by ring
        _ = _ := by rw [htr, hih]
    have hcancel := congrArg (((τ.count (f, e) + 1 : ℕ) : ℝ≥0∞)⁻¹ * ·) hmul
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel (by exact_mod_cast Nat.succ_ne_zero (τ.count (f, e)))
        (ENNReal.natCast_ne_top _), one_mul] at hcancel
    rw [hcancel, splittingSymbolAut_cons, splittingSymbolExponent_cons]
    simp only [one_div, ← Nat.cast_pow, ← Nat.cast_mul]
    rw [← ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
      ← Nat.cast_mul,
      ← ENNReal.mul_inv (.inr (ENNReal.natCast_ne_top _)) (.inl (ENNReal.natCast_ne_top _)),
      ← Nat.cast_mul]
    congr 2
    rw [pow_add]
    ring

/-- **Mass formula for a fixed ramification partition** ([Bhargava 2007, Prop. 2.2]): for a
partition `π` of `k` into at most `n - k` parts, the labelled Galois sets of size `n` whose
splitting symbol has ramification partition `π` have mass `q ^ (-k)`, where `q` is the residue
cardinality of `K`. -/
theorem etaleMass_ramificationPartition {n k : ℕ} {π : k.Partition}
    (hπ : Multiset.card π.parts ≤ n - k) :
    (n ! : ℝ≥0∞)⁻¹ *
        ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts},
          1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent =
      1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  let S := {σ : Multiset (ℕ × ℕ) // (∀ x ∈ σ, 0 < x.1 ∧ 0 < x.2) ∧
    (σ.map fun x => x.1 * x.2).sum = n ∧ ramificationPartition σ = π.parts}
  let g : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} → S :=
    fun ρ ↦ ⟨ρ.1.splittingSymbol, fun _ hx ↦ ρ.1.pos_of_mem_splittingSymbol hx,
      ρ.1.sum_map_mul_splittingSymbol, ρ.2⟩
  rw [← tsum_fiberwise
      (fun ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.parts} ↦
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) g,
    ← ENNReal.tsum_mul_left]
  have hfiber : ∀ σ : S,
      (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : g ⁻¹' {σ}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent =
        (1 / (splittingSymbolAut σ.1 : ℝ≥0∞)) * (1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k) := by
    intro σ
    let e : (g ⁻¹' {σ}) ≃ {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1} :=
      { toFun ρ := ⟨ρ.1.1, congrArg Subtype.val ρ.2⟩
        invFun ρ := ⟨⟨ρ.1, by rw [ρ.2, σ.2.2.2]⟩, Subtype.ext ρ.2⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    have heq :
        ∑' ρ : g ⁻¹' {σ}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent =
          ∑' ρ : {ρ : GaloisSet K n // ρ.splittingSymbol = σ.1},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent :=
      e.tsum_eq (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
    rw [heq, etaleMass_splittingSymbol σ.2.1 σ.2.2.1,
      splittingSymbolExponent_eq_sum_ramificationPartition, σ.2.2.2, π.parts_sum,
      one_div, one_div, one_div,
      ENNReal.mul_inv (.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
        (.inl (ENNReal.natCast_ne_top _))]
  simp_rw [hfiber]
  rw [ENNReal.tsum_mul_right, tsum_one_div_splittingSymbolAut_ramificationPartition n k π hπ,
    one_mul]

variable (K) in
/-- **Bhargava's mass formula** ([Bhargava 2007, Thm. 1.1, Prop. 2.3, §8]): for any nonarchimedean
local field `K` with `q` residue classes and any `n : ℕ`,
`M_n(K) = ∑_{k ≤ n} q(k, n - k) · q ^ (-k)`, where `q(k, m)` is the number of partitions of `k`
into at most `m` parts. For `n > 0` the `k = n` term vanishes because `q(n, 0) = 0`; at `n = 0`
both sides equal `1`. -/
theorem etaleMass_eq (n : ℕ) :
    etaleMass K n =
      ∑ k ∈ Finset.range (n + 1),
        (((Finset.univ : Finset k.Partition).filter fun π => π.parts.card ≤ n - k).card :
            ℝ≥0∞) / (Nat.card 𝓀[K] : ℝ≥0∞) ^ k := by
  classical
  have hsum_le : ∀ ρ : GaloisSet K n,
      (ramificationPartition ρ.splittingSymbol).sum +
        Multiset.card (ramificationPartition ρ.splittingSymbol) ≤ n := by
    intro ρ
    have hdeg := sum_map_mul_eq_sum_ramificationPartition_add ρ.splittingSymbol
      (fun x hx ↦ (ρ.pos_of_mem_splittingSymbol hx).2)
    rw [ρ.sum_map_mul_splittingSymbol] at hdeg
    omega
  let g₁ : GaloisSet K n → Finset.range (n + 1) :=
    fun ρ ↦ ⟨(ramificationPartition ρ.splittingSymbol).sum,
      Finset.mem_range.2 (by have := hsum_le ρ; omega)⟩
  rw [etaleMass_def,
    ← tsum_fiberwise
      (fun ρ : GaloisSet K n ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.discriminantExponent) g₁,
    tsum_fintype, Finset.mul_sum, Finset.univ_eq_attach, ← Finset.sum_attach (Finset.range (n + 1))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  let g₂ : g₁ ⁻¹' {k} → {π : (k : ℕ).Partition // π.parts.card ≤ n - k} :=
    fun ρ ↦
      ⟨{ parts := ramificationPartition ρ.1.splittingSymbol
         parts_pos := fun ht ↦ Nat.pos_of_ne_zero (mem_ramificationPartition.1 ht).1
         parts_sum := congrArg Subtype.val ρ.2 },
       by
         dsimp only
         have := hsum_le ρ.1
         have hk := congrArg Subtype.val ρ.2
         dsimp only [g₁] at hk
         omega⟩
  rw [← tsum_fiberwise
      (fun ρ : g₁ ⁻¹' {k} ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent) g₂,
    tsum_fintype, Finset.mul_sum]
  have hpart : ∀ π : {π : (k : ℕ).Partition // π.parts.card ≤ n - k},
      (n ! : ℝ≥0∞)⁻¹ *
          ∑' ρ : g₂ ⁻¹' {π}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent =
        1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ (k : ℕ) := by
    intro π
    let e : (g₂ ⁻¹' {π}) ≃
        {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.1.parts} :=
      { toFun ρ := ⟨ρ.1.1, congrArg (fun p ↦ p.1.parts) ρ.2⟩
        invFun ρ :=
          ⟨⟨ρ.1, Subtype.ext (by dsimp only [g₁]; rw [ρ.2, π.1.parts_sum])⟩,
            Subtype.ext (Nat.Partition.ext ρ.2)⟩
        left_inv _ := rfl
        right_inv _ := rfl }
    have heq :
        ∑' ρ : g₂ ⁻¹' {π}, 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.1.discriminantExponent =
          ∑' ρ : {ρ : GaloisSet K n // ramificationPartition ρ.splittingSymbol = π.1.parts},
            1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent :=
      e.tsum_eq (fun ρ ↦ 1 / (Nat.card 𝓀[K] : ℝ≥0∞) ^ ρ.1.discriminantExponent)
    rw [heq, etaleMass_ramificationPartition π.2]
  simp_rw [hpart]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_subtype, mul_one_div]

end TauCeti
