/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.FieldTheory.RatFunc.PowerTower
public import TauCeti.RingTheory.Valuation.Discrete.Frobenius

/-!
# Frobenius and separating elements of a function field

This file proves the fixed-parameter part of Stichtenoth's separable-generation criterion.  For a
one-variable function field `F / k` over a perfect field of exponential characteristic `p`, an
element outside the subfield `F^p` of Frobenius powers is separating.  Consequently, a place at
which the order of `x` is not divisible by `p` certifies that `x` is separating.

The proof combines three ingredients.  A separating parameter exists over a perfect field; the
rational function field has degree `p` over its `p`-th-power subfield; and the kernel of a nonzero
derivation is an intermediate field.  The first two facts give `[F : F^p] = p`.  Since this degree
is prime in positive characteristic, the kernel of a nonzero derivation that contains `F^p` must
equal `F^p`.

## Main results

* `TauCeti.IsFunctionField.finrank_fieldRange_frobenius`: `[F : F^p] = p`.
* `TauCeti.IsFunctionField.D_eq_zero_iff_mem_fieldRange_frobenius`: the kernel of the universal
  derivation is exactly `F^p`.
* `TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_not_dvd_ord`: the
  valuation-order criterion.

## Reference

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

noncomputable section

open Module KaehlerDifferential

open scoped IntermediateField WithZero

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

namespace IsFunctionField

/-- The degree of a one-variable function field over its subfield of `p`-th powers is `p`.
This is the degree computation underlying the fixed-parameter separability criterion. -/
theorem finrank_fieldRange_frobenius [PerfectField k] (hF : TauCeti.IsFunctionField k F)
    (p : ℕ) [ExpChar F p] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  obtain ⟨y, hy⟩ := hF.exists_transcendental
  have hA : k⟮y⟯.toSubfield.map (frobenius F p) = k⟮y ^ p⟯.toSubfield := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [IntermediateField.mem_toSubfield, frobenius_def]
      induction hz using IntermediateField.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff.mp hz]
        exact IntermediateField.mem_adjoin_simple_self k (y ^ p)
      | algebraMap c =>
        rw [← map_pow]
        exact IntermediateField.algebraMap_mem _ _
      | add a b _ _ ha hb =>
        rw [add_pow_expChar]
        exact IntermediateField.add_mem _ ha hb
      | inv a _ ha =>
        rw [inv_pow]
        exact IntermediateField.inv_mem _ ha
      | mul a b _ _ ha hb =>
        rw [mul_pow]
        exact IntermediateField.mul_mem _ ha hb
    · intro z hz
      induction hz using IntermediateField.adjoin_induction with
      | mem z hz =>
        rw [Set.mem_singleton_iff.mp hz]
        exact ⟨y, IntermediateField.mem_adjoin_simple_self k y, rfl⟩
      | algebraMap c =>
        obtain ⟨d, hd⟩ := surjective_frobenius k p c
        exact ⟨algebraMap k F d, IntermediateField.algebraMap_mem _ _, by
          rw [← RingHom.map_frobenius, hd]⟩
      | add a b _ _ ha hb => exact Subfield.add_mem _ ha hb
      | inv a _ ha => exact Subfield.inv_mem _ ha
      | mul a b _ _ ha hb => exact Subfield.mul_mem _ ha hb
  have hAB : k⟮y⟯.toSubfield.map (frobenius F p) ≤ k⟮y⟯.toSubfield := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [frobenius_def] using k⟮y⟯.toSubfield.pow_mem hz p
  have hAC : k⟮y⟯.toSubfield.map (frobenius F p) ≤ (frobenius F p).fieldRange := by
    rw [RingHom.fieldRange_eq_map]
    rintro _ ⟨z, _, rfl⟩
    exact ⟨z, trivial, rfl⟩
  have hrelAB : Subfield.relfinrank (k⟮y⟯.toSubfield.map (frobenius F p)) k⟮y⟯.toSubfield = p := by
    rw [hA]
    exact relfinrank_adjoin_pow_adjoin hy p
  have hrelAC : Subfield.relfinrank (k⟮y⟯.toSubfield.map (frobenius F p))
      (frobenius F p).fieldRange = Subfield.relfinrank k⟮y⟯.toSubfield ⊤ := by
    rw [RingHom.fieldRange_eq_map]
    exact Subfield.relfinrank_map_map k⟮y⟯.toSubfield ⊤ (frobenius F p)
  let _ : FiniteDimensional k⟮y⟯ F := hF.finiteDimensional_adjoin hy
  have hn : Subfield.relfinrank k⟮y⟯.toSubfield ⊤ ≠ 0 := by
    rw [Subfield.relfinrank_top_right]
    exact Module.finrank_pos.ne'
  have hABF := Subfield.relfinrank_mul_finrank_top hAB
  have hACF := Subfield.relfinrank_mul_finrank_top hAC
  rw [hrelAB] at hABF
  rw [← Subfield.relfinrank_top_right] at hABF
  rw [hrelAC] at hACF
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero hn)
  calc
    Subfield.relfinrank k⟮y⟯.toSubfield ⊤ * Module.finrank (frobenius F p).fieldRange F =
        Module.finrank (k⟮y⟯.toSubfield.map (frobenius F p)) F := hACF
    _ = p * Subfield.relfinrank k⟮y⟯.toSubfield ⊤ := hABF.symm
    _ = Subfield.relfinrank k⟮y⟯.toSubfield ⊤ * p := Nat.mul_comm _ _

/-- **The kernel of the universal derivation is the Frobenius subfield**: in a one-variable
function field over a perfect field, `d x = 0` exactly when `x` is a `p`-th power. This identifies
differential nonvanishing with the Frobenius-subfield obstruction used by separating criteria. -/
@[simp]
theorem D_eq_zero_iff_mem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact p.Prime] (x : F) :
    D k F x = 0 ↔ x ∈ (frobenius F p).fieldRange := by
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  let _ : CharP F p := by
    cases (inferInstance : ExpChar F p) with
    | zero => exact (Nat.not_prime_one Fact.out).elim
    | prime _ => infer_instance
  have hk : ∀ c : k, algebraMap k F c ∈ (frobenius F p).fieldRange := by
    intro c
    obtain ⟨d, hd⟩ := surjective_frobenius k p c
    exact ⟨algebraMap k F d, by rw [← RingHom.map_frobenius, hd]⟩
  let C : IntermediateField k F := (frobenius F p).fieldRange.toIntermediateField hk
  have hmemC (z : F) : z ∈ C ↔ z ∈ (frobenius F p).fieldRange := Iff.rfl
  let Z : Subfield F :=
    { carrier := {z | D k F z = 0}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simpa using congrArg₂ (· + ·) ha hb
      neg_mem' := by
        intro a ha
        simpa using congrArg Neg.neg ha
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rw [Derivation.leibniz_inv, ha, smul_zero] }
  have hkZ : ∀ c : k, algebraMap k F c ∈ Z := fun c ↦ by simp [Z]
  let K : IntermediateField k F := Z.toIntermediateField hkZ
  have hmemK (z : F) : z ∈ K ↔ D k F z = 0 := Iff.rfl
  have hCK : C ≤ K := by
    intro z hz
    obtain ⟨a, rfl⟩ := (hmemC z).mp hz
    rw [hmemK, frobenius_def, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F,
      CharP.cast_eq_zero, zero_smul]
  have hK_ne_top : K ≠ ⊤ := by
    obtain ⟨y, hy, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    let _ := hsep
    intro hK
    have hyK : y ∈ K := hK.symm ▸ IntermediateField.mem_top
    exact D_ne_zero_of_separating hy ((hmemK y).mp hyK)
  have hdeg : Module.finrank C F = p := hF.finrank_fieldRange_frobenius p
  have hdiv : IntermediateField.relfinrank C K ∣ p := by
    rw [← hdeg]
    exact IntermediateField.relfinrank_dvd_finrank_top_of_le hCK
  have hrel : IntermediateField.relfinrank C K = 1 := by
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdiv with h | h
    · exact h
    · exfalso
      have htower := IntermediateField.relfinrank_mul_finrank_top hCK
      rw [h, hdeg] at htower
      have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
      have hfin : Module.finrank K F = 1 := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0)
        simpa using htower
      exact hK_ne_top (IntermediateField.finrank_eq_one_iff_eq_top.mp hfin)
  have hKC : K ≤ C := IntermediateField.relfinrank_eq_one_iff.mp hrel
  exact ⟨fun h ↦ (hmemC x).mp (hKC ((hmemK x).mpr h)), fun h ↦ (hmemK x).mp (hCK ((hmemC x).mpr h))⟩

/-- **The valuation-order criterion for a separating element** (Stichtenoth, Proposition
3.10.2): if the order of `x` at a discrete valuation is not divisible by the exponential
characteristic `p`, then `x` is transcendental and `F / k(x)` is separable. -/
theorem transcendental_and_isSeparable_adjoin_of_not_dvd_ord [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (v : Valuation F ℤᵐ⁰) (p : ℕ)
    [ExpChar F p] {x : F} (hx : ¬ (p : ℤ) ∣ v.ord x) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  cases (inferInstance : ExpChar F p) with
  | zero => exact (hx (one_dvd _)).elim
  | prime hp =>
    let _ : Fact p.Prime := ⟨hp⟩
    have hnotmem : x ∉ (frobenius F p).fieldRange := by
      rw [← iterateFrobenius_one (R := F) p]
      apply v.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord p 1
      simpa using hx
    have hDx : D k F x ≠ 0 := fun h ↦
      hnotmem ((hF.D_eq_zero_iff_mem_fieldRange_frobenius p x).mp h)
    exact ⟨transcendental_of_D_ne_zero hDx, hF.isSeparable_adjoin_iff_D_ne_zero.mpr hDx⟩

end IsFunctionField

end TauCeti
