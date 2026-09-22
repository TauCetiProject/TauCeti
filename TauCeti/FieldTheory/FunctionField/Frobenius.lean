/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Relrank
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
is prime, the kernel of a nonzero derivation that contains `F^p` must equal `F^p`.

## Main results

* `TauCeti.IsFunctionField.finrank_fieldRange_frobenius`: `[F : F^p] = p`.
* `TauCeti.IsFunctionField.transcendental_and_isSeparable_adjoin_of_not_mem_fieldRange_frobenius`:
  an element not in `F^p` is separating.
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

/-- The degree `[k(x) : k(x^n)]` is `n` for a transcendental element `x`. -/
private theorem relfinrank_adjoin_pow_adjoin {x : F} (hx : Transcendental k x) (n : ℕ) :
    IntermediateField.relfinrank k⟮x ^ n⟯ k⟮x⟯ = n := by
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  have heX : e RatFunc.X = (⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) :=
    by
      apply Subtype.ext
      exact RatFunc.algEquivOfTranscendental_X x hx
  have hePow : (IntermediateField.adjoin k {(RatFunc.X : RatFunc k) ^ n}).map e.toAlgHom =
      IntermediateField.adjoin k
        {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow]
    congr 2
    exact congrArg (· ^ n) heX
  have heTop : (⊤ : IntermediateField k (RatFunc k)).map e.toAlgHom = ⊤ := by
    rw [← AlgHom.fieldRange_eq_map]
    exact e.fieldRange_eq_top
  have hvalPow : (IntermediateField.adjoin k
      {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n}).map k⟮x⟯.val =
      k⟮x ^ n⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, map_pow]
    rfl
  have hvalTop : (⊤ : IntermediateField k k⟮x⟯).map k⟮x⟯.val = k⟮x⟯ :=
    IntermediateField.lift_top (F := k) k⟮x⟯
  calc
    IntermediateField.relfinrank k⟮x ^ n⟯ k⟮x⟯ =
        IntermediateField.relfinrank
          ((IntermediateField.adjoin k
            {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n}).map
              k⟮x⟯.val)
          ((⊤ : IntermediateField k k⟮x⟯).map k⟮x⟯.val) := by rw [hvalPow, hvalTop]
    _ = IntermediateField.relfinrank
          (IntermediateField.adjoin k
            {(⟨x, IntermediateField.mem_adjoin_simple_self k x⟩ : k⟮x⟯) ^ n}) ⊤ :=
      IntermediateField.relfinrank_map_map _ _ k⟮x⟯.val
    _ = IntermediateField.relfinrank
          (IntermediateField.adjoin k {(RatFunc.X : RatFunc k) ^ n}) ⊤ := by
      rw [← hePow, ← heTop]
      exact IntermediateField.relfinrank_map_map _ _ e.toAlgHom
    _ = n := by
      rw [IntermediateField.relfinrank_top_right]
      exact TauCeti.RatFunc.finrank_adjoin_X_pow k n

/-- The degree of a one-variable function field over its subfield of `p`-th powers is `p`.
This is the degree computation underlying the fixed-parameter separability criterion. -/
theorem finrank_fieldRange_frobenius [PerfectField k] (hF : TauCeti.IsFunctionField k F)
    (p : ℕ) [ExpChar F p] :
    Module.finrank (frobenius F p).fieldRange F = p := by
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  obtain ⟨y, hy⟩ := hF.exists_transcendental
  let B := k⟮y⟯
  let f := frobenius F p
  let A : Subfield F := B.toSubfield.map f
  let C : Subfield F := f.fieldRange
  have hA : A = k⟮y ^ p⟯.toSubfield := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      change z ^ p ∈ k⟮y ^ p⟯
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
          change frobenius F p (algebraMap k F d) = algebraMap k F c
          rw [← RingHom.map_frobenius, hd]⟩
      | add a b _ _ ha hb => exact A.add_mem ha hb
      | inv a _ ha => exact A.inv_mem ha
      | mul a b _ _ ha hb => exact A.mul_mem ha hb
  have hAB : A ≤ B.toSubfield := by
    rintro _ ⟨z, hz, rfl⟩
    simpa [f, frobenius_def] using B.pow_mem hz p
  have hAC : A ≤ C := by
    change B.toSubfield.map f ≤ f.fieldRange
    rw [RingHom.fieldRange_eq_map]
    rintro _ ⟨z, _, rfl⟩
    exact ⟨z, trivial, rfl⟩
  have hrelAB : Subfield.relfinrank A B.toSubfield = p := by
    rw [hA]
    exact relfinrank_adjoin_pow_adjoin hy p
  have hrelAC : Subfield.relfinrank A C = Subfield.relfinrank B.toSubfield ⊤ := by
    change Subfield.relfinrank (B.toSubfield.map f) f.fieldRange = _
    rw [RingHom.fieldRange_eq_map]
    exact Subfield.relfinrank_map_map B.toSubfield ⊤ f
  let _ : FiniteDimensional B F := hF.finiteDimensional_adjoin hy
  have hn : Subfield.relfinrank B.toSubfield ⊤ ≠ 0 := by
    rw [Subfield.relfinrank_top_right]
    exact Module.finrank_pos.ne'
  have hABF := Subfield.relfinrank_mul_finrank_top hAB
  have hACF := Subfield.relfinrank_mul_finrank_top hAC
  rw [hrelAB] at hABF
  rw [← Subfield.relfinrank_top_right] at hABF
  rw [hrelAC] at hACF
  change Module.finrank C F = p
  apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_ne_zero hn)
  calc
    Subfield.relfinrank B.toSubfield ⊤ * Module.finrank C F =
        Module.finrank A F := hACF
    _ = p * Subfield.relfinrank B.toSubfield ⊤ := hABF.symm
    _ = Subfield.relfinrank B.toSubfield ⊤ * p := Nat.mul_comm _ _

/-- In a one-variable function field over a perfect field, an element outside the image of
Frobenius has nonzero universal differential. -/
theorem D_ne_zero_of_not_mem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact p.Prime] {x : F}
    (hx : x ∉ (frobenius F p).fieldRange) : D k F x ≠ 0 := by
  let _ : ExpChar k p := (algebraMap k F).expChar (algebraMap k F).injective p
  let _ : CharP F p := by
    cases (inferInstance : ExpChar F p) with
    | zero => exact (Nat.not_prime_one Fact.out).elim
    | prime _ => infer_instance
  have hk : ∀ c : k, algebraMap k F c ∈ (frobenius F p).fieldRange := by
    intro c
    obtain ⟨d, hd⟩ := surjective_frobenius k p c
    refine ⟨algebraMap k F d, ?_⟩
    change frobenius F p (algebraMap k F d) = algebraMap k F c
    rw [← RingHom.map_frobenius, hd]
  let C : IntermediateField k F := (frobenius F p).fieldRange.toIntermediateField hk
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
        change D k F a = 0 at ha
        change D k F b = 0 at hb
        change D k F (a * b) = 0
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      inv_mem' := by
        intro a ha
        change D k F a = 0 at ha
        change D k F a⁻¹ = 0
        rw [Derivation.leibniz_inv, ha, smul_zero] }
  have hkZ : ∀ c : k, algebraMap k F c ∈ Z := fun c ↦ by simp [Z]
  let K : IntermediateField k F := Z.toIntermediateField hkZ
  have hCK : C ≤ K := by
    rintro z ⟨a, rfl⟩
    change D k F (a ^ p) = 0
    rw [Derivation.leibniz_pow]
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  have hK_ne_top : K ≠ ⊤ := by
    obtain ⟨y, hy, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    let _ := hsep
    intro hK
    have hyK : y ∈ K := hK.symm ▸ IntermediateField.mem_top
    exact D_ne_zero_of_separating hy hyK
  have hdeg : Module.finrank C F = p := by
    exact hF.finrank_fieldRange_frobenius p
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
  intro hDx
  apply hx
  have hxK : x ∈ K := hDx
  exact hKC hxK

/-- An element outside the image of Frobenius is a separating parameter. -/
theorem transcendental_and_isSeparable_adjoin_of_not_mem_fieldRange_frobenius [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (p : ℕ) [ExpChar F p] [Fact p.Prime] {x : F}
    (hx : x ∉ (frobenius F p).fieldRange) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  have hDx := hF.D_ne_zero_of_not_mem_fieldRange_frobenius p hx
  have htrans : Transcendental k x := by
    intro halg
    have hsep : (minpoly k x).Separable :=
      PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)
    have hcoeff : Polynomial.aeval x (minpoly k x).derivative ≠ 0 :=
      hsep.aeval_derivative_ne_zero (minpoly.aeval k x)
    apply hDx
    have hder := (D k F).map_aeval (minpoly k x) x
    rw [minpoly.aeval, map_zero] at hder
    exact (smul_eq_zero.mp hder.symm).resolve_left hcoeff
  exact ⟨htrans, (isSeparable_adjoin_iff_D_ne_zero hF htrans).mpr hDx⟩

/-- **The valuation-order criterion for a separating element** (Stichtenoth, Proposition
3.10.2): if the order of `x` at a discrete valuation is not divisible by the exponential
characteristic `p`, then `x` is transcendental and `F / k(x)` is separable. -/
theorem transcendental_and_isSeparable_adjoin_of_not_dvd_ord [PerfectField k]
    (hF : TauCeti.IsFunctionField k F) (v : Valuation F ℤᵐ⁰) (p : ℕ)
    [ExpChar F p] [Fact p.Prime] {x : F} (hx : ¬ (p : ℤ) ∣ v.ord x) :
    Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  apply hF.transcendental_and_isSeparable_adjoin_of_not_mem_fieldRange_frobenius p
  rw [← iterateFrobenius_one (R := F) p]
  apply v.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord p 1
  simpa using hx

end IsFunctionField

end TauCeti
