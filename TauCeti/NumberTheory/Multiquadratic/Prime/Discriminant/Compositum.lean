/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.Galois.Basic
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Field
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Independence
import Mathlib.Algebra.BigOperators.Option

/-!
# Discriminants of prime-discriminant composita

Let `D i` be distinct prime discriminants, at most one of which is even, and let `root i` be
chosen square roots of their radicands in a number field. This file computes the absolute value of
the discriminant of their compositum:

`|disc ℚ(root i : i)| = ∏ i, |D i| ^ 2 ^ (n - 1)`.

The proof adjoins one root at a time. Distinct prime discriminants in the family are coprime, so
Mathlib's discriminant formula for the compositum of linearly disjoint number fields applies at
each step. This formula is the finite-place input to the genus-field construction: a rational
prime belonging to one prime-discriminant factor cannot ramify in the compositum of all the other
factors.

The discriminant formula for a compositum is
`NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow` from Mathlib. The
prime-discriminant description of genus fields is classical; see D. A. Cox, *Primes of the Form
x² + ny²*, and F. Lemmermeyer, *Reciprocity Laws*.

## Main result

* `TauCeti.Multiquadratic.natAbs_discr_adjoin_range_primeDiscriminantRadicands`: the absolute
  discriminant of a compositum of distinct prime-discriminant quadratic fields.
-/

public section

open IntermediateField
open scoped NumberField

namespace TauCeti.Multiquadratic

universe u v

/-- Adjoining the roots indexed by `some i` and then the root indexed by `none` adjoins all the
roots. -/
private lemma adjoin_range_comp_some_sup_adjoin_singleton {α : Type*} {K F : Type*} [Field K]
    [Field F] [Algebra K F] (r : Option α → F) :
    adjoin K (Set.range (r ∘ some)) ⊔ adjoin K {r none} = adjoin K (Set.range r) := by
  rw [← adjoin_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Function.comp_apply]
  constructor
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨some i, rfl⟩
    · exact ⟨none, rfl⟩
  · rintro ⟨i, rfl⟩
    cases i with
    | none => exact Or.inr rfl
    | some i => exact Or.inl ⟨i, rfl⟩

/-- The squared product of the exponent `2 ^ (n - 1)` powers is the product of the exponent
`2 ^ n` powers, where `n` is the cardinality of the index type. -/
private lemma prod_pow_two_pow_pred_sq {α : Type*} [Fintype α] (a : α → ℕ) :
    (∏ i, a i ^ (2 ^ (Fintype.card α - 1))) ^ 2 = ∏ i, a i ^ (2 ^ Fintype.card α) := by
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_mul, ← pow_succ]
  congr 2
  exact Nat.sub_add_cancel (Fintype.card_pos_iff.mpr ⟨i⟩)

/-- The compositum of the roots indexed by `some i` has discriminant coprime to that of the
quadratic field of the root indexed by `none`. -/
private lemma isCoprime_discr_adjoin_range_comp_some {α : Type u} [Fintype α] {M : Type v}
    [Field M] [NumberField M] (D : Option α → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i))
    (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) →
      IsEvenPrimeDiscriminant (D j) → D i = D j)
    (r : Option α → M)
    (hr : ∀ i, r i ^ 2 = algebraMap ℤ M (primeDiscriminantRadicand (D i)))
    (hdisc : (NumberField.discr (adjoin ℚ (Set.range (r ∘ some)))).natAbs =
      ∏ i : α, (D (some i)).natAbs ^ (2 ^ (Fintype.card α - 1))) :
    IsCoprime (NumberField.discr (adjoin ℚ (Set.range (r ∘ some))))
      (NumberField.discr (adjoin ℚ {r none})) := by
  have hdisc₂ : NumberField.discr (adjoin ℚ {r none}) = D none :=
    discr_adjoin_singleton_eq_primeDiscriminant (hD none) (hr none)
  -- Distinct prime discriminants are pairwise coprime; multiplying the old factors gives
  -- coprime discriminants for the two fields.
  have hcoprime_factor (i : α) : IsCoprime (D (some i)) (D none) := by
    have hnot_even : ¬ (IsEvenPrimeDiscriminant (D (some i)) ∧
        IsEvenPrimeDiscriminant (D none)) := by
      rintro ⟨hi, hn⟩
      exact Option.some_ne_none i (hinj (heven (some i) none hi hn))
    have h := isCoprime_discr_adjoin_singleton_of_primeDiscriminant
      (L := M) (hD (some i)) (hD none)
      (fun h ↦ Option.some_ne_none i (hinj h)) hnot_even (hr (some i)) (hr none)
    simpa only [discr_adjoin_singleton_eq_primeDiscriminant (hD (some i)) (hr (some i)),
      hdisc₂] using h
  rw [Int.isCoprime_iff_nat_coprime, hdisc, hdisc₂]
  exact Nat.Coprime.prod_left fun i _ ↦
    (Int.isCoprime_iff_nat_coprime.mp (hcoprime_factor i)).pow_left _

/-- The inductive step of `natAbs_discr_adjoin_range_primeDiscriminantRadicands`: adjoining one
more root to a family whose compositum has the predicted discriminant. -/
private lemma natAbs_discr_adjoin_range_option {α : Type u} [Fintype α] {L : Type v} [Field L]
    [NumberField L] (D : Option α → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i))
    (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) →
      IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : Option α → L)
    (hroot : ∀ i, root i ^ 2 = algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ)))
    (hdisc₁ : (NumberField.discr
      (adjoin ℚ (Set.range (gen (K := ℚ) root ∘ some)))).natAbs =
        ∏ i : α, (D (some i)).natAbs ^ (2 ^ (Fintype.card α - 1))) :
    (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
      ∏ i, (D i).natAbs ^ (2 ^ (Fintype.card (Option α) - 1)) := by
  classical
  let M : IntermediateField ℚ L := adjoin ℚ (Set.range root)
  let rootM : Option α → M := gen (K := ℚ) root
  let K₁ : IntermediateField ℚ M := adjoin ℚ (Set.range (rootM ∘ some))
  let K₂ : IntermediateField ℚ M := adjoin ℚ {rootM none}
  have hrootM_int (i : Option α) : rootM i ^ 2 =
      algebraMap ℤ M (primeDiscriminantRadicand (D i)) := by
    rw [gen_sq (d := fun i ↦ ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) hroot i,
      IsScalarTower.algebraMap_apply ℤ ℚ M]
    norm_num
  have hdisc₂ : NumberField.discr K₂ = D none :=
    discr_adjoin_singleton_eq_primeDiscriminant (hD none) (hrootM_int none)
  have hcoprime : IsCoprime (NumberField.discr K₁) (NumberField.discr K₂) :=
    isCoprime_discr_adjoin_range_comp_some D hD hinj heven rootM hrootM_int hdisc₁
  have : IsGalois ℚ K₁ :=
    isGalois (d := fun i : α ↦ ((primeDiscriminantRadicand (D (some i)) : ℤ) : ℚ))
      (root := rootM ∘ some)
      (fun i ↦ gen_sq (d := fun i ↦ ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) hroot (some i))
  have htop : K₁ ⊔ K₂ = ⊤ := by
    rw [adjoin_range_comp_some_sup_adjoin_singleton]
    exact adjoin_gen_eq_top
  have hformula := NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
    M K₁ K₂ (NumberField.linearDisjoint_of_isGalois_isCoprime_discr M K₁ K₂ hcoprime) htop
      (NumberField.isCoprime_differentIdeal_of_isCoprime_discr M hcoprime)
  -- Compute the two degrees needed as exponents in the compositum discriminant formula.
  have hfinrank₁ : Module.finrank ℚ K₁ = 2 ^ Fintype.card α := by
    have h :=
      finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
      (fun i : α ↦ D (some i)) (fun i ↦ hD (some i))
      (hinj.comp (Option.some_injective α))
      (fun i j hi hj ↦ heven (some i) (some j) hi hj)
      (rootM ∘ some) (fun i ↦ gen_sq (d := fun i ↦ ((primeDiscriminantRadicand (D i) : ℤ) : ℚ))
        hroot (some i))
    simpa only [K₁, Nat.card_eq_fintype_card] using h
  have hfinrank₂ : Module.finrank ℚ K₂ = 2 := by
    have h :=
      finrank_adjoin_roots_primeDiscriminantRadicands_of_forall_isEvenPrimeDiscriminant_eq
      (fun _ : Unit ↦ D none) (fun _ ↦ hD none) (fun _ _ _ ↦ Subsingleton.elim _ _)
      (fun _ _ _ _ ↦ rfl) (fun _ : Unit ↦ rootM none)
      (fun _ ↦ gen_sq (d := fun i ↦ ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) hroot none)
    have hrange : Set.range (fun _ : Unit ↦ rootM none) = {rootM none} := by
      ext x
      simp
    rw [hrange] at h
    simpa only [K₂, Nat.card_unique, pow_one] using h
  rw [hdisc₁, hdisc₂, hfinrank₁, hfinrank₂, prod_pow_two_pow_pred_sq] at hformula
  simpa only [M, Fintype.card_option, Fintype.prod_option, Function.comp_apply,
    Nat.add_sub_cancel, mul_comm] using hformula

/-- **Discriminant of a prime-discriminant compositum.** Let `D : ι → ℤ` be an injective
family of prime discriminants containing at most one even member, and let `root i` square to the
radicand attached to `D i`. If `n = |\u03b9|`, then the compositum of these roots has absolute
discriminant `∏ i, |D i| ^ 2 ^ (n - 1)`.

For the empty family both sides are one. For a singleton this recovers that the quadratic field
attached to a prime discriminant `D` has discriminant `D`. -/
theorem natAbs_discr_adjoin_range_primeDiscriminantRadicands
    {ι : Type u} [Fintype ι] {L : Type v} [Field L] [NumberField L]
    (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
    (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) →
      IsEvenPrimeDiscriminant (D j) → D i = D j)
    (root : ι → L)
  (hroot : ∀ i, root i ^ 2 =
      algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ))) :
    (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
      ∏ i, (D i).natAbs ^ (2 ^ (Fintype.card ι - 1)) := by
  classical
  refine (Fintype.induction_empty_option
    (P := fun (ι : Type u) [Fintype ι] =>
      ∀ {L : Type v} [Field L] [NumberField L]
        (D : ι → ℤ) (hD : ∀ i, IsPrimeDiscriminant (D i)) (hinj : Function.Injective D)
        (heven : ∀ i j, IsEvenPrimeDiscriminant (D i) →
          IsEvenPrimeDiscriminant (D j) → D i = D j)
        (root : ι → L),
        (∀ i, root i ^ 2 =
          algebraMap ℚ L (((primeDiscriminantRadicand (D i) : ℤ) : ℚ))) →
        (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
          ∏ i, (D i).natAbs ^ (2 ^ (Fintype.card ι - 1)))
    ?_ ?_ ?_ ι) D hD hinj heven root hroot
  · intro α β _ e ih
    exact by
      intro L _ _ D hD hinj heven root hroot
      let _ := Fintype.ofEquiv β e.symm
      have h := ih (L := L) (D := D ∘ e) (fun i ↦ hD (e i)) (hinj.comp e.injective)
        (fun i j hi hj ↦ heven (e i) (e j) hi hj) (root ∘ e)
        (fun i ↦ hroot (e i))
      rw [EquivLike.range_comp root e, Fintype.card_congr e] at h
      calc
        (NumberField.discr (adjoin ℚ (Set.range root))).natAbs =
            ∏ i : α, (D (e i)).natAbs ^ (2 ^ (Fintype.card β - 1)) := by
          simpa only [Function.comp_apply] using h
        _ = ∏ i : β, (D i).natAbs ^ (2 ^ (Fintype.card β - 1)) :=
          Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
  · exact by
      intro L _ _ D _ _ _ root _
      have hdisc := NumberField.discr_eq_discr_of_algEquiv _ (botEquiv ℚ L)
      rw [Set.range_eq_empty root, adjoin_empty, hdisc, Rat.numberField_discr]
      simp
  · intro α _ ih
    exact by
      intro L _ _ D hD hinj heven root hroot
      refine natAbs_discr_adjoin_range_option D hD hinj heven root hroot ?_
      exact ih (L := adjoin ℚ (Set.range root)) (D := D ∘ some) (fun i ↦ hD (some i))
        (hinj.comp (Option.some_injective α))
        (fun i j hi hj ↦ heven (some i) (some j) hi hj)
        (gen (K := ℚ) root ∘ some)
        (fun i ↦ gen_sq (d := fun i ↦ ((primeDiscriminantRadicand (D i) : ℤ) : ℚ)) hroot (some i))

end TauCeti.Multiquadratic
