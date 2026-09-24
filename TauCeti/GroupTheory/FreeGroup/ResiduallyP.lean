/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.ResiduallyFinite
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Free groups are residually `p`

For every prime `p`, a nontrivial element of a free group survives in some finite `p`-group
quotient. This is the classical residual `p`-finiteness of free groups; it is what makes the
generators of a free pro-`p` group behave like free generators, and it gives residual finiteness
of free groups as a special case.

## Main results

* `FreeGroup.exists_normal_isPGroup_quotient_notMem`: a nontrivial element of `FreeGroup X`
  lies outside some normal subgroup of finite index whose quotient is a `p`-group.
* `FreeGroup.instResiduallyFinite`: free groups are residually finite.

## Implementation notes

Write a nontrivial reduced element as a product of syllables `x₁ ^ e₁ ⋯ x_k ^ e_k`, with nonzero
exponents and consecutive generators distinct, and put `tᵢ = p ^ v_p(eᵢ)`. Spell out the word
`x₁ ^ t₁ ⋯ x_k ^ t_k` in positions `1, …, D`, and let the generator `x` act on `(ZMod p) ^ (D + 1)`
by `1 + Nₓ`, where `Nₓ` is the shift matrix with an entry `1` at `(s - 1, s)` for each position `s`
spelled with `x`. These matrices are upper unitriangular, and the upper unitriangular matrices
over `ZMod p` form a finite `p`-group. The entry of `(1 + Nₓ) ^ n` at `(a, b)` is `n.choose (b - a)`
when all positions in `(a, b]` are spelled with `x`, and `0` otherwise. Tracking the first row
syllable by syllable, the entry of the image of the element at `(0, D)` is a product of binomial
coefficients `n.choose (p ^ v_p(n))`, none of which vanishes modulo `p` by Lucas' theorem; so the
image is not the identity. This is a matrix form of the Magnus embedding reduced modulo `p`.

## References

* W. Magnus, *Beziehungen zwischen Gruppen und Idealen in einem speziellen Ring*,
  Math. Ann. 111 (1935), for the embedding of a free group in a ring of noncommutative power
  series.
* K. Iwasawa, *Einige Sätze über freie Gruppen*, Proc. Imp. Acad. Tokyo 19 (1943), for the
  residual `p`-finiteness of free groups.
-/

public section

open Matrix

namespace FreeGroup

variable {X : Type*}

section Syllables

/-- The product `x₁ ^ e₁ ⋯ x_k ^ e_k` of a list of syllables. -/
private def syllableProd (s : List (X × ℤ)) : FreeGroup X :=
  (s.map fun a ↦ of a.1 ^ a.2).prod

@[simp]
private theorem syllableProd_nil : syllableProd ([] : List (X × ℤ)) = 1 := rfl

@[simp]
private theorem syllableProd_cons (a : X × ℤ) (s : List (X × ℤ)) :
    syllableProd (a :: s) = of a.1 ^ a.2 * syllableProd s := rfl

/-- A syllable list is normal when its exponents are nonzero and consecutive generators are
distinct. -/
private def IsSyllableNormal (s : List (X × ℤ)) : Prop :=
  (∀ a ∈ s, a.2 ≠ 0) ∧ s.IsChain fun a b ↦ a.1 ≠ b.1

/-- Every element of a free group is the product of a normal syllable list. -/
private theorem exists_isSyllableNormal (w : FreeGroup X) :
    ∃ s, IsSyllableNormal s ∧ syllableProd s = w := by
  classical
  rw [← mk_toWord (x := w)]
  induction w.toWord with
  | nil => exact ⟨[], ⟨by simp, .nil⟩, rfl⟩
  | cons a L ih =>
    obtain ⟨x, b⟩ := a
    obtain ⟨s, ⟨hs0, hsc⟩, hs⟩ := ih
    set ε : ℤ := if b then 1 else -1 with hε
    have hε0 : ε ≠ 0 := by rw [hε]; split <;> simp
    have hmk : mk ((x, b) :: L) = of x ^ ε * mk L := by
      rw [← List.singleton_append, ← mul_mk]
      cases b <;> simp [hε, of, inv_mk, invRev]
    rw [hmk, ← hs]
    match s, hs0, hsc with
    | [], _, _ => exact ⟨[(x, ε)], ⟨by simpa using hε0, .singleton _⟩, by simp⟩
    | (y, f) :: s', hs0, hsc =>
      by_cases hyx : y = x
      · subst hyx
        by_cases hf : ε + f = 0
        · refine ⟨s', ⟨fun a ha ↦ hs0 a (List.mem_cons_of_mem _ ha), hsc.tail⟩, ?_⟩
          rw [syllableProd_cons, ← mul_assoc, ← zpow_add, hf, zpow_zero, one_mul]
        · refine ⟨(y, ε + f) :: s', ⟨?_, ?_⟩, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact hf
            · exact hs0 a (List.mem_cons_of_mem _ ha)
          · cases s' with
            | nil => exact .singleton _
            | cons c s'' => exact .cons_cons (List.isChain_cons_cons.mp hsc).1 hsc.tail
          · simp [mul_assoc, zpow_add]
      · refine ⟨(x, ε) :: (y, f) :: s', ⟨?_, .cons_cons (Ne.symm hyx) hsc⟩, by simp⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hε0
        · exact hs0 a ha

end Syllables

section Matrices

variable {p : ℕ} (ℓ : ℕ → Option X) (D : ℕ)

/-- All positions in the interval `(a, b]` are spelled with the letter `x`. -/
private def Spelled (x : X) (a b : ℕ) : Prop :=
  ∀ s ∈ Finset.Ioc a b, ℓ s = some x

private instance [DecidableEq X] (x : X) (a b : ℕ) : Decidable (Spelled ℓ x a b) := by
  unfold Spelled; infer_instance

private theorem spelled_iff {x : X} {a b : ℕ} :
    Spelled ℓ x a b ↔ ∀ s, a < s → s ≤ b → ℓ s = some x := by
  simp [Spelled]

private theorem spelled_succ_iff {x : X} {a c : ℕ} (hac : a ≤ c) :
    Spelled ℓ x a (c + 1) ↔ Spelled ℓ x a c ∧ ℓ (c + 1) = some x := by
  simp only [spelled_iff]
  refine ⟨fun h ↦ ⟨fun s h₁ h₂ ↦ h s h₁ (by omega), h _ (by omega) le_rfl⟩, fun h s h₁ h₂ ↦ ?_⟩
  rcases Nat.lt_or_ge s (c + 1) with hs | hs
  · exact h.1 s h₁ (by omega)
  · rw [show s = c + 1 by omega]
    exact h.2

variable [DecidableEq X]

/-- The shift matrix of the letter `x`: it has an entry `1` at `(s - 1, s)` for each position
`s` spelled with `x`, and is zero elsewhere. -/
private def shift (x : X) : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p) :=
  Matrix.of fun a b ↦ if (b : ℕ) = a + 1 ∧ ℓ b = some x then 1 else 0

private theorem shift_pow_apply (x : X) (j : ℕ) (a b : Fin (D + 1)) :
    (shift (p := p) ℓ D x ^ j) a b =
      if (b : ℕ) = a + j ∧ Spelled ℓ x a b then 1 else 0 := by
  induction j generalizing b with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left rfl, ite_eq_left ⟨rfl, (spelled_iff ℓ).2 fun s h₁ h₂ ↦ absurd h₂ (by omega)⟩]
    · rw [ite_eq_right hab, ite_eq_right fun h ↦ hab (Fin.ext (by omega))]
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply]
    by_cases hb : (b : ℕ) = a + j + 1
    · rw [Fintype.sum_eq_single (⟨a + j, by omega⟩ : Fin (D + 1))]
      · have key := spelled_succ_iff ℓ (x := x) (le_add_right (le_refl (a : ℕ)) : (a : ℕ) ≤ a + j)
        rw [ih]
        simp only [shift, Matrix.of_apply, hb, ← add_assoc]
        by_cases h₁ : Spelled ℓ x a (a + j) <;> by_cases h₂ : ℓ (a + j + 1) = some x <;>
          simp [h₁, h₂, key]
      · intro c hc
        have hc' : (c : ℕ) ≠ a + j := fun h ↦ hc (Fin.ext h)
        rw [ih, ite_eq_right fun h ↦ hc' h.1, zero_mul]
    · rw [ite_eq_right fun h ↦ hb (by omega)]
      refine Finset.sum_eq_zero fun c _ ↦ ?_
      by_cases hc : (c : ℕ) = a + j
      · have : ¬ ((b : ℕ) = c + 1 ∧ ℓ b = some x) := fun h ↦ hb (by omega)
        simp [shift, this]
      · rw [ih, ite_eq_right fun h ↦ hc h.1, zero_mul]

private theorem one_add_shift_pow_apply (x : X) (n : ℕ) (a b : Fin (D + 1)) :
    ((1 + shift (p := p) ℓ D x) ^ n) a b =
      if (a : ℕ) ≤ b ∧ Spelled ℓ x a b then (n.choose (b - a) : ZMod p) else 0 := by
  rw [add_comm (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)), (Commute.one_right _).add_pow,
    Matrix.sum_apply]
  simp only [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, shift_pow_apply, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [Finset.sum_eq_single ((b : ℕ) - a)]
    · rw [ite_eq_left ⟨by omega, h.2⟩]
    · intro j _ hj
      rw [ite_eq_right fun h' ↦ hj (by omega)]
    · intro hj
      rw [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, ite_self]
  · exact Finset.sum_eq_zero fun j _ ↦ ite_eq_right fun h' ↦ h ⟨by omega, h'.2⟩

omit [DecidableEq X] in
/-- A strictly upper triangular matrix raised to the power `j` is supported on entries `(a, b)`
with `a + j ≤ b`. -/
private theorem pow_apply_ne_zero_le {R : Type*} [CommRing R]
    {N : Matrix (Fin (D + 1)) (Fin (D + 1)) R} (hN : ∀ a b, b ≤ a → N a b = 0) (j : ℕ)
    (a b : Fin (D + 1)) (h : (N ^ j) a b ≠ 0) : (a : ℕ) + j ≤ b := by
  induction j generalizing b with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    split_ifs at h with hab
    · subst hab; simp
    · exact absurd rfl h
  | succ j ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h₁ := ih c (left_ne_zero_of_mul hc)
    have h₂ : c < b := lt_of_not_ge fun hbc ↦ right_ne_zero_of_mul hc (hN c b hbc)
    have : (c : ℕ) < b := h₂
    omega

omit [DecidableEq X] in
variable (p) in
/-- Upper unitriangularity of a square matrix over `ZMod p`. -/
private def IsUnitri (M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) : Prop :=
  ∀ a b, b ≤ a → M a b = (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) a b

omit [DecidableEq X] in
private theorem IsUnitri.mul {M M' : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)}
    (hM : IsUnitri p D M) (hM' : IsUnitri p D M') : IsUnitri p D (M * M') := by
  intro a b hab
  rw [Matrix.mul_apply, Fintype.sum_eq_single a]
  · rw [hM a a le_rfl, hM' a b hab, Matrix.one_apply_eq, one_mul]
  · intro c hca
    rcases lt_or_gt_of_ne hca with h | h
    · rw [hM a c h.le, Matrix.one_apply_ne (Ne.symm hca), zero_mul]
    · rw [hM' c b (hab.trans h.le), Matrix.one_apply_ne (ne_of_gt (lt_of_le_of_lt hab h)),
        mul_zero]

omit [DecidableEq X] in
private theorem IsUnitri.pow {M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)}
    (hM : IsUnitri p D M) (k : ℕ) : IsUnitri p D (M ^ k) := by
  induction k with
  | zero => exact fun _ _ _ ↦ rfl
  | succ k ih => rw [pow_succ]; exact ih.mul D hM

private theorem isUnitri_one_add_shift (x : X) : IsUnitri p D (1 + shift ℓ D x) := by
  intro a b hab
  have : ¬ ((b : ℕ) = a + 1 ∧ ℓ b = some x) := fun h ↦ by
    have : (b : ℕ) ≤ a := hab
    omega
  simp [shift, this]

variable [hp : Fact p.Prime]

omit [DecidableEq X] in
/-- An upper unitriangular matrix over `ZMod p` of size `D + 1` has order dividing
`p ^ (D + 1)`. -/
private theorem IsUnitri.pow_eq_one {M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)}
    (hM : IsUnitri p D M) : M ^ p ^ (D + 1) = 1 := by
  have hN : ∀ a b, b ≤ a → (M - 1) a b = 0 := fun a b hab ↦ by
    rw [Matrix.sub_apply, hM a b hab, sub_self]
  have hnil : (M - 1) ^ (D + 1) = 0 := by
    ext a b
    by_contra h
    have := pow_apply_ne_zero_le D hN (D + 1) a b h
    omega
  calc M ^ p ^ (D + 1) = (1 + (M - 1)) ^ p ^ (D + 1) := by rw [add_sub_cancel]
    _ = 1 := by
      rw [add_pow_char_pow_of_commute p (D + 1) (Commute.one_left _), one_pow,
        pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le hnil, add_zero]

omit [DecidableEq X] in
/-- The subgroup of upper unitriangular matrices over `ZMod p`. -/
private def unitriangular : Subgroup (Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))ˣ where
  carrier := {u | IsUnitri p D u}
  one_mem' := fun _ _ _ ↦ rfl
  mul_mem' {u v} hu hv := by
    rw [Set.mem_ofPred, Units.val_mul]
    exact hu.mul D hv
  inv_mem' {u} hu := by
    have hpow : u ^ p ^ (D + 1) = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hu.pow_eq_one D)
    have hinv : u⁻¹ = u ^ (p ^ (D + 1) - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
        Nat.sub_add_cancel (Nat.one_le_pow _ _ hp.out.pos), hpow]
    rw [hinv, Set.mem_ofPred, Units.val_pow_eq_pow_val]
    exact hu.pow D _

omit [DecidableEq X] in
private theorem isPGroup_unitriangular : IsPGroup p (unitriangular (p := p) D) := fun u ↦
  ⟨D + 1, Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact IsUnitri.pow_eq_one D u.2))⟩

/-- The generator `x` as the unitriangular matrix `1 + Nₓ`. -/
private def generator (x : X) : unitriangular (p := p) D :=
  ⟨Units.ofPowEqOne _ (p ^ (D + 1)) ((isUnitri_one_add_shift ℓ D x).pow_eq_one D)
      (pow_pos hp.out.pos _).ne',
    isUnitri_one_add_shift ℓ D x⟩

/-- The representation of the free group by upper unitriangular matrices. -/
private def rep : FreeGroup X →* unitriangular (p := p) D :=
  lift (generator ℓ D)

/-- The image of `x ^ e` is a natural power of `1 + Nₓ`, with exponent `e` reduced modulo
`p ^ (D + 1)`. -/
private theorem coe_rep_of_zpow (x : X) (e : ℤ) :
    (((rep (p := p) ℓ D (of x ^ e) : unitriangular (p := p) D) :
        (Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))ˣ) :
        Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) =
      (1 + shift ℓ D x) ^ (e % (p ^ (D + 1) : ℕ)).toNat := by
  have hpow : generator (p := p) ℓ D x ^ p ^ (D + 1) = 1 := Subtype.ext (Units.ext (by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
    exact IsUnitri.pow_eq_one D (generator ℓ D x).2))
  rw [rep, map_zpow, lift_apply_of, zpow_eq_zpow_emod' e hpow,
    ← Int.toNat_of_nonneg (Int.emod_nonneg _ (Nat.cast_ne_zero.2 (pow_pos hp.out.pos _).ne')),
    zpow_natCast, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  rfl

end Matrices

section Binomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- If `n ≡ e` modulo a power of `p` beyond `v_p(e)`, then `n.choose (p ^ v_p(e))` is nonzero
modulo `p`. -/
private theorem choose_emod_ne_zero {e : ℤ} (he : e ≠ 0) {K : ℕ} (hK : padicValInt p e < K) :
    (((e % (p ^ K : ℕ)).toNat.choose (p ^ padicValInt p e) : ℕ) : ZMod p) ≠ 0 := by
  set v := padicValInt p e
  set n := (e % (p ^ K : ℕ)).toNat
  have hn : (n : ℤ) = e % (p ^ K : ℕ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Nat.cast_ne_zero.2 (pow_pos hp.out.pos _).ne'))
  have hdvd : ∀ k ≤ K, ((p ^ k : ℕ) ∣ n ↔ (p : ℤ) ^ k ∣ e) := fun k hk ↦ by
    rw [← Int.natCast_dvd_natCast, hn, Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero,
      Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow p hk))]
    simp
  obtain ⟨m, hm⟩ := (hdvd v hK.le).2 (padicValInt_dvd e)
  have hpm : ¬ p ∣ m := fun ⟨c, hc⟩ ↦ by
    have := (hdvd (v + 1) hK).1 ⟨c, by rw [hm, hc, pow_succ, mul_assoc]⟩
    rw [padicValInt_dvd_iff] at this
    omega
  have hmod := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := v) (a := m) (b := 1)
  rw [mul_one, Nat.choose_one_right] at hmod
  rw [hm, (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, Ne, ZMod.natCast_eq_zero_iff]
  exact hpm

end Binomial

section Tracking

variable (p : ℕ)

/-- The length `p ^ v_p(e)` given to a syllable with exponent `e`. -/
private def weight (e : ℤ) : ℕ :=
  p ^ padicValInt p e

/-- The letters spelling `x₁ ^ t₁ ⋯ x_k ^ t_k` in positions `1, 2, …`, where `tᵢ` is the weight
of the `i`-th syllable. -/
private def letters : List (X × ℤ) → ℕ → Option X
  | [], _ => none
  | a :: s, j => if j ≤ weight p a.2 then some a.1 else letters s (j - weight p a.2)

/-- The total weight of a syllable list. -/
private def totalWeight (s : List (X × ℤ)) : ℕ :=
  (s.map fun a ↦ weight p a.2).sum

variable {p} (ℓ : ℕ → Option X) (D : ℕ)

/-- The positions `L + 1, …, D` spell the syllable list `s` with the weights. -/
private def Spells : ℕ → List (X × ℤ) → Prop
  | L, [] => L = D
  | L, a :: s => Spelled ℓ a.1 L (L + weight p a.2) ∧ Spells (L + weight p a.2) s

private theorem Spells.le {L : ℕ} {s : List (X × ℤ)} (h : Spells (p := p) ℓ D L s) : L ≤ D := by
  induction s generalizing L with
  | nil => exact le_of_eq h
  | cons a s ih => exact (Nat.le_add_right _ _).trans (ih h.2)

private theorem spells_letters (s : List (X × ℤ)) (L : ℕ)
    (hℓ : ∀ j, 0 < j → ℓ (L + j) = letters p s j) (hD : L + totalWeight p s = D) :
    Spells (p := p) ℓ D L s := by
  induction s generalizing L with
  | nil =>
    simp only [Spells]
    simpa [totalWeight] using hD
  | cons a s ih =>
    refine ⟨(spelled_iff ℓ).2 fun j h₁ h₂ ↦ ?_, ih _ (fun j hj ↦ ?_) ?_⟩
    · rw [show j = L + (j - L) by omega, hℓ _ (by omega), letters, ite_eq_left (by omega)]
    · rw [add_assoc, hℓ _ (by omega), letters, ite_eq_right (by omega), Nat.add_sub_cancel_left]
    · simp only [totalWeight, List.map_cons, List.sum_cons] at hD ⊢
      omega

/-- The first row of `R` is supported in the columns `≤ L` and is nonzero in column `L`. -/
private def RowInv (R : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) (L : ℕ) : Prop :=
  (∀ b : Fin (D + 1), R 0 b ≠ 0 → (b : ℕ) ≤ L) ∧ ∀ b : Fin (D + 1), (b : ℕ) = L → R 0 b ≠ 0

variable [hp : Fact p.Prime]

/-- One syllable step: multiplying by a matrix supported on runs of `x`, whose entry across the
run `(L, L + t]` is nonzero, moves the first-row invariant from `L` to `L + t`, provided the run
is maximal. -/
private theorem RowInv.mul {R M : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)} {L t : ℕ} {x : X}
    (hR : RowInv D R L) (hLt : L + t ≤ D) (hprev : L = 0 ∨ ℓ L ≠ some x)
    (hnext : L + t = D ∨ ℓ (L + t + 1) ≠ some x)
    (hM : ∀ a b : Fin (D + 1), M a b ≠ 0 → Spelled ℓ x a b)
    (hMv : ∀ a b : Fin (D + 1), (a : ℕ) = L → (b : ℕ) = L + t → M a b ≠ 0) :
    RowInv D (R * M) (L + t) := by
  constructor
  · intro b hb
    rw [Matrix.mul_apply] at hb
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
    have h₁ := hR.1 a (left_ne_zero_of_mul ha)
    have h₂ := (spelled_iff ℓ).1 (hM a b (right_ne_zero_of_mul ha))
    by_contra hlt
    rcases hnext with h | h
    · exact hlt (by omega)
    · exact h (h₂ _ (by omega) (by omega))
  · intro b hb
    rw [Matrix.mul_apply, Fintype.sum_eq_single (⟨L, by omega⟩ : Fin (D + 1))]
    · exact mul_ne_zero (hR.2 _ rfl) (hMv _ _ rfl hb)
    · intro a ha
      by_contra hne
      have haL := hR.1 a (left_ne_zero_of_mul hne)
      have haL' : (a : ℕ) < L := lt_of_le_of_ne haL fun h ↦ ha (Fin.ext h)
      have h₂ := (spelled_iff ℓ).1 (hM a b (right_ne_zero_of_mul hne))
      rcases hprev with h | h
      · omega
      · exact h (h₂ _ haL' (by omega))

private theorem one_le_weight (e : ℤ) : 1 ≤ weight p e :=
  Nat.one_le_pow _ _ hp.out.pos

variable [DecidableEq X]

/-- The first-row invariant is carried through the image of a normal syllable list spelled by
the positions after `L`. -/
private theorem RowInv.mul_rep (s : List (X × ℤ)) (hs : IsSyllableNormal s) (L : ℕ)
    (hL : Spells (p := p) ℓ D L s) (R : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))
    (hR : RowInv D R L) (hprev : ∀ a ∈ s.head?, L = 0 ∨ ℓ L ≠ some a.1) :
    RowInv D (R * (((rep (p := p) ℓ D (syllableProd s) : unitriangular (p := p) D) :
      (Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))ˣ) :
      Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))) D := by
  induction s generalizing L R with
  | nil =>
    obtain rfl : L = D := hL
    simpa using hR
  | cons a s ih =>
    obtain ⟨x, e⟩ := a
    obtain ⟨hs0, hsc⟩ := hs
    obtain ⟨hrun, hL'⟩ := hL
    have hLt : L + weight p e ≤ D := hL'.le
    have hrunx : ℓ (L + weight p e) = some x :=
      (spelled_iff ℓ).1 hrun _ (by have := one_le_weight (p := p) e; omega) le_rfl
    rw [syllableProd_cons, _root_.map_mul, Subgroup.coe_mul, Units.val_mul, ← mul_assoc]
    -- Apply the one-syllable step to `x ^ e`, then continue with the remaining syllables.
    refine ih ⟨fun a ha ↦ hs0 a (List.mem_cons_of_mem _ ha), hsc.tail⟩ _ hL' _
      (RowInv.mul ℓ D hR hLt (hprev (x, e) rfl) ?_ ?_ ?_) ?_
    -- The run of `x` ends at `L + weight p e`: the next syllable has a different letter.
    · cases s with
      | nil => exact Or.inl hL'
      | cons c s =>
        right
        rw [(spelled_iff ℓ).1 hL'.1 _ (by omega)
          (by have := one_le_weight (p := p) c.2; omega)]
        exact fun h ↦ (List.isChain_cons_cons.mp hsc).1 (Option.some_injective _ h).symm
    -- The image of `x ^ e` is supported on runs of `x`.
    · intro a b hab
      rw [coe_rep_of_zpow, one_add_shift_pow_apply] at hab
      by_contra h
      exact hab (ite_eq_right fun h' ↦ h h'.2)
    -- Its entry across the run is a binomial coefficient that is nonzero modulo `p`.
    · intro a b ha hb
      dsimp only at hb ⊢
      rw [coe_rep_of_zpow, one_add_shift_pow_apply, ite_eq_left ⟨by omega, by rwa [ha, hb]⟩,
        show (b : ℕ) - a = p ^ padicValInt p e by rw [ha, hb]; simp [weight]]
      refine choose_emod_ne_zero (e := e) (hs0 _ List.mem_cons_self) ?_
      have := Nat.lt_pow_self hp.out.one_lt (n := padicValInt p e)
      have : weight p e ≤ D := by omega
      simp only [weight] at this
      omega
    -- Position `L + weight p e` is spelled `x`, which differs from the next syllable's letter.
    · intro c hc
      right
      rw [hrunx]
      cases s with
      | nil => simp at hc
      | cons d s =>
        obtain rfl : d = c := by simpa using hc
        exact fun h ↦ (List.isChain_cons_cons.mp hsc).1 (Option.some_injective _ h)

end Tracking

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Free groups are residually `p`.** A nontrivial element of a free group lies outside some
normal subgroup of finite index whose quotient is a `p`-group. -/
theorem exists_normal_isPGroup_quotient_notMem {w : FreeGroup X} (hw : w ≠ 1) :
    ∃ (N : Subgroup (FreeGroup X)) (_ : N.Normal),
      N.FiniteIndex ∧ IsPGroup p (FreeGroup X ⧸ N) ∧ w ∉ N := by
  classical
  obtain ⟨s, hs, rfl⟩ := exists_isSyllableNormal w
  have hs₀ : s ≠ [] := by rintro rfl; exact hw rfl
  let D := totalWeight p s
  let ρ := rep (p := p) (letters p s) D
  refine ⟨ρ.ker, inferInstance, inferInstance,
    (isPGroup_unitriangular D).of_injective _ (QuotientGroup.kerLift_injective ρ), fun hmem ↦ ?_⟩
  have hD : 0 < D := by
    obtain ⟨a, s', rfl⟩ := List.exists_cons_of_ne_nil hs₀
    have := one_le_weight (p := p) a.2
    simp only [D, totalWeight, List.map_cons, List.sum_cons]
    omega
  have hR : RowInv D (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) 0 := by
    refine ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
    · by_contra h
      exact hb (Matrix.one_apply_ne fun h' ↦ h (by rw [← h']; rfl))
    · rw [show b = 0 from Fin.ext hb, Matrix.one_apply_eq]
      exact one_ne_zero
  have := (RowInv.mul_rep (letters p s) D s hs 0
    (spells_letters _ _ s 0 (fun j _ ↦ by rw [zero_add]) (zero_add _)) 1 hR
    (fun _ _ ↦ Or.inl rfl)).2 ⟨D, by omega⟩ rfl
  rw [MonoidHom.mem_ker.mp hmem, one_mul] at this
  exact this (Matrix.one_apply_ne fun h ↦ by simp [Fin.ext_iff] at h; omega)

/-- Free groups are residually finite. -/
instance instResiduallyFinite : Group.ResiduallyFinite (FreeGroup X) :=
  Group.residuallyFinite_iff_exists_finiteIndex.mpr fun _ hw ↦
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let ⟨N, _, hN, _, hwN⟩ := exists_normal_isPGroup_quotient_notMem (p := 2) hw
    ⟨N, hN, hwN⟩


end FreeGroup
