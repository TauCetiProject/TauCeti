/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Syllables
public import TauCeti.LinearAlgebra.Matrix.UnitriangularP
public import TauCeti.NumberTheory.Binomial.PadicVal
public import Mathlib.GroupTheory.ResiduallyFinite

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

The proof uses finite upper unitriangular representations over `ZMod p`, in the spirit of the
Magnus embedding reduced modulo `p`.

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

private theorem isUnitri_one_add_shift (x : X) : IsUnitri p D (1 + shift ℓ D x) := by
  unfold IsUnitri
  intro a b hab
  have : ¬ ((b : ℕ) = a + 1 ∧ ℓ b = some x) := fun h ↦ by
    have : (b : ℕ) ≤ a := hab
    omega
  simp [shift, this]

variable [hp : Fact p.Prime]

/-- The generator `x` as the unitriangular matrix `1 + Nₓ`. -/
private def generator (x : X) : unitriangular (p := p) D :=
  ⟨Units.ofPowEqOne _ (p ^ (D + 1)) ((isUnitri_one_add_shift ℓ D x).pow_eq_one D)
      (pow_pos hp.out.pos _).ne',
    isUnitri_one_add_shift ℓ D x⟩

private theorem generator_val (x : X) :
    (((generator (p := p) ℓ D x : unitriangular (p := p) D) :
        (Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p))ˣ) :
        Matrix (Fin (D + 1)) (Fin (D + 1)) (ZMod p)) = 1 + shift ℓ D x := by
  simp only [generator, Units.val_ofPowEqOne]

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
    zpow_natCast, Subgroup.coe_pow, Units.val_pow_eq_pow_val, generator_val]
  congr 1

end Matrices

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
    obtain ⟨hs0, hsc⟩ := (show (∀ a ∈ (x, e) :: s, a.2 ≠ 0) ∧
      ((x, e) :: s).IsChain (fun a b ↦ a.1 ≠ b.1) from hs)
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
      refine TauCeti.choose_emod_ne_zero (e := e) (hs0 _ List.mem_cons_self) ?_
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

/-
For a nontrivial normal syllable word `x₁ ^ e₁ ⋯ x_k ^ e_k`, assign syllable `i` a run of
`p ^ v_p(eᵢ)` positions spelled with `xᵢ`. The generator `x` acts by `1 + shift ℓ D x`.
Its `n`th power has entry `n.choose (b - a)` when `a ≤ b` and `(a, b]` is spelled with `x`,
and zero otherwise. Following the first row through successive syllables gives a nonzero
entry at the end of the word by Lucas' theorem.
-/

/-- **Free groups are residually `p`.** A nontrivial element of a free group lies outside some
normal subgroup of finite index whose quotient is a `p`-group. -/
theorem exists_normal_isPGroup_quotient_notMem {w : FreeGroup X} (hw : w ≠ 1) :
    ∃ (N : Subgroup (FreeGroup X)) (_ : N.Normal),
      N.FiniteIndex ∧ IsPGroup p (FreeGroup X ⧸ N) ∧ w ∉ N := by
  classical
  obtain ⟨s, hs, rfl⟩ := exists_isSyllableNormal w
  have hs₀ : s ≠ [] := by rintro rfl; exact hw (by simp)
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
