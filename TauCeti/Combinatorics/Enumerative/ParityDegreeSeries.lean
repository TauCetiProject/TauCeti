/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Int.Interval
import TauCeti.InformationTheory.Coding.Binary.Basic
public import TauCeti.InformationTheory.Coding.Weight.Enumerator
import TauCeti.RingTheory.PowerSeries.ProdOneSubXPow

/-!
# Counting integer degree vectors with prescribed parities

Fix a finite coordinate type `ι` with `N` elements, a lower bound `N₀ : ℕ` and a set `C` of
parity vectors in `𝔽₂^ι`. This file computes the generating series, by total degree, of the
integer vectors `m : ι → ℤ` whose coordinates are all at least `N₀` and whose reduction modulo `2`
lies in `C`:

  `∑ₙ #{m | (∀ i, N₀ ≤ m i) ∧ (m mod 2) ∈ C ∧ ∑ i, m i = n} Xⁿ
    = X^(N N₀) W(X) (1 - X²)^(-N)`,

where `W` is the one-variable weight enumerator `Set.weightPolynomial` of the translate
`{ε + N₀ · 𝟙 | ε ∈ C}` of `C`. Such counts arise for the degree vectors of fixed fibers in the
fixed-point formulas for power actions on marked central extensions (Wood), where the parities
`ε` of the degrees that admit fixed points form an affine subspace of `𝔽₂^ι`.

The computation rests on the lower-bound translation `TauCeti.natEquivLowerBoundParity`: an
integer `x` satisfies `N₀ ≤ x` and `x ≡ e (mod 2)` exactly when `x = N₀ + r + 2 k` for a unique
`k : ℕ`, where `r = (e + N₀).val ∈ {0, 1}`. Summing over the coordinates, the total degree of
a vector with parity `ε` is `N N₀ + wt (ε + N₀ · 𝟙) + 2 ∑ k i`, and the vectors `k : ι → ℕ` are
counted by the `N`-th power of `(1 - X²)⁻¹`. The translation by `N₀ · 𝟙` matters: the series for
the two parities with `N = 1`, `N₀ = 1` are `X² / (1 - X²)` for `C = {0}` and `X / (1 - X²)` for
`C = {1}`.

## Main definitions and statements

* `TauCeti.natEquivLowerBoundParity N₀ e`: the parametrization `k ↦ N₀ + (e + N₀).val + 2 k` of
  the integers that are at least `N₀` and congruent to `e` modulo `2`.
* `TauCeti.mk_natCard_parityDegrees_eq`: the generating series of the integer degree vectors
  with coordinates at least `N₀` and parity in `C`.

## References

* M. M. Wood, *Nonabelian Cohen–Lenstra moments*, Duke Math. J. 168 (2019), no. 3, 377–427,
  §4.1, Proposition 4.1 and equation (6).
-/

public section

open Finset PowerSeries

namespace TauCeti

/-! ### The lower-bound translation -/

/-- **The lower-bound translation.** The integers `x` with `N₀ ≤ x` and `x ≡ e (mod 2)` are
exactly the integers `N₀ + (e + N₀).val + 2 k` for `k : ℕ`, and `k` is determined by `x`. Here
`(e + N₀).val ∈ {0, 1}` is the least excess over `N₀` with the parity `e`. -/
@[expose, simps apply_coe symm_apply]
def natEquivLowerBoundParity (N₀ : ℕ) (e : ZMod 2) :
    ℕ ≃ {x : ℤ // (N₀ : ℤ) ≤ x ∧ (x : ZMod 2) = e} where
  toFun k := ⟨N₀ + (e + N₀).val + 2 * k, by omega, by
    push_cast [ZMod.natCast_zmod_val]
    linear_combination ((N₀ : ZMod 2) + k) * (by decide : (2 : ZMod 2) = 0)⟩
  invFun x := (x.val - N₀).toNat / 2
  left_inv k := by
    have := ZMod.val_lt (e + (N₀ : ZMod 2))
    dsimp only
    omega
  right_inv := by
    rintro ⟨x, hx, rfl⟩
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, x = N₀ + d := ⟨(x - N₀).toNat, by omega⟩
    have hval : (((N₀ + d : ℤ) : ZMod 2) + N₀).val = d % 2 := by
      rw [show ((N₀ + d : ℤ) : ZMod 2) + N₀ = ((d + 2 * N₀ : ℕ) : ZMod 2) by push_cast; ring,
        ZMod.val_natCast]
      omega
    ext
    simp only [hval]
    omega

/-! ### The generating series -/

variable {ι : Type*} [Fintype ι]

/-- The integer degree vectors with coordinates at least `N₀`, parity `ε` and total degree `n`
correspond to the vectors `k : ι → ℕ` with `a + 2 ∑ i, k i = n`, where
`a = #ι · N₀ + wt (ε + N₀ · 𝟙)` is the least total degree with these constraints. -/
private def parityDegreesEquiv (N₀ : ℕ) (ε : ι → ZMod 2) (n : ℕ) :
    {k : ι → ℕ // Fintype.card ι * N₀ + hammingNorm (fun i ↦ ε i + N₀) + 2 * ∑ i, k i = n} ≃
      {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧ (fun i ↦ (m i : ZMod 2)) = ε ∧
        ∑ i, m i = (n : ℤ)} :=
  (Equiv.subtypeEquiv (q := fun m : {m : ι → ℤ // ∀ i, (N₀ : ℤ) ≤ m i ∧ (m i : ZMod 2) = ε i} ↦
    ∑ i, m.val i = n)
    ((Equiv.piCongrRight fun i ↦ natEquivLowerBoundParity N₀ (ε i)).trans
      Equiv.subtypePiEquivPi.symm) fun k ↦ by
    simp only [Equiv.subtypePiEquivPi, Equiv.trans_apply, Equiv.coe_fn_symm_mk,
      Equiv.piCongrRight_apply, Pi.map_apply, natEquivLowerBoundParity_apply_coe,
      sum_add_distrib, sum_const, card_univ, ← mul_sum, nsmul_eq_mul]
    rw [← sum_val_eq_hammingNorm, ← Nat.cast_inj (R := ℤ)]
    push_cast
    constructor <;> intro h <;> linear_combination h).trans <|
  (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun m : ι → ℤ ↦ ∀ i, (N₀ : ℤ) ≤ m i ∧ (m i : ZMod 2) = ε i) (fun m ↦ ∑ i, m i = n)).trans <|
    Equiv.subtypeEquivRight fun m ↦ by
    simp only [funext_iff, forall_and, and_assoc]

/-- The generating series of the integer degree vectors with coordinates at least `N₀` and the
single parity vector `ε`. -/
private theorem mk_natCard_parity_eq (N₀ : ℕ) (ε : ι → ZMod 2) :
    mk (fun n : ℕ ↦ (Nat.card {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧
      (fun i ↦ (m i : ZMod 2)) = ε ∧ ∑ i, m i = (n : ℤ)} : ℤ)) =
      X ^ (Fintype.card ι * N₀ + hammingNorm (fun i ↦ ε i + N₀)) *
        invOfUnit (1 - X ^ 2 : ℤ⟦X⟧) 1 ^ Fintype.card ι := by
  -- The vectors `k : ι →₀ ℕ`, counted by their weight `∑ i, 2 * k i`, have generating series
  -- `(1 - X²)^(-#ι)`: both series invert `(1 - X²)^#ι`.
  have hinv : mk (fun n ↦ (Nat.card {k : ι →₀ ℕ // Finsupp.weight (fun _ ↦ 2) k = n} : ℤ)) =
      invOfUnit (1 - X ^ 2 : ℤ⟦X⟧) 1 ^ Fintype.card ι := by
    have h₁ := mk_natCard_weight_mul_prod_one_sub_X_pow (R := ℤ) (d := fun _ : ι ↦ 2)
      fun _ ↦ two_ne_zero
    rw [prod_const, card_univ] at h₁
    have h₂ : invOfUnit (1 - X ^ 2 : ℤ⟦X⟧) 1 ^ Fintype.card ι * (1 - X ^ 2) ^ Fintype.card ι =
        1 := by
      rw [← mul_pow, invOfUnit_mul _ _ (by simp), one_pow]
    linear_combination (invOfUnit (1 - X ^ 2 : ℤ⟦X⟧) 1 ^ Fintype.card ι) * h₁ -
      mk (fun n ↦ (Nat.card {k : ι →₀ ℕ // Finsupp.weight (fun _ ↦ 2) k = n} : ℤ)) * h₂
  ext n
  rw [coeff_mk, coeff_X_pow_mul', ← hinv, coeff_mk, ← Nat.card_congr (parityDegreesEquiv N₀ ε n)]
  split_ifs with h
  · refine congrArg _ (Nat.card_congr (Finsupp.equivFunOnFinite.symm.subtypeEquiv fun k ↦ ?_))
    simp only [Finsupp.weight_apply, Finsupp.sum_fintype, smul_eq_mul, zero_mul, implies_true,
      Finsupp.coe_equivFunOnFinite_symm, ← sum_mul]
    omega
  · rw [Nat.card_eq_zero.mpr (.inl ⟨fun ⟨_, _⟩ ↦ h (by omega)⟩), Nat.cast_zero]

/-- **The parity degree series.** For a set `C` of parity vectors in `𝔽₂^ι` and a lower bound
`N₀ : ℕ`, the generating series, by total degree `n`, of the integer vectors `m : ι → ℤ` with all
coordinates at least `N₀` and reduction modulo `2` in `C` is
`X^(#ι · N₀) · W(X) · (1 - X²)^(-#ι)`, where `W` is the weight polynomial of the translate
`{ε + N₀ · 𝟙 | ε ∈ C}`. -/
theorem mk_natCard_parityDegrees_eq (N₀ : ℕ) (C : Set (ι → ZMod 2)) :
    mk (fun n : ℕ ↦ (Nat.card {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧
      (fun i ↦ (m i : ZMod 2)) ∈ C ∧ ∑ i, m i = (n : ℤ)} : ℤ)) =
      X ^ (Fintype.card ι * N₀) *
        (((fun ε : ι → ZMod 2 ↦ fun i ↦ ε i + (N₀ : ZMod 2)) '' C).weightPolynomial : ℤ⟦X⟧) *
        invOfUnit (1 - X ^ 2 : ℤ⟦X⟧) 1 ^ Fintype.card ι := by
  classical
  have hC := C.toFinite
  -- Split the degree vectors according to their parity vector `ε ∈ C`.
  have hcard (n : ℕ) : Nat.card {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧
      (fun i ↦ (m i : ZMod 2)) ∈ C ∧ ∑ i, m i = (n : ℤ)} =
      ∑ ε ∈ hC.toFinset, Nat.card {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧
        (fun i ↦ (m i : ZMod 2)) = ε ∧ ∑ i, m i = (n : ℤ)} := by
    -- The degree vectors of total degree `n` lie in the finite box `[0, n]^ι`.
    have : Finite {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧ (fun i ↦ (m i : ZMod 2)) ∈ C ∧
        ∑ i, m i = (n : ℤ)} :=
      Finite.of_injective (β := ι → Set.Icc (0 : ℤ) n)
        (fun m i ↦ ⟨m.val i, (Int.natCast_nonneg N₀).trans (m.property.1 i),
          (single_le_sum (fun j _ ↦ (Int.natCast_nonneg N₀).trans (m.property.1 j))
            (mem_univ i)).trans m.property.2.2.le⟩)
        fun _ _ h ↦ Subtype.ext (funext fun i ↦ congrArg Subtype.val (congrFun h i))
    let f : {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧ (fun i ↦ (m i : ZMod 2)) ∈ C ∧
        ∑ i, m i = (n : ℤ)} → hC.toFinset :=
      fun m ↦ ⟨fun i ↦ (m.val i : ZMod 2), by simpa using m.property.2.1⟩
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma, ← sum_coe_sort hC.toFinset]
    refine sum_congr rfl fun ε _ ↦ Nat.card_congr <|
      (Equiv.subtypeEquivRight fun _ ↦ Subtype.ext_iff).trans <|
      (Equiv.subtypeSubtypeEquivSubtypeInter _
        (fun m : ι → ℤ ↦ (fun i ↦ (m i : ZMod 2)) = ε.val)).trans <|
      Equiv.subtypeEquivRight fun m ↦ ?_
    have hε : ε.val ∈ C := by simpa using ε.property
    exact ⟨fun ⟨⟨h₁, _, h₃⟩, h₂⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂ ▸ hε, h₃⟩, h₂⟩⟩
  have hmk : mk (fun n : ℕ ↦ (Nat.card {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧
      (fun i ↦ (m i : ZMod 2)) ∈ C ∧ ∑ i, m i = (n : ℤ)} : ℤ)) =
      ∑ ε ∈ hC.toFinset, mk (fun n : ℕ ↦ (Nat.card {m : ι → ℤ // (∀ i, (N₀ : ℤ) ≤ m i) ∧
        (fun i ↦ (m i : ZMod 2)) = ε ∧ ∑ i, m i = (n : ℤ)} : ℤ)) := by
    ext n
    simp [hcard, map_sum]
  rw [hmk, Set.weightPolynomial_eq_sum (Set.toFinite _), Set.Finite.toFinset_image _ hC,
    sum_image fun _ _ _ _ h ↦ funext fun i ↦ add_right_cancel (congrFun h i)]
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
  simp [mk_natCard_parity_eq, mul_sum, sum_mul, pow_add]

end TauCeti
