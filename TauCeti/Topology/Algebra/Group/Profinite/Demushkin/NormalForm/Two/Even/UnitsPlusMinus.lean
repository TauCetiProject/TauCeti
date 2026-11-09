/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Exact
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Character.Image
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Equiv
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ElementaryAutomorphism
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CrossedHom
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.PadicModule
public import TauCeti.NumberTheory.Padics.TwistedUnits
import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Labute.RelatorCharacter

/-!
# Labute's normal form for the dyadic Demushkin groups of even rank with image `{±1} × U^(f)`

Let `G` be a Demushkin group at `p = 2` of even rank `n ≥ 4` whose canonical character has image
`V^(f) = {±1} × U^(f)` for a finite `f ≥ 2`. Labute's Theorem 6 says that `G` is presented on
`n` generators by the single relator `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, the
normal-form word `TauCeti.demushkinWordTwoEven 0 f n`; in particular two such groups with the same
rank and the same `f` are topologically isomorphic. This file proves that theorem, from the exact
normal form of the dyadic relators of even rank
(`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Exact`), the values of
the canonical character forced by that normal form, the symplectic transvection pair
`TauCeti.freeProP.symplecticTransvection` of
`TauCeti.Topology.Algebra.Group.Profinite.Free.ElementaryAutomorphism`, which adjusts the
character value at `x₂`, and the constrained successive approximation of
`TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Two.Even.Approximation`.

## Main results

* `TauCeti.freeProP.gradedMap_symplecticTransvection_gradedMk_demushkinWordNeTwo`: the symplectic
  transvection pair `x₂ ↦ x₂ x₄^c`, `x₃ ↦ x₃ x₁^{-c}` fixes the class of
  `x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1(F)`.
* `TauCeti.freeProP.apply_eq_of_forall_isCrossedHom_eq_zero_padicPow_mul_labuteComm_mul`: the
  values of a character of `F` all of whose continuous crossed homomorphisms kill the exact
  normal-form relator `x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)`.
* `TauCeti.freeProP.exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq`:
  **Labute's Theorem 6, relator form**: a relator of `F` presenting a Demushkin group of even rank
  `n ≥ 4` whose canonical character has image `{±1} × U^(f)` is carried to
  `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)` by a continuous automorphism of `F`.
* `TauCeti.freeProP.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq`
  and its intrinsic form
  `TauCeti.IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq`:
  such a Demushkin group is topologically isomorphic to
  `⟨x₁, …, x_n ∣ x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` on `n = demushkinRank hG`
  generators.
* `TauCeti.IsDemushkin.nonempty_continuousMulEquiv_of_even_demushkinRank_of_range_eq_unitsPlusMinus`
  is **uniqueness**: two Demushkin groups at `p = 2` of the same even rank `n ≥ 4` whose canonical
  characters have the same image `{±1} × U^(f)` are topologically isomorphic.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §4,
  Theorem 6.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.19).
-/

public section

namespace TauCeti

open Subgroup

universe u v

variable {n : ℕ}

namespace freeProP

/-! ### The symplectic transvection pair and the normal-form word -/

section SymplecticTransvection

variable {p : ℕ} [Fact p.Prime] (hn3 : 3 < n) (c : ℤ_[p])

/-- **The symplectic transvection pair fixes the class of the normal-form word**
`x₁^q (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1(F)`, for `n ≥ 4` and `p ∣ q`. -/
theorem gradedMap_symplecticTransvection_gradedMk_demushkinWordNeTwo {q : ℕ} (hq : p ∣ q) :
    gradedMap p
        (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).continuous 1
        (gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo q n (freeProPGen p n),
          demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩) =
      gradedMk p (freeProP p (Fin n)) 1 ⟨demushkinWordNeTwo q n (freeProPGen p n),
        demushkinWordNeTwo_mem_pLowerCentralSeries_one hq n _⟩ := by
  -- The pair fixes `x₁`, so the `p`-power term is unchanged, and the commutator terms
  -- `[ξ₁, c ξ₄]` it creates from `(x₁, x₂)` and `[-c ξ₁, ξ₄]` from `(x₃, x₄)` cancel.
  obtain ⟨k, hk⟩ : ∃ k, n / 2 = k + 2 := ⟨n / 2 - 2, by omega⟩
  have hσ : ∀ m, m ≠ 1 → m ≠ 2 →
      (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
        (freeProPGen p n m) = freeProPGen p n m :=
    fun m hm₁ hm₂ ↦ symplecticTransvection_freeProPGen_of_ne hn3 c m hm₁ hm₂
  have hσ₁ : (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
      (freeProPGen p n 1) =
      freeProPGen p n 1 * (isProP_freeProP p (Fin n)).padicPow (freeProPGen p n 3) c :=
    symplecticTransvection_freeProPGen_one hn3 c
  have hσ₂ : (symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
      (freeProPGen p n 2) =
      freeProPGen p n 2 * (isProP_freeProP p (Fin n)).padicPow (freeProPGen p n 0) (-c) :=
    symplecticTransvection_freeProPGen_two hn3 c
  rw [gradedMk_demushkinWordNeTwo hq, map_add, map_nsmul, map_sum, gradedMap_gradedPow,
    gradedMap_gradedMkZero, hσ 0 (by omega) (by omega)]
  congr 1
  simp only [gradedMap_gradedBracket_zero_zero, gradedMap_gradedMkZero]
  rw [hk, Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ',
    Finset.sum_range_succ']
  have hrest : ∀ i ∈ Finset.range k,
      gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMkZero p _
          ((symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
            (freeProPGen p n (2 * (i + 1 + 1)))))
        (gradedMkZero p _
          ((symplecticTransvection hn3 c : freeProP p (Fin n) →ₜ* freeProP p (Fin n)).toMonoidHom
            (freeProPGen p n (2 * (i + 1 + 1) + 1)))) =
      gradedBracket p (freeProP p (Fin n)) 0 0
        (gradedMkZero p _ (freeProPGen p n (2 * (i + 1 + 1))))
        (gradedMkZero p _ (freeProPGen p n (2 * (i + 1 + 1) + 1))) := fun i _ ↦ by
    rw [hσ _ (by omega) (by omega), hσ _ (by omega) (by omega)]
  rw [Finset.sum_congr rfl hrest]
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, hσ₁, hσ₂, gradedMkZero_mul,
    hσ 0 (by omega) (by omega), hσ 3 (by omega) (by omega), map_add, AddMonoidHom.add_apply]
  have hkey := (isProP_freeProP p (Fin n)).gradedBracket_gradedMkZero_padicPow_neg_add p
    (freeProPGen p n 0) (freeProPGen p n 3) c
  rw [show ∀ S A B C D : gradedPiece p (freeProP p (Fin n)) (0 + 0 + 1),
      S + (A + B) + (C + D) = S + A + C + (B + D) from fun _ _ _ _ _ ↦ by abel, hkey, add_zero]

end SymplecticTransvection

section CharacterValues

variable {χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ} {α : ℤ_[2]} {q : ℕ}
  (hkill : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ D →
    D ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
      labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
      demushkinWordNeTwo q (n - 2) fun i ↦ freeProPGen 2 n (i + 2)) = 0)
include hkill

/-- Under the hypotheses of the character-values theorem, the character is trivial at the generator
`x₁`: the Kronecker crossed homomorphism `D_2` reads `χ(x₁) = 1` off the relator. -/
private theorem apply_freeProPGen_zero_eq_one (hn3 : 3 < n) : χ (freeProPGen 2 n 0) = 1 := by
  have hD := isCrossedHom_crossedHom χ (Pi.single (⟨1, by omega⟩ : Fin n) 1)
  have hv : ∀ j : ℕ, j ≠ 1 → crossedHom χ (Pi.single (⟨1, by omega⟩ : Fin n) 1)
      (freeProPGen 2 n j) = 0 := fun j hj ↦ crossedHom_single_freeProPGen_of_ne χ _ hj
  have h := hkill _ (continuous_crossedHom χ _) hD
  rw [hD.map_mul_mul, hD.map_padicPow_eq_zero_of_eq_zero (continuous_crossedHom χ _)
    (isProP_freeProP 2 (Fin n)) (hv 0 (by omega)),
    hD.map_demushkinWordNeTwo_eq_zero_of_forall_eq_zero _ _ fun j ↦ hv _ (by omega)] at h
  simp only [mul_zero, zero_add, add_zero] at h
  exact hD.eq_one_of_map_labuteComm_eq_zero_right (hv 0 (by omega))
    (crossedHom_single_freeProPGen_self χ _) ((Units.mul_right_eq_zero _).1 h)

/-- A Kronecker crossed homomorphism `D_k`, `k ∈ {2 i₀ + 2, 2 i₀ + 3}` and `k ≠ 2` (the `0`-based
index of the generator `x_{k+1}`), kills the `i₀`-th commutator factor
`(x_{2 i₀ + 3}, x_{2 i₀ + 4})` of the relator. -/
private theorem crossedHom_single_labuteComm_eq_zero {i₀ : ℕ} (hi₀ : i₀ < (n - 2) / 2) (k : Fin n)
    (hk : (k : ℕ) = 2 * i₀ + 2 ∨ (k : ℕ) = 2 * i₀ + 3) (hk₂ : (k : ℕ) ≠ 2) :
    crossedHom χ (Pi.single k 1)
      (labuteComm (freeProPGen 2 n (2 * i₀ + 2)) (freeProPGen 2 n (2 * i₀ + 3))) = 0 := by
  have hD := isCrossedHom_crossedHom χ (Pi.single k 1)
  have hv : ∀ j : ℕ, j ≠ k → crossedHom χ (Pi.single k 1) (freeProPGen 2 n j) = 0 :=
    fun j hj ↦ crossedHom_single_freeProPGen_of_ne χ _ hj
  have h := hkill _ (continuous_crossedHom χ _) hD
  rw [hD.map_mul_mul, hD.map_padicPow_eq_zero_of_eq_zero (continuous_crossedHom χ _)
    (isProP_freeProP 2 (Fin n)) (hv 0 (by omega)),
    hD.map_labuteComm_eq_zero_of_eq_zero (hv 0 (by omega)) (hv 1 (by omega)),
    hD.map_demushkinWordNeTwo_of_forall_eq_zero_of_ne q hi₀
      (x := fun i ↦ freeProPGen 2 n (i + 2)) fun j _ _ ↦ hv (j + 2) (by omega),
    hv 2 fun h ↦ hk₂ h.symm] at h
  simpa [mul_eq_zero, Units.ne_zero] using h

/-- Under the hypotheses of the character-values theorem, the character is trivial at `x_{2 i₀ + 3}`
for every `i₀` (the generator `freeProPGen 2 n (2 i₀ + 2)`): the Kronecker crossed homomorphism at
its partner `x_{2 i₀ + 4}` reads it off. -/
private theorem apply_freeProPGen_eq_one_right {i₀ : ℕ} (hi₀ : i₀ < (n - 2) / 2) :
    χ (freeProPGen 2 n (2 * i₀ + 2)) = 1 :=
  (isCrossedHom_crossedHom χ
    (Pi.single (⟨2 * i₀ + 3, by omega⟩ : Fin n) 1)).eq_one_of_map_labuteComm_eq_zero_right
    (crossedHom_single_freeProPGen_of_ne χ _ (by simp only; omega))
    (crossedHom_single_freeProPGen_self χ _)
    (crossedHom_single_labuteComm_eq_zero hkill hi₀ _ (Or.inr rfl)
      (by simp only; omega))

/-- Under the hypotheses of the character-values theorem, the character is trivial at
`x_{2 i₀ + 4}` for every `i₀ ≥ 1` (the generator `freeProPGen 2 n (2 i₀ + 3)`): the Kronecker
crossed homomorphism at its partner `x_{2 i₀ + 3}` reads it off. -/
private theorem apply_freeProPGen_eq_one_left {i₀ : ℕ} (hi₀ : i₀ < (n - 2) / 2) (hi₁ : 1 ≤ i₀) :
    χ (freeProPGen 2 n (2 * i₀ + 3)) = 1 :=
  (isCrossedHom_crossedHom χ
    (Pi.single (⟨2 * i₀ + 2, by omega⟩ : Fin n) 1)).eq_one_of_map_labuteComm_eq_zero_left
    (crossedHom_single_freeProPGen_self χ _)
    (crossedHom_single_freeProPGen_of_ne χ _ (by simp only; omega))
    (crossedHom_single_labuteComm_eq_zero hkill hi₀ _ (Or.inl rfl)
      (by simp only; omega))

/-- Under the hypotheses of the character-values theorem, the character is trivial at
`freeProPGen 2 n j` (the generator `x_{j+1}`) for every `4 ≤ j < n`, when `n` is even. -/
private theorem apply_freeProPGen_eq_one_of_four_le (hn : Even n) {j : ℕ} (hj₄ : 4 ≤ j)
    (hjn : j < n) : χ (freeProPGen 2 n j) = 1 := by
  obtain ⟨m, hm⟩ := hn
  rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
  · have := apply_freeProPGen_eq_one_right hkill (i₀ := i - 1) (by omega)
    rwa [show 2 * (i - 1) + 2 = 2 * i by omega] at this
  · have := apply_freeProPGen_eq_one_left hkill (i₀ := i - 1) (by omega) (by omega)
    rwa [show 2 * (i - 1) + 3 = 2 * i + 1 by omega] at this

/-- The Kronecker crossed homomorphism `D_1` reads `χ(x₂) (1 + α) = -1` off the relator, once
`χ(x₁) = 1`. -/
private theorem apply_freeProPGen_one_mul_one_add (hn3 : 3 < n) (h0 : χ (freeProPGen 2 n 0) = 1) :
    (χ (freeProPGen 2 n 1) : ℤ_[2]) * (1 + α) = -1 := by
  have hD := isCrossedHom_crossedHom χ (Pi.single (⟨0, by omega⟩ : Fin n) 1)
  have hDc := continuous_crossedHom χ (Pi.single (⟨0, by omega⟩ : Fin n) 1)
  have hv : ∀ j : ℕ, j ≠ 0 → crossedHom χ (Pi.single (⟨0, by omega⟩ : Fin n) 1)
      (freeProPGen 2 n j) = 0 := fun j hj ↦ crossedHom_single_freeProPGen_of_ne χ _ hj
  have h₁ : crossedHom χ (Pi.single (⟨0, by omega⟩ : Fin n) 1) (freeProPGen 2 n 0) = 1 :=
    crossedHom_single_freeProPGen_self χ _
  have hχP : χ ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α)) = 1 :=
    (isProP_freeProP 2 (Fin n)).map_padicPow_eq_one_of_eq_one χ h0 (2 + α)
  have hDP : crossedHom χ (Pi.single (⟨0, by omega⟩ : Fin n) 1)
      ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α)) = 2 + α := by
    rw [hD.map_padicPow_of_eq_one hDc (isProP_freeProP 2 (Fin n)) h0, h₁, mul_one]
  have hc := hD.mul_mul_map_labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1)
  rw [h0, Units.val_one, one_mul, sub_self, zero_mul, add_zero, h₁, mul_one] at hc
  have h := hkill _ hDc hD
  rw [hD.map_mul_mul, hD.map_demushkinWordNeTwo_eq_zero_of_forall_eq_zero _ _
    fun j ↦ hv (j + 2) (by omega), hDP, hχP] at h
  simp only [Units.val_one, one_mul, mul_zero, zero_add] at h
  linear_combination (χ (freeProPGen 2 n 1) : ℤ_[2]) * h - hc

/-- The Kronecker crossed homomorphism `D_3` reads `χ(x₄) (1 - q) = 1` off the relator, once
`χ(x₃) = 1`. -/
private theorem apply_freeProPGen_three_mul_one_sub (hn3 : 3 < n)
    (h2 : χ (freeProPGen 2 n 2) = 1) : (χ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - q) = 1 := by
  have hD := isCrossedHom_crossedHom χ (Pi.single (⟨2, by omega⟩ : Fin n) 1)
  have hv : ∀ j : ℕ, j ≠ 2 → crossedHom χ (Pi.single (⟨2, by omega⟩ : Fin n) 1)
      (freeProPGen 2 n j) = 0 := fun j hj ↦ crossedHom_single_freeProPGen_of_ne χ _ hj
  have h₁ : crossedHom χ (Pi.single (⟨2, by omega⟩ : Fin n) 1) (freeProPGen 2 n 2) = 1 :=
    crossedHom_single_freeProPGen_self χ _
  have hc := hD.mul_mul_map_labuteComm (freeProPGen 2 n 2) (freeProPGen 2 n 3)
  rw [h2, Units.val_one, one_mul, sub_self, zero_mul, add_zero, h₁, mul_one] at hc
  have h := hkill _ (continuous_crossedHom χ _) hD
  rw [hD.map_mul_mul, hD.map_padicPow_eq_zero_of_eq_zero (continuous_crossedHom χ _)
    (isProP_freeProP 2 (Fin n)) (hv 0 (by omega)),
    hD.map_labuteComm_eq_zero_of_eq_zero (hv 0 (by omega)) (hv 1 (by omega)),
    hD.map_demushkinWordNeTwo_of_forall_eq_zero_of_ne q (i₀ := 0) (by omega)
      (x := fun i ↦ freeProPGen 2 n (i + 2)) fun j _ _ ↦ hv (j + 2) (by omega)] at h
  simp only [Nat.zero_add, Nat.reduceAdd, h₁, h2, Units.val_one, one_pow, one_mul,
    mul_one, mul_zero, add_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  have h' := (mul_eq_zero.1 h).resolve_left
    (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))
  linear_combination hc - (χ (freeProPGen 2 n 3) : ℤ_[2]) * h'

end CharacterValues

/-! ### The character values forced by the exact normal form -/

/-- **The character values forced by the exact dyadic relator of even rank** (Labute, Theorem 4,
read on the exact normal form). Let `n ≥ 4` be even and let `χ` be a continuous character of the
free pro-`2` group on `n` generators all of whose continuous crossed homomorphisms kill
`x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯ (x_{n-1}, x_n)`, with `α ∈ ℤ₂` and `q : ℕ`. Then
`χ(x₂) (1 + α) = -1`, `χ(x₄) (1 - q) = 1`, and `χ(x_i) = 1` for every other generator. -/
theorem apply_eq_of_forall_isCrossedHom_eq_zero_padicPow_mul_labuteComm_mul (hn : Even n)
    (hn3 : 3 < n) (χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ) (α : ℤ_[2]) (q : ℕ)
    (hkill : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ D →
      D ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
        labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
        demushkinWordNeTwo q (n - 2) fun i ↦ freeProPGen 2 n (i + 2)) = 0) :
    (∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1) ∧
      (χ (freeProPGen 2 n 1) : ℤ_[2]) * (1 + α) = -1 ∧
      (χ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - q) = 1 := by
  have h0 := apply_freeProPGen_zero_eq_one hkill hn3
  have h2 := apply_freeProPGen_eq_one_right hkill (i₀ := 0) (by omega)
  refine ⟨fun j hj₁ hj₃ ↦ ?_, apply_freeProPGen_one_mul_one_add hkill hn3 h0,
    apply_freeProPGen_three_mul_one_sub hkill hn3 h2⟩
  by_cases hjn : j < n
  · rcases Nat.lt_or_ge j 4 with hj₄ | hj₄
    · rcases (by omega : j = 0 ∨ j = 2) with rfl | rfl
      · exact h0
      · exact h2
    · exact apply_freeProPGen_eq_one_of_four_le hkill hn hj₄ hjn
  · rw [freeProPGen_eq_one_of_le 2 (not_lt.1 hjn), map_one]

/-! ### Characters of the free pro-`2` group and the transvection pair -/

/-- **The image of a character of the free pro-`2` group** which is trivial at every generator
but `x₂` and `x₄` is the closed subgroup generated by its values there. -/
theorem range_eq_topologicalClosure_zpowers_sup_zpowers
    (χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ) (hv : ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1) :
    χ.toMonoidHom.range = (zpowers (χ (freeProPGen 2 n 1)) ⊔
      zpowers (χ (freeProPGen 2 n 3))).topologicalClosure := by
  refine MonoidHom.range_eq_topologicalClosure_of_topologicalClosure_closure_eq_top
    (topologicalClosure_closure_range_of_eq_top 2 (Fin n)) χ.continuous
    (MonoidHom.isClosed_range_of_continuous χ.continuous) ?_
    (sup_le (zpowers_le.2 ⟨_, rfl⟩) (zpowers_le.2 ⟨_, rfl⟩))
  rintro _ ⟨j, rfl⟩
  rw [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass, ← freeProPGen_val]
  by_cases hj₁ : (j : ℕ) = 1
  · rw [hj₁]
    exact le_topologicalClosure _ (mem_sup_left (mem_zpowers _))
  by_cases hj₃ : (j : ℕ) = 3
  · rw [hj₃]
    exact le_topologicalClosure _ (mem_sup_right (mem_zpowers _))
  rw [hv j hj₁ hj₃]
  exact one_mem _

/-- **The symplectic transvection pair `x₂ ↦ x₂ x₄^d`, `x₃ ↦ x₃ x₁^{-d}`** turns a character `χ`
which is trivial away from `x₂` and `x₄` into one taking the value `-1` at `x₂`, when
`χ(x₄)^d = (-χ(x₂))⁻¹`; the value at `x₄` and the triviality at the other generators persist. -/
private theorem apply_freeProPGen_of_forall_apply_eq_symplecticTransvection (hn3 : 3 < n)
    {χ χ₂ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ} {d : ℤ_[2]}
    (hχ₂ : ∀ y, χ₂ y = χ (symplecticTransvection hn3 d y))
    (hd : isProP_units_padicInt_two.padicPow (χ (freeProPGen 2 n 3)) d =
      (-χ (freeProPGen 2 n 1))⁻¹)
    (hv : ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1) :
    χ₂ (freeProPGen 2 n 1) = -1 ∧ χ₂ (freeProPGen 2 n 3) = χ (freeProPGen 2 n 3) ∧
      ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ₂ (freeProPGen 2 n j) = 1 := by
  refine ⟨?_, ?_, fun j hj₁ hj₃ ↦ ?_⟩
  · have e : χ ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 3) d) =
        isProP_units_padicInt_two.padicPow (χ (freeProPGen 2 n 3)) d :=
      (isProP_freeProP 2 (Fin n)).map_padicPow isProP_units_padicInt_two
        (χ : freeProP 2 (Fin n) →* ℤ_[2]ˣ) χ.continuous (freeProPGen 2 n 3) d
    rw [hχ₂, symplecticTransvection_freeProPGen_one, map_mul, e, hd, mul_inv_eq_iff_eq_mul,
      neg_one_mul, neg_neg]
  · rw [hχ₂, symplecticTransvection_freeProPGen_of_ne hn3 d 3 (by omega) (by omega)]
  · by_cases hj₂ : j = 2
    · rw [hj₂, hχ₂, symplecticTransvection_freeProPGen_two, map_mul,
        (isProP_freeProP 2 (Fin n)).map_padicPow_eq_one_of_eq_one χ (hv 0 (by omega) (by omega))
          (-d), hv 2 (by omega) (by omega), mul_one]
    · rw [hχ₂, symplecticTransvection_freeProPGen_of_ne hn3 d j hj₁ hj₂]
      exact hv j hj₁ hj₃

/-- The kernel of the exponent sum at `x₄` is the kernel of `χ²`, for a character `χ` with
`χ(x₂) = -1`, trivial at the other generators but `x₄`, and with `χ(x₄)` of exact level `g`. -/
private theorem exponentSumKer_eq_ker_pow_two (hn3 : 3 < n) {g : ℕ} (hg : 2 ≤ g)
    (χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ) (h₁ : χ (freeProPGen 2 n 1) = -1)
    (hv : ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1)
    (hmem : ∀ k, χ (freeProPGen 2 n 3) ∈ unitsPrincipal 2 k ↔ k ≤ g) :
    exponentSumKer 2 (Fin n) ⟨3, hn3⟩ = (χ ^ 2).toMonoidHom.ker := by
  refine (χ ^ 2).exponentSumKer_eq_ker (fun j hj ↦ ?_) ?_
  · rw [ContinuousMonoidHom.pow_apply, ← freeProPGen_val]
    by_cases hj₁ : (j : ℕ) = 1
    · rw [hj₁, h₁]
      norm_num
    · rw [hv j hj₁ fun h ↦ hj (Fin.ext h), one_pow]
  · rw [ContinuousMonoidHom.pow_apply, ← freeProPGen_val]
    have hmem₁ : χ (freeProPGen 2 n 3) ^ 2 ∈ unitsPrincipal 2 (g + 1) := by
      simpa using pow_pow_mem_unitsPrincipal (by omega) ((hmem g).2 le_rfl) 1
    have hnmem : χ (freeProPGen 2 n 3) ^ 2 ∉ unitsPrincipal 2 (g + 1 + 1) := by
      simpa using pow_pow_notMem_unitsPrincipal (by omega) (fun _ ↦ hg) ((hmem g).2 le_rfl)
        (fun h ↦ by have := (hmem _).1 h; omega) 1
    exact not_isOfFinOrder_of_mem_unitsPrincipal (by omega) (fun _ ↦ by omega) hmem₁
      fun h ↦ hnmem (h ▸ one_mem _)

/-! ### The graded classes of the normal-form words -/

/-- **The relator of the `q = 2^g` normal form has the class of the `q = 2` word in `gr_1(F)`**
(`demushkinWordNeTwo 2 n`, which has no `x₃²` factor):
`x₁^{2+α} (x₁, x₂) x₃^{2^g} (x₃, x₄) ⋯` and `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` have the same
class modulo `λ₂(F)`, when `4 ∣ α` and `g ≥ 2`. -/
private theorem gradedMk_padicPow_mul_labuteComm_mul_eq_gradedMk_demushkinWordNeTwo (hn3 : 3 < n)
    {α : ℤ_[2]} (hα : 4 ∣ α) {g : ℕ} (hg : 2 ≤ g) {r : freeProP 2 (Fin n)}
    (hr : r = (isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
      labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
      demushkinWordNeTwo (2 ^ g) (n - 2) (fun i ↦ freeProPGen 2 n (i + 2)))
    (h₁ : r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (h₀ : demushkinWordNeTwo 2 n (freeProPGen 2 n) ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1) :
    gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨r, h₁⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n), h₀⟩ := by
  subst hr
  rw [gradedMk_eq_gradedMk_iff]
  have hx0 : freeProPGen 2 n 0 = of ⟨0, by omega⟩ := freeProPGen_of_lt 2 (by omega)
  have hx2 : freeProPGen 2 n 2 = of ⟨2, by omega⟩ := freeProPGen_of_lt 2 (by omega)
  have hPα : ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) α :
      freeProP 2 (Fin n) ⧸ pLowerCentralSeries 2 (freeProP 2 (Fin n)) (1 + 1)) = 1 := by
    rw [QuotientGroup.eq_one_iff, hx0, padicPow_mem_pLowerCentralSeries_iff,
      show ((2 : ℕ) : ℤ_[2]) ^ (1 + 1) = 4 by norm_num]
    exact hα
  have hT2 : ((freeProPGen 2 n 2 ^ 2 ^ g : freeProP 2 (Fin n)) :
      freeProP 2 (Fin n) ⧸ pLowerCentralSeries 2 (freeProP 2 (Fin n)) (1 + 1)) = 1 := by
    rw [QuotientGroup.eq_one_iff, ← (isProP_freeProP 2 (Fin n)).padicPow_natCast, hx2,
      padicPow_mem_pLowerCentralSeries_iff, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_dvd_pow 2 (by omega)
  dsimp only
  rw [(isProP_freeProP 2 (Fin n)).padicPow_add, (isProP_freeProP 2 (Fin n)).padicPow_ofNat,
    demushkinWordNeTwo_eq_pow_mul_labuteComm_mul 2 (by omega), demushkinWordNeTwo_def (2 ^ g),
    demushkinWordNeTwo_def 0, pow_zero, one_mul]
  simp only [QuotientGroup.mk_mul, hPα, hT2, mul_one, one_mul]

/-- **The exact even-rank normal form has the class of the transvected relator**: if a relator `r`
has the class of the word `x₁² (x₁, x₂)(x₃, x₄) ⋯ (x_{n-1}, x_n)` in `gr_1(F)`, then the exact word
`x₁² (x₁, x₂) x₃^{2^g} (x₃, x₄) ⋯` of `demushkinWordTwoEven` has the class of `τ⁻¹ r` for the
symplectic transvection pair `τ`. -/
private theorem gradedMk_demushkinWordTwoEven_eq_gradedMk_symm (hn3 : 3 < n) (d : ℤ_[2]) {g : ℕ}
    (hg : 2 ≤ g) {r : freeProP 2 (Fin n)} (hr₁ : r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (hr₂₁ : (symplecticTransvection hn3 d).symm r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (h₀ : demushkinWordNeTwo 2 n (freeProPGen 2 n) ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (hw : demushkinWordTwoEven 0 g n (freeProPGen 2 n) ∈
      pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (hcls : gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨r, hr₁⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n), h₀⟩) :
    gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordTwoEven 0 g n (freeProPGen 2 n), hw⟩ =
      gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨(symplecticTransvection hn3 d).symm r, hr₂₁⟩ := by
  -- Apply the graded map of the transvection pair, which is injective and fixes the class of the
  -- normal-form word.
  have hinj : Function.Injective (gradedMap 2
      (symplecticTransvection hn3 d : freeProP 2 (Fin n) →* freeProP 2 (Fin n))
      (map_continuous (symplecticTransvection hn3 d)) 1) :=
    fun a b hab ↦ by
      rw [← gradedMap_symm_gradedMap (symplecticTransvection hn3 d) 1 a,
        ← gradedMap_symm_gradedMap (symplecticTransvection hn3 d) 1 b, hab]
  have h : gradedMap 2
      (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
      (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
        (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨(symplecticTransvection hn3 d).symm r, hr₂₁⟩) =
      gradedMap 2
      (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
      (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
        (gradedMk 2 (freeProP 2 (Fin n)) 1 ⟨demushkinWordNeTwo 2 n (freeProPGen 2 n), h₀⟩) := by
    rw [gradedMap_symplecticTransvection_gradedMk_demushkinWordNeTwo hn3 d dvd_rfl,
      gradedMap_gradedMk, ← hcls]
    congr 1
    exact Subtype.ext ((symplecticTransvection hn3 d).apply_symm_apply r)
  exact (gradedMk_demushkinWordTwoEven_eq_gradedMk_demushkinWordNeTwo (dvd_zero 2) hg
    (by omega) _).trans (hinj h).symm

/-! ### The steps of Labute's Theorem 6 -/

/-- **The values of the character at the marked generators**: let `χ` be a character of the free
pro-`2` group on `n` generators with image `V^(f) = {±1} × U^(f)`, `f ≥ 2`, trivial away from the
generators `x₂`, `x₄`, with `χ(x₂) (1 + α) = -1` and `χ(x₄) (1 - q) = 1`, `4 ∣ α` and
`q ∈ {0} ∪ {2^g : g ≥ 2}`. Then `q = 2^f` and `χ(x₄)^d = (-χ(x₂))⁻¹` for some `d ∈ ℤ₂`. -/
private theorem eq_two_pow_and_exists_padicPow_eq_neg_inv_of_range_eq {f : ℕ} (hf : 2 ≤ f)
    {χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ} {α : ℤ_[2]} {q : ℕ} (hα : 4 ∣ α)
    (hq : q = 0 ∨ ∃ g, 2 ≤ g ∧ q = 2 ^ g)
    (hv : ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1)
    (h₁ : (χ (freeProPGen 2 n 1) : ℤ_[2]) * (1 + α) = -1)
    (h₃ : (χ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - q) = 1)
    (hrange : χ.toMonoidHom.range = unitsPlusMinus f) :
    q = 2 ^ f ∧
      ∃ d : ℤ_[2], isProP_units_padicInt_two.padicPow (χ (freeProPGen 2 n 3)) d =
        (-χ (freeProPGen 2 n 1))⁻¹ := by
  have hV := (range_eq_topologicalClosure_zpowers_sup_zpowers χ hv).symm.trans hrange
  -- `-χ(x₂) ∈ U^(f)`: it lies in `1 + 4ℤ_2` since `4 ∣ α`, and `χ(x₂) ∈ V^(f)`.
  have hneg₂ : -χ (freeProPGen 2 n 1) ∈ unitsPrincipal 2 2 :=
    (neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one h₁).2
      (by rw [show (2 : ℤ_[2]) ^ 2 = 4 by norm_num]; exact hα)
  have hnegf : -χ (freeProPGen 2 n 1) ∈ unitsPrincipal 2 f := by
    have hmem : χ (freeProPGen 2 n 1) ∈ unitsPlusMinus f :=
      hV ▸ le_topologicalClosure _ (mem_sup_left (mem_zpowers _))
    rcases mem_unitsPlusMinus_iff.1 hmem with h | h
    · exact absurd (unitsPrincipal_antitone 2 hf h)
        (notMem_unitsPrincipal_two_of_neg_mem le_rfl hneg₂)
    · exact h
  -- The level of `χ(x₄)` is not `∞`, since `V^(f)` is not procyclic.
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h3 : χ (freeProPGen 2 n 3) = 1 := by simpa using h₃
    rw [h3, zpowers_one_eq_bot, sup_bot_eq] at hV
    exact not_exists_topologicalClosure_zpowers_eq_unitsPlusMinus hf ⟨_, hV⟩
  obtain ⟨g, hg, rfl⟩ : ∃ g, 2 ≤ g ∧ q = 2 ^ g := hq.resolve_left hq0
  have h₃g : (χ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - ((2 : ℕ) : ℤ_[2]) ^ g) = 1 := by
    push_cast at h₃ ⊢
    exact h₃
  have hmem₃ : ∀ k, χ (freeProPGen 2 n 3) ∈ unitsPrincipal 2 k ↔ k ≤ g := fun k ↦
    mem_unitsPrincipal_iff_of_val_mul_one_sub_pow_eq_one h₃g
  obtain rfl := eq_of_topologicalClosure_zpowers_sup_zpowers_eq_unitsPlusMinus hf hg hV hmem₃
  refine ⟨rfl, ?_⟩
  -- `χ(x₄)` topologically generates `U^(f)`, so `(-χ(x₂))⁻¹ ∈ U^(f)` is a `2`-adic power of it.
  have hgen : (zpowers (χ (freeProPGen 2 n 3))).topologicalClosure = unitsPrincipal 2 g :=
    topologicalClosure_zpowers_eq_unitsPrincipal_of_val_mul_one_sub_pow_eq_one (by omega)
      (fun _ ↦ hg) h₃g
  rw [← isProP_units_padicInt_two.mem_topologicalClosure_closure_singleton_iff,
    ← zpowers_eq_closure, hgen]
  exact inv_mem hnegf

/-- **The exact even-rank relator is carried to the normal form
`x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯`**: let `χ` be a character of the free pro-`2` group with the
marked values of the dyadic case (`χ(x₄)` of exact level `f`, `χ(x₄)^d = (-χ(x₂))⁻¹`, trivial
elsewhere), such that every continuous crossed homomorphism for `χ` kills the relator
`x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯` of `Φ(F)`, which `χ` trivialises. Then a continuous
automorphism of `F` carries this relator to `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯`. -/
private theorem exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_isCrossedHom_eq_zero
    (hn : Even n) (hn3 : 3 < n) {f : ℕ} (hf : 2 ≤ f) {α : ℤ_[2]} (hα : 4 ∣ α)
    {χ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ} {d : ℤ_[2]}
    (hv : ∀ j : ℕ, j ≠ 1 → j ≠ 3 → χ (freeProPGen 2 n j) = 1)
    (h₃ : (χ (freeProPGen 2 n 3) : ℤ_[2]) * (1 - ((2 ^ f : ℕ) : ℤ_[2])) = 1)
    (hd : isProP_units_padicInt_two.padicPow (χ (freeProPGen 2 n 3)) d =
      (-χ (freeProPGen 2 n 1))⁻¹)
    {r : freeProP 2 (Fin n)}
    (hr : r = (isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
      labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
      demushkinWordNeTwo (2 ^ f) (n - 2) fun i ↦ freeProPGen 2 n (i + 2))
    (hr₁ : r ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1)
    (hkill : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ D → D r = 0)
    (hχr : χ r = 1) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      e r = demushkinWordTwoEven 0 f n (freeProPGen 2 n) := by
  have hmem₃ : ∀ k, χ (freeProPGen 2 n 3) ∈ unitsPrincipal 2 k ↔ k ≤ f := fun k ↦
    mem_unitsPrincipal_iff_of_val_mul_one_sub_pow_eq_one (by push_cast at h₃ ⊢; exact h₃)
  -- Step 4: the symplectic transvection pair `x₂ ↦ x₂ x₄^d`, `x₃ ↦ x₃ x₁^{-d}` makes `χ(x₂) = -1`.
  obtain ⟨χ₂, hχ₂⟩ : ∃ χ₂ : freeProP 2 (Fin n) →ₜ* ℤ_[2]ˣ,
      ∀ y, χ₂ y = χ (symplecticTransvection hn3 d y) :=
    ⟨χ.comp (symplecticTransvection hn3 d : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)),
      fun y ↦ by
        rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, ContinuousMonoidHom.coe_coe]⟩
  obtain ⟨hχ₂₁, hχ₂₃, hχ₂ne⟩ :=
    apply_freeProPGen_of_forall_apply_eq_symplecticTransvection hn3 hχ₂ hd hv
  -- The relator `r₂` in the new basis: every crossed homomorphism for `χ₂` kills it.
  have hr₂₁ : (symplecticTransvection hn3 d).symm r ∈
      pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 :=
    MonoidHom.map_pLowerCentralSeries_le
      ((symplecticTransvection hn3 d).symm : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom
      ((symplecticTransvection hn3 d).symm : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous
      1 ⟨r, hr₁, rfl⟩
  have hkill₂ : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ₂ D →
      D ((symplecticTransvection hn3 d).symm r) = 0 := fun D hDc hD ↦
    hkill _ (hDc.comp ((symplecticTransvection hn3 d).symm :
        freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous)
      (hD.comp ((symplecticTransvection hn3 d).symm : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n))
        fun y ↦ by
          rw [hχ₂, ContinuousMonoidHom.coe_coe, (symplecticTransvection hn3 d).apply_symm_apply])
  -- `r₂` has the class of the exact normal-form word in `gr_1(F)`.
  have hcls := gradedMk_demushkinWordTwoEven_eq_gradedMk_symm hn3 d (by omega) hr₁ hr₂₁
    (demushkinWordNeTwo_mem_pLowerCentralSeries_one dvd_rfl n _)
    (demushkinWordTwoEven_mem_pLowerCentralSeries_one (dvd_zero 2) (by omega) n _)
    (gradedMk_padicPow_mul_labuteComm_mul_eq_gradedMk_demushkinWordNeTwo hn3 hα hf hr hr₁ _)
  -- `r₂` lies in the kernel of the exponent sum at `x₄`: it is killed by `χ₂²`.
  have hr₂X : (symplecticTransvection hn3 d).symm r ∈ exponentSumKer 2 (Fin n) ⟨3, hn3⟩ := by
    rw [exponentSumKer_eq_ker_pow_two hn3 hf χ₂ hχ₂₁ hχ₂ne (by simpa only [hχ₂₃] using hmem₃),
      MonoidHom.mem_ker, ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass,
      ContinuousMonoidHom.pow_apply, hχ₂, (symplecticTransvection hn3 d).apply_symm_apply, hχr,
      one_pow]
  -- Step 5: the constrained successive approximation inside the exponent-sum kernel.
  obtain ⟨e₃, -, he₃⟩ :=
    exists_continuousMulEquiv_apply_demushkinWordTwoEven_zero_eq_of_forall_crossedHom_eq_zero hn
      hn3 hf (by rw [← freeProPGen_val]; exact hχ₂₁)
      (by rw [← freeProPGen_val, hχ₂₃]; push_cast at h₃ ⊢; exact h₃)
      (fun j hj₁ hj₃ ↦ by
        rw [← freeProPGen_val]
        exact hχ₂ne j (fun h ↦ hj₁ (Fin.ext h)) fun h ↦ hj₃ (Fin.ext h))
      ⟨_, hr₂₁⟩ hcls hr₂X
      fun i _ ↦ hkill₂ _ (continuous_crossedHom χ₂ _) (isCrossedHom_crossedHom χ₂ _)
  refine ⟨(symplecticTransvection hn3 d).symm.trans e₃.symm, ?_⟩
  rw [ContinuousMulEquiv.trans_apply, e₃.symm_apply_eq]
  exact he₃.symm

/-! ### Labute's Theorem 6 -/

/-- **Labute's normal form for the dyadic Demushkin groups of even rank with image `{±1} × U^(f)`**
(Labute, Theorem 6). Let `r ∈ Φ(F)` be a relator of the free pro-`2` group on an even number
`n ≥ 4` of generators presenting a Demushkin group `G = ⟨x₁, …, x_n ∣ r⟩` whose canonical character
has image `V^(f) = {±1} × U^(f)` for a finite `f ≥ 2`. Then a continuous automorphism of `F`
carries `r` to `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`. -/
theorem exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq
    {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) (hn : Even n) (hn3 : 3 < n) {f : ℕ}
    (hf : 2 ≤ f) (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    ∃ e : freeProP 2 (Fin n) ≃ₜ* freeProP 2 (Fin n),
      e r = demushkinWordTwoEven 0 f n (freeProPGen 2 n) := by
  -- Step 0: `q(G) = 2`, because `-1 ∉ 1 + 4ℤ_2` is a value of the canonical character.
  have hq : demushkinQ hG = 2 := by
    by_contra hq
    have hle := (demushkinQ_ne_two_iff_range_demushkinCharacter_le hG).1 hq rfl
    have := neg_one_mem_unitsPrincipal_two_iff.1 (hle (hA ▸ neg_one_mem_unitsPlusMinus f))
    omega
  -- Step 1: the exact normal form `x₁^{2+α} (x₁, x₂) x₃^{q} (x₃, x₄) ⋯` of the relator.
  obtain ⟨e₀, α, q, hα, hq', he₀⟩ :=
    hG.exists_continuousMulEquiv_apply_eq_padicPow_mul_labuteComm_mul_demushkinWordNeTwo hn hr hq
  set rex := (isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 0) (2 + α) *
    labuteComm (freeProPGen 2 n 0) (freeProPGen 2 n 1) *
    demushkinWordNeTwo q (n - 2) (fun i ↦ freeProPGen 2 n (i + 2)) with hrex
  have hrex₁ : rex ∈ pLowerCentralSeries 2 (freeProP 2 (Fin n)) 1 := he₀ ▸
    (e₀ : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).toMonoidHom.map_pLowerCentralSeries_le
      (e₀ : freeProP 2 (Fin n) →ₜ* freeProP 2 (Fin n)).continuous 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).symm.le hr, rfl⟩
  -- Step 2: the presented group on `rex` is Demushkin with the same image of the canonical
  -- character, which is read on `F` as a character `χ₁` killed by the crossed homomorphisms.
  have hG₁ : IsDemushkin 2 (presentedProP 2 (Fin n) {rex}) :=
    IsDemushkin.of_equiv 2 hG (presentedProP.congrSingleton e₀ he₀)
  have hrex₁Φ : rex ∈ proPFrattini 2 (freeProP 2 (Fin n)) :=
    (pLowerCentralSeries_one_eq_proPFrattini Nat.prime_two).le hrex₁
  set χ₁ := demushkinRelatorCharacter hG₁
  have hrange : χ₁.toMonoidHom.range = unitsPlusMinus f := by
    rw [range_demushkinRelatorCharacter, range_demushkinCharacter_of_equiv hG hG₁
      (presentedProP.congrSingleton e₀ he₀), hA]
  have hkill₁ : ∀ D : freeProP 2 (Fin n) → ℤ_[2], Continuous D → IsCrossedHom χ₁ D → D rex = 0 :=
    fun D hDc hD ↦ demushkinRelatorCharacter_isCrossedHom_eq_zero hG₁ hrex₁Φ hDc hD
  have hχ₁rex : χ₁ rex = 1 := demushkinRelatorCharacter_mem_ker hG₁
  -- Step 3: the values of `χ₁` on the generators and the level of its marked values.
  obtain ⟨hv, h₁, h₃⟩ :=
    apply_eq_of_forall_isCrossedHom_eq_zero_padicPow_mul_labuteComm_mul hn hn3 χ₁ α q hkill₁
  obtain ⟨rfl, d, hd⟩ :=
    eq_two_pow_and_exists_padicPow_eq_neg_inv_of_range_eq hf hα hq' hv h₁ h₃ hrange
  -- Steps 4 and 5: the transvection pair and the successive approximation.
  obtain ⟨e₃, he₃⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_isCrossedHom_eq_zero hn hn3
      hf hα hv h₃ hd hrex hrex₁ hkill₁ hχ₁rex
  exact ⟨e₀.trans e₃, by rw [ContinuousMulEquiv.trans_apply, he₀]; exact he₃⟩

/-- **Labute's normal form for a one-relator dyadic Demushkin group of even rank with image
`{±1} × U^(f)`.** Let `r ∈ Φ(F)` be a relator of the free pro-`2` group on an even number `n ≥ 4`
of generators presenting a Demushkin group whose canonical character has image `V^(f)`, `f ≥ 2`
finite. Then `⟨x₁, …, x_n ∣ r⟩` is topologically isomorphic to
`⟨x₁, …, x_n ∣ x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩`. -/
theorem exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq
    {r : freeProP 2 (Fin n)} (hr : r ∈ proPFrattini 2 (freeProP 2 (Fin n)))
    (hG : IsDemushkin 2 (presentedProP 2 (Fin n) {r})) (hn : Even n) (hn3 : 3 < n) {f : ℕ}
    (hf : 2 ≤ f) (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (presentedProP 2 (Fin n) {r} ≃ₜ*
      presentedProP 2 (Fin n) {demushkinWordTwoEven 0 f n (freeProPGen 2 n)}) := by
  obtain ⟨e, he⟩ :=
    exists_continuousMulEquiv_apply_eq_demushkinWordTwoEven_of_range_eq hr hG hn hn3 hf hA
  exact ⟨presentedProP.congrSingleton e he⟩

end freeProP

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Labute's normal form for a dyadic Demushkin group of even rank with image `{±1} × U^(f)`,
intrinsic form** (Labute, Theorem 6). A Demushkin group `G` at `p = 2` of even rank `n ≥ 4` whose
canonical character has image `V^(f) = {±1} × U^(f)` for a finite `f ≥ 2` is topologically
isomorphic to `⟨x₁, …, x_n ∣ x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)⟩` on
`n = demushkinRank hG` generators. -/
theorem IsDemushkin.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq
    (hG : IsDemushkin 2 G) (hn : Even (demushkinRank hG)) (hn3 : 3 < demushkinRank hG) {f : ℕ}
    (hf : 2 ≤ f) (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (G ≃ₜ* presentedProP 2 (Fin (demushkinRank hG))
      {demushkinWordTwoEven 0 f (demushkinRank hG) (freeProPGen 2 (demushkinRank hG))}) := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP_fin
  have : Nonempty (Fin (demushkinRank hG)) := ⟨⟨0, hG.demushkinRank_pos⟩⟩
  have hG' : IsDemushkin 2 (presentedProP 2 (Fin (demushkinRank hG)) {r}) :=
    isDemushkin_of_nondegenerate_degreeOneForm hr (ContinuousMulEquiv.refl _)
      (hG.nondegenerate_degreeOneForm hr e)
  have hA' : (demushkinCharacter hG').toMonoidHom.range = unitsPlusMinus f := by
    rw [range_demushkinCharacter_of_equiv hG hG' e.symm, hA]
  obtain ⟨e'⟩ :=
    freeProP.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq hr hG' hn
      hn3 hf hA'
  exact ⟨e.symm.trans e'⟩

/-- **Uniqueness of the dyadic Demushkin groups of even rank with image `{±1} × U^(f)`** (Labute,
Theorem 6). Two Demushkin groups at `p = 2` of the same even rank `n ≥ 4` whose canonical
characters have the same image `V^(f) = {±1} × U^(f)`, `f ≥ 2` finite, are topologically
isomorphic. -/
theorem IsDemushkin.nonempty_continuousMulEquiv_of_even_demushkinRank_of_range_eq_unitsPlusMinus
    {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    [TotallyDisconnectedSpace H] (hG : IsDemushkin 2 G) (hH : IsDemushkin 2 H)
    (hn : demushkinRank hG = demushkinRank hH) (heven : Even (demushkinRank hG))
    (hn3 : 3 < demushkinRank hG) {f : ℕ} (hf : 2 ≤ f)
    (hA : (demushkinCharacter hG).toMonoidHom.range = unitsPlusMinus f)
    (hB : (demushkinCharacter hH).toMonoidHom.range = unitsPlusMinus f) :
    Nonempty (G ≃ₜ* H) := by
  obtain ⟨e⟩ :=
    hG.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq heven hn3 hf hA
  obtain ⟨e'⟩ :=
    hH.exists_continuousMulEquiv_presentedProP_demushkinWordTwoEven_of_range_eq (hn ▸ heven)
      (hn ▸ hn3) hf hB
  rw [hn] at e
  exact ⟨e.trans e'.symm⟩

end TauCeti
