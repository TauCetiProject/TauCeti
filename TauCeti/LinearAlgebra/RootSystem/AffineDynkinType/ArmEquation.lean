/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Star
public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Star.Kernel
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The affine arm equation for three-armed stars

With the centre included in each arm size, the affine equation is `1/p + 1/q + 1/r = 1`.
The ordered arm sizes are `(3,3,3)`, `(2,4,4)` and `(2,3,6)`, giving the exceptional
simply-laced affine diagrams via the existing star isomorphisms. This is the equality case
of the fork inequality studied in `Mathlib.NumberTheory.ADEInequality`; for the affine
semidefinite classification see Etingof et al., *Introduction to representation theory*,
Problem 5.3(c)–(g).
-/

public section

open scoped Matrix

namespace TauCeti

/-- The ordered edge lengths of three arms whose reciprocal sizes sum to one. No arm can be
empty, since that arm alone would contribute `1`. -/
theorem sum_inv_nat_add_one_eq_one_iff {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ((a : ℚ) + 1)⁻¹ + ((b : ℚ) + 1)⁻¹ + ((c : ℚ) + 1)⁻¹ = 1 ↔
      (a = 2 ∧ b = 2 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 3) ∨ (a = 1 ∧ b = 2 ∧ c = 5) := by
  constructor
  · intro h
    have hanti {m n : ℕ} (hmn : m ≤ n) : ((n : ℚ) + 1)⁻¹ ≤ ((m : ℚ) + 1)⁻¹ :=
      inv_anti₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hmn)
    have heq {m n : ℕ} (hmn : ((m : ℚ) + 1)⁻¹ = ((n : ℚ) + 1)⁻¹) : m = n := by
      have := inv_injective hmn
      exact_mod_cast (add_right_cancel this)
    have hpos (n : ℕ) : 0 < ((n : ℚ) + 1)⁻¹ := by positivity
    have ha0 : 0 < a := by
      by_contra! ha
      have ha' : a = 0 := Nat.eq_zero_of_le_zero ha
      norm_num [ha'] at h
      linarith [hpos b, hpos c]
    by_cases ha : 2 ≤ a
    · -- All three terms are at most 1/3, so all must attain that bound.
      have h₁ := hanti ha
      have h₂ := hanti (ha.trans hab)
      have h₃ := hanti (ha.trans (hab.trans hbc))
      exact Or.inl ⟨heq (by linarith), heq (by linarith), heq (by linarith)⟩
    have ha1 : a = 1 := by omega
    have hb2 : 2 ≤ b := by
      by_contra! hb
      have hb1 : b = 1 := by omega
      norm_num [ha1, hb1] at h
      linarith [hpos c]
    by_cases hb : 3 ≤ b
    · -- After 1/2 from the first arm, both remaining terms must be 1/4.
      have h₂ := hanti hb
      have h₃ := hanti (hb.trans hbc)
      norm_num [ha1] at h
      exact Or.inr (Or.inl ⟨ha1, heq (by linarith), heq (by linarith)⟩)
    · have hb' : b = 2 := by omega
      norm_num [ha1, hb'] at h
      exact Or.inr (Or.inr ⟨ha1, hb', heq (by linarith)⟩)
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num

/-- A three-armed star with ordered edge lengths has a nonzero rational null vector exactly
for the three exceptional affine shapes. -/
theorem exists_ne_zero_mulVec_starCartanMatrix_three_eq_zero_iff {a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∃ x : StarIndex ![a, b, c] → ℚ, x ≠ 0 ∧
      ((starCartanMatrix ![a, b, c]).map (Int.cast : ℤ → ℚ)) *ᵥ x = 0) ↔
      (a = 2 ∧ b = 2 ∧ c = 2) ∨ (a = 1 ∧ b = 3 ∧ c = 3) ∨ (a = 1 ∧ b = 2 ∧ c = 5) := by
  have hcard : (Fintype.card (Fin 3) : ℚ) - 2 = 1 := by norm_num
  rw [exists_ne_zero_mulVec_starCartanMatrix_eq_zero_iff, Fin.sum_univ_three, hcard]
  exact sum_inv_nat_add_one_eq_one_iff hab hbc

/-- A three-armed star with a nonzero rational null vector is isomorphic to one of the
exceptional affine Dynkin diagrams. The arms need not be presented in increasing order. -/
theorem exists_affineDynkinType_iso_of_exists_ne_zero_mulVec_starCartanMatrix_three
    {ℓ : Fin 3 → ℕ} (h : ∃ x : StarIndex ℓ → ℚ, x ≠ 0 ∧
      ((starCartanMatrix ℓ).map (Int.cast : ℤ → ℚ)) *ᵥ x = 0) :
    ∃ t : AffineDynkinType, (t = .E6 ∨ t = .E7 ∨ t = .E8) ∧
      Nonempty (diagramGraph (starCartanMatrix ℓ) ≃g t.graph) := by
  let σ := Tuple.sort ℓ
  let m := ℓ ∘ σ
  have hm : Monotone m := Tuple.monotone_sort ℓ
  have hs : ∑ i, ((m i : ℚ) + 1)⁻¹ = 1 := by
    calc
      _ = ∑ i, ((ℓ i : ℚ) + 1)⁻¹ :=
        Equiv.sum_comp σ (fun i ↦ ((ℓ i : ℚ) + 1)⁻¹)
      _ = 1 := by
        have hs := exists_ne_zero_mulVec_starCartanMatrix_eq_zero_iff.mp h
        norm_num at hs
        exact hs
  rw [Fin.sum_univ_three] at hs
  have hmvec : m = ![m 0, m 1, m 2] := by
    funext i
    fin_cases i <;> rfl
  have hlen : m = ![2, 2, 2] ∨ m = ![1, 3, 3] ∨ m = ![1, 2, 5] := by
    rcases (sum_inv_nat_add_one_eq_one_iff (hm (by decide : (0 : Fin 3) ≤ 1))
      (hm (by decide : (1 : Fin 3) ≤ 2))).mp hs with h | h | h
    · exact Or.inl (by rw [hmvec, h.1, h.2.1, h.2.2])
    · exact Or.inr (Or.inl (by rw [hmvec, h.1, h.2.1, h.2.2]))
    · exact Or.inr (Or.inr (by rw [hmvec, h.1, h.2.1, h.2.2]))
  have e : diagramGraph (starCartanMatrix m) ≃g diagramGraph (starCartanMatrix ℓ) := by
    rw [starCartanMatrix_comp, diagramGraph_submatrix (starIndexCongrArms σ ℓ).injective]
    exact SimpleGraph.Iso.comap (starIndexCongrArms σ ℓ) _
  rcases hlen with h6 | h7 | h8
  · rw [h6] at e
    exact ⟨.E6, Or.inl rfl, ⟨e.symm.trans AffineDynkinType.starGraphIsoE6⟩⟩
  · rw [h7] at e
    exact ⟨.E7, Or.inr (Or.inl rfl), ⟨e.symm.trans AffineDynkinType.starGraphIsoE7⟩⟩
  · rw [h8] at e
    exact ⟨.E8, Or.inr (Or.inr rfl), ⟨e.symm.trans AffineDynkinType.starGraphIsoE8⟩⟩

/-- The native affine marks, in star coordinates, are the star marks scaled to agree at the
centre. This applies to the three exceptional relabellings. -/
theorem AffineDynkinType.marks_comp_eq_smul_starMark {α : Type*} [Fintype α] [DecidableEq α]
    {ℓ : α → ℕ} {t : AffineDynkinType} (ht : t.Valid) (e : StarIndex ℓ ≃ Fin t.nodes)
    (he : starCartanMatrix ℓ = t.cartanMatrix.submatrix e e) :
    (fun v ↦ (t.marks (e v) : ℚ)) =
      ((t.marks (e none) : ℚ) / starMark ℓ none) • starMark ℓ := by
  have hcast : (t.cartanMatrix.map (Int.cast : ℤ → ℚ)) *ᵥ (fun i ↦ (t.marks i : ℚ)) = 0 := by
    calc
      _ = (Int.castRingHom ℚ) ∘ (t.cartanMatrix *ᵥ t.marks) :=
        (funext ((Int.castRingHom ℚ).map_mulVec t.cartanMatrix t.marks)).symm
      _ = 0 := by
        ext i
        simp [t.cartanMatrix_mulVec_marks_eq_zero ht]
  apply eq_smul_starMark_of_mulVec_some_eq_zero
  intro v
  rw [he, ← Matrix.submatrix_map]
  -- The reindexed vector is written as a composition to apply `submatrix_mulVec_equiv`.
  change (((t.cartanMatrix.map (Int.cast : ℤ → ℚ)).submatrix e e) *ᵥ
    ((fun i ↦ (t.marks i : ℚ)) ∘ e)) (some v) = 0
  rw [Matrix.submatrix_mulVec_equiv, Function.comp_assoc, Equiv.self_comp_symm,
    Function.comp_id, hcast]
  rfl

end TauCeti
