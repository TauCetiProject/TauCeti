/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.OrderOfElement.OrbitMarks
import TauCeti.Data.ZMod.Two

/-!
# Thick letters in split Frobenius orbits

Write the split host group as `A × C₂ × C₂`, with the two binary coordinates the exponents
of complex conjugation `c` and of the inertia generator `σ_d`. The two letters of a thick
place differ by `c`: both have nonzero `σ_d` coordinate, and their `A` coordinate belongs to
the translated thick set. Thus a Frobenius with nonzero `σ_d` coordinate can meet thick
letters at only one parity. In the other case the thick marks are either exactly the projected
marks on `A` or empty. This distinguishes the orbit of complex conjugation with two thick
letters from the orbits that necessarily contain an unmarked letter.

The orbit distinction is used in Levent Alpöge's formalization of the Riemann hypothesis for
Dirichlet L-functions, in `Formalism.HC.Frame.hostThickOrbit` and
`GlobalTheory.HTW.LongWindow.main`.
-/

public section

open Set Multiplicative
open scoped Pointwise

namespace TauCeti

local notation "C₂" => Multiplicative (ZMod 2)
local notation "ε₂" => Multiplicative.ofAdd (1 : ZMod 2)

variable {A : Type*} {S : Set A} {y φ : A × C₂ × C₂}

/-- In the split host coordinates `(a, c-bit, σ_d-bit)`, the letters of thick places have
`a ∈ S` and a nontrivial `σ_d` coordinate. Here `S` includes the translation of the thick set. -/
def _root_.Set.thickLetters (S : Set A) : Set (A × C₂ × C₂) := {g | g.1 ∈ S ∧ g.2.2 ≠ 1}

/-- A thick letter lies over a point of `S` and has nontrivial inertia coordinate. -/
@[simp]
theorem _root_.Set.mem_thickLetters_iff {g : A × C₂ × C₂} :
    g ∈ thickLetters S ↔ g.1 ∈ S ∧ g.2.2 ≠ 1 := (Iff.rfl)

variable [Group A]

/-- An integer position is thick exactly when its projection lands in the thick set and its
inertia coordinate is nontrivial. -/
theorem intCast_mem_orbitMarks_thickLetters_iff (i : ℤ) :
    (i : ZMod (orderOf φ)) ∈ orbitMarks (orderOf φ) y φ (thickLetters S) ↔
      (i : ZMod (orderOf φ)) ∈ orbitMarks (orderOf φ) y.1 φ.1 S ∧
        y.2.2 * φ.2.2 ^ i ≠ 1 := by
  have hN : orderOf φ.1 ∣ orderOf φ := orderOf_map_dvd (MonoidHom.fst A _) φ
  rw [intCast_mem_orbitMarks_iff dvd_rfl, intCast_mem_orbitMarks_iff hN, mem_thickLetters_iff]
  simp

/-- Projecting to `A` can only add marks. -/
theorem orbitMarks_thickLetters_subset :
    orbitMarks (orderOf φ) y φ (thickLetters S) ⊆ orbitMarks (orderOf φ) y.1 φ.1 S := by
  intro i hi
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  exact (intCast_mem_orbitMarks_thickLetters_iff k |>.mp hi).1

/-- When Frobenius fixes the inertia coordinate, all projected marks survive if the starting
letter has nontrivial inertia coordinate; otherwise none survives. -/
theorem orbitMarks_thickLetters_of_snd_snd_eq_one (hφ : φ.2.2 = 1) :
    orbitMarks (orderOf φ) y φ (thickLetters S) =
      if y.2.2 = 1 then ∅ else orbitMarks (orderOf φ) y.1 φ.1 S := by
  ext i
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  rw [intCast_mem_orbitMarks_thickLetters_iff]
  by_cases hy : y.2.2 = 1 <;> simp [hφ, hy]

/-- When Frobenius changes the inertia coordinate, exactly one parity of the projected marks
survives. The parity is even for a starting letter with nontrivial inertia coordinate. -/
theorem intCast_mem_orbitMarks_thickLetters_iff_of_snd_snd_ne_one (hφ : φ.2.2 ≠ 1) (i : ℤ) :
    (i : ZMod (orderOf φ)) ∈ orbitMarks (orderOf φ) y φ (thickLetters S) ↔
      (i : ZMod (orderOf φ)) ∈ orbitMarks (orderOf φ) y.1 φ.1 S ∧
        ((i : ZMod 2) = 1 ↔ y.2.2 = 1) := by
  rw [intCast_mem_orbitMarks_thickLetters_iff]
  have hbit : φ.2.2.toAdd = 1 := ZMod.ne_zero_iff_eq_one.mp hφ
  have hcoord : (y.2.2 * φ.2.2 ^ i).toAdd = y.2.2.toAdd + (i : ZMod 2) := by
    calc
      _ = y.2.2.toAdd + i • φ.2.2.toAdd := rfl
      _ = _ := by rw [← Int.cast_smul_eq_zsmul (ZMod 2), hbit, smul_eq_mul, mul_one]
  have hparity (b k : ZMod 2) : (b + k ≠ 0) ↔ (k = 1 ↔ b = 0) := by decide +revert
  refine and_congr_right fun _ ↦ ?_
  -- Expose the additive coordinates so that the computed sum `hcoord` can rewrite the goal.
  change (y.2.2 * φ.2.2 ^ i).toAdd ≠ 0 ↔ ((i : ZMod 2) = 1 ↔ y.2.2.toAdd = 0)
  rw [hcoord, hparity]

/-- If Frobenius changes the inertia coordinate, a thick letter cannot have a thick
immediate predecessor. -/
theorem sub_one_notMem_orbitMarks_thickLetters (hφ : φ.2.2 ≠ 1) {i : ZMod (orderOf φ)}
    (hi : i ∈ orbitMarks (orderOf φ) y φ (thickLetters S)) :
    i - 1 ∉ orbitMarks (orderOf φ) y φ (thickLetters S) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  intro hprev
  have hprev' : ((k - 1 : ℤ) : ZMod (orderOf φ)) ∈
      orbitMarks (orderOf φ) y φ (thickLetters S) := by simpa using hprev
  have hk := (intCast_mem_orbitMarks_thickLetters_iff_of_snd_snd_ne_one hφ k |>.mp hi).2
  have hk' := (intCast_mem_orbitMarks_thickLetters_iff_of_snd_snd_ne_one hφ (k - 1) |>.mp hprev').2
  have himpossible (b : ZMod 2) : ¬ (b = 1 ↔ b - 1 = 1) := by decide +revert
  exact himpossible (k : ZMod 2) (hk.trans (by simpa using hk'.symm))

variable {T : Set ℤ} {a u : A} {L j : ℕ}

/-- The cluster bound for thick letters follows from the window bound on `A` in the long
case, and from separation by the projected order in the short case. -/
theorem NoRelation.hasMarkClusters_orbitMarks_thickLetters (hT : NoRelation L T)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L))
    (hdepth : (4 * L < orderOf φ.1 ∧ 2 * j < L) ∨ (orderOf φ.1 ≤ 4 * L ∧ j < orderOf φ.1)) :
    (orbitMarks (orderOf φ) y φ (thickLetters (u • ((a ^ ·) '' T)))).HasMarkClusters j := by
  have hN := orderOf_map_dvd (MonoidHom.fst A (C₂ × C₂)) φ
  apply Set.HasMarkClusters.mono _ orbitMarks_thickLetters_subset
  rcases hdepth with ⟨hlong, hj⟩ | ⟨hshort, hj⟩
  · exact hT.hasMarkClusters_orbitMarks hN hTM hlong hj
  · exact hasMarkClusters_orbitMarks_of_lt_orderOf hN
      (subsingleton_smul_zpowers_inter_smul_image_zpow_of_orderOf_le hTM hshort _ _) hj

open scoped Classical in
/-- Complex conjugation gives a two-letter orbit. The whole orbit is thick exactly when
its starting letter is thick. -/
theorem orbitMarks_thickLetters_conjugation :
    orderOf ((1, ε₂, 1) : A × C₂ × C₂) = 2 ∧
      orbitMarks 2 y (1, ε₂, 1) (thickLetters S) = if y ∈ thickLetters S then univ else ∅ := by
  have hc : orderOf ε₂ = 2 := by
    apply orderOf_eq_prime (p := 2) (by decide)
    decide
  have hN : orderOf ((1, ε₂, 1) : A × C₂ × C₂) = 2 := by simp [Prod.orderOf_mk, hc]
  refine ⟨hN, ?_⟩
  ext i
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  rw [intCast_mem_orbitMarks_iff hN.dvd]
  have hsame : y * ((1, ε₂, 1) : A × C₂ × C₂) ^ k ∈ thickLetters S ↔ y ∈ thickLetters S := by
    simp
  rw [hsame]
  by_cases hy : y ∈ thickLetters S
  · rw [ite_eq_left hy, iff_true_intro (mem_univ _)]
    exact iff_true_intro hy
  · rw [ite_eq_right hy, mem_empty_iff_false]
    exact iff_false_intro hy

/-- Apart from a wholly thick conjugation orbit, no three consecutive letters are thick
and at least one letter is not thick. In the split host, inertness in the distinguished
quadratic field says that the two binary coordinates of Frobenius are different. -/
theorem NoRelation.orbitMarks_thickLetters_not_three_consecutive (hT : NoRelation L T)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hL : 3 ≤ L)
    (hinert : φ.2.1 ≠ φ.2.2)
    (hex : ¬ (φ = (1, ε₂, 1) ∧ y ∈ thickLetters (u • ((a ^ ·) '' T)))) :
    let marks := orbitMarks (orderOf φ) y φ (thickLetters (u • ((a ^ ·) '' T)))
    (∀ i ∈ marks, i - 1 ∈ marks → i - 2 ∉ marks) ∧ ∃ i, i ∉ marks := by
  let marks := orbitMarks (orderOf φ) y φ (thickLetters (u • ((a ^ ·) '' T)))
  suffices h : ∀ i ∈ marks, i - 1 ∈ marks → i - 2 ∉ marks by
    refine ⟨h, ?_⟩
    by_contra! hall
    exact h 0 (hall 0) (hall (0 - 1)) (hall (0 - 2))
  by_cases hm : φ.2.2 = 1
  · by_cases hh : φ.1 = 1
    · have hf : φ.2.1 ≠ 1 := hm ▸ hinert
      have hbit : φ.2.1.toAdd = 1 := ZMod.ne_zero_iff_eq_one.mp hf
      have hφ : φ = (1, ε₂, 1) := Prod.ext hh (Prod.ext (congrArg ofAdd hbit) hm)
      have hy := not_and.mp hex hφ
      have hc := orbitMarks_thickLetters_conjugation (y := y) (S := u • ((a ^ ·) '' T))
      dsimp only [marks]
      rw [hφ, hc.1, hc.2, ite_eq_right hy]
      simp
    · have hN := orderOf_map_dvd (MonoidHom.fst A (C₂ × C₂)) φ
      by_cases hzero : orderOf φ.1 = 0
      · have hs := subsingleton_smul_zpowers_inter_smul_image_zpow_of_orderOf_le
          hTM (h := φ.1) (hzero ▸ Nat.zero_le _) y.1 u
        have hnoadj (i : ZMod (orderOf φ))
            (hi : i ∈ orbitMarks (orderOf φ) y φ (thickLetters (u • ((a ^ ·) '' T)))) :
            i - 1 ∉ orbitMarks (orderOf φ) y φ (thickLetters (u • ((a ^ ·) '' T))) := by
          obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
          intro hk
          have hp : ((k - 1 : ℤ) : ZMod (orderOf φ)) ∈ orbitMarks (orderOf φ) y.1 φ.1
              (u • ((a ^ ·) '' T)) := by simpa using orbitMarks_thickLetters_subset hk
          have hdiv := (modEq_of_mem_orbitMarks hN hs hp (orbitMarks_thickLetters_subset hi)).dvd
          simp [hzero] at hdiv
        exact fun i hi hi₁ ↦ (hnoadj i hi hi₁).elim
      · have hne := mt orderOf_eq_one_iff.mp hh
        have hord : 1 < orderOf φ.1 := by omega
        exact fun _ hi hi₁ hi₂ ↦ hT.sub_two_notMem_orbitMarks hN hTM hL hord
          (orbitMarks_thickLetters_subset hi) (orbitMarks_thickLetters_subset hi₁)
          (orbitMarks_thickLetters_subset hi₂)
  · exact fun _ hi hi₁ ↦ (sub_one_notMem_orbitMarks_thickLetters hm hi hi₁).elim

end TauCeti
