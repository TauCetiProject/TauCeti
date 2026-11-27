/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.OrderOfElement.OrbitMarks
import TauCeti.Data.ZMod.Two

/-!
# Thick letters in Frobenius order

In the coordinates `G = A × ⟨c⟩ × ⟨σ_d⟩` for a cyclic CM host, the infinite-place
representatives have equal involution coordinates. Passing from a letter to its place
changes only the `c` coordinate. Thus a letter is thick precisely when its `σ_d` coordinate
is nonzero and its `A` coordinate belongs to the translate of the thick set.

Along an orbit, the `σ_d` coordinate either stays fixed or alternates. This lets us transfer
cluster bounds for the orbit in `A` to the word of thick letters. The only all-marked orbit
outside the subgroup of place representatives is the orbit of complex conjugation at a
thick place.

The thick-letter description and long-window bound correspond to Levent Alpöge's
`Formalism.HC.Frame.placeOf` and `GlobalTheory.HTW.LongWindow.main`.
-/

public section

open Set Multiplicative
open scoped Pointwise

namespace TauCeti.FrobeniusRiesz

variable {A : Type*} [Group A]

/-- Mark the `N`-periodic orbit of `y` under `φ` at the thick letters. The two involution
coordinates, in order, correspond to complex conjugation and the distinguished ramified
involution. The set `S` is the translate of the thick set in the first factor. -/
def thickLetterOrbitMarks (N : ℕ) (y φ : A × Multiplicative (ZMod 2 × ZMod 2)) (S : Set A) :
    Set (ZMod N) :=
  orbitMarks N y φ (S ×ˢ {b | b.toAdd.2 = 1})

variable {N : ℕ} {y φ : A × Multiplicative (ZMod 2 × ZMod 2)} {S : Set A}

/-- Thick letters are the orbit marks of the product of the translated thick set with the
involution coordinates whose second component is `1`. -/
theorem thickLetterOrbitMarks_def :
    thickLetterOrbitMarks N y φ S = orbitMarks N y φ (S ×ˢ {b | b.toAdd.2 = 1}) := (rfl)

/-- At a compatible period, a thick mark tests the projected orbit point and the parity of
the second involution coordinate. -/
@[simp] theorem intCast_mem_thickLetterOrbitMarks_iff (hN : orderOf φ ∣ N) (i : ℤ) :
    (i : ZMod N) ∈ thickLetterOrbitMarks N y φ S ↔
      y.1 * φ.1 ^ i ∈ S ∧ y.2.toAdd.2 + (i : ZMod 2) * φ.2.toAdd.2 = 1 := by
  rw [thickLetterOrbitMarks_def, intCast_mem_orbitMarks_iff hN]
  simp [toAdd_mul, toAdd_zpow, zsmul_eq_mul]

/-- Forgetting the involution coordinates can only add marks. -/
theorem thickLetterOrbitMarks_subset :
    thickLetterOrbitMarks N y φ S ⊆ orbitMarks N y.1 φ.1 S := by
  rw [thickLetterOrbitMarks_def]
  intro i hi
  obtain ⟨k, hk, rfl⟩ := mem_orbitMarks_iff.mp hi
  exact mem_orbitMarks_iff.mpr ⟨k, hk.1, rfl⟩

/-- When the second involution coordinate does not change along an orbit, its letter marks
are either all of the projected marks or none of them. -/
theorem mem_thickLetterOrbitMarks_iff_of_snd_eq_zero (hN : orderOf φ ∣ N)
    (hφ : φ.2.toAdd.2 = 0) (i : ZMod N) :
    i ∈ thickLetterOrbitMarks N y φ S ↔ i ∈ orbitMarks N y.1 φ.1 S ∧ y.2.toAdd.2 = 1 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  have hproj : orderOf φ.1 ∣ N := (orderOf_map_dvd (MonoidHom.fst A _) φ).trans hN
  rw [intCast_mem_thickLetterOrbitMarks_iff hN, intCast_mem_orbitMarks_iff hproj]
  simp [hφ]

/-- When the second involution coordinate alternates, any two thick marks have the same
parity, expressed on their integer representatives. -/
theorem modEq_two_of_mem_thickLetterOrbitMarks (hN : orderOf φ ∣ N) (hφ : φ.2.toAdd.2 = 1)
    {i k : ℤ} (hi : (i : ZMod N) ∈ thickLetterOrbitMarks N y φ S)
    (hk : (k : ZMod N) ∈ thickLetterOrbitMarks N y φ S) : i ≡ k [ZMOD 2] := by
  have hi' := ((intCast_mem_thickLetterOrbitMarks_iff hN i).mp hi).2
  have hk' := ((intCast_mem_thickLetterOrbitMarks_iff hN k).mp hk).2
  simp only [hφ, mul_one] at hi' hk'
  exact (ZMod.intCast_eq_intCast_iff i k 2).mp (add_left_cancel (hi'.trans hk'.symm))

/-- In the alternating case no thick mark has an immediately preceding thick mark. -/
theorem sub_one_notMem_thickLetterOrbitMarks (hN : orderOf φ ∣ N) (hφ : φ.2.toAdd.2 = 1)
    {i : ZMod N} (hi : i ∈ thickLetterOrbitMarks N y φ S) :
    i - 1 ∉ thickLetterOrbitMarks N y φ S := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  intro hprev
  have hk : ((k - 1 : ℤ) : ZMod N) ∈ thickLetterOrbitMarks N y φ S := by simpa using hprev
  have h := (modEq_two_of_mem_thickLetterOrbitMarks hN hφ hk hi).dvd
  omega

section ThickSet

variable {a u : A} {T : Set ℤ} {L j : ℕ}

/-- The thick-letter marks have clusters of depth `j` when either the `2 * j + 1` tested
positions fit in a long-orbit window of length `L`, or `j` is below the order of a short
projected orbit. -/
theorem hasMarkClusters_thickLetterOrbit (hT : NoRelation L T)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L))
    (hdepth : (4 * L < orderOf φ.1 ∧ 2 * j < L) ∨
      (orderOf φ.1 ≤ 4 * L ∧ j < orderOf φ.1)) :
    (thickLetterOrbitMarks (orderOf φ) y φ (u • ((a ^ ·) '' T))).HasMarkClusters j := by
  apply Set.HasMarkClusters.mono _ thickLetterOrbitMarks_subset
  have hd := orderOf_map_dvd (MonoidHom.fst A _) φ
  rcases hdepth with ⟨hlong, hj⟩ | ⟨hshort, hj⟩
  · exact hT.hasMarkClusters_orbitMarks hd hTM hlong hj
  · exact hasMarkClusters_orbitMarks_of_lt_orderOf hd
      (subsingleton_smul_zpowers_inter_smul_image_zpow_of_orderOf_le hTM hshort y.1 u) hj

/-- Three consecutive letters cannot all be thick when the second involution coordinate
alternates or the projected orbit has finite order greater than one. -/
theorem sub_two_notMem_thickLetterOrbitMarks (hT : NoRelation L T)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hL : 3 ≤ L)
    (hφ : φ.2.toAdd.2 = 1 ∨ 1 < orderOf φ.1)
    {i : ZMod (orderOf φ)}
    (hi : i ∈ thickLetterOrbitMarks (orderOf φ) y φ (u • ((a ^ ·) '' T)))
    (hi₁ : i - 1 ∈ thickLetterOrbitMarks (orderOf φ) y φ (u • ((a ^ ·) '' T))) :
    i - 2 ∉ thickLetterOrbitMarks (orderOf φ) y φ (u • ((a ^ ·) '' T)) := by
  rcases hφ with hstep | hproj
  · exact (sub_one_notMem_thickLetterOrbitMarks dvd_rfl hstep hi hi₁).elim
  · exact fun hi₂ ↦ hT.sub_two_notMem_orbitMarks (orderOf_map_dvd (MonoidHom.fst A _) φ)
      hTM hL hproj (thickLetterOrbitMarks_subset hi) (thickLetterOrbitMarks_subset hi₁)
      (thickLetterOrbitMarks_subset hi₂)

/-- On an orbit of finite order outside the subgroup of place representatives, every letter
is thick exactly when the step is complex conjugation and the starting letter is thick. -/
theorem thickLetterOrbitMarks_eq_univ_iff (hT : NoRelation L T)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hL : 3 ≤ L)
    (hφ : 0 < orderOf φ) (hout : φ.2.toAdd.1 ≠ φ.2.toAdd.2) :
    thickLetterOrbitMarks (orderOf φ) y φ (u • ((a ^ ·) '' T)) = univ ↔
      φ = (1, ofAdd (1, 0)) ∧ y.1 ∈ u • ((a ^ ·) '' T) ∧ y.2.toAdd.2 = 1 := by
  constructor
  · intro hall
    have hm (i : ZMod (orderOf φ)) : i ∈ thickLetterOrbitMarks (orderOf φ) y φ
        (u • ((a ^ ·) '' T)) := hall ▸ mem_univ i
    have hno : ¬ (φ.2.toAdd.2 = 1 ∨ 1 < orderOf φ.1) := fun hd ↦
      sub_two_notMem_thickLetterOrbitMarks hT hTM hL hd (hm 0) (hm (0 - 1)) (hm (0 - 2))
    have hpos : 0 < orderOf φ.1 := Nat.pos_of_dvd_of_pos
      (orderOf_map_dvd (MonoidHom.fst A _) φ) hφ
    have hfirst : φ.1 = 1 := orderOf_eq_one_iff.mp (by omega)
    have hsnd : φ.2.toAdd.2 = 0 := by
      rcases ZMod.eq_zero_or_eq_one φ.2.toAdd.2 with hz | ho
      · exact hz
      · exact (hno (.inl ho)).elim
    have hf : φ.2.toAdd.1 = 1 := ZMod.ne_zero_iff_eq_one.mp (hsnd ▸ hout)
    have hstep : φ = (1, ofAdd (1, 0)) := Prod.ext hfirst (toAdd.injective (Prod.ext hf hsnd))
    have hzero : ((0 : ℤ) : ZMod (orderOf φ)) ∈ thickLetterOrbitMarks (orderOf φ) y φ
        (u • ((a ^ ·) '' T)) := by simpa only [Int.cast_zero] using hm 0
    exact ⟨hstep, by simpa using (intCast_mem_thickLetterOrbitMarks_iff dvd_rfl 0).mp hzero⟩
  · rintro ⟨rfl, hy, hys⟩
    apply eq_univ_of_forall
    intro i
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
    exact (intCast_mem_thickLetterOrbitMarks_iff dvd_rfl k).mpr
      (by simpa [one_zpow] using And.intro hy hys)

end ThickSet

end TauCeti.FrobeniusRiesz
