/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Stretch
public import TauCeti.Data.Rat.ZMultiples

/-!
# Integral subdivisions of stretched LS paths

After clearing the rational segment durations, a stretched Lakshmibai–Seshadri path is a
concatenation of straight paths along integral Weyl-orbit weights of the original shape.
The number of factors is exactly the stretching factor. For a dominant shape one stretching
factor works simultaneously for every LS path, by finiteness of the set of LS encodings.

`LSPath.subdivisionWord` records these factors in their original order, repeating each
direction the prescribed number of times. `LSPath.toPLPath_stretch_eq_prod_subdivisionWord`
identifies the concatenation with the actual stretched realization; this is not merely an
endpoint identity. `LSPath.exists_uniform_subdivision` supplies a common factor and words of
that length. These words provide integral straight factors for comparing path concatenation
with tensor products. No compatibility of stretching with root operators is asserted here.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §§4–5 (LS paths, stretching and subdivision).
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- The ordered word obtained by repeating the `j`-th direction `m j` times.
When `m j = n * duration j`, this subdivides the dilation by `n` into orbit-weight segments. -/
def subdivisionWord (π : LSPath P b lam) (m : Fin (π.length + 1) → ℕ) : List P.weylGroup :=
  (List.ofFn fun j ↦ List.replicate (m j) (π.dir j).1).flatten

/-- The subdivision word lists the repeated directions in their original order. -/
theorem subdivisionWord_def (π : LSPath P b lam) (m : Fin (π.length + 1) → ℕ) :
    π.subdivisionWord m =
      (List.ofFn fun j ↦ List.replicate (m j) (π.dir j).1).flatten := (rfl)

/-- The number of straight factors is the sum of their multiplicities. -/
@[simp]
theorem length_subdivisionWord (π : LSPath P b lam) (m : Fin (π.length + 1) → ℕ) :
    (π.subdivisionWord m).length = ∑ j, m j := by
  simp only [subdivisionWord_def, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.length_replicate, List.sum_ofFn]

/-- A direction occurs in the subdivision word exactly when it has positive multiplicity. -/
@[simp]
theorem mem_subdivisionWord_iff (π : LSPath P b lam) (m : Fin (π.length + 1) → ℕ)
    {w : P.weylGroup} :
    w ∈ π.subdivisionWord m ↔ ∃ j, 0 < m j ∧ (π.dir j).1 = w := by
  constructor
  · intro hw
    obtain ⟨l, hl, hw⟩ := List.mem_flatten.mp hw
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hl
    obtain ⟨hm, hw⟩ := List.mem_replicate.mp hw
    exact ⟨j, Nat.pos_of_ne_zero hm, hw.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩,
      List.mem_replicate.mpr ⟨hj.ne', rfl⟩⟩

/-- Every letter remains a minimal representative for the stabilizer of the original shape. -/
theorem isMinimalCosetRep_of_mem_subdivisionWord (π : LSPath P b lam)
    (m : Fin (π.length + 1) → ℕ) {w : P.weylGroup} (hw : w ∈ π.subdivisionWord m) :
    (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w := by
  obtain ⟨j, _, rfl⟩ := (π.mem_subdivisionWord_iff m).mp hw
  exact (π.dir j).2

/-- Clearing the durations makes the subdivision word have exactly the stretching length. -/
theorem length_subdivisionWord_eq (π : LSPath P b lam) (n : ℕ)
    (m : Fin (π.length + 1) → ℕ)
    (hm : ∀ j, (m j : ℚ) = (n : ℚ) * π.duration j) :
    (π.subdivisionWord m).length = n := by
  rw [length_subdivisionWord]
  have hsum : (∑ j, (m j : ℚ)) = n := by
    simp only [hm, ← Finset.mul_sum, sum_duration, mul_one]
  exact_mod_cast hsum

section Realization

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

/-- Subdivision into integral orbit segments realizes a stretched LS path as a product of
powers of straight paths, in the original direction order. -/
theorem toPLPath_stretch_eq_prod_pow (π : LSPath P b lam) (n : ℕ) (hn : 0 < n)
    (m : Fin (π.length + 1) → ℕ)
    (hm : ∀ j, (m j : ℚ) = (n : ℚ) * π.duration j) :
    (π.stretch n hn).toPLPath 𝕜 f =
      (List.ofFn fun j ↦ PLPath.straight 𝕜 (f ((π.dir j).1 • lam)) ^ m j).prod := by
  rw [toPLPath_stretch, toPLPath_def, PLPath.map_ofSegments, ← PLPath.prod_map_straight]
  simp only [timed_def, List.map_ofFn, Function.comp_def, LinearMap.smul_apply,
    LinearMap.id_apply, smul_smul]
  congr 2
  funext j
  have hj : (n : 𝕜) * (π.duration j : 𝕜) = (m j : 𝕜) := by
    exact_mod_cast (hm j).symm
  rw [hj, PLPath.straight_natCast_smul]

/-- The actual stretched path is the concatenation of the straight orbit paths in its
subdivision word. Equality holds as paths modulo the admitted reparametrizations. -/
theorem toPLPath_stretch_eq_prod_subdivisionWord (π : LSPath P b lam) (n : ℕ) (hn : 0 < n)
    (m : Fin (π.length + 1) → ℕ)
    (hm : ∀ j, (m j : ℚ) = (n : ℚ) * π.duration j) :
    (π.stretch n hn).toPLPath 𝕜 f =
      ((π.subdivisionWord m).map fun w ↦ PLPath.straight 𝕜 (f (w • lam))).prod := by
  rw [π.toPLPath_stretch_eq_prod_pow 𝕜 f n hn m hm]
  simp [subdivisionWord_def, List.map_flatten, List.map_ofFn, List.prod_flatten,
    List.map_replicate, List.prod_replicate, Function.comp_def]

end Realization

variable [P.flip.IsReduced]

/-- For a dominant shape, one positive integer clears the durations of all LS paths
simultaneously. Each segment then has a strictly positive integral multiplicity. -/
theorem exists_uniform_integral_durations (hlam : lam ∈ dominantChamber P b) :
    ∃ n : ℕ, 0 < n ∧ ∀ π : LSPath P b lam,
      ∃ m : Fin (π.length + 1) → ℕ,
        (∀ j, 0 < m j) ∧ ∀ j, (m j : ℚ) = (n : ℚ) * π.duration j := by
  have := LSPath.finite hlam
  obtain ⟨n, hn, hden⟩ := Rat.exists_forall_mem_zmultiples_inv_natCast
    (fun x : (π : LSPath P b lam) × Fin (π.length + 1) ↦ x.1.duration x.2)
  have hint (π : LSPath P b lam) (j : Fin (π.length + 1)) :
      ∃ k : ℕ, 0 < k ∧ (k : ℚ) = (n : ℚ) * π.duration j := by
    have hd := (Rat.mem_zmultiples_inv_natCast_iff hn.ne').mp (hden ⟨π, j⟩)
    obtain ⟨z, hz⟩ := (Rat.den_dvd_iff_exists_mul_intCast_eq (π.duration j) (n : ℤ)).mp
      (by exact_mod_cast hd)
    have hpos : (0 : ℚ) < z := by
      rw [← hz]
      exact mul_pos (π.duration_pos j) (Nat.cast_pos.mpr hn)
    have hzpos : 0 < z := by exact_mod_cast hpos
    refine ⟨z.toNat, by omega, ?_⟩
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hzpos.le, ← hz, Int.cast_natCast, mul_comm]
  refine ⟨n, hn, fun π ↦ ?_⟩
  choose m hpos hm using hint π
  exact ⟨m, hpos, hm⟩

variable (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] (f : M →+ V)

/-- Every LS path of a fixed dominant shape admits a common positive stretching factor for
which it is a concatenation of exactly that many straight paths along the original Weyl orbit.
The letters are minimal coset representatives, including on chamber walls. -/
theorem exists_uniform_subdivision (hlam : lam ∈ dominantChamber P b) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∀ π : LSPath P b lam,
      ∃ word : List P.weylGroup, word.length = n ∧
        (∀ w ∈ word, (weylCoxeterSystem P b).IsMinimalCosetRep (P.wallIndices b lam) w) ∧
        (π.stretch n hn).toPLPath 𝕜 f =
          (word.map fun w ↦ PLPath.straight 𝕜 (f (w • lam))).prod := by
  obtain ⟨n, hn, h⟩ := exists_uniform_integral_durations hlam
  refine ⟨n, hn, fun π ↦ ?_⟩
  obtain ⟨m, _, hm⟩ := h π
  exact ⟨π.subdivisionWord m, π.length_subdivisionWord_eq n m hm,
    fun _ hw ↦ π.isMinimalCosetRep_of_mem_subdivisionWord m hw,
    π.toPLPath_stretch_eq_prod_subdivisionWord 𝕜 f n hn m hm⟩

end TauCeti.LSPath
