/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Integrality

/-!
# The unique highest Lakshmibai–Seshadri path

For a dominant shape, the straight path is the only LS encoding annihilated by every
simple-root raising operator. This is a statement about the actual piecewise-linear root
operators, not an assumed crystal structure on the encodings.

First, nonnegative minimum simple-coroot heights force the initial direction to be dominant.
The unique dominant weight in a Weyl orbit is the shape itself, so its minimal coset
representative is the identity. Since the directions strictly decrease, there can be no
further direction. Finally, integrality of minimum heights converts annihilation by a raising
operator into nonnegativity of its minimum height.

The realization can be any additive map into a vector space over an ordered field, provided
its height forms agree with the simple coroots on the lattice. No spanning or regularity
assumption is imposed: weights on walls, central weights and empty root systems are included.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4 (LS paths and their highest path).
-/

public section

namespace TauCeti.LSPath

open RootPairing

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- The straight path is the only LS encoding of dominant shape whose minimum simple-coroot
heights are all nonnegative. The height forms must agree with the actual simple coroots. -/
theorem eq_straight_iff_forall_minHeight_nonneg [P.flip.IsReduced]
    (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) :
    π = straight lam ↔ ∀ i, 0 ≤ (π.toPLPath 𝕜 f).minHeight (F i) := by
  constructor
  · rintro rfl i
    rw [toPLPath_straight, PLPath.minHeight_straight, hF]
    apply le_min le_rfl
    exact_mod_cast (mem_dominantChamber P b lam).mp hlam i i.2
  · intro h
    apply π.eq_straight_iff_dir_zero_eq_one.mpr
    have hdom : (π.dir 0).1 • lam ∈ dominantChamber P b := by
      apply (mem_dominantChamber P b _).mpr
      intro i hi
      have hprod : 0 ≤ (π.duration 0 : 𝕜) * (P.coroot' i ((π.dir 0).1 • lam) : 𝕜) := by
        simpa only [hF] using
          (h ⟨i, hi⟩).trans (π.minHeight_le_duration_mul_dir_zero f (F ⟨i, hi⟩))
      have hd : (0 : 𝕜) < (π.duration 0 : ℚ) := Rat.cast_pos.mpr (π.duration_pos 0)
      exact_mod_cast nonneg_of_mul_nonneg_right hprod hd
    have hfix := smul_eq_self_of_smul_mem_dominantChamber P b (π.dir 0).1 hlam hdom
    exact eq_of_isMinimalCosetRep_of_smul_eq hlam (π.dir 0).2
      ((weylCoxeterSystem P b).isMinimalCosetRep_one _) (by simpa using hfix)

/-- **Uniqueness of the highest LS path.** For a dominant shape, all actual simple-root raising
operators vanish exactly on the straight path. No operator-stability assumption is needed. -/
theorem forall_raise_eq_none_iff [P.flip.IsReduced]
    (π : LSPath P b lam) (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    (F : b.support → Module.Dual 𝕜 V)
    (hF : ∀ i m, F i (f m) = (P.coroot' i m : 𝕜)) :
    (∀ i, PLPath.raise (F i) (f (P.root i)) (π.toPLPath 𝕜 f) = none) ↔
      π = straight lam := by
  rw [π.eq_straight_iff_forall_minHeight_nonneg hlam f F hF]
  constructor
  · intro h i
    obtain ⟨z, hz⟩ := π.exists_minHeight_eq_intCast hlam f i (F i) (hF i)
    have hgt := PLPath.raise_eq_none_iff.mp (h i)
    rw [hz] at hgt ⊢
    have hz' : (-1 : ℤ) < z := by exact_mod_cast hgt
    have : 0 ≤ z := by omega
    exact_mod_cast this
  · intro h i
    exact PLPath.raise_eq_none_iff.mpr (lt_of_lt_of_le (by norm_num) (h i))

end TauCeti.LSPath
