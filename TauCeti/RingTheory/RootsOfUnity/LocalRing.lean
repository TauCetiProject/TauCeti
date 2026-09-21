/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Roots of unity in a local ring and its residue field

Reduction modulo the maximal ideal maps the roots of unity of a local ring to those of its
residue field. This map is injective when the order is invertible in the ring.

## Main results

* `TauCeti.rootsOfUnityResidue`: the reduction homomorphism on roots of unity.
* `TauCeti.rootsOfUnityResidue_injective`: reduction is injective on roots of unity of invertible
  order.
-/

public section

noncomputable section

open IsLocalRing

namespace TauCeti

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Reduction modulo the maximal ideal, as a homomorphism between the groups of `n`-th roots of
unity of a local ring and of its residue field. -/
def rootsOfUnityResidue (n : ℕ) :
    rootsOfUnity n R →* rootsOfUnity n (ResidueField R) :=
  restrictRootsOfUnity (residue R) n

/-- The value of the reduction homomorphism on roots of unity. -/
@[simp]
theorem coe_rootsOfUnityResidue (n : ℕ) (ζ : rootsOfUnity n R) :
    ((rootsOfUnityResidue n ζ : (ResidueField R)ˣ) : ResidueField R) =
      residue R ((ζ : Rˣ) : R) := by
  rw [rootsOfUnityResidue, restrictRootsOfUnity_coe_apply]

/-- **Distinct roots of unity of invertible order have distinct reductions.** -/
theorem rootsOfUnityResidue_injective {n : ℕ} (hn : IsUnit (n : R)) :
    Function.Injective (rootsOfUnityResidue (R := R) n) := by
  refine (injective_iff_map_eq_one _).mpr fun ζ hζ ↦ ?_
  have hval : residue R ((ζ : Rˣ) : R) = 1 := by
    have h := congrArg
      (fun x : rootsOfUnity n (ResidueField R) ↦ ((x : (ResidueField R)ˣ) : ResidueField R)) hζ
    simpa using h
  have hpow : ((ζ : Rˣ) : R) ^ n = 1 := (mem_rootsOfUnity' n _).mp ζ.2
  let s := ∑ i ∈ Finset.range n, ((ζ : Rˣ) : R) ^ i
  have hs : IsUnit s := by
    rw [← residue_ne_zero_iff_isUnit]
    have hres : residue R s = residue R (n : R) := by
      simp [s, map_pow, hval]
    rw [hres, residue_ne_zero_iff_isUnit]
    exact hn
  have hgeom : s * (((ζ : Rˣ) : R) - 1) = 0 := by
    simpa [s, hpow] using geom_sum_mul ((ζ : Rˣ) : R) n
  ext
  exact sub_eq_zero.mp (hs.mul_right_eq_zero.mp hgeom)

end TauCeti
