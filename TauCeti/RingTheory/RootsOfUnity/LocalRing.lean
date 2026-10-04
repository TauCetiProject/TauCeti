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
* `TauCeti.eq_of_residue_eq_of_pow_eq_one`, `IsPrimitiveRoot.map_residue`: the same statement for
  elements of the ring, and its consequence that reduction preserves primitive roots of unity of
  invertible order.
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

/-- Two `n`-th roots of unity with the same residue are equal, when `n` is invertible. -/
theorem eq_of_residue_eq_of_pow_eq_one {n : ℕ} (hn : IsUnit (n : R)) {x y : R} (hx : x ^ n = 1)
    (hy : y ^ n = 1) (h : residue R x = residue R y) : x = y := by
  have : NeZero n := ⟨by rintro rfl; simp at hn⟩
  have h' : rootsOfUnity.mkOfPowEq x hx = rootsOfUnity.mkOfPowEq y hy :=
    rootsOfUnityResidue_injective hn (Subtype.ext (Units.ext (by simpa using h)))
  simpa using congrArg (fun u : rootsOfUnity n R ↦ ((u : Rˣ) : R)) h'

end TauCeti

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- **Reduction preserves primitive roots of unity of invertible order.** -/
theorem map_residue {n : ℕ} (hn : IsUnit (n : R)) {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (residue R ζ) n := by
  refine ⟨by rw [← map_pow, hζ.pow_eq_one, map_one], fun l hl ↦ hζ.dvd_of_pow_eq_one l ?_⟩
  refine TauCeti.eq_of_residue_eq_of_pow_eq_one hn
    (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow n) ?_
  rw [map_pow, hl, map_one]

end IsPrimitiveRoot
