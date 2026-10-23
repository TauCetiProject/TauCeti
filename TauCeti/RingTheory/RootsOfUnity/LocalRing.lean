/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.FieldTheory.Separable

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
* `TauCeti.aeval_minpoly_eq_zero_of_aeval_residue_eq_zero`: a root of unity of invertible order
  whose residue is a root of the minimal polynomial of an integral root of unity is itself a root
  of that minimal polynomial.
-/

public section

noncomputable section

open IsLocalRing Polynomial

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

/-- Let `A` be an integrally closed domain, let `ζ` be an `n`-th root of unity of a domain `S`
over `A` such that `ζ` is integral over `A`, and let `R` be a local domain over `A` in which `n` is
invertible. An `n`-th root of unity `ξ` of `R` whose residue is a root of the minimal polynomial of
`ζ` over `A` is itself a root of that minimal polynomial. -/
theorem aeval_minpoly_eq_zero_of_aeval_residue_eq_zero {A S : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing S] [IsDomain S] [Algebra A S] [Module.IsTorsionFree A S]
    [IsDomain R] [Algebra A R] {n : ℕ} (hn : IsUnit (n : R)) {ζ : S} (hζA : IsIntegral A ζ)
    (hζ : ζ ^ n = 1) {ξ : R} (hξ : ξ ^ n = 1) (hres : aeval (residue R ξ) (minpoly A ζ) = 0) :
    aeval ξ (minpoly A ζ) = 0 := by
  obtain ⟨h, hgh⟩ : minpoly A ζ ∣ X ^ n - 1 :=
    minpoly.isIntegrallyClosed_dvd hζA (by simp [hζ])
  have hhξ : aeval ξ h ≠ 0 := by
    intro H
    have hhξ₀ : aeval (residue R ξ) h = 0 := by
      rw [← ResidueField.algebraMap_eq, aeval_algebraMap_apply, H, map_zero]
    -- `X ^ n - 1 = g h` is separable over the residue field, so `g` and `h` are coprime there.
    have hn' : (n : ResidueField R) ≠ 0 := by
      simpa only [map_natCast] using (residue_ne_zero_iff_isUnit _).2 hn
    have hsep : ((minpoly A ζ).map (algebraMap A (ResidueField R)) *
        h.map (algebraMap A (ResidueField R))).Separable := by
      rw [← Polynomial.map_mul, ← hgh, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_one]
      exact X_pow_sub_one_separable_iff.2 hn'
    rcases aeval_ne_zero_of_isCoprime hsep.isCoprime (residue R ξ) with hg | hh
    · exact hg (by rw [aeval_map_algebraMap, hres])
    · exact hh (by rw [aeval_map_algebraMap, hhξ₀])
  refine (mul_eq_zero.1 ?_).resolve_right hhξ
  rw [← map_mul, ← hgh, map_sub, map_pow, aeval_X, map_one, hξ, sub_self]

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
