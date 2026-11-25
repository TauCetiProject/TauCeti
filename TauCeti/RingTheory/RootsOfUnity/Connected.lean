/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Algebra.Group.Invertible.Basic
import Mathlib.Algebra.Ring.GeomSum
import TauCeti.RingTheory.Idempotents.Connected.Spectrum
import TauCeti.RingTheory.Idempotents.RootOfOne

/-!
# Roots of unity over a connected prime spectrum

A root of unity of invertible order on a connected spectrum is determined by its image at
any point. More generally, `RingHom.injOn_pow_eq_one` shows that a ring map to any
nontrivial semiring detects equality of such roots.
-/

public section

namespace RingHom

/-- If `Spec R` is preconnected and `n` is a unit in `R`, any ring homomorphism from `R`
to a nontrivial semiring is injective on the `n`-th roots of unity. -/
theorem injOn_pow_eq_one {R S : Type*} [CommRing R] [Semiring S] [Nontrivial S]
    [PreconnectedSpace (PrimeSpectrum R)] (f : R →+* S) {n : ℕ} (hn : IsUnit (n : R)) :
    Set.InjOn f {x | x ^ n = 1} := by
  intro x hx y hy hxy
  have hpowX : x ^ n = 1 := hx
  have hpowY : y ^ n = 1 := hy
  have : Nontrivial R := f.domain_nontrivial
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  let u : Rˣ := (IsUnit.of_pow_eq_one hpowY hn0).unit
  have hu : (u : R) = y := IsUnit.unit_spec _
  let z := x * ((u⁻¹ : Rˣ) : R)
  have hz : z ^ n = 1 := by
    have hun : u ^ n = 1 := Units.ext (by simpa [hu] using hpowY)
    simp [z, mul_pow, hpowX, ← Units.val_pow_eq_pow_val, inv_pow, hun]
  have hfz : f z = 1 := by
    rw [map_mul, hxy, ← hu, ← map_mul, Units.mul_inv, map_one]
  let := hn.invertible
  set e : R := (⅟(n : R)) • ∑ i ∈ Finset.range n, z ^ i with he_def
  have he : IsIdempotentElem e := TauCeti.isIdempotentElem_invOf_smul_geom_sum R hz
  -- The averaging idempotent maps to `1`, so connectedness forces it to be `1` globally.
  have hfe : f e = 1 := by
    have hs : f (∑ i ∈ Finset.range n, z ^ i) = f (n : R) := by simp [hfz]
    rw [he_def, smul_eq_mul, map_mul, hs, ← map_mul, invOf_mul_self, map_one]
  have he1 : e = 1 := he.eq_zero_or_eq_one_of_preconnectedSpace.resolve_left fun h ↦ by
    simp [h] at hfe
  have hgeom : (∑ i ∈ Finset.range n, z ^ i) * (z - 1) = 0 := by
    simpa [hz] using geom_sum_mul z n
  have hze : e * (z - 1) = 0 := by rw [he_def, smul_mul_assoc, hgeom, smul_zero]
  have hz1 : z = 1 := sub_eq_zero.mp (by simpa [he1] using hze)
  calc
    x = z * (u : R) := by simp [z, mul_assoc]
    _ = y := by simp [hz1, hu]

end RingHom
