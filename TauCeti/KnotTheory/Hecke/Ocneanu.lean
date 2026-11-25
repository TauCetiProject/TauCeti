/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Polynomial
public import TauCeti.KnotTheory.Hecke
import Mathlib.Tactic.Ring

/-!
# Base-change naturality and character specializations of the Ocneanu braid trace

Specializing `TauCeti.MarkovBraid.heckeTrace` to the universal algebraic Ocneanu trace
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace R q z` produces Jones's normalized Hecke
braid-closure functional over an arbitrary commutative ring `R`. This file records its
ring-homomorphism naturality and its two one-dimensional character specializations (`z = q` and
`z = -q⁻¹`), where both Markov normalization equations hold unconditionally with `C = 1` and the
invariant is identically `1` (including at `q = ±1`).

## Main results

* `TauCeti.MarkovBraid.map_heckeTrace_ocneanuTrace`: every ring homomorphism commutes with
  `heckeTrace` applied to `ocneanuTrace`.
* `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_indexCharacter` and
  `TauCeti.MarkovBraid.heckeTrace_ocneanuTrace_signCharacter`: the index-character (`z = q`,
  `l = q⁻¹`) and sign-character (`z = -q⁻¹`, `l = -q`) specializations evaluate identically to `1`.

## References

* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388, Sections 5–6.
-/

public section

namespace TauCeti

open InfiniteTypeAHeckeAlgebra (ocneanuTrace isMarkovTrace_ocneanuTrace)

namespace MarkovBraid

/-- **Base-change naturality of the normalized Ocneanu braid trace.** Every ring homomorphism
`f : R →+* S` commutes with `heckeTrace` applied to `ocneanuTrace`. -/
theorem map_heckeTrace_ocneanuTrace {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (q : Rˣ) (z C : R) (l : Rˣ) (β : MarkovBraid) :
    f (β.heckeTrace (ocneanuTrace R q z) C l) =
      β.heckeTrace (ocneanuTrace S (Units.map f.toMonoidHom q) (f z))
        (f C) (Units.map f.toMonoidHom l) := by
  let : Algebra R S := f.toAlgebra
  have hq : algebraMap R S q = ((Units.map f.toMonoidHom q : Sˣ) : S) := by
    simp [RingHom.algebraMap_toAlgebra]
  have htr : f (ocneanuTrace R q z
        (InfiniteTypeAHeckeAlgebra.braidHom R q (β.predStrands + 1) β.braid)) =
      ocneanuTrace S (Units.map f.toMonoidHom q) (f z)
        (InfiniteTypeAHeckeAlgebra.braidHom S (Units.map f.toMonoidHom q) (β.predStrands + 1)
          β.braid) := by
    simpa only [RingHom.algebraMap_toAlgebra] using
      (InfiniteTypeAHeckeAlgebra.ocneanuTrace_braidHom_algebraMap hq z
        (β.predStrands + 1) β.braid).symm
  simp only [heckeTrace_def, map_mul, map_pow, htr]
  congr 2
  exact (Units.coe_map (f : R →* S) (l ^ _)).symm.trans
    (congrArg Units.val (map_zpow (Units.map (f : R →* S)) l _))

/-- **Index-character specialization (`z = q`, `C = 1`, `l = q⁻¹`).** Over any commutative ring `R`
and for any `q : Rˣ` (including `q = ±1`), the normalized Ocneanu trace at `(z, C, l) = (q, 1, q⁻¹)`
is identically `1`. -/
@[simp]
theorem heckeTrace_ocneanuTrace_indexCharacter {R : Type*} [CommRing R] (q : Rˣ)
    (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R q (q : R)) 1 q⁻¹ = 1 := by
  have hnorm := IsHeckeNormalization.of_mul_eq_inv_sub (q := q) (z := (q : R)) (l := q⁻¹)
    (one_mul (1 : R)) (by simp) (by simp)
  have hpos : ((q⁻¹ : Rˣ) : R) * (q : R) = 1 := by simpa only [one_mul] using hnorm.stabilize
  have hneg : (↑((q⁻¹ : Rˣ)⁻¹) : R) * ((q : R) - ((q : R) - ↑q⁻¹)) = 1 := by
    simpa only [one_mul] using hnorm.stabilizeInv
  exact β.heckeTrace_eq_one (isMarkovTrace_ocneanuTrace (q : R)) hpos hneg

/-- **Sign-character specialization (`z = -q⁻¹`, `C = 1`, `l = -q`).** Over any commutative ring `R`
and for any `q : Rˣ` (including `q = ±1`), the normalized Ocneanu trace at
`(z, C, l) = (-q⁻¹, 1, -q)` is identically `1`. -/
@[simp]
theorem heckeTrace_ocneanuTrace_signCharacter {R : Type*} [CommRing R] (q : Rˣ)
    (β : MarkovBraid) :
    β.heckeTrace (ocneanuTrace R q (-(↑q⁻¹ : R))) 1 (-q) = 1 := by
  have hnorm := IsHeckeNormalization.of_mul_eq_inv_sub (q := q) (z := -(↑q⁻¹ : R)) (l := -q)
    (one_mul (1 : R)) (by simp; ring) (by simp)
  have hpos : ((-q : Rˣ) : R) * (-(↑q⁻¹ : R)) = 1 := by simpa only [one_mul] using hnorm.stabilize
  have hneg : (↑((-q : Rˣ)⁻¹) : R) * (-(↑q⁻¹ : R) - ((q : R) - ↑q⁻¹)) = 1 := by
    simpa only [one_mul] using hnorm.stabilizeInv
  exact β.heckeTrace_eq_one (isMarkovTrace_ocneanuTrace (-(↑q⁻¹ : R))) hpos hneg

end MarkovBraid

end TauCeti
