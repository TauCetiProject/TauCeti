/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Characteristic polynomial and multiplicative order under matrix intertwining

If `V` semiconjugates `M` to `G` over `R` (`V * M = G * V`) and `V.map f` is left-invertible over a
commutative ring `S` for an injective ring homomorphism `f : R →+* S`, then `M` and `G` become
conjugate over `S` and therefore have the same characteristic polynomial and multiplicative order.

## Main results

* `Matrix.charpoly_eq_of_semiconjBy`: `M.charpoly = G.charpoly` under an injective scalar extension
  invertible on the intertwiner.
* `Matrix.orderOf_eq_of_semiconjBy`: `orderOf M = orderOf G` under the same hypothesis.
-/

public section

namespace Matrix

variable {κ R S : Type*} [Fintype κ] [DecidableEq κ]

/-- **Characteristic polynomial invariance under intertwining.** If `V * M = G * V` over `R` and
`V.map f` has a left inverse `U` over `S` for an injective ring homomorphism `f : R →+* S`, then
`M.charpoly = G.charpoly`. -/
theorem charpoly_eq_of_semiconjBy [CommRing R] [CommRing S] {V M G : Matrix κ κ R}
    (h : SemiconjBy V M G) {f : R →+* S} (hf : Function.Injective f) {U : Matrix κ κ S}
    (hUV : U * V.map f = 1) :
    M.charpoly = G.charpoly := by
  have hVU : V.map f * U = 1 := mul_eq_one_comm.1 hUV
  have hinter : V.map f * M.map f = G.map f * V.map f := by
    simpa only [map_mul, RingHom.mapMatrix_apply] using congrArg f.mapMatrix h.eq
  have hconj : V.map f * M.map f * U = G.map f := by
    rw [hinter, Matrix.mul_assoc, hVU, Matrix.mul_one]
  apply Polynomial.map_injective f hf
  rw [← charpoly_map, ← charpoly_map, ← hconj, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUV,
    Matrix.one_mul]

/-- **Multiplicative order invariance under intertwining.** If `V * M = G * V` over `R` and
`V.map f` has a left inverse `U` over `S` for an injective ring homomorphism `f : R →+* S`, then
`orderOf M = orderOf G`. -/
theorem orderOf_eq_of_semiconjBy [Semiring R] [CommRing S] {V M G : Matrix κ κ R}
    (h : SemiconjBy V M G) {f : R →+* S} (hf : Function.Injective f) {U : Matrix κ κ S}
    (hUV : U * V.map f = 1) :
    orderOf M = orderOf G := by
  have hVU : V.map f * U = 1 := mul_eq_one_comm.1 hUV
  have hinter : SemiconjBy (V.map f) (M.map f) (G.map f) := by
    simpa only [SemiconjBy, map_mul, RingHom.mapMatrix_apply] using congrArg f.mapMatrix h.eq
  have hφ : Function.Injective (f.mapMatrix : Matrix κ κ R →+* Matrix κ κ S) :=
    Matrix.map_injective hf
  refine orderOf_eq_orderOf_iff.2 fun k => ?_
  have hpow : V.map f * M.map f ^ k = G.map f ^ k * V.map f := (hinter.pow_right k).eq
  rw [← hφ.eq_iff, map_pow, map_one, ← hφ.eq_iff, map_pow, map_one, RingHom.mapMatrix_apply,
    RingHom.mapMatrix_apply]
  exact ⟨fun hMk => by
      rw [← Matrix.mul_one (G.map f ^ k), ← hVU, ← Matrix.mul_assoc, ← hpow, hMk, Matrix.mul_one,
        hVU],
    fun hGk => by
      rw [← Matrix.one_mul (M.map f ^ k), ← hUV, Matrix.mul_assoc, hpow, hGk, Matrix.one_mul, hUV]⟩

end Matrix

end
