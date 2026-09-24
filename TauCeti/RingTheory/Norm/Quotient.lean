/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Quotient

/-!
# The norm modulo the maximal ideal

Let `R` be a local ring with maximal ideal `𝔪` and `S` a finite free `R`-algebra. Reducing a
basis of `S` modulo `𝔪` gives a basis of `S ⧸ 𝔪S` over the residue field `R ⧸ 𝔪`
(`IsLocalRing.basisQuotient`), and the matrix of multiplication by the reduction of `x` is the
reduction of the matrix of multiplication by `x`. Taking determinants shows that the norm commutes
with reduction modulo `𝔪`. This is the norm counterpart of Mathlib's `Algebra.trace_quotient_mk`.

## Main results

* `TauCeti.Algebra.norm_quotient_mk`: the norm of `S ⧸ 𝔪S` over `R ⧸ 𝔪` of the class of `x` is
  the class of the norm of `x`.
-/

public section

open IsLocalRing

namespace TauCeti

variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

attribute [local instance] Ideal.Quotient.field

/-- **The norm commutes with reduction modulo the maximal ideal.** For a finite free algebra `S`
over a local ring `R`, the norm of `S ⧸ 𝔪S` over `R ⧸ 𝔪` of the class of `x` is the class of the
norm of `x`. -/
theorem Algebra.norm_quotient_mk (x : S) :
    Algebra.norm (R ⧸ maximalIdeal R)
        (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) x) =
      Ideal.Quotient.mk (maximalIdeal R) (Algebra.norm R x) := by
  let b := Module.Free.chooseBasis R S
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (basisQuotient b),
    RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.leftMulMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.toMatrix_apply,
    basisQuotient_apply, LinearMap.mul_apply', RingHom.mapMatrix_apply, Matrix.map_apply,
    ← map_mul, basisQuotient_repr]

end TauCeti
