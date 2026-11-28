/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import TauCeti.RingTheory.Polynomial.Resultant.BinaryForm
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Coprimality
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Resultant
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultants of homogeneous division polynomials

The `x`-coordinate of multiplication on a nonsingular Weierstrass curve gives the Lattès
map on the projective line. See [J. Milnor, *On Lattès maps*](https://arxiv.org/abs/math/0402147v2),
§2.

* `WeierstrassCurve.isUnit_binaryResultant_Φ_ΨSq` shows that the degree-`n.natAbs ^ 2`
  homogenizations have unit resultant if the discriminant is a unit. It uses
  `WeierstrassCurve.isCoprime_Φ_ΨSq` and `Polynomial.Monic.resultant_of_le` over residue fields.
* `WeierstrassCurve.binaryResultant_Φ_two_ΨSq_two` computes the binary resultant of the
  doubling lift using `WeierstrassCurve.resultant_Φ_two_ΨSq_two` and
  `Polynomial.binaryResultant_homogenize`. This formula also holds on singular models.
-/

public section

namespace WeierstrassCurve

open Polynomial

/-- If the discriminant is a unit, the degree-`n.natAbs ^ 2` homogenizations of `Φ n` and
`ΨSq n` have unit binary resultant. This certifies that the multiplication Lattès lift for
`n ≠ 0` has no common projective zero after base change to any field. -/
theorem isUnit_binaryResultant_Φ_ΨSq {R : Type*} [CommRing R] (W : WeierstrassCurve R)
    (n : ℤ) (hΔ : IsUnit W.Δ) :
    IsUnit (MvPolynomial.binaryResultant ((W.Φ n).homogenize (n.natAbs ^ 2))
      ((W.ΨSq n).homogenize (n.natAbs ^ 2)) (n.natAbs ^ 2) (n.natAbs ^ 2)) := by
  rw [binaryResultant_homogenize]
  -- A nonunit resultant would vanish over some residue field.
  by_contra hres
  rw [← Ideal.span_singleton_eq_top] at hres
  obtain ⟨m, hm, hle⟩ := Ideal.ne_top_iff_exists_maximal.mp hres
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let φ := Ideal.Quotient.mk m
  have hzero : φ ((W.Φ n).resultant (W.ΨSq n) (n.natAbs ^ 2) (n.natAbs ^ 2)) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.subset_span (Set.mem_singleton _)))
  have hΔm : (W.map φ).Δ ≠ 0 := by
    rw [map_Δ]
    exact (hΔ.map φ).ne_zero
  have hcop := (W.map φ).isCoprime_Φ_ΨSq n hΔm
  have hmonic : ((W.map φ).Φ n).Monic := Monic.def.mpr ((W.map φ).leadingCoeff_Φ n)
  have hdeg : ((W.map φ).ΨSq n).natDegree ≤ n.natAbs ^ 2 :=
    ((W.map φ).natDegree_ΨSq_le n).trans (Nat.sub_le _ _)
  have hzero' : ((W.map φ).Φ n).resultant ((W.map φ).ΨSq n) = 0 := by
    rw [← hmonic.resultant_of_le hdeg, natDegree_Φ, map_Φ, map_ΨSq, resultant_map_map]
    exact hzero
  exact (resultant_ne_zero _ _ hcop) hzero'

/-- The binary resultant of the degree-four homogenizations for Weierstrass doubling is
`Δ ^ 2` over any commutative ring, including in characteristic two. -/
theorem binaryResultant_Φ_two_ΨSq_two {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    MvPolynomial.binaryResultant ((W.Φ 2).homogenize 4) ((W.ΨSq 2).homogenize 4) 4 4 =
      W.Δ ^ 2 := by
  rw [binaryResultant_homogenize, W.resultant_Φ_two_ΨSq_two]

end WeierstrassCurve
