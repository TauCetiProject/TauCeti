/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Hazewinkel.Integral
public import TauCeti.RingTheory.FormalGroup.PTypical.Basic

/-!
# `p`-typicality of Hazewinkel's formal group laws

This file connects the curve-theoretic notion of `p`-typical formal group laws
(`FormalGroup.IsPTypical`) and Cartier–Quillen `p`-typicalization (`FormalGroup.pTypicalize`) to
Hazewinkel's rational and integral formal group laws (`TauCeti.hazewinkelFormalGroup`,
`TauCeti.universalHazewinkelIntegralFormalGroup`, and `TauCeti.hazewinkelIntegralFormalGroup`).

Over a `ℚ`-algebra `K` and for a prime `p`, a commutative formal group law is `p`-typical if and
only if its formal logarithm has zero coefficients outside the degrees `p^n`, hence if and only if
it equals `TauCeti.hazewinkelFormalGroup p v` for a (unique) family `v : ℕ+ → K`. Over
`ℤ[v₁, v₂, …]`, injectivity of `ℤ[v₁, v₂, …] →+* ℚ[v₁, v₂, …]` implies that Hazewinkel's integral
polynomial law `TauCeti.universalHazewinkelIntegralFormalGroup p` is `p`-typical, and therefore its
specialization `TauCeti.hazewinkelIntegralFormalGroup p v` is `p`-typical over **every**
commutative ring `R`, including rings with torsion.

## Main results

* `TauCeti.isPTypical_hazewinkelFormalGroup`: over a `ℚ`-algebra and for `p` prime,
  `hazewinkelFormalGroup p v` is `p`-typical.
* `TauCeti.isPTypical_universalHazewinkelIntegralFormalGroup` and
  `TauCeti.isPTypical_hazewinkelIntegralFormalGroup`: Hazewinkel's integral formal group law is
  `p`-typical over `ℤ[v₁, v₂, …]` and over any commutative ring `R`.
* `FormalGroup.IsPTypical.existsUnique_eq_hazewinkelFormalGroup` and
  `FormalGroup.isPTypical_iff_exists_eq_hazewinkelFormalGroup`: rational classification of
  `p`-typical formal group laws by Hazewinkel families `v : ℕ+ → K`.
* `FormalGroup.existsUnique_pTypicalize_eq_hazewinkelFormalGroup` and
  `FormalGroup.hazewinkelLogCoeff_of_pTypicalize_eq`: over a `ℚ`-algebra, the `p`-typicalization of
  any commutative formal group law `F` is `hazewinkelFormalGroup p v` for a unique `v`, whose
  Hazewinkel logarithm coefficients satisfy `m_n(v) = [X^(p^n)] log_F(X)`.

## References

* M. Hazewinkel, *Constructing formal groups. I. The local one dimensional case*, J. Pure Appl.
  Algebra 9 (1977), 131–149.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter I, §2 and Chapter III,
  §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2.1.24–A2.1.27.
-/

public section

namespace TauCeti

section Rational

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- Over a `ℚ`-algebra and for a prime `p`, Hazewinkel's formal group law
`hazewinkelFormalGroup p v` is `p`-typical. -/
theorem isPTypical_hazewinkelFormalGroup {p : ℕ} (hp : p.Prime) (v : ℕ+ → K) :
    (hazewinkelFormalGroup p v).IsPTypical p := by
  rw [FormalGroup.isPTypical_iff_coeff_log_eq_zero _ hp, log_hazewinkelFormalGroup]
  intro k hk
  exact coeff_hazewinkelLog_eq_zero v hk

end Rational

section Integral

/-- Hazewinkel's universal integral formal group law over `ℤ[v₁, v₂, …]` is `p`-typical. -/
@[simp]
theorem isPTypical_universalHazewinkelIntegralFormalGroup (p : ℕ) [hp : Fact p.Prime] :
    (universalHazewinkelIntegralFormalGroup p).IsPTypical p := by
  rw [← FormalGroup.isPTypical_map_iff (MvPolynomial.map_injective (Int.castRingHom ℚ)
      Int.cast_injective),
    FormalGroup.isPTypical_congr (map_intCast_universalHazewinkelIntegralFormalGroup p) p]
  exact isPTypical_hazewinkelFormalGroup hp.out _

/-- Hazewinkel's integral formal group law specialized at any family `v : ℕ+ → R` is `p`-typical
over every commutative ring `R`, including rings with torsion. -/
@[simp]
theorem isPTypical_hazewinkelIntegralFormalGroup {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (v : ℕ+ → R) :
    (hazewinkelIntegralFormalGroup p v).IsPTypical p := by
  rw [FormalGroup.isPTypical_congr (hazewinkelIntegralFormalGroup_def p v) p]
  exact (isPTypical_universalHazewinkelIntegralFormalGroup p).map _

end Integral

end TauCeti

namespace FormalGroup

open TauCeti

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- Over a `ℚ`-algebra and for a prime `p`, every `p`-typical commutative formal group law is
`hazewinkelFormalGroup p v` for a unique family `v : ℕ+ → K`. -/
theorem IsPTypical.existsUnique_eq_hazewinkelFormalGroup {F : FormalGroup K} [F.IsComm] {p : ℕ}
    (hp : p.Prime) (hF : F.IsPTypical p) :
    ∃! v : ℕ+ → K, F = hazewinkelFormalGroup p v :=
  TauCeti.existsUnique_eq_hazewinkelFormalGroup hp.one_lt fun _ hk ↦ hF.coeff_log_eq_zero hk

/-- Over a `ℚ`-algebra and for a prime `p`, a commutative formal group law is `p`-typical if and
only if it is `hazewinkelFormalGroup p v` for some family `v : ℕ+ → K`. -/
theorem isPTypical_iff_exists_eq_hazewinkelFormalGroup (F : FormalGroup K) [F.IsComm] {p : ℕ}
    (hp : p.Prime) :
    F.IsPTypical p ↔ ∃ v : ℕ+ → K, F = hazewinkelFormalGroup p v :=
  ⟨fun hF ↦ (hF.existsUnique_eq_hazewinkelFormalGroup hp).exists,
   fun ⟨v, hv⟩ ↦ (isPTypical_congr hv p).mpr (isPTypical_hazewinkelFormalGroup hp v)⟩

/-- Over a `ℚ`-algebra and for a prime `p`, the `p`-typicalization of any commutative formal group
law `F` is `hazewinkelFormalGroup p v` for a unique family `v : ℕ+ → K`. -/
theorem existsUnique_pTypicalize_eq_hazewinkelFormalGroup (F : FormalGroup K) [F.IsComm] {p : ℕ}
    (hp : p.Prime) (hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : K)) :
    ∃! v : ℕ+ → K, F.pTypicalize p hunit = hazewinkelFormalGroup p v :=
  (F.isPTypical_pTypicalize p hunit).existsUnique_eq_hazewinkelFormalGroup hp

/-- If the `p`-typicalization of `F` over a `ℚ`-algebra equals `hazewinkelFormalGroup p v`, then
the `n`-th Hazewinkel logarithm coefficient `m_n(v)` equals the `X^(p^n)` coefficient of `log_F`. -/
theorem hazewinkelLogCoeff_of_pTypicalize_eq {F : FormalGroup K} [F.IsComm] {p : ℕ}
    (hp : p.Prime) {hunit : ∀ ⦃q : ℕ⦄, q.Prime → q ≠ p → IsUnit (q : K)} {v : ℕ+ → K}
    (hv : F.pTypicalize p hunit = hazewinkelFormalGroup p v) (n : ℕ) :
    hazewinkelLogCoeff p v n = PowerSeries.coeff (p ^ n) F.log := by
  rw [← coeff_hazewinkelLog_pow v hp.one_lt n, ← log_hazewinkelFormalGroup, ← hv,
    F.coeff_log_pTypicalize_pow hp hunit n]

end FormalGroup
