/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.NumberField
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.RealPeriod
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.Regulator.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Tamagawa.Product

/-!
# The Birch–Swinnerton-Dyer quotient of an elliptic curve over `ℚ`

For an elliptic curve `E` over `ℚ` whose Shafarevich–Tate group `Ш(E/ℚ)` is finite, the
*arithmetic side* of the Birch–Swinnerton-Dyer conjecture is the real number

  `Ω(E) · Reg(E/ℚ) · #Ш(E/ℚ) · ∏_p c_p / #E(ℚ)_tors²`.

Its factors are, in order:

* `WeierstrassCurve.minimalRealPeriod E`, the real period `2 ∫_{D(x) > 0} dx / √D(x)` of a global
  minimal equation of `E`; every global minimal equation gives the same value;
* `WeierstrassCurve.Affine.regulator`, the absolute determinant of the Néron–Tate pairing on a basis
  of `E(ℚ)` modulo torsion, which is `1` in rank zero; it is defined since `E(ℚ)` is finitely
  generated (`WeierstrassCurve.Affine.moduleFinite_point_of_numberField`);
* the order of `WeierstrassCurve.sha E`, the classes in `H¹(G_ℚ, E(ℚˢ))` that vanish over `ℝ` and
  over every `ℚ_p`; its finiteness is conjectural and is taken as a hypothesis;
* `WeierstrassCurve.tamagawaProduct E`, the product of the local Tamagawa numbers `c_p` over the
  primes of `ℤ`, all but finitely many of which are `1`;
* the order of the torsion subgroup of `E(ℚ)`, finite by
  `WeierstrassCurve.Affine.finite_torsion`.

The real period is the only factor that depends on the Weierstrass equation rather than on the
curve; it is normalised by global minimality, which is why the quotient is pinned to `ℚ`, where
global minimal models exist and the units of `ℤ` are `±1`. The Birch–Swinnerton-Dyer conjecture
predicts that this quotient is the leading coefficient `L^{(r)}(E, 1) / r!` of the `L`-function
of `E` at `s = 1`, `r` being the rank of `E(ℚ)`.

## Main definitions

* `WeierstrassCurve.bsdQuotient E`: the Birch–Swinnerton-Dyer quotient of `E`, for `Ш(E/ℚ)` finite.

## Main results

* `WeierstrassCurve.bsdQuotient_def`: the quotient in terms of its five factors.
* `WeierstrassCurve.bsdQuotient_pos`: the quotient is positive.
* `WeierstrassCurve.IsGlobalMinimal.bsdQuotient_eq`: on a global minimal equation the period
  factor is the real period of the equation itself.

## References

* B. J. Birch and H. P. F. Swinnerton-Dyer, *Notes on elliptic curves. II*, J. Reine Angew. Math.
  218 (1965), 79–108.
* J. Tate, *On the conjectures of Birch and Swinnerton-Dyer and a geometric analog*, Séminaire
  Bourbaki 306 (1966).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix C, §16.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., Cambridge University Press,
  1997.
-/

public section

open WeierstrassCurve.Affine

namespace WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The Birch–Swinnerton-Dyer quotient** of an elliptic curve `E` over `ℚ` whose
Shafarevich–Tate group is finite:

  `Ω(E) · Reg(E/ℚ) · #Ш(E/ℚ) · ∏_p c_p / #E(ℚ)_tors²`,

with `Ω(E)` the real period of a global minimal equation, `Reg(E/ℚ)` the regulator of the
Néron–Tate pairing, `c_p` the local Tamagawa number at the prime `p` and `E(ℚ)_tors` the torsion
subgroup of the Mordell–Weil group. The order of `Ш(E/ℚ)` is counted with the finiteness
hypothesis, so the quotient has no value on a curve with infinite `Ш(E/ℚ)`
(`WeierstrassCurve.bsdQuotient_def` restates it with `Nat.card`). -/
noncomputable def bsdQuotient [Finite E.sha] : ℝ :=
  letI := Fintype.ofFinite E.sha
  E.minimalRealPeriod * E.toAffine.regulator * Fintype.card E.sha * E.tamagawaProduct (R := ℤ) /
    Nat.card (AddCommGroup.torsion E.toAffine.Point) ^ 2

/-- **The Birch–Swinnerton-Dyer quotient in terms of its factors**:
`Ω(E) · Reg(E/ℚ) · #Ш(E/ℚ) · ∏_p c_p / #E(ℚ)_tors²`. -/
theorem bsdQuotient_def [Finite E.sha] :
    E.bsdQuotient = E.minimalRealPeriod * E.toAffine.regulator * Nat.card E.sha *
      E.tamagawaProduct (R := ℤ) / Nat.card (AddCommGroup.torsion E.toAffine.Point) ^ 2 := by
  let := Fintype.ofFinite E.sha
  rw [bsdQuotient, Nat.card_eq_fintype_card (α := E.sha)]

/-- **The Birch–Swinnerton-Dyer quotient is positive**: each of its five factors is. -/
theorem bsdQuotient_pos [Finite E.sha] : 0 < E.bsdQuotient := by
  have := finite_torsion (W := E.toAffine)
  have := E.minimalRealPeriod_pos
  have := E.toAffine.regulator_pos
  have := E.tamagawaProduct_pos (R := ℤ)
  have : 0 < Nat.card E.sha := Nat.card_pos
  have : 0 < Nat.card (AddCommGroup.torsion E.toAffine.Point) := Nat.card_pos
  rw [bsdQuotient_def]
  positivity

/-- **The Birch–Swinnerton-Dyer quotient of a global minimal equation**: if `E` is itself globally
minimal over `ℤ`, the period factor is the real period of the equation `E` over `ℝ`. -/
theorem IsGlobalMinimal.bsdQuotient_eq {E : WeierstrassCurve ℚ} [E.IsElliptic] [Finite E.sha]
    (h : IsGlobalMinimal ℤ E) :
    E.bsdQuotient = (E.baseChange ℝ).realPeriod * E.toAffine.regulator * Nat.card E.sha *
      E.tamagawaProduct (R := ℤ) / Nat.card (AddCommGroup.torsion E.toAffine.Point) ^ 2 := by
  rw [bsdQuotient_def, h.minimalRealPeriod_eq]

end WeierstrassCurve
