/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.InfiniteOrder
public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.FinitelyGenerated
-- Proof-only: integral models over a tower, points carried along `ZMod p → k`, and membership
-- in the maximal ideal of the valuation ring at a prime.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# Worked example: the curve 37.a1 has positive rank

The elliptic curve with LMFDB label 37.a1 (Cremona label 37a1) is `y² + y = x³ - x`, the integral
Weierstrass model `[0, 0, 1, -1, 0]`, of discriminant `37`. This file shows that its rational
point `P = (0, 0)` has infinite order, so the Mordell–Weil group `E(ℚ)` has positive rank.

The certificate is reduction at the two primes `2` and `3`, where the curve has good reduction.
Modulo `2` the reduction of `P` is killed by `5`, and modulo `3` it is killed by `7`; both are
computations in the finite groups `E(𝔽₂)` and `E(𝔽₃)`. A prime dividing the order of `P`, if `P`
were torsion, would divide both `2 * 5` and `3 * 7`
(`WeierstrassCurve.Affine.Point.not_isOfFinAddOrder_of_coprime`), which are coprime. Reduction is
used only through its injectivity on torsion prime to the residue characteristic.

The two finite computations are made over `ZMod 2` and `ZMod 3` by evaluating the group law in
the kernel: Mathlib's point addition is not computable, since its `AddCommGroup` structure goes
through `Classical.choice`, but `n • P` reduces in the kernel for a concrete curve. The residue
field of `ℚ` at `p` contains `ZMod p`, and the reduction of `P` is the image of the point `(0, 0)`
over `ZMod p`.

## Main results

* `TauCeti.WorkedExamples.not_isOfFinAddOrder_curve37a1Point`: `P = (0, 0)` has infinite order.
* `TauCeti.WorkedExamples.finrank_point_curve37a1_pos`: the rank of `E(ℚ)` is positive.

## Provenance

The method follows Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, commit `3bfe124`),
`EllipticCurves/InfiniteOrderExample.lean`, which certifies that `(1, 1)` on `y² = x³ - x + 1` has
infinite order by reduction modulo `3` and `5`, with the finite computations made by
`decide +kernel` over `ZMod p`. The curve, the primes and the transport to the residue field are
different here.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.3.1 and VIII.7.
* J. E. Cremona, *Algorithms for Modular Elliptic Curves*, 2nd ed., the tables, curve 37A1.
* The L-functions and modular forms database, elliptic curve 37.a1.
-/

public section

open WeierstrassCurve Affine IsDedekindDomain IsLocalRing

namespace TauCeti.WorkedExamples

/-- The curve 37.a1, `y² + y = x³ - x`, as an integral Weierstrass model. -/
abbrev curve37a1 : WeierstrassCurve ℤ := ⟨0, 0, 1, -1, 0⟩

/-- The discriminant of `y² + y = x³ - x` is `37`. -/
theorem Δ_curve37a1 : curve37a1.Δ = 37 := by
  simp [Δ, b₂, b₄, b₆, b₈]

/-- 37.a1 is an elliptic curve over `ℚ`. -/
instance : (curve37a1.baseChange ℚ).IsElliptic := by
  rw [isElliptic_iff, WeierstrassCurve.baseChange, map_Δ, Δ_curve37a1]
  norm_num

/-- The rational points of 37.a1 are the solutions of `y² + y = x³ - x`. -/
theorem equation_curve37a1_iff (x y : ℚ) :
    (curve37a1.baseChange ℚ).toAffine.Equation x y ↔ y ^ 2 + y = x ^ 3 - x := by
  rw [equation_iff]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_zero,
    map_one, map_neg]
  constructor <;> intro h <;> linear_combination h

/-- Every rational solution of `y² + y = x³ - x` is a nonsingular point of 37.a1. -/
theorem nonsingular_curve37a1 {x y : ℚ} (h : y ^ 2 + y = x ^ 3 - x) :
    (curve37a1.baseChange ℚ).toAffine.Nonsingular x y :=
  equation_iff_nonsingular.1 ((equation_curve37a1_iff x y).2 h)

/-- The rational point `(0, 0)` of 37.a1. -/
def curve37a1Point : (curve37a1.baseChange ℚ).toAffine.Point :=
  .some 0 0 (nonsingular_curve37a1 (by norm_num))

/-- `curve37a1Point` is the point `(0, 0)`. -/
@[simp]
theorem curve37a1Point_def :
    curve37a1Point = .some 0 0 (nonsingular_curve37a1 (by norm_num)) := (rfl)

/-! ### Reduction at a prime of `ℤ` -/

section Reduction

variable (v : HeightOneSpectrum ℤ)

/-- 37.a1 has coefficients in the valuation ring of `ℚ` at every prime. -/
instance : IsIntegral (v.valuation ℚ).valuationSubring (curve37a1.baseChange ℚ) :=
  have : IsIntegral ℤ (curve37a1.baseChange ℚ) := ⟨⟨curve37a1, rfl⟩⟩
  .of_isScalarTower (R := ℤ) _

private theorem integralModel_curve37a1 :
    integralModel (v.valuation ℚ).valuationSubring (curve37a1.baseChange ℚ) =
      curve37a1.map (algebraMap ℤ (v.valuation ℚ).valuationSubring) :=
  integralModel_eq_of_baseChange_eq (by
    rw [WeierstrassCurve.baseChange, map_map, ← IsScalarTower.algebraMap_eq,
      WeierstrassCurve.baseChange])

/-- 37.a1 has good reduction at every prime other than `37`. -/
private theorem isElliptic_integralModel_curve37a1 (h37 : (37 : ℤ) ∉ v.asIdeal) :
    (integralModel (v.valuation ℚ).valuationSubring (curve37a1.baseChange ℚ)).IsElliptic := by
  rwa [integralModel_curve37a1, isElliptic_iff, map_Δ, Δ_curve37a1, ← notMem_maximalIdeal,
    ← map_ofNat (algebraMap ℤ _), v.algebraMap_mem_maximalIdeal_valuationSubring_iff]

/-- A point `(x, y)` with `x = y = 0` on a curve equal to the image of 37.a1 over `ZMod p` is the
image of the point `(0, 0)` over `ZMod p`, so it is killed by whatever kills that point. -/
private theorem nsmul_some_eq_zero {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [DecidableEq k]
    [CharP k p] {V : WeierstrassCurve k}
    (hV : V = (curve37a1.map (Int.castRingHom (ZMod p))).map (ZMod.castHom dvd_rfl k))
    {x y : k} (hx : x = 0) (hy : y = 0) (h : V.toAffine.Nonsingular x y)
    (h₀ : (curve37a1.map (Int.castRingHom (ZMod p))).toAffine.Nonsingular 0 0) {m : ℕ}
    (hm : m • (Point.some 0 0 h₀) = 0) : m • (Point.some x y h : V.toAffine.Point) = 0 := by
  subst hV hx hy
  have := congrArg (Point.mapAlong (ZMod.castHom dvd_rfl k) (RingHom.injective _)) hm
  rw [← natCast_zsmul, Point.mapAlong_zsmul, natCast_zsmul, Point.mapAlong_some,
    Point.mapAlong_zero] at this
  simpa using this

/-- At a prime of good reduction containing `p`, the reduction of `(0, 0)` is killed by whatever
kills the point `(0, 0)` of the reduced curve over `ZMod p`. -/
private theorem nsmul_reductionHom_curve37a1Point {p : ℕ} [Fact p.Prime]
    (hp : (p : ℤ) ∈ v.asIdeal)
    [(integralModel (v.valuation ℚ).valuationSubring (curve37a1.baseChange ℚ)).IsElliptic]
    [DecidableEq (ResidueField (v.valuation ℚ).valuationSubring)]
    (h₀ : (curve37a1.map (Int.castRingHom (ZMod p))).toAffine.Nonsingular 0 0) {m : ℕ}
    (hm : m • (Point.some 0 0 h₀) = 0) :
    m • Point.reductionHom (v.valuation ℚ) curve37a1Point = 0 := by
  -- the residue field has characteristic `p`, since `p ∈ v`
  have : CharP (ResidueField (v.valuation ℚ).valuationSubring) p := by
    refine (CharP.charP_iff_prime_eq_zero Fact.out).mpr ?_
    rwa [← map_natCast (residue (v.valuation ℚ).valuationSubring), residue_eq_zero_iff,
      ← map_natCast (algebraMap ℤ _), v.algebraMap_mem_maximalIdeal_valuationSubring_iff]
  have hV : (integralModel (v.valuation ℚ).valuationSubring (curve37a1.baseChange ℚ)).map
      (residue (v.valuation ℚ).valuationSubring) =
        (curve37a1.map (Int.castRingHom (ZMod p))).map (ZMod.castHom dvd_rfl _) := by
    rw [integralModel_curve37a1, map_map, map_map]
    congr 1
    exact RingHom.ext_int _ _
  have hval : v.valuation ℚ 0 ≤ 1 := by simp
  have h0 : residue (v.valuation ℚ).valuationSubring
      ⟨0, (Valuation.mem_valuationSubring_iff _ _).mpr hval⟩ = 0 :=
    map_zero _
  rw [curve37a1Point_def, Point.reductionHom_some_of_valuation_le_one _ _ hval]
  · exact nsmul_some_eq_zero hV h0 h0 _ h₀ hm
  · rw [hV, h0]
    simpa only [map_zero] using (map_nonsingular _
      (ZMod.castHom dvd_rfl (ResidueField (v.valuation ℚ).valuationSubring)).injective 0 0).mpr h₀

end Reduction

/-! ### The certificate at `2` and `3` -/

/-- `(0, 0)` is a point of 37.a1 over `𝔽₂`. -/
private theorem nonsingular_curve37a1_zmod_two :
    (curve37a1.map (Int.castRingHom (ZMod 2))).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  decide

/-- `(0, 0)` is a point of 37.a1 over `𝔽₃`. -/
private theorem nonsingular_curve37a1_zmod_three :
    (curve37a1.map (Int.castRingHom (ZMod 3))).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff, equation_iff]
  decide

/-- Over `𝔽₂`, `5 • (0, 0) = 0` on 37.a1: the multiples are `(0, 0)`, `(1, 0)`, `(1, 1)`,
`(0, 1)`. The group law is evaluated in the kernel. -/
private theorem five_nsmul_curve37a1_zmod_two :
    5 • (Point.some 0 0 nonsingular_curve37a1_zmod_two) = 0 := by
  decide +kernel

/-- Over `𝔽₃`, `7 • (0, 0) = 0` on 37.a1: the multiples are `(0, 0)`, `(1, 0)`, `(2, 2)`,
`(2, 0)`, `(1, 2)`, `(0, 2)`. The group law is evaluated in the kernel. -/
private theorem seven_nsmul_curve37a1_zmod_three :
    7 • (Point.some 0 0 nonsingular_curve37a1_zmod_three) = 0 := by
  decide +kernel

/-- **The point `(0, 0)` of 37.a1 has infinite order.** Its reductions modulo `2` and `3` are
killed by `5` and `7`, and `2 * 5` and `3 * 7` are coprime. -/
theorem not_isOfFinAddOrder_curve37a1Point : ¬IsOfFinAddOrder curve37a1Point := by
  classical
  -- the primes `(2)` and `(3)` of `ℤ`
  have hex {p : ℕ} (hp : p.Prime) : ∃ v : HeightOneSpectrum ℤ, (p : ℤ) ∈ v.asIdeal :=
    ⟨⟨Ideal.span {(p : ℤ)}, (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp), by simpa using hp.ne_zero⟩,
      Ideal.mem_span_singleton_self _⟩
  obtain ⟨v, hv⟩ := hex Nat.prime_two
  obtain ⟨w, hw⟩ := hex Nat.prime_three
  -- `37` is coprime to `2` and to `3`, so it lies in neither prime
  have h37 {p : ℕ} {u : HeightOneSpectrum ℤ} (hu : (p : ℤ) ∈ u.asIdeal) (hp : p.Coprime 37) :
      (37 : ℤ) ∉ u.asIdeal := by
    exact_mod_cast Ideal.IsPrime.notMem_of_isCoprime_of_mem (hp.cast (R := ℤ)) hu
  have := isElliptic_integralModel_curve37a1 v (h37 hv (by norm_num))
  have := isElliptic_integralModel_curve37a1 w (h37 hw (by norm_num))
  exact Point.not_isOfFinAddOrder_of_coprime v w (Point.some_ne_zero _) hv hw (by norm_num)
    (nsmul_reductionHom_curve37a1Point v hv _ five_nsmul_curve37a1_zmod_two)
    (nsmul_reductionHom_curve37a1Point w hw _ seven_nsmul_curve37a1_zmod_three)

/-- **37.a1 has positive rank**: its Mordell–Weil group `E(ℚ)`, finitely generated by the
Mordell–Weil theorem, contains the point `(0, 0)` of infinite order. -/
theorem finrank_point_curve37a1_pos :
    0 < Module.finrank ℤ (curve37a1.baseChange ℚ).toAffine.Point := by
  have : Module.Finite ℤ (curve37a1.baseChange ℚ).toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr fg_point_of_numberField
  refine Nat.pos_of_ne_zero fun h ↦ not_isOfFinAddOrder_curve37a1Point ?_
  obtain ⟨a, ha, hP⟩ := Module.finrank_eq_zero_iff.mp h curve37a1Point
  exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨a, ha, hP⟩

end TauCeti.WorkedExamples

end
