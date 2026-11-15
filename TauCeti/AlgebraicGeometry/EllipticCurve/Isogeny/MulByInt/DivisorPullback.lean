/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Sum
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Place
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.DivisorPullback
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.PointPlace
public import TauCeti.FieldTheory.FunctionField.Divisor.Automorphism
-- Proof-only: `[n]` is separable, hence unramified, when `n` is invertible.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
-- Proof-only: `#E[n] = n ²` and `[n]` onto `E[n]`, over a separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
-- Proof-only: every point is divisible by `n`, over a separably closed field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective

/-!
# The pullback of a point along `[n]`

Let `W` be an elliptic curve over a field `F` and `n` an integer invertible in `F`. The
coefficient of `[n]^* D` at the place of a point `R` is the coefficient of `D` at the place of
`n • R`. Over a separably closed field, pulling the divisor `(T)` of a point back along
multiplication by `n` gives the points `R` with `n • R = T`, each with multiplicity one.

At an `n`-torsion point `T`, the divisor `[n]^* (T) - [n]^* (O)` is principal. This is the second
input to the divisor construction of the Weil pairing (Silverman III.8.1), after
`WeierstrassCurve.Affine.exists_principal_eq_zsmul_ofPoint_sub_infinity`: the pairing is built
from a function with this divisor.

## Main definitions

* `TauCeti.Isogeny.weilPairingDivisor`: the divisor `[n]^* (T) - [n]^* (O)`.

## Main results

* `TauCeti.Isogeny.coeff_divisorPullback_mulByIntIsogeny`: the coefficient of `[n]^* D` at the
  place of `R` is the coefficient of `D` at the place of `n • R`.
* `TauCeti.Isogeny.divisorPullback_mulByIntIsogeny_ofPoint`: over a separably closed field,
  `[n]^* (T) = ∑_{n • R = T} (R)`.
* `TauCeti.Isogeny.weilPairingDivisor_eq_sum`: with `n • R₀ = T`, the divisor
  `[n]^* (T) - [n]^* (O)` is `∑_{n • S = O} ((R₀ + S) - (S))`.
* `TauCeti.Isogeny.translation_smul_weilPairingDivisor`: the translate by `X` of
  `[n]^* (T) - [n]^* (O)` is `([n]^* (T - n X) - [n]^* (O)) - ([n]^* (-n X) - [n]^* (O))`.
* `TauCeti.Isogeny.exists_principal_eq_weilPairingDivisor_sub`: at any point `T`,
  `[n]^* (T) - [n]^* (O) - ((n T) - (O))` is the divisor of a function.
* `TauCeti.Isogeny.exists_principal_eq_weilPairingDivisor`: at an `n`-torsion
  point `T`, `[n]^* (T) - [n]^* (O)` is the divisor of a function.

The place-level inputs are in `Isogeny/MulByInt/PointPlace.lean`
(`isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff`, `finite_setOf_zsmul_eq`,
`restrict_eq_pointEquivDegreeOnePlace_iff`), and the torsion counts on the points of `W` in
`Isogeny/MulByInt/IsSepClosed.lean`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10, III.8.1.

## Prior art

AINTLIB (`github.com/CBirkbeck/AINTLIB` @ `f622f4aa0bd7b9d8b8cb931b5f8cb709f1d179e2`, Apache-2.0)
proves both results in its own divisor framework, in
`projects/HasseWeil/HasseWeil/HasseBound/WeilPairing/`: `Pullback.lean` defines the fibre divisor
`pullbackDiv` combinatorially, `DivisorPullback.lean`'s
`projectiveDivisorOf_pullback_eq_pullbackDivisor` identifies it with the divisor of `k ∘ φ` by
per-place order transport over an algebraically closed field, and `WeilFunction.lean`'s
`pullbackDiv_sub_isPrincipal` (used by `Pairing.lean`'s `weilFunction_isPrincipal`) proves the
fibre difference principal. Nothing is ported: here the pullback is the conorm
`TauCeti.Isogeny.divisorPullback`, read off places.
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The coefficient of `[n]^* D` at the place of `R` is the coefficient of `D` at the place of
`n • R`**, for `n` invertible in `F`: the place of `R` lies over that of `n • R`, and `[n]` is
unramified, being separable. -/
@[simp]
theorem coeff_divisorPullback_mulByIntIsogeny {n : ℤ} (hchar : (n : F) ≠ 0)
    (D : Divisor F W.toAffine.FunctionField) (R : W.toAffine.Point) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    ((mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).divisorPullback (fun _ ↦ rfl) D).coeff
        (pointEquivDegreeOnePlace W.toAffine R).1 =
      D.coeff (pointEquivDegreeOnePlace W.toAffine (n • R)).1 := by
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
  have := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
    (fun _ ↦ rfl)
  have := (isSeparable_mulByIntIsogeny_iff W (psiFunctionField_ne_zero W hchar)).2 hchar
  rw [coeff_divisorPullback, ramificationIdx_eq_one _ (fun _ ↦ rfl), Nat.cast_one, one_mul,
    (Place.restrict_eq_iff_isEquiv_comap F W.toAffine.FunctionField _ _).mpr
      ((isEquiv_comap_valuation_pointEquivDegreeOnePlace_iff W _ R (n • R)).mpr rfl)]

/-- **The divisor `[n]^* (T) - [n]^* (O)`**, the pullback along `[n]` of `(T) - (O)`. The Weil
pairing is built from a function with this divisor (Silverman III.8.1). -/
noncomputable def weilPairingDivisor {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (T : W.toAffine.Point) :
    Divisor F W.toAffine.FunctionField :=
  letI := (mulByIntIsogeny W (hn)).fieldPullback.toAlgebra
  (mulByIntIsogeny W (hn)).divisorPullback (fun _ ↦ rfl)
      (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1) -
    (mulByIntIsogeny W (hn)).divisorPullback (fun _ ↦ rfl)
      (WeilDivisor.ofPoint (Place.infinity W.toAffine))

omit [DecidableEq F] in
/-- The defining equation of `weilPairingDivisor`. -/
-- A lemma rather than left to unfolding: the body is not exposed across a module boundary.
theorem weilPairingDivisor_def {n : ℤ} (hn : psiFunctionField W n ≠ 0) (T : W.toAffine.Point) :
    letI := (mulByIntIsogeny W (hn)).fieldPullback.toAlgebra
    weilPairingDivisor W hn T =
      (mulByIntIsogeny W (hn)).divisorPullback (fun _ ↦ rfl)
          (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1) -
        (mulByIntIsogeny W (hn)).divisorPullback (fun _ ↦ rfl)
          (WeilDivisor.ofPoint (Place.infinity W.toAffine)) :=
  (rfl)

omit [DecidableEq F] in
/-- **The divisor `[n]^* (O) - [n]^* (O)` is zero.** -/
@[simp]
theorem weilPairingDivisor_zero {n : ℤ} (hn : psiFunctionField W n ≠ 0) :
    weilPairingDivisor W hn 0 = 0 := by
  rw [weilPairingDivisor_def, Point.zero_def, coe_pointEquivDegreeOnePlace_zero, sub_self]

section SepClosed

variable [IsSepClosed F]

/-- **The pullback of a point along `[n]` is its fibre**: over a separably closed field in which
`n` is invertible, `[n]^* (T) = ∑_{n • R = T} (R)`. -/
@[simp]
theorem divisorPullback_mulByIntIsogeny_ofPoint {n : ℤ} (hchar : (n : F) ≠ 0)
    (T : W.toAffine.Point) :
    letI := (mulByIntIsogeny W
      (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).divisorPullback (fun _ ↦ rfl)
        (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine T).1) =
      ∑ R ∈ (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T).toFinset,
        WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine R).1 := by
  classical
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_fieldPullback
    (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)) (fun _ ↦ rfl)
  have := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).finiteDimensional_functionField
    (fun _ ↦ rfl)
  have := (isSeparable_mulByIntIsogeny_iff W (psiFunctionField_ne_zero W hchar)).2 hchar
  -- the fibre sum is the finite-set divisor of the places of the fibre
  have hsum : ∑ R ∈ (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T).toFinset,
        WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine R).1 =
      WeilDivisor.ofFinset ((finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar)
        T).toFinset.map ⟨fun R ↦ (pointEquivDegreeOnePlace W.toAffine R).1,
          Subtype.val_injective.comp (pointEquivDegreeOnePlace W.toAffine).injective⟩) := by
    rw [WeilDivisor.ofFinset_eq_sum, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [hsum]
  ext P
  rw [coeff_divisorPullback, ramificationIdx_eq_one _ (fun _ ↦ rfl), Nat.cast_one, one_mul,
    WeilDivisor.coeff_ofFinset]
  -- the pullback has coefficient `1` at the places over the place of `T`, and `0` elsewhere
  have hfin := finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T
  split_ifs with hmem
  · obtain ⟨R, hR, hRP⟩ := Finset.mem_map.mp hmem
    rw [(restrict_eq_pointEquivDegreeOnePlace_iff W hchar T P).mpr
      ⟨R, (Set.Finite.mem_toFinset hfin).mp hR, hRP⟩, WeilDivisor.coeff_ofPoint_self]
  · refine WeilDivisor.coeff_ofPoint_of_ne fun hP ↦ hmem ?_
    obtain ⟨R, hR, rfl⟩ := (restrict_eq_pointEquivDegreeOnePlace_iff W hchar T P).mp hP
    exact Finset.mem_map_of_mem _
      ((Set.Finite.mem_toFinset hfin).mpr (by simpa only [Set.mem_ofPred_eq] using hR))

/-! ### The divisor `[n]^* (T) - [n]^* (O)` -/

/-- **`[n]^* (T) - [n]^* (O)` is the translate of the fibre over `O` minus that fibre**: for any
`R₀` with `n • R₀ = T`, it is `∑_{n • S = O} ((R₀ + S) - (S))`, over a separably closed field in
which `n` is invertible. -/
theorem weilPairingDivisor_eq_sum {n : ℤ} (hchar : (n : F) ≠ 0) {T R₀ : W.toAffine.Point}
    (hR₀ : n • R₀ = T) :
    weilPairingDivisor W (psiFunctionField_ne_zero W hchar) T =
      ∑ S ∈ (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) 0).toFinset,
        (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine (R₀ + S)).1 -
          WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine S).1) := by
  rw [weilPairingDivisor_def]
  let _ := (mulByIntIsogeny W (psiFunctionField_ne_zero W hchar)).fieldPullback.toRingHom.toAlgebra
  rw [← coe_pointEquivDegreeOnePlace_zero, divisorPullback_mulByIntIsogeny_ofPoint W hchar T,
    divisorPullback_mulByIntIsogeny_ofPoint W hchar .zero]
  set s₀ := (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) 0).toFinset with hs₀
  -- the fibre over `T` is the translate by `R₀` of the fibre over `O`
  have hfib : (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) T).toFinset =
      s₀.map ⟨(R₀ + ·), add_right_injective R₀⟩ := by
    ext R
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_map,
      Function.Embedding.coeFn_mk, hs₀]
    refine ⟨fun hR ↦ ⟨R - R₀, by rw [smul_sub, hR, hR₀, sub_self], add_sub_cancel _ _⟩, ?_⟩
    rintro ⟨S, hS, rfl⟩
    rw [smul_add, hR₀, hS, add_zero]
  rw [hfib, Finset.sum_map, ← Finset.sum_sub_distrib]
  simp only [Function.Embedding.coeFn_mk]

/-- **The translate of `[n]^* (T) - [n]^* (O)`**: translation by `X` carries it to
`([n]^* (T - n X) - [n]^* (O)) - ([n]^* (-n X) - [n]^* (O))`, over a separably closed field in
which `n` is invertible. -/
theorem translation_smul_weilPairingDivisor {n : ℤ} (hchar : (n : F) ≠ 0)
    (X T : W.toAffine.Point) :
    Affine.translation W.toAffine (Affine.Point.equivBaseChangeSelf _ X) •
        weilPairingDivisor W (psiFunctionField_ne_zero W hchar) T =
      weilPairingDivisor W (psiFunctionField_ne_zero W hchar) (T - n • X) -
        weilPairingDivisor W (psiFunctionField_ne_zero W hchar) (-(n • X)) := by
  obtain ⟨R, hR⟩ := W.toAffine.zsmul_surjective hchar T
  replace hR : n • R = T := hR
  have h₁ : n • (R - X) = T - n • X := by rw [smul_sub, hR]
  have h₂ : n • -X = -(n • X) := smul_neg n X
  rw [weilPairingDivisor_eq_sum W hchar hR, weilPairingDivisor_eq_sum W hchar h₁,
    weilPairingDivisor_eq_sum W hchar h₂, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun S _ ↦ ?_
  simp only [smul_sub, WeilDivisor.smul_ofPoint, translation_smul_pointEquivDegreeOnePlace]
  abel_nf

/-- **`[n]^* (T) - [n]^* (O) - ((n T) - (O))` is principal** at every point `T`, over a separably
closed field in which `n` is invertible: with `n • R₀ = T`, its sum is `#E[n] • R₀ - n • T =
n • (n • R₀) - n • T = O`. -/
theorem exists_principal_eq_weilPairingDivisor_sub {n : ℤ} (hchar : (n : F) ≠ 0)
    (T : W.toAffine.Point) :
    ∃ z : W.toAffine.FunctionFieldˣ, Divisor.principal W.toAffine.isFunctionField z =
      weilPairingDivisor W (psiFunctionField_ne_zero W hchar) T -
        (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine (n • T)).1 -
          WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine 0).1) := by
  -- with `n • R₀ = T` the divisor is `∑_{n • S = O} ((R₀ + S) - (S))` minus `(n • T) - (O)`
  obtain ⟨R₀, hR₀⟩ := W.toAffine.zsmul_surjective hchar T
  replace hR₀ : n • R₀ = T := hR₀
  rw [weilPairingDivisor_eq_sum W hchar hR₀]
  set s₀ := (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) 0).toFinset with hs₀
  let D : (Divisor.degree (k := F) (F := W.toAffine.FunctionField)).ker :=
    ∑ S ∈ s₀, ⟨_, W.toAffine.ofPoint_sub_ofPoint_mem_ker_degree (R₀ + S) S⟩ -
      ⟨_, W.toAffine.ofPoint_sub_ofPoint_mem_ker_degree (n • T) 0⟩
  have hσ : W.toAffine.divisorSum D = 0 := by
    simp only [D, map_sub, map_sum, divisorSum_ofPoint_sub_ofPoint, add_sub_cancel_right,
      Finset.sum_const, sub_zero]
    rw [hs₀, ← Nat.card_eq_card_finite_toFinset, W.toAffine.natCard_setOf_zsmul_eq_zero hchar,
      ← natCast_zsmul, Nat.cast_pow, Int.natAbs_sq, sq, mul_smul, hR₀, sub_self]
  obtain ⟨z, hz⟩ := W.toAffine.divisorSum_eq_zero_iff.mp hσ
  exact ⟨z, hz.trans (by simp [D])⟩

/-- **`[n]^* (T) - [n]^* (O)` is principal** at an `n`-torsion point `T`, over a separably closed
field in which `n` is invertible (Silverman III.8.1). A function with this divisor is the
function `g_T` from which the Weil pairing is built. -/
theorem exists_principal_eq_weilPairingDivisor {n : ℤ} (hchar : (n : F) ≠ 0)
    {T : W.toAffine.Point} (hT : n • T = 0) :
    ∃ z : W.toAffine.FunctionFieldˣ, Divisor.principal W.toAffine.isFunctionField z =
      weilPairingDivisor W (psiFunctionField_ne_zero W hchar) T := by
  simpa only [hT, sub_self, sub_zero] using exists_principal_eq_weilPairingDivisor_sub W hchar T

end SepClosed

end TauCeti.Isogeny

end
