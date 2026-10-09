/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
-- Proof-only: a principal divisor supported on rational points is carried along `f`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Map.Place
-- Proof-only: `f` intertwines translation by `P` with translation by `f P`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Map
-- Proof-only: `E[N](F) → E[N](K)` is bijective over separably closed fields.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed

/-!
# The Weil pairing under change of field

Let `W` be an elliptic curve over a field `F`, let `f : F →+* K` be a homomorphism of fields, and
let `N` be invertible in `F`. A point `P` of `W` is carried to the point `f P` of `W.map f`, and
this restricts to a homomorphism `E[N](F) → E[N](K)` (`WeierstrassCurve.torsionMapAlong`). When
`F` and `K` are separably closed both groups have `N²` elements, so it is an isomorphism
(`WeierstrassCurve.torsionMapAlong_bijective`). This file proves that the Weil pairing is
functorial under change of field (Silverman III.8.1):

    e_N(f S, f T) = f (e_N(S, T)).

The proof follows the definition of the pairing. Let `g` be a function on `W` with divisor
`[N]^* (T) - [N]^* (O)`. This divisor is supported on the `F`-rational points of `[N]`-preimages
of `T` and of `O`, and the divisor of a function supported on rational points is carried along
`f` point by point (`WeierstrassCurve.Affine.FunctionField.principal_map_eq_pushforward`). Since
`f` maps the `[N]`-preimages of `T` and of `O` over `F` bijectively onto those over `K`, the image
`f^* g` has divisor `[N]^* (f T) - [N]^* (O)`. As `f^*` intertwines translation by `S` with
translation by `f S`,

    e_N(f S, f T) = τ_{f S} (f^* g) / f^* g = f^* (τ_S g / g) = f (e_N(S, T)).

## Main results

* `WeierstrassCurve.principal_map_eq_weilPairingDivisor`: the image along `f` of a function with
  divisor `[N]^* (T) - [N]^* (O)` has divisor `[N]^* (f T) - [N]^* (O)`.
* `WeierstrassCurve.weilPairing_torsionMapAlong`: the Weil pairing is functorial under change of
  field.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1.
-/

public section

open TauCeti TauCeti.Isogeny AlgebraicGeometry

namespace WeierstrassCurve

open WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K] (W : WeierstrassCurve F)
  (f : F →+* K)

omit [DecidableEq F] [DecidableEq K] in
/-- `(n : K) ≠ 0` when `(n : F) ≠ 0`, since `f` is injective. -/
private theorem intCast_ne_zero_map (g : F →+* K) {n : ℤ} (hn : (n : F) ≠ 0) : (n : K) ≠ 0 := by
  rwa [← map_intCast g, map_ne_zero]

variable [W.IsElliptic] [IsSepClosed F] [IsSepClosed K]

omit [DecidableEq K] in
/-- **The divisor `[n]^* (T) - [n]^* (O)` is carried along `f`**: if `g` is a function on `W` with
that divisor, then its image on `W.map f` has divisor `[n]^* (f T) - [n]^* (O)`, for an
`n`-torsion point `T` and `n` invertible. -/
theorem principal_map_eq_weilPairingDivisor {n : ℤ} (hchar : (n : F) ≠ 0)
    {T : W.toAffine.Point} (hT : n • T = 0) {hψ : psiFunctionField W n ≠ 0}
    {hψ' : psiFunctionField (W.map f) n ≠ 0} {g : W.toAffine.FunctionFieldˣ}
    (hg : Divisor.principal W.toAffine.isFunctionField g = weilPairingDivisor W hψ T) :
    Divisor.principal (W.map f).toAffine.isFunctionField
        (Units.map (FunctionField.map W.toAffine f).toMonoidHom g) =
      weilPairingDivisor (W.map f) hψ' (T.mapAlong f f.injective) := by
  classical
  have hcharK := intCast_ne_zero_map f hchar
  obtain ⟨R₀, hR₀⟩ := W.toAffine.exists_point_zsmul_eq_of_zsmul_eq_zero hchar hT
  -- write both divisors as sums over the `n`-torsion, `∑_{n • S = O} ((R₀ + S) - (S))`
  rw [weilPairingDivisor_eq_sum W hchar hR₀] at hg
  rw [weilPairingDivisor_eq_sum (W.map f) hcharK
    (R₀ := R₀.mapAlong f f.injective) (by rw [← Point.mapAlong_zsmul, hR₀])]
  set s₀ := (finite_setOf_zsmul_eq W (psiFunctionField_ne_zero W hchar) 0).toFinset
  rw [show ∑ S ∈ s₀, (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine (R₀ + S)).1 -
      WeilDivisor.ofPoint (pointEquivDegreeOnePlace W.toAffine S).1) =
      WeilDivisor.pushforward (fun P ↦ (pointEquivDegreeOnePlace W.toAffine P).1)
        (∑ S ∈ s₀, (WeilDivisor.ofPoint (R₀ + S) - WeilDivisor.ofPoint S)) by
    simp [map_sum]] at hg
  rw [FunctionField.principal_map_eq_pushforward W.toAffine f hg]
  simp only [map_sum, map_sub, WeilDivisor.pushforward_ofPoint, Point.mapAlong_add]
  -- the `n`-torsion of `W` maps bijectively onto that of `W.map f`
  refine Finset.sum_nbij (fun S ↦ S.mapAlong f f.injective) (fun S hS ↦ ?_)
    (Point.mapAlong_injective f f.injective).injOn (fun S' hS' ↦ ?_) fun _ _ ↦ rfl
  · simp only [s₀, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hS ⊢
    rw [← Point.mapAlong_zsmul, hS, Point.mapAlong_zero]
  · simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq] at hS'
    obtain ⟨S, hS⟩ := (W.torsionMapAlong_bijective f hchar).2
      ⟨S', (Submodule.mem_torsionBy_iff _ _).mpr hS'⟩
    refine ⟨S, ?_, by simpa using congrArg Subtype.val hS⟩
    simp [s₀]

/-- **The Weil pairing is functorial under change of field** (Silverman III.8.1): for a
homomorphism `f` of separably closed fields and `N` invertible,
`e_N(f S, f T) = f (e_N(S, T))`. -/
@[simp]
theorem weilPairing_torsionMapAlong (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)
    (S T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)) :
    weilPairing (W.map f) N (by rwa [← map_natCast f, map_ne_zero])
        (W.torsionMapAlong f N S) (W.torsionMapAlong f N T) =
      Additive.ofMul (restrictRootsOfUnity f N (weilPairing W N hN S T).toMul) := by
  have hchar : ((N : ℤ) : F) ≠ 0 := by rwa [Int.cast_natCast]
  have hT := (Submodule.mem_torsionBy_iff _ _).mp T.2
  obtain ⟨g, hg⟩ := exists_principal_eq_weilPairingDivisor W hchar hT
  have hg' : Divisor.principal (W.map f).toAffine.isFunctionField
      (Units.map (FunctionField.map W.toAffine f).toMonoidHom g) =
      weilPairingDivisor (W.map f) (psiFunctionField_ne_zero (W.map f)
        (intCast_ne_zero_map f hchar)) (W.torsionMapAlong f N T) := by
    rw [coe_torsionMapAlong_apply]
    exact principal_map_eq_weilPairingDivisor W f hchar hT hg
  refine Additive.toMul.injective <| Subtype.val_injective <| Units.val_injective <|
    (algebraMap K (W.map f).toAffine.FunctionField).injective ?_
  rw [algebraMap_weilPairing (W.map f) N _ hg', toMul_ofMul, restrictRootsOfUnity_coe_apply,
    ← FunctionField.map_algebraMap, algebraMap_weilPairing W N hN hg, map_div₀,
    FunctionField.map_translation]
  simp

end WeierstrassCurve

end
