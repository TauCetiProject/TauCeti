/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Galois.Divisor
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic

/-!
# Galois equivariance of the Weil pairing

Let `W` be an elliptic curve over a field `F`, let `K` be a separably closed extension of `F`, and
let `N` be a positive integer invertible in `K`. Every `F`-automorphism `σ` of `K` acts on the
points of `W` over `K` (`WeierstrassCurve.pointGaloisAction`), on its function field
(`WeierstrassCurve.functionFieldGaloisAction`) and on its divisors
(`WeierstrassCurve.divisorGaloisAction`). This file proves that the Weil pairing of `W` over `K`
commutes with these actions:

    e_N(σ S, σ T) = σ (e_N(S, T)).

The proof is Silverman's. The divisor `[N]^* (T) - [N]^* (O)` is the formal sum of the fibre of
`[N]` over `T` minus that over `O`, and `σ` carries the fibre of `[N]` over `T` bijectively onto
the fibre over `σ T`, because it acts on points by a group automorphism. So `σ` carries the
divisor attached to `T` to the divisor attached to `σ T`
(`TauCeti.Isogeny.divisorGaloisAction_weilPairingDivisor`). If `g` has divisor
`[N]^* (T) - [N]^* (O)`, then `σ g` therefore has divisor `[N]^* (σ T) - [N]^* (O)`, and since
`σ` intertwines translation by `S` with translation by `σ S`,

    e_N(σ S, σ T) = τ_{σ S} (σ g) / σ g = σ (τ_S g / g) = σ (e_N(S, T)).

## Main results

* `TauCeti.Isogeny.divisorGaloisAction_divisorPullback_mulByIntIsogeny_ofPoint`: the pullback
  `[n]^* (T)` is Galois-equivariant in `T`.
* `TauCeti.Isogeny.divisorGaloisAction_weilPairingDivisor`: the divisor
  `[n]^* (T) - [n]^* (O)` is Galois-equivariant in `T`.
* `TauCeti.Isogeny.weilPairing_torsionGaloisAction`: the Weil pairing is Galois-equivariant.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(e).
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve

namespace TauCeti.Isogeny

open AlgebraicGeometry

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] [IsSepClosed K]
  (W : WeierstrassCurve F) [W.IsElliptic]

/-- **Pullback along `[n]` is Galois-equivariant on points**: an `F`-automorphism `σ` of a
separably closed field `K` in which `n` is invertible carries `[n]^* (T)` to `[n]^* (σ T)`. -/
theorem divisorGaloisAction_divisorPullback_mulByIntIsogeny_ofPoint (σ : K ≃ₐ[F] K) {n : ℤ}
    (hchar : (n : K) ≠ 0) (T : (W⁄K).toAffine.Point) :
    letI := (mulByIntIsogeny (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar)).fieldPullback.toAlgebra
    Multiplicative.toAdd (W.divisorGaloisAction σ)
        ((mulByIntIsogeny (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar)).divisorPullback
          (fun _ ↦ rfl) (WeilDivisor.ofPoint ((W⁄K).toAffine.pointEquivDegreeOnePlace T).1)) =
      (mulByIntIsogeny (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar)).divisorPullback
        (fun _ ↦ rfl) (WeilDivisor.ofPoint ((W⁄K).toAffine.pointEquivDegreeOnePlace
          (Multiplicative.toAdd (W.pointGaloisAction σ) T)).1) := by
  let _ := (mulByIntIsogeny (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar)).fieldPullback.toAlgebra
  set e := Multiplicative.toAdd (W.pointGaloisAction σ)
  -- `σ` carries the fibre of `[n]` over `T` onto the fibre over `σ T`
  rw [divisorPullback_mulByIntIsogeny_ofPoint _ hchar,
    divisorPullback_mulByIntIsogeny_ofPoint _ hchar, map_sum]
  refine Finset.sum_equiv e.toEquiv (fun R ↦ ?_) fun R _ ↦ ?_
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, AddEquiv.toEquiv_eq_coe,
      EquivLike.coe_coe, ← map_zsmul, e.injective.eq_iff]
  · rw [divisorGaloisAction_ofPoint, placeGaloisAction_pointEquivDegreeOnePlace]
    simp only [e, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe]

/-- **The divisor `[n]^* (T) - [n]^* (O)` is Galois-equivariant**: an `F`-automorphism `σ` of a
separably closed field `K` in which `n` is invertible carries it to `[n]^* (σ T) - [n]^* (O)`. -/
@[simp]
theorem divisorGaloisAction_weilPairingDivisor (σ : K ≃ₐ[F] K) {n : ℤ} (hchar : (n : K) ≠ 0)
    (T : (W⁄K).toAffine.Point) :
    Multiplicative.toAdd (W.divisorGaloisAction σ)
        (weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar) T) =
      weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar)
        (Multiplicative.toAdd (W.pointGaloisAction σ) T) := by
  have h0 : Multiplicative.toAdd (W.pointGaloisAction σ) .zero = .zero := by
    rw [← Point.zero_def, map_zero]
  rw [weilPairingDivisor_def, weilPairingDivisor_def, map_sub,
    ← coe_pointEquivDegreeOnePlace_zero,
    divisorGaloisAction_divisorPullback_mulByIntIsogeny_ofPoint W σ hchar,
    divisorGaloisAction_divisorPullback_mulByIntIsogeny_ofPoint W σ hchar, h0]

variable (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)

/-- **The Weil pairing is Galois-equivariant** (Silverman III.8.1(e)): for an `F`-automorphism `σ`
of a separably closed field `K` in which `N` is invertible, `e_N(σ S, σ T) = σ (e_N(S, T))`. -/
@[simp]
-- `torsionGaloisAction` acts on `AddSubgroup.torsionBy`, which Mathlib defines as
-- `(Submodule.torsionBy ℤ _ _).toAddSubgroup`, so its carrier is that of the Weil pairing's domain
-- `Submodule.torsionBy ℤ _ _` and `S`, `T` may be fed to it directly.
theorem weilPairing_torsionGaloisAction (σ : K ≃ₐ[F] K)
    (S T : Submodule.torsionBy ℤ (W⁄K).toAffine.Point (N : ℤ)) :
    weilPairing (W⁄K) N hN (Multiplicative.toAdd (W.torsionGaloisAction N σ) S)
        (Multiplicative.toAdd (W.torsionGaloisAction N σ) T) =
      Additive.ofMul (restrictRootsOfUnity σ N (weilPairing (W⁄K) N hN S T).toMul) := by
  have hchar : ((N : ℤ) : K) ≠ 0 := by rwa [Int.cast_natCast]
  obtain ⟨g, hg⟩ := exists_principal_eq_weilPairingDivisor (W⁄K) hchar
    ((Submodule.mem_torsionBy_iff _ _).mp T.2)
  let σg := Units.map (MonoidHom.ofClass (W.functionFieldGaloisAction σ)) g
  have hσg : Divisor.principal (W⁄K).toAffine.isFunctionField σg =
      weilPairingDivisor (W⁄K) (psiFunctionField_ne_zero (W⁄K) hchar)
        (Multiplicative.toAdd (W.torsionGaloisAction N σ) T :) := by
    -- `torsionGaloisAction_apply_coe` fires through the unfolding of `AddSubgroup.torsionBy`
    rw [divisorGaloisAction_principal, hg, divisorGaloisAction_weilPairingDivisor W σ hchar,
      torsionGaloisAction_apply_coe]
  refine Additive.toMul.injective <| Subtype.val_injective <| Units.val_injective <|
    (algebraMap K (W⁄K).toAffine.FunctionField).injective ?_
  -- as above, `torsionGaloisAction_apply_coe` fires by unfolding `AddSubgroup.torsionBy`
  rw [algebraMap_weilPairing (W⁄K) N hN hσg, toMul_ofMul, restrictRootsOfUnity_coe_apply,
    ← functionFieldGaloisAction_algebraMap, algebraMap_weilPairing (W⁄K) N hN hg, map_div₀,
    functionFieldGaloisAction_translation, torsionGaloisAction_apply_coe]
  simp [σg]

end TauCeti.Isogeny
