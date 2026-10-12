/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Basic
-- Proof-only: `[m] ∘ [k] = [m k]`; `[n]` is `n` times the identity, acts on points as `n • ·`,
-- and is separable when `n` is invertible.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Comp
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Separability
-- Proof-only: `τ_P^* ∘ φ^* = φ^* ∘ τ_{φ(P)}^*` for a separable isogeny `φ`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Kernel

/-!
# Compatibility of the Weil pairings across levels

Let `W` be an elliptic curve over a separably closed field `F`, and let `N = m k` be a positive
integer invertible in `F`. The Weil pairings at the levels `N` and `m` are compatible
(Silverman III.8.1(g)):

    e_N(S, T) = e_m(k S, T)    for `S ∈ E[N]` and `T ∈ E[m]`,

as roots of unity in `F`; consequently `e_N(S, T) ^ k = e_m(k S, k T)` for `S, T ∈ E[N]`. At
`N = ℓ ^ (n + 1)` and `m = ℓ ^ n` the second form says that the pairings `e_{ℓ ^ n}` are compatible
with multiplication by `ℓ` on the torsion tower and the `ℓ`-th power map on the roots of unity,
which is what assembling them into the `ℓ`-adic Weil pairing on the Tate module requires.

## Main results

* `TauCeti.Isogeny.coe_weilPairing_eq_coe_weilPairing_nsmul`: `e_N(S, T) = e_m(k S, T)` for
  `S ∈ E[N]` and `T ∈ E[m]`.
* `TauCeti.Isogeny.coe_weilPairing_pow_eq_coe_weilPairing_nsmul`: `e_N(S, T) ^ k = e_m(k S, k T)`
  for `S, T ∈ E[N]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1(g).
-/

public section

open WeierstrassCurve WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]

-- Pulling back along `[m]` and then along `[k]` is pulling back along `[m k]`, since
-- `[m] ∘ [k] = [m k]`. All three pullbacks are endomorphisms of `F(W)`, so each carries its own
-- algebra structure, passed explicitly.
private theorem divisorPullback_mulByIntIsogeny_divisorPullback_mulByIntIsogeny {m k n : ℤ}
    (hmk : m * k = n) (hm : psiFunctionField W m ≠ 0) (hk : psiFunctionField W k ≠ 0)
    (hn : psiFunctionField W n ≠ 0) (D : Divisor F W.toAffine.FunctionField) :
    @divisorPullback _ _ _ _ (mulByIntIsogeny W hk) (mulByIntIsogeny W hk).fieldPullback.toAlgebra
        (fun _ ↦ rfl)
      (@divisorPullback _ _ _ _ (mulByIntIsogeny W hm)
        (mulByIntIsogeny W hm).fieldPullback.toAlgebra (fun _ ↦ rfl) D) =
      @divisorPullback _ _ _ _ (mulByIntIsogeny W hn)
        (mulByIntIsogeny W hn).fieldPullback.toAlgebra (fun _ ↦ rfl) D := by
  subst hmk
  have hcongr : ∀ ψ ψ' : Isogeny W.toAffine W.toAffine, ψ = ψ' →
      @divisorPullback _ _ _ _ ψ ψ.fieldPullback.toAlgebra (fun _ ↦ rfl) D =
        @divisorPullback _ _ _ _ ψ' ψ'.fieldPullback.toAlgebra (fun _ ↦ rfl) D := by
    rintro _ _ rfl
    rfl
  rw [@divisorPullback_comp _ _ _ _ (mulByIntIsogeny W hk)
    (mulByIntIsogeny W hk).fieldPullback.toAlgebra (fun _ ↦ rfl) _ (mulByIntIsogeny W hm)
    (mulByIntIsogeny W hm).fieldPullback.toAlgebra
    ((mulByIntIsogeny W hm).comp (mulByIntIsogeny W hk)).fieldPullback.toAlgebra (fun _ ↦ rfl)
    (fun _ ↦ rfl) D]
  exact hcongr _ _ (mulByIntIsogeny_comp_mulByIntIsogeny W hm hk hn)

variable [DecidableEq F] [IsSepClosed F] {N m : ℕ} [NeZero N] [NeZero m] (hN : (N : F) ≠ 0)
  (hm : (m : F) ≠ 0)

local instance : IsIntegrallyClosed W.toAffine.CoordinateRing :=
  W.toAffine.isIntegrallyClosed_coordinateRing

/- The proof is Silverman's. Let `g` be a function with divisor `[m]^* (T) - [m]^* (O)`, the
function from which `e_m(·, T)` is built. Since `[m] ∘ [k] = [N]`, its pullback `[k]^* g` has
divisor `[N]^* (T) - [N]^* (O)`, so it computes `e_N(·, T)`. Translation by `S` moves `[k]^* g`
to `[k]^* (τ_{k S}^* g)`, as `[k]` is a separable isogeny sending `S` to `k S`, hence

    e_N(S, T) = τ_S ([k]^* g) / [k]^* g = [k]^* (τ_{k S}^* g / g) = e_m(k S, T). -/

/-- **The Weil pairings are compatible across levels** (Silverman III.8.1(g)): for `N = m k`
invertible in `F`, `e_N(S, T) = e_m(k S, T)` for `S ∈ E[N]` and `T ∈ E[m]`, as roots of unity in
`F`. The `m`-torsion point `k S` and the `N`-torsion point `T` are given as `S'` and `T'`. -/
theorem coe_weilPairing_eq_coe_weilPairing_nsmul {k : ℕ} (hk : m * k = N)
    {S T' : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)}
    {S' T : Submodule.torsionBy ℤ W.toAffine.Point (m : ℤ)}
    (hS : (S' : W.toAffine.Point) = k • (S : W.toAffine.Point))
    (hT : (T' : W.toAffine.Point) = T) :
    ((weilPairing W N hN S T').toMul : Fˣ) = ((weilPairing W m hm S' T).toMul : Fˣ) := by
  have hcN : ((N : ℤ) : F) ≠ 0 := by rwa [Int.cast_natCast]
  have hcm : ((m : ℤ) : F) ≠ 0 := by rwa [Int.cast_natCast]
  have hck : ((k : ℤ) : F) ≠ 0 := by
    rw [Int.cast_natCast]
    exact right_ne_zero_of_mul (by rwa [← Nat.cast_mul, hk])
  have hmkN : (m : ℤ) * k = N := by rw [← hk, Nat.cast_mul]
  have hψN := psiFunctionField_ne_zero W hcN
  have hψm := psiFunctionField_ne_zero W hcm
  have hψk := psiFunctionField_ne_zero W hck
  -- `g` computes `e_m(·, T)`
  obtain ⟨g, hg⟩ := exists_principal_eq_weilPairingDivisor W hcm
    ((Submodule.mem_torsionBy_iff _ _).mp T.2)
  -- and its pullback `[k]^* g` computes `e_N(·, T)`
  let g' : W.toAffine.FunctionFieldˣ :=
    Units.map ((mulByIntIsogeny W hψk).fieldPullback : W.toAffine.FunctionField →* _) g
  have hg' : Divisor.principal W.toAffine.isFunctionField g' = weilPairingDivisor W hψN T' := by
    have hpull : Divisor.principal W.toAffine.isFunctionField g' =
        @divisorPullback _ _ _ _ (mulByIntIsogeny W hψk)
          (mulByIntIsogeny W hψk).fieldPullback.toAlgebra (fun _ ↦ rfl)
          (Divisor.principal W.toAffine.isFunctionField g) :=
      (@divisorPullback_principal _ _ _ _ (mulByIntIsogeny W hψk)
        (mulByIntIsogeny W hψk).fieldPullback.toAlgebra (fun _ ↦ rfl) g).symm
    rw [hpull, hg, weilPairingDivisor_def, weilPairingDivisor_def, map_sub, hT,
      divisorPullback_mulByIntIsogeny_divisorPullback_mulByIntIsogeny W hmkN hψm hψk hψN,
      divisorPullback_mulByIntIsogeny_divisorPullback_mulByIntIsogeny W hmkN hψm hψk hψN]
  -- translation by `S` moves `[k]^* g` to `[k]^* (τ_{k S}^* g)`
  have := (isSeparable_mulByIntIsogeny_iff W hψk).2 hck
  have hkS : (mulByIntIsogeny W hψk).toPointHom S = S' := by
    rw [← Hom.pointMap_ofIsogeny_eq_toPointHom, ofIsogeny_mulByIntIsogeny, Hom.zsmul_pointMap,
      Hom.id_pointMap, hS, natCast_zsmul]
  have hmove := (mulByIntIsogeny W hψk).translation_fieldPullback S g
  rw [hkS] at hmove
  refine Units.ext ((algebraMap F W.toAffine.FunctionField).injective ?_)
  rw [algebraMap_weilPairing W N hN hg', ← (mulByIntIsogeny W hψk).fieldPullback.commutes,
    algebraMap_weilPairing W m hm hg, map_div₀, ← hmove, Units.coe_map, MonoidHom.coe_ofClass]

/-- **The Weil pairings are compatible with the torsion tower**: for `N = m k` invertible in `F`,
`e_N(S, T) ^ k = e_m(k S, k T)` for `S, T ∈ E[N]`, as roots of unity in `F`. The `m`-torsion
points `k S` and `k T` are given as `S'` and `T'`. -/
theorem coe_weilPairing_pow_eq_coe_weilPairing_nsmul {k : ℕ} (hk : m * k = N)
    {S T : Submodule.torsionBy ℤ W.toAffine.Point (N : ℤ)}
    {S' T' : Submodule.torsionBy ℤ W.toAffine.Point (m : ℤ)}
    (hS : (S' : W.toAffine.Point) = k • (S : W.toAffine.Point))
    (hT : (T' : W.toAffine.Point) = k • (T : W.toAffine.Point)) :
    ((weilPairing W N hN S T).toMul : Fˣ) ^ k = ((weilPairing W m hm S' T').toMul : Fˣ) := by
  rw [← coe_weilPairing_eq_coe_weilPairing_nsmul W hN hm hk hS (T' := k • T)
    (by rw [Submodule.coe_smul_of_tower, hT]), map_nsmul, toMul_nsmul, SubgroupClass.coe_pow]

end TauCeti.Isogeny

end
