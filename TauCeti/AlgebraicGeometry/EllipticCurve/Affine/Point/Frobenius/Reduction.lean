/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
-- Proof-only: transport of points along an equality of curves keeps their coordinates.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
-- Proof-only: reduction is injective on torsion prime to the residue characteristic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction
-- Proof-only: the `q`-power map on points is a root of `X² - a_q X + q`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Charpoly

/-!
# Reduction turns a Frobenius element into the `q`-power map

Let `W` be a Weierstrass curve over a field `K`, let `L` be an extension of `K` with a valuation
`v`, and suppose that the equation `W`, read over `L`, has good reduction at `v`: its integral
model over the valuation ring `O` of `v` has unit discriminant. Reduction of points is then a
homomorphism `W(L) →+ W_k(k)` to the points of the reduced curve over the residue field `k` of
`O` (`WeierstrassCurve.Affine.Point.reductionHom`).

Suppose moreover that the reduced curve is the base change to `k` of a curve `C` over a finite
subfield `F` of `k` with `q` elements, as the reduction of a curve over a local field is the base
change of its reduction over the smaller residue field. Let `τ` be a `K`-algebra endomorphism of
`L` which is a **Frobenius element** for `v`: `v (τ x - x ^ q) < 1` for every `x` in `O`, so
that `τ` acts on `k` as the `q`-power map. Then reduction carries `τ` to the `q`-power map on the
coordinates of the points of `C` over `k`:

`red (τ P) = Fr (red P)`.

This is how the Galois action of a Frobenius element on the points of good reduction is computed
on the reduced curve, where the `q`-power map satisfies `Fr² - a_q Fr + q = 0`
(`TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom`).

Over the fraction field `L` of a Dedekind domain, at a height-one prime `u` of good reduction,
this gives the relation `τ (τ P) = a_q • τ P - q • P` on the torsion of order prime to `u`, where
`a_q` is the Frobenius trace of `C`: the difference of the two sides reduces to the point at
infinity and is killed by an integer prime to `u`, and reduction is injective on such torsion
(`WeierstrassCurve.Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero`).

## Main results

* `WeierstrassCurve.Affine.Point.cast_reductionHom_map_eq_map_frobeniusAlgHom`: reduction carries
  a Frobenius element for `v` to the `q`-power map on the points of the reduced curve.
* `WeierstrassCurve.Affine.Point.map_map_eq_of_nsmul_eq_zero`: over the fraction field of a
  Dedekind domain, an endomorphism acting on the residues at a prime `u` of good reduction as the
  `q`-power map satisfies `τ (τ P) = a_q • τ P - q • P` on the torsion of order prime to `u`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.2.3.1, VII.2, VII.3.1 and
  VII.7.
-/

public section

open IsLocalRing

namespace WeierstrassCurve.Affine.Point

variable {K L Γ₀ : Type*} [Field K] [Field L] [Algebra K L] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀) {W : WeierstrassCurve K} [IsIntegral v.valuationSubring (W⁄L)]
  [(integralModel v.valuationSubring (W⁄L)).IsElliptic] [DecidableEq L]
  [DecidableEq (ResidueField v.valuationSubring)]
  {F : Type*} [Field F] [Fintype F] [Algebra F (ResidueField v.valuationSubring)]
  {C : WeierstrassCurve F}

/-- **Reduction carries a Frobenius element to the `q`-power map.** Let `W` have good reduction at
the valuation `v` of `L`, with reduced curve the base change of a curve `C` over a finite field `F`
with `q` elements, and let `τ` be a `K`-algebra endomorphism of `L` with `v (τ x - x ^ q) < 1` for
every `x` in the valuation ring. Then the reduction of `τ P` is the image of the reduction of `P`
under the `q`-power map `FiniteField.frobeniusAlgHom` on the coordinates of the points of `C`. -/
theorem cast_reductionHom_map_eq_map_frobeniusAlgHom
    (hC : (integralModel v.valuationSubring (W⁄L)).map (residue v.valuationSubring) =
      C.baseChange (ResidueField v.valuationSubring))
    {τ : L →ₐ[K] L} (hτ : ∀ x, v x ≤ 1 → v (τ x - x ^ Fintype.card F) < 1)
    (P : (W⁄L).toAffine.Point) :
    AddEquiv.cast (M := fun V ↦ V.toAffine.Point) hC (reductionHom v (map τ P)) =
      map (FiniteField.frobeniusAlgHom F _)
        (AddEquiv.cast (M := fun V ↦ V.toAffine.Point) hC (reductionHom v P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · simp only [← zero_def, _root_.map_zero]
  rw [map_some]
  by_cases hx : v x ≤ 1
  · -- `τ` preserves integrality and raises residues to the `q`-th power
    have hres (z : L) (hz : v z ≤ 1) :
        ∃ hτz : v (τ z) ≤ 1,
          residue v.valuationSubring ⟨τ z, (v.mem_valuationSubring_iff _).mpr hτz⟩ =
            residue v.valuationSubring ⟨z, (v.mem_valuationSubring_iff z).mpr hz⟩ ^
              Fintype.card F := by
      have hzq : v (z ^ Fintype.card F) ≤ 1 := by
        rw [map_pow]
        exact pow_le_one' hz _
      have hτz : v (τ z) ≤ 1 := by
        rw [← sub_add_cancel (τ z) (z ^ Fintype.card F)]
        exact v.map_add_le (hτ z hz).le hzq
      refine ⟨hτz, ?_⟩
      rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
      exact hτ z hz
    obtain ⟨hτx, hx'⟩ := hres x hx
    obtain ⟨hτy, hy'⟩ := hres y (valuation_y_le_one_of_valuation_x_le_one v h.left hx)
    have hmem (P : (W⁄L).toAffine.Point) : P ∈ (W⁄L).toAffine.nonsingularReduction v := by
      rw [nonsingularReduction_eq_top]
      trivial
    have hτh := (W.toAffine.baseChange_nonsingular τ.injective x y).mpr h
    rw [reductionHom_some_of_valuation_le_one v hτh hτx
        ((some_mem_nonsingularReduction_iff v hτh hτx).mp (hmem _)),
      reductionHom_some_of_valuation_le_one v h hx
        ((some_mem_nonsingularReduction_iff v h hx).mp (hmem _)),
      AddEquiv.cast_apply, AddEquiv.cast_apply, cast_some hC, cast_some hC, map_some]
    simp only [FiniteField.frobeniusAlgHom_apply, hx', hy']
  · -- a coordinate with a pole keeps its pole, since `τ` sends `x⁻¹` into the maximal ideal
    have hx₁ : 1 < v x := not_le.mp hx
    have hτx : 1 < v (τ x) := by
      have hinv : v x⁻¹ < 1 := by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ hx₁
      have h' : v (τ x⁻¹) < 1 := by
        rw [← sub_add_cancel (τ x⁻¹) (x⁻¹ ^ Fintype.card F)]
        refine v.map_add_lt (hτ _ hinv.le) ?_
        rw [map_pow]
        exact pow_lt_one₀ zero_le hinv Fintype.card_ne_zero
      have hx0 : τ x ≠ 0 :=
        (map_ne_zero τ).mpr (v.ne_zero_iff.mp (zero_lt_one.trans hx₁).ne')
      rwa [map_inv₀, map_inv₀, inv_lt_one₀ (v.pos_iff.mpr hx0)] at h'
    rw [reductionHom_some_of_one_lt v h hx₁, reductionHom_some_of_one_lt v _ hτx, _root_.map_zero,
      _root_.map_zero]

end WeierstrassCurve.Affine.Point

namespace WeierstrassCurve

section Dedekind

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K L : Type*} [Field K] [Field L]
  [Algebra K L] [Algebra A L] [IsFractionRing A L] (u : HeightOneSpectrum A)
  {W : WeierstrassCurve K} [IsIntegral (u.valuation L).valuationSubring (W⁄L)]
  [(integralModel (u.valuation L).valuationSubring (W⁄L)).IsElliptic] [DecidableEq L]
  {F : Type*} [Field F] [Fintype F] [Algebra F (ResidueField (u.valuation L).valuationSubring)]
  {C : WeierstrassCurve F}

/-- **A Frobenius element satisfies `X² - a_q X + q` on prime-to-`u` torsion at good reduction.**
Let `W` have good reduction at a height-one prime `u` of a Dedekind domain with fraction field `L`,
with reduced curve the base change of a curve `C` over a finite field `F` with `q` elements, and
let `τ` be a `K`-algebra endomorphism of `L` acting on the residues at `u` as the `q`-power map.
If `n • P = 0` for a point `P` of `W(L)` and an integer `n ∉ u`, then
`τ (τ P) = a_q • τ P - q • P`, where `a_q` is the Frobenius trace of `C`. -/
theorem Affine.Point.map_map_eq_of_nsmul_eq_zero
    (hC : (integralModel (u.valuation L).valuationSubring (W⁄L)).map
      (residue (u.valuation L).valuationSubring) =
        C.baseChange (ResidueField (u.valuation L).valuationSubring))
    {τ : L →ₐ[K] L}
    (hτ : ∀ x, u.valuation L x ≤ 1 → u.valuation L (τ x - x ^ Fintype.card F) < 1) {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) {P : (W⁄L).toAffine.Point} (hP : n • P = 0) :
    Affine.Point.map τ (Affine.Point.map τ P) =
      C.frobeniusTrace • Affine.Point.map τ P - Nat.card F • P := by
  classical
  -- `C` is elliptic, its base change being the reduction of `W`
  have : C.IsElliptic := by
    have hΔ := ((integralModel (u.valuation L).valuationSubring (W⁄L)).map
      (residue (u.valuation L).valuationSubring)).isUnit_Δ
    rw [hC, WeierstrassCurve.baseChange, map_Δ] at hΔ
    exact ⟨isUnit_iff_ne_zero.mpr fun h0 ↦ not_isUnit_zero (by rwa [h0, _root_.map_zero] at hΔ)⟩
  -- `τ (τ P) - a_q • τ P + q • P` reduces to `Fr (Fr P') - a_q • Fr P' + q • P' = 0`, where
  -- `P'` is the reduction of `P` and `Fr` is the `q`-power map, and is killed by `n`
  set e := AddEquiv.cast
    (M := fun V : WeierstrassCurve (ResidueField (u.valuation L).valuationSubring) ↦
      V.toAffine.Point) hC
  have hred (Q : (W⁄L).toAffine.Point) :=
    Affine.Point.cast_reductionHom_map_eq_map_frobeniusAlgHom (u.valuation L) hC hτ Q
  rw [← sub_eq_zero]
  refine Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u hn ?_ ?_
  · apply e.injective
    rw [map_sub, map_sub, map_sub, map_sub, map_zsmul, map_zsmul, map_nsmul, map_nsmul, hred, hred,
      TauCeti.Isogeny.map_frobeniusAlgHom_map_frobeniusAlgHom, _root_.map_zero]
    exact sub_self _
  · rw [nsmul_sub, nsmul_sub, ← map_nsmul, ← map_nsmul, smul_comm n, ← map_nsmul, smul_comm n, hP]
    simp

end Dedekind


end WeierstrassCurve
