/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion
-- Proof-only: carrying points of `W` to the completion.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong

/-!
# Reduction is injective on torsion prime to the residue characteristic

Let `A` be a Dedekind domain with fraction field `F`, let `u` be a height-one prime of `A`, and let
`W` be an elliptic curve over `F` with an integral model at `u`. A point of `W(F)` whose order
`n` lies outside `u` has integral coordinates at `u`: carried to the completion `F_u`, it is a
point of order prime to the residue characteristic, and those avoid the kernel of reduction
`E₁(F_u)` (`WeierstrassCurve.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero`).

When the integral model has unit discriminant, so that `W` has good reduction at `u`, reduction of
points is a homomorphism `W(F) →+ W_k(k)` to the points of the reduced curve
(`WeierstrassCurve.Affine.Point.reductionHom`), whose kernel is the point at infinity together with
the points whose `x`-coordinate has a pole. Integrality of prime-to-`u` torsion therefore says that
this homomorphism is injective on the `n`-torsion `W(F)[n]` for every `n ∉ u`: Silverman AEC
VII.3.1(b), read over the global field. When the residue field is finite this bounds the
prime-to-`u` torsion: `#W(F)[n]` divides `#W_k(k)`.

## Main results

All results are in the namespace `WeierstrassCurve.Affine.Point`.

* `valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero`: a nonzero point of
  `W(F)` killed by an integer `n ∉ u` has coordinates integral at `u`.
* `eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero`: at good reduction, a point of order prime to
  `u` that reduces to the point at infinity is zero.
* `injOn_reductionHom_torsionBy`: at good reduction, reduction is injective on `W(F)[n]` for
  `n ∉ u`.
* `card_torsionBy_dvd_card_reduction`: at good reduction, `#W(F)[n]` divides the number of points
  of the reduced curve for `n ∉ u`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.3.1.
-/

public section

namespace WeierstrassCurve.Affine.Point

open IsDedekindDomain IsLocalRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) {W : Affine F}

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F

/-- **Torsion of order prime to `u` is integral at `u`**: a nonzero point of `W(F)` killed by an
integer `n ∉ u` has both coordinates integral at `u`, for any integral model of `W` at `u`. -/
theorem valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero
    [IsIntegral (u.valuation F).valuationSubring W] [W.IsElliptic] [DecidableEq F] {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) {P : W.Point} (hP : P ≠ 0) (h : n • P = 0) :
    u.valuation F P.xCoord ≤ 1 ∧ u.valuation F P.yCoord ≤ 1 := by
  classical
  -- over the completion, a nonzero point of order prime to `u` on an integral curve has integral
  -- coordinates; writing the curve as `C⁄F_u` for an integral model `C` puts it in the form the
  -- formal-group result is stated for
  have key (W' : WeierstrassCurve F_u) [hW' : IsIntegral O_u W'] [W'.IsElliptic]
      (Q : W'.toAffine.Point) (hQ : Q ≠ 0) (hnQ : n • Q = 0) :
      Valued.v Q.xCoord ≤ 1 ∧ Valued.v Q.yCoord ≤ 1 := by
    obtain ⟨C, rfl⟩ := hW'.integral
    exact C.valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero u hn hQ hnQ
  have hval (a : F) : Valued.v (algebraMap F F_u a) = u.valuation F a :=
    u.valuedAdicCompletion_eq_valuation' a
  -- the coefficients of `W`, integral at `u`, stay integral in the completion
  have hmem (a : F) (ha : u.valuation F a ≤ 1) : algebraMap F F_u a ∈ O_u :=
    (HeightOneSpectrum.mem_adicCompletionIntegers ..).mpr ((hval a).trans_le ha)
  have : IsIntegral O_u (W.map (algebraMap F F_u)) :=
    ⟨⟨⟨_, hmem _ (valuation_a₁_le_one _)⟩, ⟨_, hmem _ (valuation_a₂_le_one _)⟩,
      ⟨_, hmem _ (valuation_a₃_le_one _)⟩, ⟨_, hmem _ (valuation_a₄_le_one _)⟩,
      ⟨_, hmem _ (valuation_a₆_le_one _)⟩⟩, rfl⟩
  obtain ⟨x, y, hxy, rfl⟩ : ∃ x y, ∃ hxy : W.Nonsingular x y, P = some x y hxy := by
    cases P with
    | zero => exact absurd rfl hP
    | some x y hxy => exact ⟨x, y, hxy, rfl⟩
  -- carry the point to the completion
  have hnQ : n • mapAlong (algebraMap F F_u) (algebraMap F F_u).injective (some x y hxy) = 0 := by
    rw [← natCast_zsmul, ← mapAlong_zsmul, natCast_zsmul, h, mapAlong_zero]
  have hv := key _ _ (by simp) hnQ
  rw [mapAlong_some, xCoord_some, yCoord_some, hval, hval] at hv
  rwa [xCoord_some, yCoord_some]

variable [IsIntegral (u.valuation F).valuationSubring W]
  [(integralModel (u.valuation F).valuationSubring W).IsElliptic] [DecidableEq F]
  [DecidableEq (ResidueField (u.valuation F).valuationSubring)]

/-- **At good reduction, reduction has no torsion prime to `u` in its kernel** (Silverman AEC
VII.3.1(b)): a point killed by an integer `n ∉ u` that reduces to the point at infinity is the
point at infinity. -/
theorem eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : (n : A) ∉ u.asIdeal)
    {P : W.Point} (hP : reductionHom (u.valuation F) P = 0) (h : n • P = 0) : P = 0 := by
  -- good reduction makes `W` itself elliptic
  have : W.IsElliptic := by
    rw [← baseChange_integralModel_eq (u.valuation F).valuationSubring W]
    exact inferInstanceAs ((integralModel _ W).map (algebraMap _ F)).IsElliptic
  by_contra hP0
  rcases (reductionHom_eq_zero_iff _ P).mp hP with hP' | hx
  · exact hP0 hP'
  · exact hx.not_ge
      (valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero u hn hP0 h).1

/-- **At good reduction, reduction is injective on torsion prime to `u`** (Silverman AEC
VII.3.1(b)): for `n ∉ u`, reduction of points is injective on the `n`-torsion `W(F)[n]`. -/
theorem injOn_reductionHom_torsionBy {n : ℕ} (hn : (n : A) ∉ u.asIdeal) :
    Set.InjOn (reductionHom (u.valuation F) (W := W)) (AddSubgroup.torsionBy W.Point n) := by
  intro P hP Q hQ hPQ
  rw [SetLike.mem_coe, AddSubgroup.torsionBy.nsmul_iff] at hP hQ
  rw [← sub_eq_zero]
  exact eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u hn
    (by rw [map_sub, hPQ, sub_self]) (by rw [nsmul_sub, hP, hQ, sub_self])

omit [DecidableEq (ResidueField (u.valuation F).valuationSubring)] in
/-- **At good reduction, the torsion prime to `u` divides the reduced point count**: for `n ∉ u`,
the order of `W(F)[n]` divides the number of points of the reduced curve. When the reduced curve
has infinitely many points, `Nat.card` reads `0` there and the statement is vacuous. -/
theorem card_torsionBy_dvd_card_reduction {n : ℕ} (hn : (n : A) ∉ u.asIdeal) :
    Nat.card (AddSubgroup.torsionBy W.Point n) ∣
      Nat.card ((integralModel (u.valuation F).valuationSubring W).map
        (residue (u.valuation F).valuationSubring)).toAffine.Point := by
  classical
  exact AddSubgroup.card_dvd_of_injective
    ((reductionHom (u.valuation F)).comp (AddSubgroup.torsionBy W.Point n).subtype)
    fun P Q hPQ ↦ Subtype.ext (injOn_reductionHom_torsionBy u hn P.2 Q.2 hPQ)

end WeierstrassCurve.Affine.Point

end
