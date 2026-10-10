/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.GoodReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Torsion.Free
-- Proof-only: carrying points of `W` to the completion.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong

/-!
# Reduction is injective on torsion

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

Torsion of order divisible by the residue characteristic `p` is caught as well when the
ramification at `u` is small relative to `p`: if `p ∉ u ^ (p - 1)`, the kernel of reduction has no
`p`-torsion either (Silverman AEC IV.6.1;
`WeierstrassCurve.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero_of_forall_prime_dvd`). When every
prime `p` satisfies `p ∉ u ^ (p - 1)`, as at every odd prime of `ℤ`, reduction is therefore
injective on the whole torsion subgroup of `W(F)`, and its order divides `#W_k(k)`.

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
* `valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero_of_forall_prime_dvd`: a
  nonzero point of `W(F)` killed by an integer `n ≠ 0` whose prime factors `p` satisfy
  `p ∉ u ^ (p - 1)` has coordinates integral at `u`.
* `eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero_of_forall_prime_dvd`: at good reduction, such
  a point that reduces to the point at infinity is zero.
* `injOn_reductionHom_torsion`: at good reduction, if every prime `p` satisfies
  `p ∉ u ^ (p - 1)`, reduction is injective on the torsion subgroup of `W(F)`.
* `card_torsion_dvd_card_reduction`: under the same hypotheses, the order of the torsion subgroup
  of `W(F)` divides the number of points of the reduced curve.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.6.1 and VII.3.1.
-/

public section

namespace WeierstrassCurve.Affine.Point

open IsDedekindDomain IsLocalRing

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A) {W : Affine F}

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F

open scoped Classical in
/-- A nonzero point of `W(F)` killed by `n` has both coordinates integral at `u`, for any integral
model of `W` at `u`, as soon as the kernel of reduction of every integral model over the completion
has no nonzero `n`-torsion. -/
private theorem valuation_le_one_of_forall_kerReduction
    [IsIntegral (u.valuation F).valuationSubring W] [W.IsElliptic] [DecidableEq F] {n : ℕ}
    (hker : ∀ (C : WeierstrassCurve O_u) [(C.baseChange F_u).IsElliptic]
      {Q : (C.baseChange F_u).toAffine.Point}, Q ∈ C.kerReduction u → n • Q = 0 → Q = 0)
    {P : W.Point} (hP : P ≠ 0) (h : n • P = 0) :
    u.valuation F P.xCoord ≤ 1 ∧ u.valuation F P.yCoord ≤ 1 := by
  -- over the completion, a nonzero point of order `n` on an integral curve has integral
  -- coordinates; writing the curve as `C⁄F_u` for an integral model `C` puts it in the form the
  -- formal-group result is stated for
  have key (W' : WeierstrassCurve F_u) [hW' : IsIntegral O_u W'] [W'.IsElliptic]
      (Q : W'.toAffine.Point) (hQ : Q ≠ 0) (hnQ : n • Q = 0) :
      Valued.v Q.xCoord ≤ 1 ∧ Valued.v Q.yCoord ≤ 1 := by
    obtain ⟨C, rfl⟩ := hW'.integral
    exact C.valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_notMem_range u fun hmem ↦
      hQ (hker C (C.range_formalPointHomAdicCompletion_eq_kerReduction u ▸ hmem) hnQ)
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

/-- **Torsion of order prime to `u` is integral at `u`**: a nonzero point of `W(F)` killed by an
integer `n ∉ u` has both coordinates integral at `u`, for any integral model of `W` at `u`. -/
theorem valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero
    [IsIntegral (u.valuation F).valuationSubring W] [W.IsElliptic] [DecidableEq F] {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) {P : W.Point} (hP : P ≠ 0) (h : n • P = 0) :
    u.valuation F P.xCoord ≤ 1 ∧ u.valuation F P.yCoord ≤ 1 :=
  valuation_le_one_of_forall_kerReduction u
    (fun C _ _ hQ hnQ ↦ C.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero u hn hQ hnQ) hP h

/-- **Torsion is integral at `u` when ramification is small relative to the prime factors of its
order**: a nonzero point of `W(F)` killed by an integer `n ≠ 0` whose prime factors `p` all satisfy
`p ∉ u ^ (p - 1)` has both coordinates integral at `u`, for any integral model of `W` at `u`. -/
theorem valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero_of_forall_prime_dvd
    [IsIntegral (u.valuation F).valuationSubring W] [W.IsElliptic] [DecidableEq F] {n : ℕ}
    (hn : n ≠ 0)
    (hnu : ∀ p : ℕ, p.Prime → p ∣ n → (p : A) ∉ u.asIdeal ^ (p - 1)) {P : W.Point}
    (hP : P ≠ 0) (h : n • P = 0) :
    u.valuation F P.xCoord ≤ 1 ∧ u.valuation F P.yCoord ≤ 1 :=
  valuation_le_one_of_forall_kerReduction u (fun C _ _ hQ hnQ ↦
    C.eq_zero_of_mem_kerReduction_of_nsmul_eq_zero_of_forall_prime_dvd u hn hnu hQ hnQ) hP h

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

/-- **At good reduction, the kernel of reduction has no `n`-torsion when ramification is small
relative to the prime factors of `n`** (Silverman AEC VII.3.1 and IV.6.1): a point killed by an
integer `n ≠ 0` whose prime factors `p` all satisfy `p ∉ u ^ (p - 1)` and that reduces to the point
at infinity is the point at infinity. -/
theorem eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero_of_forall_prime_dvd {n : ℕ} (hn : n ≠ 0)
    (hnu : ∀ p : ℕ, p.Prime → p ∣ n → (p : A) ∉ u.asIdeal ^ (p - 1)) {P : W.Point}
    (hP : reductionHom (u.valuation F) P = 0) (h : n • P = 0) : P = 0 := by
  -- good reduction makes `W` itself elliptic
  have : W.IsElliptic := by
    rw [← baseChange_integralModel_eq (u.valuation F).valuationSubring W]
    exact inferInstanceAs ((integralModel _ W).map (algebraMap _ F)).IsElliptic
  by_contra hP0
  rcases (reductionHom_eq_zero_iff _ P).mp hP with hP' | hx
  · exact hP0 hP'
  · exact hx.not_ge
      (valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero_of_forall_prime_dvd u
        hn hnu hP0 h).1

/-- **At good reduction, reduction is injective on the torsion when ramification is small relative
to `p`** (Silverman AEC VII.3.1 and IV.6.1): if every prime `p` satisfies `p ∉ u ^ (p - 1)`,
that is, if the residue characteristic `p` of `u` has ramification index less than `p - 1` at `u`,
then reduction of points is injective on the whole torsion subgroup of `W(F)`. Over `ℚ` this holds
at every odd prime. -/
theorem injOn_reductionHom_torsion
    (hu : ∀ p : ℕ, p.Prime → (p : A) ∉ u.asIdeal ^ (p - 1)) :
    Set.InjOn (reductionHom (u.valuation F) (W := W)) (AddCommGroup.torsion W.Point) := by
  intro P hP Q hQ hPQ
  obtain ⟨m, hm, hmP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hP
  obtain ⟨k, hk, hkQ⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hQ
  rw [← sub_eq_zero]
  refine eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero_of_forall_prime_dvd u
    (Nat.mul_ne_zero hm.ne' hk.ne') (fun p hp _ ↦ hu p hp) (by rw [map_sub, hPQ, sub_self]) ?_
  rw [nsmul_sub, mul_nsmul, hmP, nsmul_zero, mul_comm m k, mul_nsmul, hkQ, nsmul_zero, sub_zero]

omit [DecidableEq (ResidueField (u.valuation F).valuationSubring)] in
/-- **At good reduction, the torsion divides the reduced point count when ramification is small
relative to `p`**: if every prime `p` satisfies `p ∉ u ^ (p - 1)`, the order of the torsion
subgroup of `W(F)` divides the number of points of the reduced curve. When the reduced curve has
infinitely many points, `Nat.card` reads `0` there and the statement is vacuous. -/
theorem card_torsion_dvd_card_reduction
    (hu : ∀ p : ℕ, p.Prime → (p : A) ∉ u.asIdeal ^ (p - 1)) :
    Nat.card (AddCommGroup.torsion W.Point) ∣
      Nat.card ((integralModel (u.valuation F).valuationSubring W).map
        (residue (u.valuation F).valuationSubring)).toAffine.Point := by
  classical
  exact AddSubgroup.card_dvd_of_injective
    ((reductionHom (u.valuation F)).comp (AddCommGroup.torsion W.Point).subtype)
    fun P Q hPQ ↦ Subtype.ext (injOn_reductionHom_torsion u hu P.2 Q.2 hPQ)

end WeierstrassCurve.Affine.Point

end
