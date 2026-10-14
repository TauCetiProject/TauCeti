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
-- Proof-only: the torsion of the nonsingular points of a singular cubic.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Singular

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

At bad reduction, when the integral model has singular reduction, the same integrality makes
reduction injective on the points of `W(F)[n]` with nonsingular reduction, for `n ∉ u`. Those land
in the `n`-torsion of the nonsingular points of a singular cubic over the residue field, whose
order divides `n`. So the subgroup `E₀(F)` of points with nonsingular reduction meets `W(F)[n]` in
at most `n` points, and the rest of `W(F)[n]` is seen by the index `[E(F) : E₀(F)]`:
`#W(F)[n]` divides `n · [E(F) : E₀(F)]`. In particular, if `W(F)[n]` is all of the `n²` torsion
points, `n` divides that index. This is the step of the criterion of Néron, Ogg and Shafarevich
(Silverman AEC VII.7.1) that turns unramified torsion of unbounded order into good reduction, the
index being bounded independently of `n` over unramified extensions.

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
* `natCard_nonsingularReduction_inf_torsionBy_dvd`: at bad reduction, the number of points of
  `W(F)[n]` with nonsingular reduction divides `n`, for `n ∉ u`.
* `natCard_torsionBy_dvd_mul_index_nonsingularReduction`: at bad reduction, `#W(F)[n]` divides
  `n · [E(F) : E₀(F)]` for `n ∉ u`.
* `dvd_index_nonsingularReduction`: at bad reduction, if `W(F)[n]` has `n²` points for some
  `n ∉ u`, then `n` divides `[E(F) : E₀(F)]`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.6.1, VII.3.1 and VII.7.1.
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

section GoodReduction

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

end GoodReduction

section BadReduction

variable [IsIntegral (u.valuation F).valuationSubring W] [W.IsElliptic] [DecidableEq F]

/-- **At bad reduction, the `n`-torsion with nonsingular reduction is small** (Silverman AEC
VII.7.1): if the integral model of `W` at `u` has singular reduction, then for `n ∉ u` the number of
points of `W(F)[n]` with nonsingular reduction divides `n`. In particular `E₀(F) ∩ W(F)[n]` is
never all of `(ℤ / n)²` for `n > 1`. -/
theorem natCard_nonsingularReduction_inf_torsionBy_dvd (hΔ : u.valuation F W.Δ < 1) {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) :
    Nat.card ↥(W.nonsingularReduction (u.valuation F) ⊓ AddSubgroup.torsionBy W.Point n) ∣ n := by
  classical
  -- the reduced curve is singular, and `n` is invertible over the residue field
  have hΔk : ((integralModel (u.valuation F).valuationSubring W).map
      (residue (u.valuation F).valuationSubring)).Δ = 0 := by
    rw [map_Δ, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    rwa [← integralModel_Δ_eq (u.valuation F).valuationSubring W,
      ValuationSubring.algebraMap_apply] at hΔ
  have hnk : (n : ResidueField (u.valuation F).valuationSubring) ≠ 0 := by
    rw [← map_natCast (residue _), Ne, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    push_cast
    rwa [← map_natCast (algebraMap A F), HeightOneSpectrum.valuation_lt_one_iff_mem]
  -- reduction is injective on the `n`-torsion with nonsingular reduction
  let ρ := (W.nonsingularReductionHom (u.valuation F)).comp
    (AddSubgroup.inclusion (inf_le_left (b := AddSubgroup.torsionBy W.Point n)))
  have hρ : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun P hP ↦ Subtype.ext <| by_contra fun hP0 ↦ ?_
    rcases (nonsingularReductionHom_eq_zero_iff _ _).1 hP with h0 | hx
    · exact hP0 h0
    · exact hx.not_ge (valuation_xCoord_le_one_and_valuation_yCoord_le_one_of_nsmul_eq_zero u hn
        hP0 (AddSubgroup.torsionBy.nsmul_iff.1 P.2.2)).1
  -- and its image consists of `n`-torsion points of the singular reduced curve
  have hρn (P) : ρ P ∈ AddSubgroup.torsionBy _ n := by
    have hnP : n • P = 0 := Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 P.2.2)
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, hnP, _root_.map_zero]
  exact (AddSubgroup.card_dvd_of_injective (ρ.codRestrict _ hρn)
    fun P Q h ↦ hρ (congrArg Subtype.val h)).trans (natCard_torsionBy_dvd_of_Δ_eq_zero hΔk hnk)

/-- **At bad reduction, torsion forces a large index of `E₀`** (Silverman AEC VII.7.1): if the
integral model of `W` at `u` has singular reduction, then for `n ∉ u` the number of points of
`W(F)[n]` divides `n · [E(F) : E₀(F)]`, where `E₀(F)` is the subgroup of points with nonsingular
reduction. -/
theorem natCard_torsionBy_dvd_mul_index_nonsingularReduction (hΔ : u.valuation F W.Δ < 1) {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) :
    Nat.card (AddSubgroup.torsionBy W.Point n) ∣
      n * (W.nonsingularReduction (u.valuation F)).index := by
  rw [← (W.nonsingularReduction (u.valuation F)).relIndex_mul_card
    (AddSubgroup.torsionBy W.Point n), mul_comm n]
  exact mul_dvd_mul (AddSubgroup.relIndex_dvd_index_of_normal _ _)
    (natCard_nonsingularReduction_inf_torsionBy_dvd u hΔ hn)

/-- **At bad reduction, full `n`-torsion forces `n` to divide the index of `E₀`** (Silverman AEC
VII.7.1): if the integral model of `W` at `u` has singular reduction and `W(F)[n]` has `n²` points
for some `n ∉ u`, then `n` divides `[E(F) : E₀(F)]`. In particular, when that index is finite,
`n` is at most the index: full torsion of order prime to `u` beyond the index excludes bad
reduction. -/
theorem dvd_index_nonsingularReduction (hΔ : u.valuation F W.Δ < 1) {n : ℕ}
    (hn : (n : A) ∉ u.asIdeal) (h : Nat.card (AddSubgroup.torsionBy W.Point n) = n ^ 2) :
    n ∣ (W.nonsingularReduction (u.valuation F)).index := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have := natCard_torsionBy_dvd_mul_index_nonsingularReduction u hΔ hn
  rw [h, sq] at this
  exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hn0)).1 this

end BadReduction

end WeierstrassCurve.Affine.Point

end
