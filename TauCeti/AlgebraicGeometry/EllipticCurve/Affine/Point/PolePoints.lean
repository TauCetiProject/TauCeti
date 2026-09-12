/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.Range
import TauCeti.FieldTheory.FunctionField.AffineModel.Place

/-!
# The points with a pole at a place form a subgroup

Let `W` be an elliptic curve over `F`, let `K` be a field extension of `F` and let `P` be a place
of `K / F`. A point of `W` over `K` either has both coordinates in the valuation ring of `P` or has
a pole of `x` there (`Affine/ValuationIntegrality.lean`). This file shows that the points with a
pole, together with the point at infinity, form a subgroup of `W(K)`. These are the `K`-points
lying in the kernel `E₁(K_P)` of reduction at `P` on the completion `K_P` (Silverman VII.2.2); no
reduction map is constructed here, the subgroup being cut out by the valuation of the
`x`-coordinate alone.

The group law on the points of an affine Weierstrass curve depends definitionally on the chosen
`DecidableEq K`, so that instance is a parameter of every declaration here rather than being fixed
classically: the statements apply to the point operations of whatever instance is in context, in
particular to the function field of a curve with its own.

## Main definitions

* `WeierstrassCurve.Affine.polePoints`: the subgroup of `W(K)` of points whose `x`-coordinate has
  a pole at `P`, together with the point at infinity.

## Main results

* `WeierstrassCurve.Affine.one_lt_valuation_xCoord_add`: a pole of `x` at `P` is preserved by
  addition of points, as long as the sum is not the point at infinity.
* `WeierstrassCurve.Affine.mem_polePoints_iff`: membership in `polePoints`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.2.2.

## Provenance

Built on `WeierstrassCurve.range_formalPointHomAdicCompletion` (`FormalGroup/Point/Range.lean`,
adapted there from Michael Stoll's `EllipticCurves` development) and `TauCeti.Place.center`
(`FieldTheory/FunctionField/AffineModel/Place.lean`).
-/

public section

open IsDedekindDomain WeierstrassCurve

namespace WeierstrassCurve.Affine

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- **A pole of `x` at a place is preserved by addition of points.** If the `x`-coordinates of two
points of `W` over `K` both have a pole at the place `P`, and the points do not cancel, then the
`x`-coordinate of their sum has a pole at `P` too. -/
theorem one_lt_valuation_xCoord_add (P : TauCeti.Place F K) {Q₁ Q₂ : (W⁄K).toAffine.Point}
    (h₁ : 1 < P.valuation Q₁.xCoord) (h₂ : 1 < P.valuation Q₂.xCoord) (h : Q₁ + Q₂ ≠ 0) :
    1 < P.valuation (Q₁ + Q₂).xCoord := by
  classical
  -- The place is the adic place of the maximal ideal of its own valuation ring.
  set u : HeightOneSpectrum P.integers := P.center (R := P.integers) fun r ↦ r.2
  have hu : u.valuation K = P.valuation := P.valuation_center _
  have hval : ∀ x : K, Valued.v (algebraMap K (u.adicCompletion K) x) = P.valuation x := fun x ↦
    (u.valuedAdicCompletion_eq_valuation' x).trans (by rw [hu])
  -- Constants are integral in the completion, so `W` has a model over its integers.
  have hF : ∀ c : F, algebraMap F (u.adicCompletion K) c ∈ u.adicCompletionIntegers K := fun c ↦ by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      IsScalarTower.algebraMap_apply F K (u.adicCompletion K), hval]
    exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _
  let _ : Algebra F (u.adicCompletionIntegers K) :=
    ((algebraMap F (u.adicCompletion K)).codRestrict _ hF).toAlgebra
  have : IsScalarTower F (u.adicCompletionIntegers K) (u.adicCompletion K) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsLinearTopology (u.adicCompletionIntegers K) (u.adicCompletionIntegers K) :=
    u.isAdic_maximalIdeal_adicCompletionIntegers (K := K) ▸ Ideal.isLinearTopology _
  have : Fact (IsAdic (IsLocalRing.maximalIdeal (u.adicCompletionIntegers K))) :=
    ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := K)⟩
  -- The model over the integers of the completion; its base change back to the completion is `W`
  -- over the completion.
  set C : WeierstrassCurve (u.adicCompletionIntegers K) := W⁄(u.adicCompletionIntegers K)
  have hC : C.baseChange (u.adicCompletion K) = W⁄(u.adicCompletion K) :=
    W.map_baseChange (IsScalarTower.toAlgHom F (u.adicCompletionIntegers K) (u.adicCompletion K))
  have : (C.baseChange (u.adicCompletion K)).IsElliptic := by rw [hC]; infer_instance
  -- Over the completion the points with a pole of `x`, and the point at infinity, are the range of
  -- the formal parametrisation, an additive homomorphism, so they are closed under addition. This
  -- is stated for the curve `Range.lean` speaks about and carried to `W` along `hC` below.
  have key : ∀ V : WeierstrassCurve (u.adicCompletion K), V = C.baseChange (u.adicCompletion K) →
      ∀ R₁ R₂ : V.toAffine.Point, 1 < Valued.v R₁.xCoord → 1 < Valued.v R₂.xCoord →
        R₁ + R₂ ≠ 0 → 1 < Valued.v (R₁ + R₂).xCoord := by
    rintro V rfl R₁ R₂ hR₁ hR₂ hR
    have hmem : ∀ R : (C.baseChange (u.adicCompletion K)).toAffine.Point, 1 < Valued.v R.xCoord →
        R ∈ (C.formalPointHomAdicCompletion u).range := fun R hR ↦ by
      rw [← SetLike.mem_coe, AddMonoidHom.coe_range, range_formalPointHomAdicCompletion]
      exact Or.inr hR
    have hsum := (C.formalPointHomAdicCompletion u).range.add_mem (hmem R₁ hR₁) (hmem R₂ hR₂)
    rw [← SetLike.mem_coe, AddMonoidHom.coe_range, range_formalPointHomAdicCompletion,
      Set.mem_ofPred_eq] at hsum
    exact hsum.resolve_left hR
  -- Points transport to the completion, where the valuation of `x` is that of the place.
  let ι : K →ₐ[F] u.adicCompletion K := IsScalarTower.toAlgHom F K _
  have hx : ∀ Q : (W⁄K).toAffine.Point, Valued.v (Point.map ι Q).xCoord = P.valuation Q.xCoord :=
    fun Q ↦ by rw [Point.xCoord_map, IsScalarTower.coe_toAlgHom', hval]
  have := key _ hC.symm (Point.map ι Q₁) (Point.map ι Q₂) (by rwa [hx]) (by rwa [hx])
    (by rw [← map_add]; exact fun h0 ↦ h ((Point.map_injective ι) (h0.trans (map_zero _).symm)))
  rwa [← map_add, hx] at this

/-- **The points with a pole at `P`**, together with the point at infinity, as a subgroup of
`W(K)`: the `K`-points lying in the kernel `E₁(K_P)` of reduction at `P` on the completion. -/
def polePoints (P : TauCeti.Place F K) : AddSubgroup (W⁄K).toAffine.Point where
  carrier := {Q | Q = 0 ∨ 1 < P.valuation Q.xCoord}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro Q₁ Q₂ (rfl | h₁) (rfl | h₂)
    · exact Or.inl (zero_add 0)
    · rw [zero_add]; exact Or.inr h₂
    · rw [add_zero]; exact Or.inr h₁
    · rcases eq_or_ne (Q₁ + Q₂) 0 with h | h
      · exact Or.inl h
      · exact Or.inr (one_lt_valuation_xCoord_add W P h₁ h₂ h)
  neg_mem' := by
    rintro Q (rfl | h)
    · exact Or.inl neg_zero
    · exact Or.inr (by rwa [Point.xCoord_neg])

/-- A point lies in `polePoints` when it is the point at infinity or its `x`-coordinate has a pole
at `P`. -/
@[simp]
theorem mem_polePoints_iff (P : TauCeti.Place F K) (Q : (W⁄K).toAffine.Point) :
    Q ∈ polePoints W P ↔ Q = 0 ∨ 1 < P.valuation Q.xCoord :=
  Iff.rfl

end WeierstrassCurve.Affine

end
