/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.DivisorPullback
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified

/-!
# The pullback of a point divisor along a separable isogeny

Over a separably closed field a separable isogeny `φ : W₁ → W₂` is unramified and splits every
place completely, so every place over the place of a point `T` of `W₂` is the place of a point of
`W₁`, necessarily one over `T`. The pullback of the point divisor `(T)` is therefore the fibre
`∑_{φ P = T} (P)`, with every multiplicity `1`, and the fibre over `T` is the translate of the
kernel by any point over `T`. This is the divisor computation behind the adjointness of the dual
isogeny for the Weil pairing.

## Main results

* `TauCeti.Isogeny.divisorPullback_ofPoint_eq_sum`: `φ^* (T) = ∑_{φ P = T} (P)`.
* `TauCeti.Isogeny.divisorPullback_ofPoint_sub_eq_sum`:
  `φ^* ((T) - (O)) = ∑_{φ K = O} ((P₀ + K) - (K))` for any `P₀` over `T`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 and III.4.10.
-/

public section

namespace TauCeti.Isogeny

open AlgebraicGeometry WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [IsSepClosed F]
  {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

local instance : IsIntegrallyClosed W₁.CoordinateRing := W₁.isIntegrallyClosed_coordinateRing
local instance : IsIntegrallyClosed W₂.CoordinateRing := W₂.isIntegrallyClosed_coordinateRing
local instance : IsDedekindDomain W₂.CoordinateRing :=
  W₂.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The pullback of a point along a separable isogeny is its fibre**: over a separably closed
field, `φ^* (T) = ∑_{φ P = T} (P)`. The isogeny is unramified, and every place over the place of
`T` is the place of a point, since `φ` splits it completely. -/
theorem divisorPullback_ofPoint_eq_sum (T : W₂.Point) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    φ.divisorPullback (fun _ ↦ rfl) (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₂ T).1) =
      ∑ P ∈ (φ.finite_setOf_toPointHom_eq T).toFinset,
        WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₁ P).1 := by
  classical
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback fun _ ↦ rfl
  have := φ.finiteDimensional_functionField fun _ ↦ rfl
  have hinj : Function.Injective fun P : W₁.Point ↦ (pointEquivDegreeOnePlace W₁ P).1 :=
    Subtype.val_injective.comp (pointEquivDegreeOnePlace W₁).injective
  -- a place lies over the place of `T` exactly when it is the place of a point over `T`
  have hover (v : Place F W₁.FunctionField) :
      v.restrict F W₂.FunctionField = (pointEquivDegreeOnePlace W₂ T).1 ↔
        ∃ P, φ.toPointHom P = T ∧ (pointEquivDegreeOnePlace W₁ P).1 = v := by
    refine ⟨fun hv ↦ ?_, ?_⟩
    · have hdeg : v.degree = 1 := by
        rw [Place.degree_eq_degree_restrict_mul_relativeDegree F W₂.FunctionField v, hv,
          (pointEquivDegreeOnePlace W₂ T).2, one_mul]
        exact (φ.isSplitCompletely (fun _ ↦ rfl) _).relativeDegree_eq_one hv
      refine ⟨(pointEquivDegreeOnePlace W₁).symm ⟨v, hdeg⟩, ?_, by simp⟩
      refine (pointEquivDegreeOnePlace W₂).injective (Subtype.ext ?_)
      rw [φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl), Equiv.apply_symm_apply, hv]
    · rintro ⟨P, rfl, rfl⟩
      exact (φ.coe_pointEquivDegreeOnePlace_toPointHom (fun _ ↦ rfl) P).symm
  have hfin := φ.finite_setOf_toPointHom_eq T
  -- the fibre sum is the finite-set divisor of the places of the fibre
  have hsum : ∑ P ∈ hfin.toFinset, WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₁ P).1 =
      WeilDivisor.ofFinset (hfin.toFinset.map ⟨_, hinj⟩) := by
    rw [WeilDivisor.ofFinset_eq_sum, Finset.sum_map, Function.Embedding.coeFn_mk]
  rw [hsum]
  ext v
  rw [coeff_divisorPullback, φ.ramificationIdx_eq_one (fun _ ↦ rfl), Nat.cast_one, one_mul,
    WeilDivisor.coeff_ofFinset]
  -- the pullback has coefficient `1` at the places over the place of `T`, and `0` elsewhere
  split_ifs with hmem
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_map.mp hmem
    rw [Function.Embedding.coeFn_mk, (hover _).mpr ⟨P, (Set.Finite.mem_toFinset hfin).mp hP, rfl⟩,
      WeilDivisor.coeff_ofPoint_self]
  · refine WeilDivisor.coeff_ofPoint_of_ne fun hv ↦ hmem ?_
    obtain ⟨P, hP, rfl⟩ := (hover v).mp hv
    exact Finset.mem_map_of_mem _ ((Set.Finite.mem_toFinset hfin).mpr hP)

/-- **`φ^* ((T) - (O))` is the translate of the kernel minus the kernel**: for any `P₀` over `T`, it
is `∑_{φ K = O} ((P₀ + K) - (K))`, over a separably closed field. -/
theorem divisorPullback_ofPoint_sub_eq_sum {T : W₂.Point} {P₀ : W₁.Point}
    (hP₀ : φ.toPointHom P₀ = T) :
    letI := φ.fieldPullback.toRingHom.toAlgebra
    φ.divisorPullback (fun _ ↦ rfl) (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₂ T).1 -
        WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₂ 0).1) =
      ∑ K ∈ (φ.finite_setOf_toPointHom_eq 0).toFinset,
        (WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₁ (P₀ + K)).1 -
          WeilDivisor.ofPoint (pointEquivDegreeOnePlace W₁ K).1) := by
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  rw [map_sub, divisorPullback_ofPoint_eq_sum, divisorPullback_ofPoint_eq_sum,
    Finset.sum_sub_distrib]
  congr 1
  -- the fibre over `T` is the translate by `P₀` of the fibre over `O`
  refine Finset.sum_nbij' (· - P₀) (P₀ + ·) (fun P hP ↦ ?_) (fun K hK ↦ ?_)
    (fun P _ ↦ add_sub_cancel P₀ P) (fun K _ ↦ add_sub_cancel_left P₀ K)
    (fun P _ ↦ by rw [add_sub_cancel])
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP ⊢
    rw [map_sub, hP, hP₀, sub_self]
  · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hK ⊢
    rw [map_add, hK, hP₀, add_zero]

end TauCeti.Isogeny

end
