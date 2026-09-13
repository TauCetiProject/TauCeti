/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Picard.Basic

/-!
# Rank of the Picard group of a numerical type

The Picard group of a numerical type is a finitely generated abelian group of rank one. The key
input is that the kernel of the intersection matrix has rank one: its positive-entry graph is
connected and its strictly positive multiplicity vector lies in the kernel, so the weighted
maximum principle shows that every rational kernel vector is proportional to that vector.

The weighted intersection matrix defining `Pic(T)` differs from the intersection matrix by the
injective rescaling of each coordinate by its positive weight. Consequently it has the same
kernel rank. Rank-nullity then computes the rank of its cokernel.

## Main results

* `TauCeti.NumericalType.vecMul_intersection_eq_zero_iff`: an integral row vector is killed by
  the intersection matrix exactly when its cross-products with the multiplicity vector agree.
* `TauCeti.NumericalType.finrank_ker_vecMulLinear_intersection`: the kernel of the intersection
  matrix has rank one over `ℤ`.
* `TauCeti.NumericalType.finrank_pic`: the Picard group has rank one over `ℤ`.

The kernel argument is the weighted maximum principle in
`Matrix.eq_smul_of_mulVec_eq_zero`. The rank-one conclusion is
[Stacks, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H).
-/

public section

namespace TauCeti

open Finset Matrix

namespace NumericalType

universe u

variable (T : NumericalType.{u})

private def intersectionRat : Matrix T.Component T.Component ℚ :=
  T.intersection.map (Int.castRingHom ℚ)

private lemma multiplicityRat_pos (i : T.Component) :
    0 < ((T.multiplicity i : ℤ) : ℚ) := by
  exact Int.cast_pos.mpr (Int.natCast_pos.mpr (T.multiplicity i).pos)

private lemma intersection_mulVec_multiplicity :
    T.intersection.mulVec (fun i ↦ (T.multiplicity i : ℤ)) = 0 := by
  funext i
  simpa [Matrix.mulVec, dotProduct, mul_comm] using T.fiber_relation i

private lemma intersectionRat_mulVec_multiplicityRat :
    T.intersectionRat.mulVec (fun i ↦ ((T.multiplicity i : ℤ) : ℚ)) = 0 := by
  funext i
  calc
    T.intersectionRat.mulVec (fun j ↦ ((T.multiplicity j : ℤ) : ℚ)) i =
        ((T.intersection.mulVec (fun j ↦ (T.multiplicity j : ℤ)) i : ℤ) : ℚ) := by
      simpa [intersectionRat, Function.comp_def] using
        (RingHom.map_mulVec (Int.castRingHom ℚ) T.intersection
          (fun j ↦ (T.multiplicity j : ℤ)) i).symm
    _ = 0 := by rw [congrFun T.intersection_mulVec_multiplicity i]; simp

private lemma intersection_mulVec_eq_zero_of_vecMul_eq_zero {v : T.Component → ℤ}
    (hv : v ᵥ* T.intersection = 0) : T.intersection.mulVec v = 0 := by
  funext i
  calc
    T.intersection.mulVec v i = ∑ j, v j * T.intersection j i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [T.intersection_comm, mul_comm]
    _ = (v ᵥ* T.intersection) i := rfl
    _ = 0 := congrFun hv i

private lemma intersectionRat_mulVec_eq_zero_of_vecMul_eq_zero {v : T.Component → ℤ}
    (hv : v ᵥ* T.intersection = 0) :
    T.intersectionRat.mulVec (fun i ↦ (v i : ℚ)) = 0 := by
  have hv' := T.intersection_mulVec_eq_zero_of_vecMul_eq_zero hv
  funext i
  calc
    T.intersectionRat.mulVec (fun j ↦ (v j : ℚ)) i =
        ((T.intersection.mulVec v i : ℤ) : ℚ) := by
      simpa [intersectionRat, Function.comp_def] using
        (RingHom.map_mulVec (Int.castRingHom ℚ) T.intersection v i).symm
    _ = 0 := by rw [congrFun hv' i]; simp

private lemma intersectionRat_offDiagonal_nonneg (i j : T.Component) (hij : i ≠ j) :
    0 ≤ T.intersectionRat i j := by
  simp only [intersectionRat, Matrix.map_apply]
  exact Int.cast_nonneg (T.offDiagonal_nonneg i j hij)

private lemma intersectionRat_connected (i j : T.Component) :
    Relation.ReflTransGen
      (fun i j ↦ i ≠ j ∧ 0 < T.intersectionRat i j) i j := by
  have mapEdge {a b : T.Component} (hab : T.Adj a b) :
      a ≠ b ∧ 0 < T.intersectionRat a b := by
    rw [T.adj_iff] at hab
    refine ⟨hab.1, ?_⟩
    simp only [intersectionRat, Matrix.map_apply]
    exact Int.cast_pos.mpr hab.2
  induction T.reflTransGen_adj i j with
  | refl => exact .refl
  | tail hab hbc ih => exact ih.tail (mapEdge hbc)

/-- An integral row vector is killed by the intersection matrix of a numerical type exactly when
its cross-products with the multiplicity vector agree. Thus, over the fraction field, every
kernel vector is proportional to the multiplicity vector. The cross-product formulation remains
exact over `ℤ` even when the multiplicities have a nontrivial common factor. -/
theorem vecMul_intersection_eq_zero_iff (v : T.Component → ℤ) :
    v ᵥ* T.intersection = 0 ↔
      ∀ i j, (T.multiplicity j : ℤ) * v i = (T.multiplicity i : ℤ) * v j := by
  constructor
  · intro hv
    obtain ⟨c, hc⟩ := Matrix.eq_smul_of_mulVec_eq_zero T.intersectionRat
      T.intersectionRat_offDiagonal_nonneg T.intersectionRat_connected
      (fun i ↦ ((T.multiplicity i : ℤ) : ℚ)) (fun i ↦ (v i : ℚ)) T.multiplicityRat_pos
      T.intersectionRat_mulVec_multiplicityRat
      (T.intersectionRat_mulVec_eq_zero_of_vecMul_eq_zero hv)
    intro i j
    have hi := congrFun hc i
    have hj := congrFun hc j
    simp only [Pi.smul_apply, smul_eq_mul] at hi hj
    have hq : ((T.multiplicity j : ℤ) : ℚ) * (v i : ℚ) =
        ((T.multiplicity i : ℤ) : ℚ) * (v j : ℚ) := by
      rw [hi, hj]
      ring
    exact_mod_cast hq
  · intro hv
    funext j
    have hmul : (T.multiplicity j : ℤ) * (v ᵥ* T.intersection) j = 0 := by
      calc
        (T.multiplicity j : ℤ) * (v ᵥ* T.intersection) j =
            ∑ i, ((T.multiplicity j : ℤ) * v i) * T.intersection i j := by
              simp [Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
        _ = ∑ i, ((T.multiplicity i : ℤ) * v j) * T.intersection j i := by
              apply Finset.sum_congr rfl
              intro i _
              rw [hv i j, T.intersection_comm]
        _ = v j * ∑ i, (T.multiplicity i : ℤ) * T.intersection j i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ = 0 := by rw [T.fiber_relation j, mul_zero]
    exact (mul_eq_zero.mp hmul).resolve_left
      (Int.natCast_ne_zero.mpr (T.multiplicity j).ne_zero)

/-- Evaluation at any component is injective on the kernel of the intersection matrix. -/
lemma injective_ker_vecMulLinear_intersection_apply (i : T.Component) :
    Function.Injective
      ((LinearMap.proj i).domRestrict (LinearMap.ker T.intersection.vecMulLinear)) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  funext j
  have hker : (x - y : T.Component → ℤ) ᵥ* T.intersection = 0 := by
    rw [← Matrix.vecMulLinear_apply, ← LinearMap.mem_ker]
    exact sub_mem x.property y.property
  have hcross := (T.vecMul_intersection_eq_zero_iff (x - y)).mp hker i j
  have hi : (x - y : T.Component → ℤ) i = 0 := sub_eq_zero.mpr hxy
  rw [hi, mul_zero] at hcross
  exact (mul_eq_zero.mp hcross.symm).resolve_left
    (Int.natCast_ne_zero.mpr (T.multiplicity i).ne_zero)

/-- The kernel of the intersection matrix of a numerical type has rank one over `ℤ`. -/
theorem finrank_ker_vecMulLinear_intersection :
    Module.finrank ℤ (LinearMap.ker T.intersection.vecMulLinear) = 1 := by
  have hle : Module.finrank ℤ (LinearMap.ker T.intersection.vecMulLinear) ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective
      (T.injective_ker_vecMulLinear_intersection_apply (Classical.choice inferInstance))
  have hm_mem : (fun i ↦ (T.multiplicity i : ℤ)) ∈
      LinearMap.ker T.intersection.vecMulLinear := by
    rw [LinearMap.mem_ker, Matrix.vecMulLinear_apply]
    funext j
    simpa [Matrix.vecMul, dotProduct, T.intersection_comm, mul_comm] using T.fiber_relation j
  have hm_ne : (⟨_, hm_mem⟩ : LinearMap.ker T.intersection.vecMulLinear) ≠ 0 := by
    intro h
    have := congrFun (congrArg Subtype.val h) (Classical.choice inferInstance)
    exact (Int.natCast_ne_zero.mpr (T.multiplicity _).ne_zero) this
  have hpos : 0 < Module.finrank ℤ (LinearMap.ker T.intersection.vecMulLinear) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hm_ne⟩
  omega

/-- The Picard group of a numerical type has rank one over `ℤ`. -/
theorem finrank_pic : Module.finrank ℤ T.Pic = 1 := by
  have hker_weighted : LinearMap.ker T.weightedIntersection.vecMulLinear =
      LinearMap.ker T.intersection.vecMulLinear := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have hcomp := LinearMap.congr_fun T.weightScaling_comp_weightedIntersection x
    rw [LinearMap.comp_apply] at hcomp
    constructor
    · intro hx
      simpa [hx] using hcomp.symm
    · intro hx
      apply T.weightScaling_injective
      simpa [hx] using hcomp
  have hrange : Module.finrank ℤ T.principalDivisors + 1 = Fintype.card T.Component := by
    have h := (LinearMap.ker T.weightedIntersection.vecMulLinear).finrank_quotient_add_finrank
    rw [LinearEquiv.finrank_eq T.weightedIntersection.vecMulLinear.quotKerEquivRange,
      hker_weighted, T.finrank_ker_vecMulLinear_intersection, Module.finrank_pi] at h
    have hp : T.principalDivisors = LinearMap.range T.weightedIntersection.vecMulLinear := by
      ext d
      rw [T.mem_principalDivisors_iff, LinearMap.mem_range]
      rfl
    rwa [hp]
  have hpic := T.principalDivisors.finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hpic
  exact (by omega :
    Module.finrank ℤ ((T.Component → ℤ) ⧸ T.principalDivisors) = 1)

end NumericalType

end TauCeti
