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
* `TauCeti.NumericalType.ker_vecMulLinear_intersection_eq_span`: the kernel of the intersection
  matrix is spanned over `ℤ` by the primitive multiplicity vector `i ↦ mᵢ / gcd(m)`.
* `TauCeti.NumericalType.ker_vecMulLinear_intersection_eq_span_of_gcd_eq_one`: when the
  multiplicities are coprime (`gcd = 1`), the kernel is spanned over `ℤ` by `i ↦ mᵢ`.
* `TauCeti.NumericalType.finrank_ker_vecMulLinear_intersection`: the kernel of the intersection
  matrix has rank one over `ℤ`.
* `TauCeti.NumericalType.finrank_pic`: the Picard group has rank one over `ℤ`.

The kernel argument is the weighted maximum principle in
`Matrix.eq_smul_of_mulVec_eq_zero`. The rank-one conclusion is
[Stacks, Tag 0C7I](https://stacks.math.columbia.edu/tag/0C7I).
-/

public section

namespace TauCeti

open Finset Matrix

/-- For nonzero natural numbers `m : ι → ℕ` on a finite nonempty index type, the cross-product
equations `m j * v i = m i * v j` hold for all `i, j` if and only if `v` lies in the `ℤ`-span of
the primitive vector `i ↦ m i / gcd(m)`. -/
theorem forall_nat_mul_eq_iff_mem_span_div_gcd {ι : Type*} [Fintype ι] [Nonempty ι]
    (m : ι → ℕ) (hm : ∀ i, m i ≠ 0) (v : ι → ℤ) :
    (∀ i j, (m j : ℤ) * v i = (m i : ℤ) * v j) ↔
      v ∈ Submodule.span ℤ {fun i ↦ ((m i / Finset.univ.gcd m : ℕ) : ℤ)} := by
  set d : ℕ := Finset.univ.gcd m
  have hd_dvd (i : ι) : d ∣ m i := Finset.gcd_dvd (Finset.mem_univ i)
  have hd_ne : d ≠ 0 := by
    let i₀ : ι := Classical.choice inferInstance
    exact ne_zero_of_dvd_ne_zero (hm i₀) (hd_dvd i₀)
  have hd_ne_int : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd_ne
  have hmul_div (i : ι) : (d : ℤ) * ((m i / d : ℕ) : ℤ) = (m i : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' (hd_dvd i)
  constructor
  · intro hv
    set dℤ : ℤ := Finset.univ.gcd (fun j : ι ↦ (m j : ℤ))
    have hdℤ_dvd : dℤ ∣ (d : ℤ) := Int.natAbs_dvd_natAbs.mp <| by
      rw [Int.natAbs_natCast]
      exact Finset.dvd_gcd fun j _ ↦ by
        simpa only [Int.natAbs_natCast] using
          Int.natAbs_dvd_natAbs.mpr (Finset.gcd_dvd (f := fun k ↦ (m k : ℤ)) (Finset.mem_univ j))
    obtain ⟨q, hq⟩ := hdℤ_dvd
    obtain ⟨g, hg⟩ := Finset.gcd_eq_sum_mul Finset.univ (fun j : ι ↦ (m j : ℤ))
    refine Submodule.mem_span_singleton.mpr ⟨∑ j : ι, v j * (g j * q), funext fun i ↦ ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    apply mul_left_cancel₀ hd_ne_int
    calc
      (d : ℤ) * ((∑ j : ι, v j * (g j * q)) * ((m i / d : ℕ) : ℤ))
          = (m i : ℤ) * ∑ j : ι, v j * (g j * q) := by
            rw [mul_comm (∑ j : ι, _), ← mul_assoc, hmul_div i]
      _ = ∑ j : ι, ((m i : ℤ) * v j) * (g j * q) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = ∑ j : ι, ((m j : ℤ) * v i) * (g j * q) := by
            exact Finset.sum_congr rfl fun j _ ↦ by rw [hv i j]
      _ = ((∑ j : ι, (m j : ℤ) * g j) * q) * v i := by
            rw [Finset.sum_mul, Finset.sum_mul]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ = (d : ℤ) * v i := by rw [← hg, ← hq]
  · intro hv i j
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    apply mul_left_cancel₀ hd_ne_int
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (d : ℤ) * ((m j : ℤ) * (c * ((m i / d : ℕ) : ℤ)))
          = (m j : ℤ) * c * ((d : ℤ) * ((m i / d : ℕ) : ℤ)) := by ring
      _ = (m j : ℤ) * c * (m i : ℤ) := by rw [hmul_div i]
      _ = (m i : ℤ) * c * ((d : ℤ) * ((m j / d : ℕ) : ℤ)) := by
            rw [hmul_div j]; ring
      _ = (d : ℤ) * ((m i : ℤ) * (c * ((m j / d : ℕ) : ℤ))) := by ring

namespace NumericalType

universe u

variable (T : NumericalType.{u})

private def intersectionRat : Matrix T.Component T.Component ℚ :=
  T.intersection.map (Int.castRingHom ℚ)

private lemma multiplicityRat_pos (i : T.Component) :
    0 < ((T.multiplicity i : ℤ) : ℚ) := by
  exact Int.cast_pos.mpr (Int.natCast_pos.mpr (T.multiplicity i).pos)

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
  rw [← T.intersection_isSymm.eq, Matrix.mulVec_transpose, hv]

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
  | tail _ hbc ih => exact ih.tail (mapEdge hbc)

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
lemma ker_vecMulLinear_intersection_apply_injective (i : T.Component) :
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

/-- The kernel of `T.intersection.vecMulLinear` is spanned over `ℤ` by the primitive multiplicity
vector `i ↦ mᵢ / gcd(m)`. -/
theorem ker_vecMulLinear_intersection_eq_span :
    LinearMap.ker T.intersection.vecMulLinear =
      Submodule.span ℤ {fun i ↦
        (((T.multiplicity i : ℕ) /
          Finset.univ.gcd (fun j : T.Component ↦ (T.multiplicity j : ℕ)) : ℕ) : ℤ)} := by
  ext v
  rw [LinearMap.mem_ker, Matrix.vecMulLinear_apply, T.vecMul_intersection_eq_zero_iff]
  exact forall_nat_mul_eq_iff_mem_span_div_gcd (fun i ↦ (T.multiplicity i : ℕ))
    (fun i ↦ (T.multiplicity i).ne_zero) v

/-- When the multiplicities of `T` are coprime (`gcd = 1`), the kernel of
`T.intersection.vecMulLinear` is spanned over `ℤ` by the multiplicity vector `i ↦ mᵢ`. -/
theorem ker_vecMulLinear_intersection_eq_span_of_gcd_eq_one
    (hgcd : Finset.univ.gcd (fun i : T.Component ↦ (T.multiplicity i : ℕ)) = 1) :
    LinearMap.ker T.intersection.vecMulLinear =
      Submodule.span ℤ {fun i ↦ (T.multiplicity i : ℤ)} := by
  simpa only [hgcd, Nat.div_one] using T.ker_vecMulLinear_intersection_eq_span

/-- The kernel of the intersection matrix of a numerical type has rank one over `ℤ`. -/
theorem finrank_ker_vecMulLinear_intersection :
    Module.finrank ℤ (LinearMap.ker T.intersection.vecMulLinear) = 1 := by
  have hle : Module.finrank ℤ (LinearMap.ker T.intersection.vecMulLinear) ≤ 1 := by
    simpa using LinearMap.finrank_le_finrank_of_injective
      (T.ker_vecMulLinear_intersection_apply_injective (Classical.choice inferInstance))
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
    rw [← T.weightScaling_comp_weightedIntersection, LinearMap.ker_comp_of_ker_eq_bot _
      (LinearMap.ker_eq_bot_of_injective T.weightScaling_injective)]
  have hrange : Module.finrank ℤ T.principalDivisors + 1 = Fintype.card T.Component := by
    have h := (LinearMap.ker T.weightedIntersection.vecMulLinear).finrank_quotient_add_finrank
    rw [LinearEquiv.finrank_eq T.weightedIntersection.vecMulLinear.quotKerEquivRange,
      hker_weighted, T.finrank_ker_vecMulLinear_intersection, Module.finrank_pi] at h
    have hp : T.principalDivisors = LinearMap.range T.weightedIntersection.vecMulLinear := by
      ext d
      simp only [T.mem_principalDivisors_iff, LinearMap.mem_range, Matrix.vecMulLinear_apply]
    rwa [hp]
  have hpic := T.principalDivisors.finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hpic
  exact (by omega :
    Module.finrank ℤ ((T.Component → ℤ) ⧸ T.principalDivisors) = 1)

end NumericalType

end TauCeti
