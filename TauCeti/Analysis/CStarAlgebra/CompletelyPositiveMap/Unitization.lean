/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Unitization
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Unitization of completely positive contractions

A complex-linear map `φ : A → B` between possibly nonunital C⋆-algebras extends to the
unitizations `A⁺¹ → B⁺¹` by `λ + a ↦ t λ + φ a` for any scalar `t`. If `φ` is `n`-positive and
`‖φ p‖ ≤ t` for every positive contraction `p`, then the extension is `n`-positive. In
particular the unital extension `λ + a ↦ λ + φ a` of a completely positive contraction is a
unital completely positive map (Blackadar II.6.9.5).

The proof compresses a positive matrix `[λᵢⱼ + aᵢⱼ]` over `A⁺¹` by an increasing approximate unit
`e` of `A`. The compression `[e aᵢⱼ e + λᵢⱼ e²]` lies in `M_n(A)` and is positive, so its image
`[φ(e aᵢⱼ e) + λᵢⱼ φ(e²)]` is positive. Adding the positive matrix `[λᵢⱼ (t - φ(e²))]` gives
`[φ(e aᵢⱼ e) + t λᵢⱼ]`, which tends to `[φ(aᵢⱼ) + t λᵢⱼ]`.

Applied with `n = 2`, the unital Kadison–Schwarz bound for the extension shows that a `2`-positive
map with `‖φ p‖ ≤ t` on positive contractions satisfies `‖φ a‖ ≤ t ‖a‖`. Hence the norm of a
continuous `2`-positive map is the limit of `‖φ e‖` along any increasing approximate unit `e`
(Blackadar II.6.9.5), the nonunital form of `‖φ‖ = ‖φ 1‖`.

## Main declarations

* `TauCeti.IsNPositive.unitizationLinearMap`: the extension `Unitization.linearMap t φ`,
  `λ + a ↦ t λ + φ a`, of an `n`-positive map that is bounded by `t` on positive contractions is
  `n`-positive.
* `TauCeti.IsNPositive.norm_apply_le_of_forall_nonneg`: a `2`-positive map bounded by `t` on
  positive contractions is bounded by `t`.
* `TauCeti.IsNPositive.tendsto_norm_nhds_opNorm`: for a continuous `2`-positive map `ψ`,
  `‖ψ e‖ → ‖ψ‖` along an increasing approximate unit, with the class version
  `CompletelyPositiveMapClass.tendsto_norm_nhds_opNorm_ofClass`.
* `CompletelyPositiveMap.unitization`: the unital completely positive extension `A⁺¹ →CP B⁺¹` of
  a completely positive contraction.

## References

* B. Blackadar, *Operator Algebras*, II.6.9.5.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The compression `[e aᵢⱼ e + λᵢⱼ e²]` of a positive matrix `[λᵢⱼ + aᵢⱼ]` over `A⁺¹` by a
self-adjoint `e ∈ A` is a positive matrix over `A`. -/
private theorem compress_nonneg {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) A⁺¹} (hM : 0 ≤ M)
    {e : A} (he : star e = e) : 0 ≤ CStarMatrix.ofMatrix
      (Matrix.of fun i j => e * (M i j).snd * e + (M i j).fst • (e * e)) := by
  refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun z => ?_
  have h := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hM fun i => ((e * z i : A) : A⁺¹)
  rw [← Unitization.inr_nonneg_iff ℂ]
  convert h using 1
  simp only [← Unitization.inrNonUnitalStarAlgHom_apply ℂ, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ext <;> simp [he, mul_assoc, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, add_comm]

/-- For a positive matrix `[λᵢⱼ + aᵢⱼ]` over `A⁺¹` and a positive `c`, the quadratic form of
`[λᵢⱼ c]` is positive. -/
private theorem sum_fst_smul_nonneg {n : ℕ} {M : CStarMatrix (Fin n) (Fin n) A⁺¹} (hM : 0 ≤ M)
    {c : B⁺¹} (hc : 0 ≤ c) (w : Fin n → B⁺¹) :
    0 ≤ ∑ i, ∑ j, star (w i) * ((M i j).fst • c) * w j := by
  obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
  have hfst (i j : Fin n) :
      ((star R * R) i j).fst = ∑ k, star (R k i).fst * (R k j).fst := by
    rw [CStarMatrix.mul_apply, ← Unitization.fstHom_apply ℂ, map_sum]
    simp [CStarMatrix.star_apply]
  calc (0 : B⁺¹)
      ≤ ∑ k, star (∑ i, (R k i).fst • w i) * c * ∑ j, (R k j).fst • w j :=
        Finset.sum_nonneg fun k _ => star_left_conjugate_nonneg hc _
    _ = ∑ k, ∑ i, ∑ j, (star (R k i).fst * (R k j).fst) • (star (w i) * c * w j) := by
        simp_rw [star_sum, Finset.sum_mul, Finset.mul_sum]
        simp [star_smul, smul_smul, mul_comm]
    _ = ∑ i, ∑ j, ∑ k, (star (R k i).fst * (R k j).fst) • (star (w i) * c * w j) :=
        Finset.sum_comm_cycle.symm
    _ = ∑ i, ∑ j, star (w i) * (((star R * R) i j).fst • c) * w j := by
        simp [hfst, Finset.sum_smul, Finset.mul_sum, Finset.sum_mul]

/-- The extension `λ + a ↦ t λ + φ a` of an `n`-positive map `φ` with `‖φ p‖ ≤ t` for every
positive contraction `p` is `n`-positive. -/
theorem IsNPositive.unitizationLinearMap {n : ℕ} {φ : A →ₗ[ℂ] B} (hφ : IsNPositive n φ) {t : ℝ}
    (ht : ∀ p, 0 ≤ p → ‖p‖ ≤ 1 → ‖φ p‖ ≤ t) : IsNPositive n (Unitization.linearMap (t : ℂ) φ) := by
  refine isNPositive_iff.mpr fun M hM => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact isNPositive_iff.mp (isNPositive_zero _) M hM
  have hcont : Continuous φ :=
    (map_continuous (hφ.toPositiveLinearMap hn)).congr (hφ.toPositiveLinearMap_apply hn)
  have hl := CStarAlgebra.increasingApproximateUnit A
  refine CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun w => ?_
  have hlim : Tendsto (fun e => ∑ i, ∑ j, star (w i) *
      (Unitization.inl (t * (M i j).fst) + (φ (e * (M i j).snd * e) : B⁺¹)) * w j)
      (CStarAlgebra.approximateUnit A)
      (𝓝 (∑ i, ∑ j, star (w i) * (M.map (Unitization.linearMap (t : ℂ) φ)) i j * w j)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    rw [CStarMatrix.map_apply, Unitization.linearMap_apply]
    refine ((tendsto_const_nhds.add ?_).const_mul _).mul_const _
    exact (Unitization.continuous_inr.comp hcont).tendsto _ |>.comp (hl.tendsto_mul_self _)
  refine ge_of_tendsto hlim ?_
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he0 he1
  have hee0 : 0 ≤ e * e := he0.isSelfAdjoint.mul_self_nonneg
  have hee : 0 ≤ φ (e * e) := hφ.map_nonneg hn hee0
  have hc : 0 ≤ Unitization.inl (t : ℂ) - (φ (e * e) : B⁺¹) := by
    have h1 := IsSelfAdjoint.le_algebraMap_norm_self (φ (e * e) : B⁺¹)
      (Unitization.inr_nonneg_iff ℂ |>.mpr hee).isSelfAdjoint
    have h2 : ‖φ (e * e)‖ ≤ t := ht _ hee0 ((norm_mul_le _ _).trans (by nlinarith [norm_nonneg e]))
    rw [sub_nonneg]
    refine h1.trans ?_
    have hinl : Unitization.inl (t : ℂ) = algebraMap ℝ B⁺¹ t := by
      simp [Unitization.algebraMap_eq_inl_comp]
    rw [Unitization.norm_inr, hinl]
    exact algebraMap_mono _ h2
  have hy := hφ.map_cstarMatrix_nonneg (compress_nonneg hM he0.star_eq)
  have hy' := CStarMatrix.nonneg_iff_forall_sum_nonneg.mp
    (CompletelyPositiveMapClass.map_cstarMatrix_nonneg'
      (Unitization.inrNonUnitalStarAlgHom ℂ B) n _ hy) w
  convert add_nonneg hy' (sum_fst_smul_nonneg hM hc w) using 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_mul, ← mul_add]
  congr 2
  ext <;> simp [map_add, map_smul, Unitization.inl_mul, mul_comm]

/-- A `2`-positive map with `‖φ p‖ ≤ t` for every positive contraction `p` satisfies
`‖φ a‖ ≤ t ‖a‖`. -/
theorem IsNPositive.norm_apply_le_of_forall_nonneg {φ : A →ₗ[ℂ] B} (hφ : IsNPositive 2 φ)
    {t : ℝ} (ht : ∀ p, 0 ≤ p → ‖p‖ ≤ 1 → ‖φ p‖ ≤ t) (a : A) : ‖φ a‖ ≤ t * ‖a‖ := by
  have h0 : 0 ≤ t := by simpa using ht 0 le_rfl (by simp)
  simpa [Unitization.norm_inr, ← Unitization.algebraMap_eq_inl, norm_algebraMap',
    abs_of_nonneg h0] using (hφ.unitizationLinearMap ht).norm_apply_le (a : A⁺¹)

/-- Compressing a positive contraction `p` by a positive contraction `e` gives `e p e ≤ e`. -/
private theorem mul_mul_le_of_nonneg_of_norm_le_one {e p : A} (he0 : 0 ≤ e) (he1 : ‖e‖ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : ‖p‖ ≤ 1) : e * p * e ≤ e := by
  have h := CStarAlgebra.star_left_conjugate_le_norm_smul e p hp0.isSelfAdjoint
  rw [he0.star_eq] at h
  exact h.trans ((smul_le_of_le_one_left he0.isSelfAdjoint.mul_self_nonneg hp1).trans
    (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one he0 he1))

/-- The norm of a continuous `2`-positive map `ψ` is the limit of `‖ψ e‖` along any increasing
approximate unit. -/
theorem IsNPositive.tendsto_norm_nhds_opNorm {ψ : A →L[ℂ] B} (hψ : IsNPositive 2 (ψ : A →ₗ[ℂ] B))
    {l : Filter A} (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e => ‖ψ e‖) l (𝓝 ‖ψ‖) := by
  refine tendsto_order.mpr ⟨fun s hs => ?_, fun s hs => ?_⟩
  · -- some positive contraction `p` has `s < ‖ψ p‖`, and `‖ψ (e p e)‖ ≤ ‖ψ e‖`
    obtain ⟨p, hp0, hp1, hp⟩ : ∃ p, 0 ≤ p ∧ ‖p‖ ≤ 1 ∧ s < ‖ψ p‖ := by
      by_contra! h
      have hs0 : 0 ≤ s := by simpa using h 0 le_rfl (by simp)
      exact hs.not_ge <| ContinuousLinearMap.opNorm_le_bound _ hs0
        (hψ.norm_apply_le_of_forall_nonneg h)
    have hlim : Tendsto (fun e => ‖ψ (e * p * e)‖) l (𝓝 ‖ψ p‖) :=
      ((continuous_norm.comp ψ.continuous).tendsto p).comp (hl.tendsto_mul_self p)
    filter_upwards [hlim.eventually (lt_mem_nhds hp), hl.eventually_nonneg, hl.eventually_norm]
      with e he he0 he1
    refine he.trans_le ?_
    simpa [hψ.toPositiveLinearMap_apply] using
      CStarAlgebra.norm_le_norm_of_le_of_nonneg
        (OrderHomClass.mono (hψ.toPositiveLinearMap two_pos)
          (mul_mul_le_of_nonneg_of_norm_le_one he0 he1 hp0 hp1))
        (_root_.map_nonneg (hψ.toPositiveLinearMap two_pos)
          (he0.isSelfAdjoint.conjugate_nonneg hp0))
  · filter_upwards [hl.eventually_norm] with e he
    exact (ψ.le_opNorm e).trans_lt <|
      (mul_le_of_le_one_right (norm_nonneg _) he).trans_lt hs

end TauCeti

namespace CompletelyPositiveMapClass

open TauCeti

variable {A B F : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [FunLike F A B]
  [LinearMapClass F ℂ A B] [CompletelyPositiveMapClass F A B]

/-- The norm of a completely positive map, made continuous by
`PositiveContinuousLinearMap.ofClass`, is the limit of `‖φ e‖` along any increasing approximate
unit. -/
theorem tendsto_norm_nhds_opNorm_ofClass (φ : F) {l : Filter A}
    (hl : l.IsIncreasingApproximateUnit) :
    Tendsto (fun e => ‖φ e‖) l
      (𝓝 ‖((PositiveContinuousLinearMap.ofClass φ : A →P[ℂ] B) : A →L[ℂ] B)‖) :=
  (isNPositive φ 2).tendsto_norm_nhds_opNorm hl

end CompletelyPositiveMapClass

namespace CompletelyPositiveMap

open TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The unital extension `λ + a ↦ λ + φ a` of a completely positive contraction `φ : A → B` is a
unital completely positive map `A⁺¹ →CP B⁺¹`. -/
noncomputable def unitization (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) : A⁺¹ →CP B⁺¹ :=
  ofIsNPositive (Unitization.linearMap 1 φ.toLinearMap) fun n => by
    simpa using (φ.isNPositive n).unitizationLinearMap (t := 1) fun p _ hp => (hφ p).trans hp

/-- The underlying linear map of `φ.unitization hφ` is `Unitization.linearMap 1 φ`. -/
theorem toLinearMap_unitization (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) :
    (φ.unitization hφ).toLinearMap = Unitization.linearMap 1 φ.toLinearMap := by
  ext x <;> simp [unitization]

theorem unitization_apply (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (x : A⁺¹) :
    φ.unitization hφ x = Unitization.inl x.fst + (φ x.snd : B⁺¹) := by
  simp [unitization, Unitization.linearMap_apply]

@[simp]
theorem unitization_apply_inr (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (a : A) :
    φ.unitization hφ (a : A⁺¹) = (φ a : B⁺¹) := by
  simp [unitization_apply]

/-- The unital extension is the identity on scalars. -/
@[simp]
theorem unitization_apply_inl (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) (c : ℂ) :
    φ.unitization hφ (Unitization.inl c) = Unitization.inl c := by
  simp [unitization_apply]

@[simp]
theorem unitization_apply_one (φ : A →CP B) (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖) :
    φ.unitization hφ 1 = 1 := by
  simp [unitization_apply]

end CompletelyPositiveMap
