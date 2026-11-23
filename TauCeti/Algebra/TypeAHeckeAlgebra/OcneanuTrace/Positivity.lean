/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
public import TauCeti.Analysis.StarAlgebra.GNS.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Positivity
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.WenzlInterval.Basic
import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Zero
import TauCeti.Analysis.RCLike.Basic

/-!
# Positivity of the Ocneanu trace on Wenzl's positive-real parameter set

For a real nonzero parameter `q : ℂˣ` (`IsSelfAdjoint (q : ℂ)`) with `Q = q ^ 2 > 0` and any
projection parameter `η ∈ TauCeti.wenzlPositiveSet Q`, the Ocneanu trace with Markov parameter
`z = q * η - q⁻¹ * (1 - η)` is `⋆`-positive on `TauCeti.InfiniteTypeAHeckeAlgebra ℂ q`
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_star_mul_self_nonneg`, bundled as
`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuPositiveFunctional`).

## References

* H. Wenzl, *Hecke algebras of type A_n and subfactors*, Invent. Math. 92 (1988), 349–383, §3.
* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1.
-/

public section

open scoped ComplexOrder

namespace TauCeti.InfiniteTypeAHeckeAlgebra

private theorem exists_countableAtomicTrace_of_model {q : ℂˣ} {η : ℝ}
    {ι₀ : Type} [LinearOrder ι₀] [Countable ι₀] (pos : ι₀ → Prop) [DecidablePred pos]
    (w : ι₀ → ℝ) (hw_sum : Summable fun a ↦ ‖w a‖) (hw_nonneg : ∀ a, 0 ≤ w a)
    (hw_tsum : (∑' a, w a) = 1)
    (hw_eq : ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n),
      TypeAHeckeAlgebra.countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
          (hw_sum.congr fun _ ↦ (Complex.norm_real _).symm) n x =
        ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
          (TypeAHeckeAlgebra.toInfinite ℂ q n x)) :
    ∃ (ι : Type) (_ : LinearOrder ι) (_ : Countable ι) (pos' : ι → Prop) (_ : DecidablePred pos')
      (p : ι → ℝ) (hp_sum : Summable fun a ↦ ‖(p a : ℂ)‖),
      (∀ a, 0 < p a) ∧ (∑' a, p a = 1) ∧ ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n),
        TypeAHeckeAlgebra.countableAtomicTrace pos' q (fun a ↦ (p a : ℂ)) hp_sum n x =
          ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
            (TypeAHeckeAlgebra.toInfinite ℂ q n x) := by
  have htsum : (∑' a : {a : ι₀ // w a ≠ 0}, w a.val) = 1 := by
    have h0 : Function.support w ⊆ Set.range (Subtype.val : {a : ι₀ // w a ≠ 0} → ι₀) :=
      fun a ha ↦ ⟨⟨a, ha⟩, rfl⟩
    rw [Subtype.val_injective.tsum_eq h0, hw_tsum]
  refine ⟨{a : ι₀ // w a ≠ 0}, inferInstance, inferInstance, fun a ↦ pos a.val, inferInstance,
    fun a ↦ w a.val,
    ((hw_sum.congr fun _ ↦ (Complex.norm_real _).symm).comp_injective Subtype.val_injective),
    fun a ↦ (hw_nonneg a.val).lt_of_ne' a.property, htsum, fun {n} x ↦ ?_⟩
  rw [TypeAHeckeAlgebra.countableAtomicTrace_subtype_eq_of_eq_zero pos q (fun a ↦ w a ≠ 0)
    (fun a ↦ (w a : ℂ)) (hw_sum.congr fun _ ↦ (Complex.norm_real _).symm)
    (fun a h ↦ by simp [not_not.mp h]) x]
  exact hw_eq x

private theorem exists_countableAtomicTrace_wenzlParam {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {d : ℤ} (hd : d ≠ 0) :
    ∃ (ι : Type) (_ : LinearOrder ι) (_ : Countable ι) (pos : ι → Prop) (_ : DecidablePred pos)
      (p : ι → ℝ) (hp_sum : Summable fun a ↦ ‖(p a : ℂ)‖),
      (∀ a, 0 < p a) ∧ (∑' a, p a = 1) ∧ ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n),
        TypeAHeckeAlgebra.countableAtomicTrace pos q (fun a ↦ (p a : ℂ)) hp_sum n x =
          ocneanuTrace ℂ q ((q : ℂ) * ((wenzlParam d Q : ℝ) : ℂ) -
              (↑q⁻¹ : ℂ) * (1 - ((wenzlParam d Q : ℝ) : ℂ)))
            (TypeAHeckeAlgebra.toInfinite ℂ q n x) := by
  obtain ⟨_ | r, rfl | rfl⟩ := Int.eq_nat_or_neg d
  · exact absurd rfl hd
  · simp at hd
  all_goals
    set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a
    have hZ0 : 0 < Z :=
      Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r))
    set c : ℝ := Z⁻¹
    have hc0 : 0 < c := inv_pos.mpr hZ0
    have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
      simpa [c, Z, hQ] using congrArg ((↑) : ℝ → ℂ) (inv_mul_cancel₀ hZ0.ne')
    have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by
      rw [← hQ, ← Complex.ofReal_one, ← Complex.ofReal_add]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hmap (k : ℤ) : ((wenzlParam k Q : ℝ) : ℂ) = wenzlParam k ((q : ℂ) ^ 2) := by
      rw [← hQ]; exact map_wenzlParam Complex.ofRealHom k Q
    have htsum : (∑' a : Fin (r + 1), c * Q ^ (a : ℕ)) = 1 := by
      rw [tsum_fintype, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun a ↦ Q ^ a)]
      exact inv_mul_cancel₀ hZ0.ne'
  · refine ⟨Fin (r + 1), inferInstance, inferInstance, fun _ ↦ True, inferInstance,
      fun a ↦ c * Q ^ (a : ℕ), (hasSum_fintype _).summable,
      fun a ↦ mul_pos hc0 (pow_pos hQ0 a), htsum, fun {n} x ↦ ?_⟩
    simp only [hmap, mul_wenzlParam_natCast_sub h1Q hcZ,
      TypeAHeckeAlgebra.countableAtomicTrace_eq_atomicTrace]
    simpa [hQ] using TypeAHeckeAlgebra.atomicTrace_geometric_eq q hcZ x
  · refine ⟨Fin (r + 1), inferInstance, inferInstance, fun _ ↦ False, inferInstance,
      fun a ↦ c * Q ^ (a : ℕ), (hasSum_fintype _).summable,
      fun a ↦ mul_pos hc0 (pow_pos hQ0 a), htsum, fun {n} x ↦ ?_⟩
    simp only [hmap, mul_wenzlParam_neg_natCast_sub h1Q hcZ,
      TypeAHeckeAlgebra.countableAtomicTrace_eq_atomicTrace]
    simpa [hQ] using TypeAHeckeAlgebra.atomicTrace_negGeometric_eq q hcZ x

/-- **Countable atomic realization of the Ocneanu trace on Wenzl's positive set (`Q ≠ 1`).**
For real nonzero `q : ℂˣ` with `(Q : ℂ) = (q : ℂ) ^ 2`, `Q ≠ 1`, and `η ∈ wenzlPositiveSet Q`,
there exists a countable linearly ordered signed alphabet with strictly positive normalized
weights whose countable atomic trace agrees with `ocneanuTrace ℂ q (q * η - q⁻¹ * (1 - η))` on
every finite stage. -/
theorem exists_countableAtomicTrace_eq_ocneanuTrace {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))]
    {Q : ℝ} (hQ : (Q : ℂ) = (q : ℂ) ^ 2) (hQ1 : Q ≠ 1) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    ∃ (ι : Type) (_ : LinearOrder ι) (_ : Countable ι) (pos : ι → Prop) (_ : DecidablePred pos)
      (p : ι → ℝ) (hp_sum : Summable fun a ↦ ‖(p a : ℂ)‖),
      (∀ a, 0 < p a) ∧ (∑' a, p a = 1) ∧ ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n),
        TypeAHeckeAlgebra.countableAtomicTrace pos q (fun a ↦ (p a : ℂ)) hp_sum n x =
          ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
            (TypeAHeckeAlgebra.toInfinite ℂ q n x) := by
  have hQ0 : 0 < Q := RCLike.pos_of_ofReal_eq_sq_of_isSelfAdjoint q.ne_zero Fact.out hQ
  have : Countable (ℕ ⊕ₗ ℕᵒᵈ) :=
    Countable.of_equiv (ℕ ⊕ ℕ)
      (toLex.symm.trans (Equiv.sumCongr (Equiv.refl ℕ) OrderDual.ofDual)).symm
  rcases mem_wenzlPositiveSet_iff.mp hη with hIcc | ⟨d, hd, rfl⟩
  · rcases hQ1.lt_or_gt with hQlt | hQgt
    · have hle : Q / (1 + Q) ≤ 1 / (1 + Q) := div_le_div_of_nonneg_right hQlt.le (by linarith)
      rw [min_eq_right hle, max_eq_left hle] at hIcc
      exact exists_countableAtomicTrace_of_model TypeAHeckeAlgebra.wenzlLtOnePos
        (TypeAHeckeAlgebra.wenzlLtOneWeight Q η)
        (TypeAHeckeAlgebra.summable_norm_wenzlLtOneWeight hQ0 hQlt η)
        (TypeAHeckeAlgebra.wenzlLtOneWeight_nonneg hQ0 hIcc)
        (TypeAHeckeAlgebra.tsum_wenzlLtOneWeight hQ0 hQlt η)
        (fun x ↦ TypeAHeckeAlgebra.countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace
          hQ0 hQlt hQ.symm η x)
    · have hle : 1 / (1 + Q) ≤ Q / (1 + Q) := div_le_div_of_nonneg_right hQgt.le (by linarith)
      rw [min_eq_left hle, max_eq_right hle] at hIcc
      exact exists_countableAtomicTrace_of_model TypeAHeckeAlgebra.wenzlGtOnePos
        (TypeAHeckeAlgebra.wenzlGtOneWeight Q η)
        (TypeAHeckeAlgebra.summable_norm_wenzlGtOneWeight hQgt η)
        (TypeAHeckeAlgebra.wenzlGtOneWeight_nonneg hQgt hIcc)
        (TypeAHeckeAlgebra.tsum_wenzlGtOneWeight hQgt η)
        (fun x ↦ TypeAHeckeAlgebra.countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace
          hQgt hQ.symm η x)
  · exact exists_countableAtomicTrace_wenzlParam hQ0 hQ hd

private theorem ocneanuTrace_star_mul_self_nonneg_of_countable {q : ℂˣ}
    [Fact (IsSelfAdjoint (q : ℂ))] {η : ℝ}
    (hreal : ∃ (ι : Type) (_ : LinearOrder ι) (_ : Countable ι) (pos : ι → Prop)
      (_ : DecidablePred pos) (p : ι → ℝ) (hp_sum : Summable fun a ↦ ‖(p a : ℂ)‖),
      (∀ a, 0 < p a) ∧ (∑' a, p a = 1) ∧ ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n),
        TypeAHeckeAlgebra.countableAtomicTrace pos q (fun a ↦ (p a : ℂ)) hp_sum n x =
          ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
            (TypeAHeckeAlgebra.toInfinite ℂ q n x))
    {n : ℕ} (y : TypeAHeckeAlgebra ℂ q n) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
      (TypeAHeckeAlgebra.toInfinite ℂ q n (star y * y)) := by
  obtain ⟨_ι, _, _, pos, _, p, hp_sum, hp_pos, _, heq⟩ := hreal
  rw [← heq (star y * y)]
  exact TypeAHeckeAlgebra.countableAtomicTrace_star_mul_self_nonneg pos q hp_sum
    (fun a ↦ Complex.zero_le_real.mpr (hp_pos a).le) y

/-- **Positivity of the Ocneanu trace across Wenzl's positive-real parameter set.** For real nonzero
`q : ℂˣ` with `(Q : ℂ) = (q : ℂ) ^ 2` and `η ∈ wenzlPositiveSet Q`, the Ocneanu trace at
`z = q * η - q⁻¹ * (1 - η)` is nonnegative on every `star x * x`. -/
theorem ocneanuTrace_star_mul_self_nonneg {q : ℂˣ} [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    0 ≤ ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) (star x * x) := by
  have hQ0 : 0 < Q := RCLike.pos_of_ofReal_eq_sq_of_isSelfAdjoint q.ne_zero Fact.out hQ
  obtain ⟨n, y, rfl⟩ := exists_toInfinite_eq x
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul]
  rcases mem_wenzlPositiveSet_iff.mp hη with hIcc | ⟨d, hd, rfl⟩
  · rcases eq_or_ne Q 1 with rfl | hQ1
    · rw [one_add_one_eq_two, min_self, max_self, Set.Icc_self, Set.mem_singleton_iff] at hIcc
      subst hIcc
      have hz0 : (q : ℂ) * ((1 / 2 : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((1 / 2 : ℝ) : ℂ)) = 0 := by
        have _ := q.ne_zero; have hq2 : (q : ℂ) ^ 2 = 1 := by simpa using hQ.symm
        rw [Units.val_inv_eq_inv_val]; push_cast; field_simp; linear_combination hq2
      rw [hz0, map_mul, TypeAHeckeAlgebra.toInfinite_star]
      exact ocneanuTrace_zero_star_mul_self_nonneg _
    · exact ocneanuTrace_star_mul_self_nonneg_of_countable
        (exists_countableAtomicTrace_eq_ocneanuTrace hQ hQ1 hη) y
  · exact ocneanuTrace_star_mul_self_nonneg_of_countable
      (exists_countableAtomicTrace_wenzlParam hQ0 hQ hd) y

/-- The complex Ocneanu trace on `InfiniteTypeAHeckeAlgebra ℂ q` bundled as a
`StarPositiveFunctional` for real nonzero `q : ℂˣ` and `η ∈ wenzlPositiveSet Q`. -/
noncomputable def ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    StarPositiveFunctional (InfiniteTypeAHeckeAlgebra ℂ q) where
  toLinearMap := ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))
  square_nonneg := ocneanuTrace_star_mul_self_nonneg hQ hη

/-- Forgetting positivity recovers the underlying Ocneanu trace. -/
@[simp]
theorem toLinearMap_ocneanuPositiveFunctional (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q) :
    (ocneanuPositiveFunctional q hQ hη).toLinearMap =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) := (rfl)

/-- Evaluating `ocneanuPositiveFunctional` at an element recovers `ocneanuTrace`. -/
@[simp]
theorem ocneanuPositiveFunctional_apply (q : ℂˣ) [Fact (IsSelfAdjoint (q : ℂ))] {Q : ℝ}
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (x : InfiniteTypeAHeckeAlgebra ℂ q) :
    ocneanuPositiveFunctional q hQ hη x =
      ocneanuTrace ℂ q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η)) x := (rfl)

end TauCeti.InfiniteTypeAHeckeAlgebra
