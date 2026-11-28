/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Countable.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.WenzlParam
import TauCeti.Algebra.TypeAHeckeAlgebra.AtomicModel.Wenzl.Basic

/-!
# Countable atomic realizations of the Ocneanu trace on Wenzl's positive set

For real `Q > 0` with `q ^ 2 = Q`, every `η ∈ wenzlPositiveSet Q` except `(Q, η) = (1, 1 / 2)`
admits a `CountableAtomicRealization q z` (`z = q * η - q⁻¹ * (1 - η)`): a discrete realization at
`wenzlParam d Q` (`nonempty_countableAtomicRealization_wenzlParam`) and the full positive-set
realization (`nonempty_countableAtomicRealization_ocneanuTrace`), built via
`CountableAtomicRealization.ofNonneg`.
-/

public section

open OrderDual

namespace TauCeti.TypeAHeckeAlgebra

/-- Bundled countable atomic realization of `ocneanuTrace ℂ q z` with strictly positive weights. -/
structure CountableAtomicRealization (q : ℂˣ) (z : ℂ) : Type 1 where
  /-- The countable linearly ordered alphabet. -/
  ι : Type
  [linearOrder : LinearOrder ι]
  [countable : Countable ι]
  /-- Sign predicate splitting `ι` into positive and negative letters. -/
  pos : ι → Prop
  [decidablePred : DecidablePred pos]
  /-- Normalized strictly positive real weights on `ι`. -/
  weight : ι → ℝ
  summable_norm_weight : Summable fun a ↦ ‖(weight a : ℂ)‖
  weight_pos : ∀ a, 0 < weight a
  tsum_weight : (∑' a, weight a) = 1
  /-- Agreement of the countable atomic trace with the Ocneanu trace on every finite stage. -/
  trace_eq : ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n),
    countableAtomicTrace pos q (fun a ↦ (weight a : ℂ)) summable_norm_weight n x =
      InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q z (toInfinite ℂ q n x)

attribute [instance] CountableAtomicRealization.linearOrder CountableAtomicRealization.countable
  CountableAtomicRealization.decidablePred

section

variable {q : ℂˣ} {z : ℂ} {ι₀ : Type} [LinearOrder ι₀] [Countable ι₀] (pos : ι₀ → Prop)
  [DecidablePred pos] (w : ι₀ → ℝ) (hw_sum : Summable fun a ↦ ‖w a‖)
  (hw_nonneg : ∀ a, 0 ≤ w a) (hw_tsum : (∑' a, w a) = 1)
  (hw_eq : ∀ {n : ℕ} (x : TypeAHeckeAlgebra ℂ q n), countableAtomicTrace pos q (fun a ↦ (w a : ℂ))
      (hw_sum.congr fun _ ↦ (Complex.norm_real _).symm) n x =
    InfiniteTypeAHeckeAlgebra.ocneanuTrace ℂ q z (toInfinite ℂ q n x))

/-- Construct a strictly-positive `CountableAtomicRealization` from nonnegative weights by
restricting the alphabet to the support `{a : ι₀ // w a ≠ 0}`. -/
@[expose] def CountableAtomicRealization.ofNonneg : CountableAtomicRealization q z where
  ι := {a : ι₀ // w a ≠ 0}
  pos a := pos a.val
  weight a := w a.val
  summable_norm_weight := (hw_sum.congr fun _ ↦ (Complex.norm_real _).symm).comp_injective
    Subtype.val_injective
  weight_pos a := (hw_nonneg a.val).lt_of_ne' a.property
  tsum_weight := (Subtype.val_injective.tsum_eq fun a (ha : w a ≠ 0) ↦ ⟨⟨a, ha⟩, rfl⟩).trans hw_tsum
  trace_eq {n} x := (countableAtomicTrace_subtype_eq_of_eq_zero pos q (fun a ↦ w a ≠ 0) _
    (hw_sum.congr fun _ ↦ (Complex.norm_real _).symm) (fun a h ↦ by simp [not_not.mp h]) x).trans
    (hw_eq x)

/-- The sign predicate of `CountableAtomicRealization.ofNonneg` is inherited from the ambient
alphabet. -/
@[simp] theorem CountableAtomicRealization.ofNonneg_pos (a : {a : ι₀ // w a ≠ 0}) :
    (CountableAtomicRealization.ofNonneg pos w hw_sum hw_nonneg hw_tsum hw_eq).pos a ↔
      pos a.val := Iff.rfl

/-- The weight of `CountableAtomicRealization.ofNonneg` is inherited from the ambient alphabet. -/
@[simp] theorem CountableAtomicRealization.ofNonneg_weight (a : {a : ι₀ // w a ≠ 0}) :
    (CountableAtomicRealization.ofNonneg pos w hw_sum hw_nonneg hw_tsum hw_eq).weight a = w a.val :=
  rfl

end

/-- **Discrete countable atomic realization** at `η = wenzlParam d Q` (`d ≠ 0`) for `0 < Q`. -/
theorem nonempty_countableAtomicRealization_wenzlParam {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {d : ℤ} (hd : d ≠ 0) :
    Nonempty (CountableAtomicRealization q
      ((q : ℂ) * ((wenzlParam d Q : ℝ) : ℂ) - (↑q⁻¹ : ℂ) * (1 - ((wenzlParam d Q : ℝ) : ℂ)))) := by
  obtain ⟨_ | r, rfl | rfl⟩ := Int.eq_nat_or_neg d <;>
    [exact absurd rfl hd; exact absurd (by simp) hd; skip; skip]
  all_goals
    set Z : ℝ := ∑ a ∈ Finset.range (r + 1), Q ^ a; set c : ℝ := Z⁻¹
    have hZ0 : 0 < Z := Finset.sum_pos (fun a _ ↦ pow_pos hQ0 a) (by simp)
    have hcZ : (c : ℂ) * ∑ a ∈ Finset.range (r + 1), ((q : ℂ) ^ 2) ^ a = 1 := by
      simpa [c, Z, hQ] using congrArg ((↑) : ℝ → ℂ) (inv_mul_cancel₀ hZ0.ne')
    have h1Q : 1 + (q : ℂ) ^ 2 ≠ 0 := by rw [← hQ]; exact mod_cast (by linarith : (1 + Q : ℝ) ≠ 0)
    have hmap (k : ℤ) : ((wenzlParam k Q : ℝ) : ℂ) = wenzlParam k ((q : ℂ) ^ 2) :=
      hQ ▸ map_wenzlParam Complex.ofRealHom k Q
    have htsum : (∑' a : Fin (r + 1), c * Q ^ (a : ℕ)) = 1 := by
      rw [tsum_fintype, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range]; exact inv_mul_cancel₀ hZ0.ne'
  · exact ⟨⟨Fin (r + 1), fun _ ↦ True, fun a ↦ c * Q ^ (a : ℕ), (hasSum_fintype _).summable,
      fun a ↦ mul_pos (inv_pos.mpr hZ0) (pow_pos hQ0 a), htsum, fun x ↦ by
        rw [hmap, mul_wenzlParam_natCast_sub h1Q hcZ, countableAtomicTrace_eq_atomicTrace]
        simpa [hQ] using atomicTrace_geometric_eq q hcZ x⟩⟩
  · exact ⟨⟨Fin (r + 1), fun _ ↦ False, fun a ↦ c * Q ^ (a : ℕ), (hasSum_fintype _).summable,
      fun a ↦ mul_pos (inv_pos.mpr hZ0) (pow_pos hQ0 a), htsum, fun x ↦ by
        rw [hmap, mul_wenzlParam_neg_natCast_sub h1Q hcZ, countableAtomicTrace_eq_atomicTrace]
        simpa [hQ] using atomicTrace_negGeometric_eq q hcZ x⟩⟩

/-- **Countable atomic realization of the Ocneanu trace on Wenzl's positive set** away from
`(Q, η) = (1, 1 / 2)`. -/
theorem nonempty_countableAtomicRealization_ocneanuTrace {q : ℂˣ} {Q : ℝ} (hQ0 : 0 < Q)
    (hQ : (Q : ℂ) = (q : ℂ) ^ 2) {η : ℝ} (hη : η ∈ wenzlPositiveSet Q)
    (hreg : ¬ (Q = 1 ∧ η = 1 / 2)) :
    Nonempty (CountableAtomicRealization q ((q : ℂ) * η - (↑q⁻¹ : ℂ) * (1 - η))) := by
  have : Countable (ℕ ⊕ₗ ℕᵒᵈ) := Countable.of_equiv (ℕ ⊕ ℕᵒᵈ) toLex.symm
  rcases mem_wenzlPositiveSet_iff.mp hη with hIcc | ⟨d, hd, rfl⟩
  · rcases lt_trichotomy Q 1 with hQlt | rfl | hQgt
    · have hle := div_le_div_of_nonneg_right hQlt.le (by linarith : 0 ≤ 1 + Q)
      rw [min_eq_right hle, max_eq_left hle] at hIcc
      exact ⟨.ofNonneg wenzlLtOnePos (wenzlLtOneWeight Q η)
        (summable_norm_wenzlLtOneWeight hQ0 hQlt η) (wenzlLtOneWeight_nonneg hQ0 hIcc)
        (tsum_wenzlLtOneWeight hQ0 hQlt η) fun x ↦
          countableAtomicTrace_wenzlLtOneWeight_eq_ocneanuTrace hQ0 hQlt hQ.symm η x⟩
    · rw [one_add_one_eq_two, min_self, max_self, Set.Icc_self, Set.mem_singleton_iff] at hIcc
      exact absurd ⟨rfl, hIcc⟩ hreg
    · have hle := div_le_div_of_nonneg_right hQgt.le (by linarith : 0 ≤ 1 + Q)
      rw [min_eq_left hle, max_eq_right hle] at hIcc
      exact ⟨.ofNonneg wenzlGtOnePos (wenzlGtOneWeight Q η)
        (summable_norm_wenzlGtOneWeight hQgt η) (wenzlGtOneWeight_nonneg hQgt hIcc)
        (tsum_wenzlGtOneWeight hQgt η) fun x ↦
          countableAtomicTrace_wenzlGtOneWeight_eq_ocneanuTrace hQgt hQ.symm η x⟩
  · exact nonempty_countableAtomicRealization_wenzlParam hQ0 hQ hd

end TauCeti.TypeAHeckeAlgebra
