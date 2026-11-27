/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylDimension.Log
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.TargetParameter
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.WeightBounds

/-!
# The degree of a family of theta-lift target parameters

The consecutive initial entries of the target parameter contribute no factor to the Weyl
quotient. Each subsequent column of the product has one large factor for each initial entry.
Bounding the remaining factors by the shifted weights controls the product of the local degrees
in the second moment of a Poincaré series.

The degree estimate is `New.Data.log_filling_besselDegree_mem_Icc` in
`New/Spanning/Unfolding/FillingAdmissible.lean` of
<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>.
-/

public section

open Finset Real

namespace TauCeti.OneSidedBound

private theorem sum_log_targetParameter_sub_mem_Icc {a m κ g : ℕ}
    (l : DominantWeight (a + m)) (hl : ∀ i, l.rhoShift i = targetParameter (a + 1) κ g i)
    (hg₁ : a ≤ (a + 1) / 2 + 2 * g) (hg₂ : (a + 1) / 2 ≤ g + 1) (j : Fin m) :
    (∑ i ∈ Iio (j.natAdd a), log ((l.rhoShift i : ℝ) - l.rhoShift (j.natAdd a))) ∈
      Set.Icc (a * log κ) ((a + j.val : ℕ) * log (κ + (2 * (j.val + 1) + 1) * g : ℕ)) := by
  have hpos (i : Fin (a + m)) (hi : i ∈ Iio (j.natAdd a)) :
      1 ≤ (l.rhoShift i : ℝ) - l.rhoShift (j.natAdd a) := by
    have he : (1 : ℤ) ≤ l.rhoShift i - l.rhoShift (j.natAdd a) := by
      have := l.rhoShift_strictAnti (mem_Iio.mp hi)
      omega
    exact_mod_cast he
  have hlow (i : Fin (a + m)) (hi : i.val < a) :
      (κ : ℝ) ≤ (l.rhoShift i : ℝ) - l.rhoShift (j.natAdd a) := by
    rw [hl, hl, Fin.val_natAdd]
    exact_mod_cast le_targetParameter_sub_of_lt_stem (κ := κ) (j := j.val) hg₁ hi
  have hstem : (univ : Finset (Fin a)).map (Fin.castAddEmb m) ⊆ Iio (j.natAdd a) := by
    intro i hi
    obtain ⟨t, -, rfl⟩ := mem_map.mp hi
    exact mem_Iio.mpr (by simpa [Fin.lt_def] using t.isLt.trans_le (Nat.le_add_right a j.val))
  refine ⟨?_, ?_⟩
  · calc
      _ = ∑ _i : Fin a, log κ := by simp
      _ ≤ ∑ i : Fin a, log ((l.rhoShift (i.castAdd m) : ℝ) - l.rhoShift (j.natAdd a)) := by
        refine sum_le_sum fun i _ ↦ ?_
        by_cases hκ : κ = 0
        · simpa [hκ] using log_nonneg (hpos _ (hstem (mem_map.mpr ⟨i, mem_univ _, rfl⟩)))
        · exact log_le_log (by positivity) (hlow _ i.isLt)
      _ ≤ _ := by
        simpa only [sum_map, Fin.coe_castAddEmb] using
          (sum_le_sum_of_subset_of_nonneg (f := fun i ↦
            log ((l.rhoShift i : ℝ) - l.rhoShift (j.natAdd a))) hstem
            fun i hi _ ↦ log_nonneg (hpos i hi))
  · calc
      _ ≤ ∑ _i ∈ Iio (j.natAdd a), log (κ + (2 * (j.val + 1) + 1) * g : ℕ) := by
        refine sum_le_sum fun i hi ↦ log_le_log (one_pos.trans_le (hpos i hi)) ?_
        rw [hl, hl, Fin.val_natAdd]
        exact_mod_cast targetParameter_sub_le_liftWeight (κ := κ) (i := i.val) (j := j.val) hg₂
      _ = _ := by rw [sum_const, nsmul_eq_mul, Fin.card_Iio, Fin.val_natAdd]

/-- Bounds for the logarithm of the product of Weyl degrees of the theta-lift target rows,
corrected by the factorials in the tail. Here `a = k - 1` is the stem length, `m` is the number of
lifts, and the target rank is `a + m`. The degree of a row is computed from the dominant weight
whose rho shift is that row. -/
theorem log_prod_weylDimension_targetParameter_mem_Icc {ι : Type*} (S : Finset ι)
    {a m x : ℕ} (κ : ι → ℕ) (l : ι → DominantWeight (a + m))
    (hl : ∀ v ∈ S, ∀ i, (l v).rhoShift i = targetParameter (a + 1) (κ v) ((a + m) ^ 8) i)
    (hx : 3 ^ 8 ≤ x) (hm : m ^ 2 ≤ 4 * x) (hr : a + m ≤ 3 * x ^ 5)
    (hκ : ∀ v ∈ S, x ^ 43 ≤ κ v) :
    log (∏ v ∈ S, (weylDimension (l v) : ℝ)) +
        S.card * (∑ j : Fin m, log ((a + j.val).factorial : ℝ)) ∈
      Set.Icc (∑ v ∈ S, (m : ℝ) * (a * log (κ v)))
        (∑ v ∈ S, (m : ℝ) * ((a + m : ℕ) * (log (κ v) + 1 / x))) := by
  have hg : a ≤ (a + m) ^ 8 := (Nat.le_add_right a m).trans (Nat.le_self_pow (by decide) _)
  have hstem (v : ι) (hv : v ∈ S) (i j : Fin (a + m)) (hij : i < j) (hj : j.val < a) :
      (l v).val i = (l v).val j := by
    have hi := Fin.lt_def.mp hij
    have hentry (t : Fin (a + m)) (ht : t.val < a) :
        (l v).val t = (↑((a + 1) / 2) : ℤ) - 1 := by
      have he := hl v hv t
      rw [DominantWeight.rhoShift_apply, targetParameter_of_succ_lt _ _ (by omega)] at he
      omega
    exact (hentry i (hi.trans hj)).trans (hentry j hj).symm
  rw [log_prod (fun v _ ↦ Nat.cast_ne_zero.mpr (weylDimension_pos (l v)).ne'),
    ← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
  constructor
  · refine sum_le_sum fun v hv ↦ ?_
    rw [log_weylDimension_add_sum_tail_log_factorial (l v) (hstem v hv)]
    simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (sum_le_sum (s := (univ : Finset (Fin m))) fun j _ ↦
        (sum_log_targetParameter_sub_mem_Icc (l v) (hl v hv) (by omega) (by omega) j).1)
  · refine sum_le_sum fun v hv ↦ ?_
    rw [log_weylDimension_add_sum_tail_log_factorial (l v) (hstem v hv)]
    calc
      _ ≤ ∑ _j : Fin m, (↑(a + m : ℕ) : ℝ) * (log (κ v) + 1 / x) := by
        refine sum_le_sum fun j _ ↦ (sum_log_targetParameter_sub_mem_Icc (l v) (hl v hv)
          (by omega) (by omega) j).2.trans ?_
        have hδ := (shiftedWeight_mem_Icc (κ := κ v) hx hm hr
          (i := 2 * (j.val + 1)) (by have := j.isLt; omega)).2
        have hlog := log_shiftedWeight_le (hκ v hv) (Nat.le_of_add_le_add_left hδ)
        have hj : (↑(a + j.val) : ℝ) ≤ (↑(a + m : ℕ) : ℝ) := by
          exact_mod_cast Nat.add_le_add_left j.isLt.le a
        exact mul_le_mul hj hlog (log_natCast_nonneg _) (by positivity)
      _ = _ := by simp

end TauCeti.OneSidedBound
