/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic

/-!
# Spectral cutoffs of bounded normal operators

For a bounded normal operator `a : H →L[ℂ] H` on a complex Hilbert space and a threshold `ε : ℝ`,
the spectral cutoff `a.spectralCutoff ε` is the spectral projection of `a` onto the closed tail
`{z ∈ spectrum ℂ a | ε ≤ ‖z‖}`.

Because `z` is invertible away from `0` on `{z | ε ≤ ‖z‖}` for `ε > 0`, `a.spectralCutoff ε`
factors through `a` in the Borel functional calculus and therefore belongs to every two-sided ideal
of `H →L[ℂ] H` containing `a`. Meanwhile, `‖a - a * a.spectralCutoff ε‖ ≤ ε` for every `ε ≥ 0`, so
`a * a.spectralCutoff ε → a` in operator norm as `ε → 0⁺`. Consequently, if `a` avoids a closed
two-sided ideal `I`, some spectral cutoff `a.spectralCutoff ε` (`ε > 0`) also avoids `I`.

## Main declarations

* `ContinuousLinearMap.spectralCutoff`: the spectral projection of a normal operator `a` onto
  `{z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}`, characterized by
  `ContinuousLinearMap.spectralCutoff_eq_spectralPVM_proj`.
* `ContinuousLinearMap.isStarProjection_spectralCutoff`,
  `ContinuousLinearMap.commute_spectralCutoff`, `ContinuousLinearMap.spectralCutoff_of_nonpos`, and
  `ContinuousLinearMap.spectralCutoff_zero`: basic algebraic properties of spectral cutoffs.
* `ContinuousLinearMap.spectralCutoff_mem_twoSidedIdeal`: for `ε > 0`, `a.spectralCutoff ε` belongs
  to every two-sided ideal containing `a`.
* `ContinuousLinearMap.norm_sub_mul_spectralCutoff_le` and
  `ContinuousLinearMap.tendsto_mul_spectralCutoff`: operator-norm approximation of `a` by
  `a * a.spectralCutoff ε` as `ε → 0⁺`.
* `ContinuousLinearMap.exists_spectralCutoff_notMem_of_isClosed`: if `a` avoids a closed two-sided
  ideal `I`, then some `a.spectralCutoff ε` (`ε > 0`) also avoids `I`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Academic Press (1990), Theorem 2.4.9.
-/

public noncomputable section

open Filter TauCeti Topology

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Measurability of the closed spectral tail `{z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}`. -/
private theorem measurableSet_spectralCutoffSet (a : H →L[ℂ] H) (ε : ℝ) :
    MeasurableSet {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖} :=
  (isClosed_le continuous_const (continuous_norm.comp continuous_subtypeVal)).measurableSet

/-- For a normal operator `a : H →L[ℂ] H` and `ε : ℝ`, `a.spectralCutoff ε` is the spectral
projection of `a` onto `{z ∈ spectrum ℂ a | ε ≤ ‖z‖}`. -/
def spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] (ε : ℝ) : H →L[ℂ] H :=
  a.spectralPVM.proj {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖} (measurableSet_spectralCutoffSet a ε)

/-- Defining formula for `spectralCutoff` in terms of `spectralPVM.proj`. -/
theorem spectralCutoff_eq_spectralPVM_proj (a : H →L[ℂ] H) [IsStarNormal a] (ε : ℝ)
    (h : MeasurableSet {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}) :
    a.spectralCutoff ε = a.spectralPVM.proj {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖} h :=
  (rfl)

/-- Every spectral cutoff of a normal operator is a star projection. -/
theorem isStarProjection_spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] (ε : ℝ) :
    IsStarProjection (a.spectralCutoff ε) :=
  a.spectralPVM.isStarProjection_proj _ _

/-- Every spectral cutoff of a normal operator `a` commutes with `a`. -/
theorem commute_spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] (ε : ℝ) :
    Commute a (a.spectralCutoff ε) :=
  (a.forall_commute_spectralPVM_proj_iff a).mpr (Commute.refl a) _ _

/-- For `ε ≤ 0`, the spectral cutoff `a.spectralCutoff ε` is the identity operator. -/
theorem spectralCutoff_of_nonpos (a : H →L[ℂ] H) [IsStarNormal a] {ε : ℝ} (hε : ε ≤ 0) :
    a.spectralCutoff ε = 1 := by
  have huniv : {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖} = Set.univ :=
    Set.eq_univ_of_forall fun z ↦ hε.trans (norm_nonneg _)
  rw [spectralCutoff_eq_spectralPVM_proj a ε (measurableSet_spectralCutoffSet a ε),
    a.spectralPVM.proj_congr huniv _ MeasurableSet.univ, a.spectralPVM.proj_univ, ← one_def]

/-- The spectral cutoff at threshold `0` is the identity operator. -/
@[simp]
theorem spectralCutoff_zero (a : H →L[ℂ] H) [IsStarNormal a] :
    a.spectralCutoff 0 = 1 :=
  a.spectralCutoff_of_nonpos le_rfl

/-- For `ε > 0`, `a.spectralCutoff ε` belongs to every two-sided ideal containing `a`. -/
theorem spectralCutoff_mem_twoSidedIdeal (a : H →L[ℂ] H) [IsStarNormal a]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (ha : a ∈ I) {ε : ℝ} (hε : 0 < ε) :
    a.spectralCutoff ε ∈ I := by
  -- Truncating `z ↦ z⁻¹` at `ε⁻¹` retains `z⁻¹` on `ε ≤ ‖z‖` and vanishes on `0 < ‖z‖ < ε`.
  let B : Set (spectrum ℂ a) := {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}
  have hB : MeasurableSet B := measurableSet_spectralCutoffSet a ε
  let g : BoundedBorelFunction (spectrum ℂ a) :=
    BoundedBorelFunction.truncate (fun z : spectrum ℂ a ↦ (z : ℂ)⁻¹)
      continuous_subtypeVal.measurable.inv ε⁻¹
  let idSym : BoundedBorelFunction (spectrum ℂ a) :=
    BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
  have hprod : idSym * g = BoundedBorelFunction.indicator B hB 1 := by
    ext z
    simp only [idSym, g, _root_.mul_apply, BoundedBorelFunction.indicator_apply,
      BoundedBorelFunction.truncate_apply, BoundedBorelFunction.ofContinuousMap_apply,
      ContinuousMap.restrict_apply, ContinuousMap.id_apply]
    by_cases hz : z ∈ B
    · have hnorm_pos : 0 < ‖(z : ℂ)‖ := hε.trans_le hz
      have hle : z ∈ {y : spectrum ℂ a | ‖(y : ℂ)⁻¹‖ ≤ ε⁻¹} := by
        rw [Set.mem_ofPred_eq, norm_inv]
        exact (inv_le_inv₀ hnorm_pos hε).mpr hz
      rw [Set.indicator_of_mem hle, Set.indicator_of_mem hz,
        _root_.one_apply, mul_inv_cancel₀ (norm_pos_iff.mp hnorm_pos)]
    · have hlt : ‖(z : ℂ)‖ < ε := not_le.mp hz
      rw [Set.indicator_of_notMem hz]
      rcases eq_or_ne (z : ℂ) 0 with hz0 | hz0
      · rw [hz0, zero_mul]
      · have hgt : z ∉ {y : spectrum ℂ a | ‖(y : ℂ)⁻¹‖ ≤ ε⁻¹} := by
          rw [Set.mem_ofPred_eq, norm_inv, not_le]
          exact (inv_lt_inv₀ hε (norm_pos_iff.mpr hz0)).mpr hlt
        rw [Set.indicator_of_notMem hgt, mul_zero]
  have heq : a.spectralCutoff ε = a * a.borelCalculus g := by
    rw [spectralCutoff_eq_spectralPVM_proj a ε hB, ← a.borelCalculus_indicator hB, ← hprod, map_mul,
      a.borelCalculus_restrict_id]
  rw [heq]
  exact I.mul_mem_right a _ ha

/-- Truncating the spectrum of a normal operator `a` below radius `ε ≥ 0` changes `a` by at most
`ε` in operator norm. -/
theorem norm_sub_mul_spectralCutoff_le (a : H →L[ℂ] H) [IsStarNormal a] {ε : ℝ} (hε : 0 ≤ ε) :
    ‖a - a * a.spectralCutoff ε‖ ≤ ε := by
  let B : Set (spectrum ℂ a) := {z : spectrum ℂ a | ε ≤ ‖(z : ℂ)‖}
  have hB : MeasurableSet B := measurableSet_spectralCutoffSet a ε
  let idSym : BoundedBorelFunction (spectrum ℂ a) :=
    BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a))
  have heq : a - a * a.spectralCutoff ε =
      a.borelCalculus (idSym - idSym * BoundedBorelFunction.indicator B hB 1) := by
    rw [spectralCutoff_eq_spectralPVM_proj a ε hB, map_sub, map_mul, a.borelCalculus_restrict_id,
      a.borelCalculus_indicator hB]
  rw [heq]
  refine a.norm_borelCalculus_le hε fun z ↦ ?_
  by_cases hz : z ∈ B
  · simpa [hz] using hε
  · have hlt : ‖(z : ℂ)‖ < ε := not_le.mp hz
    simpa [idSym, hz] using hlt.le

/-- As `ε → 0⁺`, `a * a.spectralCutoff ε` converges to `a` in operator norm. -/
theorem tendsto_mul_spectralCutoff (a : H →L[ℂ] H) [IsStarNormal a] :
    Tendsto (fun ε : ℝ ↦ a * a.spectralCutoff ε) (𝓝[≥] 0) (𝓝 a) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (eventually_nhdsWithin_of_forall fun ε hε ↦ ?_)
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)
  rw [norm_sub_rev]
  exact a.norm_sub_mul_spectralCutoff_le hε

/-- If a normal operator `a` avoids a closed two-sided ideal `I`, then some spectral cutoff
`a.spectralCutoff ε` (`ε > 0`) also avoids `I`. -/
theorem exists_spectralCutoff_notMem_of_isClosed (a : H →L[ℂ] H) [IsStarNormal a]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (hI : IsClosed (I : Set (H →L[ℂ] H))) (ha : a ∉ I) :
    ∃ ε > 0, a.spectralCutoff ε ∉ I := by
  by_contra! h
  have hlim : Tendsto (fun ε : ℝ ↦ a * a.spectralCutoff ε) (𝓝[>] 0) (𝓝 a) :=
    a.tendsto_mul_spectralCutoff.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
  exact ha (hI.mem_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun ε hε ↦ I.mul_mem_left a _ (h ε hε)))

end ContinuousLinearMap

end
