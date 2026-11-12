/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Analysis.Sobolev.Local.Reflection

/-!
# Morrey's embedding on half-discs

Let `Ω ⊆ ℂ` be open and let `U = Ω ∩ {0 ≤ im}` be the corresponding relatively open subset of
the closed upper half-plane. The local Sobolev class `TauCeti.MemWkpLoc p U k` tests weak
derivatives on the interior `Ω ∩ {0 < im}` and imposes `Lᵖ` bounds on compact subsets of `U`,
which may reach the real axis. This file proves Morrey's embedding up to the real axis: for
`2 < p ≤ ∞` and a finite-dimensional codomain, a map in `MemWkpLoc p U 1` has a representative
that is continuous on `U` and Hölder continuous with exponent `1 - 2 / p` on compact subsets
of `U`, with the local Morrey inequality across the axis.

The representative is `TauCeti.halfPlanePreciseRepresentative u`, the precise representative of
the even reflection `TauCeti.planarReflection (higherReflectionCoeff 1) u` of `u` across the real
axis. In the open upper half-plane it is the precise representative of `u` itself
(`TauCeti.halfPlanePreciseRepresentative_of_im_pos`). The proof reflects: near a real point
`x ∈ Ω` the reflection is in `W^{k,p}_loc` of a disc centred at `x`, and off the axis it agrees
with `u`, so by locality it is in `W^{k,p}_loc` of an open neighbourhood of `U` in `Ω`
(`TauCeti.MemWkpLoc.exists_opens_memWkpLoc_planarReflection`, in
`TauCeti.Analysis.Sobolev.Local.Reflection`). The interior Morrey theorems of
`TauCeti.Analysis.Sobolev.Local.Morrey` then apply to the reflection.

The converse fails: `z ↦ √(Im z)` is continuous on the closed half-disc and in `W^{1,p}_loc` of
the open half-disc for every `p` (`TauCeti.memWkpLoc_sqrt_im_ball_inter_im_pos`), but not in
`MemWkpLoc p (ball 0 1 ∩ {0 ≤ im}) 1` for `p ≥ 2` (`TauCeti.memWkpLoc_sqrt_im_iff`).

## Main declarations

* `TauCeti.halfPlanePreciseRepresentative`: the representative up to the real axis.
* `TauCeti.MemWkpLoc.continuousOn_halfPlanePreciseRepresentative` and
  `TauCeti.MemWkpLoc.ae_eq_halfPlanePreciseRepresentative`: it is a continuous representative.
* `TauCeti.MemWkpLoc.exists_holderOnWith_halfPlanePreciseRepresentative_of_isCompact`: Hölder
  continuity with exponent `1 - 2 / p` on compact subsets of `Ω ∩ {0 ≤ im}`; the endpoint `p = ∞`
  is `TauCeti.MemWkpLoc.exists_lipschitzOnWith_halfPlanePreciseRepresentative_of_isCompact`.
* `TauCeti.MemWkpLoc.exists_dist_halfPlanePreciseRepresentative_le`: the local Morrey inequality
  on conjugation-invariant domains, bounded by the `Lᵖ` norm of the derivative on the upper half
  of a disc and its mirror image.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Sobolev spaces on half-discs).
* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19 (extension by
  reflection).
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace TauCeti.MeasureTheory Complex
open scoped ENNReal NNReal ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {u : ℂ → F}

/-! ### The representative up to the real axis -/

variable (u) in
/-- The representative of a half-disc Sobolev map up to the real axis: the precise representative
of its even reflection `TauCeti.planarReflection (higherReflectionCoeff 1) u` across the real axis.
In the open upper half-plane it is the precise representative of `u`
(`TauCeti.halfPlanePreciseRepresentative_of_im_pos`); for `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` with
`p > 2` it is continuous on `Ω ∩ {0 ≤ im}`
(`TauCeti.MemWkpLoc.continuousOn_halfPlanePreciseRepresentative`). -/
def halfPlanePreciseRepresentative : ℂ → F :=
  preciseRepresentative volume (TauCeti.planarReflection (higherReflectionCoeff 1) u)

variable (u) in
/-- The defining equation of `TauCeti.halfPlanePreciseRepresentative`: the precise representative
of the even reflection. -/
theorem halfPlanePreciseRepresentative_def :
    halfPlanePreciseRepresentative u =
      preciseRepresentative volume (TauCeti.planarReflection (higherReflectionCoeff 1) u) := by
  rw [halfPlanePreciseRepresentative]

/-- Off the real axis the representative is the precise representative of `u`: the reflection
agrees with `u` on the open upper half-plane. -/
theorem halfPlanePreciseRepresentative_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    halfPlanePreciseRepresentative u z = preciseRepresentative volume u z :=
  preciseRepresentative_congr_ae_nhds ((isOpen_lt continuous_const continuous_im).mem_nhds hz)
    (ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_im) fun _ hw =>
      planarReflection_of_nonneg _ _ (le_of_lt hw))

/-- The representative `TauCeti.halfPlanePreciseRepresentative u` agrees with `u` almost
everywhere on `Ω ∩ {0 ≤ im}`. -/
theorem MemWkpLoc.ae_eq_halfPlanePreciseRepresentative [CompleteSpace F] (hp : 1 ≤ p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) :
    u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] halfPlanePreciseRepresentative u := by
  obtain ⟨V, hUV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection hp
  have hU : MeasurableSet ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const measurable_im)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hUV
    (hV.memLpLoc.ae_eq_preciseRepresentative hp), ae_restrict_mem hU] with z hz hzU
  rw [halfPlanePreciseRepresentative_def, ← hz, planarReflection_of_nonneg _ _ hzU.2]

variable [FiniteDimensional ℝ F]

/-- **Continuity up to the real axis.** For `2 < p`, the representative
`TauCeti.halfPlanePreciseRepresentative u` of `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` is continuous on
`Ω ∩ {0 ≤ im}`. -/
theorem MemWkpLoc.continuousOn_halfPlanePreciseRepresentative (hp : 2 < p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) :
    ContinuousOn (halfPlanePreciseRepresentative u) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨V, hUV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection (one_le_two.trans hp.le)
  exact (hV.continuousOn_preciseRepresentative hp).mono hUV

/-- **Morrey's embedding up to the real axis.** For `2 < p ≤ ∞`, the representative
`TauCeti.halfPlanePreciseRepresentative u` of `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` is Hölder
continuous with exponent `1 - 2 / p` on every compact subset of `Ω ∩ {0 ≤ im}`, including compact
sets meeting the real axis. -/
theorem MemWkpLoc.exists_holderOnWith_halfPlanePreciseRepresentative_of_isCompact (hp : 2 < p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal
      (halfPlanePreciseRepresentative u) K := by
  obtain ⟨V, hUV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection (one_le_two.trans hp.le)
  exact hV.exists_holderOnWith_preciseRepresentative_of_isCompact hp hK (hKU.trans hUV)

/-- **`W^{1,∞}` maps on half-discs are Lipschitz up to the real axis.** At `p = ∞` the
representative `TauCeti.halfPlanePreciseRepresentative u` is Lipschitz on every compact subset of
`Ω ∩ {0 ≤ im}`. -/
theorem MemWkpLoc.exists_lipschitzOnWith_halfPlanePreciseRepresentative_of_isCompact
    (hu : MemWkpLoc ∞ ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ C : ℝ≥0, LipschitzOnWith C (halfPlanePreciseRepresentative u) K := by
  obtain ⟨V, hUV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection le_top
  exact hV.exists_lipschitzOnWith_preciseRepresentative_of_isCompact hK (hKU.trans hUV)

/-! ### The local Morrey inequality across the real axis -/

/-- **The local Morrey inequality across the real axis.** Let `2 < p ≤ ∞` and `α = 1 - 2 / p`.
There is a constant `C > 0`, depending only on `p` and `F`, such that the following holds. Let
`Ω` be open and invariant under complex conjugation, let `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` with
weak derivative `D` on `Ω ∩ {0 < im}`, and let `x, y` be points with `closedBall x ρ ⊆ Ω`,
`ρ = 2 |x - y|`. Then the representative `u* = TauCeti.halfPlanePreciseRepresentative u` satisfies

`‖u*(x) - u*(y)‖ ≤ C ‖D‖_{Lᵖ((B(x, ρ) ∪ B(conj x, ρ)) ∩ {0 ≤ im})} |x - y|^α`.

The mirror disc `B(conj x, ρ)` enters because the even reflection samples the lower half of
`B(x, ρ)` at its conjugate points. -/
theorem MemWkpLoc.exists_dist_halfPlanePreciseRepresentative_le (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ}, (∀ z ∈ Ω, conj z ∈ Ω) → ∀ {u : ℂ → F}
      {D : ℂ → ℂ →L[ℝ] F}, MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u →
      HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) u D →
      ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (halfPlanePreciseRepresentative u x) (halfPlanePreciseRepresentative u y) ≤
          C * (eLpNorm D p (volume.restrict
            ((ball x (2 * dist x y) ∪ ball (conj x) (2 * dist x y)) ∩ {z | 0 ≤ z.im}))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  obtain ⟨C, hC, h⟩ := MemWkpLoc.exists_dist_preciseRepresentative_le (F := F) hp
  refine ⟨2 * C, by positivity, fun {Ω} hΩ {u D} hu hD {x y} hxy => ?_⟩
  set ρ := 2 * dist x y
  set S : Set ℂ := ball x ρ ∪ ball (conj x) ρ
  set H : Set ℂ := {z | 0 ≤ z.im}
  set Dr := planarReflectionFDeriv (higherReflectionCoeff 1) D with hDr_def
  have hconj : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin 1, imDilation (higherReflectionNode j) z ∈ Ω :=
    fun z hz _ j => by rw [imDilation_higherReflectionNode_fin_one]; exact hΩ z hz
  have hDp := hu.memLpLoc_of_hasWeakFDerivOn_inter_setOf_im_nonneg hD
  have hext := hu.planarReflection_higherReflectionCoeff hp1 hconj
  have hDr : HasWeakFDerivOn volume Ω (TauCeti.planarReflection (higherReflectionCoeff 1) u)
      (Dr) :=
    hD.planarReflection hconj (hu.memLpLoc.mono_exponent hp1) (hDp.mono_exponent hp1)
      (by simp [higherReflectionCoeff_one])
  -- The reflected derivative is bounded pointwise by the reflection of `‖D‖`.
  have hpt (z : ℂ) :
      ‖Dr z‖ ≤ TauCeti.planarReflection (higherReflectionCoeff 1) (fun w => ‖D w‖) z := by
    rw [hDr_def]
    rcases le_or_gt 0 z.im with hz | hz
    · rw [planarReflectionFDeriv_of_nonneg _ _ hz, planarReflection_of_nonneg _ _ hz]
    · rw [planarReflectionFDeriv_of_neg _ _ hz, planarReflection_of_neg _ _ hz]
      simp only [Fin.sum_univ_one, higherReflectionCoeff_one, one_smul]
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right
        (norm_nonneg _) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_))
      rw [one_mul]
      refine norm_imDilation_le ?_ w
      rw [higherReflectionNode_eq]
      simp
  have hS : ∀ z ∈ S, z.im < 0 → ∀ j : Fin 1, imDilation (higherReflectionNode j) z ∈ S := by
    intro z hz _ j
    rw [imDilation_higherReflectionNode_fin_one]
    rcases hz with hz | hz
    · right
      rwa [mem_ball, Complex.dist_conj_conj]
    · left
      rwa [mem_ball, ← Complex.dist_conj_conj, Complex.conj_conj]
  have hbound : planarReflectionBound (higherReflectionCoeff 1) p = 2 := by
    rw [planarReflectionBound_higherReflectionCoeff, higherReflectionBound_eq]
    simp [higherReflectionCoeff_one, higherReflectionNode_eq]
    norm_num
  -- `D` is `Lᵖ` on `S ∩ H`: `S ∩ H` lies in a compact subset of `Ω ∩ H`.
  have hDS : MemLp D p (volume.restrict (S ∩ H)) := by
    have hxy' : closedBall (conj x) ρ ⊆ Ω := fun z hz => by
      have hz' : conj z ∈ closedBall x ρ := by
        rwa [mem_closedBall, ← Complex.dist_conj_conj, Complex.conj_conj]
      simpa using hΩ _ (hxy hz')
    have hK : IsCompact ((closedBall x ρ ∪ closedBall (conj x) ρ) ∩ H) :=
      ((isCompact_closedBall _ _).union (isCompact_closedBall _ _)).inter_right
        (isClosed_le continuous_const continuous_im)
    refine ((memLpLoc_iff.1 hDp _ (inter_subset_inter_left _ (union_subset hxy hxy')) hK)
      |>.mono_measure (Measure.restrict_mono (inter_subset_inter_left _
        (union_subset_union ball_subset_closedBall ball_subset_closedBall)) le_rfl))
  have hDrm : AEStronglyMeasurable Dr (volume.restrict (ball x ρ)) :=
    ((memLpLoc_iff.1 (hext.memLpLoc_of_hasWeakFDerivOn hDr) _ hxy (isCompact_closedBall _ _))
      |>.mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl)).aestronglyMeasurable
  have hle : eLpNorm Dr p (volume.restrict (ball x ρ)) ≤
      2 * eLpNorm D p (volume.restrict (S ∩ H)) :=
    calc eLpNorm Dr p (volume.restrict (ball x ρ))
        ≤ eLpNorm (TauCeti.planarReflection (higherReflectionCoeff 1) (fun w => ‖D w‖)) p
          (volume.restrict (ball x ρ)) := eLpNorm_mono_real hDrm hpt
      _ ≤ eLpNorm (TauCeti.planarReflection (higherReflectionCoeff 1) (fun w => ‖D w‖)) p
          (volume.restrict S) :=
          eLpNorm_mono_measure _ (Measure.restrict_mono subset_union_left le_rfl)
      _ ≤ 2 * eLpNorm (fun w => ‖D w‖) p (volume.restrict (S ∩ H)) := by
          rw [← hbound]
          exact eLpNorm_planarReflection_le hp1 hS _ _
      _ = 2 * eLpNorm D p (volume.restrict (S ∩ H)) := by
          rw [eLpNorm_norm]
          exact hDS.aestronglyMeasurable
  refine (h hext hDr hxy).trans ?_
  have hle' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hDS.eLpNorm_ne_top) hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hle'
  calc C * (eLpNorm Dr p (volume.restrict (ball x ρ))).toReal *
        dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ)
      ≤ C * (2 * (eLpNorm D p (volume.restrict (S ∩ H))).toReal) *
        dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by gcongr
    _ = _ := by ring

end TauCeti
