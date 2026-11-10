/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Morrey
public import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.Sobolev.Local.Examples
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

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
`x ∈ Ω` the reflection is in `W^{k,p}_loc` of a disc centred at `x`
(`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball`), and off the axis it agrees
with `u`, so by locality it is in `W^{k,p}_loc` of an open neighbourhood of `U` in `Ω`
(`TauCeti.MemWkpLoc.exists_opens_memWkpLoc_planarReflection`). The interior Morrey theorems of
`TauCeti.Analysis.Sobolev.Local.Morrey` then apply to the reflection.

The converse fails: `z ↦ √(Im z)` is continuous on the closed half-disc and in `W^{1,p}_loc` of
the open half-disc for every `p`, but not in `MemWkpLoc p (ball 0 1 ∩ {0 ≤ im}) 1` for `p ≥ 2`
(`TauCeti.exists_continuousOn_not_memWkpLoc_ball_inter_setOf_im_nonneg`).

## Main declarations

* `TauCeti.MemWkpLoc.exists_opens_memWkpLoc_planarReflection`: the order-`k` reflection of a map
  in `MemWkpLoc p (Ω ∩ {0 ≤ im}) k` is in `MemWkpLoc p V k` for an open `V` with
  `Ω ∩ {0 ≤ im} ⊆ V ⊆ Ω`.
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

/-! ### Extension across the real axis -/

/-- **Reflection near a relatively open subset of the closed upper half-plane.** The order-`k`
higher reflection of `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) k` is in `MemWkpLoc p V k` on an open set
`V` between `Ω ∩ {0 ≤ im}` and `Ω`: the union of the open upper part of `Ω` and of discs in `Ω`
centred on the real axis. No symmetry of `Ω` is assumed. -/
theorem MemWkpLoc.exists_opens_memWkpLoc_planarReflection [CompleteSpace F] (hp : 1 ≤ p)
    {k : ℕ} (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    ∃ V : Opens ℂ, (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ V ∧ (V : Set ℂ) ⊆ Ω ∧
      MemWkpLoc p V k (TauCeti.planarReflection (higherReflectionCoeff k) u) := by
  choose r hr0 hrΩ using fun x : {x : ℝ // (x : ℂ) ∈ Ω} => Metric.isOpen_iff.1 Ω.isOpen _ x.2
  let H : Opens ℂ := ⟨{z | 0 < z.im}, isOpen_lt continuous_const continuous_im⟩
  let O : Option {x : ℝ // (x : ℂ) ∈ Ω} → Opens ℂ := fun i =>
    i.elim (Ω ⊓ H) fun x => ⟨ball (x : ℂ) (r x), isOpen_ball⟩
  refine ⟨⨆ i, O i, fun z hz => ?_, ?_, (memWkpLoc_iSup_iff O).2 ?_⟩
  · rw [Opens.coe_iSup, mem_iUnion]
    rcases (show 0 ≤ z.im from hz.2).lt_or_eq with h | h
    · exact ⟨none, hz.1, h⟩
    · have hz' : ((z.re : ℝ) : ℂ) = z := Complex.ext rfl (by simpa using h)
      refine ⟨some ⟨z.re, by rw [hz']; exact hz.1⟩, ?_⟩
      exact mem_ball.2 ((dist_eq_zero.2 hz'.symm).trans_lt (hr0 _))
  · rw [Opens.coe_iSup]
    refine iUnion_subset fun i => ?_
    cases i with
    | none => exact inter_subset_left
    | some x => exact hrΩ x
  · rintro (_ | x)
    · change MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 < z.im}) k _
      refine (hu.mono (inter_subset_inter_right _ (ofPred_subset_ofPred.2 fun _ h => h.le)))
        |>.congr_ae ?_
      exact ae_restrict_of_forall_mem ((Ω ⊓ H).isOpen.measurableSet) fun z hz =>
        (planarReflection_of_nonneg _ _ hz.2.le).symm
    · exact (hu.mono (inter_subset_inter_left _ (hrΩ x)))
        |>.planarReflection_higherReflectionCoeff_ball hp x (r x)

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

/-- Off the real axis the representative is the precise representative of `u`: the reflection
agrees with `u` on the open upper half-plane. -/
theorem halfPlanePreciseRepresentative_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    halfPlanePreciseRepresentative u z = preciseRepresentative volume u z :=
  preciseRepresentative_congr_ae_nhds ((isOpen_lt continuous_const continuous_im).mem_nhds hz)
    (ae_restrict_of_forall_mem (measurableSet_lt measurable_const measurable_im) fun _ hw =>
      planarReflection_of_nonneg _ _ (le_of_lt hw))

variable [FiniteDimensional ℝ F]

/-- **Continuity up to the real axis.** For `2 < p`, the representative
`TauCeti.halfPlanePreciseRepresentative u` of `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` is continuous on
`Ω ∩ {0 ≤ im}`. -/
theorem MemWkpLoc.continuousOn_halfPlanePreciseRepresentative (hp : 2 < p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) :
    ContinuousOn (halfPlanePreciseRepresentative u) ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨V, hUV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection (one_le_two.trans hp.le)
  exact (hV.continuousOn_preciseRepresentative hp).mono hUV

/-- The representative `TauCeti.halfPlanePreciseRepresentative u` agrees with `u` almost
everywhere on `Ω ∩ {0 ≤ im}`. -/
theorem MemWkpLoc.ae_eq_halfPlanePreciseRepresentative (hp : 1 ≤ p)
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) :
    u =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] halfPlanePreciseRepresentative u := by
  obtain ⟨V, hUV, -, hV⟩ := hu.exists_opens_memWkpLoc_planarReflection hp
  have hU : MeasurableSet ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :=
    Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const measurable_im)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hUV
    (hV.memLpLoc.ae_eq_preciseRepresentative hp), ae_restrict_mem hU] with z hz hzU
  rw [halfPlanePreciseRepresentative, ← hz, planarReflection_of_nonneg _ _ hzU.2]

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

/-- At order one the reflection node is `-1`, so the node dilation is complex conjugation. -/
private theorem imDilation_higherReflectionNode_fin_one (j : Fin 1) (z : ℂ) :
    imDilation (higherReflectionNode j) z = conj z := by
  rw [Fin.fin_one_eq_zero j, imDilation_apply, higherReflectionNode_eq]
  apply Complex.ext <;> simp

omit [FiniteDimensional ℝ F] in
/-- Every weak derivative of a half-disc Sobolev map is locally `Lᵖ` up to the real axis: it
agrees with the one supplied by the definition off the axis, which is a null set. -/
private theorem memLpLoc_of_hasWeakFDerivOn_inter_setOf_im_nonneg
    (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 u) {D : ℂ → ℂ →L[ℝ] F}
    (hD : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) u D) :
    MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) D := by
  obtain ⟨-, D', hD', hD'p⟩ := memWkpLoc_succ_iff.1 hu
  have hset : ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im} : Set ℂ) =ᵐ[volume]
      (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) : Set ℂ) := by
    rw [Opens.coe_interior, interior_inter_setOf_im_nonneg Ω.isOpen]
    exact ae_eq_set_inter (ae_eq_refl _) (setOf_le_im_ae_eq 0)
  exact (memWkpLoc_zero_iff.1 hD'p).congr_ae
    (by rw [Measure.restrict_congr_set hset]; exact hD'.ae_eq hD)

/-- **The local Morrey inequality across the real axis.** Let `2 < p ≤ ∞` and `α = 1 - 2 / p`.
There is a constant `C > 0`, depending only on `p` and `F`, such that the following holds. Let
`Ω` be open and invariant under complex conjugation, let `u ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` with
weak derivative `D` on `Ω ∩ {0 < im}`, and let `x, y` be points with `closedBall x ρ ⊆ Ω`,
`ρ = 2 |x - y|`. Then the representative `u* = TauCeti.halfPlanePreciseRepresentative u` satisfies

`‖u*(x) - u*(y)‖ ≤ C ‖D‖_{Lᵖ((B(x, ρ) ∪ B(x̄, ρ)) ∩ {0 ≤ im})} |x - y|^α`.

The mirror disc `B(x̄, ρ)` enters because the even reflection samples the lower half of `B(x, ρ)`
at its conjugate points. -/
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
  have hDp := memLpLoc_of_hasWeakFDerivOn_inter_setOf_im_nonneg hu hD
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
      have := hΩ _ (hxy (show conj z ∈ closedBall x ρ by
        rwa [mem_closedBall, ← Complex.dist_conj_conj, Complex.conj_conj]))
      rwa [Complex.conj_conj] at this
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

/-! ### Continuity does not imply membership -/

/-- **The converse of Morrey's embedding fails on half-discs.** For `2 ≤ p`, the map
`z ↦ √(Im z)` is continuous on the closed half-disc and in `W^{1,p}_loc` of the open half-disc,
but not in `MemWkpLoc p (ball 0 1 ∩ {0 ≤ im}) 1`: its derivative `(2 √(Im z))⁻¹` is not `Lᵖ` up to
the real axis (`TauCeti.memWkpLoc_sqrt_im_iff`). -/
theorem exists_continuousOn_not_memWkpLoc_ball_inter_setOf_im_nonneg (hp : 2 ≤ p) :
    ∃ u : ℂ → ℝ, ContinuousOn u (ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) ∧
      MemWkpLoc p (ball (0 : ℂ) 1 ∩ {z | 0 < z.im}) 1 u ∧
      ¬ MemWkpLoc p (ball (0 : ℂ) 1 ∩ {z | 0 ≤ z.im}) 1 u :=
  ⟨fun z => √z.im, (by fun_prop : Continuous fun z : ℂ => √z.im).continuousOn,
    memWkpLoc_sqrt_im_ball_inter_im_pos, by rw [memWkpLoc_sqrt_im_iff]; exact not_lt.2 hp⟩

end TauCeti
