/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Reflection
import TauCeti.Analysis.Sobolev.WeakDeriv.ImDilation
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Bounds for all derivatives of the half-disc reflection

The higher-order reflection `TauCeti.planarReflection d g` of a map `g` on `Ω ∩ {0 ≤ im}` is
bounded in `Lᵖ(Ω)` by `TauCeti.planarReflectionBound d p` times the `Lᵖ(Ω ∩ {0 ≤ im})` norm of `g`
(`TauCeti.eLpNorm_planarReflection_le`). This file proves the same bound, with the same constant,
for weak derivatives of every order: whatever weak derivatives `D^i (planarReflection d g)` on `Ω`
and `D^i g` on `Ω ∩ {0 < im}` are chosen,

`‖D^i (planarReflection d g)‖_{Lᵖ(Ω)} ≤ planarReflectionBound d p * ‖D^i g‖_{Lᵖ(Ω ∩ {0 ≤ im})}`.

The bound is packaged by the predicate `TauCeti.WeakDerivChainLe` of
`TauCeti.Analysis.Sobolev.Local.Basic`, which compares chains of weak derivatives level by level.
Below the real axis the reflection is `∑ j, d j • g ∘ σ j` for the node dilations
`σ j = imDilation (higherReflectionNode j)`, so by the weak chain rule
(`TauCeti.HasWeakFDerivOn.comp_imDilation`) its `i`th weak derivative is `∑ j, d j • (D^i g ∘ σ j)`
with every slot precomposed with `σ j`. The nodes lie in `[-1, 0)`, so every `σ j` is a
contraction and the precomposition does not increase operator norms: the weights, and hence the
constant, are the same at every order. Above the axis the
derivatives of the reflection are those of `g`, by uniqueness of weak derivatives.

With the Vandermonde weights the constant is `TauCeti.higherReflectionBound k p`, and together with
`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff` this is the extension of a
`W^{k,p}` map on a half-disc to a `W^{k,p}` map on the disc with a bound
(`TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball_bound`).

## Main declarations

* `TauCeti.weakDerivChainLe_planarReflection`: the all-order bound for the reflection with
  arbitrary weights.
* `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_bound` and
  `TauCeti.MemWkpLoc.planarReflection_higherReflectionCoeff_ball_bound`: the packaged extension
  with its bound.

## References

* R. A. Adams, J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 5.19 (extension by higher
  order reflection).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Complex
open scoped ENNReal

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Reflections up to contractions -/

/-- The node dilations are contractions. -/
private theorem norm_imDilation_higherReflectionNode_le {k : ℕ} (j : Fin k) :
    ‖imDilation (higherReflectionNode j)‖ ≤ 1 := by
  have hn : |higherReflectionNode j| ≤ 1 := by
    rw [higherReflectionNode_eq, abs_neg, abs_inv, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by simp)
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    simpa using norm_imDilation_le hn w

variable {k : ℕ} {d : Fin k → ℝ}

/-- `f` is the reflection of `g` with weights `d` up to contractions: almost everywhere on the
upper part of `Ω` it is `g`, and almost everywhere on the lower part it is
`∑ j, d j • T j (g (σ j z))` for linear maps `T j` of norm at most one. The iterated weak
derivatives of the reflection keep this form, with `T j` replaced by precomposition with `σ j`. -/
private def IsContractedReflection (Ω : Opens ℂ) (d : Fin k → ℝ) (f g : ℂ → F) : Prop :=
  (∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z : ℂ | 0 < z.im}), f z = g z) ∧
    ∃ T : Fin k → F →L[ℝ] F, (∀ j, ‖T j‖ ≤ 1) ∧
      ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z : ℂ | z.im < 0}),
        f z = ∑ j, d j • T j (g (imDilation (higherReflectionNode j) z))

/-- The reflection itself, with `T j` the identity. -/
private theorem isContractedReflection_planarReflection (Ω : Opens ℂ) (d : Fin k → ℝ)
    (g : ℂ → F) : IsContractedReflection Ω d (planarReflection d g) g :=
  ⟨ae_restrict_of_forall_mem
      (Ω.isOpen.measurableSet.inter (measurableSet_lt measurable_const measurable_im)) fun _ hz =>
      planarReflection_of_nonneg _ _ (le_of_lt hz.2),
    fun _ => ContinuousLinearMap.id ℝ F, fun _ => ContinuousLinearMap.norm_id_le,
    ae_restrict_of_forall_mem
      (Ω.isOpen.measurableSet.inter (measurableSet_lt measurable_im measurable_const)) fun _ hz =>
      planarReflection_of_neg _ _ hz.2⟩

/-- **The `Lᵖ` bound up to contractions.** A reflection up to contractions is bounded in `Lᵖ(Ω)` by
`planarReflectionBound d p` times the `Lᵖ(Ω ∩ {0 ≤ im})` norm of `g`. -/
private theorem IsContractedReflection.eLpNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {f g : ℂ → F} (h : IsContractedReflection Ω d f g)
    (hfm : AEStronglyMeasurable f (volume.restrict Ω)) :
    eLpNorm f p (volume.restrict Ω) ≤
      planarReflectionBound d p * eLpNorm g p (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) := by
  obtain ⟨hup, T, hT, hlo⟩ := h
  have hup' := (ae_restrict_iff'
    (Ω.isOpen.measurableSet.inter (measurableSet_lt measurable_const measurable_im))).1 hup
  have hlo' := (ae_restrict_iff'
    (Ω.isOpen.measurableSet.inter (measurableSet_lt measurable_im measurable_const))).1 hlo
  have hax : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ {z : ℂ | z.im = 0} :=
    measure_eq_zero_iff_ae_notMem.1 (volume_setOf_im_eq 0)
  -- Pointwise, `‖f‖` is dominated by the reflection of `‖g‖` with the weights `|d j|`.
  have hle : ∀ᵐ z ∂volume.restrict Ω,
      ‖f z‖ ≤ ‖planarReflection (fun j => |d j|) (fun w => ‖g w‖) z‖ := by
    refine (ae_restrict_iff' Ω.isOpen.measurableSet).2 ?_
    filter_upwards [hup', hlo', hax] with z h1 h2 h3 hz
    rcases lt_or_gt_of_ne h3 with hneg | hpos
    · rw [planarReflection_of_neg _ _ hneg, h2 ⟨hz, hneg⟩]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (le_abs_self _))
      rw [norm_smul, Real.norm_eq_abs, smul_eq_mul]
      gcongr
      exact ((T j).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (hT j))
    · rw [planarReflection_of_nonneg _ _ hpos.le, h1 ⟨hz, hpos⟩, norm_norm]
  calc eLpNorm f p (volume.restrict Ω)
      ≤ eLpNorm (planarReflection (fun j => |d j|) (fun w => ‖g w‖)) p (volume.restrict Ω) :=
        eLpNorm_mono_ae hfm hle
    _ ≤ planarReflectionBound (fun j => |d j|) p *
          eLpNorm (fun w => ‖g w‖) p (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) :=
        eLpNorm_planarReflection_le hp hΩ _ _
    _ ≤ _ := by
      rw [planarReflectionBound_abs]
      gcongr
      by_cases hg : AEStronglyMeasurable g (volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
      · rw [eLpNorm_norm _ hg]
      · simp [eLpNorm_of_not_aestronglyMeasurable hg]

/-- **Weak derivatives of a reflection up to contractions.** If `f` is a reflection of `g` up to
contractions, then every weak derivative of `f` on `Ω` is a reflection up to contractions of every
weak derivative of `g` on `Ω ∩ {0 < im}`, with the same weights. -/
private theorem IsContractedReflection.weakFDeriv {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {f g : ℂ → F} (h : IsContractedReflection Ω d f g) {Df Dg : ℂ → ℂ →L[ℝ] F}
    (hf : HasWeakFDerivOn volume Ω f Df)
    (hg : HasWeakFDerivOn volume (Opens.interior ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) g Dg) :
    IsContractedReflection Ω d Df Dg := by
  have := hf.completeSpace
  obtain ⟨hup, T, hT, hlo⟩ := h
  let Up : Opens ℂ := ⟨(Ω : Set ℂ) ∩ {z : ℂ | 0 < z.im},
    Ω.isOpen.inter (isOpen_lt continuous_const continuous_im)⟩
  let Lo : Opens ℂ := ⟨(Ω : Set ℂ) ∩ {z : ℂ | z.im < 0},
    Ω.isOpen.inter (isOpen_lt continuous_im continuous_const)⟩
  have hgU : HasWeakFDerivOn volume Up g Dg := hg.mono fun z hz => by
    rw [← SetLike.mem_coe, Opens.coe_interior, interior_inter_setOf_im_nonneg Ω.isOpen]
    exact hz
  have hUp : Up ≤ Ω := SetLike.coe_subset_coe.1 inter_subset_left
  have hLo : Lo ≤ Ω := SetLike.coe_subset_coe.1 inter_subset_left
  refine ⟨(hf.mono hUp).ae_eq (hgU.congr_ae ?_), ?_⟩
  · exact hup.mono fun _ hz => hz.symm
  -- Below the axis, differentiate `∑ j, d j • T j (g (σ j z))` by the weak chain rule.
  let T' : Fin k → (ℂ →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] F := fun j =>
    (ContinuousLinearMap.compL ℝ ℂ F F (T j)).comp
      ((ContinuousLinearMap.compL ℝ ℂ ℂ F).flip (imDilation (higherReflectionNode j)))
  have hT'apply (j : Fin k) (L : ℂ →L[ℝ] F) :
      T' j L = (T j).comp (L.comp (imDilation (higherReflectionNode j))) := rfl
  refine ⟨T', fun j => ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_, ?_⟩
  · rw [hT'apply, one_mul]
    calc ‖(T j).comp (L.comp (imDilation (higherReflectionNode j)))‖
        ≤ ‖T j‖ * (‖L‖ * ‖imDilation (higherReflectionNode j)‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖L‖ * 1) := by
          gcongr
          · exact hT j
          · exact norm_imDilation_higherReflectionNode_le j
      _ = ‖L‖ := by ring
  have hmaps (j : Fin k) : MapsTo (imDilation (higherReflectionNode j)) Lo Up := fun z hz =>
    ⟨hΩ z hz.1 hz.2 j, by
      simpa [imDilation_apply_im] using mul_pos_of_neg_of_neg (higherReflectionNode_neg j) hz.2⟩
  have hj (j : Fin k) : HasWeakFDerivOn volume Lo
      (fun z => d j • T j (g (imDilation (higherReflectionNode j) z)))
      (fun z => d j • T' j (Dg (imDilation (higherReflectionNode j) z))) :=
    (((HasWeakFDerivOn.comp_imDilation (higherReflectionNode_ne_zero j) hgU
      (hmaps j)).clm_comp (T j)).const_smul (d j))
  have hsum := HasWeakFDerivOn.sum Finset.univ fun j _ => hj j
  exact (hf.mono hLo).ae_eq (hsum.congr_ae (hlo.mono fun _ hz => hz.symm))

/-! ### The bound for all derivatives -/

/-- **The reflection bounds all derivatives.** For `1 ≤ p` and any weights `d`, every iterated weak
derivative of `planarReflection d g` on `Ω` is bounded in `Lᵖ(Ω)` by `planarReflectionBound d p`
times the `Lᵖ(Ω ∩ {0 ≤ im})` norm of the corresponding iterated weak derivative of `g` on
`Ω ∩ {0 < im}`, at every order and for every choice of these derivatives. No moment condition on
the weights is needed: it is what makes the derivatives exist
(`TauCeti.MemWkpLoc.planarReflection`), not what bounds them. -/
theorem weakDerivChainLe_planarReflection {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    (d : Fin k → ℝ) (g : ℂ → F) (m : ℕ) :
    WeakDerivChainLe p Ω ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (planarReflectionBound d p) m
      (planarReflection d g) g := by
  -- The derivatives are reflections up to contractions, measurable by local integrability.
  have key : ∀ (m : ℕ) {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] (f g : ℂ → F),
      IsContractedReflection Ω d f g → AEStronglyMeasurable f (volume.restrict Ω) →
        WeakDerivChainLe p Ω ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (planarReflectionBound d p) m f g := by
    intro m
    induction m with
    | zero => exact fun f g h hfm => weakDerivChainLe_zero_iff.2 (h.eLpNorm_le hp hΩ hfm)
    | succ m ih =>
      intro F _ _ f g h hfm
      refine weakDerivChainLe_succ_iff.2 ⟨h.eLpNorm_le hp hΩ hfm, fun Df Dg hf hg => ?_⟩
      rw [Opens.interior_coe] at hf
      exact ih Df Dg (h.weakFDeriv hΩ hf hg) hf.locallyIntegrableOn_deriv.aestronglyMeasurable
  cases m with
  | zero => exact weakDerivChainLe_zero_iff.2 (eLpNorm_planarReflection_le hp hΩ d g)
  | succ m =>
    refine weakDerivChainLe_succ_iff.2
      ⟨eLpNorm_planarReflection_le hp hΩ d g, fun Df Dg hf hg => ?_⟩
    rw [Opens.interior_coe] at hf
    exact key m Df Dg ((isContractedReflection_planarReflection Ω d g).weakFDeriv hΩ hf hg)
      hf.locallyIntegrableOn_deriv.aestronglyMeasurable

/-- **Higher-order reflection extends half-disc Sobolev maps with a bound.** A map `u` in
`W^{k,p}_loc(Ω ∩ {0 ≤ im})` extends by the order-`k` reflection with the Vandermonde weights to a
map in `W^{k,p}_loc(Ω)`, and every iterated weak derivative of the extension of order at most `k`
is bounded in `Lᵖ(Ω)` by `higherReflectionBound k p` times the `Lᵖ(Ω ∩ {0 ≤ im})` norm of the
corresponding derivative of `u`. -/
theorem MemWkpLoc.planarReflection_higherReflectionCoeff_bound {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Opens ℂ}
    (hΩ : ∀ z ∈ Ω, z.im < 0 → ∀ j : Fin k, imDilation (higherReflectionNode j) z ∈ Ω)
    {u : ℂ → F} (hu : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p Ω k (TauCeti.planarReflection (higherReflectionCoeff k) u) ∧
      WeakDerivChainLe p Ω ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) (higherReflectionBound k p) k
        (TauCeti.planarReflection (higherReflectionCoeff k) u) u := by
  refine ⟨hu.planarReflection_higherReflectionCoeff hp hΩ, ?_⟩
  rw [← planarReflectionBound_higherReflectionCoeff]
  exact weakDerivChainLe_planarReflection hp hΩ _ u k

/-- **Extension from a half-disc to the disc, with a bound.** For a disc `D` centred on the real
axis, a map `u` in `W^{k,p}_loc(D ∩ {0 ≤ im})` extends by the order-`k` higher reflection to a map
in `W^{k,p}_loc(D)` whose iterated weak derivatives of order at most `k` are bounded in `Lᵖ(D)` by
`higherReflectionBound k p` times the `Lᵖ(D ∩ {0 ≤ im})` norms of those of `u`. -/
theorem MemWkpLoc.planarReflection_higherReflectionCoeff_ball_bound {p : ℝ≥0∞} (hp : 1 ≤ p)
    (x r : ℝ) {u : ℂ → F} (hu : MemWkpLoc p (Metric.ball (x : ℂ) r ∩ {z | 0 ≤ z.im}) k u) :
    MemWkpLoc p (Metric.ball (x : ℂ) r) k (TauCeti.planarReflection (higherReflectionCoeff k) u) ∧
      WeakDerivChainLe p (Metric.ball (x : ℂ) r) (Metric.ball (x : ℂ) r ∩ {z | 0 ≤ z.im})
        (higherReflectionBound k p) k (TauCeti.planarReflection (higherReflectionCoeff k) u) u :=
  MemWkpLoc.planarReflection_higherReflectionCoeff_bound (Ω := ⟨_, Metric.isOpen_ball⟩) hp
    (fun _ hz _ j => imDilation_higherReflectionNode_mem_ball x r j hz) hu

end TauCeti
