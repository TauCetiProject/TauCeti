/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.FirstJet
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# First jets of relative Poincaré primitives on a vector bundle and on a tube

Let `V → B` be a `C¹` real vector bundle, and let `P` be its relative Poincaré operator
(`TauCeti.vectorBundlePoincareHomotopy`), which integrates the time contraction of the pullback of
a form `η` by fibre scaling `(v, t) ↦ t • v`.

A preferred chart of the total space is a chart of the base followed by the fibre coordinate of a
local trivialization, so it is linear in the fibre and turns fibre scaling into the scaling
`(q, w) ↦ (q, t • w)` of the second coordinate
(`TauCeti.vectorBundleFiberScaling_extChartAt_symm`). Consequently, in every preferred chart of
the total space, `P` is the flat relative Poincaré operator `TauCeti.fiberwisePoincareHomotopy` of
the chart expression of `η` (`TauCeti.inChartAt_vectorBundlePoincareHomotopy`).

The flat operator has zero first jet along the zero section wherever its input is continuous and
vanishes there as a full ambient tensor
(`TauCeti.hasFDerivAt_fiberwisePoincareHomotopy_zeroSection`).
So if a continuous form `η` vanishes at the zero vector `0_b`, the chart expression of `P η` at
`0_b` has zero derivative at the chart point of `0_b`, within the range of the model
(`TauCeti.hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`), and outright
over a boundaryless base
(`TauCeti.hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`). Since `P η`
vanishes along the zero section for every form `η`
(`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), its value and first derivative both vanish
at `0_b`. For a closed `C¹` form `η` on a `C²` bundle over a `C²` base, vanishing as a full
ambient tensor along the whole zero section, `P η` is moreover a primitive of `η`
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`, whose correction term `ρ^* η` vanishes), so it
is a primitive with zero first jet along the zero section. Vanishing of `η` as a full ambient
tensor is needed here: vanishing of its restriction to the zero section alone does not make the
first jet of `P η` vanish.

Everything transports along a diffeomorphism `Φ` from the total space onto a manifold `M`, such as
a tubular neighbourhood of an embedded submanifold
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). With the zero-section inclusion
`i = Φ ∘ 0` and the retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹`, every closed `C^r` form `η` of positive
degree on `M`, with `r ≥ 1`, has a `C^r` form `β` with `d β = η - ρ^* η` that vanishes along
`i` as a full ambient tensor (`Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`), and
`d β = η` when `i^* η = 0` (`Diffeomorph.exists_isSmoothForm_relative_primitive`). This needs `Φ`
and the bundle to be `C^(r + 1)`. Since pullback along a `C¹` map preserves zero first jets
(`TauCeti.hasFDerivWithinAt_inChartAt_mpullback_of_apply_eq_zero`), `β` moreover has zero first
jet at every point of `i` where `η` vanishes as a full ambient tensor.

A primitive with zero first jet along a submanifold is the input to the relative Moser argument
which, for two symplectic forms agreeing on the full ambient tangent spaces along a compact
submanifold, produces a neighbourhood diffeomorphism fixing the submanifold whose differential is
the identity along it
(`TauCeti.SmoothTwoForm.exists_diffeomorph_fix_embedding_eventually_mpullback_eq`).

## Main results

* `TauCeti.inChartAt_vectorBundlePoincareHomotopy`: in a preferred chart of the total space, the
  relative Poincaré operator is the flat fibre-scaling operator of the chart expression.
* `TauCeti.hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`,
  `TauCeti.hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`: the relative
  Poincaré primitive of a form vanishing at `0_b` has zero first jet at `0_b`.
* `Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`,
  `Diffeomorph.exists_isSmoothForm_relative_primitive`: the relative Poincaré lemma on a tube,
  with primitives of zero first jet where the form vanishes along the core.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §§6–7 (the relative Poincaré lemma and Moser's relative theorem).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set Bundle Filter
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  [VectorBundle ℝ FV V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

section Chart

variable [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB]

/-- On the flat cylinder over the target of a preferred chart of the total space, the pullback of
`H^* η`, for fibre scaling `H`, is the pullback of the chart expression of `η` by the flat fibre
scaling `TauCeti.fiberScaling`: in the chart, `H` is that scaling. -/
private theorem mpullbackWithin_cylinderChart_mpullback_vectorBundleFiberScaling
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (p : TotalSpace FV V)
    {y : EB × FV} (hy : y ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) p).target) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    mpullbackWithin 𝓘(ℝ, (EB × FV) × ℝ) ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1))
      (cylinderChart (IB.prod 𝓘(ℝ, FV)) p)
      ((extChartAt (IB.prod 𝓘(ℝ, FV)) p).target ×ˢ Icc 0 1)
      (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
        (vectorBundleFiberScaling FV V) η) (y, t) =
      fiberScalingPullback (η.inChartAt p) (y, t) := by
  have hST : MapsTo fiberScaling ((extChartAt (IB.prod 𝓘(ℝ, FV)) p).target ×ˢ Icc 0 1)
      (extChartAt (IB.prod 𝓘(ℝ, FV)) p).target :=
    fun z hz ↦ (fiberScaling_apply z).symm ▸ smul_snd_mem_extChartAt_target p hz.1 z.2
  have hcomp : EqOn (vectorBundleFiberScaling FV V ∘ cylinderChart (IB.prod 𝓘(ℝ, FV)) p)
      ((extChartAt (IB.prod 𝓘(ℝ, FV)) p).symm ∘ fiberScaling)
      ((extChartAt (IB.prod 𝓘(ℝ, FV)) p).target ×ˢ Icc 0 1) := fun z hz ↦ by
    simp only [Function.comp_apply, cylinderChart_apply, fiberScaling_apply]
    rw [vectorBundleFiberScaling_extChartAt_symm p hz.1, projIcc_of_mem _ hz.2]
  have hyt : (y, t) ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) p).target ×ˢ Icc (0 : ℝ) 1 := ⟨hy, ht⟩
  have hu : UniqueDiffWithinAt ℝ ((extChartAt (IB.prod 𝓘(ℝ, FV)) p).target ×ˢ Icc (0 : ℝ) 1)
      (y, t) :=
    (uniqueDiffOn_extChartAt_target p).prod uniqueDiffOn_Icc_zero_one _ hyt
  rw [← mpullbackWithin_univ, ← mpullbackWithin_comp_at
    ((contMDiffOn_cylinderChart (n := 1) p subset_rfl _ hyt).mdifferentiableWithinAt
      one_ne_zero)
    ((contMDiff_vectorBundleFiberScaling (n := 1) _).mdifferentiableAt one_ne_zero
      |>.mdifferentiableWithinAt) (mapsTo_univ _ _) hu.uniqueMDiffWithinAt,
    mpullbackWithin_congr hcomp hyt]
  rw [mpullbackWithin_comp_apply_of_hasFDerivWithinAt
    ((contDiff_fiberScaling (r := 1)).differentiable one_ne_zero _).hasFDerivAt.hasFDerivWithinAt
    (mdifferentiableWithinAt_extChartAt_symm (hST hyt)) (hST.mono_right
      (extChartAt_target_subset_range p)) hu η, fiberScalingPullback_apply]
  congr 1
  ext v
  exact (mpullbackWithin_apply _ _ η _ v).trans (RoughForm.inChartAt_apply η p _ v).symm

/-- **The relative Poincaré operator in a chart.** In the preferred chart at any point `p` of the
total space of a vector bundle, the relative Poincaré operator of a form `η` is the flat relative
Poincaré operator `TauCeti.fiberwisePoincareHomotopy` of the chart expression of `η`, at every
point of the chart target. -/
theorem inChartAt_vectorBundlePoincareHomotopy
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (p : TotalSpace FV V)
    {y : EB × FV} (hy : y ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) p).target) :
    (vectorBundlePoincareHomotopy η).inChartAt p y =
      fiberwisePoincareHomotopy (η.inChartAt p) y := by
  rw [vectorBundlePoincareHomotopy_def,
    inChartAt_homotopyOperator p subset_rfl (uniqueDiffOn_extChartAt_target p) _ hy,
    fiberwisePoincareHomotopy_def]
  exact cylinderHomotopy_congr fun t ht ↦
    mpullbackWithin_cylinderChart_mpullback_vectorBundleFiberScaling η p hy ht

/-- **Zero first jet of the relative Poincaré primitive.** Let `η` be a continuous form on the
total space of a `C¹` vector bundle which vanishes, as a full ambient tensor, at the zero vector
`0_b`. In the preferred chart at `0_b`, the relative Poincaré primitive `P η` has zero derivative
within the range of the model at the chart point of `0_b`. Since `P η` also vanishes at `0_b`
(`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), its whole first jet vanishes there. -/
theorem hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η) {b : B} (hb : η (zeroSection FV V b) = 0) :
    HasFDerivWithinAt ((vectorBundlePoincareHomotopy η).inChartAt (zeroSection FV V b))
      (0 : (EB × FV) →L[ℝ] (EB × FV) [⋀^Fin k]→L[ℝ] F) (range (IB.prod 𝓘(ℝ, FV)))
      (extChartAt (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V b) (zeroSection FV V b)) := by
  have hx : extChartAt (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V b) (zeroSection FV V b) =
      (extChartAt IB b b, 0) :=
    extChartAt_zeroSection_of_mem_baseSet b (FiberBundle.mem_baseSet_trivializationAt' b)
  -- The range of the model of the total space is stable under scaling the fibre coordinate.
  have hscale : ∀ z ∈ range (IB.prod 𝓘(ℝ, FV)), ∀ t ∈ Icc (0 : ℝ) 1,
      (z.1, t • z.2) ∈ range (IB.prod 𝓘(ℝ, FV)) := fun z hz t _ ↦ by
    rw [ModelWithCorners.range_prod] at hz ⊢
    exact ⟨hz.1, by simp⟩
  have hcont : ContinuousWithinAt (η.inChartAt (zeroSection FV V b)) (range (IB.prod 𝓘(ℝ, FV)))
      (extChartAt IB b b, 0) :=
    hx ▸ (hη.contDiffWithinAt_inChartAt_self _).continuousWithinAt
  have hzero : η.inChartAt (zeroSection FV V b) (extChartAt IB b b, 0) = 0 :=
    hx ▸ (RoughForm.inChartAt_extChartAt_self η _).trans hb
  rw [hx]
  refine (hasFDerivWithinAt_fiberwisePoincareHomotopy_zeroSection hcont hzero hscale)
    |>.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hx ▸ extChartAt_target_mem_nhdsWithin (zeroSection FV V b)] with y hy
    exact inChartAt_vectorBundlePoincareHomotopy η _ hy
  · exact inChartAt_vectorBundlePoincareHomotopy η _
      (hx ▸ mem_extChartAt_target (zeroSection FV V b))

/-- **Zero first jet of the relative Poincaré primitive over a boundaryless base.** Let `η` be a
continuous form on the total space of a `C¹` vector bundle over a boundaryless base, vanishing as
a full ambient tensor at the zero vector `0_b`. In the preferred chart at `0_b`, the relative
Poincaré primitive `P η` has zero derivative at the chart point of `0_b`. -/
theorem hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection [IB.Boundaryless]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η) {b : B} (hb : η (zeroSection FV V b) = 0) :
    HasFDerivAt ((vectorBundlePoincareHomotopy η).inChartAt (zeroSection FV V b))
      (0 : (EB × FV) →L[ℝ] (EB × FV) [⋀^Fin k]→L[ℝ] F)
      (extChartAt (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V b) (zeroSection FV V b)) := by
  have h := hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection hη hb
  rwa [ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ] at h

end Chart

/-! ### Transport to a tube -/

section Tube

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : WithTop ℕ∞} [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB] [CompleteSpace F]

/-- **The relative Poincaré lemma on a tube.** Let `Φ` be a `C^n` diffeomorphism from the total
space of a `C^n` vector bundle onto `M`, such as a tubular neighbourhood, with zero-section
inclusion `i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Every closed `C^r`
form `η` of positive degree on `M`, with `1 ≤ r` and `r + 1 ≤ n`, has a `C^r` form `β` with
`d β = η - ρ^* η` that vanishes along `i` as a full ambient tensor. Moreover `β` has zero first
jet at every point of `i` where `η` vanishes as a full ambient tensor: its coordinate expression
in the chart at that point has zero derivative within the model range at its chart point. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧
      mextDeriv β = η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivWithinAt (β.inChartAt (Φ (zeroSection FV V b)))
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by rw [← one_add_one_eq_two]; gcongr) hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) h2).ne'
  have : IsManifold IB ((r : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle ((r : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have : IsManifold IB 2 B := .of_le h2
  have : ContMDiffVectorBundle 2 FV V IB := .of_le h2
  have hη₀ := hη.mpullback (Φ.contMDiff.of_le hn)
  have hβ₀ := hη₀.vectorBundlePoincareHomotopy
  refine ⟨mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm (vectorBundlePoincareHomotopy
    (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η)), hβ₀.mpullback (Φ.symm.contMDiff.of_le hn), ?_,
    fun b ↦ ?_, fun b hb ↦ ?_⟩
  · have hd := Φ.mdifferentiable hn0
    have hds := Φ.symm.mdifferentiable hn0
    have hZ := (contMDiff_zeroSection ℝ V (IB := IB) (F := FV) (n := 1)).mdifferentiable one_ne_zero
    have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
    rw [← mpullback_mextDeriv (Φ.symm.contMDiff.of_le h2)
        ((isSmoothBundleForm_def 1 _).mpr (hβ₀.of_le hr').contMDiff),
      mextDeriv_vectorBundlePoincareHomotopy (hη₀.of_le hr')
        (hη.of_le hr' |>.mextDeriv_mpullback_eq_zero hclosed (Φ.contMDiff.of_le h2)),
      mpullback_sub, mpullback_symm_mpullback hn0, ← mpullback_comp (hZ.comp hp) hd,
      ← mpullback_comp hds (hd.comp (hZ.comp hp))]
    -- Both retractions are `Φ ∘ 0 ∘ π ∘ Φ⁻¹`, associated differently.
    simp only [Function.comp_assoc]
  · exact mpullback_apply_eq_zero ((congrArg _ (Φ.symm_apply_apply _)).trans
      (vectorBundlePoincareHomotopy_zeroSection _ b))
  · -- The primitive on the total space has zero first jet at `0_b`, and pulling back along `Φ⁻¹`
    -- preserves this.
    have hx : Φ.symm (Φ (zeroSection FV V b)) = zeroSection FV V b := Φ.symm_apply_apply _
    have hη0 : mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η (zeroSection FV V b) = 0 :=
      mpullback_apply_eq_zero hb
    refine hasFDerivWithinAt_inChartAt_mpullback_of_apply_eq_zero
      ((Φ.symm.contMDiff.of_le (one_le_two.trans h2)).contMDiffAt) ?_ ?_
    · rw [hx]
      exact vectorBundlePoincareHomotopy_zeroSection _ b
    · rw [hx]
      exact hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection
        (hη₀.of_le (by simp)) hη0

omit [IsManifold I 2 M] [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB] [CompleteSpace F] in
/-- A form that restricts to zero along the zero-section inclusion `i = Φ ∘ 0` of a tube also
pulls back to zero along the retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image, since `ρ` factors
through `i` as `ρ = i ∘ (π ∘ Φ⁻¹)`. -/
theorem _root_.Diffeomorph.mpullback_retraction_eq_zero
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) (hn : n ≠ 0) {η : RoughForm I M F k}
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η = 0 := by
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  have hiΦ := (Φ.contMDiff.comp (contMDiff_zeroSection ℝ V (IB := IB) (F := FV))).mdifferentiable
    hn
  rw [← Function.comp_assoc (Φ : TotalSpace FV V → M) (zeroSection FV V),
    mpullback_comp (hp.comp (Φ.symm.mdifferentiable hn)) hiΦ, hi, mpullback_zero]

/-- **The relative Poincaré lemma on a tube**, for forms restricting to zero on the core. Let `Φ`
be a `C^n` diffeomorphism from the total space of a `C^n` vector bundle onto `M`, such as a
tubular neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Every closed `C^r` form `η` of
positive degree on `M` with `i^* η = 0`, where `1 ≤ r` and `r + 1 ≤ n`, is the exterior
derivative of a `C^r` form `β` that vanishes along `i` as a full ambient tensor, and has zero
first jet at every point of `i` where `η` vanishes as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivWithinAt (β.inChartAt (Φ (zeroSection FV V b)))
          (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F) (range I)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  obtain ⟨β, hβ, hdβ, hβ₀, hβ₁⟩ :=
    Φ.exists_isSmoothForm_mextDeriv_eq_sub_mpullback hr hn hη hclosed
  refine ⟨β, hβ, ?_, hβ₀, hβ₁⟩
  rw [hdβ, Φ.mpullback_retraction_eq_zero (lt_of_lt_of_le (by simp) hn).ne' hi, sub_zero]

end Tube

end TauCeti
