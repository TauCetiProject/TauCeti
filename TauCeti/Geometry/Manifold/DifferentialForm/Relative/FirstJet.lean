/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Relative.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.FirstJet
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.VectorBundle.Submersion

/-!
# First jets of relative Poincaré primitives on a vector bundle

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

The same holds on a tube: for a diffeomorphism `Φ` from the total space onto a manifold `M`,
such as a tubular neighbourhood, the transported primitive `(Φ⁻¹)^* P (Φ^* η)` of a continuous
form `η` vanishing at `Φ(0_b)` has zero first jet at `Φ(0_b)`
(`Diffeomorph.hasFDerivAt_inChartAt_mpullback_symm_vectorBundlePoincareHomotopy`), because
pullback along a `C¹` map preserves zero first jets
(`TauCeti.RoughForm.hasFDerivAt_inChartAt_mpullback`).

A primitive with zero first jet along a submanifold is the input to the relative Moser argument
which, for two symplectic forms agreeing on the full ambient tangent spaces along a compact
submanifold, produces a neighbourhood diffeomorphism fixing the submanifold whose differential is
the identity along it.

## Main results

* `TauCeti.inChartAt_vectorBundlePoincareHomotopy`: in a preferred chart of the total space, the
  relative Poincaré operator is the flat fibre-scaling operator of the chart expression.
* `TauCeti.hasFDerivWithinAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`,
  `TauCeti.hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`: the relative
  Poincaré primitive of a form vanishing at `0_b` has zero first jet at `0_b`.
* `Diffeomorph.hasFDerivAt_inChartAt_mpullback_symm_vectorBundlePoincareHomotopy`: the same for the
  primitive transported to a tube.

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

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n : WithTop ℕ∞}

/-- **Zero first jet of the relative Poincaré primitive on a tube.** Let `Φ` be a `C^n`
diffeomorphism, `n ≥ 1`, from the total space of a `C¹` vector bundle onto `M`, over boundaryless
models, and let `η` be a continuous form on `M` vanishing at `Φ(0_b)` as a full ambient tensor.
Then the transported relative Poincaré primitive `(Φ⁻¹)^* P (Φ^* η)` has zero derivative, in the
preferred chart at `Φ(0_b)`, at the chart point of `Φ(0_b)`; since it also vanishes there, its
whole first jet vanishes at `Φ(0_b)`. -/
theorem _root_.Diffeomorph.hasFDerivAt_inChartAt_mpullback_symm_vectorBundlePoincareHomotopy
    [IB.Boundaryless] [I.Boundaryless] (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M)
    (hn : 1 ≤ n) {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I 0 η) {b : B}
    (hb : η (Φ (zeroSection FV V b)) = 0) :
    HasFDerivAt ((mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm
        (vectorBundlePoincareHomotopy (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η))).inChartAt
          (Φ (zeroSection FV V b)))
      (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
      (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  have hη₀ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η) :=
    hη.mpullback (Φ.contMDiff.of_le (by simpa using hn))
  have h := hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection hη₀
    (mpullback_apply_eq_zero hb)
  rw [← Φ.symm_apply_apply (zeroSection FV V b)] at h
  refine RoughForm.hasFDerivAt_inChartAt_mpullback (Φ.symm.contMDiff.of_le hn).contMDiffAt h ?_
  rw [Φ.symm_apply_apply]
  exact vectorBundlePoincareHomotopy_zeroSection _ b

end TauCeti
