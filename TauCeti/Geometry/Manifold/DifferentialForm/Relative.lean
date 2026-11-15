/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.HomotopyOperator
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorBundle.FiberScaling
public import TauCeti.Analysis.Calculus.DifferentialForm.Relative.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Relative.FirstJet
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# The relative Poincaré lemma on the total space of a vector bundle

Let `V → B` be a smooth real vector bundle. Fibre scaling
`H : V × [0, 1] → V`, `(v, t) ↦ t • v` (`TauCeti.vectorBundleFiberScaling`), is a smooth homotopy
from the retraction `ρ = 0 ∘ π` of `V` onto its zero section to the identity, and it fixes the
zero section at all times. Applying the homotopy operator of the cylinder `V × [0, 1]` to `H^* η`
gives the *relative Poincaré operator* `P` (`TauCeti.vectorBundlePoincareHomotopy`)

`β = P η = h (H^* η)`, `β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH w₁, …, dH wₖ) dt`.

Since `H` is constant in time along the zero section, `dH ∂ₜ = 0` there, so `β` vanishes at
every point of the zero section as a full ambient tensor, for every form `η`
(`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), even when `η` does not. For a `C¹` form `η`
of positive degree, the cochain-homotopy identity of the homotopy operator gives

`d (P η) + P (d η) = η - ρ^* η`

(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`), so
`d β = η - ρ^* η` when `η` is closed (`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`), and
`ρ^* η = π^* (i^* η)` only depends on the restriction `i^* η` of `η` to the zero section `i`
(`TauCeti.mpullback_zeroSection_comp_proj`). Hence `d β = η` as soon as `i^* η = 0`
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero`), although `η`
need not vanish as a full ambient tensor along the zero section. The operator preserves `C^r`
regularity over a `C^(r + 1)` bundle (`TauCeti.IsSmoothForm.vectorBundlePoincareHomotopy`) and is
additive on continuous forms (`TauCeti.vectorBundlePoincareHomotopy_add`). The identities above
need only a `C²` bundle.

Everything transports along a diffeomorphism `Φ` from the total space onto a manifold `M`, such as
a tubular neighbourhood of an embedded submanifold
(`TauCeti.SmoothEmbedding.exists_isSmoothForm_relative_primitive`). With the zero-section inclusion
`i = Φ ∘ 0` and the retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹`, every closed `C^r` form `η` of positive
degree on `M`, with `r ≥ 1`, has a `C^r` form `β` with `d β = η - ρ^* η` that vanishes along
`i` as a full ambient tensor (`Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback`), and
`d β = η` when `i^* η = 0` (`Diffeomorph.exists_isSmoothForm_relative_primitive`). This needs `Φ`
and the bundle to be `C^(r + 1)`. This is the primitive used to compare two symplectic forms
relative to a submanifold.

The flat counterpart on an open set stable under scaling the normal coordinate is
`IsOpen.exists_contDiffOn_relative_primitive`. The base may have boundary or corners and the
coefficient space is any Banach space.

The two are related chart by chart. The preferred chart of the total space at any point is linear
on fibres, so it turns fibre scaling into the flat scaling `(q, p) ↦ (q, t • p)` of the fibre
coordinate, and the relative Poincaré operator read in that chart is the flat operator
`TauCeti.fiberwisePoincareHomotopy` of the chart expression of `η`
(`TauCeti.inChartAt_vectorBundlePoincareHomotopy`). The flat operator contracts with the normal
coordinate, which contributes a factor vanishing at the zero section, so over a boundaryless
base `β` has **zero first jet** at every zero vector `0_b` at which the continuous form `η`
vanishes as a full ambient tensor: its chart expression there has zero value and zero derivative
(`TauCeti.hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`). Vanishing of `i^* η`
alone does not give this. The first jet transports along `Φ`
(`Diffeomorph.exists_isSmoothForm_relative_primitive_hasFDerivAt_inChartAt`). When two symplectic
forms agree as full ambient tensors along a submanifold, the primitive of their difference
therefore has zero first jet there. This is what a relative Moser argument needs in order to
produce a diffeomorphism whose differential is the identity along the submanifold.

## Main declarations

* `TauCeti.vectorBundlePoincareHomotopy`: the relative Poincaré operator `β = h (H^* η)`.
* `TauCeti.vectorBundlePoincareHomotopy_zeroSection`: `β` vanishes along the zero section.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv`:
  `d (P η) + P (d η) = η - ρ^* η`.
* `TauCeti.mextDeriv_vectorBundlePoincareHomotopy`: `d β = η - ρ^* η` for closed `η`.
* `Diffeomorph.exists_isSmoothForm_relative_primitive`: the relative Poincaré lemma on a tube.
* `TauCeti.inChartAt_vectorBundlePoincareHomotopy`: in a bundle chart, `P` is the flat relative
  Poincaré operator.
* `TauCeti.hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection`: `β` has zero first jet
  wherever `η` vanishes along the zero section.
* `Diffeomorph.exists_isSmoothForm_relative_primitive_hasFDerivAt_inChartAt`: the relative
  Poincaré lemma on a tube with zero first jets.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, §6.2 (the relative Poincaré lemma by fibre scaling).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §4.
-/

public section

noncomputable section

open Set Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {B FV : Type*} {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup FV] [NormedSpace ℝ FV]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace FV V)] [FiberBundle FV V]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The relative Poincaré operator -/

/-- The **relative Poincaré operator** of a vector bundle: the homotopy operator of the cylinder
`V × [0, 1]` applied to the pullback of `η` by fibre scaling `H(v, t) = t • v`,

`β(v)(w₁, …, wₖ) = ∫₀¹ η(t • v)(dH ∂ₜ, dH (w₁, 0), …, dH (wₖ, 0)) dt`.

It vanishes along the zero section (`TauCeti.vectorBundlePoincareHomotopy_zeroSection`), and for a
closed `C¹` form `η`, `d β = η - ρ^* η` with `ρ` the retraction onto the zero section
(`TauCeti.mextDeriv_vectorBundlePoincareHomotopy`). -/
def vectorBundlePoincareHomotopy
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F k :=
  homotopyOperator
    (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) η)

/-- The relative Poincaré operator is the homotopy operator of the pullback by fibre scaling. -/
theorem vectorBundlePoincareHomotopy_def
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    vectorBundlePoincareHomotopy η =
      homotopyOperator (mpullback ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
        (vectorBundleFiberScaling FV V) η) :=
  (rfl)

/-- The relative Poincaré operator of the zero form is zero. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zero :
    vectorBundlePoincareHomotopy
      (0 : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) = 0 := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_zero, homotopyOperator_zero]

/-- The relative Poincaré operator commutes with real scalar multiplication of forms. -/
@[simp]
theorem vectorBundlePoincareHomotopy_smul (c : ℝ)
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) :
    vectorBundlePoincareHomotopy (c • η) = c • vectorBundlePoincareHomotopy η := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_smul, homotopyOperator_smul,
    vectorBundlePoincareHomotopy_def]

variable [VectorBundle ℝ FV V]

/-- **The relative Poincaré operator vanishes along the zero section**, as a full ambient tensor,
for every form `η`: fibre scaling kills the time direction there. -/
@[simp]
theorem vectorBundlePoincareHomotopy_zeroSection
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (b : B) :
    vectorBundlePoincareHomotopy η (zeroSection FV V b) = 0 :=
  homotopyOperator_apply_eq_zero fun t _ ↦ by
    rw [mpullback_apply]
    exact (η _).map_coord_zero 0 (mfderiv_vectorBundleFiberScaling_zeroSection_time b t _)

/-- The relative Poincaré operator is additive on continuous forms, over a `C¹` vector bundle on a
`C¹` base. -/
theorem vectorBundlePoincareHomotopy_add [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB]
    {η₁ η₂ : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (h₁ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η₁) (h₂ : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η₂) :
    vectorBundlePoincareHomotopy (η₁ + η₂) =
      vectorBundlePoincareHomotopy η₁ + vectorBundlePoincareHomotopy η₂ := by
  rw [vectorBundlePoincareHomotopy_def, mpullback_add,
    homotopyOperator_add (h₁.mpullback contMDiff_vectorBundleFiberScaling)
      (h₂.mpullback contMDiff_vectorBundleFiberScaling)]
  rfl

/-- The relative Poincaré operator preserves `C^r` regularity of forms, over a `C^(r + 1)` vector
bundle on a `C^(r + 1)` base. -/
theorem IsSmoothForm.vectorBundlePoincareHomotopy {r : ℕ∞} [IsManifold IB 1 B]
    [ContMDiffVectorBundle 1 FV V IB] [IsManifold IB (r + 1) B]
    [ContMDiffVectorBundle (r + 1) FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r η) :
    IsSmoothForm (IB.prod 𝓘(ℝ, FV)) r (vectorBundlePoincareHomotopy η) := by
  exact IsSmoothForm.homotopyOperator (hη.mpullback contMDiff_vectorBundleFiberScaling)

/-! ### The relative Poincaré operator in bundle charts -/

/-- In the preferred chart of the total space at any point, fibre scaling by `t` is the flat
scaling `(q, p) ↦ (q, t • p)` of the fibre coordinate, on the whole chart target. -/
private theorem vectorBundleFiberScaling_extChartAt_symm (x₀ : TotalSpace FV V) {y : EB × FV}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) x₀).target) (t : Icc (0 : ℝ) 1) :
    vectorBundleFiberScaling FV V ((extChartAt (IB.prod 𝓘(ℝ, FV)) x₀).symm y, t) =
      (extChartAt (IB.prod 𝓘(ℝ, FV)) x₀).symm (y.1, (t : ℝ) • y.2) := by
  rw [FiberBundle.extChartAt_target] at hy
  have hb := hy.1.2
  set e := trivializationAt FV V x₀.proj
  simp only [FiberBundle.extChartAt, PartialEquiv.coe_trans_symm, PartialEquiv.prod_symm,
    PartialEquiv.refl_symm, Function.comp_apply, PartialEquiv.prod_coe, PartialEquiv.refl_coe,
    id_eq, OpenPartialHomeomorph.coe_toPartialEquiv_symm, vectorBundleFiberScaling_apply]
  rw [← e.mk_symm hb, ← e.mk_symm hb]
  simp only [← e.symmₗ_apply (R := ℝ) hb, map_smul]

omit [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [VectorBundle ℝ FV V] in
/-- The fibre coordinate of the preferred chart of the total space can be scaled freely: the
chart target is a product with the whole fibre. -/
private theorem mk_smul_mem_extChartAt_target (x₀ : TotalSpace FV V) {y : EB × FV}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) x₀).target) (c : ℝ) :
    (y.1, c • y.2) ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) x₀).target := by
  rw [FiberBundle.extChartAt_target] at hy ⊢
  exact ⟨hy.1, mem_univ _⟩

variable [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB] in
/-- **The relative Poincaré operator in a bundle chart.** Read in the preferred chart of the total
space at any point, the relative Poincaré operator of a vector bundle is the flat relative
Poincaré operator `TauCeti.fiberwisePoincareHomotopy` of the chart expression of the form, on the
whole chart target. Indeed the chart is linear on fibres, so it turns fibre scaling into the flat
scaling `(q, p) ↦ (q, t • p)` of the fibre coordinate. No regularity of the form is needed. -/
theorem inChartAt_vectorBundlePoincareHomotopy
    (η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)) (x₀ : TotalSpace FV V)
    {y : EB × FV} (hy : y ∈ (extChartAt (IB.prod 𝓘(ℝ, FV)) x₀).target) :
    (vectorBundlePoincareHomotopy η).inChartAt x₀ y =
      fiberwisePoincareHomotopy (η.inChartAt x₀) y := by
  set e := extChartAt (IB.prod 𝓘(ℝ, FV)) x₀
  set S : Set ((EB × FV) × ℝ) := e.target ×ˢ Icc 0 1
  have hTu : UniqueDiffOn ℝ e.target := uniqueDiffOn_extChartAt_target x₀
  have hSu : UniqueDiffOn ℝ S := hTu.prod (uniqueDiffOn_Icc zero_lt_one)
  -- On the flat cylinder over the chart target, fibre scaling read in the chart is flat.
  have hflat : EqOn (e ∘ vectorBundleFiberScaling FV V ∘ cylinderChart (IB.prod 𝓘(ℝ, FV)) x₀)
      fiberScaling S := by
    rintro ⟨y', t'⟩ ⟨hy', ht'⟩
    simp only [Function.comp_apply, cylinderChart_apply, fiberScaling_apply]
    rw [vectorBundleFiberScaling_extChartAt_symm x₀ hy', projIcc_of_mem _ ht',
      e.right_inv (mk_smul_mem_extChartAt_target x₀ hy' t')]
  rw [vectorBundlePoincareHomotopy_def, inChartAt_homotopyOperator x₀ subset_rfl hTu _ hy]
  refine (cylinderHomotopy_apply _ y).trans ((intervalIntegral.integral_congr fun t ht ↦ ?_).trans
    (fiberwisePoincareHomotopy_apply _ y).symm)
  rw [uIcc_of_le zero_le_one] at ht
  have hyt : (y, t) ∈ S := ⟨hy, ht⟩
  have hcyl : MDifferentiableWithinAt 𝓘(ℝ, (EB × FV) × ℝ) ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1))
      (cylinderChart (IB.prod 𝓘(ℝ, FV)) x₀) S (y, t) :=
    ((contMDiffOn_cylinderChart (n := 1) x₀ subset_rfl) _ hyt).mdifferentiableWithinAt
      one_ne_zero
  have hH : MDifferentiableWithinAt ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV))
      (vectorBundleFiberScaling FV V) univ (cylinderChart (IB.prod 𝓘(ℝ, FV)) x₀ (y, t)) :=
    ((contMDiff_vectorBundleFiberScaling (n := 1) _).mdifferentiableAt one_ne_zero)
      |>.mdifferentiableWithinAt
  have hsrc : (vectorBundleFiberScaling FV V ∘ cylinderChart (IB.prod 𝓘(ℝ, FV)) x₀) (y, t) ∈
      e.source := by
    rw [Function.comp_apply, cylinderChart_apply, projIcc_of_mem _ ht,
      vectorBundleFiberScaling_extChartAt_symm x₀ hy]
    exact e.map_target (mk_smul_mem_extChartAt_target x₀ hy t)
  -- The pulled-back form on the flat cylinder is the flat pullback by fibre scaling.
  have hpull := mpullbackWithin_comp_at hcyl hH (mapsTo_univ _ _)
    (hSu _ hyt).uniqueMDiffWithinAt η
  rw [mpullbackWithin_univ] at hpull
  rw [← hpull, RoughForm.mpullbackWithin_eq_compContinuousLinearMap η x₀ hsrc (hH.comp _ hcyl
      (mapsTo_univ _ _)) (hSu _ hyt), fderivWithin_congr hflat (hflat hyt),
    (contDiff_fiberScaling (r := 1)).differentiable one_ne_zero (y, t) |>.fderivWithin
      (hSu _ hyt)]
  have hval : e ((vectorBundleFiberScaling FV V ∘ cylinderChart (IB.prod 𝓘(ℝ, FV)) x₀) (y, t)) =
      (y.1, t • y.2) := (hflat hyt).trans (fiberScaling_apply _)
  rw [hval]
  ext w
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.curryLeft_apply_apply]
  congr 1
  funext i
  cases i using Fin.cases <;> simp [fderiv_fiberScaling_apply, Prod.map]

omit [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)] [VectorBundle ℝ FV V] in
/-- The preferred chart of the total space sends the zero vector over `b` to the chart point of
`b` and the zero fibre coordinate. -/
private theorem extChartAt_zeroSection [∀ b, AddCommGroup (V b)] [∀ b, Module ℝ (V b)]
    [VectorBundle ℝ FV V] (b : B) :
    extChartAt (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V b) (zeroSection FV V b) =
      (extChartAt IB b b, 0) := by
  simp only [FiberBundle.extChartAt, PartialEquiv.coe_trans, Function.comp_apply,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq, zeroSection_proj,
    OpenPartialHomeomorph.coe_toPartialEquiv, Trivialization.coe_coe,
    (trivializationAt FV V b).zeroSection ℝ (mem_baseSet_trivializationAt FV V b)]

variable [IsManifold IB 1 B] [ContMDiffVectorBundle 1 FV V IB] in
/-- **The relative Poincaré operator has zero first jet along the zero section** at every point
where the form vanishes as a full ambient tensor: read in the preferred chart there, it has zero
value and zero derivative. Only continuity of the form is needed. Vanishing of the restriction of
`η` to the zero section does not suffice; the full tensor must vanish. -/
theorem hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection [IB.Boundaryless]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 0 η) {b : B} (hb : η (zeroSection FV V b) = 0) :
    HasFDerivAt ((vectorBundlePoincareHomotopy η).inChartAt (zeroSection FV V b))
      (0 : (EB × FV) →L[ℝ] (EB × FV) [⋀^Fin k]→L[ℝ] F)
      (extChartAt (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V b) (zeroSection FV V b)) := by
  set x₀ := zeroSection FV V b
  set e := extChartAt (IB.prod 𝓘(ℝ, FV)) x₀
  have hz₀ : e x₀ = (extChartAt IB b b, 0) := extChartAt_zeroSection b
  have hT : e.target ∈ 𝓝 (e x₀) := extChartAt_target_mem_nhds x₀
  rw [hz₀] at hT ⊢
  have hzero : η.inChartAt x₀ (extChartAt IB b b, 0) = 0 := by
    rw [← hz₀, RoughForm.inChartAt_extChartAt_self, hb]
    -- The zero alternating maps on the tangent space and on the model agree by definition.
    rfl
  have hflat := (hasFDerivWithinAt_fiberwisePoincareHomotopy_zeroSection
    ((hη.continuousOn_inChartAt x₀).continuousWithinAt (mem_of_mem_nhds hT)) hzero
    fun z hz t _ ↦ mk_smul_mem_extChartAt_target x₀ hz t).hasFDerivAt hT
  refine hflat.congr_of_eventuallyEq ?_
  filter_upwards [hT] with z hz
  exact inChartAt_vectorBundlePoincareHomotopy η x₀ hz

variable [CompleteSpace F]

/-- **The relative cochain-homotopy identity.** For a `C¹` form `η` of positive degree on the total
space of a `C²` vector bundle over a `C²` base, `d β + P (d η) = η - ρ^* η`, where `P` is the
relative Poincaré operator, `β = P η`, and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) :
    mextDeriv (vectorBundlePoincareHomotopy η) + vectorBundlePoincareHomotopy (mextDeriv η) =
      η - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η := by
  have hH : ContMDiff ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (IB.prod 𝓘(ℝ, FV)) 2
      (vectorBundleFiberScaling FV V) :=
    contMDiff_vectorBundleFiberScaling
  have hι (s : Icc (0 : ℝ) 1) : MDifferentiable (IB.prod 𝓘(ℝ, FV))
      ((IB.prod 𝓘(ℝ, FV)).prod (𝓡∂ 1)) (fun v : TotalSpace FV V ↦ (v, s)) :=
    mdifferentiable_id.prodMk mdifferentiable_const
  have h₁ : vectorBundleFiberScaling FV V ∘ (fun v ↦ (v, 1)) = id :=
    funext fun v ↦ vectorBundleFiberScaling_one v
  have h₀ : vectorBundleFiberScaling FV V ∘ (fun v ↦ (v, 0)) =
      zeroSection FV V ∘ TotalSpace.proj :=
    funext fun v ↦ vectorBundleFiberScaling_zero v
  funext v
  rw [Pi.add_apply, vectorBundlePoincareHomotopy_def, vectorBundlePoincareHomotopy_def,
    mpullback_mextDeriv hH ((isSmoothBundleForm_def 1 _).mpr hη.contMDiff),
    mextDeriv_homotopyOperator_add_homotopyOperator_mextDeriv
      (hη.mpullback (hH.of_le (by norm_num))),
    ← mpullback_comp_at (hι 1 v) (hH.mdifferentiable two_ne_zero _),
    ← mpullback_comp_at (hι 0 v) (hH.mdifferentiable two_ne_zero _), h₁, h₀, mpullback_id,
    Pi.sub_apply]

/-- **The relative Poincaré identity.** For a closed `C¹` form `η` of positive degree on the total
space of a `C²` vector bundle over a `C²` base, `d β = η - ρ^* η`, where `β` is the relative
Poincaré operator of `η` and `ρ = 0 ∘ π` is the retraction onto the zero section. -/
theorem mextDeriv_vectorBundlePoincareHomotopy [IsManifold IB 2 B]
    [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) =
      η - mpullback (IB.prod 𝓘(ℝ, FV)) (IB.prod 𝓘(ℝ, FV))
        (zeroSection FV V ∘ TotalSpace.proj) η := by
  rw [← mextDeriv_vectorBundlePoincareHomotopy_add_vectorBundlePoincareHomotopy_mextDeriv hη,
    hclosed, vectorBundlePoincareHomotopy_zero, add_zero]

/-- **The relative Poincaré lemma on the total space of a vector bundle.** If a closed `C¹` form
`η` of positive degree, on the total space of a `C²` vector bundle over a `C²` base, restricts to
zero on the zero section, then the relative Poincaré operator is a primitive of `η`, which
vanishes along the zero section as a full ambient tensor. The form `η` itself need not vanish as
an ambient tensor there. -/
theorem mextDeriv_vectorBundlePoincareHomotopy_of_mpullback_zeroSection_eq_zero
    [IsManifold IB 2 B] [ContMDiffVectorBundle 2 FV V IB]
    {η : RoughForm (IB.prod 𝓘(ℝ, FV)) (TotalSpace FV V) F (k + 1)}
    (hη : IsSmoothForm (IB.prod 𝓘(ℝ, FV)) 1 η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB (IB.prod 𝓘(ℝ, FV)) (zeroSection FV V) η = 0) :
    mextDeriv (vectorBundlePoincareHomotopy η) = η := by
  rw [mextDeriv_vectorBundlePoincareHomotopy hη hclosed, mpullback_zeroSection_comp_proj, hi,
    mpullback_zero, sub_zero]

/-! ### Transport to a tube -/

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {n : WithTop ℕ∞} [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB]

/-- The primitive on a tube: the relative Poincaré operator of the bundle, transported along `Φ`. -/
private def tubePrimitive (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M)
    (η : RoughForm I M F (k + 1)) : RoughForm I M F k :=
  mpullback I (IB.prod 𝓘(ℝ, FV)) Φ.symm
    (vectorBundlePoincareHomotopy (mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η))

omit [CompleteSpace F] in
private theorem isSmoothForm_tubePrimitive (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M)
    {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n) {η : RoughForm I M F (k + 1)}
    (hη : IsSmoothForm I r η) : IsSmoothForm I r (tubePrimitive Φ η) := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by rw [← one_add_one_eq_two]; gcongr) hn
  have : IsManifold IB ((r : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle ((r : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have : IsManifold IB 1 B := .of_le (one_le_two.trans h2)
  have : ContMDiffVectorBundle 1 FV V IB := .of_le (one_le_two.trans h2)
  exact (hη.mpullback (Φ.contMDiff.of_le hn)).vectorBundlePoincareHomotopy.mpullback
    (Φ.symm.contMDiff.of_le hn)

omit [CompleteSpace F] [IsManifold I 2 M] [IsManifold IB n B] [ContMDiffVectorBundle n FV V IB] in
private theorem tubePrimitive_zeroSection (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M)
    (η : RoughForm I M F (k + 1)) (b : B) : tubePrimitive Φ η (Φ (zeroSection FV V b)) = 0 :=
  mpullback_apply_eq_zero ((congrArg _ (Φ.symm_apply_apply _)).trans
    (vectorBundlePoincareHomotopy_zeroSection _ b))

private theorem mextDeriv_tubePrimitive (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M)
    {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n) {η : RoughForm I M F (k + 1)}
    (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    mextDeriv (tubePrimitive Φ η) =
      η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have h2 : (2 : WithTop ℕ∞) ≤ n := le_trans (by rw [← one_add_one_eq_two]; gcongr) hn
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by norm_num) h2).ne'
  have : IsManifold IB ((r : WithTop ℕ∞) + 1) B := .of_le hn
  have : ContMDiffVectorBundle ((r : WithTop ℕ∞) + 1) FV V IB := .of_le hn
  have : IsManifold IB 2 B := .of_le h2
  have : ContMDiffVectorBundle 2 FV V IB := .of_le h2
  have hη₀ := hη.mpullback (Φ.contMDiff.of_le hn)
  have hβ₀ := hη₀.vectorBundlePoincareHomotopy
  have hd := Φ.mdifferentiable hn0
  have hds := Φ.symm.mdifferentiable hn0
  have hZ := (contMDiff_zeroSection ℝ V (IB := IB) (F := FV) (n := 1)).mdifferentiable one_ne_zero
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  rw [tubePrimitive, ← mpullback_mextDeriv (Φ.symm.contMDiff.of_le h2)
      ((isSmoothBundleForm_def 1 _).mpr (hβ₀.of_le hr').contMDiff),
    mextDeriv_vectorBundlePoincareHomotopy (hη₀.of_le hr')
      (hη.of_le hr' |>.mextDeriv_mpullback_eq_zero hclosed (Φ.contMDiff.of_le h2)),
    mpullback_sub, mpullback_symm_mpullback hn0, ← mpullback_comp (hZ.comp hp) hd,
    ← mpullback_comp hds (hd.comp (hZ.comp hp))]
  -- Both retractions are `Φ ∘ 0 ∘ π ∘ Φ⁻¹`, associated differently.
  simp only [Function.comp_assoc]

private theorem mextDeriv_tubePrimitive_of_mpullback_eq_zero
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) : mextDeriv (tubePrimitive Φ η) = η := by
  have hn0 : n ≠ 0 := (lt_of_lt_of_le (by simp) hn).ne'
  have hp := (Bundle.contMDiff_proj (IB := IB) (n := 1) (F := FV) V).mdifferentiable one_ne_zero
  have hiΦ := (Φ.contMDiff.comp (contMDiff_zeroSection ℝ V (IB := IB) (F := FV))).mdifferentiable
    hn0
  rw [mextDeriv_tubePrimitive Φ hr hn hη hclosed,
    ← Function.comp_assoc (Φ : TotalSpace FV V → M) (zeroSection FV V),
    mpullback_comp (hp.comp (Φ.symm.mdifferentiable hn0)) hiΦ, hi, mpullback_zero, sub_zero]

/-- **The relative Poincaré lemma on a tube.** Let `Φ` be a `C^n` diffeomorphism from the total
space of a `C^n` vector bundle onto `M`, such as a tubular neighbourhood, with zero-section
inclusion `i = Φ ∘ 0` and retraction `ρ = Φ ∘ 0 ∘ π ∘ Φ⁻¹` onto its image. Every closed `C^r`
form `η` of positive degree on `M`, with `1 ≤ r` and `r + 1 ≤ n`, has a `C^r` form `β` with
`d β = η - ρ^* η` that vanishes along `i` as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_mextDeriv_eq_sub_mpullback
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧
      mextDeriv β = η - mpullback I I (Φ ∘ zeroSection FV V ∘ π FV V ∘ Φ.symm) η ∧
      ∀ b, β (Φ (zeroSection FV V b)) = 0 :=
  ⟨tubePrimitive Φ η, isSmoothForm_tubePrimitive Φ hr hn hη,
    mextDeriv_tubePrimitive Φ hr hn hη hclosed, tubePrimitive_zeroSection Φ η⟩

/-- **The relative Poincaré lemma on a tube**, for forms restricting to zero on the core. Let `Φ`
be a `C^n` diffeomorphism from the total space of a `C^n` vector bundle onto `M`, such as a
tubular neighbourhood, with zero-section inclusion `i = Φ ∘ 0`. Every closed `C^r` form `η` of
positive degree on `M` with `i^* η = 0`, where `1 ≤ r` and `r + 1 ≤ n`, is the exterior
derivative of a `C^r` form `β` that vanishes along `i` as a full ambient tensor. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      ∀ b, β (Φ (zeroSection FV V b)) = 0 :=
  ⟨tubePrimitive Φ η, isSmoothForm_tubePrimitive Φ hr hn hη,
    mextDeriv_tubePrimitive_of_mpullback_eq_zero Φ hr hn hη hclosed hi,
    tubePrimitive_zeroSection Φ η⟩

/-- **The relative Poincaré lemma on a tube with zero first jets.** Let `Φ` be a `C^n`
diffeomorphism from the total space of a `C^n` vector bundle onto `M`, such as a tubular
neighbourhood, with zero-section inclusion `i = Φ ∘ 0`, over boundaryless models. Every closed
`C^r` form `η` of positive degree on `M` with `i^* η = 0`, where `1 ≤ r` and `r + 1 ≤ n`, is the
exterior derivative of a `C^r` form `β` that vanishes along `i` as a full ambient tensor and has
zero first jet wherever `η` vanishes as a full ambient tensor: at such a point `Φ (0_b)`, the
coordinate expression of `β` in the preferred chart has zero derivative. Vanishing of `i^* η`
alone does not give the first jet. -/
theorem _root_.Diffeomorph.exists_isSmoothForm_relative_primitive_hasFDerivAt_inChartAt
    [IB.Boundaryless] [I.Boundaryless]
    (Φ : TotalSpace FV V ≃ₘ^n⟮IB.prod 𝓘(ℝ, FV), I⟯ M) {r : ℕ∞} (hr : 1 ≤ r) (hn : r + 1 ≤ n)
    {η : RoughForm I M F (k + 1)} (hη : IsSmoothForm I r η) (hclosed : mextDeriv η = 0)
    (hi : mpullback IB I (Φ ∘ zeroSection FV V) η = 0) :
    ∃ β : RoughForm I M F k, IsSmoothForm I r β ∧ mextDeriv β = η ∧
      (∀ b, β (Φ (zeroSection FV V b)) = 0) ∧
      ∀ b, η (Φ (zeroSection FV V b)) = 0 →
        HasFDerivAt (β.inChartAt (Φ (zeroSection FV V b))) (0 : E →L[ℝ] E [⋀^Fin k]→L[ℝ] F)
          (extChartAt I (Φ (zeroSection FV V b)) (Φ (zeroSection FV V b))) := by
  have h1 : (1 : WithTop ℕ∞) ≤ n := le_add_self.trans hn
  have : IsManifold IB 1 B := .of_le h1
  have : ContMDiffVectorBundle 1 FV V IB := .of_le h1
  have : IsManifold I 1 M := .of_le one_le_two
  refine ⟨tubePrimitive Φ η, isSmoothForm_tubePrimitive Φ hr hn hη,
    mextDeriv_tubePrimitive_of_mpullback_eq_zero Φ hr hn hη hclosed hi,
    tubePrimitive_zeroSection Φ η, fun b hb ↦ ?_⟩
  -- The bundle primitive has zero first jet at the zero vector over `b`, and pulling back along
  -- `Φ⁻¹`, which sends `Φ (0_b)` to `0_b`, keeps it.
  have hsymm : Φ.symm (Φ (zeroSection FV V b)) = zeroSection FV V b := Φ.symm_apply_apply _
  have hΦη : mpullback (IB.prod 𝓘(ℝ, FV)) I Φ η (zeroSection FV V b) = 0 :=
    mpullback_apply_eq_zero hb
  have hjet := hasFDerivAt_inChartAt_vectorBundlePoincareHomotopy_zeroSection
    ((hη.of_le (by simp)).mpullback (Φ.contMDiff.of_le h1)) hΦη
  refine RoughForm.hasFDerivAt_inChartAt_mpullback_of_eq_zero
    (Φ.symm.contMDiff.of_le h1).contMDiffAt ?_ ?_
  · rw [hsymm]
    exact vectorBundlePoincareHomotopy_zeroSection _ b
  · rw [hsymm]
    exact hjet

end TauCeti
