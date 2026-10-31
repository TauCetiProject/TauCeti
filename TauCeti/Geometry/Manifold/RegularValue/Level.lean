/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Geometry.Manifold.ModelTransport.Immersion
public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Manifold

import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.PullbackGroupoid
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# Regular levels of maps into finite-dimensional spaces

Let `f : M → F` be a map from a boundaryless manifold modelled on a finite-dimensional real space
`E` to a finite-dimensional real normed space `F`.
Suppose `f` is `C¹` at every point of the level `f⁻¹(c)` and `c` is a regular value of `f`. Then
the actual subtype `{x // f x = c}` carries the atlas `TauCeti.regularLevelChartedSpace`, modelled
on `Fin n → ℝ` for `n = dim E - dim F`, and is a `C^m` manifold when `f` is `C^m` at the points
of the level, `m ≥ 1` (`TauCeti.isManifold_regularLevel`). No Hausdorff or second-countability
hypothesis is used, and the level may be empty. When it is nonempty, regularity forces
`dim F ≤ dim E`, so the natural-number subtraction is exact. The model dimension is a parameter
`n` together with a proof of `dim E - dim F = n`, so that special cases can fix a convenient
expression for it: for scalar functions, `F = ℝ`, users take `n = dim E - 1`, with the proof
`by rw [finrank_self]`.

The atlas is the section-zero atlas `TauCeti.sectionZeroChartedSpace` of the section `f - c` of
the trivial bundle with fibre `F` over the self-modelled copy `TauCeti.BoundarylessModel I M`,
transported to `f⁻¹(c)` along the identity of points. The trivialization coordinate of this
section is `f - c` itself, and the linearization at `x` is the derivative

`D_x = fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x)`

of `f` in the preferred extended chart. Writing `π_x` for the chosen projection of `E` onto
`ker D_x` and `K_x : ker D_x ≃ (Fin n → ℝ)` for the index-model identification, the preferred
chart at `x` is

`w ↦ K_x (π_x (extChartAt I x w - extChartAt I x x))`

(`TauCeti.regularLevelChartAt_apply`). Its inverse is the inverse preferred extended chart of `M`
applied to the inverse implicit-function chart of `f - c` on the zero slice
(`TauCeti.coe_regularLevelChartAt_symm_apply`).

For this atlas the level is an embedded submanifold: the inclusion `{x // f x = c} → M` is a
`C^m` immersion with complement `F` and a topological embedding, hence a smooth embedding
(`TauCeti.isSmoothEmbedding_coe_regularLevel`), and its differential at `x` has range
`ker (mfderiv I 𝓘(ℝ, F) f x)` (`TauCeti.range_mfderiv_coe_regularLevel`).

## Main declarations

* `TauCeti.regularLevelChartAt` and `TauCeti.regularLevelChartedSpace`: the preferred charts and
  the atlas of a regular level.
* `TauCeti.regularLevelChartAt_apply`, `TauCeti.regularLevelChartAt_source`,
  `TauCeti.regularLevelChartAt_symm_zero`, `TauCeti.mem_regularLevelChartAt_target_iff` and
  `TauCeti.coe_regularLevelChartAt_symm_apply`: the chart formulas.
* `TauCeti.isManifold_regularLevel`: the level is a manifold of dimension `dim E - dim F`.
* `TauCeti.isImmersionOfComplement_coe_regularLevel` and
  `TauCeti.isSmoothEmbedding_coe_regularLevel`: the inclusion of the level is an immersion with
  complement `F` and a smooth embedding.
* `TauCeti.range_mfderiv_coe_regularLevel`: the tangent space of the level at `x` is the kernel of
  the differential of `f` at `x`.
* `TauCeti.ker_mfderiv_eq_of_forall_eq_imp`: two defining maps of a regular level have the same
  tangent kernels along it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Corollary 5.14 (regular level sets) and Proposition 5.38 (their tangent
  spaces).
-/

public section

open Bundle Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

/-! ### The section-zero data of a regular level -/

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [NormedAddCommGroup F] {f : M → F} {c : F}

namespace RegularLevel

variable (I f c) in
/-- The section `f - c` of the trivial bundle with fibre `F` over the base point `0`, on the
self-modelled copy of `M`. -/
private noncomputable def sec (y : BoundarylessModel I M) :
    Bundle.Trivial ℝ F ((fun _ ↦ (0 : ℝ)) y) :=
  f ((BoundarylessModel.homeomorph I M).symm y) - c

variable (I f c) in
/-- The zero set of `f - c` on the self-modelled copy is the level `f⁻¹(c)`. -/
private noncomputable def zeroHomeomorph :
    ↥{y : BoundarylessModel I M | sec I f c y = 0} ≃ₜ {x : M // f x = c} :=
  (BoundarylessModel.homeomorph I M).symm.subtype fun y ↦ by
    rw [mem_ofPred_eq, sec, sub_eq_zero]

private theorem coe_zeroHomeomorph (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    (zeroHomeomorph I f c z : M) = (BoundarylessModel.homeomorph I M).symm z.1 :=
  (rfl)

private theorem coe_zeroHomeomorph_symm (x : {x : M // f x = c}) :
    ((zeroHomeomorph I f c).symm x).1 = BoundarylessModel.homeomorph I M x.1 :=
  (rfl)

variable [I.Boundaryless] [ChartedSpace H M]

/-- A zero lies in the preferred chart source of the copy at `z` exactly when the corresponding
point of the level lies in the preferred chart source of `M`. -/
private theorem mem_chartAt_source_iff (z w : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    w.1 ∈ (chartAt E z.1).source ↔
      (zeroHomeomorph I f c w : M) ∈ (chartAt H (zeroHomeomorph I f c z : M)).source := by
  rw [BoundarylessModel.chartAt_eq, BoundarylessModel.chart_source, mem_preimage,
    coe_zeroHomeomorph, coe_zeroHomeomorph]

private theorem chartAt_self (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    chartAt E z.1 z.1 = extChartAt I (zeroHomeomorph I f c z : M) (zeroHomeomorph I f c z) := by
  rw [BoundarylessModel.chartAt_apply, coe_zeroHomeomorph]

/-- The trivialization coordinate of `f - c` in the preferred chart is `f - c` read in the
preferred extended chart of `M`. -/
private theorem coord_eq (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    (fun y ↦ ((trivializationAt F (Bundle.Trivial ℝ F) ((fun _ ↦ (0 : ℝ)) z.1))
      ⟨(fun _ ↦ (0 : ℝ)) ((chartAt E z.1).symm y), sec I f c ((chartAt E z.1).symm y)⟩).2) =
      fun y ↦ f ((extChartAt I (zeroHomeomorph I f c z : M)).symm y) - c := by
  funext y
  rw [coe_zeroHomeomorph]
  simp [sec, BoundarylessModel.chartAt_eq, BoundarylessModel.coe_homeomorph_symm]
  -- The remaining `id` is the identity of `M` read on the model copy.
  rfl

variable [NormedSpace ℝ F]

/-- The section-zero linearization at a zero: the preferred-chart derivative of `f`. -/
private noncomputable abbrev linearization (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    E →L[ℝ] F :=
  fderiv ℝ (f ∘ (extChartAt I (zeroHomeomorph I f c z : M)).symm)
    (extChartAt I (zeroHomeomorph I f c z : M) (zeroHomeomorph I f c z))

private theorem hasStrictFDerivAt_coord (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) 1 f x)
    (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    HasStrictFDerivAt
      (fun y ↦ ((trivializationAt F (Bundle.Trivial ℝ F) ((fun _ ↦ (0 : ℝ)) z.1))
        ⟨(fun _ ↦ (0 : ℝ)) ((chartAt E z.1).symm y), sec I f c ((chartAt E z.1).symm y)⟩).2)
      (linearization z) (chartAt E z.1 z.1) := by
  rw [coord_eq, chartAt_self]
  exact ((hf _ (zeroHomeomorph I f c z).2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt
    one_ne_zero).sub_const c

private theorem surjective_linearization (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) : Surjective (linearization z) :=
  (hreg.isRegularPoint (zeroHomeomorph I f c z).2).surjective_fderiv_comp_extChartAt_symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}

omit [I.Boundaryless] in
private theorem isFredholm_linearization (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    (linearization z).IsFredholm :=
  ContinuousLinearMap.isFredholm_of_finiteDimensional _

omit [FiniteDimensional ℝ F] in
private theorem index_linearization (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    (hn : finrank ℝ E - finrank ℝ F = n) (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    (linearization z).index = n :=
  ((linearization z).finrank_ker_eq_iff_index_eq (surjective_linearization hreg z)).1
    ((Nat.eq_sub_of_add_eq ((hreg.isRegularPoint (zeroHomeomorph I f c z).2)
      |>.finrank_ker_fderiv_comp_extChartAt_symm_add_finrank)).trans hn)

/-- The implicit-function chart and regular neighbourhood of the section-zero chart at a zero are
those of `f - c` read in the preferred extended chart of `M`. -/
private theorem implicit_coord_eq (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) 1 f x)
    (hreg : IsRegularValue I 𝓘(ℝ, F) f c) (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    let x := (zeroHomeomorph I f c z : M)
    let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I x).symm y) - c) (linearization z)
        (extChartAt I x x) :=
      ((hf x (zeroHomeomorph I f c z).2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt
        one_ne_zero).sub_const c
    let hD' := LinearMap.range_eq_top.2 (surjective_linearization hreg z)
    let hker := (isFredholm_linearization z).closedComplemented_ker
    (hasStrictFDerivAt_coord hf z).implicitToOpenPartialHomeomorphOfComplemented _ _ hD' hker =
        hD.implicitToOpenPartialHomeomorphOfComplemented _ _ hD' hker ∧
      (hasStrictFDerivAt_coord hf z).implicitCoordSource hD' hker =
        hD.implicitCoordSource hD' hker :=
  ⟨HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_congr _ _ (coord_eq z)
      (chartAt_self z) _ _,
    HasStrictFDerivAt.implicitCoordSource_congr _ _ (coord_eq z) (chartAt_self z) _ _⟩

end RegularLevel

open RegularLevel

variable [NormedSpace ℝ F] [I.Boundaryless] [ChartedSpace H M] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] {n : ℕ} (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) 1 f x)
  (hreg : IsRegularValue I 𝓘(ℝ, F) f c) (hn : finrank ℝ E - finrank ℝ F = n)

/-- The preferred chart at a point `x` of a regular level `f⁻¹(c)`, modelled on `Fin n → ℝ` for
`n = dim E - dim F`: the section-zero chart of `f - c` at `x`. It reads a point `w` as the kernel
component of `extChartAt I x w - extChartAt I x x` for the derivative of `f` in the preferred
extended chart at `x` (`TauCeti.regularLevelChartAt_apply`). -/
noncomputable def regularLevelChartAt (x : {x : M // f x = c}) :
    OpenPartialHomeomorph {x : M // f x = c} (Fin n → ℝ) :=
  (zeroHomeomorph I f c).symm.transOpenPartialHomeomorph
    (sectionZeroChartAt (hasStrictFDerivAt_coord hf) isFredholm_linearization
      (surjective_linearization hreg) (index_linearization hreg hn)
      ((zeroHomeomorph I f c).symm x))

/-- The preferred chart at the point of the level corresponding to a zero `z` of `f - c` is the
section-zero chart at `z`, transported along the level homeomorphism. -/
private theorem regularLevelChartAt_zeroHomeomorph
    (z : ↥{y : BoundarylessModel I M | sec I f c y = 0}) :
    regularLevelChartAt hf hreg hn (zeroHomeomorph I f c z) =
      (zeroHomeomorph I f c).symm.transOpenPartialHomeomorph
        (sectionZeroChartAt (hasStrictFDerivAt_coord hf) isFredholm_linearization
          (surjective_linearization hreg) (index_linearization hreg hn) z) := by
  rw [regularLevelChartAt, Homeomorph.symm_apply_apply]

/-- Every point of the level lies in the source of its preferred chart. -/
theorem mem_regularLevelChartAt_source (x : {x : M // f x = c}) :
    x ∈ (regularLevelChartAt hf hreg hn x).source := by
  rw [regularLevelChartAt, Homeomorph.transOpenPartialHomeomorph_source]
  exact mem_sectionZeroChartAt_source _ _ _ _ (fun _ ↦ continuousAt_const)
    (fun z ↦ mem_baseSet_trivializationAt F (Bundle.Trivial ℝ F) _) _

/-- The atlas of a regular level `f⁻¹(c)`: the section-zero atlas of `f - c`, with preferred
charts `TauCeti.regularLevelChartAt`. It is modelled on `Fin n → ℝ` for `n = dim E - dim F`. -/
@[irreducible]
noncomputable def regularLevelChartedSpace : ChartedSpace (Fin n → ℝ) {x : M // f x = c} where
  atlas := range (regularLevelChartAt hf hreg hn)
  chartAt := regularLevelChartAt hf hreg hn
  mem_chart_source := mem_regularLevelChartAt_source hf hreg hn
  chart_mem_atlas := mem_range_self

/-- The installed preferred charts are `TauCeti.regularLevelChartAt`. -/
@[simp]
theorem regularLevelChartedSpace_chartAt (x : {x : M // f x = c}) :
    @chartAt (Fin n → ℝ) _ {x : M // f x = c} _ (regularLevelChartedSpace hf hreg hn) x =
      regularLevelChartAt hf hreg hn x := by
  unfold regularLevelChartedSpace
  rfl

/-- The installed atlas consists exactly of the preferred charts. -/
@[simp]
theorem regularLevelChartedSpace_atlas :
    @atlas (Fin n → ℝ) _ {x : M // f x = c} _ (regularLevelChartedSpace hf hreg hn) =
      range (regularLevelChartAt hf hreg hn) := by
  unfold atlas regularLevelChartedSpace
  rfl

/-- The preferred chart at `x` reads the displacement `extChartAt I x w - extChartAt I x x` through
the chosen projection onto the kernel of the preferred-chart derivative `D` of `f` at `x`,
followed by the identification of that kernel with `Fin n → ℝ`. -/
theorem regularLevelChartAt_apply (x w : {x : M // f x = c}) :
    regularLevelChartAt hf hreg hn x w =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        ((Nat.eq_sub_of_add_eq
          (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm_add_finrank).trans hn)
        (Classical.choose D.isFredholm_of_finiteDimensional.closedComplemented_ker
          (extChartAt I (x : M) w - extChartAt I (x : M) x)) := by
  obtain ⟨z, rfl⟩ := (zeroHomeomorph I f c).surjective x
  simp only [regularLevelChartAt_zeroHomeomorph, Homeomorph.transOpenPartialHomeomorph_apply,
    comp_apply, Homeomorph.symm_apply_apply, sectionZeroChartAt_apply,
    BoundarylessModel.chartAt_apply, coe_zeroHomeomorph_symm, ← coe_zeroHomeomorph]

/-- A preferred chart is centred at its point. -/
@[simp]
theorem regularLevelChartAt_apply_self (x : {x : M // f x = c}) :
    regularLevelChartAt hf hreg hn x x = 0 := by
  simp only [regularLevelChartAt_apply, sub_self, map_zero]

/-- The origin belongs to the target of every preferred chart. -/
theorem mem_regularLevelChartAt_target (x : {x : M // f x = c}) :
    (0 : Fin n → ℝ) ∈ (regularLevelChartAt hf hreg hn x).target :=
  regularLevelChartAt_apply_self hf hreg hn x ▸
    (regularLevelChartAt hf hreg hn x).map_source (mem_regularLevelChartAt_source hf hreg hn x)

/-- The inverse preferred chart at `x` sends the origin to `x`. -/
@[simp]
theorem regularLevelChartAt_symm_zero (x : {x : M // f x = c}) :
    (regularLevelChartAt hf hreg hn x).symm 0 = x := by
  rw [← regularLevelChartAt_apply_self hf hreg hn x]
  exact (regularLevelChartAt hf hreg hn x).left_inv (mem_regularLevelChartAt_source hf hreg hn x)

/-- The source of the preferred chart at `x`: points of the level in the preferred chart of `M`
at `x` whose extended coordinates lie in the source of the implicit-function chart of `f - c` and
in the neighbourhood where its derivative stays invertible. -/
@[simp]
theorem regularLevelChartAt_source (x : {x : M // f x = c}) :
    (regularLevelChartAt hf hreg hn x).source =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I (x : M)).symm y) - c) D
          (extChartAt I (x : M) x) :=
        ((hf x x.2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const c
      let hD' := LinearMap.range_eq_top.2
        (hreg.isRegularPoint x.2).surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      {w : {x : M // f x = c} | (w : M) ∈ (chartAt H (x : M)).source ∧
        extChartAt I (x : M) w ∈
        (hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker).source ∩
          hD.implicitCoordSource hD' hker} := by
  obtain ⟨z, rfl⟩ := (zeroHomeomorph I f c).surjective x
  obtain ⟨hΦ, hsrc⟩ := implicit_coord_eq hf hreg z
  dsimp only
  rw [regularLevelChartAt_zeroHomeomorph, Homeomorph.transOpenPartialHomeomorph_source,
    sectionZeroChartAt_source, hΦ, hsrc]
  ext w
  obtain ⟨w, rfl⟩ := (zeroHomeomorph I f c).surjective w
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, Homeomorph.symm_apply_apply,
    mem_chartAt_source_iff, BoundarylessModel.chartAt_apply, ← coe_zeroHomeomorph,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_baseSet,
    preimage_univ, interior_univ, mem_univ, and_true]

/-- The target of the preferred chart at `x`: model points `k` whose kernel vector `K.symm k`
gives a point `(0, K.symm k)` of the implicit-function chart target of `f - c`, whose inverse lies
in the regular neighbourhood and in the target of the preferred extended chart at `x`. -/
@[simp]
theorem mem_regularLevelChartAt_target_iff (x : {x : M // f x = c}) (k : Fin n → ℝ) :
    k ∈ (regularLevelChartAt hf hreg hn x).target ↔
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I (x : M)).symm y) - c) D
          (extChartAt I (x : M) x) :=
        ((hf x x.2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const c
      let hD' := LinearMap.range_eq_top.2
        (hreg.isRegularPoint x.2).surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      let K := D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        ((Nat.eq_sub_of_add_eq
          (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm_add_finrank).trans hn)
      let Φ := hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker
      (0, K.symm k) ∈ Φ.target ∧ Φ.symm (0, K.symm k) ∈ hD.implicitCoordSource hD' hker ∧
        Φ.symm (0, K.symm k) ∈ (extChartAt I (x : M)).target := by
  obtain ⟨z, rfl⟩ := (zeroHomeomorph I f c).surjective x
  obtain ⟨hΦ, hsrc⟩ := implicit_coord_eq hf hreg z
  dsimp only
  rw [regularLevelChartAt_zeroHomeomorph, Homeomorph.transOpenPartialHomeomorph_target,
    mem_sectionZeroChartAt_target_iff]
  dsimp only
  rw [hΦ, hsrc]
  simp only [BoundarylessModel.chartAt_eq, BoundarylessModel.chart_target, extChartAt_target,
    ModelWithCorners.Boundaryless.range_eq_univ, inter_univ, mem_preimage, ← coe_zeroHomeomorph,
    Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_baseSet,
    preimage_univ, interior_univ, mem_univ, and_true]

/-- On its target, the inverse preferred chart at `x` is the inverse preferred extended chart of
`M` at `x`, applied to the inverse implicit-function chart of `f - c` on the zero slice. -/
theorem coe_regularLevelChartAt_symm_apply (x : {x : M // f x = c}) {k : Fin n → ℝ}
    (hk : k ∈ (regularLevelChartAt hf hreg hn x).target) :
    ((regularLevelChartAt hf hreg hn x).symm k : M) =
      let D := fderiv ℝ (f ∘ (extChartAt I (x : M)).symm) (extChartAt I (x : M) x)
      let hD : HasStrictFDerivAt (fun y ↦ f ((extChartAt I (x : M)).symm y) - c) D
          (extChartAt I (x : M) x) :=
        ((hf x x.2).contDiffAt_comp_extChartAt_symm.hasStrictFDerivAt one_ne_zero).sub_const c
      let hD' := LinearMap.range_eq_top.2
        (hreg.isRegularPoint x.2).surjective_fderiv_comp_extChartAt_symm
      let hker := D.isFredholm_of_finiteDimensional.closedComplemented_ker
      let K := D.kerModelEquiv D.isFredholm_of_finiteDimensional.finite_ker
        ((Nat.eq_sub_of_add_eq
          (hreg.isRegularPoint x.2).finrank_ker_fderiv_comp_extChartAt_symm_add_finrank).trans hn)
      (extChartAt I (x : M)).symm
        ((hD.implicitToOpenPartialHomeomorphOfComplemented _ D hD' hker).symm (0, K.symm k)) := by
  obtain ⟨z, rfl⟩ := (zeroHomeomorph I f c).surjective x
  obtain ⟨hΦ, -⟩ := implicit_coord_eq hf hreg z
  rw [regularLevelChartAt_zeroHomeomorph, Homeomorph.transOpenPartialHomeomorph_target] at hk
  rw [regularLevelChartAt_zeroHomeomorph, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    comp_apply, Homeomorph.symm_symm, coe_zeroHomeomorph,
    coe_sectionZeroChartAt_symm_apply _ _ _ _ _ hk, hΦ, BoundarylessModel.chartAt_eq,
    BoundarylessModel.chart_symm_apply, Homeomorph.symm_apply_apply, ← coe_zeroHomeomorph]
  -- `(extChartAt I x).symm` is `(chartAt H x).symm ∘ I.symm`, and `linearization z` abbreviates
  -- the preferred-chart derivative at `x`.
  rfl

/-- The coordinate smoothness input of the section-zero atlas of `f - c`: when `f` is `C^m` at the
points of the level, the trivialization coordinate of `f - c` is `C^m` in the preferred chart of
the self-modelled copy at every zero of its chart domain. -/
private theorem contDiffAt_coord {m : ℕ∞ω} [IsManifold I m M]
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) m f x) :
    m ≠ 0 → ∀ z w : ↥{y : BoundarylessModel I M | sec I f c y = 0},
      w.1 ∈ (chartAt E z.1).source →
      (fun _ ↦ (0 : ℝ)) w.1 ∈
        (trivializationAt F (Bundle.Trivial ℝ F) ((fun _ ↦ (0 : ℝ)) z.1)).baseSet →
      chartAt E z.1 w.1 ∈ (hasStrictFDerivAt_coord hf z).implicitCoordSource
        (LinearMap.range_eq_top.2 (surjective_linearization hreg z))
        (isFredholm_linearization z).closedComplemented_ker →
      ContDiffAt ℝ m
        (fun y ↦ ((trivializationAt F (Bundle.Trivial ℝ F) ((fun _ ↦ (0 : ℝ)) z.1))
          ⟨(fun _ ↦ (0 : ℝ)) ((chartAt E z.1).symm y), sec I f c ((chartAt E z.1).symm y)⟩).2)
        (chartAt E z.1 w.1) := by
  intro _ z w hw _ _
  have hw' := (mem_chartAt_source_iff z w).1 hw
  rw [coord_eq, BoundarylessModel.chartAt_apply, ← coe_zeroHomeomorph, ← coe_zeroHomeomorph]
  exact ContDiffAt.sub ((contMDiffAt_iff_contDiffAt_comp_extend_symm
    (IsManifold.chart_mem_maximalAtlas (I := I) (n := m) _) hw').1
    (hfm _ (zeroHomeomorph I f c w).2)) contDiffAt_const

/-! ### The level as a submanifold -/

/-- The section-zero atlas of `f - c` on the zero set in the self-modelled copy. -/
private noncomputable abbrev zeroChartedSpace :
    ChartedSpace (Fin n → ℝ) ↥{y : BoundarylessModel I M | sec I f c y = 0} :=
  sectionZeroChartedSpace (hasStrictFDerivAt_coord hf) isFredholm_linearization
    (surjective_linearization hreg) (index_linearization hreg hn) (fun _ ↦ continuousAt_const)
    (fun _ ↦ mem_baseSet_trivializationAt F (Bundle.Trivial ℝ F) _)

/-- The atlas of the level is the section-zero atlas of `f - c`, pulled back along the
identification of the level with the zero set. -/
private theorem regularLevelChartedSpace_eq_pullbackChartedSpace :
    regularLevelChartedSpace hf hreg hn =
      letI := zeroChartedSpace hf hreg hn
      (zeroHomeomorph I f c).symm.pullbackChartedSpace := by
  let := zeroChartedSpace hf hreg hn
  ext1
  · refine (regularLevelChartedSpace_atlas hf hreg hn).trans
      (Eq.trans ?_ (Homeomorph.pullbackChartedSpace_atlas _).symm)
    rw [sectionZeroChartedSpace_atlas, ← range_comp,
      ← (zeroHomeomorph I f c).symm.surjective.range_comp]
    -- Each preferred chart of the level is by definition the transported section-zero chart.
    rfl
  · funext x
    refine (regularLevelChartedSpace_chartAt hf hreg hn x).trans
      (Eq.trans ?_ (Homeomorph.pullbackChartedSpace_chartAt _ x).symm)
    rw [sectionZeroChartedSpace_chartAt, regularLevelChartAt]

/-- A regular level `f⁻¹(c)` of a map which is `C^m` at the points of the level, with `m ≥ 1`, is
a `C^m` manifold of dimension `dim E - dim F` for its preferred atlas. -/
theorem isManifold_regularLevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) m f x) (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    (hn : finrank ℝ E - finrank ℝ F = n) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg hn
    IsManifold 𝓘(ℝ, Fin n → ℝ) m {x : M // f x = c} := by
  have hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) 1 f x := fun x hx ↦ (hfm x hx).of_le hm
  let := zeroChartedSpace hf hreg hn
  have := isManifold_sectionZero (hasStrictFDerivAt_coord hf)
    isFredholm_linearization (surjective_linearization hreg) (index_linearization hreg hn)
    (fun _ ↦ continuousAt_const) (fun _ ↦ mem_baseSet_trivializationAt F (Bundle.Trivial ℝ F) _)
    (contDiffAt_coord hf hreg hfm)
  rw [regularLevelChartedSpace_eq_pullbackChartedSpace]
  exact (zeroHomeomorph I f c).symm.pullback_isManifold _ m

/-- **The inclusion of a regular level is an immersion with complement `F`.** For the preferred
atlas `TauCeti.regularLevelChartedSpace`, the inclusion of a regular level `f⁻¹(c)` of a map which
is `C^m` at the points of the level, `m ≥ 1`, is a `C^m` immersion whose normal forms have the
space `F` of values of `f` as complement. -/
theorem isImmersionOfComplement_coe_regularLevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) m f x) (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    (hn : finrank ℝ E - finrank ℝ F = n) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg hn
    Manifold.IsImmersionOfComplement F 𝓘(ℝ, Fin n → ℝ) I m
      (Subtype.val : {x : M // f x = c} → M) := by
  have hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) 1 f x := fun x hx ↦ (hfm x hx).of_le hm
  let := zeroChartedSpace hf hreg hn
  have hZ := isImmersionOfComplement_coe_sectionZero (hasStrictFDerivAt_coord hf)
    isFredholm_linearization (surjective_linearization hreg) (index_linearization hreg hn)
    (fun _ ↦ continuousAt_const) (fun _ ↦ mem_baseSet_trivializationAt F (Bundle.Trivial ℝ F) _)
    (contDiffAt_coord hf hreg hfm)
  have := isManifold_sectionZero (hasStrictFDerivAt_coord hf)
    isFredholm_linearization (surjective_linearization hreg) (index_linearization hreg hn)
    (fun _ ↦ continuousAt_const) (fun _ ↦ mem_baseSet_trivializationAt F (Bundle.Trivial ℝ F) _)
    (contDiffAt_coord hf hreg hfm)
  rw [regularLevelChartedSpace_eq_pullbackChartedSpace]
  let := (zeroHomeomorph I f c).symm.pullbackChartedSpace (H := Fin n → ℝ)
  have := (zeroHomeomorph I f c).symm.pullback_isManifold 𝓘(ℝ, Fin n → ℝ) m
  refine BoundarylessModel.isImmersionOfComplement_target_iff.1 ?_
  -- Read in the self-modelled copy, the inclusion of the level is the inclusion of the zero set
  -- precomposed with the pulled-back diffeomorphism from the level to the zero set.
  have hcomp : BoundarylessModel.homeomorph I M ∘ (Subtype.val : {x : M // f x = c} → M) =
      Subtype.val ∘ (zeroHomeomorph I f c).symm.pullbackDiffeomorph 𝓘(ℝ, Fin n → ℝ) m := by
    funext x
    rw [comp_apply, comp_apply, Homeomorph.coe_pullbackDiffeomorph, coe_zeroHomeomorph_symm]
  rw [hcomp]
  exact isImmersionOfComplement_comp_diffeomorph _ hZ

/-- **A regular level is an embedded submanifold.** For the preferred atlas
`TauCeti.regularLevelChartedSpace`, the inclusion of a regular level `f⁻¹(c)` of a map which is
`C^m` at the points of the level, `m ≥ 1`, is a `C^m` smooth embedding. -/
theorem isSmoothEmbedding_coe_regularLevel {m : ℕ∞ω} [IsManifold I m M] (hm : 1 ≤ m)
    (hfm : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) m f x) (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    (hn : finrank ℝ E - finrank ℝ F = n) :
    letI := regularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg hn
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin n → ℝ) I m (Subtype.val : {x : M // f x = c} → M) :=
  letI := regularLevelChartedSpace (fun x hx ↦ (hfm x hx).of_le hm) hreg hn
  ⟨(isImmersionOfComplement_coe_regularLevel hm hfm hreg hn).isImmersion,
    Topology.IsEmbedding.subtypeVal⟩

/-- **The tangent space of a regular level is the kernel of `df`.** At a point `x` of a regular
level `f⁻¹(c)`, the differential of the inclusion, for the preferred atlas
`TauCeti.regularLevelChartedSpace`, has range the kernel of the differential of `f` at `x`. -/
theorem range_mfderiv_coe_regularLevel [IsManifold I 1 M] (x : {x : M // f x = c}) :
    letI := regularLevelChartedSpace hf hreg hn
    (mfderiv 𝓘(ℝ, Fin n → ℝ) I (Subtype.val : {x : M // f x = c} → M) x).range =
      (mfderiv I 𝓘(ℝ, F) f x).ker := by
  let := regularLevelChartedSpace hf hreg hn
  have hx := hreg.isRegularPoint x.2
  -- At a point of the level, regularity gives `dim F ≤ dim E`, so `n + dim F = dim E`.
  have hdim := hx.finrank_ker_mfderiv_add_finrank
  refine hx.range_mfderiv_eq_ker_mfderiv (g := Subtype.val) (.of_forall fun y ↦ y.2)
    ((isImmersionOfComplement_coe_regularLevel le_rfl hf hreg hn x).mfderiv_injective
      one_ne_zero) ?_
  rw [finrank_fin_fun]
  omega

/-- **Two defining maps of a regular level have the same tangent kernels.** If the regular level
`f⁻¹(c)` of a map which is `C¹` near the level is contained in the level `g⁻¹(c')` of a second map
into the same space, then `ker dg_x = ker df_x` at each of its points `x` which is a regular point
of `g`. -/
theorem ker_mfderiv_eq_of_forall_eq_imp [IsManifold I 1 M]
    (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ, F) 1 f x) (hreg : IsRegularValue I 𝓘(ℝ, F) f c)
    {g : M → F} {c' : F} (hfg : ∀ x, f x = c → g x = c') {x : M} (hx : f x = c)
    (hgx : IsRegularPoint I 𝓘(ℝ, F) g x) :
    (mfderiv I 𝓘(ℝ, F) g x).ker = (mfderiv I 𝓘(ℝ, F) f x).ker := by
  let := regularLevelChartedSpace (n := finrank ℝ E - finrank ℝ F) hf hreg rfl
  -- The tangent space of the level, the range of the differential of its inclusion, is `ker df`
  -- and lies in `ker dg`, since `g` is constant on the level.
  have hle : (mfderiv I 𝓘(ℝ, F) f x).ker ≤ (mfderiv I 𝓘(ℝ, F) g x).ker := by
    rw [← range_mfderiv_coe_regularLevel hf hreg rfl (⟨x, hx⟩ : {x : M // f x = c})]
    exact range_mfderiv_le_ker_mfderiv_of_eventually_eq
      (.of_forall fun y : {x : M // f x = c} ↦ hfg y y.2)
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have hf' := (hreg.isRegularPoint hx).finrank_ker_mfderiv_add_finrank
  have hg' := hgx.finrank_ker_mfderiv_add_finrank
  omega

end TauCeti
