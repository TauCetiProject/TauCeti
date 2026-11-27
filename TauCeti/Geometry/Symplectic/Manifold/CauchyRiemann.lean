/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.JHolomorphic.Linearization
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Symplectic.Manifold.Energy
public import TauCeti.LinearAlgebra.Complex.LinearPart
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

/-!
# The Cauchy–Riemann section of a map between almost complex manifolds

Let `(M, j)` and `(M', J)` be manifolds with smooth almost complex structures; in the main case
`M` is a Riemann surface. The **Cauchy–Riemann section** of a map `u : M → M'` is

`∂bar_J u = (du + J ∘ du ∘ j) / 2`,

at each point `x` a real-linear map `T_x M → T_{u x} M'` (`TauCeti.cauchyRiemannSection`). It is
the complex-antilinear part of the manifold derivative of `u` for the structures `j x` and
`J (u x)` (`TauCeti.toLinearMap_cauchyRiemannSection`), so it anticommutes with the two structures
(`TauCeti.isComplexAntilinear_cauchyRiemannSection`), and `du - ∂bar_J u` is complex linear
(`TauCeti.isComplexLinearMap_mfderiv_sub_cauchyRiemannSection`). This is the half-normalized
convention of McDuff–Salamon; the operator `du + J ∘ du ∘ j` used by Wendl is twice it.

* **Pseudoholomorphic maps are its zeros.** At a point where `u` is differentiable, `∂bar_J u`
  vanishes exactly when `u` is pseudoholomorphic there in the sense of
  `TauCeti.IsPseudoholomorphicAt` (`TauCeti.cauchyRiemannSection_eq_zero_iff`), and a
  differentiable map is pseudoholomorphic exactly when its Cauchy–Riemann section vanishes
  everywhere (`TauCeti.isPseudoholomorphic_iff_forall_cauchyRiemannSection_eq_zero`).
  Differentiability cannot be dropped: Mathlib's `mfderiv` is `0` where `u` is not
  differentiable, so there `∂bar_J u` is `0` as well
  (`TauCeti.cauchyRiemannSection_eq_zero_of_not_mdifferentiableAt`).
* **In charts.** The coordinate expression of a map pseudoholomorphic at `x`, in the charts at
  `x` and at `u x`, solves the coordinate Cauchy–Riemann equation `TauCeti.cauchyRiemannOperator`
  at the chart centre
  (`TauCeti.IsPseudoholomorphicAt.cauchyRiemannOperator_writtenInExtChartAt_eq_zero`). Away from
  the centre the source structure is read in the chart at `x` too, and a continuous map
  pseudoholomorphic near `x` solves the equation near the chart centre
  (`TauCeti.eventually_cauchyRiemannOperator_writtenInExtChartAt_eq_zero`).
* **Naturality.** Precomposing with a map pseudoholomorphic for the source structures, such as a
  biholomorphism of Riemann surfaces or a holomorphic chart, precomposes the section with its
  derivative (`TauCeti.cauchyRiemannSection_comp_of_isPseudoholomorphicAt_right`), and
  postcomposing with a map intertwining the target structures postcomposes it with its derivative
  (`TauCeti.cauchyRiemannSection_comp_of_isPseudoholomorphicAt_left`). Reversing both structures
  does not change the section (`TauCeti.cauchyRiemannSection_neg_neg`).
* **Complex vector spaces.** For a map between complex normed spaces, with multiplication by `i`
  as almost complex structure on both, the section is the conjugate Wirtinger derivative
  (`TauCeti.cauchyRiemannSection_ofComplexManifold_apply`).
* **Energy.** For a curve `u` from the standard complex line `ℝ × ℝ` into `M'` and a smooth
  two-form `ω` invariant under `J`, the energy density of `du` splits as
  `e(du) = 2 ω(∂s u, ∂t u) + 2 e(∂bar_J u)`
  (`TauCeti.SmoothTwoForm.Invariant.stdComplexLineEnergyDensity_mfderiv_eq`), where
  `e = TauCeti.SmoothTwoForm.stdComplexLineEnergyDensity`; the linear statement behind it is
  `TauCeti.SmoothTwoForm.Invariant.stdComplexLineEnergyDensity_eq_two_mul_twoForm_add` in
  `TauCeti.Geometry.Symplectic.Manifold.Energy`. Since
  the energy is half the integral of `e`, this is the pointwise form of the identity
  `E(u) = ∫ u*ω + ∫ e(∂bar_J u)` of McDuff–Salamon: the energy of a curve is its symplectic area
  plus the integral of the energy density of its Cauchy–Riemann section, which is twice the
  energy of that section. The integrated identity needs a taming form, since
  `TauCeti.SmoothTwoForm.stdComplexLineEnergy` truncates negative densities to `0`. For a taming
  form the second density is nonnegative and vanishes, at a point of differentiability, exactly
  when the curve is pseudoholomorphic there.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (the operator `∂bar_J` and Lemma 2.2.1) and
  Section 3.1.
* C. Wendl, *Lectures on holomorphic curves in symplectic and contact geometry*, Section 2, on
  the nonlinear Cauchy–Riemann operator.
-/

public section

open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

variable {E H M E' H' M' E'' H'' M'' E₀ H₀ M₀ : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ### The section and its characterization -/

section Basic

variable {j : SmoothAlmostComplexStructure I M} {J : SmoothAlmostComplexStructure I' M'}
  {u : M → M'} {x : M}

/-- The **Cauchy–Riemann section** `∂bar_J u = (du + J ∘ du ∘ j) / 2` of a map `u : M → M'`
between manifolds with almost complex structures `j` and `J`, at the point `x`: a real-linear
map from the tangent space at `x` to the tangent space at `u x`, built from the manifold
derivative `mfderiv`. It vanishes at a point of differentiability exactly when `u` is
pseudoholomorphic there (`TauCeti.cauchyRiemannSection_eq_zero_iff`). -/
def cauchyRiemannSection (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I' (u x) :=
  (2⁻¹ : ℝ) • (mfderiv I I' u x +
    (J.toEndomorphism (u x)).comp ((mfderiv I I' u x).comp (j.toEndomorphism x)))

/-- The definition of the Cauchy–Riemann section. -/
theorem cauchyRiemannSection_def (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) :
    cauchyRiemannSection j J u x = (2⁻¹ : ℝ) • (mfderiv I I' u x +
      (J.toEndomorphism (u x)).comp ((mfderiv I I' u x).comp (j.toEndomorphism x))) :=
  (rfl)

/-- The Cauchy–Riemann section evaluated on a tangent vector:
`∂bar_J u (v) = (du v + J (du (j v))) / 2`. -/
theorem cauchyRiemannSection_apply (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) (v : TangentSpace I x) :
    cauchyRiemannSection j J u x v =
      (2⁻¹ : ℝ) • (mfderiv I I' u x v + J (u x) (mfderiv I I' u x (j x v))) :=
  (rfl)

/-- The Cauchy–Riemann section is the complex-antilinear part of the manifold derivative, for
the almost complex structures at the point and at its image. -/
theorem toLinearMap_cauchyRiemannSection (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) :
    (cauchyRiemannSection j J u x).toLinearMap =
      complexAntilinearPart (j.almostComplexStructureAt x).toLinearMap
        (J.almostComplexStructureAt (u x)).toLinearMap (mfderiv I I' u x).toLinearMap := by
  ext v
  simp only [complexAntilinearPart_apply,
    SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap, ContinuousLinearMap.coe_coe,
    cauchyRiemannSection_apply]

/-- The Cauchy–Riemann section anticommutes with the almost complex structures:
`∂bar_J u ∘ j = -J ∘ ∂bar_J u`. -/
theorem isComplexAntilinear_cauchyRiemannSection (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) :
    IsComplexAntilinear (j.almostComplexStructureAt x).toLinearMap
      (J.almostComplexStructureAt (u x)).toLinearMap
      (cauchyRiemannSection j J u x).toLinearMap := by
  rw [toLinearMap_cauchyRiemannSection]
  exact isComplexAntilinear_complexAntilinearPart (j.almostComplexStructureAt x).square_neg
    (J.almostComplexStructureAt (u x)).square_neg _

/-- The Cauchy–Riemann section anticommutes with the almost complex structures, on a tangent
vector. -/
theorem cauchyRiemannSection_apply_almostComplexStructure (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) (v : TangentSpace I x) :
    cauchyRiemannSection j J u x (j x v) = -J (u x) (cauchyRiemannSection j J u x v) := by
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    ContinuousLinearMap.coe_coe] using (isComplexAntilinear_cauchyRiemannSection j J u x).apply v

/-- The difference `du - ∂bar_J u`, the complex-linear part `∂_J u` of the derivative, commutes with
the almost complex structures. -/
theorem isComplexLinearMap_mfderiv_sub_cauchyRiemannSection (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) :
    IsComplexLinearMap (j.almostComplexStructureAt x) (J.almostComplexStructureAt (u x))
      (mfderiv I I' u x - cauchyRiemannSection j J u x).toLinearMap := by
  have hsub : (mfderiv I I' u x - cauchyRiemannSection j J u x).toLinearMap =
      complexLinearPart (j.almostComplexStructureAt x).toLinearMap
        (J.almostComplexStructureAt (u x)).toLinearMap (mfderiv I I' u x).toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_sub, toLinearMap_cauchyRiemannSection, sub_eq_iff_eq_add',
      add_comm, complexLinearPart_add_complexAntilinearPart]
  rw [isComplexLinearMap_iff_isComplexLinear, hsub]
  exact isComplexLinear_complexLinearPart (j.almostComplexStructureAt x).square_neg
    (J.almostComplexStructureAt (u x)).square_neg _

/-- The Cauchy–Riemann section of a map pseudoholomorphic at a point vanishes there. -/
theorem IsPseudoholomorphicAt.cauchyRiemannSection_eq_zero (hu : IsPseudoholomorphicAt j J u x) :
    cauchyRiemannSection j J u x = 0 := by
  ext v
  simp [cauchyRiemannSection_apply, hu.mfderiv_apply_commute]

/-- The identity map has vanishing Cauchy–Riemann section. -/
@[simp]
theorem cauchyRiemannSection_id (j : SmoothAlmostComplexStructure I M) (x : M) :
    cauchyRiemannSection j j id x = 0 :=
  (isPseudoholomorphicAt_id j x).cauchyRiemannSection_eq_zero

/-- A constant map has vanishing Cauchy–Riemann section. -/
@[simp]
theorem cauchyRiemannSection_const (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (c : M') (x : M) :
    cauchyRiemannSection j J (fun _ ↦ c) x = 0 :=
  (isPseudoholomorphicAt_const j J c x).cauchyRiemannSection_eq_zero

/-- At a point where the map is not differentiable its Cauchy–Riemann section is `0`, because
Mathlib's `mfderiv` is `0` there. So `cauchyRiemannSection_eq_zero_iff` needs differentiability. -/
theorem cauchyRiemannSection_eq_zero_of_not_mdifferentiableAt (hu : ¬MDifferentiableAt I I' u x) :
    cauchyRiemannSection j J u x = 0 := by
  rw [cauchyRiemannSection_def, mfderiv_zero_of_not_mdifferentiableAt hu,
    ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, add_zero, smul_zero]

/-- At a point where the map is differentiable, its Cauchy–Riemann section vanishes exactly when
the map is pseudoholomorphic there. -/
theorem cauchyRiemannSection_eq_zero_iff (hu : MDifferentiableAt I I' u x) :
    cauchyRiemannSection j J u x = 0 ↔ IsPseudoholomorphicAt j J u x := by
  refine ⟨fun h ↦ isPseudoholomorphicAt_iff_mfderiv.2 ⟨hu, fun w ↦ ?_⟩,
    IsPseudoholomorphicAt.cauchyRiemannSection_eq_zero⟩
  have hw := (toLinearMap_cauchyRiemannSection j J u x).symm.trans
    (congrArg ContinuousLinearMap.toLinearMap h)
  have hlin := (isComplexLinear_iff_complexAntilinearPart_eq_zero
    (J.almostComplexStructureAt (u x)).square_neg _).2 hw
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    ContinuousLinearMap.coe_coe] using hlin.apply w

/-- A differentiable map is pseudoholomorphic exactly when its Cauchy–Riemann section vanishes at
every point. -/
theorem isPseudoholomorphic_iff_forall_cauchyRiemannSection_eq_zero (hu : MDifferentiable I I' u) :
    IsPseudoholomorphic j J u ↔ ∀ x, cauchyRiemannSection j J u x = 0 := by
  rw [isPseudoholomorphic_iff]
  exact forall_congr' fun x ↦ (cauchyRiemannSection_eq_zero_iff (hu x)).symm

/-- Reversing both almost complex structures does not change the Cauchy–Riemann section. -/
@[simp]
theorem cauchyRiemannSection_neg_neg (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') :
    cauchyRiemannSection (-j) (-J) u = cauchyRiemannSection j J u := by
  ext x v
  simp only [cauchyRiemannSection_apply, SmoothAlmostComplexStructure.neg_apply, map_neg, neg_neg]

end Basic

/-! ### The Cauchy–Riemann equation in charts -/

section Chart

variable [I.Boundaryless] {j : SmoothAlmostComplexStructure I M}
  {J : SmoothAlmostComplexStructure I' M'} {u : M → M'} {x : M}

/-- At a point where `u` is pseudoholomorphic, its coordinate expression in the charts at `x` and
at `u x` solves the Cauchy–Riemann equation at the chart centre, with the source structure frozen
at its value at the chart centre. -/
theorem IsPseudoholomorphicAt.cauchyRiemannOperator_writtenInExtChartAt_eq_zero
    (hu : IsPseudoholomorphicAt j J u x) :
    cauchyRiemannOperator (j.inChart x (extChartAt I x x)) (J.inChart (u x))
      (writtenInExtChartAt I I' x u) (extChartAt I x x) = 0 := by
  ext v
  rw [cauchyRiemannOperator_apply, zero_apply, hu.mdifferentiableAt.fderiv_writtenInExtChartAt,
    writtenInExtChartAt_apply_extChartAt (mem_extChartAt_source x), J.inChart_extChartAt_self,
    j.inChart_extChartAt_self]
  exact sub_eq_zero.2 (hu.mfderiv_apply_commute v)

/-- Away from the chart centre, the coordinate expression of `u` in the charts at `x` and at `u x`
solves the Cauchy–Riemann equation at every chart point `z` whose point `y` is one where `u` is
pseudoholomorphic and continuous and lands in the target chart, for the source structure read in
the chart at `x` at `z`. -/
theorem IsPseudoholomorphicAt.cauchyRiemannOperator_writtenInExtChartAt_eq_zero_of_mem
    {z : E} (hz : z ∈ (extChartAt I x).target)
    (hu : IsPseudoholomorphicAt j J u ((extChartAt I x).symm z))
    (hc : ContinuousAt u ((extChartAt I x).symm z))
    (hw : u ((extChartAt I x).symm z) ∈ (extChartAt I' (u x)).source) :
    cauchyRiemannOperator (j.inChart x z) (J.inChart (u x))
      (writtenInExtChartAt I I' x u) z = 0 := by
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm z :=
    (mdifferentiableWithinAt_extChartAt_symm hz).mdifferentiableAt
      (by simp [I.range_eq_univ])
  -- The inverse chart carries the source structure read in the chart to `j`.
  have hj (v : E) : mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm z (j.inChart x z v) =
      j ((extChartAt I x).symm z) (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm z v) := by
    have hinv := congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz)
      (j ((extChartAt I x).symm z)
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I) z v)))
    rw [I.range_eq_univ, mfderivWithin_univ] at hinv
    rw [j.inChart_apply_eq_mfderiv x hz, I.range_eq_univ, mfderivWithin_univ]
    exact hinv
  ext v
  rw [cauchyRiemannOperator_apply, zero_apply, sub_eq_zero]
  refine J.fderiv_extChartAt_comp_apply_eq_inChart (u x) (u := u ∘ (extChartAt I x).symm)
    (hc.comp (continuousAt_extChartAt_symm'' hz)) hw ?_
  rw [mfderiv_comp z hu.mdifferentiableAt hsymm]
  exact (congrArg (mfderiv I I' u _) (hj v)).trans (hu.mfderiv_apply_commute _)

/-- If `u` is continuous at `x` and pseudoholomorphic near `x`, its coordinate expression in the
charts at `x` and at `u x` solves the Cauchy–Riemann equation near the chart centre, for the
source structure read in the chart at `x`. -/
theorem eventually_cauchyRiemannOperator_writtenInExtChartAt_eq_zero
    (hu : ∀ᶠ y in 𝓝 x, IsPseudoholomorphicAt j J u y ∧ ContinuousAt u y)
    (hc : ContinuousAt u x) :
    ∀ᶠ z in 𝓝 (extChartAt I x x), cauchyRiemannOperator (j.inChart x z) (J.inChart (u x))
      (writtenInExtChartAt I I' x u) z = 0 := by
  have hsymm := continuousAt_extChartAt_symm (I := I) x
  have hsrc : u ⁻¹' (extChartAt I' (u x)).source ∈
      𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by
    rw [extChartAt_to_inv]
    exact hc.preimage_mem_nhds (extChartAt_source_mem_nhds (u x))
  rw [← extChartAt_to_inv (I := I) x] at hu
  filter_upwards [extChartAt_target_mem_nhds (I := I) x, hsymm.preimage_mem_nhds hu,
    hsymm.preimage_mem_nhds hsrc] with z hz hzu hzc
  exact hzu.1.cauchyRiemannOperator_writtenInExtChartAt_eq_zero_of_mem hz hzu.2 hzc

end Chart

/-! ### Naturality -/

section Naturality

variable [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I'' ∞ M'']
variable [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [TopologicalSpace H₀]
  {I₀ : ModelWithCorners ℝ E₀ H₀} [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀]
variable {j₀ : SmoothAlmostComplexStructure I₀ M₀} {j : SmoothAlmostComplexStructure I M}
  {J : SmoothAlmostComplexStructure I' M'} {K : SmoothAlmostComplexStructure I'' M''}

/-- Postcomposing with a map that intertwines the target almost complex structures postcomposes
the Cauchy–Riemann section with its derivative: `∂bar_K (ψ ∘ u) = dψ ∘ ∂bar_J u`. -/
theorem cauchyRiemannSection_comp_of_isPseudoholomorphicAt_left {ψ : M' → M''} {u : M → M'} {x : M}
    (hψ : IsPseudoholomorphicAt J K ψ (u x)) (hu : MDifferentiableAt I I' u x) :
    cauchyRiemannSection j K (ψ ∘ u) x =
      (mfderiv I' I'' ψ (u x)).comp (cauchyRiemannSection j J u x) := by
  ext v
  simp only [cauchyRiemannSection_apply, mfderiv_comp x hψ.mdifferentiableAt hu,
    ContinuousLinearMap.comp_apply, map_smul, map_add, Function.comp_apply]
  rw [hψ.mfderiv_apply_commute]

/-- Precomposing with a map that intertwines the source almost complex structures, such as a
biholomorphism of Riemann surfaces or a holomorphic chart, precomposes the Cauchy–Riemann
section with its derivative: `∂bar_J (u ∘ φ) = ∂bar_J u ∘ dφ`. -/
theorem cauchyRiemannSection_comp_of_isPseudoholomorphicAt_right {u : M → M'} {φ : M₀ → M} {x : M₀}
    (hu : MDifferentiableAt I I' u (φ x)) (hφ : IsPseudoholomorphicAt j₀ j φ x) :
    cauchyRiemannSection j₀ J (u ∘ φ) x =
      (cauchyRiemannSection j J u (φ x)).comp (mfderiv I₀ I φ x) := by
  ext v
  simp only [cauchyRiemannSection_apply, mfderiv_comp x hu hφ.mdifferentiableAt,
    ContinuousLinearMap.comp_apply, Function.comp_apply]
  rw [hφ.mfderiv_apply_commute]

end Naturality

/-! ### Complex vector spaces -/

section ComplexVectorSpace

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- For a map `g` between complex normed spaces, with multiplication by `i` as the almost complex
structure on both, the Cauchy–Riemann section is the conjugate Wirtinger derivative
`v ↦ (dg v + i dg (i v)) / 2`. -/
theorem cauchyRiemannSection_ofComplexManifold_apply (g : V → W) (x : V)
    (v : TangentSpace 𝓘(ℝ, V) x) :
    cauchyRiemannSection (SmoothAlmostComplexStructure.ofComplexManifold V V)
        (SmoothAlmostComplexStructure.ofComplexManifold W W) g x v =
      conjWirtingerDeriv g x v := by
  rw [cauchyRiemannSection_apply, conjWirtingerDeriv_eq_complexAntilinearPart, mfderiv_eq_fderiv]
  simp only [SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  exact (ContinuousLinearMap.complexAntilinearPart_apply (fderiv ℝ g x) v).symm

end ComplexVectorSpace

/-! ### The energy identity -/

namespace SmoothTwoForm

variable {form : SmoothTwoForm I' M'} {J : SmoothAlmostComplexStructure I' M'}

/-- **The energy identity.** For a two-form invariant under `J`, the energy density of the
derivative of a curve `u` from the standard complex line is twice its symplectic area density
plus twice the energy density of its Cauchy–Riemann section:
`e(du) = 2 ω(∂s u, ∂t u) + 2 e(∂bar_J u)`. -/
theorem Invariant.stdComplexLineEnergyDensity_mfderiv_eq (hinv : form.Invariant J)
    (u : ℝ × ℝ → M') (z : ℝ × ℝ) :
    form.stdComplexLineEnergyDensity J (u z)
        (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' u z).toLinearMap =
      2 * SmoothBundleForm.eval₂ form (u z)
          (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' u z stdComplexLineReal)
          (mfderiv (modelWithCornersSelf ℝ (ℝ × ℝ)) I' u z stdComplexLineImag) +
        2 * form.stdComplexLineEnergyDensity J (u z)
          (cauchyRiemannSection (SmoothAlmostComplexStructure.product ℝ) J u z).toLinearMap := by
  rw [toLinearMap_cauchyRiemannSection,
    SmoothAlmostComplexStructure.product_almostComplexStructureAt]
  exact hinv.stdComplexLineEnergyDensity_eq_two_mul_twoForm_add (u z) _

end SmoothTwoForm

end TauCeti
