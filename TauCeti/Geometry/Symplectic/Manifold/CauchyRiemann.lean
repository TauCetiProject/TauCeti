/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic

/-!
# The half-normalized nonlinear Cauchy–Riemann section

For almost complex manifolds `(M, j)` and `(N, J)`, `pseudoholomorphicSection j J u` is
`∂̄_J u = (du + J ∘ du ∘ j) / 2`, a family of real continuous linear maps from `T_x M`
to `T_(u x) N`. It is complex antilinear in the source tangent vector. Its vanishing
characterizes the existing derivative-level predicate `IsPseudoholomorphic`, provided the map
is differentiable. No smoothness or elliptic regularity of the map is inferred.

This pointwise section and its source and target composition laws require neither a
symplectic form nor compactness, finite dimension, or a surface source. The normalization
identity explicitly compares it with the unhalved expression `du + J ∘ du ∘ j`.

As with `mfderiv`, the definition is totalized: it is zero at a point of nondifferentiability.
Consequently differentiability must not be omitted from its zero-locus characterization.

The half-normalized convention follows McDuff–Salamon, *J-holomorphic Curves and Symplectic
Topology*, second edition, §3.1. Wendl, *Lectures on Holomorphic Curves in Symplectic and
Contact Geometry*, version 3.2, §2, uses the unhalved expression instead.
-/

public noncomputable section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M E' H' M' E'' H'' M'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M''] [ChartedSpace H'' M'']
  [IsManifold I'' ∞ M'']

/-- The half-normalized Cauchy–Riemann section `(du + J ∘ du ∘ j) / 2`.
Its fibre at `x` consists of maps `T_x M → T_(u x) M'`. -/
def pseudoholomorphicSection (j : SmoothAlmostComplexStructure I M)
    (J : SmoothAlmostComplexStructure I' M') (u : M → M') (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I' (u x) :=
  (2⁻¹ : ℝ) • (mfderiv I I' u x +
    (J.toEndomorphism (u x)).comp ((mfderiv I I' u x).comp (j.toEndomorphism x)))

variable (j : SmoothAlmostComplexStructure I M) (J : SmoothAlmostComplexStructure I' M')
  (K : SmoothAlmostComplexStructure I'' M'') (u : M → M') (v : M' → M'') (x : M)

/-- Evaluation of the half-normalized section on a tangent vector. -/
theorem pseudoholomorphicSection_apply (w : TangentSpace I x) :
    pseudoholomorphicSection j J u x w =
      (2⁻¹ : ℝ) • (mfderiv I I' u x w + J (u x) (mfderiv I I' u x (j x w))) :=
  (rfl)

/-- The underlying linear map is the existing complex-antilinear projection of the derivative. -/
theorem toLinearMap_pseudoholomorphicSection :
    (pseudoholomorphicSection j J u x).toLinearMap =
      complexAntilinearPart (j.almostComplexStructureAt x).toLinearMap
        (J.almostComplexStructureAt (u x)).toLinearMap (mfderiv I I' u x).toLinearMap := by
  ext w
  simp [pseudoholomorphicSection_apply]

/-- The section takes values in complex-antilinear source covectors. -/
theorem isComplexAntilinear_pseudoholomorphicSection :
    IsComplexAntilinear (j.almostComplexStructureAt x).toLinearMap
      (J.almostComplexStructureAt (u x)).toLinearMap
      (pseudoholomorphicSection j J u x).toLinearMap := by
  rw [toLinearMap_pseudoholomorphicSection]
  exact isComplexAntilinear_complexAntilinearPart
    (j.almostComplexStructureAt x).square_neg (J.almostComplexStructureAt (u x)).square_neg _

/-- Inserting the source structure is the negative of applying the target structure. -/
theorem pseudoholomorphicSection_apply_almostComplex (w : TangentSpace I x) :
    pseudoholomorphicSection j J u x (j x w) =
      -J (u x) (pseudoholomorphicSection j J u x w) := by
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    ContinuousLinearMap.coe_coe] using
    (isComplexAntilinear_pseudoholomorphicSection j J u x).apply w

/-- Twice the section is the unhalved Cauchy–Riemann expression. -/
theorem two_smul_pseudoholomorphicSection :
    (2 : ℝ) • pseudoholomorphicSection j J u x =
      mfderiv I I' u x +
        (J.toEndomorphism (u x)).comp ((mfderiv I I' u x).comp (j.toEndomorphism x)) := by
  simp [pseudoholomorphicSection, smul_smul]

/-- For a differentiable map, vanishing is precisely the pinned pseudoholomorphicity predicate. -/
@[simp]
theorem pseudoholomorphicSection_eq_zero_iff (hu : MDifferentiableAt I I' u x) :
    pseudoholomorphicSection j J u x = 0 ↔ IsPseudoholomorphicAt j J u x := by
  rw [isPseudoholomorphicAt_iff_mfderiv, and_iff_right hu, ContinuousLinearMap.ext_iff]
  simp only [pseudoholomorphicSection_apply, zero_apply,
    smul_eq_zero, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  exact forall_congr' fun w ↦ add_apply_eq_zero_iff_eq_apply (J.apply_apply (u x)) _ _

/-- The zero locus, with differentiability recorded explicitly, has no spurious solutions. -/
theorem isPseudoholomorphicAt_iff_pseudoholomorphicSection_eq_zero :
    IsPseudoholomorphicAt j J u x ↔
      MDifferentiableAt I I' u x ∧ pseudoholomorphicSection j J u x = 0 := by
  constructor
  · intro hu
    exact ⟨hu.mdifferentiableAt,
      (pseudoholomorphicSection_eq_zero_iff j J u x hu.mdifferentiableAt).2 hu⟩
  · rintro ⟨hu, hzero⟩
    exact (pseudoholomorphicSection_eq_zero_iff j J u x hu).1 hzero

/-- The global zero-section equation characterizes differentiable pseudoholomorphic maps. -/
theorem isPseudoholomorphic_iff_pseudoholomorphicSection_eq_zero :
    IsPseudoholomorphic j J u ↔
      MDifferentiable I I' u ∧ ∀ x, pseudoholomorphicSection j J u x = 0 := by
  simp only [isPseudoholomorphic_iff, isPseudoholomorphicAt_iff_pseudoholomorphicSection_eq_zero,
    forall_and, MDifferentiable]

/-- Postcomposition by a pseudoholomorphic map acts by its derivative on the section. -/
theorem pseudoholomorphicSection_comp_left (hu : MDifferentiableAt I I' u x)
    (hv : IsPseudoholomorphicAt J K v (u x)) :
    pseudoholomorphicSection j K (v ∘ u) x =
      (mfderiv I' I'' v (u x)).comp (pseudoholomorphicSection j J u x) := by
  ext w
  simp only [pseudoholomorphicSection_apply, mfderiv_comp x hv.mdifferentiableAt hu,
    ContinuousLinearMap.comp_apply, Function.comp_apply, map_smul, map_add]
  rw [hv.mfderiv_apply_commute]

/-- Precomposition by a pseudoholomorphic map pulls back the section. -/
theorem pseudoholomorphicSection_comp_right (hu : IsPseudoholomorphicAt j J u x)
    (hv : MDifferentiableAt I' I'' v (u x)) :
    pseudoholomorphicSection j K (v ∘ u) x =
      (pseudoholomorphicSection J K v (u x)).comp (mfderiv I I' u x) := by
  ext w
  simp only [pseudoholomorphicSection_apply, mfderiv_comp x hv hu.mdifferentiableAt,
    ContinuousLinearMap.comp_apply, Function.comp_apply]
  rw [hu.mfderiv_apply_commute]

/-- Constant maps have zero Cauchy–Riemann section. -/
@[simp]
theorem pseudoholomorphicSection_const (c : M') :
    pseudoholomorphicSection j J (fun _ : M ↦ c) x = 0 := by
  simp [pseudoholomorphicSection]

/-- The identity map has zero Cauchy–Riemann section. -/
@[simp]
theorem pseudoholomorphicSection_id : pseudoholomorphicSection j j id x = 0 := by
  ext w
  simp [pseudoholomorphicSection_apply, j.apply_apply]

end TauCeti
