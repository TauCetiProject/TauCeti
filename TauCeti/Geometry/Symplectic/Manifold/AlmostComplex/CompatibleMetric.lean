/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.Riemannian.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
import TauCeti.Geometry.Manifold.Riemannian.Section
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# The smooth Riemannian metric of a compatible almost complex structure

For any smooth two-form `σ` and smooth almost complex structure `J` on a smooth manifold `M`, the
pointwise bilinear forms `(u, w) ↦ σ_x(u, J_x w)` assemble into a smooth section
`TauCeti.SmoothTwoForm.associatedBilinSection` of `Hom(TM, Hom(TM, ℝ))`. No compatibility or
finite-dimensionality assumption is needed for smoothness of this section: it is the fibrewise
transpose of `σ((-J) ·, ·)`.

When `M` is finite-dimensional and `J` is compatible with `σ` (`σ.Compatible J`), these fibrewise
bilinear forms are symmetric, positive definite, and have von Neumann bounded unit sets, so they
define a smooth Riemannian metric `TauCeti.SmoothTwoForm.Compatible.riemannianMetric` on `TM`.
Installed as a `RiemannianBundle` on `TM`, this metric makes `J` orthogonal, recovers `J` as the
polar normalization of `σ`, and recovers `σ` as the Kähler two-form `⟪J ·, ·⟫`.

## Main definitions

* `TauCeti.SmoothTwoForm.associatedBilinSection`: the smooth section `x ↦ (u, w) ↦ σ_x(u, J_x w)`
  of `Hom(TM, Hom(TM, ℝ))`, without finite-dimensionality or compatibility assumptions.
* `TauCeti.SmoothTwoForm.Compatible.riemannianMetric`: the smooth Riemannian metric
  `g_x(u, w) = σ_x(u, J_x w)` on `TM` associated to `h : σ.Compatible J` in finite dimensions.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.inner_apply_apply_riemannianMetric`: `J` is fibrewise
  orthogonal for `h.riemannianMetric`.
* `TauCeti.SmoothTwoForm.Compatible.polarComplexStructure_riemannianMetric`: the polar
  normalization of `σ` for `h.riemannianMetric` is `J`.
* `TauCeti.SmoothTwoForm.Compatible.kahlerTwoForm_riemannianMetric`: the Kähler two-form of `J`
  for `h.riemannianMetric` is `σ`.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 12.2.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Proposition 2.5.6 and Section 4.1.
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti.SmoothTwoForm

section AssociatedBilinSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- Restate Mathlib's `IsNormableSpace` instance on `TangentSpace I x` against the tangent space's
own `Module` instance so that `ContMDiffWithinAt.clm_bundle_flip` finds it during elaboration. -/
local instance (x : M) : IsNormableSpace ℝ (TangentSpace I x) :=
  instIsNormableSpaceTangentSpace I x

/-- For a smooth two-form `σ` and a smooth almost complex structure `J`, the fibrewise continuous
bilinear forms `(u, w) ↦ σ_x(u, J_x w)` form a smooth section of `Hom(TM, Hom(TM, ℝ))`. Neither
finite dimension nor compatibility is needed. -/
def associatedBilinSection (σ : SmoothTwoForm I M) (J : SmoothAlmostComplexStructure I M) :
    Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ, fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯ where
  toFun x := (σ.flatComp (-J).toEndomorphism x).flip
  contMDiff_toFun := by
    have : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) := fun _ ↦ inferInstance
    intro x
    exact contMDiffWithinAt_univ.1
      ((σ.flatComp (-J).toEndomorphism).contMDiff x).contMDiffWithinAt.clm_bundle_flip

/-- Evaluating `σ.associatedBilinSection J` at `x` on `u` and `w` gives `σ_x(u, J_x w)`. -/
@[simp]
theorem associatedBilinSection_apply (σ : SmoothTwoForm I M)
    (J : SmoothAlmostComplexStructure I M) (x : M) (u w : TangentSpace I x) :
    σ.associatedBilinSection J x u w = σ.eval₂ x u (J x w) := by
  have hval : σ.associatedBilinSection J x u w =
      (σ.flatComp (-J).toEndomorphism x).flip u w := rfl
  rw [hval, ContinuousLinearMap.flip_apply, flatComp_apply, ContinuousLinearMap.comp_apply,
    flat_apply]
  simp only [SmoothAlmostComplexStructure.neg_toEndomorphism, ContMDiffSection.coe_neg,
    Pi.neg_apply, _root_.neg_apply, SmoothBundleForm.eval₂_neg_left]
  rw [SmoothBundleForm.eval₂_swap, neg_neg]

end AssociatedBilinSection

namespace Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}

/-- **The smooth compatible Riemannian metric.** For a smooth two-form `σ` on a finite-dimensional
smooth manifold `M` and a `σ`-compatible smooth almost complex structure `J`, the fibrewise forms
`g_x(u, w) = σ_x(u, J_x w)` assemble into a smooth Riemannian metric on `TM`. -/
def riemannianMetric (h : σ.Compatible J) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) :=
  ContMDiffRiemannianMetric.ofPositiveDefiniteSection (σ.associatedBilinSection J) <|
    (Manifold.mem_positiveDefiniteBilinearSections _).2
      ⟨(Manifold.mem_symmetricBilinearSections _).2 fun x v w ↦ by
          rw [associatedBilinSection_apply, associatedBilinSection_apply]
          simpa only [SymplecticForm.associatedBilinForm_apply,
            IsNondegenerate.symplecticFormAt_apply,
            SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
            (h.compatibleAt x).associatedBilinForm_apply_swap v w,
        fun x v hv ↦ by
          rw [associatedBilinSection_apply]
          exact SmoothTwoForm.tames_iff.1 h.tames x v hv⟩

/-- The fibrewise inner product of `h.riemannianMetric` is `σ_x(u, J_x w)`. -/
@[simp]
theorem riemannianMetric_inner_apply (h : σ.Compatible J) (x : M) (u w : TangentSpace I x) :
    h.riemannianMetric.inner x u w = σ.eval₂ x u (J x w) := by
  rw [riemannianMetric, ContMDiffRiemannianMetric.ofPositiveDefiniteSection_inner,
    associatedBilinSection_apply]

/-- Installed as a `RiemannianBundle` on `TM`, `h.riemannianMetric` evaluates `⟪u, w⟫` to
`σ_x(u, J_x w)`. -/
theorem inner_eq_eval₂_riemannianMetric (h : σ.Compatible J) (x : M) (u w : TangentSpace I x) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨h.riemannianMetric.toRiemannianMetric⟩
    ⟪u, w⟫ = σ.eval₂ x u (J x w) :=
  h.riemannianMetric_inner_apply x u w

/-- A `σ`-compatible smooth almost complex structure `J` is fibrewise orthogonal for
`h.riemannianMetric`. -/
theorem inner_apply_apply_riemannianMetric (h : σ.Compatible J) (x : M)
    (u w : TangentSpace I x) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨h.riemannianMetric.toRiemannianMetric⟩
    ⟪J x u, J x w⟫ = ⟪u, w⟫ := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨h.riemannianMetric.toRiemannianMetric⟩
  rw [h.inner_eq_eval₂_riemannianMetric, h.inner_eq_eval₂_riemannianMetric]
  exact SmoothTwoForm.invariant_iff.1 h.invariant x u (J x w)

/-- The polar normalization of `σ` with respect to `h.riemannianMetric` recovers `J`. -/
@[simp]
theorem polarComplexStructure_riemannianMetric (h : σ.Compatible J) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨h.riemannianMetric.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle h.riemannianMetric
    h.isNondegenerate.polarComplexStructure = J := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨h.riemannianMetric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle h.riemannianMetric
  exact h.isNondegenerate.polarComplexStructure_eq_of_inner_eq h.inner_eq_eval₂_riemannianMetric

/-- The Kähler two-form `⟪J ·, ·⟫` of `J` with respect to `h.riemannianMetric` recovers `σ`. -/
@[simp]
theorem kahlerTwoForm_riemannianMetric (h : σ.Compatible J) :
    letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨h.riemannianMetric.toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
      Bundle.instIsContMDiffRiemannianBundle h.riemannianMetric
    J.kahlerTwoForm h.inner_apply_apply_riemannianMetric = σ := by
  let : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
    ⟨h.riemannianMetric.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) :=
    Bundle.instIsContMDiffRiemannianBundle h.riemannianMetric
  refine SmoothBundleForm.ext_eval₂_iff.2 fun x u w ↦ ?_
  rw [SmoothBundleForm.eval₂_apply, J.kahlerTwoForm_apply_two]
  have hg (v z : TangentSpace I x) :
      h.isNondegenerate.symplecticFormAt x v (J.almostComplexStructureAt x z) = ⟪v, z⟫ := by
    rw [IsNondegenerate.symplecticFormAt_apply,
      SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
    exact (h.inner_eq_eval₂_riemannianMetric x v z).symm
  have h1 := (h.isNondegenerate.symplecticFormAt x).inner_apply_left_eq_of_apply_apply_eq_inner
    hg u w
  rwa [SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    IsNondegenerate.symplecticFormAt_apply] at h1

end Compatible

end TauCeti.SmoothTwoForm
