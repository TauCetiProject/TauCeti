/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.ComplexStructure
public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Almost complex structures determined by a metric and a two-form

Let `M` be a manifold with a smooth Riemannian metric `g` and let `σ` be a smooth two-form on `M`.
The metric represents `σ` by a field of skew-adjoint endomorphisms `A` of the tangent spaces,
`g(A u, w) = σ(u, w)` (`TauCeti.SmoothTwoForm.innerOperator`). At each point `A` is the
contraction by the two-vector representing `σ` (`TauCeti.twoVectorContraction`), and the field `A`
is smooth, being the sharp musical isomorphism of `g` composed with the flat map `u ↦ σ(u, ·)`.

A smooth almost complex structure `J` with `g(u, v) = σ(u, J v)` is therefore `A` itself, so it is
unique, and it is compatible with `σ`. On a four-manifold with an orientation, the pointwise
characterization `TauCeti.exists_almostComplexStructure_inner_eq_iff` assembles into the
following statement: such a `J` exists if and only if at every point `σ` is self-dual or
anti-self-dual, `⋆σ = ±σ`, and has pointwise norm `|σ| = √2`. If the orientation is the
symplectic orientation of `σ`, in the sense that `⟨⋆σ, σ⟩ > 0` at every point (equivalently,
`σ ∧ σ` is a positive volume form), the condition is `⋆σ = σ` and `|σ| = √2`. Thus, for a
symplectic form on an oriented four-manifold, these are exactly the metrics of the form
`σ(·, J ·)` for a smooth `σ`-compatible `J`.

## Main definitions

* `TauCeti.SmoothTwoForm.innerOperator`: the smooth endomorphism field `A` with
  `g(A u, w) = σ(u, w)`.

## Main results

* `TauCeti.SmoothTwoForm.inner_innerOperator_apply`: its defining property.
* `TauCeti.SmoothAlmostComplexStructure.toEndomorphism_eq_innerOperator` and
  `TauCeti.SmoothAlmostComplexStructure.eq_of_inner_eq`: a smooth `J` with
  `g(u, v) = σ(u, J v)` is the operator of `σ`, so it is unique.
* `TauCeti.SmoothTwoForm.compatible_of_inner_eq`: such a `J` is compatible with `σ`.
* `TauCeti.SmoothTwoForm.exists_smoothAlmostComplexStructure_inner_eq_iff`: on an oriented
  four-manifold, such a `J` exists if and only if `⋆σ = ±σ` and `|σ|² = 2` at every point.
* `TauCeti.SmoothTwoForm.exists_smoothAlmostComplexStructure_inner_eq_iff_of_pos`: for the
  symplectic orientation, it exists if and only if `⋆σ = σ` and `|σ|² = 2` at every point.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford (2017).
* S. K. Donaldson and P. B. Kronheimer, *The Geometry of Four-Manifolds*, Oxford (1990).
-/

public section

noncomputable section

open Bundle Module exteriorPower
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace SmoothTwoForm

/-- A two-form at `x` is the inner product with the two-vector representing it:
`σ(u, w) = ⟪F, u ∧ w⟫`. -/
private theorem eval₂_eq_inner (σ : SmoothTwoForm I M) (x : M) (u w : TangentSpace I x) :
    σ.eval₂ x u w =
      ⟪(alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x), ιMulti ℝ 2 ![u, w]⟫ := by
  rw [inner_alternatingFormEquiv_symm_ιMulti, SmoothBundleForm.eval₂_apply]

/-- The operator of `σ` at a point: the contraction by the two-vector representing `σ`. -/
private def innerOperatorAt (σ : SmoothTwoForm I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (twoVectorContraction ((alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)))

private theorem inner_innerOperatorAt_apply (σ : SmoothTwoForm I M) (x : M)
    (u w : TangentSpace I x) : ⟪innerOperatorAt σ x u, w⟫ = σ.eval₂ x u w := by
  rw [innerOperatorAt, LinearMap.coe_toContinuousLinearMap', inner_twoVectorContraction_apply,
    eval₂_eq_inner]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The operator of a smooth two-form is a smooth section of the endomorphism bundle. -/
private theorem contMDiff_innerOperatorAt (σ : SmoothTwoForm I M) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞ (fun x ↦ TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) x (innerOperatorAt σ x)) := by
  -- The operator is the sharp map of the metric composed with the flat map `u ↦ σ(u, ·)`, and
  -- both are smooth sections of their `Hom` bundles.
  let g := Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle I M
  have hcomp (x : M) (u : TangentSpace I x) :
      innerOperatorAt σ x u = (g x).inverse (σ.flat x u) := by
    rw [g.inverse_apply, g.eq_sharp_iff]
    intro w
    rw [Manifold.ContMDiffNondegenerateMetric.ofRiemannianBundle_apply,
      inner_innerOperatorAt_apply, ContinuousLinearMap.coe_coe, flat_apply]
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  intro a
  set e := trivializationAt E (TangentSpace I) a
  have hbase : e.baseSet = (chartAt H a).source := TangentBundle.trivializationAt_baseSet a
  -- Test the section on the local frame of the tangent trivialization at `a`.
  refine (TauCeti.Manifold.contMDiffOn_hom_of_localFrame (Module.finBasis ℝ E) (e := e) (e' := e)
    (f := id) contMDiffOn_id (fun y hy ↦ ⟨hbase ▸ hy, hbase ▸ hy⟩) fun j ↦ ?_).contMDiffAt
    ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))
  have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y ↦ TotalSpace.mk' E y (e.localFrame (Module.finBasis ℝ E) j y))
      (chartAt H a).source := by
    rw [← hbase]
    exact e.contMDiffOn_localFrame_baseSet ∞ (Module.finBasis ℝ E) j
  simp only [id, hcomp, g.inverse_apply]
  exact g.contMDiffOn_sharp le_rfl (σ.contMDiff_flat.contMDiffOn.clm_bundle_apply hframe)

/-- **The operator of a two-form.** For a smooth two-form `σ` on a manifold with a smooth
Riemannian metric `g`, the smooth field `A` of endomorphisms of the tangent spaces with
`g(A u, w) = σ(u, w)` (`TauCeti.SmoothTwoForm.inner_innerOperator_apply`). At each point it is
the contraction by the two-vector representing `σ`
(`TauCeti.SmoothTwoForm.innerOperator_apply`). -/
def innerOperator (σ : SmoothTwoForm I M) :
    ContMDiffSection I (E →L[ℝ] E) ∞
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) where
  toFun := innerOperatorAt σ
  contMDiff_toFun := contMDiff_innerOperatorAt σ

/-- The defining property of the operator of `σ`: `g(A u, w) = σ(u, w)`. -/
@[simp]
theorem inner_innerOperator_apply (σ : SmoothTwoForm I M) (x : M) (u w : TangentSpace I x) :
    ⟪σ.innerOperator x u, w⟫ = σ.eval₂ x u w :=
  inner_innerOperatorAt_apply σ x u w

/-- At each point the operator of `σ` is the contraction `u ↦ u ⌟ F` by the two-vector `F`
representing `σ`, through `σ(u, w) = ⟪F, u ∧ w⟫`. -/
theorem innerOperator_apply (σ : SmoothTwoForm I M) (x : M) (u : TangentSpace I x) :
    σ.innerOperator x u =
      twoVectorContraction ((alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)) u :=
  (rfl)

end SmoothTwoForm

/-! ### Almost complex structures with `g(u, v) = σ(u, J v)` -/

variable {σ : SmoothTwoForm I M} {J K : SmoothAlmostComplexStructure I M}

omit [FiniteDimensional ℝ E] in
/-- A smooth almost complex structure with `g(u, v) = σ(u, J v)` is orthogonal. -/
private theorem inner_apply_apply_of_inner_eq
    (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M) (u v : TangentSpace I x) :
    ⟪J x u, J x v⟫ = ⟪u, v⟫ := by
  rw [hJ, SmoothAlmostComplexStructure.apply_apply, SmoothBundleForm.eval₂_neg_right,
    ← SmoothBundleForm.eval₂_swap, ← hJ, real_inner_comm]

omit [FiniteDimensional ℝ E] in
/-- A smooth almost complex structure with `g(u, v) = σ(u, J v)` represents `σ` through the
metric: `g(J u, w) = σ(u, w)`. -/
private theorem inner_apply_left_of_inner_eq
    (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) (x : M) (u w : TangentSpace I x) :
    ⟪J x u, w⟫ = σ.eval₂ x u w := by
  rw [← inner_apply_apply_of_inner_eq hJ x (J x u) w, SmoothAlmostComplexStructure.apply_apply,
    inner_neg_left, hJ x u (J x w), SmoothAlmostComplexStructure.apply_apply,
    SmoothBundleForm.eval₂_neg_right, neg_neg]

namespace SmoothTwoForm

omit [FiniteDimensional ℝ E] in
/-- **Compatibility.** A smooth almost complex structure with `g(u, v) = σ(u, J v)` is
compatible with `σ`: `σ` is `J`-invariant, and `σ(v, J v) = g(v, v) > 0` for `v ≠ 0`. -/
theorem compatible_of_inner_eq (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) :
    σ.Compatible J where
  invariant := invariant_iff.2 fun x u v ↦ by
    rw [← hJ]
    exact inner_apply_left_of_inner_eq hJ x u v
  tames := tames_iff.2 fun x v hv ↦ by
    rw [← hJ]
    exact real_inner_self_pos.2 hv

end SmoothTwoForm

namespace SmoothAlmostComplexStructure

omit [FiniteDimensional ℝ E] in
/-- **Uniqueness.** At most one smooth almost complex structure satisfies
`g(u, v) = σ(u, J v)`. -/
theorem eq_of_inner_eq (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v))
    (hK : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (K x v)) : J = K :=
  ext fun x u ↦ ext_inner_right ℝ fun w ↦ by
    rw [inner_apply_left_of_inner_eq hJ, inner_apply_left_of_inner_eq hK]

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- A smooth almost complex structure with `g(u, v) = σ(u, J v)` is the operator of `σ`. -/
theorem toEndomorphism_eq_innerOperator (hJ : ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) :
    J.toEndomorphism = σ.innerOperator := by
  have h (x : M) (u : TangentSpace I x) : J x u = σ.innerOperator x u :=
    ext_inner_right ℝ fun w ↦ by
      rw [inner_apply_left_of_inner_eq hJ, SmoothTwoForm.inner_innerOperator_apply]
  ext x u
  exact h x u

end SmoothAlmostComplexStructure

/-! ### Four-manifolds -/

namespace SmoothTwoForm

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  (o : Manifold.Orientation I M (Fin 4)) (σ : SmoothTwoForm I M)

/-- The two-vector representing `⋆σ` at `x` is the Hodge star of the two-vector representing
`σ`. -/
private theorem alternatingFormEquiv_symm_hodgeStar_apply (x : M) :
    letI := o.fact_finrank_tangentSpace x
    (alternatingFormEquiv (TangentSpace I x) 2).symm ((SmoothForm.hodgeStar o rfl σ).1 x) =
      (o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
        ((alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)) := by
  let := o.fact_finrank_tangentSpace x
  rw [LinearEquiv.symm_apply_eq, ← Orientation.formHodgeStar_alternatingFormEquiv,
    LinearEquiv.apply_symm_apply, ← RoughForm.hodgeStar_apply, ← SmoothForm.coe_hodgeStar]

/-- **Compatible almost complex structures on a four-manifold.** On an oriented four-manifold
with a smooth Riemannian metric `g`, a smooth two-form `σ` admits a smooth almost complex
structure `J` with `g(u, v) = σ(u, J v)` if and only if at every point `σ` is self-dual or
anti-self-dual, `⋆σ = ±σ`, and has pointwise norm `|σ| = √2`. Such a `J` is unique
(`TauCeti.SmoothAlmostComplexStructure.eq_of_inner_eq`) and compatible with `σ`
(`TauCeti.SmoothTwoForm.compatible_of_inner_eq`). -/
theorem exists_smoothAlmostComplexStructure_inner_eq_iff :
    (∃ J : SmoothAlmostComplexStructure I M, ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) ↔
      ∀ x, ((SmoothForm.hodgeStar o rfl σ).1 x = σ.1 x ∨
          (SmoothForm.hodgeStar o rfl σ).1 x = -σ.1 x) ∧
        alternatingFormInner (TangentSpace I x) 2 (σ.1 x) (σ.1 x) = 2 := by
  -- At each point, both conditions are those of the pointwise theorem for the two-vector `F`
  -- representing `σ`, read through `TauCeti.alternatingFormEquiv`.
  have hpt (x : M) : letI := o.fact_finrank_tangentSpace x
      (((SmoothForm.hodgeStar o rfl σ).1 x = σ.1 x ∨
          (SmoothForm.hodgeStar o rfl σ).1 x = -σ.1 x) ∧
        alternatingFormInner (TangentSpace I x) 2 (σ.1 x) (σ.1 x) = 2) ↔
      ((o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
            ((alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)) =
          (alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x) ∨
        (o.orientationAt x).hodgeStar (o.fact_finrank_tangentSpace x).out.symm
            ((alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)) =
          -(alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)) ∧
        ‖(alternatingFormEquiv (TangentSpace I x) 2).symm (σ.1 x)‖ ^ 2 = 2 := by
    rw [← alternatingFormEquiv_symm_hodgeStar_apply, ← map_neg,
      (alternatingFormEquiv (TangentSpace I x) 2).symm.injective.eq_iff,
      (alternatingFormEquiv (TangentSpace I x) 2).symm.injective.eq_iff,
      alternatingFormInner_apply, real_inner_self_eq_norm_sq]
  refine ⟨fun ⟨J, hJ⟩ x ↦ ?_, fun h ↦ ?_⟩
  · let := o.fact_finrank_tangentSpace x
    refine (hpt x).2 ((exists_almostComplexStructure_inner_eq_iff (o.orientationAt x)
      (o.fact_finrank_tangentSpace x).out.symm).1 ⟨J.almostComplexStructureAt x, fun u v ↦ ?_⟩)
    rw [hJ x u v, eval₂_eq_inner, SmoothAlmostComplexStructure.almostComplexStructureAt_apply]
  · -- The operator of `σ` squares to `-1`, by the pointwise theorem.
    have hsq (x : M) : (σ.innerOperator x).comp (σ.innerOperator x) =
        -ContinuousLinearMap.id ℝ (TangentSpace I x) := by
      let := o.fact_finrank_tangentSpace x
      obtain ⟨hF, hF₂⟩ := (hpt x).1 (h x)
      ext u
      have hu := LinearMap.congr_fun (twoVectorContraction_comp_self (o.orientationAt x) _ hF) u
      rw [hF₂] at hu
      simpa [innerOperator_apply] using hu
    refine ⟨⟨σ.innerOperator, hsq⟩, fun x u v ↦ ?_⟩
    let := o.fact_finrank_tangentSpace x
    obtain ⟨hF, hF₂⟩ := (hpt x).1 (h x)
    rw [eval₂_eq_inner]
    exact inner_eq_inner_ιMulti_twoVectorContraction (o.orientationAt x) _ hF hF₂ u v

/-- **Compatible almost complex structures for the symplectic orientation.** On a four-manifold
with a smooth Riemannian metric `g`, oriented so that `⟨⋆σ, σ⟩ > 0` at every point (that is,
`σ ∧ σ = ⟨⋆σ, σ⟩ vol` is positive), a smooth two-form `σ` admits a smooth almost complex
structure `J` with `g(u, v) = σ(u, J v)` if and only if `⋆σ = σ` and `σ` has pointwise norm
`|σ| = √2`. -/
theorem exists_smoothAlmostComplexStructure_inner_eq_iff_of_pos
    (ho : ∀ x, 0 < alternatingFormInner (TangentSpace I x) 2
      ((SmoothForm.hodgeStar o rfl σ).1 x) (σ.1 x)) :
    (∃ J : SmoothAlmostComplexStructure I M, ∀ x u v, ⟪u, v⟫ = σ.eval₂ x u (J x v)) ↔
      SmoothForm.hodgeStar o rfl σ = σ ∧
        ∀ x, alternatingFormInner (TangentSpace I x) 2 (σ.1 x) (σ.1 x) = 2 := by
  rw [exists_smoothAlmostComplexStructure_inner_eq_iff o, SmoothBundleForm.ext_iff]
  refine ⟨fun h ↦ ⟨fun x ↦ ?_, fun x ↦ (h x).2⟩, fun ⟨h, h₂⟩ x ↦ ⟨Or.inl ?_, h₂ x⟩⟩
  · -- `⋆σ = -σ` at `x` would make `⟨⋆σ, σ⟩ = -|σ|²` nonpositive.
    intro v
    rw [(h x).1.resolve_right fun hneg ↦ ?_]
    have hx := ho x
    rw [hneg, LinearMap.map_neg₂] at hx
    have := alternatingFormInner_self_nonneg (V := TangentSpace I x) (σ.1 x)
    linarith
  · ext v
    exact h x v

end SmoothTwoForm

end TauCeti
