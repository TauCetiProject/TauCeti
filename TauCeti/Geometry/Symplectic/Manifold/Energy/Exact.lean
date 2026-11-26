/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.Geometry.Manifold.DeRham.Integration.Exact
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Symplectic.Manifold.CurvePairing
import Mathlib.Analysis.Convex.Contractible
import TauCeti.Geometry.Manifold.DeRham.Integration.Homotopy

/-!
# Closed pseudoholomorphic curves in exact regions are constant

Let `u : C → X` be a smooth pseudoholomorphic map from a compact connected boundaryless surface
`(C, j)`, oriented so that the frames `(e, j e)` are positive, into an almost complex manifold
`(X, J)`, and let `form` be a smooth two-form on `X` taming `J` along `u`:
`form(v, J v) > 0` for every nonzero tangent vector `v` at a point of the image. The energy of `u`
is its symplectic area `∫_C u^* form`
(`TauCeti.SmoothTwoForm.energy_eq_integralTopForm_mpullback`), and when this area vanishes the
differential of `u` vanishes (`TauCeti.mfderiv_eq_zero_of_integralTopForm_mpullback_eq_zero`). So
`u` is constant as soon as its symplectic area vanishes, and Stokes' theorem gives this in the
following situations. All the results below are in the namespace `TauCeti`.

* **Exact regions.** If `u` maps `C` into an open subset `U` of `X` on which `form` is exact, then
  `u` is constant (`apply_eq_of_isPseudoholomorphicAt_of_range_subset`). The primitive of `form` on
  `U` need not extend to `X`. Equivalently, a nonconstant closed pseudoholomorphic curve leaves
  every such region (`exists_apply_notMem_of_isPseudoholomorphicAt`). When `form` is exact on all of
  `X`, every closed pseudoholomorphic curve is constant; this is
  `TauCeti.apply_eq_of_mem_exactForms`.
* **Acyclic regions.** For a closed `form`, the region `U` only needs `H²_dR(U) = 0`
  (`apply_eq_of_isPseudoholomorphicAt_of_subsingleton_deRhamCohomology`).
* **Null-homotopic curves.** For a closed `form` on a finite-dimensional Hausdorff manifold without
  boundary, a null-homotopic closed pseudoholomorphic curve is constant
  (`apply_eq_of_isPseudoholomorphicAt_of_nullhomotopic`), since homotopic maps have the same
  symplectic area. In particular a closed pseudoholomorphic curve lying in a contractible open
  subset of `X`, such as the image of a ball under an open embedding, is constant
  (`apply_eq_of_isPseudoholomorphicAt_of_range_subset_of_contractibleSpace`). So is one lying in the
  source of a chart whose target is star-shaped, such as a ball
  (`apply_eq_of_isPseudoholomorphicAt_of_range_subset_source`), and so is every closed
  pseudoholomorphic curve in a contractible manifold
  (`apply_eq_of_isPseudoholomorphicAt_of_contractibleSpace`). For a real normed space with any
  closed taming form this is `TauCeti.apply_eq_of_mem_closedForms_normedSpace`, which does not
  need finite dimension.

These are the inputs that confine pseudoholomorphic spheres in a localized transversality argument:
in Gromov's proof of the nonsqueezing theorem the almost complex structure is kept fixed on a
neighbourhood of a symplectically embedded ball, where the symplectic form is exact, and perturbed
only outside it. A nonconstant sphere cannot lie entirely in the fixed region, so it has points in
the perturbation region where its injective points can be sought.

## Main results

* `apply_eq_of_isPseudoholomorphicAt_of_range_subset`: a closed pseudoholomorphic curve in an open
  set on which the taming form is exact is constant.
* `exists_apply_notMem_of_isPseudoholomorphicAt`: a nonconstant closed pseudoholomorphic curve
  leaves every open set on which the taming form is exact.
* `apply_eq_of_isPseudoholomorphicAt_of_subsingleton_deRhamCohomology`: a closed pseudoholomorphic
  curve in an open set with vanishing second de Rham cohomology is constant, for a closed taming
  form.
* `apply_eq_of_isPseudoholomorphicAt_of_nullhomotopic`: a null-homotopic closed pseudoholomorphic
  curve is constant, for a closed taming form.
* `apply_eq_of_isPseudoholomorphicAt_of_range_subset_of_contractibleSpace`,
  `apply_eq_of_isPseudoholomorphicAt_of_contractibleSpace`: closed pseudoholomorphic curves in
  a contractible open set, or in a contractible manifold, are constant.
* `apply_eq_of_isPseudoholomorphicAt_of_range_subset_source`: closed pseudoholomorphic curves in the
  source of a chart with star-shaped target are constant.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (the energy identity, Lemma 2.2.1) and Section
  9.3 (the proof of the nonsqueezing theorem).
* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Inventiones Mathematicae 82
  (1985), 307–347.
-/

public section

noncomputable section

open Module TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {C : Type*} [TopologicalSpace C]
  [ChartedSpace H' C] [IsManifold I' ∞ C] [BoundarylessManifold I' C] [T2Space C]
  [CompactSpace C] [PreconnectedSpace C]
  {form : SmoothTwoForm I X} {J : SmoothAlmostComplexStructure I X}
  {j : SmoothAlmostComplexStructure I' C} {o : Manifold.Orientation I' C (Fin 2)} {u : C → X}

omit [BoundarylessManifold I' C] [T2Space C] in
/-- A closed pseudoholomorphic curve of zero symplectic area is constant, for a form taming `J`
along the curve. -/
private theorem apply_eq_of_integralTopForm_mpullback_eq_zero
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (harea : integralTopForm o (mpullback I' I u form.val) = 0) (c c' : C) : u c = u c' :=
  (hu.mdifferentiable (by simp)).apply_eq_of_mfderiv_eq_zero
    (mfderiv_eq_zero_of_integralTopForm_mpullback_eq_zero hu ho hhol htame
      (by rwa [SmoothForm.coe_mpullback])) c c'

/-- **Closed pseudoholomorphic curves in exact regions are constant.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, into an open subset `U` of `X` on which `form` is exact, and let
`form` tame `J` along `u`. Then `u` is constant: its symplectic area vanishes by Stokes' theorem.
The primitive of `form` on `U` need not extend to `X`. -/
theorem apply_eq_of_isPseudoholomorphicAt_of_range_subset
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (U : Opens X) (huU : Set.range u ⊆ U)
    (hform : SmoothForm.mpullback ((↑) : U → X) contMDiff_subtypeVal form ∈ exactForms I U 2)
    (c c' : C) : u c = u c' :=
  apply_eq_of_integralTopForm_mpullback_eq_zero ho hu hhol htame
    (integralTopForm_mpullback_eq_zero_of_range_subset o hu U huU hform) c c'

/-- **Nonconstant closed pseudoholomorphic curves leave exact regions.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, and let `form` tame `J` along `u`. If `u` is not constant, then it
maps some point outside every open subset `U` of `X` on which `form` is exact. -/
theorem exists_apply_notMem_of_isPseudoholomorphicAt
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    {c₀ c₁ : C} (hne : u c₀ ≠ u c₁) (U : Opens X)
    (hform : SmoothForm.mpullback ((↑) : U → X) contMDiff_subtypeVal form ∈ exactForms I U 2) :
    ∃ c, u c ∉ U := by
  by_contra! huU
  exact hne (apply_eq_of_isPseudoholomorphicAt_of_range_subset ho hu hhol htame U
    (Set.range_subset_iff.2 huU) hform c₀ c₁)

/-- **Closed pseudoholomorphic curves in acyclic regions are constant.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, into an open subset `U` of `X` with `H²_dR(U) = 0`, and let the
closed two-form `form` tame `J` along `u`. Then `u` is constant. -/
theorem apply_eq_of_isPseudoholomorphicAt_of_subsingleton_deRhamCohomology
    (hclosed : form.IsClosed)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (U : Opens X) [Subsingleton (deRhamCohomology I U 2)] (huU : Set.range u ⊆ U) (c c' : C) :
    u c = u c' :=
  apply_eq_of_integralTopForm_mpullback_eq_zero ho hu hhol htame
    (integralTopForm_mpullback_eq_zero_of_subsingleton_deRhamCohomology o hu U huU
      ((mem_closedForms I form).2 ((SmoothForm.isClosed_def form).1 hclosed))) c c'

variable [FiniteDimensional ℝ E] [BoundarylessManifold I X] [T2Space X]

/-- **Null-homotopic closed pseudoholomorphic curves are constant.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, into a finite-dimensional Hausdorff manifold `X` without boundary,
and let the closed two-form `form` tame `J` along `u`. If `u` is null-homotopic, then it is
constant: homotopic maps have the same symplectic area, and a constant map has area zero. -/
theorem apply_eq_of_isPseudoholomorphicAt_of_nullhomotopic (hclosed : form.IsClosed)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (hnull : (⟨u, hu.continuous⟩ : C(C, X)).Nullhomotopic) (c c' : C) : u c = u c' :=
  apply_eq_of_integralTopForm_mpullback_eq_zero ho hu hhol htame
    (integralTopForm_mpullback_eq_zero_of_nullhomotopic (f := ⟨u, hu.continuous⟩) o hu hnull
      ((mem_closedForms I form).2 ((SmoothForm.isClosed_def form).1 hclosed))) c c'

/-- **Closed pseudoholomorphic curves in contractible regions are constant.** Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, into a contractible open subset `U` of a finite-dimensional
Hausdorff manifold `X` without boundary, and let the closed two-form `form` tame `J` along `u`.
Then `u` is constant. -/
theorem apply_eq_of_isPseudoholomorphicAt_of_range_subset_of_contractibleSpace
    (hclosed : form.IsClosed)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (U : Opens X) [ContractibleSpace U] (huU : Set.range u ⊆ U) (c c' : C) : u c = u c' :=
  -- `u` factors through the contractible `U`, so it is null-homotopic in `X`.
  apply_eq_of_isPseudoholomorphicAt_of_nullhomotopic hclosed ho hu hhol htame
    (((id_nullhomotopic U).comp_left
      ⟨fun c ↦ ⟨u c, huU ⟨c, rfl⟩⟩, hu.continuous.subtype_mk fun c ↦ huU ⟨c, rfl⟩⟩).comp_right
      ⟨Subtype.val, continuous_subtypeVal⟩) c c'

/-- **Closed pseudoholomorphic curves in a star-shaped coordinate patch are constant.** Let `ψ` be
a local homeomorphism from a finite-dimensional Hausdorff manifold `X` without boundary to a real
normed space whose target is star-shaped, such as a chart onto a ball. Let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, into the source of `ψ`, and let the closed two-form `form` tame `J`
along `u`. Then `u` is constant. -/
theorem apply_eq_of_isPseudoholomorphicAt_of_range_subset_source {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (hclosed : form.IsClosed)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (ψ : OpenPartialHomeomorph X F) {x : F} (hψ : StarConvex ℝ x ψ.target)
    (huψ : Set.range u ⊆ ψ.source) (c c' : C) : u c = u c' := by
  have : ContractibleSpace ψ.target :=
    hψ.contractibleSpace ⟨ψ (u c), ψ.map_source (huψ ⟨c, rfl⟩)⟩
  have : ContractibleSpace (⟨ψ.source, ψ.open_source⟩ : Opens X) :=
    ψ.toHomeomorphSourceTarget.contractibleSpace
  exact apply_eq_of_isPseudoholomorphicAt_of_range_subset_of_contractibleSpace hclosed ho hu hhol
    htame ⟨ψ.source, ψ.open_source⟩ huψ c c'

/-- **Closed pseudoholomorphic curves in a contractible manifold are constant.** Let `X` be a
contractible finite-dimensional Hausdorff manifold without boundary, let `u` be a smooth
pseudoholomorphic map from a compact connected boundaryless surface `(C, j)`, oriented so that the
frames `(e, j e)` are positive, into `X`, and let the closed two-form `form` tame `J` along `u`.
Then `u` is constant. -/
theorem apply_eq_of_isPseudoholomorphicAt_of_contractibleSpace [ContractibleSpace X]
    (hclosed : form.IsClosed)
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I' c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    (hu : ContMDiff I' I ∞ u) (hhol : ∀ c, IsPseudoholomorphicAt j J u c)
    (htame : ∀ c (v : TangentSpace I (u c)), v ≠ 0 →
      0 < SmoothBundleForm.eval₂ form (u c) v (J (u c) v))
    (c c' : C) : u c = u c' :=
  apply_eq_of_isPseudoholomorphicAt_of_nullhomotopic hclosed ho hu hhol htame
    ((id_nullhomotopic X).comp_left ⟨u, hu.continuous⟩) c c'

end TauCeti
