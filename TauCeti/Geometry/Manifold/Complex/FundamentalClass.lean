/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions

/-!
# The fundamental class of a compact Riemann surface

A Riemann surface `M`, a complex manifold modelled on `𝓘(ℂ, ℂ)`, carries the canonical orientation
of its complex structure (`TauCeti.complexManifoldOrientation`): every holomorphic chart carries
it to the canonical orientation `complexOrientation ℂ` of `ℂ`, given by the real basis `(1, i)`.
Through `TauCeti.Manifold.Orientation.toHomologicalOrientation`, this orientation selects at every
point a generator of `H₂(M, M ∖ {x}; ℤ)`, giving the canonical homological orientation
`TauCeti.complexHomologicalOrientation M`. For `M` compact its fundamental class
`TauCeti.complexFundamentalClass M ∈ H₂(M; ℤ)` is the fundamental class of the complex
orientation, `[M]`. Characteristic numbers such as `c₁(E)[M]` are evaluations
`TauCeti.HomologicalOrientation.evalFundamentalClass` of top-degree classes on it, and the Euler
number of an oriented real plane bundle is the sum of the local indices of a section with finitely
many zeros (`TauCeti.VectorBundleOrientation.evalFundamentalClass_eulerClass_eq_sum_sectionIndex`).

The local orientation at `x` may be read in *any* holomorphic chart `e` at `x`, not only in the
preferred one: it is the local orientation selected in `e` by the standard orientation
`Complex.orientation` of `ℂ`, which is `complexOrientation ℂ` reindexed to `Fin 2`
(`TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`). Two holomorphic charts
differ by a holomorphic transition map, whose real Jacobian determinant is the squared modulus of
its complex derivative, hence positive, and a change of oriented chart multiplies the selected
local orientation by the sign of that determinant
(`OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul`).

Consequently the canonical homological orientation is natural. A local biholomorphism `j : M → N`
which is an open embedding pulls the canonical orientation of `N` back to that of `M`
(`TauCeti.comap_complexHomologicalOrientation`): a holomorphic chart of `N` at `j x` composed with
`j` is a holomorphic chart of `M` at `x`, and oriented-chart local orientations are natural
(`OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart`). Since a homeomorphism
carries the fundamental class of a pulled-back orientation to the fundamental class
(`TauCeti.HomologicalOrientation.mapFundamentalClass_comap`), a biholomorphism of compact Riemann
surfaces carries fundamental class to fundamental class
(`Diffeomorph.mapFundamentalClass_complexHomologicalOrientation`).

## Main definitions

* `TauCeti.complexHomologicalOrientation`: the canonical homological orientation of a Riemann
  surface.
* `TauCeti.complexFundamentalClass`: the fundamental class `[M] ∈ H₂(M; ℤ)` of a compact Riemann
  surface.

## Main results

* `TauCeti.complexHomologicalOrientation_apply`: the canonical local orientations, read in the
  preferred charts.
* `TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`: the canonical local
  orientations, read in any holomorphic chart.
* `TauCeti.comap_complexHomologicalOrientation`: local biholomorphisms that are open embeddings
  pull canonical homological orientations back to canonical homological orientations.
* `TauCeti.comap_subtypeVal_complexHomologicalOrientation`: the canonical homological orientation
  restricts to that of each open subset.
* `Diffeomorph.mapFundamentalClass_complexHomologicalOrientation`,
  `Diffeomorph.singularHomologyFunctor_map_complexFundamentalClass`: biholomorphisms carry
  fundamental classes to fundamental classes.
* `Diffeomorph.mapFundamentalClass_complexHomologicalOrientation_comp`: pushing the fundamental
  class forward along `f ∘ Φ`, for a biholomorphism `Φ`, is pushing it forward along `f`.

## Implementation notes

The model is `ℂ` itself, of real dimension `2 = 1 + 1`, as required by
`TauCeti.Manifold.Orientation.toHomologicalOrientation`; the homological orientation is that of
the canonical orientation reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`. Fundamental classes
need `M : Type`, as for `TauCeti.HomologicalOrientation.fundamentalClass`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52 (2012), Appendix C.3 (the Maslov index of a bundle pair as `c₁(E_F)[Σ_ℂ]`).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3 (local orientations and fundamental classes).
-/

public section

noncomputable section

open Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

open scoped ComplexManifold

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) 1 M]

variable (M) in
/-- The canonical homological orientation of a Riemann surface `M`. -/
def complexHomologicalOrientation : HomologicalOrientation M ℂ 2 :=
  ((complexManifoldOrientation ℂ M).reindex
    (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))
    ).toHomologicalOrientation (n := 1) Complex.finrank_real_complex

/-- The canonical homological orientation of a Riemann surface is the homological orientation of
its canonical orientation, reindexed from `Fin (2 * finrank ℂ ℂ)` to `Fin 2`. -/
theorem complexHomologicalOrientation_def :
    complexHomologicalOrientation M =
      ((complexManifoldOrientation ℂ M).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))
        ).toHomologicalOrientation (n := 1) Complex.finrank_real_complex :=
  (rfl)

/-- At every point `x`, the canonical homological orientation of a Riemann surface is the local
orientation selected in the preferred chart at `x` by the standard orientation
`Complex.orientation` of the model. -/
theorem complexHomologicalOrientation_apply (x : M) :
    complexHomologicalOrientation M x =
      (chartAt ℂ x).localOrientationOfOrientedChart (mem_chart_source ℂ x) Complex.orientation
        (n := 1) Complex.finrank_real_complex := by
  rw [complexHomologicalOrientation_def, Manifold.Orientation.toHomologicalOrientation_apply,
    localOrientationOfManifoldOrientation_eq, Manifold.Orientation.orientationAt_reindex,
    orientationAt_complexManifoldOrientation_eq_complexOrientation,
    ← reindex_complexOrientation_complex]
  -- The tangent space at `x` is `ℂ`, and the two reindexings are along the same cast of `Fin`.
  rfl

/-- **The canonical local orientations, read in any holomorphic chart.** At every point `x`, the
canonical homological orientation of a Riemann surface is the local orientation selected in any
`C^k` holomorphic chart `e` at `x`, for `k ≠ 0`, by the standard orientation `Complex.orientation`
of the model. -/
theorem complexHomologicalOrientation_apply_of_mem_maximalAtlas {k : ℕ∞ω} [NeZero k]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) k M) {x : M}
    (hx : x ∈ e.source) :
    complexHomologicalOrientation M x =
      e.localOrientationOfOrientedChart hx Complex.orientation (n := 1)
        Complex.finrank_real_complex := by
  rw [complexHomologicalOrientation_apply]
  -- The holomorphic transition from the preferred chart to `e` preserves orientation.
  have hmem := IsManifold.compatible_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)
    (IsManifold.maximalAtlas_subset_of_le (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne k)) he)
  have hy : chartAt ℂ x x ∈ ((chartAt ℂ x).symm.trans e).source := by
    simp [mem_chart_source, hx]
  obtain ⟨hd, hdet⟩ := orientationPreservingOn_iff.1 (mem_orientationPreservingGroupoid_iff.1
    (contDiffGroupoid_complex_le_orientationPreservingGroupoid 1 hmem)).1 _ hy
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
    differentiableWithinAt_univ, fderivWithin_univ, Function.id_comp, Function.comp_id,
    OpenPartialHomeomorph.coe_trans, id_eq] at hd hdet
  apply Subtype.ext
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart_eq_sign_det_smul _ _ (chartAt ℂ x) e
    (mem_chart_source ℂ x) hx hd.hasFDerivAt hdet.ne', sign_pos hdet, SignType.coe_one, one_smul]

variable {N : Type} [TopologicalSpace N] [T2Space N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ, ℂ) 1 N]

/-- **Naturality of the canonical homological orientation.** Pulling the canonical homological
orientation of `N` back along an open embedding `j : M → N` which is a `C^k` local
biholomorphism, for `k ≠ 0`, gives the canonical homological orientation of `M`. -/
theorem comap_complexHomologicalOrientation {k : ℕ∞ω} [NeZero k] {j : M → N}
    (hj : IsOpenEmbedding j)
    (hf : IsLocalDiffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k j) :
    (complexHomologicalOrientation N).comap hj = complexHomologicalOrientation M := by
  ext x : 1
  apply (hj.localOrientationEquiv x 2).injective
  rw [HomologicalOrientation.localOrientationEquiv_comap_apply]
  -- A holomorphic chart `e'` of `M` at `x` with `e' = ψ ∘ j` near `x`, for the preferred chart
  -- `ψ` of `N` at `j x`.
  set ψ := chartAt ℂ (j x)
  have hk : (1 : ℕ∞ω) ≤ k := ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne k)
  obtain ⟨e', he', hxe', hcomp⟩ := ((hf x).of_le hk).exists_mem_maximalAtlas_eventuallyEq
    (IsManifold.chart_mem_maximalAtlas (j x)) (mem_chart_source ℂ (j x))
  apply Subtype.ext
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas he' hxe',
    complexHomologicalOrientation_apply (j x), IsOpenEmbedding.coe_localOrientationEquiv,
    localHomologyIsoOfIsOpenEmbedding_hom]
  exact (OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart _ _
    ⟨j, hj.continuous⟩ e' ψ hxe' (mem_chart_source ℂ (j x)) hcomp.symm _).symm

/-- The canonical homological orientation of a Riemann surface restricts to the canonical
homological orientation of each open subset. -/
@[simp]
theorem comap_subtypeVal_complexHomologicalOrientation {U : TopologicalSpace.Opens M}
    (hj : IsOpenEmbedding (Subtype.val : U → M)) :
    (complexHomologicalOrientation M).comap hj = complexHomologicalOrientation U :=
  comap_complexHomologicalOrientation (k := 1) hj isLocalDiffeomorph_subtype_val

section CompactSpace

variable [CompactSpace M]

variable (M) in
/-- **The fundamental class of a compact Riemann surface** `[M] ∈ H₂(M; ℤ)`, for the canonical
orientation of its complex structure. -/
def complexFundamentalClass :
    ((TopCat.toSSet.obj (TopCat.of M)).homology (ModuleCat.of ℤ (ULift.{0} ℤ)) 2 :
      ModuleCat.{0} ℤ) :=
  (complexHomologicalOrientation M).fundamentalClass Complex.finrank_real_complex

/-- The fundamental class of a compact Riemann surface is that of its canonical homological
orientation. -/
theorem complexFundamentalClass_def :
    complexFundamentalClass M =
      (complexHomologicalOrientation M).fundamentalClass Complex.finrank_real_complex :=
  (rfl)

/-- **Biholomorphisms preserve fundamental classes.** A `C^k` biholomorphism `Φ : M ≃ N` of
compact Riemann surfaces, for `k ≠ 0`, carries the fundamental class of `M` to that of `N`. -/
theorem _root_.Diffeomorph.mapFundamentalClass_complexHomologicalOrientation [CompactSpace N]
    {k : ℕ∞ω} [NeZero k] (Φ : M ≃ₘ^k⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ N) :
    (complexHomologicalOrientation M).mapFundamentalClass Complex.finrank_real_complex
      (Φ.toHomeomorph : C(M, N)) = complexFundamentalClass N := by
  rw [← comap_complexHomologicalOrientation Φ.toHomeomorph.isOpenEmbedding
    Φ.isLocalDiffeomorph]
  exact HomologicalOrientation.mapFundamentalClass_comap _ _ Φ.toHomeomorph

/-- **Biholomorphisms preserve fundamental classes**, stated on singular homology: the map
`H₂(M; ℤ) → H₂(N; ℤ)` induced by a `C^k` biholomorphism `Φ : M ≃ N` of compact Riemann surfaces,
for `k ≠ 0`, carries `[M]` to `[N]`. -/
theorem _root_.Diffeomorph.singularHomologyFunctor_map_complexFundamentalClass [CompactSpace N]
    {k : ℕ∞ω} [NeZero k] (Φ : M ≃ₘ^k⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ N) :
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj
      (ModuleCat.of ℤ (ULift.{0} ℤ))).map (TopCat.ofHom (Φ.toHomeomorph : C(M, N)))).hom
        (complexFundamentalClass M) = complexFundamentalClass N := by
  rw [complexFundamentalClass_def, ← HomologicalOrientation.mapFundamentalClass_def]
  exact Φ.mapFundamentalClass_complexHomologicalOrientation

/-- The image of the fundamental class of a compact Riemann surface `M` under a composite
`f ∘ Φ`, for a `C^k` biholomorphism `Φ : M ≃ N` with `k ≠ 0`, is the image of the fundamental
class of `N` under `f`. -/
theorem _root_.Diffeomorph.mapFundamentalClass_complexHomologicalOrientation_comp
    [CompactSpace N] {X : Type} [TopologicalSpace X] {k : ℕ∞ω} [NeZero k]
    (Φ : M ≃ₘ^k⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ N) (f : C(N, X)) :
    (complexHomologicalOrientation M).mapFundamentalClass Complex.finrank_real_complex
      (f.comp (Φ.toHomeomorph : C(M, N))) =
      (complexHomologicalOrientation N).mapFundamentalClass Complex.finrank_real_complex f := by
  rw [← comap_complexHomologicalOrientation Φ.toHomeomorph.isOpenEmbedding
    Φ.isLocalDiffeomorph]
  exact HomologicalOrientation.mapFundamentalClass_comap_comp _ _ Φ.toHomeomorph f

end CompactSpace

end TauCeti
