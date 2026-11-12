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
preferred one: it is the local orientation selected in `e` by `complexOrientation ℂ`
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

* `TauCeti.complexHomologicalOrientation_apply_of_mem_maximalAtlas`: the canonical local
  orientations, read in any holomorphic chart.
* `TauCeti.comap_complexHomologicalOrientation`: open local biholomorphisms pull canonical
  homological orientations back to canonical homological orientations.
* `Diffeomorph.mapFundamentalClass_complexHomologicalOrientation`: biholomorphisms carry
  fundamental classes to fundamental classes.

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

omit [T2Space M] in
/-- The reindexed canonical orientation is represented by the reindexed canonical lift. -/
private theorem reindex_complexManifoldOrientation_eq_mk :
    (complexManifoldOrientation ℂ M).reindex
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex)) =
      Manifold.Orientation.mk ((complexOrientationLift ℂ M).reindex
        (finCongr Complex.finrank_real_complex)) := by
  ext x
  simp only [Manifold.Orientation.orientationAt_reindex, Manifold.Orientation.orientationAt_mk,
    Manifold.OrientationLift.orientationAt_reindex, orientationAt_complexOrientationLift,
    orientationAt_complexManifoldOrientation_eq_complexOrientation]
  -- The tangent space at `x` is `ℂ`, and reindexing twice is reindexing along the composite.
  exact Orientation.reindex_trans (M := ℂ) (finCongr (finrank_real_of_complex ℂ).symm)
    (finCongr Complex.finrank_real_complex) (complexOrientation ℂ)

/-- **The canonical local orientations, read in any holomorphic chart.** At every point `x`, the
canonical homological orientation of a Riemann surface is the local orientation selected in any
holomorphic chart `e` at `x` by the canonical real orientation `complexOrientation ℂ` of the
model. -/
theorem complexHomologicalOrientation_apply_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) 1 M) {x : M}
    (hx : x ∈ e.source) :
    complexHomologicalOrientation M x =
      e.localOrientationOfOrientedChart hx (Orientation.reindex ℝ ℂ
        (finCongr ((finrank_real_of_complex ℂ).symm.trans Complex.finrank_real_complex))
        (complexOrientation ℂ)) (n := 1) Complex.finrank_real_complex := by
  rw [complexHomologicalOrientation_def, Manifold.Orientation.toHomologicalOrientation_apply,
    reindex_complexManifoldOrientation_eq_mk, localOrientationOfManifoldOrientation_mk,
    Manifold.OrientationLift.chartOrientation_eq_ite]
  simp only [Manifold.OrientationLift.reindex_sign, complexOrientationLift_sign, ite_true,
    Manifold.OrientationLift.reindex_modelOrientation, complexOrientationLift_modelOrientation,
    ← Orientation.reindex_trans]
  -- The holomorphic transition from the preferred chart to `e` preserves orientation.
  have hmem := IsManifold.compatible_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) he
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
  -- The two reindexings of `complexOrientation ℂ` are along the same cast of `Fin`.
  rfl

variable {N : Type} [TopologicalSpace N] [T2Space N] [ChartedSpace ℂ N] [IsManifold 𝓘(ℂ, ℂ) 1 N]

/-- **Naturality of the canonical homological orientation.** Pulling the canonical homological
orientation of `N` back along an open embedding `j : M → N` which is a `C^k` local
biholomorphism, for `k ≠ 0`, gives the canonical homological orientation of `M`. -/
theorem comap_complexHomologicalOrientation (k : ℕ∞ω) [NeZero k] [IsManifold 𝓘(ℂ, ℂ) k M]
    [IsManifold 𝓘(ℂ, ℂ) k N] {j : M → N} (hj : IsOpenEmbedding j)
    (hf : IsLocalDiffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) k j) :
    (complexHomologicalOrientation N).comap hj = complexHomologicalOrientation M := by
  ext x : 1
  apply (hj.localOrientationEquiv x 2).injective
  rw [HomologicalOrientation.localOrientationEquiv_comap_apply]
  -- A holomorphic chart `φ` of `M` at `x` with `φ = ψ ∘ j` on its source, for the preferred chart
  -- `ψ` of `N` at `j x`.
  set ψ := chartAt ℂ (j x)
  obtain ⟨e', he', hxe', hcomp⟩ := (hf x).exists_mem_maximalAtlas_eventuallyEq
    (IsManifold.chart_mem_maximalAtlas (j x)) (mem_chart_source ℂ (j x))
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1 (Filter.inter_mem hcomp
    (hj.continuous.continuousAt.preimage_mem_nhds (ψ.open_source.mem_nhds
      (mem_chart_source ℂ (j x)))))
  have hk : (1 : ℕ∞ω) ≤ k := ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne k)
  have hφ : e'.restr W ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) 1 M :=
    restr_mem_maximalAtlas (contDiffGroupoid 1 𝓘(ℂ, ℂ))
      (IsManifold.maximalAtlas_subset_of_le hk he') hWo
  have hsrc : (e'.restr W).source = e'.source ∩ W := e'.restr_source' W hWo
  have hxφ : x ∈ (e'.restr W).source := hsrc ▸ ⟨hxe', hxW⟩
  apply Subtype.ext
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas hφ hxφ,
    complexHomologicalOrientation_apply_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (j x)) (mem_chart_source ℂ (j x)),
    IsOpenEmbedding.coe_localOrientationEquiv, localHomologyIsoOfIsOpenEmbedding_hom]
  exact (OpenPartialHomeomorph.localHomologyMap_localOrientationOfOrientedChart _ _
    ⟨j, hj.continuous⟩ (e'.restr W) ψ hxφ
    (fun y hy ↦ (hWsub (hsrc ▸ hy).2).2)
    (fun y hy ↦ ((hWsub (hsrc ▸ hy).2).1).symm.trans (congrFun (e'.restr_apply W) y).symm) _).symm

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
    (k : ℕ∞ω) [NeZero k] [IsManifold 𝓘(ℂ, ℂ) k M] [IsManifold 𝓘(ℂ, ℂ) k N]
    (Φ : M ≃ₘ^k⟮𝓘(ℂ, ℂ), 𝓘(ℂ, ℂ)⟯ N) :
    (complexHomologicalOrientation M).mapFundamentalClass Complex.finrank_real_complex
      (Φ.toHomeomorph : C(M, N)) = complexFundamentalClass N := by
  rw [← comap_complexHomologicalOrientation k Φ.toHomeomorph.isOpenEmbedding
    Φ.isLocalDiffeomorph]
  exact HomologicalOrientation.mapFundamentalClass_comap _ _ Φ.toHomeomorph

end CompactSpace

end TauCeti
