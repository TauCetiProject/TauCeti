/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Linear
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Analysis.Complex.UnitDisc.Manifold
public import TauCeti.Analysis.Complex.UnitDisc.Subdisc
public import TauCeti.Geometry.Manifold.Complex.Orientation
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Sigma
public import TauCeti.Topology.OpenPartialHomeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Deriv

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
* `TauCeti.localHomologyMap_complexHomologicalOrientation_of_mem_maximalAtlas`: a holomorphic chart,
  centred at a point of its source, carries the canonical local orientation there to the local
  orientation of `ℂ` at `0` selected by `Complex.orientation`.
* `TauCeti.comap_complexHomologicalOrientation`: local biholomorphisms that are open embeddings
  pull canonical homological orientations back to canonical homological orientations.
* `TauCeti.comap_subtypeVal_complexHomologicalOrientation`: the canonical homological orientation
  restricts to that of each open subset.
* `TauCeti.comap_complexHomologicalOrientation_of_mem_maximalAtlas`: on an open subset of the
  source of a holomorphic chart, the canonical homological orientation is pulled back from that of
  `ℂ` along the chart.
* `TauCeti.comap_coe_comp_subdisc_complexHomologicalOrientation`: the round subdisc maps of the
  open unit disc preserve the restriction of the canonical homological orientation of `ℂ`.
* `Diffeomorph.mapFundamentalClass_complexHomologicalOrientation`,
  `Diffeomorph.singularHomologyFunctor_map_complexFundamentalClass`: biholomorphisms carry
  fundamental classes to fundamental classes.
* `Diffeomorph.mapFundamentalClass_complexHomologicalOrientation_comp`: pushing the fundamental
  class forward along `f ∘ Φ`, for a biholomorphism `Φ`, is pushing it forward along `f`.
* `TauCeti.comap_sigmaMk_complexHomologicalOrientation`: the canonical homological orientation of
  a disjoint union of Riemann surfaces restricts to that of each component.
* `TauCeti.complexFundamentalClass_sigma`: the fundamental class of a finite disjoint union of
  compact Riemann surfaces is the sum of the images of the fundamental classes of its components.

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

/-- **The canonical orientation read in a holomorphic chart.** A `C^k` holomorphic chart `e` of a
Riemann surface, for `k ≠ 0`, centred at a point `z` of its source, carries the canonical local
orientation at `z` to the local orientation of `ℂ` at `0` selected by its standard orientation
`Complex.orientation`. -/
theorem localHomologyMap_complexHomologicalOrientation_of_mem_maximalAtlas {k : ℕ∞ω} [NeZero k]
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) k M) {z : M}
    (hz : z ∈ e.source) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{0} ℤ))
        (⟨fun x : e.source ↦ e x - e z, e.continuousOn.domRestrict.sub continuous_const⟩ :
          C(e.source, ℂ)) (S := {⟨z, hz⟩}) (T := {0})
        (by
          rintro x hx
          exact Subtype.ext (e.injOn x.property hz (sub_eq_zero.1 hx))) (1 + 1)
        ((e.open_source.isOpenEmbedding_subtypeVal.localOrientationEquiv ⟨z, hz⟩
          (1 + 1)).symm (complexHomologicalOrientation M z)).val =
      (Complex.orientation.localOrientation Complex.finrank_real_complex).val := by
  set φ := e
  rw [complexHomologicalOrientation_apply_of_mem_maximalAtlas he hz]
  have hσ : (((ContinuousLinearEquiv.refl ℝ ℂ : ℂ →L[ℝ] ℂ) : C(ℂ, ℂ)).comp
      ((⟨fun y ↦ y - φ z, by fun_prop⟩ : C(ℂ, ℂ)).comp φ.sourceRestrict)) =
      (⟨fun y : φ.source ↦ φ y - φ z,
        φ.continuousOn.domRestrict.sub continuous_const⟩ : C(φ.source, ℂ)) :=
    ContinuousMap.ext fun y ↦ congrArg (fun w ↦ w - φ z) (φ.sourceRestrict_apply y)
  have hφ := φ.localHomologyMap_chart_localOrientationOfOrientedChart hz
    (ContinuousLinearEquiv.refl ℝ ℂ) Complex.orientation
    Complex.finrank_real_complex Complex.finrank_real_complex (by
      rw [hσ]
      exact fun y hy ↦ Subtype.ext (φ.injOn y.property hz (sub_eq_zero.1 hy)))
  simp only [hσ] at hφ
  -- `Orientation.map` uses the underlying linear identity, rather than the continuous structure.
  have hid : (ContinuousLinearEquiv.refl ℝ ℂ).toLinearEquiv = LinearEquiv.refl ℝ ℂ := (rfl)
  simpa only [hid, Orientation.map_refl, Equiv.refl_apply] using hφ

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

/-- The canonical homological orientation of an open subset `U` of a Riemann surface `M`, lying in
the source of a holomorphic chart `e`, is pulled back from the canonical homological orientation
of `ℂ` along `e`. -/
theorem comap_complexHomologicalOrientation_of_mem_maximalAtlas {e : OpenPartialHomeomorph M ℂ}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) 1 M) {U : TopologicalSpace.Opens M}
    (hU : (U : Set M) ⊆ e.source) :
    (complexHomologicalOrientation ℂ).comap
        (e.isOpenEmbedding_comp U.isOpenEmbedding' (by simpa using hU)) =
      complexHomologicalOrientation U :=
  comap_complexHomologicalOrientation (k := 1) _ fun u ↦
    IsLocalDiffeomorphAt.comp (K := 𝓘(ℂ, ℂ)) (P := ℂ) (isLocalDiffeomorph_subtype_val u)
      (e.isLocalDiffeomorphAt_of_mem_maximalAtlas he (hU u.property))

/-- The round subdisc maps `z ↦ c + r z`, `r > 0`, of the open unit disc
(`TauCeti.Complex.UnitDisc.subdisc`), read in `ℂ`, pull the canonical homological orientation of
`ℂ` back to its restriction to `𝔻`: they are restrictions of the affine map `w ↦ c + r w`, a
holomorphic diffeomorphism of `ℂ`. -/
theorem comap_coe_comp_subdisc_complexHomologicalOrientation {c : ℂ} {r : ℝ} {hc : ‖c‖ + r ≤ 1}
    {hr : 0 < r} :
    (complexHomologicalOrientation ℂ).comap
        (Complex.UnitDisc.isOpenEmbedding_coe_comp_subdisc (hc := hc) (hr := hr)) =
      (complexHomologicalOrientation ℂ).comap Complex.UnitDisc.isOpenEmbedding_coe := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set A := affineHomeomorph (r : ℂ) c hr0
  have hA : ⇑A = fun w ↦ r * w + c := funext (affineHomeomorph_apply _ _ hr0)
  have hloc : IsLocalDiffeomorph 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) 1 A :=
    isLocalDiffeomorph_of_deriv_ne_zero (by rw [hA]; fun_prop) le_rfl fun w ↦ by
      simpa [hA] using hr0
  refine (HomologicalOrientation.comap_comap_of_comp_eq _ A.isOpenEmbedding
    Complex.UnitDisc.isOpenEmbedding_coe _ Complex.UnitDisc.coe_comp_subdisc.symm).symm.trans ?_
  rw [comap_complexHomologicalOrientation A.isOpenEmbedding hloc]

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

section Sigma

variable {ι : Type} {C : ι → Type} [∀ i, TopologicalSpace (C i)] [∀ i, T2Space (C i)]
  [∀ i, ChartedSpace ℂ (C i)] [∀ i, IsManifold 𝓘(ℂ, ℂ) 1 (C i)]

/-- The canonical homological orientation of a disjoint union of Riemann surfaces restricts to the
canonical homological orientation of each component. -/
@[simp]
theorem comap_sigmaMk_complexHomologicalOrientation (i : ι) :
    (complexHomologicalOrientation (Σ i, C i)).comap (IsOpenEmbedding.sigmaMk (σ := C) (i := i)) =
      complexHomologicalOrientation (C i) :=
  comap_complexHomologicalOrientation (k := 1) _ (isLocalDiffeomorph_sigmaMk i)

/-- **The fundamental class of a finite disjoint union of compact Riemann surfaces** is the sum of
the images of the fundamental classes of its components under their inclusions. -/
theorem complexFundamentalClass_sigma [Fintype ι] [∀ i, CompactSpace (C i)] :
    complexFundamentalClass (Σ i, C i) =
      ∑ i, (complexHomologicalOrientation (C i)).mapFundamentalClass Complex.finrank_real_complex
        ⟨Sigma.mk i, continuous_sigmaMk⟩ := by
  rw [complexFundamentalClass_def,
    HomologicalOrientation.fundamentalClass_eq_sum_mapFundamentalClass_comap _ _
      (j := fun i ↦ ⟨Sigma.mk i, continuous_sigmaMk⟩) (fun _ ↦ IsOpenEmbedding.sigmaMk)
      (fun i k hik ↦ disjoint_left.2 ?_) fun p ↦ ⟨p.1, p.2, rfl⟩]
  · simp only [comap_sigmaMk_complexHomologicalOrientation]
    -- The two sums agree up to reading `SSet.homology` as the singular homology functor.
    rfl
  · rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
    exact hik (congrArg Sigma.fst hy).symm

end Sigma

end TauCeti
