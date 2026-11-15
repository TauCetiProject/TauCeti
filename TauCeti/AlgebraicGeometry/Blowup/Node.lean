/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
public import TauCeti.AlgebraicGeometry.Curves.Node.Relative
public import TauCeti.RingTheory.Node.Blowup
public import TauCeti.AlgebraicGeometry.Scheme.Regular.LocalRing
public import TauCeti.RingTheory.RegularLocalRing.Node.Basic
import TauCeti.AlgebraicGeometry.Blowup.AwayFromCenter

/-!
# The blowup of the node `xy = π²a` at its origin

Let `π` be a nonzerodivisor of a commutative ring `R`, let `a ∈ R`, and put
`A = R[x, y] ⧸ (xy - π²a)`. Let `I = (π, x, y)` be the ideal of the origin
(`TauCeti.NodeAlgebra.originIdeal`). This file describes the blowup `Proj A[It]` of `Spec A`
along `V(I)` as a scheme over `Spec R`:

* it is covered by three open charts, the `π`-chart `Spec R[u, v] ⧸ (uv - a)` and, for each
  coordinate, the chart `Spec R[x, t] ⧸ (xt - π)`;
* on the `π`-chart, the chart of the coordinate `xᵢ = π uᵢ` is the basic open `D(uᵢ)`, so the
  part of the blowup outside the two coordinate charts is the closed subset `V(u, v)` of the
  `π`-chart; the part of the blowup over `D(xᵢ)` lies in the chart of `xᵢ`;
* consequently its structure morphism is at worst nodal of relative dimension one over
  `Spec R`, like `Spec A` itself.

For `a = πⁿ` over a discrete valuation ring with uniformizer `π`, the coordinate charts are
regular and the `π`-chart is regular exactly when `n ≤ 1`. Thus a single blowup of the origin
turns the nodes `xy = π²` and `xy = π³` into regular schemes, while for `n ≥ 2` the blowup is
still singular. More precisely, for `n ≥ 2` the blowup is singular at exactly one point: the
origin `(π, u, v)` of the `π`-chart, a closed point of the blowup, near which the blowup is the
node `uv = πⁿ` of thickness lowered by two. This is the local computation behind the resolution
of nodal models of curves by repeatedly blowing up the remaining singular point.

## Main definitions

* `TauCeti.NodeAlgebra.blowupToSpec π a`: the structure morphism `Proj A[It] ⟶ Spec R` of the
  blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartι`: the open immersion of the `π`-chart
  `Spec R[u, v] ⧸ (uv - a)` into the blowup.
* `TauCeti.NodeAlgebra.blowupCoordChartι`: the open immersion of the chart
  `Spec R[x, t] ⧸ (xt - π)` of a coordinate `xᵢ` into the blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartOrigin`: for a local ring `R` and `a ∈ 𝔪_R`, the origin of
  the `π`-chart, the image of the maximal ideal `(𝔪_R, u, v)`.

## Main results

* `TauCeti.NodeAlgebra.opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι`: the
  three charts cover the blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartι_blowupToSpec`,
  `TauCeti.NodeAlgebra.blowupCoordChartι_blowupToSpec`: the charts are morphisms over `Spec R`.
* `TauCeti.NodeAlgebra.preimage_basicOpen_coord_le_opensRange_blowupCoordChartι`: the part of the
  blowup lying over `D(xᵢ)` is contained in the chart of `xᵢ`.
* `TauCeti.NodeAlgebra.isProper_blowup`: the blowup is proper over `Spec A`.
* `TauCeti.NodeAlgebra.isIso_morphismRestrict_iSup_basicOpen_coord`: the blowup is an isomorphism
  over `D(x₀) ∪ D(x₁)`.
* `TauCeti.NodeAlgebra.flat_blowup`, `TauCeti.NodeAlgebra.locallyOfFinitePresentation_blowup`,
  `TauCeti.NodeAlgebra.pureRelativeDimension_blowup`: the blowup is flat, locally of finite
  presentation and of pure relative dimension one over `Spec R`.
* `TauCeti.NodeAlgebra.atWorstNodalOfRelativeDimensionOne_blowup`: the blowup remains a nodal
  relative curve over `Spec R`.
* `TauCeti.NodeAlgebra.isRegularLocalRing_stalk_blowup_iff`: over a discrete valuation ring,
  for `a = πⁿ`, every local ring of the blowup is regular exactly when `n ≤ 1`.
* `TauCeti.NodeAlgebra.blowupBaseChartι_preimage_opensRange_blowupCoordChartι`: the `π`-chart
  meets the chart of `xᵢ` in the basic open set `D(xᵢ/π)`.
* `TauCeti.NodeAlgebra.isClosed_singleton_blowupBaseChartOrigin`: the origin of the `π`-chart is
  a closed point of the blowup.
* `TauCeti.NodeAlgebra.isRegularLocalRing_stalk_blowup_iff_ne`: over a discrete valuation ring,
  for `a = πⁿ` with `n ≥ 2`, the local ring of the blowup at a point is regular exactly when the
  point is not the origin of the `π`-chart, where the local ring is that of `uv = πⁿ`
  (`TauCeti.NodeAlgebra.isRegularLocalRing_stalk_blowupBaseChartOrigin_iff`).

## References

* [The Stacks Project, Example 55.14.1](https://stacks.math.columbia.edu/tag/0CDC)
* [The Stacks Project, Section *Blowing up*](https://stacks.math.columbia.edu/tag/01OF)
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry reesAlgebra Ideal

namespace TauCeti.NodeAlgebra

universe u

variable {R : Type u} [CommRing R]

variable (π a : R) in
/-- The structure morphism `Proj A[It] ⟶ Spec A ⟶ Spec R` of the blowup of
`A = R[x, y] ⧸ (xy - π²a)` along `I = (π, x, y)`, as a scheme over `Spec R`. -/
def blowupToSpec : Proj (grade (originIdeal π (π ^ 2 * a))) ⟶ Spec (.of R) :=
  Proj.toSpecZero (grade (originIdeal π (π ^ 2 * a))) ≫
    Spec.map (gradeZeroEquiv (originIdeal π (π ^ 2 * a))).toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (π ^ 2 * a))))

theorem blowupToSpec_def (π a : R) :
    blowupToSpec π a = Proj.toSpecZero (grade (originIdeal π (π ^ 2 * a))) ≫
      Spec.map (gradeZeroEquiv (originIdeal π (π ^ 2 * a))).toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (π ^ 2 * a)))) :=
  (rfl)

variable {π : R} (a : R)

/-- **The `π`-chart of the blowup of a node.** For a nonzerodivisor `π` of `R`, the open
immersion `Spec R[u, v] ⧸ (uv - a) ⟶ Proj A[It]` into the blowup of `A = R[x, y] ⧸ (xy - π²a)`
along `I = (π, x, y)`, with `u = x/π` and `v = y/π`. Its image is the standard open `D₊(π t)`. -/
def blowupBaseChartι (hπ : π ∈ nonZeroDivisors R) :
    Spec (.of (NodeAlgebra R a)) ⟶ Proj (grade (originIdeal π (π ^ 2 * a))) :=
  Spec.map (RingEquiv.toCommRingCatIso (affineBlowupBaseEquiv a
      (Localization.Away (algebraMap R (NodeAlgebra R (π ^ 2 * a)) π)) hπ).symm.toRingEquiv).hom ≫
    affineBlowupι _ (algebraMap_mem_originIdeal π _)

instance (hπ : π ∈ nonZeroDivisors R) : IsOpenImmersion (blowupBaseChartι a hπ) := by
  rw [blowupBaseChartι]
  infer_instance

/-- The `π`-chart of the blowup of the node is an open immersion onto the standard open
`D₊(π t)`. -/
theorem opensRange_blowupBaseChartι (hπ : π ∈ nonZeroDivisors R) :
    (blowupBaseChartι a hπ).opensRange =
      Proj.basicOpen _ (monomialDegreeOne (algebraMap_mem_originIdeal π (π ^ 2 * a))) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (opensRange_affineBlowupι _ _)

/-- The `π`-chart of the blowup of the node is a morphism over `Spec R`: followed by the
structure map `Proj A[It] ⟶ Spec A ⟶ Spec R`, it is the structure map of `R[u, v] ⧸ (uv - a)`. -/
@[reassoc (attr := simp)]
theorem blowupBaseChartι_blowupToSpec (hπ : π ∈ nonZeroDivisors R) :
    blowupBaseChartι a hπ ≫ blowupToSpec π a =
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a))) := by
  rw [blowupToSpec_def, blowupBaseChartι, Category.assoc, affineBlowupι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp [← IsScalarTower.algebraMap_apply]

/-- **The coordinate charts of the blowup of a node.** For a nonzerodivisor `π` of `R`, the open
immersion `Spec R[x, t] ⧸ (xt - π) ⟶ Proj A[It]` into the blowup of
`A = R[x₀, x₁] ⧸ (x₀x₁ - π²a)` along `I = (π, x₀, x₁)`, with `x = xᵢ` and `t = π/xᵢ`. Its image
is the standard open `D₊(xᵢ t)`. -/
def blowupCoordChartι (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    Spec (.of (NodeAlgebra R π)) ⟶ Proj (grade (originIdeal π (π ^ 2 * a))) :=
  Spec.map (RingEquiv.toCommRingCatIso (affineBlowupCoordEquiv a i
      (Localization.Away (coord (π ^ 2 * a) i)) hπ).symm.toRingEquiv).hom ≫
    affineBlowupι _ (coord_mem_originIdeal π _ i)

instance (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    IsOpenImmersion (blowupCoordChartι a i hπ) := by
  rw [blowupCoordChartι]
  infer_instance

/-- The chart of the coordinate `xᵢ` of the blowup of the node is an open immersion onto the
standard open `D₊(xᵢ t)`. -/
theorem opensRange_blowupCoordChartι (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    (blowupCoordChartι a i hπ).opensRange =
      Proj.basicOpen _ (monomialDegreeOne (coord_mem_originIdeal π (π ^ 2 * a) i)) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (opensRange_affineBlowupι _ _)

/-- The chart of a coordinate of the blowup of the node is a morphism over `Spec R`: followed by
the structure map `Proj A[It] ⟶ Spec A ⟶ Spec R`, it is the structure map of
`R[x, t] ⧸ (xt - π)`. -/
@[reassoc (attr := simp)]
theorem blowupCoordChartι_blowupToSpec (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    blowupCoordChartι a i hπ ≫ blowupToSpec π a =
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R π))) := by
  rw [blowupToSpec_def, blowupCoordChartι, Category.assoc, affineBlowupι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp [← IsScalarTower.algebraMap_apply]

/-- **The blowup over `D(xᵢ)` lies in the chart of `xᵢ`.** For a nonzerodivisor `π` of `R`, the
inverse image in the blowup `Proj A[It]` of `A = R[x₀, x₁] ⧸ (x₀x₁ - π²a)` of the basic open
`D(xᵢ)` of `Spec A` is contained in the chart `Spec R[x, t] ⧸ (xt - π)` of `xᵢ`. -/
theorem preimage_basicOpen_coord_le_opensRange_blowupCoordChartι (i : Fin 2)
    (hπ : π ∈ nonZeroDivisors R) :
    (Proj.toSpecZero (grade (originIdeal π (π ^ 2 * a))) ≫
        Spec.map (gradeZeroEquiv (originIdeal π (π ^ 2 * a))).toCommRingCatIso.hom) ⁻¹ᵁ
        PrimeSpectrum.basicOpen (coord (π ^ 2 * a) i) ≤
      (blowupCoordChartι a i hπ).opensRange := by
  rw [← affineBlowupι_image_basicOpen (Localization.Away (coord (π ^ 2 * a) i))
    (coord_mem_originIdeal π _ i), opensRange_blowupCoordChartι,
    ← opensRange_affineBlowupι (Localization.Away (coord (π ^ 2 * a) i))]
  exact Scheme.Hom.image_le_opensRange _ _

variable (π) in
/-- **The blowup of a node is proper.** The morphism `Proj A[It] ⟶ Spec A` from the blowup of
`A = R[x, y] ⧸ (xy - b)` along `I = (π, x, y)` is proper. -/
theorem isProper_blowup (b : R) :
    IsProper (Proj.toSpecZero (grade (originIdeal π b)) ≫
      Spec.map (gradeZeroEquiv (originIdeal π b)).toCommRingCatIso.hom) :=
  isProper_toSpecZero_reesAlgebra <| by
    rw [originIdeal_def]; exact Submodule.fg_span (Set.toFinite _)

variable (π) in
/-- **The blowup of a node is an isomorphism away from its center.** The morphism
`Proj A[It] ⟶ Spec A` from the blowup of `A = R[x₀, x₁] ⧸ (x₀x₁ - b)` along `I = (π, x₀, x₁)`
is an isomorphism over the open `D(x₀) ∪ D(x₁)`, which is disjoint from `V(I)`. -/
theorem isIso_morphismRestrict_iSup_basicOpen_coord (b : R) :
    IsIso ((Proj.toSpecZero (grade (originIdeal π b)) ≫
      Spec.map (gradeZeroEquiv (originIdeal π b)).toCommRingCatIso.hom) ∣_
        (⨆ i, PrimeSpectrum.basicOpen (coord b i) : (Spec (.of (NodeAlgebra R b))).Opens)) := by
  refine isIso_morphismRestrict_toSpecZero_reesAlgebra_of_disjoint_zeroLocus
    (Set.disjoint_left.mpr fun p hp hz ↦ ?_)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  exact hi (hz (coord_mem_originIdeal π _ i))

/-! ### The open cover by the three charts -/

/-- The generators `π, x₀, x₁` of `originIdeal`, indexed by `Option (Fin 2)`. -/
private def originGenerator (π a : R) (j : Option (Fin 2)) : NodeAlgebra R a :=
  j.elim (algebraMap R _ π) (coord a)

private theorem span_range_originGenerator (π a : R) :
    span (Set.range (originGenerator π a)) = originIdeal π a := by
  rw [originIdeal_def]
  congr 1
  ext z
  simp [originGenerator, Option.exists, Fin.exists_fin_two, eq_comm]

/-- **The charts cover the blowup of a node.** For a nonzerodivisor `π` of `R`, the blowup of
`A = R[x₀, x₁] ⧸ (x₀x₁ - π²a)` along `I = (π, x₀, x₁)` is covered by the `π`-chart
`Spec R[u, v] ⧸ (uv - a)` and the charts `Spec R[x, t] ⧸ (xt - π)` of the two coordinates. -/
theorem opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι
    (hπ : π ∈ nonZeroDivisors R) :
    (blowupBaseChartι a hπ).opensRange ⊔ ⨆ i, (blowupCoordChartι a i hπ).opensRange = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top _ _
    (irrelevant_eq_span_monomialDegreeOne (span_range_originGenerator π (π ^ 2 * a))).le
  rw [iSup_option] at h
  rw [opensRange_blowupBaseChartι]
  simp_rw [opensRange_blowupCoordChartι]
  exact h

/-- Every point of the blowup of a node lies in the `π`-chart or in a coordinate chart. -/
private theorem mem_opensRange_blowupBaseChartι_sup_iSup (hπ : π ∈ nonZeroDivisors R)
    (x : Proj (grade (originIdeal π (π ^ 2 * a)))) :
    x ∈ (blowupBaseChartι a hπ).opensRange ⊔ ⨆ i, (blowupCoordChartι a i hπ).opensRange := by
  rw [opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι]
  trivial

/-- **The `π`-chart meets a coordinate chart where the coordinate is invertible.** For a
nonzerodivisor `π` of `R`, the inverse image in the `π`-chart `Spec R[u, v] ⧸ (uv - a)` of the
chart of the coordinate `xᵢ` of the blowup of `R[x₀, x₁] ⧸ (x₀x₁ - π²a)` is the basic open set
`D(uᵢ)` of `uᵢ = xᵢ/π`. -/
theorem blowupBaseChartι_preimage_opensRange_blowupCoordChartι (i : Fin 2)
    (hπ : π ∈ nonZeroDivisors R) :
    blowupBaseChartι a hπ ⁻¹ᵁ (blowupCoordChartι a i hπ).opensRange =
      PrimeSpectrum.basicOpen (coord a i) := by
  rw [opensRange_blowupCoordChartι, blowupBaseChartι, affineBlowupι_def, Scheme.Hom.comp_preimage,
    Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen _ _ _
      (monomialDegreeOne_mem_grade _) one_pos, SpecMap_preimage_basicOpen,
    SpecMap_preimage_basicOpen]
  congr 1
  -- the degree zero fraction `(xᵢ t)/(π t)` is `xᵢ/π = uᵢ`
  simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom, RingHom.coe_coe,
    HomogeneousLocalization.Away.isLocalizationElem, pow_one, AlgEquiv.coe_toRingEquiv,
    awayEquivAffineBlowup_apply_mk_monomialDegreeOne]
  rw [AlgEquiv.symm_apply_eq]
  ext1
  rw [coe_affineBlowupBaseEquiv_coord]

/-- The open cover of the blowup of the node by the `π`-chart (index `none`) and the charts of the
two coordinates (index `some i`). -/
private def blowupOpenCover (hπ : π ∈ nonZeroDivisors R) :
    (Proj (grade (originIdeal π (π ^ 2 * a)))).OpenCover :=
  .mkOfCovers (Option (Fin 2)) (fun j ↦ Spec (.of (NodeAlgebra R (j.elim a fun _ ↦ π))))
    (fun
      | none => blowupBaseChartι a hπ
      | some i => blowupCoordChartι a i hπ)
    (fun x ↦ by
      rcases TopologicalSpace.Opens.mem_sup.mp
        (mem_opensRange_blowupBaseChartι_sup_iSup a hπ x) with h | h
      · exact ⟨none, h⟩
      · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
        exact ⟨some i, hi⟩)
    (fun
      | none => inferInstanceAs (IsOpenImmersion (blowupBaseChartι a hπ))
      | some i => inferInstanceAs (IsOpenImmersion (blowupCoordChartι a i hπ)))

/-- Each chart of `blowupOpenCover`, followed by the structure map `Proj A[It] ⟶ Spec R`, is the
structure map of the corresponding node algebra over `R`. -/
private theorem blowupOpenCover_f_blowupToSpec (hπ : π ∈ nonZeroDivisors R) (j : Option (Fin 2)) :
    (blowupOpenCover a hπ).f j ≫ blowupToSpec π a =
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (j.elim a fun _ ↦ π)))) := by
  cases j with
  | none => exact blowupBaseChartι_blowupToSpec a hπ
  | some i => exact blowupCoordChartι_blowupToSpec a i hπ

/-! ### The origin of the `π`-chart -/

section Origin

variable [IsLocalRing R] {a}

/-- **The origin of the `π`-chart of the blowup of a node.** For a nonzerodivisor `π` and `a` in
the maximal ideal `𝔪_R` of the local ring `R`, the point of the blowup of
`R[x, y] ⧸ (xy - π²a)` along `(π, x, y)` at which the `π`-chart `Spec R[u, v] ⧸ (uv - a)` has
its origin: the image of the maximal ideal `(𝔪_R, u, v)`. For `a = πⁿ` with `n ≥ 2` over a
discrete valuation ring, it is the only singular point of the blowup
(`TauCeti.NodeAlgebra.isRegularLocalRing_stalk_blowup_iff_ne`). -/
def blowupBaseChartOrigin (hπ : π ∈ nonZeroDivisors R) (ha : a ∈ IsLocalRing.maximalIdeal R) :
    Proj (grade (originIdeal π (π ^ 2 * a))) :=
  blowupBaseChartι a hπ ⟨((IsLocalRing.maximalIdeal R).comap
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) R →+* R)).map (NodeAlgebra.mk a),
    (isMaximal_map_quotient_X_mul_X_sub_C ha).isPrime⟩

/-- The origin of the `π`-chart is the image under the `π`-chart of the prime `(𝔪_R, u, v)`. -/
theorem blowupBaseChartOrigin_def (hπ : π ∈ nonZeroDivisors R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) :
    blowupBaseChartOrigin hπ ha = blowupBaseChartι a hπ ⟨((IsLocalRing.maximalIdeal R).comap
      (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) R →+* R)).map (NodeAlgebra.mk a),
    (isMaximal_map_quotient_X_mul_X_sub_C ha).isPrime⟩ :=
  (rfl)

/-- The origin of the `π`-chart does not lie in the chart of either coordinate: there both
coordinates of the `π`-chart vanish, while the coordinate charts are where they are invertible. -/
theorem blowupBaseChartOrigin_notMem_opensRange_blowupCoordChartι (hπ : π ∈ nonZeroDivisors R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) (i : Fin 2) :
    blowupBaseChartOrigin hπ ha ∉ (blowupCoordChartι a i hπ).opensRange := by
  intro h
  have h' := (Scheme.Hom.mem_preimage (blowupBaseChartι a hπ)).mpr h
  rw [blowupBaseChartι_preimage_opensRange_blowupCoordChartι] at h'
  refine (PrimeSpectrum.mem_basicOpen _ _).mp h' ?_
  rw [← mk_X]
  exact mem_map_of_mem _ (by simp)

/-- **The origin of the `π`-chart is a closed point of the blowup.** -/
theorem isClosed_singleton_blowupBaseChartOrigin (hπ : π ∈ nonZeroDivisors R)
    (ha : a ∈ IsLocalRing.maximalIdeal R) :
    IsClosed {blowupBaseChartOrigin hπ ha} := by
  refine closure_subset_iff_isClosed.mp fun y hy ↦ ?_
  rw [← specializes_iff_mem_closure] at hy
  rcases TopologicalSpace.Opens.mem_sup.mp (mem_opensRange_blowupBaseChartι_sup_iSup a hπ y) with
    ⟨z, rfl⟩ | hy'
  · -- within the `π`-chart, the origin is the closed point `(𝔪_R, u, v)`
    have hz := (PrimeSpectrum.le_iff_specializes _ _).mpr
      ((blowupBaseChartι a hπ).isOpenEmbedding.isInducing.specializes_iff.mp hy)
    exact congrArg (blowupBaseChartι a hπ) (PrimeSpectrum.ext
      ((isMaximal_map_quotient_X_mul_X_sub_C ha).eq_of_le z.isPrime.ne_top hz).symm)
  · -- an open coordinate chart containing a specialization of the origin would contain it
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
    exact absurd (hy.mem_open (blowupCoordChartι a i hπ).opensRange.isOpen hi)
      (blowupBaseChartOrigin_notMem_opensRange_blowupCoordChartι hπ ha i)

end Origin

/-! ### The blowup as a relative curve over `Spec R` -/

/-- **The blowup of a node is flat.** For a nonzerodivisor `π` of `R`, the blowup of
`R[x, y] ⧸ (xy - π²a)` along `(π, x, y)` is flat over `Spec R`. -/
theorem flat_blowup (hπ : π ∈ nonZeroDivisors R) :
    Flat (blowupToSpec π a) := by
  -- Instance search does not infer the ring-hom property `Q` in `HasRingHomProperty @Flat Q`, so
  -- the locality of `Flat` on the source is supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (blowupOpenCover a hπ) fun j ↦ ?_
  rw [blowupOpenCover_f_blowupToSpec a hπ j]
  exact flat_spec _

/-- **The blowup of a node is locally of finite presentation.** For a nonzerodivisor `π` of `R`,
the blowup of `R[x, y] ⧸ (xy - π²a)` along `(π, x, y)` is locally of finite presentation over
`Spec R`. -/
theorem locallyOfFinitePresentation_blowup (hπ : π ∈ nonZeroDivisors R) :
    LocallyOfFinitePresentation (blowupToSpec π a) := by
  -- Instance search does not infer the ring-hom property `Q` in
  -- `HasRingHomProperty @LocallyOfFinitePresentation Q`, so the locality of
  -- `LocallyOfFinitePresentation` on the source is supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    (Q := RingHom.FinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (blowupOpenCover a hπ) fun j ↦ ?_
  rw [blowupOpenCover_f_blowupToSpec a hπ j]
  exact locallyOfFinitePresentation_spec _

/-- **The blowup of a node has pure relative dimension one.** For a nonzerodivisor `π` of `R`,
every fibre of the blowup of `R[x, y] ⧸ (xy - π²a)` along `(π, x, y)` over `Spec R` is a curve
all of whose irreducible components are one-dimensional. -/
theorem pureRelativeDimension_blowup (hπ : π ∈ nonZeroDivisors R) :
    PureRelativeDimension 1 (blowupToSpec π a) := by
  have := locallyOfFinitePresentation_blowup a hπ
  rw [pureRelativeDimension_iff_of_openCover _ (blowupOpenCover a hπ)]
  intro j
  rw [blowupOpenCover_f_blowupToSpec a hπ j]
  exact pureRelativeDimension_spec _

/-- Blowing up the origin of `xy = π²a` preserves nodality over the base. This holds for
any nonzerodivisor `π` in a commutative ring: the three charts are the nodal relative curves
`uv = a` and `xt = π`. -/
theorem atWorstNodalOfRelativeDimensionOne_blowup (hπ : π ∈ nonZeroDivisors R) :
    AtWorstNodalOfRelativeDimensionOne (blowupToSpec π a) := by
  refine IsZariskiLocalAtSource.of_openCover (blowupOpenCover a hπ) fun j ↦ ?_
  rw [blowupOpenCover_f_blowupToSpec a hπ j]
  exact atWorstNodalOfRelativeDimensionOne _

/-! ### Regularity of the blowup over a discrete valuation ring -/

/-- Over a discrete valuation ring with uniformizer `π`, the blowup of `R[x, y] ⧸ (xy - π²a)` is
regular along its coordinate charts `Spec R[x, t] ⧸ (xt - π)`. -/
private theorem isRegularLocalRing_stalk_blowupCoordChartι [IsDomain R]
    [IsDiscreteValuationRing R] (hπ : Irreducible π) (hπ0 : π ∈ nonZeroDivisors R) (i : Fin 2)
    (y : Spec (.of (NodeAlgebra R π))) :
    IsRegularLocalRing ((Proj (grade (originIdeal π (π ^ 2 * a)))).presheaf.stalk
      (blowupCoordChartι a i hπ0 y)) := by
  have : IsRegularRing (NodeAlgebra R π) := by
    have h1 := (isRegularRing_pow_iff hπ 1).mpr le_rfl
    rwa [pow_one] at h1
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ y).mpr inferInstance

/-- **One blowup resolves a node of thickness two or three.** For a uniformizer `π` of a discrete
valuation ring `R`, every local ring of the blowup of `R[x, y] ⧸ (xy - πⁿ⁺²)` along `(π, x, y)` is
regular exactly when `n ≤ 1`. -/
theorem isRegularLocalRing_stalk_blowup_iff (n : ℕ) [IsDomain R] [IsDiscreteValuationRing R]
    (hπ : Irreducible π) :
    (∀ x : Proj (grade (originIdeal π (π ^ (n + 2)))),
      IsRegularLocalRing ((Proj (grade (originIdeal π (π ^ (n + 2))))).presheaf.stalk x)) ↔
      n ≤ 1 := by
  rw [pow_add, mul_comm (π ^ n)]
  have hπ0 : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  have : IsNoetherianRing (NodeAlgebra R (π ^ n)) := Algebra.FiniteType.isNoetherianRing R _
  rw [← isRegularRing_pow_iff hπ n,
    isRegularRing_iff_isRegularLocalRing_stalk_Spec (.of (NodeAlgebra R (π ^ n)))]
  refine ⟨fun h y ↦ (isRegularLocalRing_stalk_iff_of_isOpenImmersion
    (blowupBaseChartι (π ^ n) hπ0) y).mp (h _), fun h x ↦ ?_⟩
  rcases TopologicalSpace.Opens.mem_sup.mp (mem_opensRange_blowupBaseChartι_sup_iSup _ hπ0 x) with
    ⟨y, rfl⟩ | hx
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ y).mpr (h y)
  · obtain ⟨i, y, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact isRegularLocalRing_stalk_blowupCoordChartι _ hπ hπ0 i y

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/-- **The blowup of `xy = πⁿ⁺²` is regular away from the origin of its `π`-chart.** For a
uniformizer `π` of a discrete valuation ring `R` and `n ≠ 0`, every local ring of the blowup of
`R[x, y] ⧸ (xy - π²πⁿ)` along `(π, x, y)` at a point other than the origin of the `π`-chart
`Spec R[u, v] ⧸ (uv - πⁿ)` is regular. -/
theorem isRegularLocalRing_stalk_blowup_of_ne (hπ : Irreducible π) {n : ℕ}
    {hπ0 : π ∈ nonZeroDivisors R} {ha : π ^ n ∈ IsLocalRing.maximalIdeal R}
    {x : Proj (grade (originIdeal π (π ^ 2 * π ^ n)))} (hx : x ≠ blowupBaseChartOrigin hπ0 ha) :
    IsRegularLocalRing ((Proj (grade (originIdeal π (π ^ 2 * π ^ n)))).presheaf.stalk x) := by
  rcases TopologicalSpace.Opens.mem_sup.mp (mem_opensRange_blowupBaseChartι_sup_iSup _ hπ0 x) with
    ⟨y, rfl⟩ | hx'
  · -- on the `π`-chart, `y` is not the origin of `R[u, v] ⧸ (uv - πⁿ)`
    have hy : y.asIdeal ≠ ((IsLocalRing.maximalIdeal R).comap
        (MvPolynomial.constantCoeff : MvPolynomial (Fin 2) R →+* R)).map (NodeAlgebra.mk (π ^ n)) :=
      fun h ↦ hx (congrArg (blowupBaseChartι (π ^ n) hπ0) (PrimeSpectrum.ext h))
    have := y.isPrime
    have := isRegularLocalRing_localization_of_ne hπ n y.asIdeal hy
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ y).mpr
      ((isRegularLocalRing_stalk_Spec_iff _ y).mpr this)
  · obtain ⟨i, y, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
    exact isRegularLocalRing_stalk_blowupCoordChartι _ hπ hπ0 i y

/-- **The blowup of `xy = πⁿ⁺²` at the origin of its `π`-chart is the node of thickness `n`.**
For a uniformizer `π` of a discrete valuation ring `R`, the local ring of the blowup of
`R[x, y] ⧸ (xy - π²πⁿ)` along `(π, x, y)` at the origin of the `π`-chart is that of
`R[u, v] ⧸ (uv - πⁿ)` at `(π, u, v)`, so it is regular exactly when `n = 1`. -/
theorem isRegularLocalRing_stalk_blowupBaseChartOrigin_iff (hπ : Irreducible π) {n : ℕ}
    (hπ0 : π ∈ nonZeroDivisors R) (ha : π ^ n ∈ IsLocalRing.maximalIdeal R) :
    IsRegularLocalRing ((Proj (grade (originIdeal π (π ^ 2 * π ^ n)))).presheaf.stalk
      (blowupBaseChartOrigin hπ0 ha)) ↔ n = 1 := by
  have := (isMaximal_map_quotient_X_mul_X_sub_C ha).isPrime
  rw [← isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff_of_irreducible hπ n]
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion (blowupBaseChartι (π ^ n) hπ0) _).trans
    (isRegularLocalRing_stalk_Spec_iff (.of (NodeAlgebra R (π ^ n))) ⟨_, this⟩)

/-- **The singular locus of the blowup of `xy = πⁿ⁺²` for `n ≥ 2` is one closed point.** For a
uniformizer `π` of a discrete valuation ring `R` and `n ≥ 2`, the local ring of the blowup of
`R[x, y] ⧸ (xy - π²πⁿ)` along `(π, x, y)` at a point is regular exactly when the point is not the
origin of the `π`-chart, a closed point (`isClosed_singleton_blowupBaseChartOrigin`) at which
the blowup is the node `uv = πⁿ`. -/
theorem isRegularLocalRing_stalk_blowup_iff_ne (hπ : Irreducible π) {n : ℕ} (hn : 2 ≤ n)
    (hπ0 : π ∈ nonZeroDivisors R) (ha : π ^ n ∈ IsLocalRing.maximalIdeal R)
    (x : Proj (grade (originIdeal π (π ^ 2 * π ^ n)))) :
    IsRegularLocalRing ((Proj (grade (originIdeal π (π ^ 2 * π ^ n)))).presheaf.stalk x) ↔
      x ≠ blowupBaseChartOrigin hπ0 ha := by
  refine ⟨?_, isRegularLocalRing_stalk_blowup_of_ne hπ⟩
  rintro h rfl
  have := (isRegularLocalRing_stalk_blowupBaseChartOrigin_iff hπ hπ0 ha).mp h
  omega

end IsDiscreteValuationRing

end TauCeti.NodeAlgebra
