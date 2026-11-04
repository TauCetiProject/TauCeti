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
still singular. The remaining chart has thickness lowered by two, which is the local
computation used in resolving nodal models of curves.

## Main definitions

* `TauCeti.NodeAlgebra.blowupToSpec π a`: the structure morphism `Proj A[It] ⟶ Spec R` of the
  blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartι`: the open immersion of the `π`-chart
  `Spec R[u, v] ⧸ (uv - a)` into the blowup.
* `TauCeti.NodeAlgebra.blowupCoordChartι`: the open immersion of the chart
  `Spec R[x, t] ⧸ (xt - π)` of a coordinate `xᵢ` into the blowup.

## Main results

* `TauCeti.NodeAlgebra.opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι`: the
  three charts cover the blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartι_blowupToSpec`,
  `TauCeti.NodeAlgebra.blowupCoordChartι_blowupToSpec`: the charts are morphisms over `Spec R`.
* `TauCeti.NodeAlgebra.blowupBaseChartι_preimage_opensRange_blowupCoordChartι`: on the `π`-chart,
  the chart of the coordinate `xᵢ` is the basic open `D(xᵢ/π)`.
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

/-- **The overlap of the `π`-chart with a coordinate chart.** On the `π`-chart
`Spec R[u, v] ⧸ (uv - a)`, where `xᵢ = π uᵢ`, the chart of the coordinate `xᵢ` is the basic open
`D(uᵢ)`: the fraction `(xᵢ t)/(π t)` is `xᵢ/π = uᵢ`. -/
theorem blowupBaseChartι_preimage_opensRange_blowupCoordChartι (i : Fin 2)
    (hπ : π ∈ nonZeroDivisors R) :
    blowupBaseChartι a hπ ⁻¹ᵁ (blowupCoordChartι a i hπ).opensRange =
      (PrimeSpectrum.basicOpen (coord a i) : (Spec (.of (NodeAlgebra R a))).Opens) := by
  rw [opensRange_blowupCoordChartι, blowupBaseChartι, Scheme.Hom.comp_preimage,
    affineBlowupι_preimage_basicOpen, SpecMap_preimage_basicOpen]
  congr 1
  simp only [RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom, RingEquiv.coe_toRingHom,
    AlgEquiv.coe_toRingEquiv]
  rw [AlgEquiv.symm_apply_eq]
  exact Subtype.ext (coe_affineBlowupBaseEquiv_coord hπ i).symm

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

/-- The open cover of the blowup of the node by the `π`-chart (index `none`) and the charts of the
two coordinates (index `some i`). -/
private def blowupOpenCover (hπ : π ∈ nonZeroDivisors R) :
    (Proj (grade (originIdeal π (π ^ 2 * a)))).OpenCover :=
  .mkOfCovers (Option (Fin 2)) (fun j ↦ Spec (.of (NodeAlgebra R (j.elim a fun _ ↦ π))))
    (fun
      | none => blowupBaseChartι a hπ
      | some i => blowupCoordChartι a i hπ)
    (fun x ↦ by
      have hx : x ∈ (blowupBaseChartι a hπ).opensRange ⊔
          ⨆ i, (blowupCoordChartι a i hπ).opensRange := by
        rw [opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with h | h
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
  have hx : x ∈ (blowupBaseChartι (π ^ n) hπ0).opensRange ⊔
      ⨆ i, (blowupCoordChartι (π ^ n) i hπ0).opensRange := by
    rw [opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι]
    trivial
  rcases TopologicalSpace.Opens.mem_sup.mp hx with ⟨y, rfl⟩ | hx
  · exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ y).mpr (h y)
  · obtain ⟨i, y, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have : IsRegularRing (NodeAlgebra R π) := by
      have h1 := (isRegularRing_pow_iff hπ 1).mpr le_rfl
      rwa [pow_one] at h1
    exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion _ y).mpr inferInstance

end TauCeti.NodeAlgebra
