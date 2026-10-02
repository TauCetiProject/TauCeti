/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.AffineCharts
public import TauCeti.AlgebraicGeometry.Curves.Node
public import TauCeti.RingTheory.Node.Blowup
public import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
public import TauCeti.RingTheory.RegularLocalRing.Node

/-!
# The blowup of the node `xy = πⁿ⁺²` at its origin

Let `π` be a nonzerodivisor of a commutative ring `R`, for instance a uniformizer of a discrete
valuation ring, let `A = R[x, y] ⧸ (xy - πⁿ⁺²)` and let `I = (π, x, y)` be the ideal of the origin
(`TauCeti.NodeAlgebra.originIdeal`).
This file describes the blowup `Proj A[It]` of `Spec A` along `V(I)` as a scheme over `Spec R`:

* it is covered by three open charts, the `π`-chart `Spec R[u, v] ⧸ (uv - πⁿ)` and, for each
  coordinate, the chart `Spec R[x, t] ⧸ (xt - π)`;
* consequently it is flat, locally of finite presentation and of pure relative dimension one over
  `Spec R`, like `Spec A` itself.

When `R` is a discrete valuation ring with uniformizer `π`, the coordinate charts are regular and
the `π`-chart is regular exactly when `n ≤ 1`. So a single blowup of the origin turns the nodes
`xy = π²` and `xy = π³` into regular schemes, while for `n ≥ 2` the blowup is still singular.

Over a discrete valuation ring, this says that blowing up the singular point of the local model
`xy = πⁿ⁺²` of a node yields again a flat, finitely presented relative curve, whose only possibly
singular chart is the node `xy = πⁿ` of thickness lowered by two, while the two other charts are
nodes of thickness one, regular at their origin
(`TauCeti.isRegularLocalRing_localization_quotient_X_mul_X_sub_C_pow_iff_of_irreducible`).

## Main definitions

* `TauCeti.NodeAlgebra.blowupToSpec π n`: the structure morphism `Proj A[It] ⟶ Spec R` of the
  blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartι`: the open immersion of the `π`-chart
  `Spec R[u, v] ⧸ (uv - πⁿ)` into the blowup.
* `TauCeti.NodeAlgebra.blowupCoordChartι`: the open immersion of the chart
  `Spec R[x, t] ⧸ (xt - π)` of a coordinate `xᵢ` into the blowup.

## Main results

* `TauCeti.NodeAlgebra.opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι`: the
  three charts cover the blowup.
* `TauCeti.NodeAlgebra.blowupBaseChartι_blowupToSpec`,
  `TauCeti.NodeAlgebra.blowupCoordChartι_blowupToSpec`: the charts are morphisms over `Spec R`.
* `TauCeti.NodeAlgebra.flat_blowup`, `TauCeti.NodeAlgebra.locallyOfFinitePresentation_blowup`,
  `TauCeti.NodeAlgebra.pureRelativeDimension_blowup`: the blowup is flat, locally of finite
  presentation and of pure relative dimension one over `Spec R`.
* `TauCeti.NodeAlgebra.isRegularLocalRing_stalk_blowup_iff`: over a discrete valuation ring,
  every local ring of the blowup is regular exactly when `n ≤ 1`.

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

variable (π : R) (n : ℕ) in
/-- The structure morphism `Proj A[It] ⟶ Spec A ⟶ Spec R` of the blowup of
`A = R[x, y] ⧸ (xy - πⁿ⁺²)` along `I = (π, x, y)`, as a scheme over `Spec R`. -/
def blowupToSpec : Proj (grade (originIdeal π (π ^ (n + 2)))) ⟶ Spec (.of R) :=
  Proj.toSpecZero (grade (originIdeal π (π ^ (n + 2)))) ≫
    Spec.map (gradeZeroEquiv (originIdeal π (π ^ (n + 2)))).toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (π ^ (n + 2)))))

theorem blowupToSpec_def (π : R) (n : ℕ) :
    blowupToSpec π n = Proj.toSpecZero (grade (originIdeal π (π ^ (n + 2)))) ≫
      Spec.map (gradeZeroEquiv (originIdeal π (π ^ (n + 2)))).toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (π ^ (n + 2))))) :=
  (rfl)

variable {π : R} (n : ℕ)

/-- **The `π`-chart of the blowup of a node.** For a nonzerodivisor `π` of `R`, the open
immersion `Spec R[u, v] ⧸ (uv - πⁿ) ⟶ Proj A[It]` into the blowup of `A = R[x, y] ⧸ (xy - πⁿ⁺²)`
along `I = (π, x, y)`, with `u = x/π` and `v = y/π`. Its image is the standard open `D₊(π t)`. -/
def blowupBaseChartι (hπ : π ∈ nonZeroDivisors R) :
    Spec (.of (NodeAlgebra R (π ^ n))) ⟶ Proj (grade (originIdeal π (π ^ (n + 2)))) :=
  Spec.map (RingEquiv.toCommRingCatIso (affineBlowupBaseEquiv n
      (Localization.Away (algebraMap R (NodeAlgebra R (π ^ (n + 2))) π)) hπ).symm.toRingEquiv).hom ≫
    affineBlowupι _ (algebraMap_mem_originIdeal π _)

instance (hπ : π ∈ nonZeroDivisors R) : IsOpenImmersion (blowupBaseChartι n hπ) := by
  rw [blowupBaseChartι]
  infer_instance

/-- The `π`-chart of the blowup of the node is an open immersion onto the standard open
`D₊(π t)`. -/
theorem opensRange_blowupBaseChartι (hπ : π ∈ nonZeroDivisors R) :
    (blowupBaseChartι n hπ).opensRange =
      Proj.basicOpen _ (monomialDegreeOne (algebraMap_mem_originIdeal π (π ^ (n + 2)))) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (opensRange_affineBlowupι _ _)

/-- The `π`-chart of the blowup of the node is a morphism over `Spec R`: followed by the
structure map `Proj A[It] ⟶ Spec A ⟶ Spec R`, it is the structure map of `R[u, v] ⧸ (uv - πⁿ)`. -/
@[reassoc (attr := simp)]
theorem blowupBaseChartι_blowupToSpec (hπ : π ∈ nonZeroDivisors R) :
    blowupBaseChartι n hπ ≫ blowupToSpec π n =
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (π ^ n)))) := by
  rw [blowupToSpec_def, blowupBaseChartι, Category.assoc, affineBlowupι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp [← IsScalarTower.algebraMap_apply]

/-- **The coordinate charts of the blowup of a node.** For a nonzerodivisor `π` of `R`, the open
immersion `Spec R[x, t] ⧸ (xt - π) ⟶ Proj A[It]` into the blowup of
`A = R[x₀, x₁] ⧸ (x₀x₁ - πⁿ⁺²)` along `I = (π, x₀, x₁)`, with `x = xᵢ` and `t = π/xᵢ`. Its image
is the standard open `D₊(xᵢ t)`. -/
def blowupCoordChartι (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    Spec (.of (NodeAlgebra R π)) ⟶ Proj (grade (originIdeal π (π ^ (n + 2)))) :=
  Spec.map (RingEquiv.toCommRingCatIso (affineBlowupCoordEquiv n i
      (Localization.Away (coord (π ^ (n + 2)) i)) hπ).symm.toRingEquiv).hom ≫
    affineBlowupι _ (coord_mem_originIdeal π _ i)

instance (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    IsOpenImmersion (blowupCoordChartι n i hπ) := by
  rw [blowupCoordChartι]
  infer_instance

/-- The chart of the coordinate `xᵢ` of the blowup of the node is an open immersion onto the
standard open `D₊(xᵢ t)`. -/
theorem opensRange_blowupCoordChartι (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    (blowupCoordChartι n i hπ).opensRange =
      Proj.basicOpen _ (monomialDegreeOne (coord_mem_originIdeal π (π ^ (n + 2)) i)) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (opensRange_affineBlowupι _ _)

/-- The chart of a coordinate of the blowup of the node is a morphism over `Spec R`: followed by
the structure map `Proj A[It] ⟶ Spec A ⟶ Spec R`, it is the structure map of
`R[x, t] ⧸ (xt - π)`. -/
@[reassoc (attr := simp)]
theorem blowupCoordChartι_blowupToSpec (i : Fin 2) (hπ : π ∈ nonZeroDivisors R) :
    blowupCoordChartι n i hπ ≫ blowupToSpec π n =
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R π))) := by
  rw [blowupToSpec_def, blowupCoordChartι, Category.assoc, affineBlowupι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext r
  simp [← IsScalarTower.algebraMap_apply]

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
`A = R[x₀, x₁] ⧸ (x₀x₁ - πⁿ⁺²)` along `I = (π, x₀, x₁)` is covered by the `π`-chart
`Spec R[u, v] ⧸ (uv - πⁿ)` and the charts `Spec R[x, t] ⧸ (xt - π)` of the two coordinates. -/
theorem opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι
    (hπ : π ∈ nonZeroDivisors R) :
    (blowupBaseChartι n hπ).opensRange ⊔ ⨆ i, (blowupCoordChartι n i hπ).opensRange = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top _ _
    (irrelevant_eq_span_monomialDegreeOne (span_range_originGenerator π (π ^ (n + 2)))).le
  rw [iSup_option] at h
  rw [opensRange_blowupBaseChartι]
  simp_rw [opensRange_blowupCoordChartι]
  exact h

/-- The open cover of the blowup of the node by the `π`-chart (index `none`) and the charts of the
two coordinates (index `some i`). -/
private def blowupOpenCover (hπ : π ∈ nonZeroDivisors R) :
    (Proj (grade (originIdeal π (π ^ (n + 2))))).OpenCover :=
  .mkOfCovers (Option (Fin 2)) (fun j ↦ Spec (.of (NodeAlgebra R (j.elim (π ^ n) fun _ ↦ π))))
    (fun
      | none => blowupBaseChartι n hπ
      | some i => blowupCoordChartι n i hπ)
    (fun x ↦ by
      have hx : x ∈ (blowupBaseChartι n hπ).opensRange ⊔
          ⨆ i, (blowupCoordChartι n i hπ).opensRange := by
        rw [opensRange_blowupBaseChartι_sup_iSup_opensRange_blowupCoordChartι]
        trivial
      rcases TopologicalSpace.Opens.mem_sup.mp hx with h | h
      · exact ⟨none, h⟩
      · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
        exact ⟨some i, hi⟩)
    (fun
      | none => inferInstanceAs (IsOpenImmersion (blowupBaseChartι n hπ))
      | some i => inferInstanceAs (IsOpenImmersion (blowupCoordChartι n i hπ)))

/-- Each chart of `blowupOpenCover`, followed by the structure map `Proj A[It] ⟶ Spec R`, is the
structure map of the corresponding node algebra over `R`. -/
private theorem blowupOpenCover_f_blowupToSpec (hπ : π ∈ nonZeroDivisors R) (j : Option (Fin 2)) :
    (blowupOpenCover n hπ).f j ≫ blowupToSpec π n =
      Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R (j.elim (π ^ n) fun _ ↦ π)))) := by
  cases j with
  | none => exact blowupBaseChartι_blowupToSpec n hπ
  | some i => exact blowupCoordChartι_blowupToSpec n i hπ

/-! ### The blowup as a relative curve over `Spec R` -/

/-- **The blowup of a node is flat.** For a nonzerodivisor `π` of `R`, the blowup of
`R[x, y] ⧸ (xy - πⁿ⁺²)` along `(π, x, y)` is flat over `Spec R`. -/
theorem flat_blowup (hπ : π ∈ nonZeroDivisors R) :
    Flat (blowupToSpec π n) := by
  -- Instance search does not infer the ring-hom property `Q` in `HasRingHomProperty @Flat Q`, so
  -- the locality of `Flat` on the source is supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  refine IsZariskiLocalAtSource.of_openCover (blowupOpenCover n hπ) fun j ↦ ?_
  rw [blowupOpenCover_f_blowupToSpec n hπ j]
  exact flat_spec _

/-- **The blowup of a node is locally of finite presentation.** For a nonzerodivisor `π` of `R`,
the blowup of `R[x, y] ⧸ (xy - πⁿ⁺²)` along `(π, x, y)` is locally of finite presentation over
`Spec R`. -/
theorem locallyOfFinitePresentation_blowup (hπ : π ∈ nonZeroDivisors R) :
    LocallyOfFinitePresentation (blowupToSpec π n) := by
  -- Instance search does not infer the ring-hom property `Q` in
  -- `HasRingHomProperty @LocallyOfFinitePresentation Q`, so the locality of
  -- `LocallyOfFinitePresentation` on the source is supplied explicitly.
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation)
    (Q := RingHom.FinitePresentation)
  refine IsZariskiLocalAtSource.of_openCover (blowupOpenCover n hπ) fun j ↦ ?_
  rw [blowupOpenCover_f_blowupToSpec n hπ j]
  exact locallyOfFinitePresentation_spec _

/-- **The blowup of a node has pure relative dimension one.** For a nonzerodivisor `π` of `R`,
every fibre of the blowup of `R[x, y] ⧸ (xy - πⁿ⁺²)` along `(π, x, y)` over `Spec R` is a curve
all of whose irreducible components are one-dimensional. -/
theorem pureRelativeDimension_blowup (hπ : π ∈ nonZeroDivisors R) :
    PureRelativeDimension 1 (blowupToSpec π n) := by
  have := locallyOfFinitePresentation_blowup n hπ
  rw [pureRelativeDimension_iff_of_openCover _ (blowupOpenCover n hπ)]
  intro j
  rw [blowupOpenCover_f_blowupToSpec n hπ j]
  exact pureRelativeDimension_spec _

/-! ### Regularity of the blowup over a discrete valuation ring -/

/-- **One blowup resolves a node of thickness two or three.** For a uniformizer `π` of a discrete
valuation ring `R`, every local ring of the blowup of `R[x, y] ⧸ (xy - πⁿ⁺²)` along `(π, x, y)` is
regular exactly when `n ≤ 1`. -/
theorem isRegularLocalRing_stalk_blowup_iff [IsDomain R] [IsDiscreteValuationRing R]
    (hπ : Irreducible π) :
    (∀ x : Proj (grade (originIdeal π (π ^ (n + 2)))),
      IsRegularLocalRing ((Proj (grade (originIdeal π (π ^ (n + 2))))).presheaf.stalk x)) ↔
      n ≤ 1 := by
  have hπ0 : π ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hπ.ne_zero
  have : IsNoetherianRing (NodeAlgebra R (π ^ n)) := Algebra.FiniteType.isNoetherianRing R _
  rw [← isRegularRing_pow_iff hπ n,
    isRegularRing_iff_isRegularLocalRing_stalk_Spec (.of (NodeAlgebra R (π ^ n)))]
  refine ⟨fun h y ↦ (isRegularLocalRing_stalk_iff_of_isOpenImmersion
    (blowupBaseChartι n hπ0) y).mp (h _), fun h x ↦ ?_⟩
  have hx : x ∈ (blowupBaseChartι n hπ0).opensRange ⊔
      ⨆ i, (blowupCoordChartι n i hπ0).opensRange := by
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
