/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import Mathlib.AlgebraicGeometry.PullbackCarrier
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SchemeTheoreticallyDominant

/-!
# Charts of the projective Weierstrass model

Let `W` be a Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its projective
model and let `S = Spec R`. This file presents the standard affine chart `D₊(Xᵢ)` of `E` as an open
immersion from the spectrum of the chart ring `ChartRing i = R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`, and the
product `D₊(Xᵢ) ×_S D₊(Xⱼ)` of two charts as an open immersion from the spectrum of
`ChartRing i ⊗[R] ChartRing j` into `E ×_S E`.

The affine chart `D₊(Z)` is scheme-theoretically dense in `E`, with no hypothesis on `R` or on
`W`. Hence, by `TauCeti.ext_of_isSchemeTheoreticallyDominant`, two morphisms from `E` to a scheme
separated over a base that agree over the base and on `D₊(Z)` are equal.

## Main definitions

* `WeierstrassCurve.chartι W i`: the chart `D₊(Xᵢ)`, an open immersion
  `Spec (ChartRing i) ⟶ projModel W`.
* `WeierstrassCurve.chartPairι W i j`: the product of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)`, an open
  immersion `Spec (ChartRing i ⊗[R] ChartRing j) ⟶ E ×_S E`.

## Main results

* `WeierstrassCurve.opensRange_chartι`: the image of the chart `chartι W i` is the standard affine
  open `D₊(Xᵢ)`.
* `WeierstrassCurve.exists_mem_range_chartι`: the three charts cover the projective model.
* `WeierstrassCurve.isSchemeTheoreticallyDominant_chartι_two`: the chart `D₊(Z)` is
  scheme-theoretically dense in the projective model.
* `WeierstrassCurve.chartι_projModelOver`: on the chart `D₊(Xᵢ)`, the structure morphism of the
  projective model is `Spec` of the structure map `R → ChartRing i`.
* `WeierstrassCurve.chartPairι_fst` and `WeierstrassCurve.chartPairι_snd`: the two projections of
  `E ×_S E` on the product of two charts.
* `WeierstrassCurve.SpecMap_desc_chartPairι`: the point of the product of two charts given by two
  homomorphisms out of the chart rings that agree on `R` is the point of `E ×_S E` with the
  corresponding points of the two charts as components.
* `WeierstrassCurve.range_chartPairι`: the product of two charts is the locus in `E ×_S E` whose
  projections lie on the two charts.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionChartSpec.lean`: `chartι`,
`chartι_projModelπ`, and `chartPieceTensorIso` with its `_inv_fst` and `_inv_snd` lemmas, as
`chartι`, `chartι_projModelOver`, `chartPairι`, `chartPairι_fst` and `chartPairι_snd`. Here the
chart is read through `WeierstrassCurve.Projective.awayEquivChartRing`, and the product of two
charts is an open immersion into `E ×_S E` rather than an isomorphism with a pullback. From the
file `AdditionSpecPoints.lean` of the same directory: `specMap_pieceAwayZι_fst`,
`specMap_pieceAwayZι_snd`, `specMap_pieceAwayι_fst` and `specMap_pieceAwayι_snd`, as
`SpecMap_desc_chartPairι`. The source computes the two projections of a point of a piece of its
cover through the left and right inclusions of the tensor product; here a point of the product of
two charts is built from its two components through the pushout property of the tensor product.

`isSchemeTheoreticallyDominant_chartι_two` corresponds to `projModel_hom_ext_of_affine` in the
file `PoleFiltration.lean` of the same directory, which states that two morphisms from the
projective model to a separated scheme that agree on the chart `D₊(Z)` are equal, and proves it
chart by chart. Here the statement is that the chart is scheme-theoretically dominant in the sense
of Mathlib's `AlgebraicGeometry.IsSchemeTheoreticallyDominant`, deduced from
`AlgebraicGeometry.Proj.isSchemeTheoreticallyDominant_awayι` and
`WeierstrassCurve.Projective.coord_two_mem_nonZeroDivisors`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open Algebra.TensorProduct (includeLeftRingHom includeRight)

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The standard affine chart `D₊(Xᵢ)` of the projective Weierstrass model, as a morphism
`Spec (ChartRing i) ⟶ projModel W` from the spectrum of `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`. -/
noncomputable def chartι (i : Fin 3) : Spec (.of (W.toProjective.ChartRing i)) ⟶ W.projModel :=
  Spec.map (W.toProjective.awayEquivChartRing i).toCommRingCatIso.hom ≫
    Proj.awayι W.toProjective.grading (W.toProjective.coord i) (W.toProjective.coord_mem_grading i)
      one_pos

/-- The chart `D₊(Xᵢ)` is `Spec` of the isomorphism `awayEquivChartRing` from the degree-zero part
`A_(Xᵢ)` of the localization away from `Xᵢ` to the chart ring, followed by the inclusion
`Proj.awayι` of `D₊(Xᵢ)` into the projective model. The body of `chartι` is not exposed; this
lemma unfolds it. -/
theorem chartι_def (i : Fin 3) : W.chartι i =
    Spec.map (CommRingCat.ofHom (W.toProjective.awayEquivChartRing i : _ →+* _)) ≫
      Proj.awayι W.toProjective.grading (W.toProjective.coord i)
        (W.toProjective.coord_mem_grading i) one_pos := (rfl)

/-- The chart `D₊(Xᵢ)` of the projective model is an open immersion. -/
instance isOpenImmersion_chartι (i : Fin 3) : IsOpenImmersion (W.chartι i) :=
  IsOpenImmersion.comp _ _

/-- The image of the chart `chartι W i` is the standard affine open `D₊(Xᵢ)` of the projective
model. -/
@[simp]
theorem opensRange_chartι (i : Fin 3) :
    (W.chartι i).opensRange = Proj.basicOpen W.toProjective.grading (W.toProjective.coord i) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (Proj.opensRange_awayι _ _ _ _)

/-- The charts `D₊(X₀)`, `D₊(X₁)` and `D₊(X₂)` cover the projective model. -/
theorem exists_mem_range_chartι (y : W.projModel) : ∃ i, y ∈ Set.range (W.chartι i) := by
  -- the opens `D₊(Xᵢ)` cover the projective model, and `D₊(Xᵢ)` is the image of the chart `i`
  have hy : y ∈ ⨆ i, (W.chartι i).opensRange := by
    rw [iSup_congr W.opensRange_chartι,
      Proj.iSup_basicOpen_eq_top _ _ W.toProjective.irrelevant_le_span_range_coord]
    exact TopologicalSpace.Opens.mem_top y
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i, Set.mem_range.mpr (Scheme.Hom.mem_opensRange.mp hi)⟩

/-- The standard affine chart `D₊(Z)` is scheme-theoretically dense in the projective Weierstrass
model: the open immersion `chartι W 2` is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_chartι_two : IsSchemeTheoreticallyDominant (W.chartι 2) := by
  have := Proj.isSchemeTheoreticallyDominant_awayι W.toProjective.grading
    (W.toProjective.coord_mem_grading 2) one_pos W.toProjective.coord_two_mem_nonZeroDivisors
  rw [chartι]
  infer_instance

/-- On the chart `D₊(Xᵢ)`, the structure morphism of the projective model is `Spec` of the
structure map `R → ChartRing i`. -/
@[reassoc (attr := simp)]
theorem chartι_projModelOver (i : Fin 3) : W.chartι i ≫ W.projModelOver =
    Spec.map (CommRingCat.ofHom (algebraMap R (W.toProjective.ChartRing i))) := by
  rw [chartι, Category.assoc, awayι_projModelOver, ← Spec.map_comp,
    ← Projective.awayEquivChartRing_symm_comp_algebraMap]
  congr 1
  ext
  simp

/-- The product `D₊(Xᵢ) ×_S D₊(Xⱼ)` of two standard affine charts of `E = projModel W` over
`S = Spec R`, as a morphism `Spec (ChartRing i ⊗[R] ChartRing j) ⟶ E ×_S E`. It is an open
immersion (`isOpenImmersion_chartPairι`), and its composites with the two projections of
`E ×_S E` are given by `chartPairι_fst` and `chartPairι_snd`. -/
noncomputable def chartPairι (i j : Fin 3) :
    Spec (.of (W.toProjective.ChartRing i ⊗[R] W.toProjective.ChartRing j)) ⟶
      pullback W.projModelOver W.projModelOver :=
  (pullbackSpecIso R _ _).inv ≫ pullback.map _ _ _ _ (W.chartι i) (W.chartι j) (𝟙 _)
    (by simp) (by simp)

/-- The product of two charts is an open immersion into `E ×_S E`. -/
instance isOpenImmersion_chartPairι (i j : Fin 3) : IsOpenImmersion (W.chartPairι i j) := by
  rw [chartPairι]
  infer_instance

/-- Composing the product `chartPairι W i j` of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)` with the first
projection `E ×_S E ⟶ E` gives `Spec` of the inclusion `a ↦ a ⊗ₜ 1` of `ChartRing i` into
`ChartRing i ⊗[R] ChartRing j`, followed by the chart `D₊(Xᵢ)`. -/
@[reassoc (attr := simp)]
theorem chartPairι_fst (i j : Fin 3) :
    W.chartPairι i j ≫ pullback.fst W.projModelOver W.projModelOver =
      Spec.map (CommRingCat.ofHom includeLeftRingHom) ≫ W.chartι i := by
  simp [chartPairι]

/-- Composing the product `chartPairι W i j` of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)` with the second
projection `E ×_S E ⟶ E` gives `Spec` of the inclusion `b ↦ 1 ⊗ₜ b` of `ChartRing j` into
`ChartRing i ⊗[R] ChartRing j`, followed by the chart `D₊(Xⱼ)`. -/
@[reassoc (attr := simp)]
theorem chartPairι_snd (i j : Fin 3) :
    W.chartPairι i j ≫ pullback.snd W.projModelOver W.projModelOver =
      Spec.map (CommRingCat.ofHom (includeRight : _ →ₐ[R] _).toRingHom) ≫ W.chartι j := by
  simp [chartPairι]

/-- If the homomorphisms `α` and `β` from the chart rings `ChartRing i` and `ChartRing j` to `A`
agree on `R`, then `Spec` of the homomorphism `a ⊗ₜ b ↦ α a * β b` they induce on
`ChartRing i ⊗[R] ChartRing j`, followed by the product `chartPairι W i j` of the charts, is the
morphism to `E ×_S E` with components `Spec α ≫ chartι W i` and `Spec β ≫ chartι W j`. -/
theorem SpecMap_desc_chartPairι {A : CommRingCat.{u}} {i j : Fin 3}
    (α : CommRingCat.of (W.toProjective.ChartRing i) ⟶ A)
    (β : CommRingCat.of (W.toProjective.ChartRing j) ⟶ A)
    (h : CommRingCat.ofHom (algebraMap R _) ≫ α = CommRingCat.ofHom (algebraMap R _) ≫ β) :
    Spec.map ((CommRingCat.isPushout_tensorProduct R _ _).desc α β h) ≫ W.chartPairι i j =
      pullback.lift (Spec.map α ≫ W.chartι i) (Spec.map β ≫ W.chartι j)
        (by simp [← Spec.map_comp, h]) := by
  ext <;> simp [← Spec.map_comp_assoc]

/-- A point of `E ×_S E` lies on the product of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)` exactly when its
two projections lie on `D₊(Xᵢ)` and `D₊(Xⱼ)`. -/
theorem range_chartPairι (i j : Fin 3) :
    Set.range (W.chartPairι i j) =
      pullback.fst W.projModelOver W.projModelOver ⁻¹' Set.range (W.chartι i) ∩
        pullback.snd W.projModelOver W.projModelOver ⁻¹' Set.range (W.chartι j) := by
  rw [chartPairι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (pullbackSpecIso R _ _).inv.surjective, Set.image_univ,
    Scheme.Pullback.range_map]

end WeierstrassCurve
