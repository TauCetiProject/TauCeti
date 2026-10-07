/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Charts of the projective Weierstrass model

Let `W` be a Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its projective
model and let `S = Spec R`. This file presents the standard affine chart `D₊(Xᵢ)` of `E` as an open
immersion from the spectrum of the chart ring `ChartRing i = R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`, and the
product `D₊(Xᵢ) ×_S D₊(Xⱼ)` of two charts as an open immersion from the spectrum of
`ChartRing i ⊗[R] ChartRing j` into `E ×_S E`.

## Main definitions

* `WeierstrassCurve.chartι W i`: the chart `D₊(Xᵢ)`, an open immersion
  `Spec (ChartRing i) ⟶ projModel W`.
* `WeierstrassCurve.chartPairι W i j`: the product of the charts `D₊(Xᵢ)` and `D₊(Xⱼ)`, an open
  immersion `Spec (ChartRing i ⊗[R] ChartRing j) ⟶ E ×_S E`.

## Main results

* `WeierstrassCurve.exists_mem_range_chartι`: the three charts cover the projective model.
* `WeierstrassCurve.chartι_projModelOver`: on the chart `D₊(Xᵢ)`, the structure morphism of the
  projective model is `Spec` of the structure map `R → ChartRing i`.
* `WeierstrassCurve.chartPairι_fst` and `WeierstrassCurve.chartPairι_snd`: the two projections of
  `E ×_S E` on the product of two charts.
* `WeierstrassCurve.range_chartPairι`: the product of two charts is the locus in `E ×_S E` whose
  projections lie on the two charts.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionChartSpec.lean`: `chartι`,
`chartι_projModelπ`, and `chartPieceTensorIso` with its `_inv_fst` and `_inv_snd` lemmas, as
`chartι`, `chartι_projModelOver`, `chartPairι`, `chartPairι_fst` and `chartPairι_snd`. Here the
chart is read through `WeierstrassCurve.Projective.awayEquivChartRing`, and the product of two
charts is an open immersion into `E ×_S E` rather than an isomorphism with a pullback.
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

/-- The charts `D₊(X₀)`, `D₊(X₁)` and `D₊(X₂)` cover the projective model. -/
theorem exists_mem_range_chartι (y : W.projModel) : ∃ i, y ∈ Set.range (W.chartι i) :=
  let 𝒰 := Proj.affineOpenCoverOfIrrelevantLESpan _ _ W.toProjective.coord_mem_grading
    (fun _ ↦ one_pos) W.toProjective.irrelevant_le_span_range_coord
  ⟨𝒰.idx y, (Scheme.Hom.opensRange_comp_of_isIso _ _).ge (𝒰.covers y)⟩

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
