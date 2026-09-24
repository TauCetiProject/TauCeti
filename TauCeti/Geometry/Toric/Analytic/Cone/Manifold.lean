/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Toric.Analytic.Cone.Chart

/-!
# The complex manifold of a regular affine toric cone

The complex points of the affine toric scheme of a regular cone form a complex manifold.  After
choosing an integral basis extending the primitive ray generators and numbering the rays, the
ambient cone chart embeds them as the open mixed-coordinate locus
`ℂ^k × (ℂˣ)^l ⊆ ℂ^k × ℂ^l`.  Mathlib's singleton-chart construction therefore supplies a charted
space and a complex-manifold structure.

Although this construction names coordinates, its complex structure does not depend on the
extending basis or the generating family.  The transition between two extending bases is the mixed
monomial biholomorphism computed in
`TauCeti.Geometry.Toric.Analytic.Cone.Chart`; consequently the identity map between the two
singleton-chart structures is holomorphic in both directions.  The topology is likewise independent
of the finite semigroup generating family used to present the affine complex points.

## Main declarations

* `TauCeti.Toric.isOpenEmbedding_coneChartAmbient`: the ambient cone chart is an open embedding.
* `TauCeti.Toric.coneChartedSpace`: the complex charted-space structure induced by one system of
  regular cone coordinates.
* `TauCeti.Toric.contMDiff_coneChartAmbient` and
  `TauCeti.Toric.contMDiff_of_comp_coneChartAmbient`: the chart is holomorphic and lifts
  ambient holomorphy to maps into the affine cone chart.
* `TauCeti.Toric.isManifold_coneChartedSpace`: this charted space is a complex manifold.
* `TauCeti.Toric.contMDiff_id_coneChartedSpace`: changing the extending basis or the generating
  family preserves the complex structure.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.2 and 3.1.
-/

public section

open scoped ContDiff Manifold
open Function Set Topology

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {σ : PointedCone ℝ V} {s s' k l : ℕ}

variable (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {B B' : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N}
  (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ)))
  (hB' : ∀ ρ, IsPrimitiveGenerator i ρ (B' (Sum.inl ρ)))
  (κ : ToricRay σ ≃ Fin k)

/-- The ambient mixed-coordinate chart of a regular cone is an open embedding.  Its range is the
open locus on which every torus coordinate is nonzero. -/
theorem isOpenEmbedding_coneChartAmbient
    (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    @IsOpenEmbedding (AffineSemigroupComplexPoint (dualSemigroup hi σ))
      ((Fin k → ℂ) × (Fin l → ℂ)) (affinePointTopology g) inferInstance
      (coneChartAmbient hi hσ hB κ) := by
  let _ := affinePointTopology g
  have he : IsOpenEmbedding
      (Subtype.val ∘ coneChartAmbientHomeomorph hi hσ hB κ g) :=
    isOpen_mixedChartDomain.isOpenEmbedding_subtypeVal.comp
      (coneChartAmbientHomeomorph hi hσ hB κ g).isOpenEmbedding
  convert he using 1
  funext x
  exact (coneChartAmbientHomeomorph_apply hi hσ hB κ g x).symm

/-- The complex charted-space structure on the affine complex points of a regular cone, induced by
an extending integral basis and a numbering of the rays.  Its sole chart is the open embedding into
the ambient mixed-coordinate space. -/
@[instance_reducible]
noncomputable def coneChartedSpace (g : AddGeneratingFamily (dualSemigroup hi σ) s) :
    @ChartedSpace ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) (affinePointTopology g) := by
  let _ := affinePointTopology g
  let h := isOpenEmbedding_coneChartAmbient hi hσ hB κ g
  exact h.singletonChartedSpace

/-- The ambient mixed-coordinate chart of a regular cone is holomorphic for the complex
structure that it induces. -/
theorem contMDiff_coneChartAmbient (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ hB κ g
    ContMDiff 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n (coneChartAmbient hi hσ hB κ) := by
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  exact contMDiff_isOpenEmbedding (isOpenEmbedding_coneChartAmbient hi hσ hB κ g)

/-- A map into a regular affine toric chart is holomorphic if its composite with the ambient cone
chart is holomorphic. -/
theorem contMDiff_of_comp_coneChartAmbient
    {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [TopologicalSpace X] [ChartedSpace H X] (I : ModelWithCorners ℂ E H)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (f : X → AffineSemigroupComplexPoint (dualSemigroup hi σ)) (n : ℕ∞ω)
    (hf : ContMDiff I 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n
      (coneChartAmbient hi hσ hB κ ∘ f)) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ hB κ g
    ContMDiff I 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n f := by
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  exact ContMDiff.of_comp_isOpenEmbedding (isOpenEmbedding_coneChartAmbient hi hσ hB κ g) hf

/-- The target of every chart in the cone charted-space structure is the mixed-coordinate locus. -/
theorem coneChartedSpace_chartAt_target
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) :
    (@chartAt ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) (affinePointTopology g)
      (coneChartedSpace hi hσ hB κ g) x).target = mixedChartDomain k l := by
  let _ := affinePointTopology g
  rw [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq
      ((isOpenEmbedding_coneChartAmbient hi hσ hB κ g).toOpenPartialHomeomorph
        (coneChartAmbient hi hσ hB κ))
      (Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source _ _),
    IsOpenEmbedding.toOpenPartialHomeomorph_target, range_coneChartAmbient hi hσ hB κ]

/-- The affine complex points of a regular cone, with the singleton chart induced by an extending
basis, form a complex manifold to every differentiability order. -/
theorem isManifold_coneChartedSpace (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (n : ℕ∞ω) :
    let _ := affinePointTopology g
    let _ := coneChartedSpace hi hσ hB κ g
    IsManifold 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) := by
  let _ := affinePointTopology g
  let h := isOpenEmbedding_coneChartAmbient hi hσ hB κ g
  exact h.isManifold_singleton

/-- The identity map between the affine complex-point spaces equipped with two regular coordinate
systems is holomorphic.  Both the extending basis and the finite generating family used to define
the topology may change. -/
theorem contMDiff_id_coneChartedSpace
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (g' : AddGeneratingFamily (dualSemigroup hi σ) s') (n : ℕ∞ω) :
    @ContMDiff ℂ inferInstance
      ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance inferInstance
      ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) (affinePointTopology g)
      (coneChartedSpace hi hσ hB κ g)
      ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance inferInstance
      ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance
      𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
      (AffineSemigroupComplexPoint (dualSemigroup hi σ)) (affinePointTopology g')
      (coneChartedSpace hi hσ hB' κ g') n id := by
  apply @ContMDiff.of_comp_isOpenEmbedding ℂ inferInstance
    ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance inferInstance
    ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance
    𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
    (AffineSemigroupComplexPoint (dualSemigroup hi σ)) (affinePointTopology g)
    ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance inferInstance
    ((Fin k → ℂ) × (Fin l → ℂ)) inferInstance
    𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ))
    (AffineSemigroupComplexPoint (dualSemigroup hi σ)) (affinePointTopology g') n
    (coneChartedSpace hi hσ hB κ g) inferInstance
    (coneChartAmbient hi hσ hB' κ) (isOpenEmbedding_coneChartAmbient hi hσ hB' κ g') id
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ hB κ g
  let C : Matrix (Fin k) (Fin l) ℤ :=
    Matrix.of fun a c ↦ B'.toMatrix B (Sum.inl (κ.symm a)) (Sum.inr c)
  let D : Matrix (Fin l) (Fin l) ℤ := (B'.toMatrix B).submatrix Sum.inr Sum.inr
  let hD : IsUnit D.det := isUnit_det_toMatrix_submatrix_inr hi hσ.salient hB hB'
  have hchange : ContDiffOn ℂ n (basisChangeOpenPartialHomeomorph C D hD)
      (mixedChartDomain k l) := by
    simpa only [basisChangeOpenPartialHomeomorph_source] using
      contDiffOn_basisChangeOpenPartialHomeomorph (n := n) C D hD
  apply (hchange.contMDiffOn.comp_contMDiff
    (contMDiff_isOpenEmbedding (isOpenEmbedding_coneChartAmbient hi hσ hB κ g))
    (coneChartAmbient_mem_mixedChartDomain hi hσ hB κ)).congr
  intro x
  exact (basisChangeOpenPartialHomeomorph_coneChartAmbient hi hσ hB hB' κ x).symm

end TauCeti.Toric
