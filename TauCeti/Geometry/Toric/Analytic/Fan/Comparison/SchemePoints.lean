/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Fan.ProjectiveSpace.Proj
public import TauCeti.Geometry.Toric.Analytic.AffinePoint.PointTopology
public import TauCeti.Geometry.Toric.Analytic.Fan.Comparison.TorusAction
public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Compact
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Charts
public import TauCeti.Topology.Algebra.PointTopology.Scheme.Functoriality

/-!
# Toric complex points and the chart topology of scheme points

The complex points of the toric scheme `X_Φ` of a finite fan carry two topologies glued from
affine charts. The toric one, on `TauCeti.Toric.Fan.AlgebraicComplexPoint`, is glued from the
monomial-embedding topologies of the charts of the cones of `Φ`. The general one,
`TauCeti.SchemePointTopology.topology` on the morphisms `Spec ℂ ⟶ X_Φ` over `Spec ℂ`, is glued
from the evaluation topologies of all affine open charts. This file shows that they agree.

On a single chart, the monomial-embedding topology of any finite generating family of the
semigroup is the evaluation topology `TauCeti.PointTopology.topology`
(`TauCeti.Toric.affinePointTopology_eq_pointTopology`). Globally, the charts of the cones are
open embeddings for the chart topology (`TauCeti.SchemePointTopology.isOpenEmbedding_chartPoint`)
and cover all complex points, so continuity of the inverse comparison may be checked on them.

Consequently the toric results transfer to the chart topology: for a nonempty regular fan the
complex points are compact exactly when the fan is complete, and the complex points of the
projective space `Proj ℂ[X_0, …, X_n]`, the projective spectrum of the symmetric algebra of
`ℂ^{n+1}`, are compact. The latter is the input from projective geometry to the comparison of
proper morphisms with proper maps on complex points.

## Main declarations

* `TauCeti.Toric.Fan.analyticAffineChart_str_eq_pointTopology`: the analytic affine chart of a
  cone carries the evaluation topology.
* `TauCeti.Toric.Fan.algebraicComplexPointHomeomorph`: the toric complex points of `X_Φ` are
  homeomorphic, by the identity of underlying morphisms, to its points over `Spec ℂ` with the
  chart topology.
* `TauCeti.Toric.Fan.compactSpace_points_iff_isComplete`: for a nonempty regular fan, the points
  are compact exactly when the fan is complete.
* `TauCeti.Toric.compactSpace_points_projToSpec`: the complex points of `Proj ℂ[X_0, …, X_n]`
  are compact.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII, §1.1.
* J.-P. Serre, *Géométrie algébrique et géométrie analytique*, Ann. Inst. Fourier 6 (1956), §2.
* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.4.
-/

public section

open AlgebraicGeometry CategoryTheory Multiplicative Topology

namespace TauCeti.Toric

namespace Fan

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

open SchemePointTopology
open scoped PointTopology

/-- The analytic affine chart of a cone carries the evaluation topology. -/
theorem analyticAffineChart_str_eq_pointTopology (σ : Φ.cones) :
    (Φ.analyticAffineChart σ).str = PointTopology.topology := by
  obtain ⟨r, g⟩ := analyticChartGenerators Φ σ
  rw [Φ.analyticAffineChart_str_eq σ g, affinePointTopology_eq_pointTopology]

attribute [local instance] SchemePointTopology.topology

/-- The toric complex points of the scheme of a finite fan are its points over `Spec ℂ`: both
are the morphisms `Spec ℂ ⟶ X_Φ` over `Spec ℂ`. -/
noncomputable def algebraicComplexPointEquiv :
    Φ.AlgebraicComplexPoint ≃ Points (R := ℂ) Φ.algebraicRealizationStructureMap where
  toFun p := ⟨p.val, by rw [← algebraicRealization_over, p.property.comp_over, specOverSpec_over]⟩
  invFun p := ⟨p.val, ⟨by rw [algebraicRealization_over, p.property, specOverSpec_over]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The comparison of complex points keeps the underlying morphism `Spec ℂ ⟶ X_Φ`. -/
@[simp]
theorem coe_algebraicComplexPointEquiv_apply (p : Φ.AlgebraicComplexPoint) :
    (Φ.algebraicComplexPointEquiv p).val = p.val :=
  (rfl)

/-- The inverse comparison of complex points keeps the underlying morphism `Spec ℂ ⟶ X_Φ`. -/
@[simp]
theorem coe_algebraicComplexPointEquiv_symm_apply
    (p : Points (R := ℂ) Φ.algebraicRealizationStructureMap) :
    (Φ.algebraicComplexPointEquiv.symm p).val = p.val :=
  (rfl)

/-- On the chart of a cone, the comparison sends the toric chart point to the chart point of the
affine open chart. -/
theorem algebraicComplexPointEquiv_ofAffinePoint (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.val)) :
    Φ.algebraicComplexPointEquiv (AlgebraicComplexPoint.ofAffinePoint σ x) =
      chartPoint Φ.algebraicRealizationStructureMap
        (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.val)) (Φ.affineToricChartι σ)
        (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ) x := by
  ext1
  rw [coe_algebraicComplexPointEquiv_apply, AlgebraicComplexPoint.coe_ofAffinePoint,
    chartPoint_val]

/-- The toric complex points of the scheme of a finite fan are homeomorphic to its points over
`Spec ℂ` with the chart topology. The underlying map is the identity of morphisms
`Spec ℂ ⟶ X_Φ`. -/
noncomputable def algebraicComplexPointHomeomorph :
    Φ.AlgebraicComplexPoint ≃ₜ Points (R := ℂ) Φ.algebraicRealizationStructureMap where
  toEquiv := Φ.algebraicComplexPointEquiv
  continuous_toFun := by
    refine continuous_iSup_dom.2 fun σ ↦ continuous_coinduced_dom.2 ?_
    have hid : Continuous[(Φ.analyticAffineChart σ).str, PointTopology.topology]
        (id : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.val) → _) :=
      continuous_id_of_le (Φ.analyticAffineChart_str_eq_pointTopology σ).le
    refine ((continuous_chartPoint (R := ℂ) Φ.algebraicRealizationStructureMap
      (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.val)) (Φ.affineToricChartι σ)
      (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)).comp hid).congr fun x ↦ ?_
    exact (Φ.algebraicComplexPointEquiv_ofAffinePoint σ x).symm
  continuous_invFun := by
    -- The charts of the cones are open embeddings covering the points.
    refine continuous_of_cover_nhds (s := fun σ : Φ.cones ↦ Set.range (chartPoint (R := ℂ)
      Φ.algebraicRealizationStructureMap (CommAlgCat.of ℂ (affineCoordinateRing Φ.lattice σ.val))
      (Φ.affineToricChartι σ) (Φ.affineToricChartι_comp_algebraicRealizationStructureMap σ)))
      (fun p ↦ ?_) (fun σ ↦ ?_)
    · obtain ⟨σ, x, hx⟩ :=
        AlgebraicComplexPoint.exists_ofAffinePoint_eq (Φ.algebraicComplexPointEquiv.symm p)
      refine ⟨σ, (isOpenEmbedding_chartPoint _ _ _ _).isOpen_range.mem_nhds ⟨x, ?_⟩⟩
      rw [← algebraicComplexPointEquiv_ofAffinePoint, hx, Equiv.apply_symm_apply]
    · rw [← Set.image_univ, (isOpenEmbedding_chartPoint _ _ _ _).isInducing.continuousOn_image_iff,
        continuousOn_univ]
      have hid : Continuous[PointTopology.topology, (Φ.analyticAffineChart σ).str]
          (id : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.val) → _) :=
        continuous_id_of_le (Φ.analyticAffineChart_str_eq_pointTopology σ).ge
      refine ((AlgebraicComplexPoint.continuous_ofAffinePoint σ).comp hid).congr fun x ↦ ?_
      exact (Φ.algebraicComplexPointEquiv.symm_apply_eq.2
        (Φ.algebraicComplexPointEquiv_ofAffinePoint σ x).symm).symm

/-- The comparison homeomorphism is the comparison of complex points. -/
@[simp]
theorem coe_algebraicComplexPointHomeomorph :
    ⇑Φ.algebraicComplexPointHomeomorph = Φ.algebraicComplexPointEquiv :=
  (rfl)

/-- The inverse comparison homeomorphism is the inverse comparison of complex points. -/
@[simp]
theorem coe_algebraicComplexPointHomeomorph_symm :
    ⇑Φ.algebraicComplexPointHomeomorph.symm = Φ.algebraicComplexPointEquiv.symm :=
  (rfl)

end Fan

namespace Fan

open SchemePointTopology

attribute [local instance] SchemePointTopology.topology

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V} {Φ : Fan i}

/-- For a nonempty regular fan, the complex points of its scheme, with the chart topology, are
compact exactly when the fan is complete. -/
theorem compactSpace_points_iff_isComplete (hΦ : Φ.IsRegular) (hΦ0 : Nonempty Φ.cones) :
    CompactSpace (Points (R := ℂ) Φ.algebraicRealizationStructureMap) ↔ Φ.IsComplete := by
  rw [← compactSpace_algebraicComplexPoint_iff_isComplete hΦ hΦ0]
  exact ⟨fun _ ↦ Φ.algebraicComplexPointHomeomorph.symm.compactSpace,
    fun _ ↦ Φ.algebraicComplexPointHomeomorph.compactSpace⟩

end Fan

open SchemePointTopology TauCeti.SymmetricAlgebra

attribute [local instance] SchemePointTopology.topology

/-- **Complex projective space is compact.** The complex points of `Proj ℂ[X_0, …, X_n]`, the
projective spectrum of the symmetric algebra of `ℂ^{n+1}`, are compact for the chart
topology. -/
instance compactSpace_points_projToSpec (n : ℕ) :
    CompactSpace (Points (R := ℂ) (projToSpec ℂ (Option (Fin n) → ℂ))) := by
  let b := Pi.basisFun ℤ (Fin n)
  let hi := isIntegralLattice_intCast n
  let g := Fan.projectiveSpaceToProj b hi
  have hg : g ≫ projToSpec ℂ (Option (Fin n) → ℂ) =
      (Fan.projectiveSpace b hi).algebraicRealizationStructureMap := by
    rw [← over_eq_projToSpec, comp_over, Fan.algebraicRealization_over]
  have := (Fan.compactSpace_points_iff_isComplete (Fan.isRegular_projectiveSpace b hi)
    ⟨⟨⊥, Fan.bot_mem_projectiveSpace_cones b hi⟩⟩).2 (Fan.isComplete_projectiveSpace b hi)
  refine Function.Surjective.compactSpace (continuous_map g hg) fun y ↦ ?_
  refine ⟨⟨y.val ≫ inv g, ?_⟩, Subtype.ext ?_⟩
  · rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, y.property]
  · simp

end TauCeti.Toric
