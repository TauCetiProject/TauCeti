/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.FaceLocalization
public import TauCeti.Geometry.Toric.Algebraic.Regular
import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Finiteness
public import Mathlib.CategoryTheory.LocallyDirected
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The diagram of affine analytic charts of a fan

The complex points of the cones of any fan form a diagram of topological spaces.
An inclusion of cones acts by restriction of characters along the corresponding face.
For a regular fan, every map is an open embedding. When two points have the same image
in a third chart,
they come from the chart of the intersection cone. This is the overlap property needed
to glue the analytic charts and to compare that gluing with the algebraic fan scheme.

The topology on each chart is the finite-monomial-embedding topology. Its definition
chooses a finite generating family, but `affinePointTopology_eq` shows that the resulting
topology is independent of this choice.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.3–1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §3.1.
-/

public section

open CategoryTheory Topology

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} (Φ : Fan i)

/-- A finite generating family for the dual semigroup of any cone of a fan. -/
noncomputable def analyticChartGenerators (σ : Φ.cones) :
    Σ r, AddGeneratingFamily (dualSemigroup Φ.lattice σ.1) r := by
  letI : AddMonoid.FG (dualSemigroup Φ.lattice σ.1) :=
    (Φ.isToricCone σ.2).fg_dualSemigroup Φ.lattice
  let r := Classical.choose (exists_addGeneratingFamily (dualSemigroup Φ.lattice σ.1))
  exact ⟨r, Classical.choice (Classical.choose_spec
    (exists_addGeneratingFamily (dualSemigroup Φ.lattice σ.1)))⟩

/-- The affine complex-point chart of a cone, with its monomial-embedding topology. -/
@[expose] noncomputable def analyticAffineChart (σ : Φ.cones) : TopCat :=
  let g := analyticChartGenerators Φ σ
  let _ := affinePointTopology g.2
  TopCat.of (AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))

/-- The chart topology agrees with the monomial-embedding topology of any finite
generating family. -/
theorem analyticAffineChart_str_eq (σ : Φ.cones) {r : ℕ}
    (g : AddGeneratingFamily (dualSemigroup Φ.lattice σ.1) r) :
    (Φ.analyticAffineChart σ).str = affinePointTopology g :=
  affinePointTopology_eq (analyticChartGenerators Φ σ).2 g

/-- Each analytic affine chart is Hausdorff. -/
theorem t2Space_analyticAffineChart (σ : Φ.cones) :
    T2Space (Φ.analyticAffineChart σ) := by
  -- The bundled chart topology is the topology of its chosen monomial embedding.
  change @T2Space _ (affinePointTopology (analyticChartGenerators Φ σ).2)
  exact t2Space_affinePointTopology (analyticChartGenerators Φ σ).2

/-- Each analytic affine chart is second countable. -/
theorem secondCountableTopology_analyticAffineChart (σ : Φ.cones) :
    SecondCountableTopology (Φ.analyticAffineChart σ) := by
  -- The bundled chart topology is the topology of its chosen monomial embedding.
  change @SecondCountableTopology _
    (affinePointTopology (analyticChartGenerators Φ σ).2)
  exact secondCountableTopology_affinePointTopology (analyticChartGenerators Φ σ).2

/-- Each analytic affine chart is locally compact. -/
theorem locallyCompactSpace_analyticAffineChart (σ : Φ.cones) :
    LocallyCompactSpace (Φ.analyticAffineChart σ) := by
  -- The bundled chart topology is the topology of its chosen monomial embedding.
  change @LocallyCompactSpace _
    (affinePointTopology (analyticChartGenerators Φ σ).2)
  exact locallyCompactSpace_affinePointTopology (analyticChartGenerators Φ σ).2

/-- The analytic face map between two charts of a fan. -/
noncomputable def analyticFaceMap {τ σ : Φ.cones} (f : τ ⟶ σ) :
    Φ.analyticAffineChart τ ⟶ Φ.analyticAffineChart σ := by
  let gτ := analyticChartGenerators Φ τ
  let gσ := analyticChartGenerators Φ σ
  letI := affinePointTopology gτ.2
  letI := affinePointTopology gσ.2
  let hτσ := Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)
  exact TopCat.ofHom ⟨faceAffinePointMap Φ.lattice hτσ,
    continuous_faceAffinePointMap Φ.lattice hτσ gσ.2 gτ.2⟩

/-- An analytic face map restricts the character of a point to the smaller dual semigroup. -/
@[simp] theorem analyticFaceMap_apply {τ σ : Φ.cones} (f : τ ⟶ σ)
    (x : Φ.analyticAffineChart τ) :
    Φ.analyticFaceMap f x =
      faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)) x :=
  (rfl)

/-- The analytic affine charts of a fan, indexed by its cones. -/
@[expose] noncomputable def analyticAffineChartDiagram : Φ.cones ⥤ TopCat where
  obj σ := Φ.analyticAffineChart σ
  map f := Φ.analyticFaceMap f
  map_id σ := by
    apply TopCat.ext
    intro x
    -- Unwrap the bundled continuous map to use the face identity law.
    change faceAffinePointMap Φ.lattice (PointedCone.IsFaceOf.refl σ.1) x = x
    exact congrFun (faceAffinePointMap_id Φ.lattice (σ := σ.1)) x
  map_comp {X Y Z} f g := by
    apply TopCat.ext
    intro x
    -- Composition in `TopCat` is composition of the underlying face maps.
    change faceAffinePointMap Φ.lattice
        (Φ.isFaceOf_of_le Z.2 X.2 (leOfHom (f ≫ g))) x =
      faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le Z.2 Y.2 (leOfHom g))
        (faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le Y.2 X.2 (leOfHom f)) x)
    exact (faceAffinePointMap_faceAffinePointMap Φ.lattice _ _ x).symm

/-- The diagram object at a cone is its affine analytic chart. -/
@[simp]
theorem analyticAffineChartDiagram_obj (σ : Φ.cones) :
    (Φ.analyticAffineChartDiagram).obj σ =
      Φ.analyticAffineChart σ :=
  (rfl)

/-- The diagram map at a face inclusion is restriction of complex points. -/
@[simp]
theorem analyticAffineChartDiagram_map {τ σ : Φ.cones} (f : τ ⟶ σ) :
    (Φ.analyticAffineChartDiagram).map f =
      Φ.analyticFaceMap f :=
  (rfl)

/-- A map of the analytic affine chart diagram restricts a complex point along the inclusion of
dual semigroups. -/
theorem analyticAffineChartDiagram_map_apply {τ σ : Φ.cones} (f : τ ⟶ σ)
    (x : (Φ.analyticAffineChartDiagram).obj τ) :
    (Φ.analyticAffineChartDiagram).map f x =
      AffineSemigroupComplexPoint.comap
        (AddSubmonoid.inclusion (dualSemigroup_anti Φ.lattice (leOfHom f))) x :=
  congrFun (faceAffinePointMap_def Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))) x

/-- Pointwise composition of maps in the analytic affine chart diagram. -/
theorem analyticChartMap_comp {α β γ : Φ.cones}
    (f : α ⟶ β) (g : β ⟶ γ)
    (x : (Φ.analyticAffineChartDiagram).obj α) :
    (Φ.analyticAffineChartDiagram).map g
        ((Φ.analyticAffineChartDiagram).map f x) =
      (Φ.analyticAffineChartDiagram).map (f ≫ g) x := by
  exact (ConcreteCategory.congr_hom ((Φ.analyticAffineChartDiagram).map_comp f g) x).symm

/-- Every map in the analytic chart diagram is an open embedding. -/
theorem isOpenEmbedding_analyticAffineChartDiagram_map (hΦ : Φ.IsRegular) {τ σ : Φ.cones}
    (f : τ ⟶ σ) :
    IsOpenEmbedding (Φ.analyticAffineChartDiagram |>.map f) := by
  -- The chart objects carry exactly the chosen monomial-embedding topologies.
  change @IsOpenEmbedding _ _
    (affinePointTopology (analyticChartGenerators Φ τ).2)
    (affinePointTopology (analyticChartGenerators Φ σ).2)
    (faceAffinePointMap Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f)))
  exact ((isRegular_iff.mp hΦ) σ.1 σ.2).rational.isOpenEmbedding_faceAffinePointMap
    Φ.lattice (Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom f))
    (analyticChartGenerators Φ σ).2
    (analyticChartGenerators Φ τ).2

/-- Two affine analytic charts mapping into a third chart meet in the chart of the
intersection cone. -/
theorem isLocallyDirected_analyticAffineChartDiagram (hΦ : Φ.IsRegular) :
    (Φ.analyticAffineChartDiagram ⋙ forget TopCat).IsLocallyDirected := by
  refine ⟨fun {τ υ σ} fτ fυ xτ xυ h ↦ ?_⟩
  let hτσ := Φ.isFaceOf_of_le σ.2 τ.2 (leOfHom fτ)
  let hυσ := Φ.isFaceOf_of_le σ.2 υ.2 (leOfHom fυ)
  have h' : faceAffinePointMap Φ.lattice hτσ xτ =
      faceAffinePointMap Φ.lattice hυσ xυ := by
    -- Forgetting the bundled chart map gives the same restriction of characters.
    exact h
  have hσ := (isRegular_iff.mp hΦ) σ.1 σ.2
  let _ := affinePointTopology (analyticChartGenerators Φ σ).2
  let _ := affinePointTopology (analyticChartGenerators Φ τ).2
  let _ := affinePointTopology (analyticChartGenerators Φ υ).2
  have heτ : Function.Injective (faceAffinePointMap Φ.lattice hτσ) :=
    (hσ.rational.isOpenEmbedding_faceAffinePointMap Φ.lattice hτσ
      (analyticChartGenerators Φ σ).2 (analyticChartGenerators Φ τ).2).injective
  have heυ : Function.Injective (faceAffinePointMap Φ.lattice hυσ) :=
    (hσ.rational.isOpenEmbedding_faceAffinePointMap Φ.lattice hυσ
      (analyticChartGenerators Φ σ).2 (analyticChartGenerators Φ υ).2).injective
  obtain ⟨x, hx⟩ : faceAffinePointMap Φ.lattice hτσ xτ ∈
      Set.range (faceAffinePointMap Φ.lattice (hτσ.inf_left hυσ)) := by
    rw [hσ.rational.range_faceAffinePointMap_inf Φ.lattice hτσ hυσ]
    exact ⟨⟨xτ, rfl⟩, ⟨xυ, h'.symm⟩⟩
  have hτ : faceAffinePointMap Φ.lattice
      (Φ.isFaceOf_of_le τ.2 (Φ.inf_mem τ.2 υ.2) inf_le_left) x = xτ := by
    apply heτ
    rw [faceAffinePointMap_faceAffinePointMap, hx]
  have hυ : faceAffinePointMap Φ.lattice
      (Φ.isFaceOf_of_le υ.2 (Φ.inf_mem τ.2 υ.2) inf_le_right) x = xυ := by
    apply heυ
    rw [faceAffinePointMap_faceAffinePointMap, hx, h']
  refine ⟨τ ⊓ υ,
    homOfLE (Subtype.coe_le_coe.1 inf_le_left),
    homOfLE (Subtype.coe_le_coe.1 inf_le_right), x, ?_, ?_⟩
  · exact hτ
  · exact hυ

end TauCeti.Toric.Fan
