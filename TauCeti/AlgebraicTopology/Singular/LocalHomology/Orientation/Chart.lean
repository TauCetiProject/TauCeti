/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Basic
public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# Local homology generators from oriented charts

An orientation of a positive-dimensional real inner product space canonically selects the
generator of the reduced homology of its unit sphere: choose any orthonormal basis with that
orientation and use the basis-dependent sphere computation. The result is independent of the
choice of basis, is natural under orientation-preserving linear isometries, and changes sign when
the orientation is reversed.

Composing this generator with the chart computation of local homology gives the local orientation
selected by an oriented chart. This connects tangent-space orientations with the local homology
orientations used to construct fundamental classes.

The local generator is the one associated to an oriented coordinate chart in Hatcher's
*Algebraic Topology*, Section 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Metric Module
open scoped Manifold

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)

section Sphere

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The top-dimensional reduced homology generator of a unit sphere selected by an orientation of
the ambient inner product space. -/
def reducedSingularHomologySphereIsoOfOrientation {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (reducedSingularHomologyFunctor R n).obj (TopCat.of (sphere (0 : E) 1)) ≅ R :=
  reducedSingularHomologySphereIso R (o.finOrthonormalBasis (Nat.succ_pos n) hE)

/-- Any orthonormal basis compatible with `o` computes the sphere generator selected by `o`. -/
theorem reducedSingularHomologySphereIsoOfOrientation_eq {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) (hb : b.toBasis.orientation = o) :
    reducedSingularHomologySphereIsoOfOrientation R o hE =
      reducedSingularHomologySphereIso R b := by
  apply reducedSingularHomologySphereIso_eq_of_orientation_eq R
  simpa only [Orientation.finOrthonormalBasis_orientation] using hb.symm

/-- An orientation-preserving linear isometry carries the sphere generator selected by the source
orientation to the sphere generator selected by the target orientation. -/
@[reassoc]
theorem reducedSingularHomologySphereIsoOfOrientation_hom_naturality {F : Type w}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
    (oE : Orientation ℝ E (Fin (n + 1))) (oF : Orientation ℝ F (Fin (n + 1)))
    (f : E ≃ₗᵢ[ℝ] F) (hf : Orientation.map (Fin (n + 1)) f.toLinearEquiv oE = oF)
    (hE : finrank ℝ E = n + 1) :
    let hF : finrank ℝ F = n + 1 := (LinearEquiv.finrank_eq f.toLinearEquiv).symm.trans hE
    (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom ⟨f.toLinearIsometry.unitSphereMap,
            f.toLinearIsometry.continuous_unitSphereMap⟩) ≫
        (reducedSingularHomologySphereIsoOfOrientation R oF hF).hom =
      (reducedSingularHomologySphereIsoOfOrientation R oE hE).hom := by
  dsimp only
  let b := oE.finOrthonormalBasis (Nat.succ_pos n) hE
  let c := b.map f
  have hc : c.toBasis.orientation = oF := by
    rw [OrthonormalBasis.toBasis_map, Basis.orientation_map,
      Orientation.finOrthonormalBasis_orientation, hf]
  rw [reducedSingularHomologySphereIsoOfOrientation_eq R oE hE b
      (Orientation.finOrthonormalBasis_orientation _ _ _),
    reducedSingularHomologySphereIsoOfOrientation_eq R oF
      ((LinearEquiv.finrank_eq f.toLinearEquiv).symm.trans hE) c hc]
  exact reducedSingularHomologySphereIso_hom_naturality R b c f.toLinearIsometry (by simp [c])

/-- Reversing the ambient orientation negates the selected sphere generator. -/
theorem reducedSingularHomologySphereIsoOfOrientation_neg_hom {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (reducedSingularHomologySphereIsoOfOrientation R (-o) hE).hom =
      -(reducedSingularHomologySphereIsoOfOrientation R o hE).hom := by
  apply reducedSingularHomologySphereIso_hom_eq_neg_of_orientation_ne R
  simp only [Orientation.finOrthonormalBasis_orientation]
  exact Module.Ray.ne_neg_self o

end Sphere

section Chart

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The top-degree local homology isomorphism selected by an orientation of the chart model. -/
def singularHomologyComplSingletonIsoOfOrientation (φ : OpenPartialHomeomorph M E)
    {x : M} (hx : x ∈ φ.source) {n : ℕ} (o : Orientation ℝ E (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of M))).singularHomology R (n + 1) ≅ R :=
  singularHomologyComplSingletonIso R φ hx n ≪≫
    reducedSingularHomologySphereIsoOfOrientation R o hE

/-- The oriented local homology isomorphism is the chart isomorphism followed by the sphere
generator selected by the chart-model orientation. -/
@[simp]
theorem singularHomologyComplSingletonIsoOfOrientation_hom
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).hom =
      (singularHomologyComplSingletonIso R φ hx n).hom ≫
        (reducedSingularHomologySphereIsoOfOrientation R o hE).hom := by
  simp only [singularHomologyComplSingletonIsoOfOrientation, Iso.trans_hom]

/-- The inverse oriented local homology isomorphism first selects the oriented sphere generator
and then carries it into the chart. -/
@[simp]
theorem singularHomologyComplSingletonIsoOfOrientation_inv
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).inv =
      (reducedSingularHomologySphereIsoOfOrientation R o hE).inv ≫
        (singularHomologyComplSingletonIso R φ hx n).inv := by
  simp only [singularHomologyComplSingletonIsoOfOrientation, Iso.trans_inv]

/-- Reversing the chart-model orientation negates the local homology coordinate map. -/
theorem singularHomologyComplSingletonIsoOfOrientation_neg_hom
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (singularHomologyComplSingletonIsoOfOrientation R φ hx (-o) hE).hom =
      -(singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).hom := by
  simp only [singularHomologyComplSingletonIsoOfOrientation, Iso.trans_hom,
    reducedSingularHomologySphereIsoOfOrientation_neg_hom, Preadditive.comp_neg]

/-- Reversing the chart-model orientation negates the inverse of the local homology coordinate
map. -/
theorem singularHomologyComplSingletonIsoOfOrientation_neg_inv
    (φ : OpenPartialHomeomorph M E) {x : M} (hx : x ∈ φ.source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (singularHomologyComplSingletonIsoOfOrientation R φ hx (-o) hE).inv =
      -(singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).inv := by
  rw [← cancel_mono (singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).hom]
  calc
    (singularHomologyComplSingletonIsoOfOrientation R φ hx (-o) hE).inv ≫
          (singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).hom =
        (singularHomologyComplSingletonIsoOfOrientation R φ hx (-o) hE).inv ≫
          (-(singularHomologyComplSingletonIsoOfOrientation R φ hx (-o) hE).hom) := by
      rw [singularHomologyComplSingletonIsoOfOrientation_neg_hom, neg_neg]
    _ = -𝟙 R := by rw [Preadditive.comp_neg, Iso.inv_hom_id]
    _ = (-(singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).inv) ≫
          (singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).hom := by
      rw [Preadditive.neg_comp, Iso.inv_hom_id]

end Chart

section Integral

variable {M E : Type w} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The local orientation selected by an oriented chart. -/
def _root_.OpenPartialHomeomorph.localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {n : ℕ} (o : Orientation ℝ E (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) : LocalOrientation M x (n + 1) :=
  ⟨(singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
      φ hx o hE).inv 1,
    isLocalOrientation_inv_one _⟩

/-- Reversing the chart-model orientation reverses the selected local orientation. -/
@[simp]
theorem _root_.OpenPartialHomeomorph.localOrientationOfOrientedChart_neg
    (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {n : ℕ} (o : Orientation ℝ E (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) :
    φ.localOrientationOfOrientedChart hx (-o) hE =
      -φ.localOrientationOfOrientedChart hx o hE := by
  apply Subtype.ext
  rw [LocalOrientation.coe_neg]
  exact congrArg (fun f ↦ f 1) (singularHomologyComplSingletonIsoOfOrientation_neg_inv
    (ModuleCat.of ℤ (ULift.{w} ℤ)) φ hx o hE)

end Integral

section Manifold

variable {M E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- The local homology orientation at a point selected by an orientation of a boundaryless
manifold. The quotient presentation of manifold orientations causes no ambiguity: simultaneously
reversing the model orientation and every chart sign preserves the signed model orientation in
the preferred chart. -/
def localOrientationOfManifoldOrientation {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) (x : M) : LocalOrientation M x (n + 1) :=
  o.lift
    (fun l ↦ (chartAt E x).localOrientationOfOrientedChart (mem_chart_source E x)
      (l.chartOrientation x ⟨x, mem_chart_source E x⟩) hE)
    (fun l ↦ by
      have hchart : l.flip.chartOrientation x ⟨x, mem_chart_source E x⟩ =
          l.chartOrientation x ⟨x, mem_chart_source E x⟩ := by
        rw [← l.flip.orientationAt_eq x, l.orientationAt_flip, l.orientationAt_eq x]
      rw [hchart])

/-- The local orientation selected by a represented manifold orientation is the oriented-chart
generator for its signed model orientation in the preferred chart. -/
@[simp]
theorem localOrientationOfManifoldOrientation_mk {n : ℕ}
    (l : Manifold.OrientationLift 𝓘(ℝ, E) M (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) (x : M) :
    localOrientationOfManifoldOrientation (Manifold.Orientation.mk l) hE x =
      (chartAt E x).localOrientationOfOrientedChart (mem_chart_source E x)
        (l.chartOrientation x ⟨x, mem_chart_source E x⟩) hE := by
  simp only [localOrientationOfManifoldOrientation, Manifold.Orientation.lift_mk]

/-- Reversing a manifold orientation reverses every local homology orientation it selects. -/
@[simp]
theorem localOrientationOfManifoldOrientation_neg {n : ℕ}
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) (x : M) :
    localOrientationOfManifoldOrientation (-o) hE x =
      -localOrientationOfManifoldOrientation o hE x := by
  induction o using Manifold.Orientation.inductionOn with
  | _ l =>
      simp only [localOrientationOfManifoldOrientation, Manifold.Orientation.neg_mk,
        Manifold.Orientation.lift_mk]
      have hchart : (-l).chartOrientation x ⟨x, mem_chart_source E x⟩ =
          -l.chartOrientation x ⟨x, mem_chart_source E x⟩ := by
        rw [← (-l).orientationAt_eq x, l.orientationAt_neg, l.orientationAt_eq x]
        congr
      rw [hchart, OpenPartialHomeomorph.localOrientationOfOrientedChart_neg]

end Manifold

end TauCeti
