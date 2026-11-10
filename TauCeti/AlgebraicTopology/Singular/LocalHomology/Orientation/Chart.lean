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

The oriented local homology isomorphism of any chart factors through that of the identity chart of
the model, which is read through the connecting morphism and radial projection about the point.
Translations of the model preserve the local orientations selected in the identity chart.

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

variable {M E : Type w} [TopologicalSpace M] [T1Space M]
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

/-- The oriented local homology isomorphism of the identity chart of the model at `p` is the
connecting morphism of the pair `(E, E ∖ {p})`, followed by radial projection about `p` and the
sphere generator selected by the orientation. -/
theorem singularHomologyComplSingletonIsoOfOrientation_refl_hom {p : E}
    (hp : p ∈ (OpenPartialHomeomorph.refl E).source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E) hp o
        hE).hom =
      (TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R n ≫
        (reducedSingularHomologyFunctor R n).map
          (TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun) ≫
        (reducedSingularHomologySphereIsoOfOrientation R o hE).hom := by
  rw [singularHomologyComplSingletonIsoOfOrientation_hom, singularHomologyComplSingletonIso_hom,
    singularHomologyComplSingletonIsoOfChart_refl R hp, Iso.refl_hom]
  -- The identity chart sends `p` to `p` by definition, so the composite is only type-correct
  -- after unfolding it.
  erw [Category.id_comp, Category.assoc]
  rfl

/-- The oriented local homology isomorphism of a chart `φ` at `x` is the chart isomorphism of `φ`
followed by the oriented local homology isomorphism of the identity chart of the model at
`φ x`. -/
theorem singularHomologyComplSingletonIsoOfOrientation_hom_eq (φ : OpenPartialHomeomorph M E)
    {x : M} (hx : x ∈ φ.source) (hφx : φ x ∈ (OpenPartialHomeomorph.refl E).source) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    (singularHomologyComplSingletonIsoOfOrientation R φ hx o hE).hom =
      (singularHomologyComplSingletonIsoOfChart R φ hx (n + 1)).hom ≫
        (singularHomologyComplSingletonIsoOfOrientation R (OpenPartialHomeomorph.refl E) hφx o
          hE).hom := by
  rw [singularHomologyComplSingletonIsoOfOrientation_refl_hom,
    singularHomologyComplSingletonIsoOfOrientation_hom, singularHomologyComplSingletonIso_hom,
    Category.assoc, Category.assoc]

end Chart

section Integral

variable {M E : Type w} [TopologicalSpace M] [T1Space M]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The local orientation selected by an oriented chart. -/
def _root_.OpenPartialHomeomorph.localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {n : ℕ} (o : Orientation ℝ E (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) : LocalOrientation M x (n + 1) :=
  ⟨(singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
      φ hx o hE).inv 1,
    isLocalOrientation_inv_one _⟩

/-- The local orientation selected by an oriented chart is the preimage of `1` under the oriented
local homology isomorphism. -/
theorem _root_.OpenPartialHomeomorph.coe_localOrientationOfOrientedChart
    (φ : OpenPartialHomeomorph M E) {x : M}
    (hx : x ∈ φ.source) {n : ℕ} (o : Orientation ℝ E (Fin (n + 1)))
    (hE : finrank ℝ E = n + 1) :
    (φ.localOrientationOfOrientedChart hx o hE).val =
      (singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
        φ hx o hE).inv 1 :=
  (rfl)

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

section Translation

variable {E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Translation `y ↦ c + (y - p)` followed by radial projection about `c` is radial projection
about `p`. -/
private theorem snd_ofSubsetMap_translate_comp_complSingletonHomotopyEquivSphere (p c : E) :
    TopPair.Hom.snd (TopPair.ofSubsetMap (X := TopCat.of E) (Y := TopCat.of E)
        (TopCat.ofHom ⟨fun y : E ↦ c + (y - p), by fun_prop⟩) (B := {p}ᶜ) (B' := {c}ᶜ)
        (fun y hy h ↦ hy (sub_eq_zero.1 (add_eq_left.1 h)))) ≫
      TopCat.ofHom (complSingletonHomotopyEquivSphere c).toFun =
    TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun := by
  ext z
  -- The subspace of `TopPair.ofSubset` is the subtype only after unfolding the pair.
  erw [ConcreteCategory.comp_apply]
  refine ((coe_complSingletonHomotopyEquivSphere_apply c _).trans ?_).trans
    (coe_complSingletonHomotopyEquivSphere_apply p z).symm
  erw [TopPair.ofSubsetMap_snd_apply]
  simp

/-- Translation `y ↦ c + (y - p)` commutes with the connecting morphisms and radial projections
used to read local homology at `p` and at `c`. -/
@[reassoc]
private theorem localHomologyMap_translate_comp_reducedSingularHomologyδ (p c : E)
    (h : (⟨fun y ↦ c + (y - p), by fun_prop⟩ : C(E, E)) ⁻¹' {c} ⊆ {p}) (k : ℕ) :
    localHomologyMap R (⟨fun y ↦ c + (y - p), by fun_prop⟩ : C(E, E)) h (k + 1) ≫
        (TopPair.ofSubset ({c}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k ≫
          (reducedSingularHomologyFunctor R k).map
            (TopCat.ofHom (complSingletonHomotopyEquivSphere c).toFun) =
      (TopPair.ofSubset ({p}ᶜ : Set (TopCat.of E))).reducedSingularHomologyδ R k ≫
        (reducedSingularHomologyFunctor R k).map
          (TopCat.ofHom (complSingletonHomotopyEquivSphere p).toFun) := by
  rw [localHomologyMap_def, ← TopPair.reducedSingularHomologyδ_naturality_assoc]
  congr 1
  -- The composite is only type-correct after unfolding the subspace of the pair.
  erw [← Functor.map_comp, snd_ofSubsetMap_translate_comp_complSingletonHomotopyEquivSphere]

/-- **Translations preserve the model local orientations.** The translation `y ↦ c + (y - p)` of
the model carries the local orientation at `p` selected by `o` in the identity chart to the one
at `c`. -/
theorem localHomologyMap_translate_localOrientationOfOrientedChart_refl {p c : E}
    (hp : p ∈ (OpenPartialHomeomorph.refl E).source)
    (hc : c ∈ (OpenPartialHomeomorph.refl E).source)
    (h : (⟨fun y ↦ c + (y - p), by fun_prop⟩ : C(E, E)) ⁻¹' {c} ⊆ {p}) {n : ℕ}
    (o : Orientation ℝ E (Fin (n + 1))) (hE : finrank ℝ E = n + 1) :
    localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ)) (⟨fun y ↦ c + (y - p), by fun_prop⟩ : C(E, E)) h
        (n + 1)
        ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hp o hE).val =
      ((OpenPartialHomeomorph.refl E).localOrientationOfOrientedChart hc o hE).val := by
  let e {x : E} (hx : x ∈ (OpenPartialHomeomorph.refl E).source) :=
    singularHomologyComplSingletonIsoOfOrientation (ModuleCat.of ℤ (ULift.{w} ℤ))
      (OpenPartialHomeomorph.refl E) hx o hE
  have he : localHomologyMap (ModuleCat.of ℤ (ULift.{w} ℤ))
      (⟨fun y ↦ c + (y - p), by fun_prop⟩ : C(E, E)) h (n + 1) ≫ (e hc).hom = (e hp).hom := by
    simp only [e, singularHomologyComplSingletonIsoOfOrientation_refl_hom]
    exact localHomologyMap_translate_comp_reducedSingularHomologyδ_assoc _ p c h n _
  rw [OpenPartialHomeomorph.coe_localOrientationOfOrientedChart,
    OpenPartialHomeomorph.coe_localOrientationOfOrientedChart]
  apply (ConcreteCategory.bijective_of_isIso (e hc).hom).1
  rw [← ConcreteCategory.comp_apply, he]
  exact ((e hp).inv_hom_id_apply 1).trans ((e hc).inv_hom_id_apply 1).symm

end Translation

section Manifold

variable {M E : Type w} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T1Space M] [ChartedSpace E M]
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
