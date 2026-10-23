/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.SpecOver
public import TauCeti.Geometry.Toric.Algebraic.Fan.Over
public import TauCeti.Geometry.Toric.Analytic.Fan.GlueData

/-!
# Complex points of the toric scheme of a fan

A complex point of the toric scheme `X_Φ` of a finite fan `Φ` is a morphism `Spec ℂ ⟶ X_Φ` over
`Spec ℂ`, for the structure morphism `TauCeti.Toric.Fan.algebraicRealizationOver`. It is neither
a point of the underlying topological space of `X_Φ` nor a bare scheme morphism from `Spec ℂ`: on
an affine chart a bare morphism is a ring homomorphism from the coordinate ring to `ℂ`, which
need not be `ℂ`-linear.

On the affine chart of a cone `σ`, complex points are exactly the `ℂ`-algebra homomorphisms from
its coordinate ring to `ℂ`, the carrier `AffineSemigroupComplexPoint` of the analytic chart of
`σ`, by `TauCeti.AlgebraicGeometry.specOverHomEquivAlgHom`. This file shows that the complex
points of `X_Φ` are glued from these affine complex points exactly as the analytic realization is
glued from its charts: every complex point of `X_Φ` lies in some affine chart, and points of the
charts of `σ` and `τ` give the same complex point exactly when they come from a common point of
the chart of `σ ⊓ τ` under the two face maps `faceAffinePointMap`. The complex points of `X_Φ`
carry the topology glued from the monomial-embedding topologies of the affine charts, which do not
depend on the generating families used to define them. For a regular fan, the algebraic and the
analytic gluings agree, so the complex points of `X_Φ` are homeomorphic to the analytic
realization, by a homeomorphism that is the identity of complex points on every affine chart.

## Main declarations

* `TauCeti.Toric.Fan.AlgebraicComplexPoint`: the complex points of the toric scheme of a fan.
* `TauCeti.Toric.FanHom.algebraicComplexPointMap`: the action of fan morphisms on complex points,
  with identity and composition rules.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.ofAffinePoint`: the complex point given by a point of
  the affine chart of a cone.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.exists_ofAffinePoint_eq`: every complex point lies in
  an affine chart.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.ofAffinePoint_eq_ofAffinePoint_iff`: two chart points
  give the same complex point exactly when they come from the chart of the intersection cone.
* `TauCeti.Toric.Fan.AlgebraicComplexPoint.isOpen_iff_forall_isOpen_preimage_ofAffinePoint`: the
  topology on complex points glued from the monomial-embedding topologies of the affine charts.
* `TauCeti.Toric.Fan.algebraicAnalyticEquiv`: for a regular fan, the bijection between complex
  points of the toric scheme and points of the analytic realization, computed on affine charts by
  `TauCeti.Toric.Fan.algebraicAnalyticEquiv_ofAffinePoint`.
* `TauCeti.Toric.Fan.algebraicAnalyticHomeomorph`: the same bijection is a homeomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.4 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.1.
-/

public section

open AlgebraicGeometry CategoryTheory TauCeti.AlgebraicGeometry

namespace TauCeti.Toric

section

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- On complex points, the face map of a face `τ` of `σ` is the face morphism of affine toric
schemes: applying `Spec` to the restricted point is composing with `faceAffineToricSchemeMap`. -/
theorem spec_map_faceAffinePointMap (hi : IsIntegralLattice i) {τ σ : PointedCone ℝ V}
    (h : τ.IsFaceOf σ) (x : AffineSemigroupComplexPoint (dualSemigroup hi τ)) :
    Spec.map (CommRingCat.ofHom (faceAffinePointMap hi h x).toRingHom) =
      Spec.map (CommRingCat.ofHom x.toRingHom) ≫ faceAffineToricSchemeMap hi h := by
  rw [faceAffinePointMap_eq_comp, faceAffineToricSchemeMap_def, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  exact congrArg (Spec.map ∘ CommRingCat.ofHom) (AlgHom.comp_toRingHom _ _)

namespace Fan

variable (Φ : Fan i)

/-- The complex points of the toric scheme `X_Φ` of a finite fan: the morphisms
`Spec ℂ ⟶ X_Φ` over `Spec ℂ`. -/
abbrev AlgebraicComplexPoint :=
  {x : Spec (.of ℂ) ⟶ Φ.algebraicRealization // x.IsOver (Spec (.of ℂ))}

namespace AlgebraicComplexPoint

variable {Φ}

/-- The complex point of the toric scheme given by a complex point of the affine chart of a cone,
a `ℂ`-algebra homomorphism from its coordinate ring to `ℂ`. -/
noncomputable def ofAffinePoint (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) : Φ.AlgebraicComplexPoint :=
  ⟨Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Φ.affineToricChartι σ, inferInstance⟩

/-- The complex point of a chart point is `Spec` of the point followed by the chart inclusion. -/
theorem coe_ofAffinePoint (σ : Φ.cones)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)) :
    (ofAffinePoint σ x).1 = Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Φ.affineToricChartι σ :=
  (rfl)

/-- A point of the chart of a face `τ` of `σ` and its image under the face map give the same
complex point of the toric scheme. -/
@[simp]
theorem ofAffinePoint_faceAffinePointMap {τ σ : Φ.cones} (h : τ.1.IsFaceOf σ.1)
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice τ.1)) :
    ofAffinePoint σ (faceAffinePointMap Φ.lattice h x) = ofAffinePoint τ x := by
  ext1
  rw [coe_ofAffinePoint, coe_ofAffinePoint, spec_map_faceAffinePointMap, Category.assoc,
    faceAffineToricSchemeMap_comp_affineToricChartι]

/-- Every complex point of the toric scheme of a finite fan lies in one of its affine charts. -/
theorem exists_ofAffinePoint_eq (p : Φ.AlgebraicComplexPoint) :
    ∃ (σ : Φ.cones) (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1)),
      ofAffinePoint σ x = p := by
  have := p.2
  obtain ⟨σ, y, hy⟩ := Φ.exists_affineToricChartι_apply_eq (p.1 default)
  -- `Spec ℂ` has a single point, so the image of `p` is the image of that point.
  have hrange : Set.range p.1 ⊆ Set.range (Φ.affineToricChartι σ) := by
    rintro _ ⟨q, rfl⟩
    exact ⟨y, by rw [hy, Subsingleton.elim q default]⟩
  obtain ⟨x, hx⟩ := exists_spec_map_comp_eq_of_range_subset (R := ℂ) (Φ.affineToricChartι σ) p.1
    hrange
  exact ⟨σ, x, Subtype.ext hx⟩

/-- A complex point of the affine chart of a cone is determined by its complex point of the toric
scheme. -/
theorem ofAffinePoint_injective (σ : Φ.cones) : Function.Injective (ofAffinePoint (Φ := Φ) σ) := by
  intro x y h
  have h' := cancel_mono (Φ.affineToricChartι σ) |>.1 (congrArg Subtype.val h)
  exact AlgHom.toRingHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h'))

/-- Points of the affine charts of two cones `σ` and `τ` give the same complex point of the toric
scheme exactly when they come from a common point of the chart of `σ ⊓ τ` under the two face
maps. -/
theorem ofAffinePoint_eq_ofAffinePoint_iff {σ τ : Φ.cones}
    (x : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice σ.1))
    (y : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice τ.1)) :
    ofAffinePoint σ x = ofAffinePoint τ y ↔
      ∃ z : AffineSemigroupComplexPoint (dualSemigroup Φ.lattice (σ.1 ⊓ τ.1)),
        faceAffinePointMap Φ.lattice (Φ.inf_isFaceOf_left σ.2 τ.2) z = x ∧
          faceAffinePointMap Φ.lattice (Φ.inf_isFaceOf_right σ.2 τ.2) z = y := by
  refine ⟨fun h ↦ ?_, fun ⟨z, hzx, hzy⟩ ↦ ?_⟩
  · have h' := congrArg Subtype.val h
    rw [coe_ofAffinePoint, coe_ofAffinePoint] at h'
    -- The image of the single point of `Spec ℂ` lies in the chart of `σ ⊓ τ`.
    obtain ⟨w, hw, -⟩ := (Φ.affineToricChartι_eq_affineToricChartι_iff
      (Spec.map (CommRingCat.ofHom x.toRingHom) default)
      (Spec.map (CommRingCat.ofHom y.toRingHom) default)).1 (by
        rw [← Scheme.Hom.comp_apply, h', Scheme.Hom.comp_apply])
    have hrange : Set.range (Spec.map (CommRingCat.ofHom x.toRingHom)) ⊆
        Set.range (Φ.affineToricOverlapLeft σ τ) := by
      rintro _ ⟨q, rfl⟩
      exact ⟨w, by rw [hw, Subsingleton.elim q default]⟩
    have : IsOpenImmersion (Φ.affineToricOverlapLeft σ τ) := by
      rw [affineToricOverlapLeft_def]
      exact (Φ.isToricCone σ.2).rational.isOpenImmersion_faceAffineToricSchemeMap Φ.lattice _
    have : (Φ.affineToricOverlapLeft σ τ).IsOver (Spec (.of ℂ)) := by
      rw [affineToricOverlapLeft_def, faceAffineToricSchemeMap_def]
      infer_instance
    obtain ⟨z, hz⟩ := exists_spec_map_comp_eq_of_range_subset (R := ℂ)
      (Φ.affineToricOverlapLeft σ τ) _ hrange
    rw [affineToricOverlapLeft_def, ← spec_map_faceAffinePointMap] at hz
    have hzx : faceAffinePointMap Φ.lattice (Φ.inf_isFaceOf_left σ.2 τ.2) z = x := by
      refine ofAffinePoint_injective σ (Subtype.ext ?_)
      rw [coe_ofAffinePoint, coe_ofAffinePoint, hz]
    refine ⟨z, hzx, ofAffinePoint_injective τ ?_⟩
    rw [← h, ← hzx, ofAffinePoint_faceAffinePointMap (τ := σ ⊓ τ),
      ofAffinePoint_faceAffinePointMap (τ := σ ⊓ τ)]
  · rw [← hzx, ← hzy]
    exact (ofAffinePoint_faceAffinePointMap (τ := σ ⊓ τ) _ z).trans
      (ofAffinePoint_faceAffinePointMap (τ := σ ⊓ τ) _ z).symm

/-! ### The topology glued from the affine charts -/

/-- The topology on the complex points of the toric scheme glued from the affine charts: a set
is open exactly when its preimage in the complex points of every affine chart is open for the
monomial-embedding topology of the analytic chart, which by
`TauCeti.Toric.Fan.analyticAffineChart_str_eq` is the topology induced by any finite generating
family of the dual semigroup. -/
noncomputable instance : TopologicalSpace Φ.AlgebraicComplexPoint :=
  ⨆ σ : Φ.cones, .coinduced (fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x) inferInstance

/-- A set of complex points of the toric scheme is open exactly when its preimage in the complex
points of every affine chart is open. -/
theorem isOpen_iff_forall_isOpen_preimage_ofAffinePoint (s : Set Φ.AlgebraicComplexPoint) :
    IsOpen s ↔
      ∀ σ : Φ.cones, IsOpen ((fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x) ⁻¹' s) :=
  isOpen_iSup_iff

/-- The complex point of the toric scheme depends continuously on a point of an affine chart. -/
@[fun_prop]
theorem continuous_ofAffinePoint (σ : Φ.cones) :
    Continuous fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x :=
  continuous_iSup_rng (i := σ) continuous_coinduced_rng

end AlgebraicComplexPoint

end Fan

end

namespace FanHom

variable {N N' N'' V V' V'' : Type} [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
  [AddCommGroup V] [AddCommGroup V'] [AddCommGroup V''] [Module ℝ V] [Module ℝ V'] [Module ℝ V'']
  {i : N →+ V} {i' : N' →+ V'} {i'' : N'' →+ V''}
  {Φ : Fan i} {Ψ : Fan i'} {Ω : Fan i''} (f : FanHom Φ Ψ)

/-- The map on algebraic complex points induced by a fan morphism: compose the morphism
`Spec ℂ ⟶ X_Φ` over `Spec ℂ` with the toric morphism `X_Φ ⟶ X_Ψ`. -/
noncomputable def algebraicComplexPointMap (p : Φ.AlgebraicComplexPoint) :
    Ψ.AlgebraicComplexPoint :=
  letI := p.2
  ⟨p.1 ≫ f.algebraicMap, inferInstance⟩

/-- On scheme morphisms, the map of complex points is postcomposition by the algebraic map. -/
@[simp]
theorem coe_algebraicComplexPointMap (p : Φ.AlgebraicComplexPoint) :
    (f.algebraicComplexPointMap p).1 = p.1 ≫ f.algebraicMap :=
  (rfl)

/-- The identity fan morphism acts identically on algebraic complex points. -/
@[simp]
theorem algebraicComplexPointMap_id (p : Φ.AlgebraicComplexPoint) :
    (FanHom.id Φ).algebraicComplexPointMap p = p := by
  ext1
  simp

/-- Composition of fan morphisms acts by composition on algebraic complex points. -/
@[simp]
theorem algebraicComplexPointMap_comp (g : FanHom Ψ Ω) (p : Φ.AlgebraicComplexPoint) :
    (g.comp f).algebraicComplexPointMap p =
      g.algebraicComplexPointMap (f.algebraicComplexPointMap p) := by
  ext1
  simp [algebraicMap_comp, Category.assoc]

end FanHom

/-! ### The comparison with the analytic realization of a regular fan -/

namespace Fan

variable {N V : Type} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V} {Φ : Fan i}
  (hΦ : Φ.IsRegular)

open AlgebraicComplexPoint

/-- The analytic realization and the complex points of the toric scheme of a regular fan are glued
from the same affine charts along the same identifications: two chart points have the same image
in the analytic realization exactly when they give the same complex point of the toric scheme. -/
theorem analyticAffineChartι_eq_analyticAffineChartι_iff_ofAffinePoint_eq {σ τ : Φ.cones}
    (x : (Φ.analyticAffineChartDiagram).obj σ) (y : (Φ.analyticAffineChartDiagram).obj τ) :
    Φ.analyticAffineChartι hΦ σ x = Φ.analyticAffineChartι hΦ τ y ↔
      ofAffinePoint σ x = ofAffinePoint τ y := by
  refine (Φ.analyticAffineChartι_eq_analyticAffineChartι_iff hΦ x y).trans
    (Iff.trans ?_ (ofAffinePoint_eq_ofAffinePoint_iff x y).symm)
  -- The analytic overlap inclusions are the face maps on complex points.
  simp only [analyticOverlapLeft_def, analyticOverlapRight_def, analyticAffineChartDiagram_map]
  exact exists_congr fun z ↦ and_congr (Eq.congr_left (Φ.analyticFaceMap_apply _ z))
    (Eq.congr_left (Φ.analyticFaceMap_apply _ z))

/-- The point of the analytic realization of a regular fan corresponding to a complex point of its
toric scheme, read off in any affine chart containing it. -/
noncomputable def algebraicAnalyticEquiv :
    Φ.AlgebraicComplexPoint ≃ Φ.analyticRealization hΦ where
  toFun p := Φ.analyticAffineChartι hΦ (exists_ofAffinePoint_eq p).choose
    (exists_ofAffinePoint_eq p).choose_spec.choose
  invFun q := ofAffinePoint (Φ.exists_analyticAffineChartι_apply_eq hΦ q).choose
    (Φ.exists_analyticAffineChartι_apply_eq hΦ q).choose_spec.choose
  left_inv p := by
    have hp := (exists_ofAffinePoint_eq p).choose_spec.choose_spec
    refine ((analyticAffineChartι_eq_analyticAffineChartι_iff_ofAffinePoint_eq hΦ _ _).1 ?_).trans
      hp
    exact (Φ.exists_analyticAffineChartι_apply_eq hΦ _).choose_spec.choose_spec
  right_inv q := by
    have hq := (Φ.exists_analyticAffineChartι_apply_eq hΦ q).choose_spec.choose_spec
    refine ((analyticAffineChartι_eq_analyticAffineChartι_iff_ofAffinePoint_eq hΦ _ _).2 ?_).trans
      hq
    exact (exists_ofAffinePoint_eq _).choose_spec.choose_spec

/-- On every affine chart the comparison is the identity of complex points: the complex point of
the toric scheme given by a point `x` of the chart of `σ` corresponds to the point `x` of the
analytic chart of `σ`. -/
@[simp]
theorem algebraicAnalyticEquiv_ofAffinePoint (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj σ) :
    algebraicAnalyticEquiv hΦ (ofAffinePoint σ x) = Φ.analyticAffineChartι hΦ σ x :=
  (analyticAffineChartι_eq_analyticAffineChartι_iff_ofAffinePoint_eq hΦ _ _).2
    (exists_ofAffinePoint_eq _).choose_spec.choose_spec

/-- The inverse comparison sends the point `x` of the analytic chart of `σ` to the complex point
of the toric scheme given by `x`. -/
@[simp]
theorem algebraicAnalyticEquiv_symm_analyticAffineChartι (σ : Φ.cones)
    (x : (Φ.analyticAffineChartDiagram).obj σ) :
    (algebraicAnalyticEquiv hΦ).symm (Φ.analyticAffineChartι hΦ σ x) = ofAffinePoint σ x := by
  rw [Equiv.symm_apply_eq, algebraicAnalyticEquiv_ofAffinePoint]

/-- For a regular fan, the complex points of the toric scheme, with the topology glued from the
affine charts, are homeomorphic to the analytic realization, by a homeomorphism that is the
identity of complex points on every affine chart. -/
noncomputable def algebraicAnalyticHomeomorph :
    Φ.AlgebraicComplexPoint ≃ₜ Φ.analyticRealization hΦ where
  toEquiv := algebraicAnalyticEquiv hΦ
  continuous_toFun := by
    refine continuous_iSup_dom.2 fun σ ↦ continuous_coinduced_dom.2 ?_
    have : (algebraicAnalyticEquiv hΦ).toFun ∘ (fun x : Φ.analyticAffineChart σ ↦
        ofAffinePoint σ x) = Φ.analyticAffineChartι hΦ σ :=
      funext (algebraicAnalyticEquiv_ofAffinePoint hΦ σ)
    rw [this]
    exact (Φ.analyticAffineChartι hΦ σ).hom.continuous
  continuous_invFun := by
    refine continuous_def.2 fun s hs ↦ ?_
    rw [isOpen_iff_forall_preimage_analyticAffineChartι]
    intro σ
    have : (algebraicAnalyticEquiv hΦ).invFun ∘ Φ.analyticAffineChartι hΦ σ =
        fun x : Φ.analyticAffineChart σ ↦ ofAffinePoint σ x :=
      funext (algebraicAnalyticEquiv_symm_analyticAffineChartι hΦ σ)
    rw [← Set.preimage_comp, this]
    exact (isOpen_iff_forall_isOpen_preimage_ofAffinePoint s).1 hs σ

/-- The homeomorphism is the bijection `algebraicAnalyticEquiv`. -/
@[simp]
theorem coe_algebraicAnalyticHomeomorph :
    ⇑(algebraicAnalyticHomeomorph hΦ) = algebraicAnalyticEquiv hΦ :=
  (rfl)

/-- The inverse homeomorphism is the inverse of the bijection `algebraicAnalyticEquiv`. -/
@[simp]
theorem coe_algebraicAnalyticHomeomorph_symm :
    ⇑(algebraicAnalyticHomeomorph hΦ).symm = (algebraicAnalyticEquiv hΦ).symm :=
  (rfl)

end Fan

end TauCeti.Toric
