/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Regular
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Separated
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.UniversallyClosed
public import TauCeti.AlgebraicGeometry.Scheme.Place.Proper
public import TauCeti.FieldTheory.FunctionField.Place.Map

/-!
# The two-chart model of a function field is proper, and its points are the places

Let `F / k` be an algebraic function field and `x ∈ F` transcendental over `k`. The scheme
`X = TauCeti.AlgebraicGeometry.twoChartModel hF hx` is glued from `Spec 𝒪_x` and `Spec 𝒪_{x⁻¹}`,
where `𝒪_x` and `𝒪_{x⁻¹}` are the rings of functions regular wherever `x`, respectively `x⁻¹`, is
regular. It is separated, universally closed and locally of finite type over `k`, so it is
**proper over `k`**: a regular proper curve over `k` with function field `F`.

On such a curve every point other than the generic point is the centre of exactly one place of
its function field (`TauCeti.AlgebraicGeometry.CodimensionOnePoint.equivPlace`). Composing with
the identification `k(X) ≃ₐ[k] F` gives the equivalence `twoChartModel.equivPlace` between the
codimension-one points of `X` and the places of `F / k`. The valuation ring of the place attached
to a point is the local ring there, and its degree is the residue degree of the point.

The equivalence is compatible with the two charts: a point lies on the finite chart `Spec 𝒪_x`
exactly when `x` is regular at its place. So the points of the finite chart are the places at
which `x` has no pole, as for the normalization of the affine line in `F`, and the remaining
points, on the chart at infinity, are the poles of `x`.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.isProper`: the structure morphism to `Spec k` is
  proper.
* `TauCeti.AlgebraicGeometry.twoChartModel.equivPlace`: the codimension-one points of the
  two-chart model are equivalent to the places of `F / k`.
* `TauCeti.AlgebraicGeometry.twoChartModel.equivPlace_apply`: the place of a point is the place
  `AlgebraicGeometry.Scheme.toPlace` attaches to it, transported to `F`.
* `TauCeti.AlgebraicGeometry.twoChartModel.mem_integers_equivPlace_iff`: the valuation ring of
  the place attached to a point is the image of the local ring at that point.
* `TauCeti.AlgebraicGeometry.twoChartModel.degree_equivPlace`: the degree of that place is the
  residue degree of the point over `k`.
* `TauCeti.AlgebraicGeometry.twoChartModel.mem_range_ιFinite_iff`: a point lies on the finite
  chart exactly when `x` is regular at its place.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section I.6 and Theorem II.4.7.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Appendix B.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {hF : IsFunctionField k F} {x : F}
  {hx : x ≠ 0}

/-- **The two-chart model is proper over `k`**, for `x` transcendental over `k`: it is separated,
universally closed, and locally of finite type over `k`. -/
theorem isProper (hxt : Transcendental k x) : IsProper (twoChartModel hF hx ↘ Spec (.of k)) :=
  have := locallyOfFiniteType (hF := hF) (hx := hx) hxt
  { }

/-- **The codimension-one points of the two-chart model are the places of `F`**, for `x`
transcendental over `k`: a point is sent to the place of `k(X) ≃ₐ[k] F` whose valuation ring is
the local ring at the point. -/
noncomputable def equivPlace (hxt : Transcendental k x) :
    CodimensionOnePoint (twoChartModel hF hx) ≃ Place k F :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  (CodimensionOnePoint.equivPlace (k := k) (valuativeCriterion_existence hF hx)
    (coheight_le_one hxt)).trans (Place.mapEquiv (functionFieldEquiv hxt))

/-- `TauCeti.AlgebraicGeometry.twoChartModel.equivPlace` is the place attached to the point by
`AlgebraicGeometry.Scheme.toPlace`, transported along `k(X) ≃ₐ[k] F`. -/
theorem equivPlace_apply (hxt : Transcendental k x)
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt p
    equivPlace hxt p = ((twoChartModel hF hx).toPlace (k := k) (p : twoChartModel hF hx)).map
      (functionFieldEquiv hxt) := by
  simp [equivPlace]

/-- **The valuation ring of the place of a point is the local ring at the point**: `f ∈ F` is
regular at `equivPlace hxt p` exactly when it is the image of an element of the stalk at `p`. -/
theorem mem_integers_equivPlace_iff (hxt : Transcendental k x)
    (p : CodimensionOnePoint (twoChartModel hF hx)) (f : F) :
    f ∈ (equivPlace hxt p).integers ↔
      ∃ a : (twoChartModel hF hx).presheaf.stalk (p : twoChartModel hF hx),
        functionFieldEquiv hxt (algebraMap _ (twoChartModel hF hx).functionField a) = f := by
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt p
  rw [equivPlace_apply, Place.mem_integers_map_iff,
    Scheme.mem_toPlace_integers_iff_exists_stalk]
  exact exists_congr fun a ↦ (functionFieldEquiv hxt).eq_symm_apply

/-- **The degree of the place of a point is the residue degree of the point** over `k`. -/
@[simp]
theorem degree_equivPlace (hxt : Transcendental k x)
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    (equivPlace hxt p).degree =
      (twoChartModel hF hx ↘ Spec (.of k)).residueDegree (p : twoChartModel hF hx) := by
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt p
  rw [equivPlace_apply, Place.degree_map, Scheme.toPlace_degree_eq_residueDegree]

/-- **A point lies on the finite chart exactly when `x` is regular at its place.** Hence the
points of the finite chart `Spec 𝒪_x` are the places at which `x` has no pole, and the points off
it are the poles of `x`. -/
theorem mem_range_ιFinite_iff (hxt : Transcendental k x)
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    (p : twoChartModel hF hx) ∈ Set.range (ιFinite hF hx) ↔
      x ∈ (equivPlace hxt p).integers := by
  have := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  -- The function `x` on the finite chart.
  let xf : holomorphyRing {P : Place k F | x ∈ P.integers} :=
    ⟨x, mem_holomorphyRing_iff.mpr fun _ hP ↦ hP⟩
  constructor
  · -- The germ of `x` at a point of the finite chart is an element of the local ring there.
    rintro ⟨q, hq⟩
    have hpU : (p : twoChartModel hF hx) ∈ ιFinite hF hx ''ᵁ ⊤ := ⟨q, trivial, hq⟩
    refine (mem_integers_equivPlace_iff hxt p x).mpr
      ⟨(twoChartModel hF hx).presheaf.germ _ _ hpU ((finiteChartSectionsEquiv hF hx).symm xf), ?_⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, functionFieldEquiv_germToFunctionField,
      RingEquiv.apply_symm_apply]
  · -- If `x` is regular at the place `P` of `p`, then so is all of `𝒪_x`, and `Spec 𝒪_P → Spec 𝒪_x`
    -- followed by the finite chart is a lift of the generic point whose closed point is the
    -- centre `p` of `P`.
    intro hxP
    let e := functionFieldEquiv (hF := hF) (hx := hx) hxt
    let P : Place k (twoChartModel hF hx).functionField :=
      (twoChartModel hF hx).toPlace (k := k) (p : twoChartModel hF hx)
    have hmem (f : holomorphyRing {Q : Place k F | x ∈ Q.integers}) :
        e.symm (f : F) ∈ P.integers := by
      have hP : P = (equivPlace hxt p).map e.symm := by
        rw [equivPlace_apply, Place.map_symm_map]
      rw [hP, Place.mem_integers_map_iff, AlgEquiv.symm_symm, AlgEquiv.apply_symm_apply]
      exact mem_holomorphyRing_iff.mp f.2 _ hxP
    let φ : holomorphyRing {Q : Place k F | x ∈ Q.integers} →+* P.integers :=
      (e.symm.toRingHom.comp (holomorphyRing _).val.toRingHom).codRestrict P.integers hmem
    have hl : Spec.map (CommRingCat.ofHom
          (algebraMap P.integers (twoChartModel hF hx).functionField)) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ ιFinite hF hx =
          (twoChartModel hF hx).fromSpecStalk (genericPoint (twoChartModel hF hx)) := by
      have hη : genericPoint (twoChartModel hF hx) ∈ ιFinite hF hx ''ᵁ ⊤ :=
        ((genericPoint_spec (twoChartModel hF hx)).mem_open_set_iff
          (ιFinite hF hx ''ᵁ ⊤).isOpen).mpr (by simpa using Set.Nonempty.of_subtype)
      rw [← (isAffineOpen_image_ιFinite_top hF hx).fromSpecStalk_eq_fromSpecStalk hη,
        IsAffineOpen.fromSpecStalk, fromSpec_isAffineOpen_image_ιFinite_top,
        ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      ext f
      apply e.injective
      -- Evaluate both composite ring maps at `f`: on the left `φ f` is `e⁻¹ f`, on the right the
      -- germ of the section corresponding to `f`.
      change e (e.symm (f : F)) = e ((twoChartModel hF hx).germToFunctionField _
        ((finiteChartSectionsEquiv hF hx).symm f))
      rw [functionFieldEquiv_germToFunctionField, AlgEquiv.apply_symm_apply,
        RingEquiv.apply_symm_apply]
    obtain ⟨y, hy, hyP⟩ := CodimensionOnePoint.exists_toPlace_eq_of_lift (coheight_le_one hxt)
      P _ hl
    rw [toPlace_eq_iff] at hyP
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm.trans (hy.symm.trans hyP)⟩

end TauCeti.AlgebraicGeometry.twoChartModel
