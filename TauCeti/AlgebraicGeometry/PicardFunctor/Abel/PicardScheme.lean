/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.Jacobi
public import TauCeti.AlgebraicGeometry.PicardFunctor.Scheme

/-!
# The Abel morphism into the Picard scheme

Let `f : X ⟶ S` be a separated morphism of schemes which is smooth of relative dimension one,
such as a family of smooth curves. A `T`-point `x` of `X` over `S` has a graph `Γₓ ⊆ T ×_S X`,
a relative effective Cartier divisor, and hence a line bundle `𝒪(Γₓ)` on `T ×_S X`. Sending `x`
to the class of `𝒪(Γₓ)` in the relative Picard fppf sheaf is the composite of the graph divisor
and the Abel map `D ↦ 𝒪(D)` with fppf sheafification (`abelMapToPicFppf`). No section of `f` is
needed.

When the relative Picard fppf sheaf is representable, Yoneda turns this natural transformation
into the **Abel morphism** `abelMorphism f : X ⟶ Pic_{X/S}` of schemes over `S`, characterized by
`a(x) = [𝒪(Γₓ)]` on `T`-points for every `T`, nonreduced ones included
(`picardSchemeRepresentableBy_homEquiv_comp_abelMorphism`). If `f` has a section `x₀`, dividing
by the value at the base point `x₀_T` gives the Abel–Jacobi map `x ↦ [𝒪(Γₓ - x₀_T)]` on functors
of points (`picardSchemeRepresentableBy_homEquiv_comp_abelMorphism_div`).

For a smooth proper curve family the Abel morphism lands in the degree-one part of the Picard
scheme; the degree is not treated here.

## Main declarations

* `TauCeti.AlgebraicGeometry.abelMapToPicFppf`: the natural transformation `x ↦ [𝒪(Γₓ)]` from
  the functor of points of `X` to the relative Picard fppf sheaf;
* `TauCeti.AlgebraicGeometry.abelMorphism`: the Abel morphism `X ⟶ Pic_{X/S}`;
* `TauCeti.AlgebraicGeometry.picardSchemeRepresentableBy_homEquiv_comp_abelMorphism`: its value
  on `T`-points;
* `TauCeti.AlgebraicGeometry.picardSchemeRepresentableBy_homEquiv_comp_abelMorphism_div`: the
  comparison with the Abel–Jacobi map of a section.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3 (the Abel map); Definition 4.6 in the arXiv version,
  arXiv:math/0504020.
* V. Dimitrov, Z. Gao, P. Habegger, *Uniformity in Mordell–Lang for curves*, Annals of
  Mathematics 194 (2021), Section 6.1 (the Abel map of a family of curves without a section).
-/

public section

open CategoryTheory Limits Opposite MonObj

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [SmoothOfRelativeDimension 1 f]

variable {f} in
/-- The class of the line bundle `𝒪(Γₓ)` on `T ×_S X` of the graph of a `T`-point `x`. -/
private def graphClass {T : Over S} (x : T ⟶ Over.mk f) : LineBundleClass (pullback T.hom f) :=
  (LineBundleClass.mk (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension _
    (graphSection_fst x)).isEffectiveCartier.toInvertibleSheaf)⁻¹

variable {f} in
/-- The Abel map sends the graph divisor of `x` to the class of `𝒪(Γₓ)`. -/
private lemma abelMap_app_graphDivisor {T : Over S} (x : T ⟶ Over.mk f) :
    (abelMap f).app (op T) (ULift.up ((graphDivisor f).app (op T) x)) =
      (QuotientGroup.mk (graphClass x) : (relativePicardPresheaf f).obj (op T)) := by
  rw [abelMap_app_apply, graphClass]
  congr 4
  exact graphDivisor_app_apply_val x

/-- **The Abel map on points**: the natural transformation from the functor of points of `X`
over `S` to the relative Picard fppf sheaf sending a `T`-point `x` to the class of the line
bundle `𝒪(Γₓ)` of its graph (`abelMapToPicFppf_app_apply`). It is the graph divisor followed by
the Abel map `D ↦ 𝒪(D)` and fppf sheafification, and needs no section of `f`. -/
def abelMapToPicFppf : yoneda.obj (Over.mk f) ⋙ uliftFunctor.{u + 1} ⟶
    (relativePicardFppfSheaf f).obj ⋙ forget AddCommGrpCat :=
  Functor.whiskerRight (graphDivisor f) uliftFunctor.{u + 1} ≫ abelMap f ≫
    relativePicardToFppfSheafOfMul f

/-- The Abel map on points is the graph divisor, followed by the Abel map `D ↦ 𝒪(D)` and the
canonical map to the relative Picard fppf sheaf. -/
theorem abelMapToPicFppf_eq :
    abelMapToPicFppf f = Functor.whiskerRight (graphDivisor f) uliftFunctor.{u + 1} ≫
      abelMap f ≫ relativePicardToFppfSheafOfMul f :=
  (rfl)

variable {f} in
/-- The Abel map on points sends a `T`-point `x` to the image in the relative Picard fppf sheaf
of the Abel map at the graph divisor of `x`. -/
theorem abelMapToPicFppf_app_eq_relativePicardToFppfSheafOfMul {T : Over S}
    (x : T ⟶ Over.mk f) :
    (abelMapToPicFppf f).app (op T) (ULift.up x) =
      (relativePicardToFppfSheafOfMul f).app (op T)
        ((abelMap f).app (op T) (ULift.up ((graphDivisor f).app (op T) x))) :=
  (rfl)

variable {f} in
private lemma abelMapToPicFppf_app_graphClass {T : Over S} (x : T ⟶ Over.mk f) :
    (abelMapToPicFppf f).app (op T) (ULift.up x) =
      (relativePicardToFppfSheaf f).app (op T)
        (relativePicardAddPresheafMk f (op T) (graphClass x)) := by
  rw [abelMapToPicFppf_app_eq_relativePicardToFppfSheafOfMul, abelMap_app_graphDivisor,
    relativePicardToFppfSheafOfMul_app_mk]

-- The source and target of `(abelMapToPicFppf f).app (op T)` are spelled out in their
-- simp-normal form, so that the left-hand side passes the `simpNF` linter.
/-- The Abel map on points sends a `T`-point `x` to the class of `𝒪(Γₓ)`, the dual of the ideal
sheaf of the graph of `x`, in the relative Picard fppf sheaf. -/
@[simp]
lemma abelMapToPicFppf_app_apply {T : Over S} (x : T ⟶ Over.mk f) :
    ConcreteCategory.hom (C := Type (u + 1)) (X := ULift.{u + 1} (T ⟶ Over.mk f))
      (Y := ToType ((relativePicardFppfSheaf f).obj.obj (op T)))
      ((abelMapToPicFppf f).app (op T)) (ULift.up x) =
      (relativePicardToFppfSheaf f).app (op T) (relativePicardAddPresheafMk f (op T)
        (LineBundleClass.mk
          (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension _
            (graphSection_fst x)).isEffectiveCartier.toInvertibleSheaf)⁻¹) :=
  abelMapToPicFppf_app_graphClass x

variable [HasPicardScheme f]

/-- **The Abel morphism** `X ⟶ Pic_{X/S}` of a separated morphism `f : X ⟶ S` which is smooth of
relative dimension one and has a Picard scheme: the morphism of schemes over `S` representing
the Abel map on points `x ↦ [𝒪(Γₓ)]` (`picardSchemeRepresentableBy_homEquiv_comp_abelMorphism`).
No section of `f` is needed. -/
def abelMorphism : Over.mk f ⟶ picardScheme f :=
  (picardSchemeRepresentableBy f).homEquiv.symm ((abelMapToPicFppf f).app (op (Over.mk f)) ⟨𝟙 _⟩)

/-- The Abel morphism corresponds to the class of the diagonal, the graph of the identity point
of `X`. -/
lemma picardSchemeRepresentableBy_homEquiv_abelMorphism :
    (picardSchemeRepresentableBy f).homEquiv (abelMorphism f) =
      (abelMapToPicFppf f).app (op (Over.mk f)) ⟨𝟙 _⟩ := by
  rw [abelMorphism, Equiv.apply_symm_apply]

/-- **The Abel morphism on `T`-points**: for every scheme `T` over `S` and every `T`-point `x` of
`X`, the composite `x ≫ abelMorphism f` is the class of `𝒪(Γₓ)` in the relative Picard fppf
sheaf. -/
lemma picardSchemeRepresentableBy_homEquiv_comp_abelMorphism {T : Over S}
    (x : T ⟶ Over.mk f) :
    (picardSchemeRepresentableBy f).homEquiv (x ≫ abelMorphism f) =
      (abelMapToPicFppf f).app (op T) ⟨x⟩ := by
  rw [Functor.RepresentableBy.homEquiv_comp, picardSchemeRepresentableBy_homEquiv_abelMorphism]
  refine (ConcreteCategory.congr_hom ((abelMapToPicFppf f).naturality x.op) ⟨𝟙 _⟩).symm.trans ?_
  simp

/-- The Abel morphism represents the Abel map on points: under the representing isomorphism of
the Picard scheme, composition with `abelMorphism f` is `abelMapToPicFppf f`. -/
lemma uliftYoneda_map_abelMorphism_comp_picardSchemeIso_hom :
    uliftYoneda.{u + 1}.map (abelMorphism f) ≫ (picardSchemeIso f).hom = abelMapToPicFppf f := by
  ext T ⟨x⟩
  exact (picardSchemeIso_hom_app f T ⟨x ≫ abelMorphism f⟩).trans
    (picardSchemeRepresentableBy_homEquiv_comp_abelMorphism f x)

/-- **The Abel morphism and the Abel–Jacobi map.** If `f` has a section `x₀`, then for every
`T`-point `x` of `X`, the quotient of `x ≫ abelMorphism f` by the value of the Abel morphism at
the base point `x₀_T` is the image in the relative Picard fppf sheaf of the Abel–Jacobi class
`𝒪(Γₓ - x₀_T)` of `x`. -/
theorem picardSchemeRepresentableBy_homEquiv_comp_abelMorphism_div {x₀ : S ⟶ X}
    (hx₀ : x₀ ≫ f = 𝟙 S) {T : Over S} (x : T ⟶ Over.mk f) :
    (picardSchemeRepresentableBy f).homEquiv
        ((x ≫ abelMorphism f) / (basePoint hx₀ T ≫ abelMorphism f)) =
      (relativePicardToFppfSheafOfMul f).app (op T) ((abelJacobiMap f hx₀).app (op T) ⟨x⟩) := by
  rw [picardSchemeRepresentableBy_homEquiv_div,
    picardSchemeRepresentableBy_homEquiv_comp_abelMorphism,
    picardSchemeRepresentableBy_homEquiv_comp_abelMorphism,
    abelMapToPicFppf_app_eq_relativePicardToFppfSheafOfMul,
    abelMapToPicFppf_app_eq_relativePicardToFppfSheafOfMul, abelJacobiMap_app_apply,
    relativePicardToFppfSheafOfMul_app_div]

end

end TauCeti.AlgebraicGeometry
