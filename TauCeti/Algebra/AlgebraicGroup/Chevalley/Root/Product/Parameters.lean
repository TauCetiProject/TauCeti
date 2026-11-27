/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Product.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import TauCeti.AlgebraicGeometry.Scheme.AffinePoints

/-!
# Polynomial coordinates on root-product parameters

The product of additive-group schemes used to parameterize an ordered root product is
canonically the spectrum of the polynomial ring with one variable for each occurring root.
The universal point sends its variables to the corresponding additive coordinates.
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (l : List (Fin t.numRoots))

/-- The universal polynomial point of the parameter scheme of a root product. -/
def rootProductParametersPoint :
    (Spec (CommRingCat.of (MvPolynomial {γ // γ ∈ l} ℤ))).asOver
      (Spec (CommRingCat.of ℤ)) ⟶ t.rootProductParameters l :=
  Pi.lift fun γ ↦ (AdditiveGroup.schemePointsMulEquiv _).symm
    (Multiplicative.ofAdd (MvPolynomial.X γ))

/-- Each additive coordinate of the universal parameter point is the corresponding variable. -/
@[simp]
theorem rootProductParametersPoint_coordinate (γ : {γ // γ ∈ l}) :
    AdditiveGroup.schemePointsMulEquiv _ (t.rootProductParametersPoint l ≫
      Pi.π (fun _ : {γ // γ ∈ l} ↦ (AdditiveGroup.groupScheme ℤ).X) γ) =
        Multiplicative.ofAdd (MvPolynomial.X γ) := by
  simp [rootProductParametersPoint]

/-- After a map of coefficient rings, the universal parameter coordinates evaluate at the
images of the polynomial variables. -/
theorem rootProductParametersPoint_map_coordinate
    {A : Type} [CommRing A] (φ : MvPolynomial {γ // γ ∈ l} ℤ →ₐ[ℤ] A)
    (γ : {γ // γ ∈ l}) :
    AdditiveGroup.schemePointsMulEquiv A
      ((Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver (Spec (CommRingCat.of ℤ)) ≫
        t.rootProductParametersPoint l ≫
          Pi.π (fun _ : {γ // γ ∈ l} ↦ (AdditiveGroup.groupScheme ℤ).X) γ) =
      Multiplicative.ofAdd (φ (MvPolynomial.X γ)) := by
  rw [AdditiveGroup.schemePointsMulEquiv_mapValue, rootProductParametersPoint_coordinate]
  rfl

/-- The universal polynomial point identifies the root-product parameter scheme with an
affine space over `ℤ`. -/
instance isIso_rootProductParametersPoint_left : IsIso (t.rootProductParametersPoint l).left := by
  apply Scheme.isIso_of_forall_spec_bijective
  intro A
  constructor
  · intro a b hab
    obtain ⟨φ, rfl⟩ := Spec.map_surjective a
    obtain ⟨ψ, rfl⟩ := Spec.map_surjective b
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro γ
      let φ' := φ.hom.toIntAlgHom
      let ψ' := ψ.hom.toIntAlgHom
      have : (Spec.map (CommRingCat.ofHom φ'.toRingHom)).IsOver
          (Spec (CommRingCat.of ℤ)) := ⟨specZIsTerminal.hom_ext _ _⟩
      have : (Spec.map (CommRingCat.ofHom ψ'.toRingHom)).IsOver
          (Spec (CommRingCat.of ℤ)) := ⟨specZIsTerminal.hom_ext _ _⟩
      have hab' : (Spec.map (CommRingCat.ofHom φ'.toRingHom)).asOver (Spec (CommRingCat.of ℤ)) ≫
          t.rootProductParametersPoint l =
          (Spec.map (CommRingCat.ofHom ψ'.toRingHom)).asOver (Spec (CommRingCat.of ℤ)) ≫
            t.rootProductParametersPoint l := Over.OverMorphism.ext hab
      have hc := congrArg (fun p ↦ AdditiveGroup.schemePointsMulEquiv A
        (p ≫ Pi.π (fun _ : {γ // γ ∈ l} ↦ (AdditiveGroup.groupScheme ℤ).X) γ)) hab'
      have hφ := t.rootProductParametersPoint_map_coordinate l φ' γ
      have hψ := t.rootProductParametersPoint_map_coordinate l ψ' γ
      simp only [Category.assoc] at hc
      exact congrArg Multiplicative.toAdd (hφ.symm.trans (hc.trans hψ))
  · intro p
    let p' : (Spec A).asOver (Spec (CommRingCat.of ℤ)) ⟶ t.rootProductParameters l :=
      Over.homMk p (specZIsTerminal.hom_ext _ _)
    let v (γ : {γ // γ ∈ l}) := Multiplicative.toAdd
      (AdditiveGroup.schemePointsMulEquiv A
        (p' ≫ Pi.π (fun _ : {γ // γ ∈ l} ↦ (AdditiveGroup.groupScheme ℤ).X) γ))
    let φ : MvPolynomial {γ // γ ∈ l} ℤ →ₐ[ℤ] A := MvPolynomial.aeval v
    refine ⟨Spec.map (CommRingCat.ofHom φ.toRingHom), ?_⟩
    have hp : (Spec.map (CommRingCat.ofHom φ.toRingHom)).asOver
        (Spec (CommRingCat.of ℤ)) ≫ t.rootProductParametersPoint l = p' := by
      apply Pi.hom_ext
      intro γ
      apply (AdditiveGroup.schemePointsMulEquiv A).injective
      rw [Category.assoc, rootProductParametersPoint_map_coordinate]
      simp only [φ, MvPolynomial.aeval_X, v, ofAdd_toAdd]
    exact congrArg (fun z ↦ z.left) hp

/-- The universal polynomial point is an isomorphism over `Spec ℤ`. -/
instance isIso_rootProductParametersPoint : IsIso (t.rootProductParametersPoint l) := by
  have : IsIso ((Over.forget (Spec (CommRingCat.of ℤ))).map
      (t.rootProductParametersPoint l)) := t.isIso_rootProductParametersPoint_left l
  exact isIso_of_reflects_iso _ (Over.forget _)

/-- The parameter scheme of an ordered root product is affine. -/
instance isAffine_rootProductParameters : IsAffine (t.rootProductParameters l).left := by
  have : IsAffine ((Spec (CommRingCat.of (MvPolynomial {γ // γ ∈ l} ℤ))).asOver
      (Spec (CommRingCat.of ℤ))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial {γ // γ ∈ l} ℤ))))
  exact .of_isIso (inv (t.rootProductParametersPoint l).left)

/-- The coordinate ring of the root-product parameter scheme is the polynomial ring over
`ℤ`, indexed by the roots occurring in the list. -/
def rootProductParametersCoordinateRingIso :
    Γ((t.rootProductParameters l).left, ⊤) ≅
      CommRingCat.of (MvPolynomial {γ // γ ∈ l} ℤ) :=
  Scheme.Γ.mapIso (asIso (t.rootProductParametersPoint l).left).op ≪≫ Scheme.ΓSpecIso _

/-- The coordinate-ring identification is pullback along the universal parameter point,
followed by the global-sections identification for a spectrum. -/
@[simp]
theorem rootProductParametersCoordinateRingIso_hom :
    (t.rootProductParametersCoordinateRingIso l).hom =
      (t.rootProductParametersPoint l).left.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial {γ // γ ∈ l} ℤ))).hom :=
  (rfl)

end

end TauCeti.DynkinType
