/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category.Symmetry
public import TauCeti.CategoryTheory.Dagger.Basic
import Mathlib.LinearAlgebra.Basis.Bilinear

/-!
# The vertical reflection dagger on the linear Temperley–Lieb category

* `TauCeti.TLCat.verticalReflectHom_comp` lifts `TauCeti.TLDiagram.verticalReflect_comp`
  to compositions of linear combinations of diagrams.
* `TauCeti.TLCat.instDaggerCategory` and `TauCeti.TLCat.instDaggerPreadditive` give the additive
  vertical reflection dagger. The instances on Mathlib's `CategoryTheory.End` then make each
  endomorphism algebra a star ring.

The dagger uses `TauCeti.TLCat.verticalReflectHom`, which fixes the coefficients.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845,
  Definition 2.1.5 for the underlying reflection of diagrams.
-/

public section

open CategoryTheory

namespace TauCeti.TLCat

variable {R : Type*} [CommRing R] {δ : R}

/-- Vertical reflection reverses composition of linear Temperley–Lieb morphisms.
The underlying diagram reflection is Chen, Definition 2.1.5. -/
theorem verticalReflectHom_comp {n m p : ℕ}
    (f : (of n : TLCat R δ) ⟶ of m) (g : (of m : TLCat R δ) ⟶ of p) :
    verticalReflectHom n p (f ≫ g) =
      verticalReflectHom m p g ≫ verticalReflectHom n m f := by
  let X : TLCat R δ := of n
  let Y : TLCat R δ := of m
  let Z : TLCat R δ := of p
  -- Compare the two bilinear maps on the images of diagrams without circles.
  let reflectAfter := (Linear.comp (S := R) X Y Z).compr₂
    (verticalReflectHom n p).toLinearMap
  let reflectBefore := (Linear.comp (S := R) Z Y X).flip.compl₁₂
    (verticalReflectHom n m).toLinearMap (verticalReflectHom m p).toLinearMap
  suffices h : reflectAfter = reflectBefore from LinearMap.ext_iff₂.mp h f g
  apply LinearMap.ext_basis (diagBasis X Y) (diagBasis Y Z)
  intro x y
  simp only [reflectAfter, reflectBefore, LinearMap.compr₂_apply, LinearMap.compl₁₂_apply,
    LinearMap.flip_apply, Linear.comp_apply, Linear.leftComp_apply, LinearEquiv.coe_coe]
  let dx : TLDiagCat.of n ⟶ TLDiagCat.of m := TLDiagCat.Hom.mk ⟨x, 0⟩
  let dy : TLDiagCat.of m ⟶ TLDiagCat.of p := TLDiagCat.Hom.mk ⟨y, 0⟩
  have hx : (linearize R δ).map dx = diagBasis X Y x := by
    simp only [dx, linearize_map_mk, pow_zero, one_smul]
  have hy : (linearize R δ).map dy = diagBasis Y Z y := by
    simp only [dy, linearize_map_mk, pow_zero, one_smul]
  rw [← hx, ← hy, ← Functor.map_comp]
  -- Compare the two reflected stacks before linearizing.
  rw [verticalReflectHom_linearize_map, verticalReflectHom_linearize_map,
    verticalReflectHom_linearize_map, ← Functor.map_comp]
  refine congrArg (linearize R δ).map (TLDiagCat.hom_ext ?_)
  simp only [TLDiagCat.diagram_comp, TLDiagram.verticalReflect_comp]

/-- Turning diagrams upside down is an identity-on-objects contravariant involution. -/
noncomputable instance instDaggerCategory : DaggerCategory (TLCat R δ) where
  dagger := fun {X Y} => verticalReflectHom X.as Y.as
  dagger_id X := verticalReflectHom_id X.as
  dagger_comp f g := verticalReflectHom_comp f g
  dagger_dagger f := verticalReflectHom_verticalReflectHom _ _ f

/-- Computation rule for the dagger instance on strand-number objects, exposing its value
as the linear vertical reflection equivalence for use with the diagram-basis API. -/
@[simp]
theorem dagger_eq_verticalReflectHom {n m : ℕ} (f : (of n : TLCat R δ) ⟶ of m) :
    dagger f = verticalReflectHom n m f := (rfl)

/-- Vertical reflection is additive, so composition and the dagger give a star ring on each
endomorphism algebra. -/
instance instDaggerPreadditive : DaggerPreadditive (TLCat R δ) where
  dagger_add {X Y} f g := (verticalReflectHom X.as Y.as).map_add f g

/-- Vertical reflection leaves scalars unchanged. -/
theorem dagger_smul_eq_smul_dagger {X Y : TLCat R δ} (r : R) (f : X ⟶ Y) :
    dagger (r • f) = r • dagger f :=
  (verticalReflectHom X.as Y.as).map_smul r f

/-- With trivial scalar star, vertical reflection is compatible with the scalar involution. -/
instance instDaggerLinear [Star R] [TrivialStar R] : DaggerLinear R (TLCat R δ) where
  dagger_smul r f := by rw [star_trivial, dagger_smul_eq_smul_dagger]

/-- The diagram algebra star commutes with multiplication by any coefficient. -/
@[simp]
theorem star_smul_end (X : TLCat R δ) (r : R) (x : End X) :
    star (r • x) = r • star x := by
  ext
  simp only [End.star_asHom, End.smul_asHom, dagger_smul_eq_smul_dagger]

end TauCeti.TLCat
