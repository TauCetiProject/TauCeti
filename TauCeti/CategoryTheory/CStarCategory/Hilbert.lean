/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.InnerProductSpace.Category
public import TauCeti.CategoryTheory.CStarCategory.Functor

/-!
# Hilbert spaces and finite-dimensional Hilbert spaces as C*-categories

Complex Hilbert spaces `TauCeti.HilbertCat ℂ` form the archetypal C*-category, with bounded
linear operators `X →L[ℂ] Y` as Hom spaces, operator composition, operator norm, and Hilbert-space
adjoint as dagger. Because `CStarCategory` reuses the existing `Preadditive` and `Linear ℂ`
structures and defaults to the ambient operator norm and metric, the `NormedAddCommGroup` and
`NormedSpace ℂ` instances induced by `CStarCategory` on `X ⟶ Y` are definitionally equal to those
of `X →L[ℂ] Y`.

Using operator-order multiplication on `CategoryTheory.End X`, the endomorphism C*-algebra `End X`
is canonically `⋆`-isomorphic, isometric, and order-isomorphic to `X →L[ℂ] X` (matching its
spectral order with the Loewner inner-product order). The full subcategory `TauCeti.FDHilbertCat ℂ`
of finite-dimensional complex Hilbert spaces inherits its `CStarCategory` structure automatically
via `CategoryTheory.ObjectProperty.instCStarCategoryFullSubcategory`, with explicit zero-object
(`PUnit`, `‖𝟙 _‖ = 0`) and nontrivial (`ℂ`, `‖𝟙 _‖ = 1`) behavior.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory

universe v

namespace TauCeti

namespace HilbertCat

/-- Complex Hilbert spaces and continuous linear maps form a C*-category. -/
instance instCStarCategory : CStarCategory (HilbertCat.{0, v} ℂ) where
  dist_eq f g := SeminormedAddCommGroup.dist_eq f g
  norm_comp_le f g := ContinuousLinearMap.opNorm_comp_le g f
  norm_comp_dagger_self f := by
    rw [sq]
    exact ContinuousLinearMap.norm_adjoint_comp_self f
  exists_comp_dagger_eq {X Y} f := by
    have hpos : (0 : X →L[ℂ] X) ≤ (ContinuousLinearMap.adjoint f).comp f :=
      ContinuousLinearMap.le_def.mpr
        (by simpa using ContinuousLinearMap.isPositive_adjoint_comp_self f)
    obtain ⟨g, hg⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
    exact ⟨g, hg⟩

-- Verify that `CStarCategory`'s Hom-space normed instances match `X →L[ℂ] Y` definitionally.
example (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.homNormedAddCommGroup X Y =
      inferInstanceAs (NormedAddCommGroup (X →L[ℂ] Y)) := rfl

example (X Y : HilbertCat.{0, v} ℂ) :
    CStarCategory.homNormedSpace X Y =
      inferInstanceAs (NormedSpace ℂ (X →L[ℂ] Y)) := rfl

/-- `HilbertCat.endStarAlgEquiv` is norm-preserving on `End X`. -/
theorem norm_endStarAlgEquiv (X : HilbertCat.{0, v} ℂ) (a : End X) :
    ‖X.endStarAlgEquiv a‖ = ‖a‖ := by
  rw [endStarAlgEquiv_apply, End.norm_asHom]

/-- `HilbertCat.endStarAlgEquiv` identifies the spectral order on `End X` with the Loewner
inner-product order on `X →L[ℂ] X`. -/
theorem endStarAlgEquiv_le_iff (X : HilbertCat.{0, v} ℂ) {a b : End X} :
    X.endStarAlgEquiv a ≤ X.endStarAlgEquiv b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff X.endStarAlgEquiv.toStarAlgHom X.endStarAlgEquiv.injective

/-- `HilbertCat.endStarAlgEquiv` identifies positivity in `End X` with operator positivity on
`X →L[ℂ] X`. -/
theorem endStarAlgEquiv_nonneg_iff (X : HilbertCat.{0, v} ℂ) {a : End X} :
    0 ≤ X.endStarAlgEquiv a ↔ 0 ≤ a := by
  simpa only [map_zero] using X.endStarAlgEquiv_le_iff (a := 0) (b := a)

/-- The identity arrow of a subsingleton complex Hilbert space has norm `0`. -/
@[simp] theorem norm_id_of_subsingleton (X : HilbertCat.{0, v} ℂ) [Subsingleton X] :
    ‖(𝟙 X : X ⟶ X)‖ = 0 :=
  (isZero_of_subsingleton X).norm_id

/-- The identity arrow of a nontrivial complex Hilbert space has norm `1`. -/
@[simp] theorem norm_id_of_nontrivial (X : HilbertCat.{0, v} ℂ) [Nontrivial X] :
    ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  (CStarCategory.not_isZero_iff_norm_id_eq_one X).mp (not_isZero_of_nontrivial X)

end HilbertCat

namespace FDHilbertCat

-- `FDHilbertCat ℂ` inherits `CStarCategory` automatically as a full subcategory of `HilbertCat ℂ`.
example : CStarCategory (FDHilbertCat.{0, v} ℂ) := inferInstance

/-- `FDHilbertCat.endStarAlgEquiv` preserves norms on endomorphisms. -/
theorem norm_endStarAlgEquiv (X : FDHilbertCat.{0, v} ℂ) (a : End X) :
    ‖X.endStarAlgEquiv a‖ = ‖a‖ :=
  StarAlgEquiv.norm_map X.endStarAlgEquiv a

/-- `FDHilbertCat.endStarAlgEquiv` identifies the spectral order on `End X` with the Loewner order
on `X →L[ℂ] X`. -/
theorem endStarAlgEquiv_le_iff (X : FDHilbertCat.{0, v} ℂ) {a b : End X} :
    X.endStarAlgEquiv a ≤ X.endStarAlgEquiv b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff X.endStarAlgEquiv.toStarAlgHom X.endStarAlgEquiv.injective

/-- In `FDHilbertCat ℂ`, a subsingleton Hilbert space (such as `FDHilbertCat.of ℂ PUnit`) has
identity arrow of norm `0`. -/
@[simp] theorem norm_id_of_subsingleton (X : FDHilbertCat.{0, v} ℂ) [Subsingleton X] :
    ‖(𝟙 X : X ⟶ X)‖ = 0 :=
  (isZero_of_subsingleton X).norm_id

/-- In `FDHilbertCat ℂ`, a nontrivial Hilbert space (such as `FDHilbertCat.of ℂ ℂ`) has identity
arrow of norm `1`. -/
@[simp] theorem norm_id_of_nontrivial (X : FDHilbertCat.{0, v} ℂ) [Nontrivial X] :
    ‖(𝟙 X : X ⟶ X)‖ = 1 :=
  (CStarCategory.not_isZero_iff_norm_id_eq_one X).mp (not_isZero_of_nontrivial X)

-- Explicit zero-object (`PUnit`) vs nontrivial-object (`ℂ`) norm checks in `FDHilbertCat ℂ`.
example : ‖(𝟙 (FDHilbertCat.of ℂ PUnit.{v + 1}))‖ = 0 :=
  norm_id_of_subsingleton (FDHilbertCat.of ℂ PUnit.{v + 1})

example : ‖(𝟙 (FDHilbertCat.of ℂ ℂ))‖ = 1 :=
  norm_id_of_nontrivial (FDHilbertCat.of ℂ ℂ)

end FDHilbertCat

end TauCeti
