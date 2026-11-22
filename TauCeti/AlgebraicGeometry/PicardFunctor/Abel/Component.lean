/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.PicZero
public import TauCeti.AlgebraicGeometry.PicardFunctor.Component

/-!
# The Abel maps land in `Pic^d`

Let `f : X ⟶ S` be a smooth proper morphism of relative dimension one with geometrically
connected fibres. The Abel map `D ↦ 𝒪(D)` sends a relative effective Cartier divisor `D` of
degree `d` on `X_T = T ×_S X` to a class whose degree on the fibre over every point
`Spec Ω ⟶ T` is `d` (`relativePicardFiberDegree_abelMap_app_of_mem`). So, restricted to the
functor `Div^d_{X/S}` of divisors of degree `d`, it takes values in the degree-`d` subfunctor
`Pic^d_{X/S}` of the relative Picard presheaf (`abelMapOfDegree`). No section of `f` is needed,
in contrast to the normalized Abel–Jacobi maps `D ↦ 𝒪(D - d • x₀_T)` into `Pic⁰_{X/S}`
(`abelJacobiMapOfDegreeToPicZero`). The target of `abelMapOfDegree` is the presheaf `Pic^d_{X/S}`,
not a Picard scheme. The scheme-level Abel maps from the symmetric powers of a curve to the
components of its Picard scheme are induced by composing `abelMapOfDegree` with the comparison
from the relative Picard presheaf to the Picard sheaf, once `Div^d_{X/S}` is represented by the
symmetric power and the degree-`d` part of the Picard sheaf by a component of the Picard scheme.
Neither representability statement is treated here.

## Main declarations

* `TauCeti.AlgebraicGeometry.range_abelMap_le_relativePicardDegreeSubfunctor`: the Abel map on
  divisors of degree `d` lands in `Pic^d_{X/S}`;
* `TauCeti.AlgebraicGeometry.abelMapOfDegree`: the Abel map `Div^d_{X/S} ⟶ Pic^d_{X/S}`.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3 (the Abel maps `Div^d_{X/S} ⟶ Pic^d_{X/S}`).
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyConnected f]

/-- The image of the Abel map `D ↦ 𝒪(D)` on divisors of degree `d` lies in the degree-`d`
subfunctor `Pic^d_{X/S}` of the relative Picard presheaf. -/
theorem range_abelMap_le_relativePicardDegreeSubfunctor (d : ℕ) :
    Subfunctor.range
        (Functor.whiskerRight (relativeEffectiveCartierDegreeSubfunctor f d).ι
          uliftFunctor.{u + 1} ≫ abelMap f) ≤
      relativePicardDegreeSubfunctor f d := by
  rintro T _ ⟨⟨D⟩, rfl⟩
  exact (mem_relativePicardDegreeSubfunctor_obj_iff f).mpr fun _ _ _ ξ ↦
    relativePicardFiberDegree_abelMap_app_of_mem f ξ D.property

/-- **The Abel map of degree `d`**: the natural transformation from the functor `Div^d_{X/S}` of
relative effective Cartier divisors of degree `d` to the degree-`d` subfunctor `Pic^d_{X/S}` of the
relative Picard presheaf, sending `D` to the class of `𝒪(D)`. Followed by the inclusion of
`Pic^d_{X/S}` it is the Abel map on divisors of degree `d` (`abelMapOfDegree_ι`). -/
def abelMapOfDegree (d : ℕ) :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor ⋙ uliftFunctor.{u + 1} ⟶
      (relativePicardDegreeSubfunctor f d).toFunctor :=
  Subfunctor.lift _ (range_abelMap_le_relativePicardDegreeSubfunctor f d)

/-- The Abel map of degree `d` into `Pic^d_{X/S}`, followed by the inclusion of `Pic^d_{X/S}` into
the relative Picard presheaf, is the Abel map on divisors of degree `d`. -/
@[reassoc (attr := simp)]
theorem abelMapOfDegree_ι (d : ℕ) :
    abelMapOfDegree f d ≫ (relativePicardDegreeSubfunctor f d).ι =
      Functor.whiskerRight (relativeEffectiveCartierDegreeSubfunctor f d).ι
        uliftFunctor.{u + 1} ≫ abelMap f :=
  Subfunctor.lift_ι _ _

/-- The Abel map of degree `d` into `Pic^d_{X/S}` sends a divisor `D` of degree `d` to the class of
`𝒪(D)`, its value under the Abel map. -/
-- Not `@[simp]`: `simp` rewrites the type of the value by `Functor.comp_obj`, after which the
-- left-hand side no longer matches.
lemma abelMapOfDegree_app_apply_val (d : ℕ) {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    ((abelMapOfDegree f d).app T (ULift.up D)).val = (abelMap f).app T (ULift.up D.val) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
