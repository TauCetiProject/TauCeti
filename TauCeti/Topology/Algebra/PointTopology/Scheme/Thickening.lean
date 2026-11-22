/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.PointTopology.Scheme.Reduction
public import TauCeti.AlgebraicGeometry.Morphisms.Thickening

/-!
# Thickenings on scheme-valued points

A thickening `i : Z ⟶ X` over `Spec k`, that is, a surjective closed immersion, is bijective
on `R`-points when the coefficient ring `R` is reduced: a point `Spec R ⟶ X` kills the
nilpotent sections of `X`, hence the ideal sheaf of `i`, and so lifts uniquely along `i`. A
thickening induces a homeomorphism of point spaces over a reduced local coefficient ring with
continuous multiplication, open units and continuous inversion on its units, such as `ℂ`.
Indeed, the lift of points along `i` is the lift to the reduction `X.nilradical.subscheme`,
which is continuous, followed by the map induced by the lift of `X.nilradical.subschemeι`
along `i`.

This generalises the reduction `X.nilradical.subscheme ⟶ X`, a thickening, for which
`TauCeti.SchemePointTopology.reductionHomeomorph` gives the homeomorphism of points directly.
No finiteness or separation hypothesis on the schemes is needed. Reducedness of `R` is
needed: over the dual numbers `R = ℂ[ε]/(ε²)`, the identity of `Spec R` is an `R`-point of
`Spec R` which does not factor through its reduction `Spec ℂ`.

## Main results

* `TauCeti.SchemePointTopology.map_bijective_of_isThickening`: a thickening is bijective on
  points with reduced coefficients.
* `TauCeti.SchemePointTopology.isHomeomorph_map_of_isThickening` and
  `TauCeti.SchemePointTopology.homeomorphOfIsThickening`: it is a homeomorphism on points.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII, §1.1 and
  Proposition 2.1, pp. 239–242.
* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Prop. 3.1, pp. 3–4.
-/

public section

open CategoryTheory AlgebraicGeometry Topology
open scoped TauCeti.PointTopology TauCeti.SchemePointTopology

universe u

namespace TauCeti.SchemePointTopology

open TauCeti.AlgebraicGeometry

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [_root_.IsReduced R]
  {X Z : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fZ : Z ⟶ Spec (.of k)}

/-- The lift of a point along a thickening, for reduced coefficients. -/
noncomputable def liftOfIsThickening (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i]
    (x : Points (R := R) fX) : Points (R := R) fZ :=
  ⟨IsClosedImmersion.lift i x.val (IsThickening.ker_le_ker i x.val), by
    rw [← hi, ← Category.assoc, IsClosedImmersion.lift_fac, x.property]⟩

/-- The lift of a point along a thickening composes with the thickening to the point. -/
@[simp]
theorem liftOfIsThickening_val_comp (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i]
    (x : Points (R := R) fX) : (liftOfIsThickening i hi x).val ≫ i = x.val :=
  IsClosedImmersion.lift_fac _ _ _

/-- The lift along a thickening is a right inverse of the induced map on points. -/
@[simp]
theorem map_liftOfIsThickening (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i]
    (x : Points (R := R) fX) : map i hi (liftOfIsThickening i hi x) = x :=
  Subtype.ext ((map_val i hi _).trans (liftOfIsThickening_val_comp i hi x))

/-- The lift along a thickening is a left inverse of the induced map on points. -/
@[simp]
theorem liftOfIsThickening_map (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i]
    (z : Points (R := R) fZ) : liftOfIsThickening i hi (map i hi z) = z :=
  map_injective i hi (map_liftOfIsThickening i hi _)

/-- A thickening over the base is bijective on points with reduced coefficients. No topology,
locality or finiteness is involved. -/
theorem map_bijective_of_isThickening (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i] :
    Function.Bijective (map (R := R) i hi) :=
  ⟨map_injective i hi, fun x ↦ ⟨liftOfIsThickening i hi x, map_liftOfIsThickening i hi x⟩⟩

/-- The lift along a thickening factors as the lift to the reduction of the target followed by
the map induced by the lift of the reduction along the thickening. -/
private theorem liftOfIsThickening_eq_comp (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i] :
    ∃ (j : X.nilradical.subscheme ⟶ Z) (hj : j ≫ fZ = X.nilradical.subschemeι ≫ fX),
      liftOfIsThickening (R := R) i hi = map j hj ∘ reductionLift fX := by
  let j := IsClosedImmersion.lift i X.nilradical.subschemeι
    (IsThickening.ker_le_ker i X.nilradical.subschemeι)
  have hj : j ≫ i = X.nilradical.subschemeι := IsClosedImmersion.lift_fac _ _ _
  refine ⟨j, by rw [← hi, ← Category.assoc, hj], funext fun x ↦ map_injective i hi ?_⟩
  refine Subtype.ext ?_
  rw [map_liftOfIsThickening, Function.comp_apply, map_val, map_val, Category.assoc, hj,
    reductionLift_val_subschemeι]

variable [TopologicalSpace R] [ContinuousMul R] [IsLocalRing R] [IsOpenUnits R]

/-- Over a reduced local topological ring with open units and continuous inversion on its
units, the lift of points along a thickening over the base is continuous. -/
@[continuity, fun_prop]
theorem continuous_liftOfIsThickening (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i] :
    Continuous (liftOfIsThickening (R := R) i hi) := by
  obtain ⟨j, hj, h⟩ := liftOfIsThickening_eq_comp (R := R) i hi
  rw [h]
  exact (continuous_map j hj).comp (continuous_reductionLift fX)

/-- The homeomorphism of point spaces induced by a thickening over the base, with inverse the
lift of points along the thickening, over a reduced local topological ring with open units and
continuous inversion on its units. -/
noncomputable def homeomorphOfIsThickening (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i] :
    Points (R := R) fZ ≃ₜ Points (R := R) fX where
  toFun := map i hi
  invFun := liftOfIsThickening i hi
  left_inv := liftOfIsThickening_map i hi
  right_inv := map_liftOfIsThickening i hi
  continuous_toFun := continuous_map i hi
  continuous_invFun := continuous_liftOfIsThickening i hi

/-- A thickening over the base is a homeomorphism on points over a reduced local topological
ring with open units and continuous inversion on its units. -/
theorem isHomeomorph_map_of_isThickening (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i] :
    IsHomeomorph (map (R := R) i hi) :=
  (homeomorphOfIsThickening i hi).isHomeomorph

/-- The homeomorphism induced by a thickening is the induced map on points. -/
@[simp]
theorem homeomorphOfIsThickening_apply (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i]
    (z : Points (R := R) fZ) : homeomorphOfIsThickening i hi z = map i hi z :=
  (rfl)

/-- The inverse of the homeomorphism induced by a thickening lifts points along it. -/
@[simp]
theorem homeomorphOfIsThickening_symm_apply (i : Z ⟶ X) (hi : i ≫ fX = fZ) [IsThickening i]
    (x : Points (R := R) fX) :
    (homeomorphOfIsThickening i hi).symm x = liftOfIsThickening i hi x :=
  (rfl)

end TauCeti.SchemePointTopology
