/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselian.Strict
public import TauCeti.RingTheory.StrictHenselization.Lift
import TauCeti.RingTheory.StrictHenselization.Map

/-!
# Pointed étale colimits over henselian local rings

For a henselian local ring `R`, the colimit of étale neighbourhoods pointed in its residue
field is `R` itself. More generally, the same holds when the pointing algebra is identified
with the residue field as an `R`-algebra. The inverse to the structure map is the unique
henselian lift of that identification.

In particular, if `R` is strictly henselian, any separable algebraic extension `Ω` of its residue
field (such as a separable closure) is canonically isomorphic to `ResidueField R`, so its strict
henselization `algebra R Ω` is canonically isomorphic to `R`
(`algEquivOfIsStrictlyHenselianLocalRing`). No separable-closedness assumption is needed for the
more general pointed-colimit statement `algEquivOfResidueFieldEquiv`: pointing in the residue
field, rather than a larger separable closure, is what drives the equivalence.

## References

* Stacks Project, Tags 04GP, 04GQ and 08HQ.
* `TauCeti.StrictHenselization.lift` supplies the stagewise henselian lifts;
  `TauCeti.StrictHenselization.map_unique` supplies uniqueness of pointed-colimit maps.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

section Henselian

variable (R Ω : Type u) [CommRing R] [HenselianLocalRing R] [CommRing Ω] [Algebra R Ω]

/-- The henselian lift of a residue-field identification is also a right inverse to the
structure map. Thus no additional pointed étale elements are introduced. -/
@[simp]
theorem algebraMap_lift_residueFieldEquiv (e : Ω ≃ₐ[R] ResidueField R) (x : algebra R Ω) :
    algebraMap R (algebra R Ω) (lift R Ω e.toAlgHom x) = x := by
  have hpoint : (toTarget R Ω).toRingHom.comp
      ((Algebra.ofId R (algebra R Ω)).comp (lift R Ω e.toAlgHom)).toRingHom =
        (RingHom.id Ω).comp (toTarget R Ω).toRingHom := by
    ext y
    apply e.injective
    simp [ResidueField.algebraMap_eq]
  have h := map_unique (RingHom.id R) (RingHom.id Ω) (by simp)
    ((Algebra.ofId R (algebra R Ω)).comp (lift R Ω e.toAlgHom)).toRingHom
    (by ext r; simp) hpoint
  simpa using DFunLike.congr_fun h x

/-- The pointed étale colimit over a henselian local ring is the base ring when its pointing
algebra is identified with the base residue field. For a strictly henselian ring, see
`algEquivOfIsStrictlyHenselianLocalRing`. -/
noncomputable def algEquivOfResidueFieldEquiv (e : Ω ≃ₐ[R] ResidueField R) :
    algebra R Ω ≃ₐ[R] R :=
  AlgEquiv.ofAlgHom (lift R Ω e.toAlgHom) (Algebra.ofId R (algebra R Ω))
    (Subsingleton.elim _ _) (AlgHom.ext (algebraMap_lift_residueFieldEquiv R Ω e))

/-- The equivalence to the henselian base is the lift of the residue-field identification. -/
@[simp]
theorem algEquivOfResidueFieldEquiv_apply (e : Ω ≃ₐ[R] ResidueField R) (x : algebra R Ω) :
    algEquivOfResidueFieldEquiv R Ω e x = lift R Ω e.toAlgHom x :=
  (rfl)

/-- The inverse equivalence is the canonical structure map, not merely an abstract
isomorphism of rings. -/
@[simp]
theorem algEquivOfResidueFieldEquiv_symm_apply (e : Ω ≃ₐ[R] ResidueField R) (r : R) :
    (algEquivOfResidueFieldEquiv R Ω e).symm r = algebraMap R (algebra R Ω) r :=
  (rfl)

end Henselian

section StrictlyHenselian

variable (R Ω : Type u) [CommRing R] [IsStrictlyHenselianLocalRing R] [Field Ω] [Algebra R Ω]
  [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω]

/-- Over a strictly henselian local ring `R`, the pointed étale colimit `algebra R Ω` for any
separable algebraic extension `Ω` of `ResidueField R` (in particular, the strict henselization of
`R` with respect to any separable closure `Ω` of `ResidueField R`) is canonically `R`-isomorphic to
`R` itself. -/
@[stacks 04GQ]
noncomputable def algEquivOfIsStrictlyHenselianLocalRing : algebra R Ω ≃ₐ[R] R :=
  have := IsStrictlyHenselianLocalRing.isSepClosed_residueField (S := R)
  algEquivOfResidueFieldEquiv R Ω
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (ResidueField R) Ω)
      (IsSepClosed.algebraMap_bijective (ResidueField R) Ω)).symm

/-- The inverse of `algEquivOfIsStrictlyHenselianLocalRing` is `algebraMap R (algebra R Ω)`. -/
@[simp]
theorem algEquivOfIsStrictlyHenselianLocalRing_symm_apply (r : R) :
    (algEquivOfIsStrictlyHenselianLocalRing R Ω).symm r = algebraMap R (algebra R Ω) r :=
  (rfl)

end StrictlyHenselian

end TauCeti.StrictHenselization
