/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Lift
import TauCeti.RingTheory.StrictHenselization.Map

/-!
# Pointed étale colimits over henselian local rings

For a henselian local ring `R`, the colimit of étale neighbourhoods pointed in its residue
field is `R` itself. More generally, the same holds when the pointing algebra is identified
with the residue field as an `R`-algebra. The inverse to the structure map is the unique
henselian lift of that identification.

In particular, if `R` is strictly henselian and its residue field is chosen as its own
separable closure, its strict henselization is canonically isomorphic to `R`. No
separable-closedness assumption is needed for the more general pointed-colimit statement:
pointing in the residue field, rather than a larger separable closure, is essential here.

## References

* Stacks Project, Tags 04GQ and 08HQ.
* `TauCeti.StrictHenselization.lift` supplies the stagewise henselian lifts;
  `TauCeti.StrictHenselization.map_unique` supplies uniqueness of pointed-colimit maps.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

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
algebra is identified with the base residue field. For a strictly henselian ring, taking
`Ω = ResidueField R` and `e = AlgEquiv.refl` identifies its strict henselization with `R`. -/
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

end TauCeti.StrictHenselization
