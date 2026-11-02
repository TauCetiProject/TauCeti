/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import TauCeti.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.StandardEtale
import TauCeti.RingTheory.StrictHenselization.Etale

/-!
# The residue field of the strict henselization

Let `algebra R Ω` be the colimit of the pointed étale neighbourhoods of `(R, Ω)` and
`toTarget : algebra R Ω →ₐ[R] Ω` the map induced by their pointings. A simple root `ω ∈ Ω` of a
monic polynomial `f` over `R` is a value of `toTarget`: the point `X ↦ ω` of the standard étale
algebra `R[X]_{f'} ⧸ (f)` lifts through `toTarget` (`toTarget_comp_bijective`), so `ω` is the
image of `X` (`exists_toTarget_eq_of_aeval_eq_zero`).

For a local ring `R` and a separable algebraic extension `Ω` of its residue field `κ`, every
element of `Ω` is such a root: its minimal polynomial over `κ` is separable and lifts to a monic
polynomial over `R`. So `toTarget` is surjective (`toTarget_surjective`). Its kernel is the
maximal ideal (`ker_toTarget_eq_maximalIdeal`), so `toTarget` identifies the residue field of
`algebra R Ω` with `Ω` (`residueFieldEquiv`). This is property (3) of Stacks, Tag 04GP: the
residue field of the strict henselization of `R` with respect to a separable closure `Ω` of `κ`
is `Ω`. In particular the strict henselization is strictly henselian (`isSepClosed_residueField`):
it is a henselian local ring (`henselianLocalRing`) with separably closed residue field.

## Main results

* `TauCeti.StrictHenselization.exists_toTarget_eq_of_aeval_eq_zero`: a simple root in `Ω` of a
  monic polynomial over `R` is in the image of `toTarget`.
* `TauCeti.StrictHenselization.toTarget_surjective`: for `Ω` separable algebraic over the residue
  field of a local ring `R`, the map `toTarget` is surjective.
* `TauCeti.StrictHenselization.residueFieldEquiv`: the residue field of `algebra R Ω` is `Ω`.
* `TauCeti.StrictHenselization.isSepClosed_residueField`: if `Ω` is moreover separably closed,
  then so is the residue field of `algebra R Ω`.

## References

* [Stacks Project, Lemma 10.155.2](https://stacks.math.columbia.edu/tag/04GP), property (3).
-/

public section

open IsLocalRing Polynomial

universe u

namespace TauCeti.StrictHenselization

section Root

variable {R Ω : Type u} [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- A simple root `ω ∈ Ω` of a monic polynomial `f` over `R` is the image under `toTarget` of an
element of the colimit of pointed étale neighbourhoods. -/
theorem exists_toTarget_eq_of_aeval_eq_zero {f : R[X]} (hf : f.Monic) {ω : Ω}
    (hω : aeval ω f = 0) (hunit : IsUnit (aeval ω (derivative f))) :
    ∃ x : algebra R Ω, toTarget R Ω x = ω := by
  let P : StandardEtalePair R :=
    { f := f, monic_f := hf, g := derivative f, cond := ⟨1, 0, 1, by simp⟩ }
  have hP : P.HasMap ω := ⟨hω, hunit⟩
  obtain ⟨g, hg⟩ := (toTarget_comp_bijective R Ω P.Ring).2 (P.lift ω hP)
  exact ⟨g P.X, by rw [← AlgHom.comp_apply, hg, StandardEtalePair.lift_X]⟩

end Root

section ResidueField

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
  [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω]

/-- For a separable algebraic extension `Ω` of the residue field of a local ring `R`, every
element of `Ω` is the point of some element of the colimit of pointed étale neighbourhoods.
For a separable closure `Ω`, this says that the residue field of the strict henselization maps
onto `Ω`. -/
@[stacks 04GP "(3)"]
theorem toTarget_surjective : Function.Surjective (toTarget R Ω) := by
  intro ω
  have hsep : IsSeparable (ResidueField R) ω := Algebra.IsSeparable.isSeparable _ ω
  -- Lift the separable minimal polynomial of `ω` over the residue field to a monic polynomial
  -- over `R`; `ω` is a simple root of the lift.
  obtain ⟨f, hmap, -, hf⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective (algebraMap R (ResidueField R)) residue_surjective
      (minpoly (ResidueField R) ω)) (minpoly.monic hsep.isIntegral)
  have haeval (g : R[X]) :
      aeval ω (g.map (algebraMap R (ResidueField R))) = aeval ω g :=
    aeval_map_algebraMap _ ω g
  refine exists_toTarget_eq_of_aeval_eq_zero hf ?_ ?_
  · rw [← haeval, hmap, minpoly.aeval]
  · rw [← haeval, ← derivative_map, hmap, isUnit_iff_ne_zero]
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ ω)

/-- The residue field of the colimit of pointed étale neighbourhoods is `Ω`, through the map
induced by `toTarget`. For a separable closure `Ω` of the residue field of `R`, this identifies
the residue field of the strict henselization of `R` with `Ω`. -/
@[stacks 04GP "(3)"]
noncomputable def residueFieldEquiv : ResidueField (algebra R Ω) ≃ₐ[R] Ω :=
  (Ideal.quotientEquivAlgOfEq R (ker_toTarget_eq_maximalIdeal R Ω).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (toTarget_surjective R Ω))

/-- `residueFieldEquiv` sends the residue of `x` to `toTarget x`. -/
@[simp]
theorem residueFieldEquiv_residue (x : algebra R Ω) :
    residueFieldEquiv R Ω (residue (algebra R Ω) x) = toTarget R Ω x :=
  (rfl)

/-- The inverse of `residueFieldEquiv` sends `toTarget x` to the residue of `x`. -/
@[simp]
theorem residueFieldEquiv_symm_toTarget (x : algebra R Ω) :
    (residueFieldEquiv R Ω).symm (toTarget R Ω x) = residue (algebra R Ω) x :=
  (residueFieldEquiv R Ω).symm_apply_eq.mpr (residueFieldEquiv_residue R Ω x).symm

/-- If `Ω` is separably closed, so is the residue field of the colimit of pointed étale
neighbourhoods. Together with `henselianLocalRing`, this says that the strict henselization of a
local ring with respect to a separable closure of its residue field is strictly henselian. -/
@[stacks 04GP "(3)"]
instance isSepClosed_residueField [IsSepClosed Ω] :
    IsSepClosed (ResidueField (algebra R Ω)) :=
  .of_ringEquiv (residueFieldEquiv R Ω).symm.toRingEquiv

end ResidueField

end TauCeti.StrictHenselization
