/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Local
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Etale.StandardEtale

/-!
# The residue field of the pointed étale colimit

Let `R` be a local ring and let `Ω` be a separable algebraic extension of its residue field.
The pointing `toTarget : algebra R Ω →ₐ[R] Ω` is surjective: lift the minimal polynomial of
an element of `Ω` to a monic polynomial over `R`, then invert its derivative to obtain a
pointed standard étale neighbourhood containing a preimage of that element.

Consequently `residueFieldEquiv` identifies the residue field of the colimit with `Ω`,
compatibly with its pointing. When `Ω` is a separable closure, the residue field is separably
closed. These identifications specify the residue-field marking used when passing from a
geometric point to a strict henselization.

## References

* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP), properties (2) and (5).
-/

public section

open CategoryTheory IsLocalRing Polynomial

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [IsLocalRing R] [Field Ω]
  [Algebra R Ω] [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [Algebra.IsSeparable (ResidueField R) Ω]

/-- The pointing of the colimit is surjective for every separable algebraic extension of the
residue field of the base. No henselianity assumption on the base is needed. -/
@[stacks 04GP "(5), surjectivity"]
theorem toTarget_surjective : Function.Surjective (toTarget R Ω) := by
  intro x
  have hx := Algebra.IsSeparable.isSeparable (ResidueField R) x
  obtain ⟨f, hf, -, hmonic⟩ := lifts_and_degree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := R)) (minpoly (ResidueField R) x))
    (minpoly.monic hx.isIntegral)
  have heval (p : R[X]) : aeval x p = aeval x (p.map (residue R)) :=
    aeval_eq_aeval_map (by
      rw [← ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_eq]) p x
  have hroot : aeval x f = 0 := by
    rw [heval, hf]
    exact minpoly.aeval _ _
  have hderivative : aeval x f.derivative ≠ 0 := by
    rw [heval, ← derivative_map, hf]
    exact hx.aeval_derivative_ne_zero (minpoly.aeval _ _)
  let P : StandardEtalePair R :=
    { f := f, monic_f := hmonic, g := f.derivative,
      cond := ⟨1, 0, 1, by simp⟩ }
  have hpoint : P.HasMap x := ⟨hroot, isUnit_iff_ne_zero.mpr hderivative⟩
  let B : Neighbourhood R Ω :=
    ⟨Over.mk (CommAlgCat.ofHom (ULift.algEquiv.symm.toAlgHom.comp (P.lift x hpoint))),
      (isPointedNeighbourhood_iff R Ω _).mpr
        (inferInstanceAs (Algebra.Etale R P.Ring))⟩
  refine ⟨stage R Ω B P.X, ?_⟩
  rw [toTarget_stage_apply]
  -- `B` retains the standard étale carrier and its pointing, with the required universe lift.
  exact P.lift_X x hpoint

/-- The residue field of the pointed étale colimit is the chosen separable extension of the
base residue field. The equivalence is induced by `toTarget`. -/
noncomputable def residueFieldEquiv : ResidueField (algebra R Ω) ≃ₐ[R] Ω :=
  let point : ResidueField (algebra R Ω) →ₐ[R] Ω :=
    Ideal.Quotient.liftₐ (maximalIdeal (algebra R Ω)) (toTarget R Ω)
      (ker_toTarget_eq_maximalIdeal R Ω).ge
  AlgEquiv.ofBijective point ⟨point.toRingHom.injective, fun x ↦ by
    obtain ⟨y, hy⟩ := toTarget_surjective R Ω x
    exact ⟨residue (algebra R Ω) y, hy⟩⟩

/-- The residue-field identification carries reduction of a colimit element to its pointing. -/
@[simp]
theorem residueFieldEquiv_residue (x : algebra R Ω) :
    residueFieldEquiv R Ω (residue (algebra R Ω) x) = toTarget R Ω x :=
  (rfl)

/-- Under the inverse identification, the pointing of an element is its residue class. -/
@[simp]
theorem residueFieldEquiv_symm_toTarget (x : algebra R Ω) :
    (residueFieldEquiv R Ω).symm (toTarget R Ω x) = residue (algebra R Ω) x := by
  rw [← residueFieldEquiv_residue R Ω x, AlgEquiv.symm_apply_apply]

/-- A separably closed target gives a separably closed residue field of the colimit. -/
@[stacks 04GP "(2), residue field"]
instance isSepClosed_residueField [IsSepClosed Ω] : IsSepClosed (ResidueField (algebra R Ω)) where
  splits_of_separable p hp := by
    let e := residueFieldEquiv R Ω
    have h := (IsSepClosed.splits_of_separable (p.map e.toRingHom) hp.map).map
      e.symm.toRingHom
    simpa only [Polynomial.map_map, AlgEquiv.symm_toRingEquiv,
      RingEquiv.symm_toRingHom_comp_toRingHom, Polynomial.map_id] using h

end TauCeti.StrictHenselization
