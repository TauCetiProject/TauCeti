/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Etale
public import TauCeti.RingTheory.StrictHenselization.MaximalIdeal
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Strict henselization of a field

The colimit of the étale `K`-algebras pointed in a separable algebraic extension `Ω / K`
is canonically `Ω`. The equivalence is the actual pointing map `toTarget`, so it identifies
the structure map of the colimit with `K → Ω`, not with an unspecified field embedding.
In particular the strict henselization of a field is its chosen separable closure.

The injectivity statement does not require the extension to be algebraic or separable:
over a field, the maximal ideal of the pointed colimit is zero. Separability is needed only
to ensure that all of `Ω` is reached. The structure map is bijective exactly when `K → Ω`
is bijective. Thus it is bijective for a separably closed base, but not for a finite base
with infinite separable closure.

## References

* Stacks Project, Tags 04GP and 04GQ.
* `TauCeti.StrictHenselization.maximalIdeal_eq_map` and
  `TauCeti.StrictHenselization.toTarget_surjective` supply the maximal-ideal and
  standard-étale lifting arguments.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.StrictHenselization

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]

/-- Over a field, the map induced by the pointings embeds the pointed étale colimit in the
target field. No algebraicity assumption on the target is needed. -/
theorem toTarget_injective_of_field : Function.Injective (toTarget K Ω) := by
  apply (RingHom.injective_iff_ker_eq_bot (toTarget K Ω).toRingHom).mpr
  rw [ker_toTarget_eq_maximalIdeal, maximalIdeal_eq_map, maximalIdeal_eq_bot, Ideal.map_bot]

variable [Algebra.IsSeparable K Ω]

/-- The pointed étale colimit over a field is its chosen separable algebraic extension.
For a separable closure `Ω`, this computes the strict henselization of `K`. -/
noncomputable def algEquivOfField : algebra K Ω ≃ₐ[K] Ω := by
  let : Algebra (ResidueField K) Ω := (ResidueField.lift (algebraMap K Ω)).toAlgebra
  have : IsScalarTower K (ResidueField K) Ω :=
    IsScalarTower.of_algebraMap_eq fun k ↦ (ResidueField.lift_residue_apply _ k).symm
  have : Algebra.IsSeparable (ResidueField K) Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K (ResidueField K) Ω
  exact AlgEquiv.ofBijective (toTarget K Ω)
    ⟨toTarget_injective_of_field K Ω, toTarget_surjective K Ω⟩

/-- The field computation is given by the point of the colimit. -/
@[simp]
theorem algEquivOfField_apply (x : algebra K Ω) :
    algEquivOfField K Ω x = toTarget K Ω x :=
  (rfl)

/-- The inverse of the field computation lifts each element of the chosen extension. -/
@[simp]
theorem toTarget_algEquivOfField_symm (x : Ω) :
    toTarget K Ω ((algEquivOfField K Ω).symm x) = x :=
  (algEquivOfField K Ω).apply_symm_apply x

/-- The inverse of the field computation recovers each element from its pointing. -/
@[simp]
theorem algEquivOfField_symm_toTarget (x : algebra K Ω) :
    (algEquivOfField K Ω).symm (toTarget K Ω x) = x :=
  (algEquivOfField K Ω).symm_apply_apply x

/-- The structure map to the pointed étale colimit is bijective exactly when the chosen
separable algebraic extension is trivial. -/
theorem algebraMap_bijective_iff_of_field :
    Function.Bijective (algebraMap K (algebra K Ω)) ↔
      Function.Bijective (algebraMap K Ω) := by
  have hcomp : (algEquivOfField K Ω) ∘ algebraMap K (algebra K Ω) = algebraMap K Ω :=
    funext (algEquivOfField K Ω).commutes
  rw [← hcomp, (algEquivOfField K Ω).bijective.of_comp_iff']

/-- A separably closed field acquires no new elements in its strict henselization,
independently of the chosen separable algebraic extension used for pointing. -/
theorem algebraMap_bijective_of_isSepClosed [IsSepClosed K] :
    Function.Bijective (algebraMap K (algebra K Ω)) :=
  (algebraMap_bijective_iff_of_field K Ω).mpr (IsSepClosed.algebraMap_bijective K Ω)

/-- The structure map for a finite field is not surjective when the chosen separable
algebraic extension is infinite, in particular when it is an algebraic closure. -/
theorem not_surjective_algebraMap_of_finite [Finite K] [Infinite Ω] :
    ¬ Function.Surjective (algebraMap K (algebra K Ω)) := by
  intro h
  have hsurj : Function.Surjective (algebraMap K Ω) := by
    intro x
    obtain ⟨k, hk⟩ := h ((algEquivOfField K Ω).symm x)
    exact ⟨k, by simpa using congrArg (algEquivOfField K Ω) hk⟩
  have : Finite Ω := Finite.of_surjective _ hsurj
  exact not_finite Ω

end TauCeti.StrictHenselization
