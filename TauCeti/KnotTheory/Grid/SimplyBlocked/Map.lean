/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.SimplyBlocked.Basic

/-!
# Specializing semilinear grid chain maps

A semilinear map of unblocked grid chains can be specialized along any homomorphism between
the polynomial rings in the surviving variables. When the full and surviving coefficient maps
commute with blocking, the specialized map intertwines the original map and preserves its chain
equation. No compatibility is needed to construct the specialized matrix.

Column maps supply one family of compatible coefficient maps, including the column-merging
comparisons for south-west and north-east stabilization.

## Main definitions

* `TauCeti.simplyBlockedRingHomAlong`: the coefficient homomorphism along the column map.
* `TauCeti.simplyBlockedMap` (from `SimplyBlocked.Basic`): specialization of a semilinear map.

## Main results

* `TauCeti.simplyBlockedMap_simplyBlockedSpecialization`: the specialized map descends the
  original map (from `SimplyBlocked.Basic`).
* `TauCeti.simplyBlockedMap_simplyBlockedDifferential`: the chain equation descends as well.

## References

Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Sections 4.6 and 5.2.
-/

public section

open MvPolynomial

namespace TauCeti

variable {n m : ℕ} (R : Type*)

section Semiring

variable [CommSemiring R] (π : Fin m → Fin n) (i : Fin n) (j : Fin m)

/-- Rename surviving source variables along `π`, then block the target column. -/
noncomputable def simplyBlockedRingHomAlong :
    MvPolynomial {c : Fin m // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R :=
  (simplyBlockedRingHom R i).comp
    ((rename (R := R) π).toRingHom.comp (rename Subtype.val).toRingHom)

/-- A surviving variable is renamed and specialized. -/
@[simp]
theorem simplyBlockedRingHomAlong_X (c : {c : Fin m // c ≠ j}) :
    simplyBlockedRingHomAlong R π i j (X c) = simplyBlockedRingHom R i (X (π c)) := by
  simp [simplyBlockedRingHomAlong]

/-- Ground coefficients are unchanged. -/
@[simp]
theorem simplyBlockedRingHomAlong_C (r : R) :
    simplyBlockedRingHomAlong R π i j (C r) = C r := by
  simp [simplyBlockedRingHomAlong]

/-- Renaming commutes with blocking when `π` carries the blocked source column to the target. -/
theorem simplyBlockedRingHomAlong_specialization (hπ : π j = i)
    (p : MvPolynomial (Fin m) R) :
    simplyBlockedRingHomAlong R π i j (simplyBlockedRingHom R j p) =
      simplyBlockedRingHom R i (rename π p) := by
  have h : (simplyBlockedRingHomAlong R π i j).comp (simplyBlockedRingHom R j) =
      (simplyBlockedRingHom R i).comp (rename π).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [simplyBlockedRingHomAlong]
    · intro c
      by_cases hc : c = j
      · subst c
        simp [hπ]
      · have hX : X c = rename Subtype.val
            (X (R := R) (⟨c, hc⟩ : {c : Fin m // c ≠ j})) := by simp
        simp only [RingHom.comp_apply, simplyBlockedRingHom_apply]
        rw [hX, killCompl_rename_app]
        simp [simplyBlockedRingHomAlong]
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    RingHom.congr_fun h p

variable {σ : MvPolynomial (Fin m) R →+* MvPolynomial (Fin n) R}
  (τ : MvPolynomial {c : Fin m // c ≠ j} R →+* MvPolynomial {c : Fin n // c ≠ i} R)
  (f : GridChainMinus R m →ₛₗ[σ] GridChainMinus R n)

variable (G : GridDiagram n) (G' : GridDiagram m)

/-- A semilinear chain equation descends through specialization. -/
theorem simplyBlockedMap_simplyBlockedDifferential
    (hστ : ∀ p, τ (simplyBlockedRingHom R j p) = simplyBlockedRingHom R i (σ p))
    (hf : ∀ c, f (G'.unblockedDifferential R c) = G.unblockedDifferential R (f c))
    (c : GridChainHat R m j) :
    simplyBlockedMap R i j τ f (G'.simplyBlockedDifferential R j c) =
      G.simplyBlockedDifferential R i (simplyBlockedMap R i j τ f c) := by
  obtain ⟨c, rfl⟩ := simplyBlockedSpecialization_surjective R j c
  rw [← GridDiagram.simplyBlockedSpecialization_unblockedDifferential,
    simplyBlockedMap_simplyBlockedSpecialization R i j τ f hστ,
    simplyBlockedMap_simplyBlockedSpecialization R i j τ f hστ,
    ← GridDiagram.simplyBlockedSpecialization_unblockedDifferential, hf]

end Semiring

end TauCeti
