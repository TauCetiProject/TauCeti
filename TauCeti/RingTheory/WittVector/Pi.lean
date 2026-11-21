/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.WittVector.Basic

/-!
# Witt vectors of products

Witt vectors are computed coordinatewise: for an arbitrary family of commutative rings `R i`,
the Witt vectors of the projections give a ring isomorphism `W(∏ R i) ≃+* ∏ W(R i)`, under which
the `n`-th Witt coordinate of a family is the family of `n`-th Witt coordinates.

## Main definitions

* `WittVector.piEquiv`: `WittVector p (∀ i, R i) ≃+* ∀ i, WittVector p (R i)`.

## Main results

* `WittVector.coeff_piEquiv_apply`, `WittVector.coeff_piEquiv_symm`: Witt coordinates under
  `WittVector.piEquiv`.
-/

public section

variable {ι : Type*}

namespace WittVector

variable (p : ℕ) [Fact p.Prime] {R : ι → Type*} [∀ i, CommRing (R i)]

/-- **Witt vectors commute with products**: `W(∏ R i) ≃+* ∏ W(R i)`, by the Witt vectors of the
projections; Witt coordinates are taken coordinatewise. -/
noncomputable def piEquiv : WittVector p (∀ i, R i) ≃+* ∀ i, WittVector p (R i) :=
  RingEquiv.ofBijective (RingHom.pi fun i ↦ map (Pi.evalRingHom R i)) <| by
    refine ⟨fun x y hxy ↦ ext fun n ↦ funext fun i ↦ ?_, fun y ↦
      ⟨mk p fun n i ↦ (y i).coeff n, funext fun i ↦ ext fun n ↦ by
        rw [RingHom.pi_apply, map_coeff, coeff_mk, Pi.evalRingHom_apply]⟩⟩
    simpa [map_coeff] using congr(($hxy i).coeff n)

variable {p}

@[simp]
theorem piEquiv_apply (x : WittVector p (∀ i, R i)) (i : ι) :
    piEquiv p x i = map (Pi.evalRingHom R i) x :=
  (rfl)

theorem coeff_piEquiv_apply (x : WittVector p (∀ i, R i)) (i : ι) (n : ℕ) :
    (piEquiv p x i).coeff n = x.coeff n i := by
  rw [piEquiv_apply, map_coeff, Pi.evalRingHom_apply]

@[simp]
theorem coeff_piEquiv_symm (y : ∀ i, WittVector p (R i)) (n : ℕ) :
    ((piEquiv p).symm y).coeff n = fun i ↦ (y i).coeff n :=
  funext fun i ↦ by rw [← coeff_piEquiv_apply, RingEquiv.apply_symm_apply]

end WittVector
