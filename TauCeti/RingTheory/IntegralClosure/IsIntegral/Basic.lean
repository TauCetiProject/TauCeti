/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
-- Proof-only: supplies `isIntegral_trans` and `Algebra.IsIntegral.adjoin`, the two facts the
-- argument runs through. The statement mentions only `IsIntegral`, which the public import
-- above already provides, so nothing here is re-exported.
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Changing the base ring of an integrality claim

Mathlib's `isIntegral_trans` transfers integrality down a scalar tower `R → A → B`. The variant
here drops the tower: the two candidate base rings are only required to map compatibly into the
ring where the element lives, which is what happens when both of them sit inside that ring
without either being an algebra over the other.

## Main results

* `TauCeti.isIntegral_trans_common`: if every element of `P` becomes integral over `R` once
  mapped into `L`, then an element of `L` integral over `P` is integral over `R`.
-/

public section

namespace TauCeti

/-- Integrality transfers through compatible maps from two rings into a common ring. -/
theorem isIntegral_trans_common {R P L : Type*} [CommRing R] [CommRing P]
    [CommRing L] [Algebra R L] [Algebra P L]
    (hP : ∀ x : P, IsIntegral R (algebraMap P L x)) {x : L}
    (hx : IsIntegral P x) : IsIntegral R x := by
  let S := Algebra.adjoin R (Set.range (algebraMap P L))
  let integral : Algebra.IsIntegral R S := Algebra.IsIntegral.adjoin fun y hy ↦ by
    obtain ⟨z, rfl⟩ := hy
    exact hP z
  let pToS : P →+* S := RingHom.codRestrict (algebraMap P L) S fun z ↦
    Algebra.subset_adjoin ⟨z, rfl⟩
  let pAlgebra : Algebra P S := pToS.toAlgebra
  -- the tower equality holds pointwise: `pToS` restricts `algebraMap P L` to `S`, so composing
  -- with the inclusion `S.val` returns the original map. Stated by extensionality rather than by
  -- `rfl`, so it does not depend on how `codRestrict` and `toAlgebra` unfold.
  let scalarTower : IsScalarTower P S L := IsScalarTower.of_algebraMap_eq' <| by
    ext z
    simp [pAlgebra, RingHom.algebraMap_toAlgebra, pToS]
  exact isIntegral_trans (R := R) (A := S) x (hx.tower_top (A := S))

end TauCeti
