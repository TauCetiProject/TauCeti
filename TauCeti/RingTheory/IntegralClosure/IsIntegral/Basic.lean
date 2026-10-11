/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
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
* `TauCeti.dvd_of_isIntegral_div`: an element of a field extension of `A` that is a quotient of
  elements of `A` and is integral over `A` has its numerator divisible by its denominator, when
  `A` is integrally closed.
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

/-- An element of a field extension of `A` that is a quotient of elements of `A` and is integral
over `A` has its numerator divisible by its denominator, when `A` is integrally closed. -/
theorem dvd_of_isIntegral_div
    {A L : Type*} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L] [Algebra A L] [FaithfulSMul A L] {a d : A} (hd : d ≠ 0)
    (h : IsIntegral A (algebraMap A L a / algebraMap A L d)) : d ∣ a := by
  have hinj : Function.Injective (algebraMap A L) := FaithfulSMul.algebraMap_injective A L
  let f : FractionRing A →ₐ[A] L := IsFractionRing.liftAlgHom (g := Algebra.ofId A L) hinj
  have hf : Function.Injective f := (f : FractionRing A →+* L).injective
  have hdF : algebraMap A (FractionRing A) d ≠ 0 := fun h' =>
    hd (IsFractionRing.injective A (FractionRing A) (by rw [h', map_zero]))
  have hw : f (algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) d) =
      algebraMap A L a / algebraMap A L d := by
    rw [map_div₀, AlgHom.commutes, AlgHom.commutes]
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((isIntegral_algHom_iff f hf).mp (hw ▸ h))
  refine ⟨e, IsFractionRing.injective A (FractionRing A) ?_⟩
  rw [map_mul, he, mul_div_cancel₀ _ hdF]

end TauCeti
