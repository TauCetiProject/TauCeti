/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The different ideal

This file supplies general lemmas about trace-dual fractional ideals. The coercion result connects
the fractional-ideal and submodule trace duals, allowing submodule results such as localization to
be transferred to fractional ideals. The identity-extension trace-dual theorem gives the unit
different, which is used to compute the relative discriminant of the identity extension.
-/

public section

open Module

open scoped nonZeroDivisors

namespace TauCeti

universe uR uS uK uL

variable {R : Type uR} {S : Type uS} {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing S] [Field K] [Field L]
variable [Algebra R S] [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L]
variable [IsScalarTower R K L] [IsScalarTower R S L]
variable [IsDomain R]
variable [IsFractionRing R K] [IsFractionRing S L]
variable [IsIntegrallyClosed R] [IsIntegralClosure S R L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

namespace FractionalIdeal

/-- Over a domain, the fractional-ideal trace dual of one coerces to the submodule trace dual. -/
@[simp]
theorem coe_dual_one_of_isDomain [IsDomain S] :
    (↑(FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L)) : Submodule S L) =
      Submodule.traceDual R K (1 : Submodule S L) := by
  ext x
  -- Rewriting through `FractionalIdeal.coe_mk` directly requires Mathlib's transparency override.
  -- Extensionality reduces the coercion equality to the definitionally equal membership predicates.
  change x ∈ FractionalIdeal.dual R K (1 : FractionalIdeal S⁰ L) ↔ _
  have h : (1 : FractionalIdeal S⁰ L) ≠ 0 := one_ne_zero
  simp [FractionalIdeal.dual, h]
  -- In the nonzero branch, `dual` stores the trace-dual submodule itself; only its proof field is
  -- discarded by the coercion, so the two remaining membership predicates are definitionally equal.
  rfl

end FractionalIdeal

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The trace dual of the unit submodule is the unit submodule for the identity extension of a
domain to its fraction field. -/
@[simp]
theorem traceDual_one_fractionRing_self :
    letI : Algebra (FractionRing A) (FractionRing A) :=
      FractionRing.liftAlgebra A (FractionRing A)
    Submodule.traceDual A (FractionRing A) (1 : Submodule A (FractionRing A)) = 1 := by
  let _ : Algebra (FractionRing A) (FractionRing A) :=
    FractionRing.liftAlgebra A (FractionRing A)
  have htrace (x : FractionRing A) : Algebra.trace (FractionRing A) (FractionRing A) x = x := by
    have htrace' := @Algebra.trace_eq_of_equiv_equiv
      (FractionRing A) (FractionRing A) (FractionRing A) (FractionRing A)
      _ _ _ _ (Algebra.id (FractionRing A))
      (FractionRing.liftAlgebra A (FractionRing A)) (RingEquiv.refl _) (RingEquiv.refl _) ?_ x
    · simpa using htrace'.symm
    · ext y
      -- The compatibility goal is definitionally the identity algebra map after
      -- reducing the two identity equivalences and the lifted algebra wrapper.
      change algebraMap (FractionRing A) (FractionRing A) y = y
      rw [FractionRing.algebraMap_liftAlgebra]
      exact IsLocalization.lift_id y
  apply le_antisymm
  · intro x hx
    have hx' := (@Submodule.mem_traceDual A (FractionRing A) (FractionRing A) A
      _ _ _ _ _ _ _ (FractionRing.liftAlgebra A (FractionRing A)) _ _ _).mp hx 1 (by simp)
    rw [Submodule.mem_one]
    exact (by simpa [Algebra.traceForm_apply, htrace x] using hx')
  · intro x hx
    rw [Submodule.mem_traceDual]
    intro y hy
    rw [Submodule.mem_one] at hx hy
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    refine ⟨x * y, ?_⟩
    rw [Algebra.traceForm_apply, htrace]
    simp

variable {D : Type*} [CommRing D] [IsDedekindDomain D]

/-- The different ideal of the identity extension of a Dedekind domain is the unit ideal. -/
@[simp]
theorem differentIdeal_self : differentIdeal D D = ⊤ := by
  let _ : Algebra (FractionRing D) (FractionRing D) :=
    FractionRing.liftAlgebra D (FractionRing D)
  rw [differentIdeal]
  -- Unfolding `differentIdeal` and its coercion exposes the quotient's ambient
  -- submodule while retaining the comap by `Algebra.linearMap`.
  change Submodule.comap (Algebra.linearMap D (FractionRing D))
    (1 / (Submodule.traceDual D (FractionRing D) 1)) = ⊤
  rw [traceDual_one_fractionRing_self]
  -- This is a coercion bridge: the unfolded different uses submodule division,
  -- while the available normalization lemmas for division apply to fractional ideals.
  rw [show (1 / (1 : Submodule D (FractionRing D))) =
      (↑((1 : FractionalIdeal D⁰ (FractionRing D)) / 1) : Submodule D (FractionRing D)) by
    rw [FractionalIdeal.coe_div one_ne_zero, FractionalIdeal.coe_one]]
  rw [FractionalIdeal.div_one, FractionalIdeal.coe_one]
  ext x
  simp [Submodule.mem_one]

end TauCeti

end
