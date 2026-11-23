/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.LinearCombination
import TauCeti.GroupTheory.Coset.Fiber

/-!
# Units along surjective ring homomorphisms

A surjective map of commutative rings whose kernel consists of nilpotent elements reflects
units. Here unit reflection is Mathlib's `IsLocalHom`; neither ring is required to be local.

Together with Mathlib's kernel containment for unit-reflecting maps, this allows unit reflection
to propagate through inverse systems with locally nilpotent transition kernels. Elementwise
nilpotence suffices, without a uniform exponent.

A surjective map out of a semilocal ring (one with finitely many maximal ideals) is surjective
on units. This is the semilocal counterpart of Mathlib's
`IsLocalRing.surjective_units_map_of_local_ringHom`; it needs no unit reflection. By the Chinese
remainder theorem a lift of a unit can be corrected by an element of the kernel so that it avoids
every maximal ideal.

A surjective unit-reflecting map is `|ker f|`-to-one on units
(`RingHom.natCard_units_eq_natCard_ker_mul`): the units are exactly the preimage of the units, and
every fibre of the underlying additive map is a coset of the kernel. Applied to the matrix ring
this counts the general linear group over `ℤ/pᵏ` from that over `𝔽_p`.

Unit reflection also passes to subalgebras: if `R → S` reflects units then so does `R → T` for
every subalgebra `T` of `S` (`Subalgebra.isLocalHom_algebraMap`).

For a surjection of local rings `A → A'`, the image of the maximal ideal of `A` has radical the
maximal ideal of `A'` (`TauCeti.IsLocalRing.radical_map_maximalIdeal_of_surjective`): the closed
point of `Spec A'` is the only point over the closed point of `Spec A`.
-/

public section

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring homomorphism with elementwise nilpotent kernel reflects units.
No uniform nilpotence exponent is required. -/
theorem isLocalHom_of_surjective_of_isNilpotent_ker (f : R →+* S)
    (hf : Function.Surjective f) (hnil : ∀ x, f x = 0 → IsNilpotent x) :
    IsLocalHom f := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨y, hy⟩ := hf (↑hx.unit⁻¹)
  have hxy : IsNilpotent (x * y - 1) := hnil _ (by simp [hy, hx.mul_val_inv])
  exact isUnit_of_mul_isUnit_left (by simpa using hxy.isUnit_add_one)

/-- A surjective ring homomorphism out of a semilocal ring is surjective on units. -/
theorem surjective_units_map_of_surjective [_root_.Finite (MaximalSpectrum R)] (f : R →+* S)
    (hf : Function.Surjective f) : Function.Surjective (Units.map f.toMonoidHom) := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum R)
  intro u
  obtain ⟨a, ha⟩ := hf u
  obtain ⟨c, hc⟩ := hf ↑u⁻¹
  -- Write `1 = k + b` with `k ∈ ker f` and `b` in every maximal ideal not containing `ker f`.
  let s : Finset (MaximalSpectrum R) := {P | ¬ker f ≤ P.asIdeal}
  have hs : ker f ⊔ ⨅ P ∈ s, P.asIdeal = ⊤ := Ideal.sup_iInf_eq_top fun P hP ↦ by
    by_contra hne
    exact (Finset.mem_filter.mp hP).2
      (le_sup_left.trans_eq (P.isMaximal.eq_of_le hne le_sup_right).symm)
  obtain ⟨k, hk, b, hb, hkb⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top (x := (1 : R)))
  -- The lift `a * b + k` of `u` lies in no maximal ideal `P`.
  have hunit : IsUnit (a * b + k) := by
    by_contra h
    obtain ⟨P, hP, haP⟩ := exists_max_ideal_of_mem_nonunits h
    refine hP.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    by_cases hkP : ker f ≤ P
    · -- Modulo `P` the lift is congruent to `a`, which is invertible modulo `ker f`.
      have hac : a * c - 1 ∈ ker f := by simp [mem_ker, ha, hc]
      rw [show (1 : R) = c * (a * b + k) + (a * c - c) * k - (a * c - 1) by
        linear_combination (-(a * c)) * hkb]
      exact P.sub_mem (P.add_mem (P.mul_mem_left _ haP) (P.mul_mem_left _ (hkP hk))) (hkP hac)
    · -- Modulo `P` the lift is congruent to `1`.
      have hbP : b ∈ P := Ideal.mem_iInf.mp (Ideal.mem_iInf.mp hb ⟨P, hP⟩) (by simpa [s])
      rw [show (1 : R) = (a * b + k) + (1 - a) * b by linear_combination -hkb]
      exact P.add_mem haP (P.mul_mem_left _ hbP)
  have hfb : f b = 1 := by simpa [mem_ker.mp hk] using congrArg f hkb
  exact ⟨hunit.unit, Units.ext (by simp [ha, hfb, mem_ker.mp hk])⟩

/-- **Units along a surjective local homomorphism.** If `f : R →+* S` is surjective and reflects
units, then `|Rˣ| = |ker f| · |Sˣ|`: the units of `R` are the preimage of the units of `S`, and
each fibre of `f` is a coset of its kernel. The rings need not be commutative, so this applies to
matrix rings. As an identity of `Nat.card`s it also holds when the rings are infinite. -/
theorem natCard_units_eq_natCard_ker_mul {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    [IsLocalHom f] (hf : Function.Surjective f) :
    Nat.card Rˣ = Nat.card (ker f) * Nat.card Sˣ := by
  have hS : Nat.card Sˣ = Nat.card {y : S | IsUnit y} :=
    Nat.card_congr <| Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans <|
      Equiv.subtypeEquivRight fun y ↦ IsUnit.mem_submonoid_iff y
  have hker : Nat.card (ker f) = Nat.card (f : R →+ S).ker :=
    Nat.card_congr <| Equiv.subtypeEquivRight fun x ↦ by simp [mem_ker]
  rw [hS, hker, mul_comm, ← AddMonoidHom.natCard_preimage_of_surjective (f : R →+ S) hf]
  exact Nat.card_congr <| Submonoid.unitsTypeEquivIsUnitSubmonoid.toEquiv.trans <|
    Equiv.subtypeEquivRight fun x ↦ by simp [IsUnit.mem_submonoid_iff, isUnit_map_iff]

end RingHom

namespace Subalgebra

variable {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]

/-- If `R → S` reflects units, then so does `R → T` for every subalgebra `T` of `S`. -/
instance isLocalHom_algebraMap [IsLocalHom (algebraMap R S)] (T : Subalgebra R S) :
    IsLocalHom (algebraMap R T) :=
  have : IsLocalHom ((T.val : T →+* S).comp (algebraMap R T)) := by
    rwa [T.val.comp_algebraMap]
  isLocalHom_of_comp _ (T.val : T →+* S)

end Subalgebra

namespace TauCeti.IsLocalRing

variable {A A' : Type*} [CommRing A] [IsLocalRing A] [CommRing A'] [IsLocalRing A']
  [Algebra A A']

/-- For a surjection of local rings `A → A'`, the closed point is the only point of `Spec A'`
over the closed point of `Spec A`. -/
theorem radical_map_maximalIdeal_of_surjective (hf : Function.Surjective (algebraMap A A')) :
    ((IsLocalRing.maximalIdeal A).map (algebraMap A A')).radical =
      IsLocalRing.maximalIdeal A' := by
  rw [IsLocalRing.map_maximalIdeal_of_surjective _ hf]
  exact (IsLocalRing.maximalIdeal.isMaximal _).isPrime.radical

end TauCeti.IsLocalRing
