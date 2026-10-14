/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Operations on fractional ideals

Two facts about Mathlib's `FractionalIdeal.ringEquivOfRingEquiv`, the transport of fractional
ideals along a ring equivalence `f : R ≃+* R'` extended to fraction rings, and two facts about
scaling a fractional ideal by a unit: the principal fractional ideal of a unit is a unit, and
scaling by a unit is cancelled by scaling by its inverse. The principal-ideal map has the base-ring
units as its kernel and is unchanged by negation of a generator.

The principal-map kernel is adapted from Michael Stoll's elliptic-curves formalisation
(`github.com/MichaelStollBayreuth/EllipticCurves`, `EllipticCurves/Mathlib/FractionalIdeal.lean`
at pin `66889eada51a`, Apache 2.0, by Michael Stoll).

## Main results

* `FractionalIdeal.canonicalEquiv_eq_ringEquivOfRingEquiv`: the canonical equivalence between the
  fractional ideals of two fraction rings of `R` is transport along the identity.
* `FractionalIdeal.ringEquivOfRingEquiv_coeIdeal`: transport sends the fractional ideal of an ideal
  `I` to that of `Ideal.map f I`.
* `FractionalIdeal.toPrincipalIdeal_eq_one_iff`: the principal-map kernel consists of base units.
* `FractionalIdeal.toPrincipalIdeal_neg`: negating a generator preserves its principal ideal.
* `FractionalIdeal.isUnit_spanSingleton`: the principal fractional ideal of a unit is a unit.
* `FractionalIdeal.spanSingleton_inv_mul_cancel_left`: scaling by a unit and then by its inverse
  returns the fractional ideal.
-/

public section

open scoped nonZeroDivisors

namespace FractionalIdeal

section RingEquiv

variable {R R' : Type*} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

/-- The canonical equivalence between the fractional ideals of two fraction fields of `R` is
transport along the identity ring equivalence. This lets a change of fraction field and a transport
along a ring equivalence be composed by `FractionalIdeal.ringEquivOfRingEquiv_trans_apply`. -/
theorem canonicalEquiv_eq_ringEquivOfRingEquiv (K K' : Type*) [CommRing K] [CommRing K']
    [Algebra R K] [Algebra R K'] [IsFractionRing R K] [IsFractionRing R K'] :
    canonicalEquiv R⁰ K K' = ringEquivOfRingEquiv K K' (RingEquiv.refl R) := by
  let : RingHomInvPair (RingEquiv.refl R : R →+* R) (RingEquiv.refl R).symm :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl R)
  let : RingHomInvPair ((RingEquiv.refl R).symm : R →+* R) (RingEquiv.refl R) :=
    RingHomInvPair.of_ringEquiv (RingEquiv.refl R).symm
  ext I x
  rw [FractionalIdeal.mem_canonicalEquiv_apply]
  erw [FractionalIdeal.ringEquivOfRingEquiv_apply]
  -- the right-hand side is the image submodule under the semilinear equivalence, presented by
  -- `erw` through the equivalence's coercion; `change` names it so `Submodule.mem_map` fires.
  change _ ↔ x ∈ Submodule.map
      (IsFractionRing.semilinearEquivOfRingEquiv K K' (RingEquiv.refl R)).toLinearMap I.val
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    erw [IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_apply]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    erw [IsFractionRing.semilinearEquivOfRingEquiv_apply,
      IsFractionRing.ringEquivOfRingEquiv_apply]
    -- what is left is `IsLocalization.map K' (RingHom.id R) _ y = IsLocalization.map K'
    -- ↑(RingEquiv.refl R) _ y`: the coercion of `RingEquiv.refl R` *is* `RingHom.id R`, and the
    -- two remaining field arguments are proofs.
    rfl

/-- Transport of a `coeIdeal` along `FractionalIdeal.ringEquivOfRingEquiv f` is the `coeIdeal` of
the pushforward ideal `Ideal.map f`. This is the fraction-field shadow of `Ideal.map`. -/
@[simp]
theorem ringEquivOfRingEquiv_coeIdeal (K L : Type*)
    [CommRing K] [CommRing L] [Algebra R K] [Algebra R' L] [IsFractionRing R K]
    [IsFractionRing R' L] (f : R ≃+* R')
    (I : Ideal R) :
    ringEquivOfRingEquiv K L f (I : FractionalIdeal R⁰ K) =
      (Ideal.map (f : R →+* R') I : FractionalIdeal R'⁰ L) := by
  -- Pin the `RingHomInvPair` instances to resolve an `f`/`f.symm.symm` defeq diamond, so the `erw`
  -- rewrites below fire without a transparency option.
  let : RingHomInvPair (f : R →+* R') (f.symm : R' →+* R) := RingHomInvPair.of_ringEquiv f
  let : RingHomInvPair (f.symm : R' →+* R) (f : R →+* R') := RingHomInvPair.of_ringEquiv f.symm
  apply FractionalIdeal.coeToSubmodule_injective
  dsimp only
  rw [← FractionalIdeal.val_eq_coe, FractionalIdeal.ringEquivOfRingEquiv_apply_val,
    FractionalIdeal.val_eq_coe, FractionalIdeal.coe_coeIdeal, FractionalIdeal.coe_coeIdeal]
  ext x
  simp only [Submodule.mem_map, FractionalIdeal.mem_coeSubmodule]
  constructor
  · rintro ⟨y, ⟨r, hr, rfl⟩, rfl⟩
    exact ⟨f r, Ideal.mem_map_of_mem _ hr, by
      erw [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective (f : R →+* R') f.surjective).mp hs
    exact ⟨algebraMap R K r, ⟨r, hr, rfl⟩, by
      erw [IsFractionRing.semilinearEquivOfRingEquiv_algebraMap]; rfl⟩

end RingEquiv

section SpanSingleton

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]
  [IsLocalization S P]

/-- The principal fractional ideal generated by a unit is a unit. -/
theorem isUnit_spanSingleton {x : P} (hx : IsUnit x) : IsUnit (spanSingleton S x) := by
  obtain ⟨u, rfl⟩ := hx
  exact IsUnit.of_mul_eq_one (spanSingleton S ((u⁻¹ : Pˣ) : P)) (by
    rw [← map_mul (spanSingleton _), Units.mul_inv, map_one (spanSingleton _)])

/-- Scaling a fractional ideal by a unit and then by its inverse returns the ideal. -/
theorem spanSingleton_inv_mul_cancel_left (x : Pˣ) (I : FractionalIdeal S P) :
    spanSingleton S ((x⁻¹ : Pˣ) : P) * (spanSingleton S (x : P) * I) = I := by
  rw [← mul_assoc, ← map_mul (spanSingleton _), Units.inv_mul, map_one (spanSingleton _), one_mul]

end SpanSingleton

/-- The kernel of the principal-ideal map is the image of `Rˣ`: `toPrincipalIdeal R K u` is trivial
exactly when `u` comes from a unit of `R`. This is the left end of the ideal class exact
sequence. -/
lemma toPrincipalIdeal_eq_one_iff {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (u : Kˣ) :
    toPrincipalIdeal R K u = 1 ↔ ∃ a : Rˣ, Units.map (algebraMap R K : R →* K) a = u := by
  rw [← Units.val_inj, coe_toPrincipalIdeal, Units.val_one, ← coeToSubmodule_inj,
    coe_spanSingleton, coe_one, Submodule.span_singleton_eq_one_iff]
  exact ⟨fun ⟨a, ha⟩ ↦ ⟨a, Units.ext ha.symm⟩, fun ⟨a, ha⟩ ↦ ⟨a, by rw [← ha]; rfl⟩⟩

/-- Negating a generator preserves its principal ideal, because `-1` is a unit of the base ring. -/
@[simp] theorem toPrincipalIdeal_neg {R : Type*} [CommRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (x : Kˣ) :
    toPrincipalIdeal R K (-x) = toPrincipalIdeal R K x := by
  have hneg : toPrincipalIdeal R K (-1 : Kˣ) = 1 :=
    (toPrincipalIdeal_eq_one_iff _).mpr ⟨-1, Units.ext (by simp)⟩
  rw [← neg_one_mul x, map_mul, hneg, one_mul]

end FractionalIdeal
