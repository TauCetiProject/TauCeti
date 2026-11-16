/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-!
# Primes above a set of primes, and the Selmer group relative to them

For an injective algebra map of commutative rings `R → B` with `B` Dedekind, only finitely
many nonzero prime ideals of `B` lie over a given nonzero prime `v` of `R`. This does not
require integrality or a Dedekind hypothesis on `R`.

For domains `R` and `B` with `B` integral over `R`, contraction defines
`HeightOneSpectrum.under R`. For a set `S` of primes of `R`,
`IsDedekindDomain.HeightOneSpectrum.primesAbove R B S` is its preimage under contraction.
When `B` is Dedekind and the algebra map is injective, this preimage is finite whenever `S` is.
The Selmer group of the fraction field of `B` relative to these primes is
`IsDedekindDomain.selmerGroupAbove R B L S n`, Mathlib's `L⟮primesAbove R B S, n⟯`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.primesAbove`: the primes of `B` above a set of primes
  of `R`, as a preimage under `HeightOneSpectrum.under`.
* `IsDedekindDomain.selmerGroupAbove`: the `n`-Selmer group of `L` relative to the primes of `B`
  above `S`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.liesOver_under`: the `LiesOver` instance relating a prime
  to its contraction, which the `under`-indexed results downstream need.
* `IsDedekindDomain.HeightOneSpectrum.under_eq_iff_liesOver`: a prime contracts to `v` exactly
  when it lies over `v`.
* `IsDedekindDomain.HeightOneSpectrum.under_surjective`: every height one prime of `R` lies
  under one of `B`.
* `IsDedekindDomain.HeightOneSpectrum.under_under`: contraction through a tower agrees with
  direct contraction.
* `IsDedekindDomain.HeightOneSpectrum.liesOverTowerEquiv`: primes over a fixed prime correspond
  to pairs of successive primes through an intermediate integral domain.
* `IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff`: `w` lies above `S` iff
  `HeightOneSpectrum.under R w ∈ S`.
* `IsDedekindDomain.HeightOneSpectrum.primesAbove_finite`: finitely many primes lie above a
  finite set.
* `IsDedekindDomain.HeightOneSpectrum.tendsto_under_cofinite`: consequently, contraction tends to
  the cofinite filter along the cofinite filter;
  `IsDedekindDomain.HeightOneSpectrum.tendsto_under_cofinite_of_isFractionRing` is the variant
  for rings mapping compatibly to a common nontrivial algebra over a fraction field.
* `IsDedekindDomain.HeightOneSpectrum.finite_liesOver`: finitely many height one primes lie over
  a given one.

## Provenance

Adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, at commit `66889eada51a`),
`EllipticCurves/Mathlib/Basic.lean`, section `DedekindDomain`. The source carries its own
`HeightOneSpectrum.below`; at our Mathlib pin that map is `HeightOneSpectrum.under`, which is
used here instead.

The source is written against Lean `v4.32.0`; this is a forward port.
-/

public section

namespace IsDedekindDomain

variable (R : Type*) [CommRing R] (B : Type*) [CommRing B] [Algebra R B]

namespace HeightOneSpectrum

section IsDomain

variable [IsDomain R] [IsDomain B] [Algebra.IsIntegral R B]

/-- A height one prime of `B` lies over its own contraction to `R`.

Mathlib's `Ideal.over_under` is this statement for `Ideal.under`, but instance search does not see
through the `HeightOneSpectrum.asIdeal` projection to reach it, so it is registered here. Results
stated at `under R w` and consuming a `LiesOver` hypothesis, such as
`HeightOneSpectrum.valuation_liesOver`, do not fire without it. -/
instance liesOver_under (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (under R w).asIdeal :=
  ⟨under_asIdeal R w⟩

variable {R B} in
/-- A height one prime of `B` contracts to the height one prime `v` of `R` exactly when it lies
over `v`. -/
theorem under_eq_iff_liesOver {v : HeightOneSpectrum R} {w : HeightOneSpectrum B} :
    under R w = v ↔ w.asIdeal.LiesOver v.asIdeal := by
  rw [HeightOneSpectrum.ext_iff, under_asIdeal, Ideal.liesOver_iff, eq_comm]

/-- **Every height one prime of `R` lies under one of `B`**, for an integral extension of domains
with injective algebra map: contraction `HeightOneSpectrum B → HeightOneSpectrum R` is
surjective. -/
theorem under_surjective [FaithfulSMul R B] :
    Function.Surjective (under R : HeightOneSpectrum B → HeightOneSpectrum R) := by
  rintro ⟨p, hp, hp0⟩
  obtain ⟨P, hP, rfl⟩ := p.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := B)
    (by simp)
  exact ⟨⟨P, hP, fun h ↦ hp0 (by rw [h, Ideal.under_bot])⟩, rfl⟩

section UnderTower

variable {A C : Type*} [CommRing A] [CommRing C] [IsDomain C]
  [Algebra A R] [Algebra R C] [Algebra A C] [IsScalarTower A R C]
  [Algebra.IsIntegral R C]

/-- Contracting a height-one prime through an intermediate integral domain agrees with direct
contraction. -/
@[simp]
theorem under_under [IsDomain A] [Algebra.IsIntegral A R] (w : HeightOneSpectrum C) :
    letI : Algebra.IsIntegral A C := Algebra.IsIntegral.trans R
    (w.under R).under A = w.under A := by
  apply asIdeal_injective
  simp only [under_asIdeal, Ideal.under_under]

/-- Height-one primes over `v` correspond to pairs of successive height-one primes through an
intermediate integral domain. -/
def liesOverTowerEquiv (v : HeightOneSpectrum A) :
    (Σ w : {w : HeightOneSpectrum R // w.asIdeal.LiesOver v.asIdeal},
      {u : HeightOneSpectrum C // u.asIdeal.LiesOver w.1.asIdeal}) ≃
      {u : HeightOneSpectrum C // u.asIdeal.LiesOver v.asIdeal} where
  toFun p :=
    have := p.1.2
    have := p.2.2
    ⟨p.2.1, .trans p.2.1.asIdeal p.1.1.asIdeal v.asIdeal⟩
  invFun u :=
    have := u.2
    ⟨⟨u.1.under R, .tower_bot u.1.asIdeal _ v.asIdeal⟩, ⟨u.1, inferInstance⟩⟩
  left_inv := by
    rintro ⟨⟨w, hw⟩, ⟨u, hu⟩⟩
    obtain rfl := under_eq_iff_liesOver.mpr hu
    rfl
  right_inv _ := rfl

/-- `liesOverTowerEquiv` keeps the top prime of the pair. -/
@[simp]
theorem liesOverTowerEquiv_apply (v : HeightOneSpectrum A)
    (p : Σ w : {w : HeightOneSpectrum R // w.asIdeal.LiesOver v.asIdeal},
      {u : HeightOneSpectrum C // u.asIdeal.LiesOver w.1.asIdeal}) :
    (liesOverTowerEquiv (R := R) (C := C) v p).1 = p.2.1 :=
  by simp [liesOverTowerEquiv]

/-- The inverse of `liesOverTowerEquiv` passes through the contraction of `u` to `R`. -/
@[simp]
theorem liesOverTowerEquiv_symm_apply_fst (v : HeightOneSpectrum A)
    (u : {u : HeightOneSpectrum C // u.asIdeal.LiesOver v.asIdeal}) :
    ((liesOverTowerEquiv (R := R) v).symm u).1.1 = u.1.under R :=
  by simp [liesOverTowerEquiv]

/-- The inverse of `liesOverTowerEquiv` keeps `u` as the top prime. -/
@[simp]
theorem liesOverTowerEquiv_symm_apply_snd (v : HeightOneSpectrum A)
    (u : {u : HeightOneSpectrum C // u.asIdeal.LiesOver v.asIdeal}) :
    ((liesOverTowerEquiv (R := R) v).symm u).2.1 = u.1 :=
  by simp [liesOverTowerEquiv]

end UnderTower

/-- The primes of `B` lying above a set `S` of primes of `R`: the preimage of `S` under the
contraction `HeightOneSpectrum.under R`. -/
def primesAbove (S : Set (HeightOneSpectrum R)) : Set (HeightOneSpectrum B) :=
  under R ⁻¹' S

/-- A prime of `B` lies above `S` exactly when its contraction to `R` lies in `S`. -/
@[simp]
lemma mem_primesAbove_iff (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ under R w ∈ S := Iff.rfl

/-- Taking the primes above a set of primes of `R` is monotone. -/
lemma primesAbove_mono {S T : Set (HeightOneSpectrum R)} (hST : S ⊆ T) :
    primesAbove R B S ⊆ primesAbove R B T :=
  Set.preimage_mono hST

/-- No prime of `B` lies above the empty set of primes. -/
@[simp]
lemma primesAbove_empty : primesAbove R B (∅ : Set (HeightOneSpectrum R)) = ∅ :=
  Set.preimage_empty

end IsDomain

section

variable {R B}

variable (B) [FaithfulSMul R B]

/-- Only finitely many nonzero primes of a Dedekind domain `B` lie over a given nonzero
prime of `R`. The extension need not be integral, and `R` need not be Dedekind. -/
instance finite_liesOver [IsDedekindDomain B] (v : HeightOneSpectrum R) :
    Finite {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} := by
  have h := Ideal.finite_factors (Ideal.map_ne_bot_of_ne_bot (S := B) v.ne_bot)
  exact (h.subset (t := {w : HeightOneSpectrum B | w.asIdeal.LiesOver v.asIdeal}) fun w hw ↦
    Ideal.dvd_iff_le.mpr (Ideal.map_le_iff_le_comap.mpr (le_of_eq hw.over))).to_subtype

end

/-- Only finitely many primes of `B` lie above a finite set of primes of `R`. -/
lemma primesAbove_finite [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]
    [FaithfulSMul R B] {S : Set (HeightOneSpectrum R)} (hS : S.Finite) :
    (primesAbove R B S).Finite := by
  refine hS.preimage' fun v _ ↦ ?_
  simp only [Set.preimage, Set.mem_singleton_iff, under_eq_iff_liesOver]
  exact Set.finite_coe_iff.mp (finite_liesOver B v)

/-- Only finitely many primes of `B` contract to each prime of `R`, so contraction tends to the
cofinite filter along the cofinite filter. -/
lemma tendsto_under_cofinite [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]
    [FaithfulSMul R B] :
    Filter.Tendsto (under R (B := B)) Filter.cofinite Filter.cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v ↦
    (primesAbove_finite R B (Set.finite_singleton v)).to_subtype

/-- `tendsto_under_cofinite` when `R` and `B` map compatibly to a nontrivial algebra `L`
over the fraction field `K` of `R`: the tower `R → K → L` makes the algebra map `R → B`
injective. -/
lemma tendsto_under_cofinite_of_isFractionRing [IsDomain R] [IsDedekindDomain B]
    [Algebra.IsIntegral R B] (K L : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    [Semiring L] [Nontrivial L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Algebra B L] [IsScalarTower R B L] :
    Filter.Tendsto (under R (B := B)) Filter.cofinite Filter.cofinite :=
  have := FaithfulSMul.of_field_isFractionRing R B K L
  tendsto_under_cofinite R B

end HeightOneSpectrum

variable [IsDomain R] [IsDedekindDomain B] [Algebra.IsIntegral R B]

/-- The `S`-Selmer group of `L`, where `B` is a Dedekind domain with fraction field `L` and `S`
is a set of primes of `R`: the classes of `Lˣ` modulo `n`-th powers whose valuation is divisible
by `n` at every prime of `B` not lying above `S`. -/
def selmerGroupAbove (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) : Subgroup (Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range) :=
  selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n)

/-- `selmerGroupAbove` is the ordinary Selmer group taken over the primes above `S`. This is the
form in which `IsDedekindDomain.selmerGroupPi` and `selmerGroupOfEquiv`, stated in terms of
`selmerGroup`, apply to it. -/
lemma selmerGroupAbove_def (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) :
    selmerGroupAbove R B L S n =
      selmerGroup (R := B) (K := L) (S := HeightOneSpectrum.primesAbove R B S) (n := n) :=
  (rfl)

/-- A class of units lies in the Selmer group relative to `S` exactly when its
`valuationOfNeZeroMod n` is trivial at every prime of `B` not lying above `S`, i.e. `n` divides
the `w`-adic valuation there. -/
@[simp]
lemma mem_selmerGroupAbove_iff (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L]
    (S : Set (HeightOneSpectrum R)) (n : ℕ) (x : Lˣ ⧸ (powMonoidHom n : Lˣ →* Lˣ).range) :
    x ∈ selmerGroupAbove R B L S n ↔
      ∀ w ∉ HeightOneSpectrum.primesAbove R B S, w.valuationOfNeZeroMod n x = 1 :=
  Iff.rfl

end IsDedekindDomain

end
