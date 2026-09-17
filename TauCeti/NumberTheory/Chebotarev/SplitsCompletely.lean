/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
public import TauCeti.NumberTheory.NumberField.SplitsCompletely

/-!
# The completely split primes as the identity Artin fibre

Let `L / K` be a finite Galois extension of number fields. Among the fibres of the Artin class
studied in `TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet`, the fibre of the identity class
`1` is distinguished: it consists exactly of the primes of `𝓞 K` that split completely in `L`.

Two readings of membership in `frobeniusPrimeSet K L 1` are recorded. The residue-degree reading
asks for a prime `𝔭` unramified in `L`, and says that `f(Q/𝔭)` is `1` at one — hence, since
`L / K` is Galois, at every — prime `Q` of `𝓞 L` above `𝔭`. The counting reading needs no
hypothesis at all: `𝔭` carries the identity Artin class exactly when `𝓞 L` has the full
complement of `[L : K]` primes above `𝔭`.

That asymmetry is the point of the file. A full complement of primes above `𝔭` already forces
the ramification index at every prime above `𝔭` to be `1`, hence forces `𝔭` to be unramified —
that is `NumberField.isUnramifiedAt_of_ncard_primesOver_eq_finrank`, in
`TauCeti.NumberTheory.NumberField.SplitsCompletely`. So the counting characterization and its
set-level corollary both stand unconditionally, and `frobeniusPrimeSet K L 1` is the set of
completely split primes on the nose, with no finite exceptional set to discard.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one`: for `𝔭` unramified
  in `L`, membership in the identity fibre is residue degree one at a prime above `𝔭`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank`: the same
  membership, read as a count of the primes above `𝔭`.
* `NumberField.Chebotarev.inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one`: a member of the
  identity fibre has residue degree one at *every* prime above it.
* `NumberField.Chebotarev.frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank`: as a set,
  the identity fibre is the primes of `𝓞 K` with `[L : K]` primes of `𝓞 L` above them.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, where the Frobenius at an unramified
  prime is trivial exactly when that prime splits completely.
-/

public section

open Ideal
open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField

-- Source: the identity fibre of Layer 2 of `TauCetiRoadmap/Chebotarev/README.md`, which Layer 10
-- consumes to derive, rather than reprove, the density of the split-completely primes.

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

namespace Chebotarev

/-- **The identity fibre is residue degree one.** For `𝔭` unramified in `L` and `Q` a prime of
`𝓞 L` above `𝔭`, the prime `𝔭` carries the identity Artin class exactly when `f(Q/𝔭) = 1`.

The residue degree is common to all primes above `𝔭`, so the choice of `Q` is immaterial; see
`inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one`. -/
theorem mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ Q.inertiaDeg (𝓞 K) = 1 :=
  (mem_frobeniusPrimeSet_iff_artinSymbol_eq hur 1).trans
    (artinSymbol_eq_one_iff_inertiaDeg_eq_one 𝔭.asIdeal hur Q)

-- The conditional form, kept private: it is the direct specialisation of the general fibre
-- description, which carries an unramifiedness hypothesis, and the unconditional statement
-- below is derived from it by supplying that witness from each side of the iff.
private theorem mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank_of_isUnramified
    {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L :=
  (mem_frobeniusPrimeSet_iff_artinSymbol_eq hur 1).trans
    (artinSymbol_eq_one_iff_ncard_primesOver_eq_finrank 𝔭.asIdeal hur)

/-- **The identity fibre is complete splitting.** A height-one prime of `𝓞 K` carries the
identity Artin class in `L` exactly when `𝓞 L` has `[L : K]` primes above it.

No unramifiedness hypothesis is needed: complete splitting already implies it, so requiring it
separately would be redundant. -/
-- Deliberately not `@[simp]`: `mem_frobeniusPrimeSet_iff` is already `@[simp]` and rewrites this
-- left-hand side to the existential over an unramifiedness witness first, so the tag would leave
-- this out of simp-normal form and fail `simpNF`.
theorem mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank
    {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ frobeniusPrimeSet K L 1 ↔ (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L :=
  ⟨fun h ↦ (mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank_of_isUnramified
      (isUnramifiedAt_of_mem_frobeniusPrimeSet h)).mp h,
    fun hcard ↦ (mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank_of_isUnramified
      (isUnramifiedAt_of_ncard_primesOver_eq_finrank 𝔭.asIdeal hcard)).mpr hcard⟩

/-- **Residue degree one at every prime above.** A member of the identity fibre has residue
degree `1` at each prime of `𝓞 L` lying over it, not merely at one of them. -/
theorem inertiaDeg_eq_one_of_mem_frobeniusPrimeSet_one {𝔭 : HeightOneSpectrum (𝓞 K)}
    (h : 𝔭 ∈ frobeniusPrimeSet K L 1) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Q.inertiaDeg (𝓞 K) = 1 :=
  (mem_frobeniusPrimeSet_one_iff_inertiaDeg_eq_one
    (isUnramifiedAt_of_mem_frobeniusPrimeSet h) Q).mp h

/-- **The identity fibre is exactly the completely split primes.** A height-one prime of `𝓞 K`
carries the identity Artin class in `L` if and only if `𝓞 L` has `[L : K]` primes above it.

Complete splitting is therefore a fibre of the Artin class with no exceptional set attached, so
a density statement for the fibre is a density statement for the completely split primes. -/
theorem frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank :
    frobeniusPrimeSet K L 1 = {𝔭 | (𝔭.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L} :=
  Set.ext fun _ ↦ mem_frobeniusPrimeSet_one_iff_ncard_primesOver_eq_finrank

end Chebotarev

end NumberField
