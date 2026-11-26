/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum

/-!
# Finite ideles of a Dedekind domain with finite class group

Let `R` be a Dedekind domain with fraction field `K`. The divisor map
`IsDedekindDomain.FiniteAdeleRing.toFractionalIdeal` sends a finite idele `x` to the invertible
fractional ideal `∏_v v ^ ord_v(x)`; its kernel is the group `integralUnits R K` of
everywhere-integral units, it sends the principal finite idele of `a ∈ Kˣ` to `(a)`, and its
composite with the class group has kernel `integralUnits R K ⊔ Kˣ`
(`IsDedekindDomain.FiniteAdeleRing.ker_toClassGroup`). This file adds the consequences of
finiteness of the class group: the `h`-th power of every finite idele lies in
`Kˣ · integralUnits R K`, where `h` is the class number, and for finite sets `S`, `S'` of places
there is a finite set `T ⊇ S` that meets `S'` only inside `S` with `Kˣ · U^T = 𝔸_{K,f}ˣ`, where
`U^T` is the group `sIntegralUnits R K T` of finite ideles that are local units outside `T`.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.pow_card_classGroup_mem`: `x ^ h ∈ integralUnits ⊔ Kˣ` for
  every finite idele `x`, with `h = Nat.card (ClassGroup R)`.
* `IsDedekindDomain.FiniteAdeleRing.finiteIndex_integralUnits_sup_range_unitEmbedding`:
  `integralUnits ⊔ Kˣ` has finite index.
* `IsDedekindDomain.FiniteAdeleRing.exists_finite_sIntegralUnits_sup_range_unitEmbedding_eq_top`:
  the set `T` above.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `src/Lib/ClassField/Places/Ideles.lean`: `New.pow_classNumber_mem_principal_sup` and
`New.exists_sup_idelesUnitOff_eq_top`. The construction of `T` here goes through ideal classes
coprime to a given ideal (`ClassGroup.exists_mk0_eq_and_isCoprime`) rather than through the
density of `K` in the finite adeles: each ideal class contains an integral ideal prime to the
places of `S'`, and `T` is `S` together with the prime factors of these finitely many ideals.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §16.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-! ### Finite class group -/

variable (K) in
/-- **The class number kills the finite ideles modulo `Kˣ · 𝒪̂ˣ`**: the `h`-th power of a finite
idele, `h` the class number, is an everywhere-integral unit times a principal finite idele. With
an infinite class group, `Nat.card` is `0` and the statement is trivial. -/
theorem pow_card_classGroup_mem (x : 𝔸ᶠ[R, K]ˣ) :
    x ^ Nat.card (ClassGroup R) ∈ integralUnits R K ⊔ (unitEmbedding R K).range := by
  rw [← ker_toClassGroup, MonoidHom.mem_ker, map_pow, pow_card_eq_one']

section FiniteClassGroup

variable [Finite (ClassGroup R)]

variable (R K) in
/-- The everywhere-integral units and the principal finite ideles together have finite index in
the finite ideles: the quotient is the class group. -/
theorem finiteIndex_integralUnits_sup_range_unitEmbedding :
    (integralUnits R K ⊔ (unitEmbedding R K).range).FiniteIndex := by
  rw [← ker_toClassGroup]
  infer_instance

variable (K) in
/-- **Enlarging a finite set of places so that `Kˣ · U^T` is everything.** For finite sets `S`
and `S'` of places there is a finite set `T ⊇ S`, meeting `S'` only inside `S`, such that every
finite idele is a principal finite idele times a finite idele that is a local unit outside `T`. -/
theorem exists_finite_sIntegralUnits_sup_range_unitEmbedding_eq_top
    {S S' : Set (HeightOneSpectrum R)} (hS : S.Finite) (hS' : S'.Finite) :
    ∃ T : Set (HeightOneSpectrum R), T.Finite ∧ S ⊆ T ∧ T ∩ S' ⊆ S ∧
      sIntegralUnits R K T ⊔ (unitEmbedding R K).range = ⊤ := by
  classical
  -- Each ideal class contains an integral ideal prime to the places of `S'`
  -- (`ClassGroup.exists_mk0_eq_and_isCoprime`); `T` is `S` together with the prime factors of
  -- these finitely many ideals. `J` is the product of the primes of `S'`.
  set J : Ideal R := ∏ v ∈ hS'.toFinset, v.asIdeal
  have hJ : J ≠ ⊥ := Finset.prod_ne_zero_iff.mpr fun v _ ↦ v.ne_bot
  choose I hI using fun c : ClassGroup R ↦ c.exists_mk0_eq_and_isCoprime hJ
  have hI0 (c : ClassGroup R) : (I c : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero (I c)
  let T : Set (HeightOneSpectrum R) := S ∪ ⋃ c, {v | v.asIdeal ∣ (I c : Ideal R)}
  refine ⟨T, hS.union (Set.finite_iUnion fun c ↦ Ideal.finite_factors (hI0 c)),
    Set.subset_union_left, ?_, ?_⟩
  · -- A prime of `S'` contains `J`, so it cannot divide an ideal coprime to `J`.
    rintro v ⟨hvS | hvI, hvS'⟩
    · exact hvS
    obtain ⟨c, hvc⟩ := Set.mem_iUnion.mp hvI
    have hJv : J ≤ v.asIdeal :=
      Ideal.prod_le_inf.trans (Finset.inf_le (hS'.mem_toFinset.mpr hvS'))
    have htop := (Ideal.isCoprime_iff_sup_eq.mp (hI c).2).symm.le
    exact absurd (top_le_iff.mp (htop.trans (sup_le (Ideal.le_of_dvd hvc) hJv)))
      v.isPrime.ne_top
  · -- Every ideal class is generated by the classes of the primes of `T`.
    rw [sIntegralUnits_sup_range_unitEmbedding_eq_top_iff, eq_top_iff]
    intro c _
    rw [← (hI c).1, ← ClassGroup.mk_mk0 K]
    refine ClassGroup.mk_mem_closure_of_count_eq_zero fun v hv ↦ ?_
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.count_coeIdeal_eq_zero_iff (hI0 c)]
    exact fun h ↦ hv (Or.inr (Set.mem_iUnion.mpr ⟨c, h⟩))

end FiniteClassGroup

end IsDedekindDomain.FiniteAdeleRing
