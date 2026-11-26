/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology
import TauCeti.RingTheory.ClassGroup.HeightOneSpectrum

/-!
# Finite ideles of a Dedekind domain with finite class group

Let `R` be a Dedekind domain with fraction field `K`. The divisor map
`IsDedekindDomain.FiniteAdeleRing.toFractionalIdeal` sends a finite idele `x` to the invertible
fractional ideal `∏_v v ^ ord_v(x)`; its kernel is the group `integralUnits R K` of
everywhere-integral units, it sends the principal finite idele of `a ∈ Kˣ` to `(a)`, and its
composite with the class group has kernel `integralUnits R K ⊔ Kˣ`
(`IsDedekindDomain.FiniteAdeleRing.ker_toClassGroup`). This file adds the value of the divisor map
on the finite idele concentrated at one place, and the consequences of finiteness of the class
group: the `h`-th power of every finite idele lies in `Kˣ · integralUnits R K`, where `h` is the
class number, and for finite sets `S`, `S'` of places there is a finite set `T ⊇ S` that meets
`S'` only inside `S` with `Kˣ · U^T = 𝔸_{K,f}ˣ`, where `U^T` is the group
`sIntegralUnits R K T` of finite ideles that are local units outside `T`.

Finally, every open subgroup of the finite ideles contains the local units `𝒪_vˣ`, placed at `v`,
for all but finitely many places `v`. Applied to
the kernel of a homomorphism, this says that a character of the finite ideles with open kernel is
unramified at almost every place.

## Main results

* `IsDedekindDomain.FiniteAdeleRing.toFractionalIdeal_unitsOfAdicCompletion`: the divisor of the
  finite idele with coordinate `u` at `v` and `1` elsewhere is `v ^ ord_v(u)`; for a uniformizer
  it is `v` (`toFractionalIdeal_unitsOfAdicCompletion_of_valued_eq_exp_neg_one`).
* `IsDedekindDomain.FiniteAdeleRing.pow_card_classGroup_mem`: `x ^ h ∈ integralUnits ⊔ Kˣ` for
  every finite idele `x`, with `h = Nat.card (ClassGroup R)`.
* `IsDedekindDomain.FiniteAdeleRing.finiteIndex_integralUnits_sup_range`: `integralUnits ⊔ Kˣ` has
  finite index.
* `IsDedekindDomain.FiniteAdeleRing.exists_finite_sIntegralUnits_sup_range_eq_top`: the set `T`
  above.
* `IsDedekindDomain.FiniteAdeleRing.eventually_unitsOfAdicCompletion_mem_of_isOpen`: an open
  subgroup contains the local units at almost every place.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic
PBC), file `src/Lib/ClassField/Places/Ideles.lean`: `New.exists_idele_divisor_hom` (clause (c)),
`New.pow_classNumber_mem_principal_sup`, `New.exists_sup_idelesUnitOff_eq_top` and
`New.eventually_unramified`. The construction of `T` here goes through ideal classes coprime to a
given ideal (`ClassGroup.exists_mk0_eq_and_isCoprime`) rather than through the density of `K` in
the finite adeles, and the last result uses the product topology on the everywhere-integral units
instead of their compactness, so it holds for every Dedekind domain.

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

/-! ### The divisor of a finite idele concentrated at one place -/

/-- The fractional ideal of the finite idele with coordinate `u` at `v` and `1` elsewhere is the
power of `v` given by the order of `u`. -/
@[simp]
theorem toFractionalIdeal_unitsOfAdicCompletion (v : HeightOneSpectrum R)
    (u : (v.adicCompletion K)ˣ) :
    toFractionalIdeal (unitsOfAdicCompletion K v u) =
      v.unitOfPrime K ^ (-WithZero.log (Valued.v (u : v.adicCompletion K))) := by
  classical
  rw [toFractionalIdeal_apply, finprod_eq_single _ v fun w hw ↦ ?_]
  · rw [adicOrd_def, ← coe_unitsProj_apply, unitsProj_unitsOfAdicCompletion]
  · rw [adicOrd_def, ← coe_unitsProj_apply, unitsProj_unitsOfAdicCompletion_of_ne hw,
      Units.val_one, map_one, WithZero.log_one, neg_zero, zpow_zero]

/-- The fractional ideal of the finite idele with a uniformizer `u` at `v` and `1` elsewhere is
the prime `v`. -/
theorem toFractionalIdeal_unitsOfAdicCompletion_of_valued_eq_exp_neg_one
    (v : HeightOneSpectrum R) {u : (v.adicCompletion K)ˣ}
    (hu : Valued.v (u : v.adicCompletion K) = WithZero.exp (-1)) :
    toFractionalIdeal (unitsOfAdicCompletion K v u) = v.unitOfPrime K := by
  rw [toFractionalIdeal_unitsOfAdicCompletion, hu, WithZero.log_exp, neg_neg, zpow_one]

/-! ### Finite class group -/

variable (K) in
/-- **The class number kills the finite ideles modulo `Kˣ · 𝒪̂ˣ`**: the `h`-th power of a finite
idele, `h` the class number, is an everywhere-integral unit times a principal finite idele. With
an infinite class group, `Nat.card` is `0` and the statement is trivial. -/
theorem pow_card_classGroup_mem (x : 𝔸ᶠ[R, K]ˣ) :
    x ^ Nat.card (ClassGroup R) ∈ integralUnits R K ⊔ (unitEmbedding R K).range := by
  rw [← ker_toClassGroup, MonoidHom.mem_ker, map_pow, pow_card_eq_one']

/-- The multiplicity of a prime `v` in a nonzero ideal not divisible by `v` is zero. -/
private theorem count_coeIdeal_eq_zero_of_not_dvd {v : HeightOneSpectrum R} {I : Ideal R}
    (hI : I ≠ 0) (hv : ¬v.asIdeal ∣ I) :
    FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) = 0 := by
  classical
  rw [FractionalIdeal.count_coeIdeal K v hI, Nat.cast_eq_zero]
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd hI v.irreducible).mp h)

section FiniteClassGroup

variable [Finite (ClassGroup R)]

variable (R K) in
/-- The everywhere-integral units and the principal finite ideles together have finite index in
the finite ideles: the quotient is the class group. -/
theorem finiteIndex_integralUnits_sup_range :
    (integralUnits R K ⊔ (unitEmbedding R K).range).FiniteIndex := by
  rw [← ker_toClassGroup]
  infer_instance

variable (K) in
/-- **Enlarging a finite set of places so that `Kˣ · U^T` is everything.** For finite sets `S`
and `S'` of places there is a finite set `T ⊇ S`, meeting `S'` only inside `S`, such that every
finite idele is a principal finite idele times a finite idele that is a local unit outside `T`.

Each ideal class contains an integral ideal prime to the places of `S'`
(`ClassGroup.exists_mk0_eq_and_isCoprime`); `T` is `S` together with the prime factors of these
finitely many ideals. -/
theorem exists_finite_sIntegralUnits_sup_range_eq_top {S S' : Set (HeightOneSpectrum R)}
    (hS : S.Finite) (hS' : S'.Finite) :
    ∃ T : Set (HeightOneSpectrum R), T.Finite ∧ S ⊆ T ∧ T ∩ S' ⊆ S ∧
      sIntegralUnits R K T ⊔ (unitEmbedding R K).range = ⊤ := by
  classical
  -- `J` is the product of the primes of `S'`.
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
    rw [FractionalIdeal.coe_mk0]
    exact count_coeIdeal_eq_zero_of_not_dvd (hI0 c)
      fun h ↦ hv (Or.inr (Set.mem_iUnion.mpr ⟨c, h⟩))

end FiniteClassGroup

/-! ### Open subgroups contain almost all local unit groups -/

/-- The coordinates of the finite idele concentrated at `v` with coordinate `u`: `u` at `v` and
`1` elsewhere. -/
private theorem unitsContinuousMulEquiv_unitsOfAdicCompletion_of_ne {v w : HeightOneSpectrum R}
    (h : w ≠ v) (u : (v.adicCompletion K)ˣ) :
    unitsContinuousMulEquiv R K (unitsOfAdicCompletion K v u) w = 1 :=
  Units.ext (by rw [coe_unitsContinuousMulEquiv_apply, ← coe_unitsProj_apply,
    unitsProj_unitsOfAdicCompletion_of_ne h, Units.val_one])

/-- **An open subgroup of the finite ideles contains the local units at almost every place**: for
all but finitely many `v`, every finite idele that is a unit `u` of `𝒪_v` at `v` and `1` elsewhere
lies in `H`. Applied to the kernel of a homomorphism, a character of the finite ideles with open
kernel is trivial on `𝒪_vˣ` for almost every `v`.

The everywhere-integral units carry the product topology of `∏_v K_vˣ`
(`IsDedekindDomain.FiniteAdeleRing.isEmbedding_coe_sIntegralUnits`), so `H` contains every
everywhere-integral unit whose coordinates are `1` on some finite set of places. -/
theorem eventually_unitsOfAdicCompletion_mem_of_isOpen {H : Subgroup 𝔸ᶠ[R, K]ˣ}
    (hH : IsOpen (H : Set 𝔸ᶠ[R, K]ˣ)) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, ∀ u : (v.adicCompletion K)ˣ,
      Valued.v (u : v.adicCompletion K) = 1 → unitsOfAdicCompletion K v u ∈ H := by
  -- the coordinate map of the everywhere-integral units into `∏_v K_vˣ`
  let f (x : sIntegralUnits R K ∅) : ∀ v : HeightOneSpectrum R, (v.adicCompletion K)ˣ :=
    unitsContinuousMulEquiv R K x
  obtain ⟨O, hO, hOH⟩ := (isEmbedding_coe_sIntegralUnits (R := R) (K := K)
    Set.finite_empty).isOpen_iff.mp (hH.preimage continuous_subtypeVal)
  have hf (x : sIntegralUnits R K ∅) : f x ∈ O ↔ (x : 𝔸ᶠ[R, K]ˣ) ∈ H :=
    Set.ext_iff.mp hOH x
  have h1 : f 1 ∈ O := (hf 1).mpr H.one_mem
  obtain ⟨I, t, ht, hIO⟩ := isOpen_pi_iff.mp hO _ h1
  filter_upwards [I.eventually_cofinite_notMem] with v hv u hu
  have hx : unitsOfAdicCompletion K v u ∈ sIntegralUnits R K ∅ := by
    rw [sIntegralUnits_empty]
    exact unitsOfAdicCompletion_mem_integralUnits_iff.mpr hu
  -- the coordinates of the idele are `1` on `I`, so it lies in the cylinder inside `O`
  refine (hf ⟨_, hx⟩).mp (hIO fun w hw ↦ ?_)
  have hw1 := (ht w hw).2
  simp only [f, OneMemClass.coe_one, map_one, RestrictedProduct.one_apply] at hw1
  simpa only [f, unitsContinuousMulEquiv_unitsOfAdicCompletion_of_ne (ne_of_mem_of_not_mem hw hv)]
    using hw1

end IsDedekindDomain.FiniteAdeleRing
