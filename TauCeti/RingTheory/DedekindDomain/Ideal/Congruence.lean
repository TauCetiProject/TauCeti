/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Factorization

/-!
# Multiplicative congruence modulo an ideal

For a Dedekind domain `R` with fraction field `K`,
`Ideal.congruenceSubgroup m K hm` consists of the elements of `Kˣ`
congruent to one locally modulo the nonzero ideal `m`.
At a prime dividing `m`, the valuation of `x - 1` must be at most the negative
exponential of the multiplicity of that prime in `m`. Such an `x` is a local unit.
No condition is imposed at primes not dividing `m`; in particular, `x` need not
belong to `R`.

The subgroup decreases under divisibility of ideals. For an element that does
belong to `R`, its local congruences are equivalent to ordinary membership of
`x - 1` in `m`. On the units of `R`, the subgroup is therefore the kernel of
reduction to `(R ⧸ m)ˣ`. This finite congruence condition can be combined with positivity
at real places to define the congruence subgroup of a number-field modulus.

## Usage

Write `m.congruenceSubgroup K hm` for an ideal
`m : Ideal R` and a proof `hm : m ≠ ⊥`. The residue-unit kernel formula is
`Ideal.comap_congruenceSubgroup_eq_ker m K hm`; it is also a simp lemma.

## Dependencies and provenance

The valuation and prime-power dictionary is Mathlib's
`IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem`, and the passage
from local membership to membership in `m` uses `Ideal.iInf_maxPowDividing_eq`.

`Ideal.congruenceSubgroup` and its subgroup proofs generalize the former
number-field construction `TauCeti.GlobalNumberFields.congruenceSubgroup` in
`TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

private theorem valuation_eq_one_of_congruence_bound {m : Ideal R} (hm : m ≠ ⊥)
    {x : Kˣ} (hx : ∀ v : HeightOneSpectrum R, v.asIdeal ∣ m →
      v.valuation K ((x : K) - 1) ≤
        WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk m).factors : ℤ)))
    {v : HeightOneSpectrum R} (hv : v.asIdeal ∣ m) : v.valuation K (x : K) = 1 := by
  have hpos : 0 < (Associates.mk v.asIdeal).count (Associates.mk m).factors :=
    Nat.pos_of_ne_zero ((Associates.count_ne_zero_iff_dvd hm v.irreducible).mpr hv)
  have hlt := (hx v hv).trans_lt
    (WithZero.exp_lt_one_iff.mpr (neg_neg_iff_pos.mpr (Int.natCast_pos.mpr hpos)))
  simpa only [add_sub_cancel] using Valuation.map_one_add_of_lt (v.valuation K) hlt

/-- The subgroup of fraction-field units congruent to one locally modulo a nonzero
ideal. Only primes dividing the ideal impose a condition. -/
def congruenceSubgroup (m : Ideal R) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (hm : m ≠ ⊥) : Subgroup Kˣ := by
  let P (x : Kˣ) := ∀ v : HeightOneSpectrum R, v.asIdeal ∣ m →
    v.valuation K ((x : K) - 1) ≤
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk m).factors : ℤ))
  exact {
    carrier := P
    one_mem' := by intro v hv; simp
    mul_mem' := by
      intro x y hx hy v hv
      have hxy : ((x * y : Kˣ) : K) - 1 = (x : K) * ((y : K) - 1) + ((x : K) - 1) := by
        push_cast
        ring
      refine (hxy ▸ Valuation.map_add (v.valuation K) _ _).trans (max_le ?_ (hx v hv))
      rw [map_mul, valuation_eq_one_of_congruence_bound hm hx hv, one_mul]
      exact hy v hv
    inv_mem' := by
      intro x hx v hv
      have hxy : ((x⁻¹ : Kˣ) : K) - 1 = -(((x : K) - 1) * (x : K)⁻¹) := by
        rw [Units.val_inv_eq_inv_val]
        field_simp
        ring
      rw [hxy, Valuation.map_neg, map_mul, map_inv₀,
        valuation_eq_one_of_congruence_bound hm hx hv, inv_one, mul_one]
      exact hx v hv }

/-- Membership is the valuation bound at every prime divisor of the ideal. -/
@[simp]
theorem mem_congruenceSubgroup_iff {m : Ideal R} {hm : m ≠ ⊥} {x : Kˣ} :
    x ∈ congruenceSubgroup m K hm ↔
      ∀ v : HeightOneSpectrum R, v.asIdeal ∣ m →
        v.valuation K ((x : K) - 1) ≤
          WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk m).factors : ℤ)) :=
  Iff.rfl

/-- A fraction-field unit congruent to one is a local unit at every prime dividing the ideal. -/
theorem valuation_eq_one_of_mem_congruenceSubgroup {m : Ideal R} {hm : m ≠ ⊥}
    {x : Kˣ} (hx : x ∈ congruenceSubgroup m K hm) {v : HeightOneSpectrum R}
    (hv : v.asIdeal ∣ m) : v.valuation K (x : K) = 1 :=
  valuation_eq_one_of_congruence_bound hm (mem_congruenceSubgroup_iff.mp hx) hv

/-- Congruence modulo a multiple implies congruence modulo a divisor. -/
theorem congruenceSubgroup_antitone {m n : Ideal R} {hm : m ≠ ⊥} {hn : n ≠ ⊥}
    (h : m ∣ n) : congruenceSubgroup n K hn ≤ congruenceSubgroup m K hm := by
  intro x hx
  refine mem_congruenceSubgroup_iff.mpr fun v hv ↦ ?_
  refine (mem_congruenceSubgroup_iff.mp hx v (hv.trans h)).trans
    (WithZero.exp_le_exp.mpr (neg_le_neg (Int.ofNat_le.mpr ?_)))
  exact Associates.count_le_count_of_le (Associates.mk_ne_zero.mpr hn)
    (Associates.irreducible_mk.mpr v.irreducible) (Associates.mk_le_mk_of_dvd h)

/-- The unit ideal imposes no multiplicative congruence condition. -/
@[simp]
theorem congruenceSubgroup_top :
    congruenceSubgroup (⊤ : Ideal R) K top_ne_bot = ⊤ := by
  apply (Subgroup.eq_top_iff' _).mpr
  intro x
  exact mem_congruenceSubgroup_iff.mpr fun v hv ↦
    (v.isPrime.ne_top (top_le_iff.mp (Ideal.dvd_iff_le.mp hv))).elim

/-- For a fraction-field unit represented by a base-ring element, local congruence is ordinary
congruence: its representative minus one belongs to the ideal. -/
theorem mem_congruenceSubgroup_iff_sub_one_mem {m : Ideal R} {hm : m ≠ ⊥}
    {x : Kˣ} {a : R} (hxa : (x : K) = algebraMap R K a) :
    x ∈ congruenceSubgroup m K hm ↔ a - 1 ∈ m := by
  have hsub : (x : K) - 1 = algebraMap R K (a - 1) := by
    rw [map_sub, map_one, hxa]
  rw [mem_congruenceSubgroup_iff]
  simp only [hsub, valuation_of_algebraMap, intValuation_le_pow_iff_mem]
  constructor
  · intro h
    rw [← Ideal.iInf_maxPowDividing_eq hm, Submodule.mem_iInf]
    intro v
    by_cases hv : v.asIdeal ∣ m
    · exact h v hv
    · have hzero : (Associates.mk v.asIdeal).count (Associates.mk m).factors = 0 := by
        by_contra hne
        exact hv ((Associates.count_ne_zero_iff_dvd hm v.irreducible).mp hne)
      -- Mathlib defines maxPowDividing by this prime power.
      rw [maxPowDividing, hzero, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  · intro h v _
    exact ((le_count_associates_iff_le_pow v hm _).mp le_rfl) h

/-- On base-ring units, finite multiplicative congruence is the kernel of reduction
to the units of the quotient ring. -/
@[simp]
theorem comap_congruenceSubgroup_eq_ker (m : Ideal R) (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] (hm : m ≠ ⊥) :
    (congruenceSubgroup m K hm).comap (Units.map (algebraMap R K)) =
      (Units.map (Ideal.Quotient.mk m).toMonoidHom).ker := by
  ext u
  rw [Subgroup.mem_comap,
    mem_congruenceSubgroup_iff_sub_one_mem (a := (u : R)) (by simp),
    MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  exact (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := m) (u : R)).symm

end Ideal
