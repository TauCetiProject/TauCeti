/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.IntermediateField.Quadratic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.SqrtFive
import Mathlib.FieldTheory.Relrank
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.NormNum.Prime
import TauCeti.Algebra.Squarefree
import TauCeti.NumberTheory.Cyclotomic.Adjoin
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank

/-!
# A fifth cyclotomic field meets `ℚ(√5, √2)` in `ℚ(√5)`

A fifth cyclotomic field has a unique quadratic subfield, namely `ℚ(√5)`. In particular it
contains no square root of `2`, and therefore the biquadratic field `ℚ(√5, √2)` meets `ℚ(ζ₅)`
in exactly `ℚ(√5)`. Read over the base `K = ℚ(√5)`: the quadratic extension `K(√2)` and the
cyclotomic extension `K(ζ₅)` intersect in `K` alone.

That trivial intersection carries no information about the cyclotomic degree over `K`. Here `Φ₅`
is reducible over `K = ℚ(√5)`, by `Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five`,
and indeed `[K(ζ₅) : K] = 2` rather than `φ(5) = 4`: the degree `[K(ζ_q) : K]` is governed by
`K ∩ ℚ(ζ_q)`, not by the intersection of `ℚ(ζ_q)` with a further extension of `K`. What does
force the full degree is that `q` be unramified in `K`, which is
`IsCyclotomicExtension.irreducible_cyclotomic_of_unramified`; the configuration here is outside
its reach because `5` ramifies in `ℚ(√5)`.

## Main results

* `TauCeti.NumberField.not_isSquare_two_fifthCyclotomic`: `2` is not a square in a fifth
  cyclotomic field.
* `TauCeti.NumberField.mem_adjoin_primitiveRoot_of_sq_eq_five`: every square root of `5` lies in
  `ℚ(ζ₅)`.
* `TauCeti.NumberField.adjoin_inf_adjoin_eq_adjoin_of_sq_eq_two`: `ℚ(√5, √2) ⊓ ℚ(ζ₅) = ℚ(√5)`.
* `TauCeti.NumberField.adjoin_inf_adjoin_eq_bot_of_sq_eq_two`: the same intersection over the
  base `ℚ(√5)`, where it is `⊥`.
* `TauCeti.NumberField.finrank_adjoin_primitiveRoot_eq_two_of_sq_eq_five`:
  `[ℚ(√5)(ζ₅) : ℚ(√5)] = 2`.
* `TauCeti.NumberField.adjoin_inf_adjoin_exp_eq_adjoin`: the configuration realised in `ℂ`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 1, for the quadratic subfield of
  `ℚ(ζ₅)`.
-/

public section

open IntermediateField
open scoped NumberField

namespace TauCeti.NumberField

private theorem prime_five_int : Prime (5 : ℤ) := by norm_num

/-- Ten is not a rational square, in the shape the square-class comparison of two quadratic
subfields produces it. -/
private theorem not_isSquare_two_mul_five : ¬ IsSquare (((2 : ℤ) : ℚ) * ((5 : ℤ) : ℚ)) := by
  have hsf : Squarefree ((2 : ℤ) * 5) := squarefree_mul_iff.mpr
    ⟨(Int.isCoprime_iff_gcd_eq_one.mpr (by decide)).isRelPrime, Int.prime_two.squarefree,
      prime_five_int.squarefree⟩
  rw [← Int.cast_mul]
  exact not_isSquare_intCast_of_squarefree_of_ne_one hsf (by decide)

/-- The square root of two generates a quadratic extension of `ℚ`. -/
private theorem finrank_adjoin_of_sq_eq_two {L : Type*} [Field L] [Algebra ℚ L] {x : L}
    (hx : x ^ 2 = algebraMap ℚ L ((2 : ℤ) : ℚ)) : Module.finrank ℚ ℚ⟮x⟯ = 2 :=
  TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare hx
    (not_isSquare_intCast_of_squarefree_of_ne_one Int.prime_two.squarefree (by decide))

/-- The square root of five generates a quadratic extension of `ℚ`. -/
private theorem finrank_adjoin_of_sq_eq_five {L : Type*} [Field L] [Algebra ℚ L] {x : L}
    (hx : x ^ 2 = algebraMap ℚ L ((5 : ℤ) : ℚ)) : Module.finrank ℚ ℚ⟮x⟯ = 2 :=
  TauCeti.IntermediateField.finrank_adjoin_simple_eq_two_of_not_isSquare hx
    (not_isSquare_intCast_of_squarefree_of_ne_one prime_five_int.squarefree (by decide))

/-- **Two is not a square in a fifth cyclotomic field.** The unique quadratic subfield is
`ℚ(√5)`, and `ℚ(√2) ≠ ℚ(√5)` because `10` is not a rational square. -/
theorem not_isSquare_two_fifthCyclotomic {K : Type*} [Field K] [_root_.NumberField K]
    [IsCyclotomicExtension {5} ℚ K] : ¬ IsSquare (2 : K) := by
  rintro ⟨x, hx⟩
  have hx2 : x ^ 2 = algebraMap ℚ K ((2 : ℤ) : ℚ) := by rw [sq, ← hx]; simp
  have hxdeg : Module.finrank ℚ ℚ⟮x⟯ = 2 := finrank_adjoin_of_sq_eq_two hx2
  obtain ⟨ζ, hζ⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot (S := {5}) ℚ K (Set.mem_singleton _) (by norm_num)
  have hs2 : (1 + 2 * (ζ + ζ⁻¹) : K) ^ 2 = algebraMap ℚ K ((5 : ℤ) : ℚ) := by
    rw [hζ.one_add_two_mul_add_inv_sq_of_five]; simp
  -- Both `ℚ(√2)` and `ℚ(√5)` are the unique quadratic subfield, so they agree.
  have hxq : ℚ⟮x⟯ = ℚ⟮(1 + 2 * (ζ + ζ⁻¹) : K)⟯ :=
    (ℚ⟮x⟯.eq_fifthCyclotomicQuadraticSubfield_of_finrank_eq_two hxdeg).trans
      (adjoin_sqrt_five_eq_fifthCyclotomicQuadraticSubfield
        hζ.one_add_two_mul_add_inv_sq_of_five).symm
  -- A quadratic `ℚ⟮x⟯` puts `x` outside `ℚ`, since `x ∈ ℚ` would make that degree `1`.
  exact not_isSquare_two_mul_five
    (TauCeti.IntermediateField.isSquare_mul_of_adjoin_simple_eq hx2 hs2
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.not.mp (by omega)) hxq)

variable {Ω : Type*} [Field Ω] [CharZero Ω] {a b ζ : Ω}

/-- **Every square root of five lies in a fifth cyclotomic field.** The explicit root is
`1 + 2 * (ζ + ζ⁻¹)`, and the two square roots of `5` differ only by a sign. -/
theorem mem_adjoin_primitiveRoot_of_sq_eq_five (hb : b ^ 2 = 5) (hζ : IsPrimitiveRoot ζ 5) :
    b ∈ ℚ⟮ζ⟯ := by
  have hζmem : ζ ∈ ℚ⟮ζ⟯ := IntermediateField.mem_adjoin_simple_self ℚ ζ
  have hsmem : (1 + 2 * (ζ + ζ⁻¹) : Ω) ∈ ℚ⟮ζ⟯ :=
    add_mem (one_mem _) (mul_mem (by simp) (add_mem hζmem (inv_mem hζmem)))
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp
      (hb.trans hζ.one_add_two_mul_add_inv_sq_of_five.symm) with h | h
  · exact h ▸ hsmem
  · exact h ▸ neg_mem hsmem

/-- `√2` does not lie in `ℚ(√5)`: two square roots generating the same quadratic field have
radicands in one square class, and `2 * 5` is not a rational square. -/
private theorem notMem_adjoin_of_sq_eq_two_of_sq_eq_five (ha : a ^ 2 = 2) (hb : b ^ 2 = 5) :
    a ∉ ℚ⟮b⟯ := by
  have ha' : a ^ 2 = algebraMap ℚ Ω ((2 : ℤ) : ℚ) := by rw [ha]; simp
  have hb' : b ^ 2 = algebraMap ℚ Ω ((5 : ℤ) : ℚ) := by rw [hb]; simp
  have hadeg : Module.finrank ℚ ℚ⟮a⟯ = 2 := finrank_adjoin_of_sq_eq_two ha'
  have : FiniteDimensional ℚ ℚ⟮b⟯ :=
    Module.finite_of_finrank_pos (by rw [finrank_adjoin_of_sq_eq_five hb']; norm_num)
  intro hmem
  have heq : ℚ⟮a⟯ = ℚ⟮b⟯ :=
    IntermediateField.eq_of_le_of_finrank_eq (IntermediateField.adjoin_simple_le_iff.mpr hmem)
      (by rw [hadeg, finrank_adjoin_of_sq_eq_five hb'])
  -- A quadratic `ℚ⟮a⟯` puts `a` outside `ℚ`, since `a ∈ ℚ` would make that degree `1`.
  exact not_isSquare_two_mul_five
    (TauCeti.IntermediateField.isSquare_mul_of_adjoin_simple_eq ha' hb'
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.not.mp (by omega)) heq)

/-- **`ℚ(√5, √2)` meets a fifth cyclotomic field in `ℚ(√5)`.** -/
theorem adjoin_inf_adjoin_eq_adjoin_of_sq_eq_two (ha : a ^ 2 = 2) (hb : b ^ 2 = 5)
    (hζ : IsPrimitiveRoot ζ 5) : ℚ⟮b, a⟯ ⊓ ℚ⟮ζ⟯ = ℚ⟮b⟯ := by
  have hb' : b ^ 2 = algebraMap ℚ Ω ((5 : ℤ) : ℚ) := by rw [hb]; simp
  have hbdeg : Module.finrank ℚ ℚ⟮b⟯ = 2 := finrank_adjoin_of_sq_eq_five hb'
  have hζdeg : Module.finrank ℚ ℚ⟮ζ⟯ = 4 := by
    rw [hζ.finrank_adjoin_eq_totient, Nat.totient_prime (by norm_num : Nat.Prime 5)]
  have : FiniteDimensional ℚ ℚ⟮b⟯ := Module.finite_of_finrank_pos (by rw [hbdeg]; norm_num)
  have : FiniteDimensional ℚ ℚ⟮ζ⟯ := Module.finite_of_finrank_pos (by rw [hζdeg]; norm_num)
  have hsup : ℚ⟮b, a⟯ = ℚ⟮b⟯ ⊔ ℚ⟮a⟯ := by
    rw [← Set.singleton_union, IntermediateField.adjoin_union]
  have hbadeg : Module.finrank ℚ ℚ⟮b, a⟯ = 4 := by
    rw [hsup, IntermediateField.finrank_sup_adjoin_simple_eq_mul_two ℚ⟮b⟯ (by rw [ha]; simp)
      (notMem_adjoin_of_sq_eq_two_of_sq_eq_five ha hb), hbdeg]
  have : FiniteDimensional ℚ ℚ⟮b, a⟯ := Module.finite_of_finrank_pos (by rw [hbadeg]; norm_num)
  have hble : ℚ⟮b⟯ ≤ ℚ⟮ζ⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (mem_adjoin_primitiveRoot_of_sq_eq_five hb hζ)
  -- `ℚ(ζ₅)` is quadratic over `ℚ(√5)`, so the intersection is one of the two ends of that step.
  have hrel : ℚ⟮b⟯.relfinrank ℚ⟮ζ⟯ = 2 := by
    have h := IntermediateField.finrank_bot_mul_relfinrank hble
    rw [hbdeg, hζdeg] at h
    omega
  set E := ℚ⟮b, a⟯ ⊓ ℚ⟮ζ⟯
  have hEζ : E ≤ ℚ⟮ζ⟯ := inf_le_right
  have hbE : ℚ⟮b⟯ ≤ E := le_inf (hsup ▸ le_sup_left) hble
  have hsplit : ℚ⟮b⟯.relfinrank E * E.relfinrank ℚ⟮ζ⟯ = 2 :=
    (IntermediateField.relfinrank_mul_relfinrank hbE hEζ).trans hrel
  have hcase : ℚ⟮b⟯.relfinrank E = 1 ∨ E.relfinrank ℚ⟮ζ⟯ = 1 := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ ⟨_, hsplit.symm⟩ with h | h
    · exact Or.inl h
    · rw [h] at hsplit
      exact Or.inr (by omega)
  rcases hcase with h | h
  · exact le_antisymm (IntermediateField.relfinrank_eq_one_iff.mp h) hbE
  · -- The other case forces `ℚ(ζ₅) = ℚ(√5, √2)`, hence `√2 ∈ ℚ(ζ₅)`.
    exfalso
    have hζba : ℚ⟮ζ⟯ = ℚ⟮b, a⟯ :=
      IntermediateField.eq_of_le_of_finrank_eq
        ((IntermediateField.relfinrank_eq_one_iff.mp h).trans inf_le_left)
        (by rw [hζdeg, hbadeg])
    have hamem : a ∈ ℚ⟮ζ⟯ := by
      rw [hζba]
      exact IntermediateField.subset_adjoin ℚ _ (by simp)
    have : IsCyclotomicExtension {5} ℚ ℚ⟮ζ⟯ := hζ.isCyclotomicExtension_adjoin_singleton
    have : _root_.NumberField ℚ⟮ζ⟯ := ⟨⟩
    -- Mathlib has no `coe_ofNat` lemma for intermediate fields: the two numerals are the same
    -- underlying element of `Ω` by definition of the numeral on the subtype.
    have hcoe : ((2 : ℚ⟮ζ⟯) : Ω) = 2 := rfl
    have hsq : ((⟨a, hamem⟩ : ℚ⟮ζ⟯) * ⟨a, hamem⟩ : ℚ⟮ζ⟯) = 2 := by
      apply Subtype.ext
      push_cast
      rw [← sq, ha, hcoe]
    exact not_isSquare_two_fifthCyclotomic (K := ℚ⟮ζ⟯) ⟨_, hsq.symm⟩

/-- **`K(√2)` and `K(ζ₅)` meet trivially over `K = ℚ(√5)`.** This is
`adjoin_inf_adjoin_eq_adjoin_of_sq_eq_two` read over the base `ℚ(√5)`. -/
theorem adjoin_inf_adjoin_eq_bot_of_sq_eq_two (ha : a ^ 2 = 2) (hb : b ^ 2 = 5)
    (hζ : IsPrimitiveRoot ζ 5) :
    (IntermediateField.adjoin ℚ⟮b⟯ {a} ⊓ IntermediateField.adjoin ℚ⟮b⟯ {ζ} :
      IntermediateField ℚ⟮b⟯ Ω) = ⊥ := by
  have hble : ℚ⟮b⟯ ≤ ℚ⟮ζ⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (mem_adjoin_primitiveRoot_of_sq_eq_five hb hζ)
  refine IntermediateField.restrictScalars_injective ℚ ?_
  rw [← IntermediateField.restrictScalars_inf, IntermediateField.restrictScalars_bot_eq_self,
    IntermediateField.restrictScalars_adjoin_eq_sup,
    IntermediateField.restrictScalars_adjoin_eq_sup, sup_eq_right.mpr hble,
    ← IntermediateField.adjoin_union, Set.singleton_union]
  exact adjoin_inf_adjoin_eq_adjoin_of_sq_eq_two ha hb hζ

/-- **The fifth cyclotomic extension of `ℚ(√5)` has degree two.** Not `φ(5) = 4`: the full
cyclotomic degree needs `5` to be unramified in the base, which fails for `ℚ(√5)`. -/
theorem finrank_adjoin_primitiveRoot_eq_two_of_sq_eq_five (hb : b ^ 2 = 5)
    (hζ : IsPrimitiveRoot ζ 5) :
    Module.finrank ℚ⟮b⟯ (IntermediateField.adjoin ℚ⟮b⟯ {ζ}) = 2 := by
  have hb' : b ^ 2 = algebraMap ℚ Ω ((5 : ℤ) : ℚ) := by rw [hb]; simp
  have hble : ℚ⟮b⟯ ≤ ℚ⟮ζ⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (mem_adjoin_primitiveRoot_of_sq_eq_five hb hζ)
  have hres : (IntermediateField.adjoin ℚ⟮b⟯ {ζ}).restrictScalars ℚ = ℚ⟮ζ⟯ := by
    rw [IntermediateField.restrictScalars_adjoin_eq_sup, sup_eq_right.mpr hble]
  -- `restrictScalars` keeps the carrier and the inherited `ℚ`-module structure, so the
  -- `ℚ`-finrank is definitionally unchanged; compare `finrank_sup_adjoin_simple_eq_mul_two`.
  have habs : Module.finrank ℚ (IntermediateField.adjoin ℚ⟮b⟯ {ζ}) = 4 := by
    rw [show Module.finrank ℚ (IntermediateField.adjoin ℚ⟮b⟯ {ζ})
        = Module.finrank ℚ ((IntermediateField.adjoin ℚ⟮b⟯ {ζ}).restrictScalars ℚ) from rfl,
      hres, hζ.finrank_adjoin_eq_totient, Nat.totient_prime (by norm_num : Nat.Prime 5)]
  have htower := Module.finrank_mul_finrank ℚ ℚ⟮b⟯ (IntermediateField.adjoin ℚ⟮b⟯ {ζ})
  rw [finrank_adjoin_of_sq_eq_five hb', habs] at htower
  omega

/-- **The configuration is realised in `ℂ`.** With the real square roots of `5` and `2` and the
primitive fifth root of unity `exp(2πi/5)`, the intersection above is an equality between three
distinct subfields of `ℂ`. -/
theorem adjoin_inf_adjoin_exp_eq_adjoin :
    ℚ⟮((Real.sqrt 5 : ℝ) : ℂ), ((Real.sqrt 2 : ℝ) : ℂ)⟯ ⊓
        ℚ⟮Complex.exp (2 * Real.pi * Complex.I / 5)⟯ = ℚ⟮((Real.sqrt 5 : ℝ) : ℂ)⟯ :=
  adjoin_inf_adjoin_eq_adjoin_of_sq_eq_two
    (by norm_cast; exact Real.sq_sqrt (by norm_num))
    (by norm_cast; exact Real.sq_sqrt (by norm_num))
    (Complex.isPrimitiveRoot_exp 5 (by norm_num))

end TauCeti.NumberField
