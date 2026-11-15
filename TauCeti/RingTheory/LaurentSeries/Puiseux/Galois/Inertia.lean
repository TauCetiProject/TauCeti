/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Puiseux.Galois.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Valuation
public import TauCeti.RingTheory.Valuation.RamificationGroup

/-!
# The Galois group of the Puiseux field is inertia

Let `𝒪` be the valuation ring of the Puiseux field `puiseuxField K`, the Puiseux series of
nonnegative order. A Kummer automorphism `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)`
(`TauCeti.puiseuxField.kummer`) multiplies every coefficient by a root of unity, so it preserves
supports and hence the valuation: it lies in the decomposition group of `𝒪`, the stabilizer of
`𝒪`. It also fixes the coefficients at integer exponents, in particular the constant coefficient.
For a series `x ∈ 𝒪` the difference `σ x - x` therefore has no coefficient at exponents `≤ 0`, so
it lies in the maximal ideal of `𝒪`. Thus the Kummer automorphisms act trivially on the residue
field of `𝒪`: they lie in the inertia group.

When `K` contains a primitive `n`-th root of unity for every `n > 0`, every automorphism of the
Puiseux field over `K⸨X⸩` is a Kummer automorphism (`TauCeti.puiseuxField.galEquivTateModule`).
So the whole Galois group `Gal(puiseuxField K / K⸨X⸩)` preserves the valuation, and equals both
its decomposition group and its inertia group at `𝒪`. For `K` algebraically closed of
characteristic zero the Puiseux field is an algebraic closure of `K⸨X⸩`
(`TauCeti.puiseuxField.instIsAlgClosure`), so the absolute Galois group of `K⸨X⸩` is entirely
inertia.

The decomposition and inertia groups are Mathlib's `ValuationSubring.decompositionSubgroup` and
`ValuationSubring.inertiaSubgroup`, for the valuation ring
`(TauCeti.puiseuxField.valuation K).valuationSubring`.

## Main results

* `TauCeti.puiseuxField.addVal_kummer` and `TauCeti.puiseuxField.valuation_kummer`: the Kummer
  automorphisms preserve the order and the valuation.
* `TauCeti.puiseuxField.valuation_kummer_sub_lt_one`: a Kummer automorphism moves every series of
  the valuation ring by an element of its maximal ideal.
* `TauCeti.puiseuxField.kummer_mem_decompositionSubgroup` and
  `TauCeti.puiseuxField.kummer_mem_inertiaSubgroup`: over any coefficient field, the Kummer
  automorphisms lie in the decomposition and inertia groups of the valuation ring.
* `TauCeti.puiseuxField.addVal_algEquiv_apply` and `TauCeti.puiseuxField.valuation_algEquiv_apply`:
  with enough roots of unity in `K`, every Galois automorphism preserves the order and the
  valuation.
* `TauCeti.puiseuxField.decompositionSubgroup_eq_top` and
  `TauCeti.puiseuxField.inertiaSubgroup_eq_top`: with enough roots of unity in `K`, the whole
  Galois group is the decomposition group and the inertia group.
-/

public section

open HahnSeries WithZero
open scoped LaurentSeries Pointwise

namespace TauCeti.puiseuxField

open PrimeToPTateModule

variable {K : Type*} [Field K]

/-- The Kummer automorphism attached to `ζ` preserves the order of Puiseux series. -/
theorem addVal_kummer (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) :
    addVal K (kummer K ζ x) = addVal K x := by
  rw [addVal_apply, addVal_apply, coe_kummer_apply, orderTop_twistEquiv]

/-- The Kummer automorphism attached to `ζ` preserves the valuation of Puiseux series. -/
theorem valuation_kummer (ζ : PrimeToPTateModule 1 K) (x : puiseuxField K) :
    valuation K (kummer K ζ x) = valuation K x := by
  rw [valuation_apply, valuation_apply, coe_kummer_apply]
  refine le_antisymm ?_ ?_ <;> rw [HahnSeries.valuation_le_valuation_iff, orderTop_twistEquiv]

/-- A Kummer automorphism fixes the coefficients of a Puiseux series at the integer exponents, so
it moves a series of nonnegative order by a series of positive order: on the valuation ring it is
the identity modulo the maximal ideal. -/
theorem valuation_kummer_sub_lt_one (ζ : PrimeToPTateModule 1 K) {x : puiseuxField K}
    (hx : valuation K x ≤ 1) : valuation K (kummer K ζ x - x) < 1 := by
  rw [← exp_zero, ← neg_zero, valuation_lt_exp_neg_iff, addVal_apply]
  rw [← exp_zero, ← neg_zero, valuation_le_exp_neg_iff, addVal_apply] at hx
  have hcoeff (q : ℚ) : ((kummer K ζ x - x : puiseuxField K) : HahnSeries ℚ K).coeff q =
      ((ratChar K ζ (.ofAdd q) : K) - 1) * (x : HahnSeries ℚ K).coeff q := by
    rw [AddSubgroupClass.coe_sub, coeff_sub, coeff_kummer, sub_one_mul]
  refine lt_of_le_of_ne (le_orderTop_iff_forall.mpr fun q hq ↦ ?_) fun h ↦ ?_
  · -- Below the exponent `0`, the series `x` itself has no coefficient.
    rw [hcoeff, coeff_eq_zero_of_lt_orderTop (hq.trans_le hx), mul_zero]
  · -- At the exponent `0`, the Kummer automorphism multiplies the coefficient by `1`.
    refine orderTop_ne_of_coeff_eq_zero ?_ h.symm
    rw [hcoeff, ← Int.cast_zero, ratChar_ofAdd_intCast, Units.val_one, sub_self, zero_mul]

/-- **Kummer automorphisms lie in the decomposition group.** For every coefficient field `K`, the
Kummer automorphism attached to `ζ` stabilizes the valuation ring of the Puiseux field. -/
theorem kummer_mem_decompositionSubgroup (ζ : PrimeToPTateModule 1 K) :
    kummer K ζ ∈ (valuation K).valuationSubring.decompositionSubgroup K⸨X⸩ :=
  (valuation K).mem_decompositionSubgroup_valuationSubring (valuation_kummer ζ)

/-- **Kummer automorphisms lie in the inertia group.** For every coefficient field `K`, the Kummer
automorphism attached to `ζ` acts trivially on the residue field of the valuation ring of the
Puiseux field. -/
theorem kummer_mem_inertiaSubgroup (ζ : PrimeToPTateModule 1 K) :
    ⟨kummer K ζ, kummer_mem_decompositionSubgroup ζ⟩ ∈
      (valuation K).valuationSubring.inertiaSubgroup K⸨X⸩ :=
  ((valuation K).mem_inertiaSubgroup_valuationSubring_iff _).mpr fun _ ↦
    valuation_kummer_sub_lt_one ζ

section RootsOfUnity

variable [∀ n : ℕ+, HasEnoughRootsOfUnity K n]

/-- If `K` contains a primitive `n`-th root of unity for every `n > 0`, every automorphism of the
Puiseux field over `K⸨X⸩` preserves the order of Puiseux series. -/
theorem addVal_algEquiv_apply (σ : Gal(puiseuxField K/K⸨X⸩)) (x : puiseuxField K) :
    addVal K (σ x) = addVal K x := by
  rw [← kummer_galEquivTateModule σ, addVal_kummer]

/-- If `K` contains a primitive `n`-th root of unity for every `n > 0`, every automorphism of the
Puiseux field over `K⸨X⸩` preserves its valuation. -/
theorem valuation_algEquiv_apply (σ : Gal(puiseuxField K/K⸨X⸩)) (x : puiseuxField K) :
    valuation K (σ x) = valuation K x := by
  rw [← kummer_galEquivTateModule σ, valuation_kummer]

/-- **The decomposition group is everything.** If `K` contains a primitive `n`-th root of unity
for every `n > 0`, every automorphism of the Puiseux field over `K⸨X⸩` stabilizes its valuation
ring. -/
theorem decompositionSubgroup_eq_top :
    (valuation K).valuationSubring.decompositionSubgroup K⸨X⸩ = ⊤ :=
  eq_top_iff.mpr fun σ _ ↦
    (valuation K).mem_decompositionSubgroup_valuationSubring (valuation_algEquiv_apply σ)

/-- **The Galois group is inertia.** If `K` contains a primitive `n`-th root of unity for every
`n > 0`, every automorphism of the Puiseux field over `K⸨X⸩` acts trivially on the residue field
of its valuation ring. For `K` algebraically closed of characteristic zero this says that the
whole absolute Galois group of `K⸨X⸩` is inertia. -/
theorem inertiaSubgroup_eq_top :
    (valuation K).valuationSubring.inertiaSubgroup K⸨X⸩ = ⊤ := by
  refine eq_top_iff.mpr fun σ _ ↦
    ((valuation K).mem_inertiaSubgroup_valuationSubring_iff σ).mpr fun x hx ↦ ?_
  rw [← kummer_galEquivTateModule (σ : Gal(puiseuxField K/K⸨X⸩))]
  exact valuation_kummer_sub_lt_one _ hx

end RootsOfUnity

end TauCeti.puiseuxField
