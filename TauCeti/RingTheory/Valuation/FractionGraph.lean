/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.Localization.Submodule

/-!
# Coprime denominators and fraction graphs for products of valuation subrings

Given an indexed family of valuation subrings `O i` of fields `K i` and a ring homomorphism
`f : (∀ i, O i) →+* C`, every element `t : ∀ i, K i` can be written componentwise as a ratio
`prodNumerator O t / prodDenominator O t` of elements of `∀ i, O i` whose images under `f` are
coprime. The pairs `(t, c) : (∀ i, K i) × C` satisfying
`f (prodNumerator O t) = f (prodDenominator O t) * c` form a subring `fractionGraph O f` in which
each `t` determines `c` uniquely.

## Main definitions and results

* `TauCeti.ValuationSubring.prodDenominator`: at each index `i`, `1` if `t i ∈ O i` and `(t i)⁻¹`
  otherwise.
* `TauCeti.ValuationSubring.prodNumerator`: `t * prodDenominator O t` in `∀ i, O i`.
* `TauCeti.ValuationSubring.isCoprime_prodDenominator_prodNumerator`: for any ring homomorphism
  `f : (∀ i, O i) →+* C`, `f (prodDenominator O t)` and `f (prodNumerator O t)` are coprime.
* `TauCeti.ValuationSubring.fractionGraph`: the subring of `(∀ i, K i) × C` cut out by the
  fraction relation `f (prodNumerator O t) = f (prodDenominator O t) * c`.
* `TauCeti.ValuationSubring.mem_fractionGraph`: membership criterion for `fractionGraph O f`.
* `TauCeti.ValuationSubring.fractionGraph_unique`: uniqueness of the second coordinate in
  `fractionGraph O f`.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean at commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`, file
  `src/Lib/Cohomology/ProperBaseChange/PlaceSpace.lean` (declarations `denominator`, `numerator`,
  `isCoprime_denominator_numerator`, `fractionGraph`, `mem_fractionGraph`, `placeGraph_unique`);
  Apache 2.0, Copyright 2026 Anthropic, PBC.
-/

public section

namespace TauCeti.ValuationSubring

variable {ι : Type*} {K : ι → Type*} [∀ i, Field (K i)]
variable (O : ∀ i, ValuationSubring (K i))

/-- Componentwise denominator of `t : ∀ i, K i` in `∀ i, O i`: `1` where `t i ∈ O i`, and
`(t i)⁻¹` otherwise. -/
noncomputable def prodDenominator (t : ∀ i, K i) : ∀ i, O i := fun i ↦
  open scoped Classical in
  if h : t i ∈ O i then 1 else ⟨(t i)⁻¹, ((O i).mem_or_inv_mem (t i)).resolve_left h⟩

/-- Componentwise numerator of `t : ∀ i, K i` in `∀ i, O i`: `t i` where `t i ∈ O i`, and `1`
otherwise, so that `(prodNumerator O t i : K i) = t i * prodDenominator O t i`. -/
noncomputable def prodNumerator (t : ∀ i, K i) : ∀ i, O i := fun i ↦
  ⟨t i * prodDenominator O t i, by
    classical
    by_cases h : t i ∈ O i
    · simp [prodDenominator, h]
    · have hne : t i ≠ 0 := fun h0 ↦ h (h0 ▸ (O i).zero_mem)
      simp [prodDenominator, h, mul_inv_cancel₀ hne]⟩

/-- For any ring homomorphism `f : (∀ i, O i) →+* C` and any `t : ∀ i, K i`, the images of
`prodDenominator O t` and `prodNumerator O t` under `f` are coprime. -/
theorem isCoprime_prodDenominator_prodNumerator {C : Type*} [CommRing C]
    (f : (∀ i, O i) →+* C) (t : ∀ i, K i) :
    IsCoprime (f (prodDenominator O t)) (f (prodNumerator O t)) := by
  refine IsCoprime.map ⟨1 - prodNumerator O t, 1, ?_⟩ f
  ext i
  classical
  by_cases h : t i ∈ O i
  · simp [prodNumerator, prodDenominator, h]
  · have hne : t i ≠ 0 := fun h0 ↦ h (h0 ▸ (O i).zero_mem)
    simp [prodNumerator, prodDenominator, h, mul_inv_cancel₀ hne]

/-- The fraction graph of a ring homomorphism `f : (∀ i, O i) →+* C`, as a subring of
`(∀ i, K i) × C`. Its elements are the pairs `(t, c)` satisfying
`f (prodNumerator O t) = f (prodDenominator O t) * c`. -/
def fractionGraph {C : Type*} [CommRing C] (f : (∀ i, O i) →+* C) :
    Subring ((∀ i, K i) × C) :=
  let : Algebra (∀ i, O i) C := f.toAlgebra
  let : Algebra (∀ i, O i) (∀ i, K i) :=
    (RingHom.pi fun i ↦ (O i).subtype.comp (Pi.evalRingHom (fun j ↦ O j) i)).toAlgebra
  ((⊥ : Subalgebra (∀ i, O i) ((∀ i, K i) × C)).saturation
    (_ ⊓ (IsUnit.submonoid C).comap (RingHom.snd (∀ i, K i) C)) inf_le_left).toSubring

/-- A pair `(t, c)` belongs to `fractionGraph O f` if and only if
`f (prodNumerator O t) = f (prodDenominator O t) * c`. -/
theorem mem_fractionGraph {C : Type*} [CommRing C] (f : (∀ i, O i) →+* C)
    {t : ∀ i, K i} {c : C} :
    (t, c) ∈ fractionGraph O f ↔ f (prodNumerator O t) = f (prodDenominator O t) * c := by
  let : Algebra (∀ i, O i) C := f.toAlgebra
  let : Algebra (∀ i, O i) (∀ i, K i) :=
    (RingHom.pi fun i ↦ (O i).subtype.comp (Pi.evalRingHom (fun j ↦ O j) i)).toAlgebra
  constructor
  · rintro ⟨_, ⟨⟨r, rfl⟩, h_unit : IsUnit (f r)⟩, r', h⟩
    have h_snd : f r' = f r * c := congrArg Prod.snd h
    have h_fst (i : ι) : (r' i : K i) = (r i : K i) * t i := congrFun (congrArg Prod.fst h) i
    have h_key : r * prodNumerator O t = prodDenominator O t * r' := by
      ext i
      change (r i : K i) * (t i * prodDenominator O t i) = prodDenominator O t i * r' i
      rw [h_fst, ← mul_assoc, mul_comm]
    refine h_unit.mul_left_cancel ?_
    calc f r * f (prodNumerator O t)
        = f (prodDenominator O t) * f r' := by rw [← map_mul, h_key, map_mul]
      _ = f r * (f (prodDenominator O t) * c) := by rw [h_snd, mul_left_comm]
  · intro h
    have h_unit : IsUnit (f (prodDenominator O t)) :=
      (isCoprime_prodDenominator_prodNumerator O f t).isUnit_of_dvd ⟨c, h⟩
    refine ⟨_, ⟨⟨prodDenominator O t, rfl⟩, h_unit⟩, prodNumerator O t, Prod.ext ?_ h⟩
    ext i
    exact mul_comm (t i) (prodDenominator O t i)

/-- Each `t : ∀ i, K i` has at most one partner `c : C` in `fractionGraph O f`. -/
theorem fractionGraph_unique {C : Type*} [CommRing C] {f : (∀ i, O i) →+* C}
    {t : ∀ i, K i} {c d : C} (hc : (t, c) ∈ fractionGraph O f)
    (hd : (t, d) ∈ fractionGraph O f) : c = d := by
  rw [mem_fractionGraph] at hc hd
  have h_unit : IsUnit (f (prodDenominator O t)) :=
    (isCoprime_prodDenominator_prodNumerator O f t).isUnit_of_dvd ⟨c, hc⟩
  exact h_unit.mul_left_cancel (hc.symm.trans hd)

end TauCeti.ValuationSubring
