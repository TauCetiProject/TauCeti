/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Irreducibility of the cyclotomic polynomial from the degree of a cyclotomic extension

Mathlib proves `[L : K] = φ n` for an `n`-th cyclotomic extension `L / K` once `Φ_n` is known to be
irreducible over `K` (`IsCyclotomicExtension.finrank`). This file records the converse: the degree
of `L / K` is always at most `φ n`, and as soon as it is at least `φ n` the polynomial `Φ_n` is
irreducible over `K`. That converse and Mathlib's forward direction give the equivalence
`IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient`.

## Main results

* `IsCyclotomicExtension.finrank_le_totient`: `[L : K] ≤ φ n`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`: if `φ n ≤ [L : K]` then
  `Φ_n` is irreducible over `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient`: `Φ_n` is irreducible over
  `K` if and only if `[L : K] = φ n`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_coprime_finrank`: irreducibility is preserved by
  a finite base change whose degree is coprime to `φ n`.

## References

This is the degree bookkeeping of Milne, *Algebraic Number Theory*, proof of Proposition 6.2, and
of Sharifi, *Algebraic Number Theory*, proof of Lemma 3.1.13, where the base field is `ℚ`.
-/

public section

open Polynomial

namespace IsCyclotomicExtension

variable {n : ℕ} [NeZero n] (K : Type*) [Field K] (L : Type*) [CommRing L] [IsDomain L]
  [Algebra K L] [IsCyclotomicExtension {n} K L]

private theorem finrank_eq_natDegree_minpoly_zeta :
    Module.finrank K L = (minpoly K (zeta n K L)).natDegree := by
  -- `L = K(ζ)` has the power basis `1, ζ, …` of length `deg (minpoly K ζ)`.
  -- Source: Mathlib, proof of `IsCyclotomicExtension.finrank`.
  rw [((zeta_spec n K L).powerBasis K).finrank, IsPrimitiveRoot.powerBasis_dim]

private theorem minpoly_zeta_dvd_cyclotomic : minpoly K (zeta n K L) ∣ cyclotomic n K :=
  -- A primitive `n`-th root of unity is a root of `Φ_n`.
  -- Mathlib's `IsPrimitiveRoot.minpoly_dvd_cyclotomic` does not apply here: it is stated over
  -- `ℤ`, needs the root to lie in `K` itself, and assumes `[CharZero K]`.
  have : NeZero (n : L) := IsCyclotomicExtension.neZero n K L
  minpoly.dvd K _ (aeval_zeta n K L)

/-- **The degree of a cyclotomic extension is at most `φ n`.**

The bound is unconditional: nothing is assumed about `cyclotomic n K`. That is what separates it
from Mathlib's `IsCyclotomicExtension.finrank`, which gives the sharper `[L : K] = φ n` but only
under `Irreducible (cyclotomic n K)`. Reach for this one when that irreducibility is unknown, or
is itself what is being proved.

Source: Milne, *Algebraic Number Theory*, proof of Prop. 6.2 ("we know `[ℚ[ζ] : ℚ] ≤ φ(p^r)`");
Sharifi, *Algebraic Number Theory*, proof of Lemma 3.1.13 ("`[ℚ(µ_{p^r}) : ℚ] ≤ deg Φ_{p^r}`"). -/
theorem finrank_le_totient : Module.finrank K L ≤ n.totient :=
  calc
    Module.finrank K L = (minpoly K (zeta n K L)).natDegree :=
      finrank_eq_natDegree_minpoly_zeta K L
    _ ≤ (cyclotomic n K).natDegree :=
      natDegree_le_of_dvd (minpoly_zeta_dvd_cyclotomic K L) (cyclotomic_ne_zero n K)
    _ = n.totient := natDegree_cyclotomic n K

/-- **A cyclotomic extension of full degree has irreducible cyclotomic polynomial.** This is the
converse of Mathlib's `IsCyclotomicExtension.finrank`, and with it gives the equivalence
`irreducible_cyclotomic_iff_finrank_eq_totient`.

Source: Milne, *Algebraic Number Theory*, proof of Prop. 6.2 ("(3.34) implies
`[ℚ[ζ] : ℚ] ≥ φ(p^r)`. This proves (a)"); Sharifi, proof of Lemma 3.1.13 ("which forces
`[ℚ(µ_{p^r}) : ℚ] = p^{r−1}(p − 1)`"). -/
theorem irreducible_cyclotomic_of_totient_le_finrank (h : n.totient ≤ Module.finrank K L) :
    Irreducible (cyclotomic n K) := by
  have hint : IsIntegral K (zeta n K L) := (integral {n} K L).isIntegral _
  have hdeg : (cyclotomic n K).natDegree ≤ (minpoly K (zeta n K L)).natDegree := by
    rwa [natDegree_cyclotomic, ← finrank_eq_natDegree_minpoly_zeta K L]
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic n K)
    (minpoly_zeta_dvd_cyclotomic K L) hdeg]
  exact minpoly.irreducible hint

/-- **`Φ_n` is irreducible over `K` exactly when the cyclotomic extension has degree `φ n`.** The
forward direction is Mathlib's `IsCyclotomicExtension.finrank`; the converse is
`irreducible_cyclotomic_of_totient_le_finrank`.

Source: as for the two lemmas it combines. -/
theorem irreducible_cyclotomic_iff_finrank_eq_totient :
    Irreducible (cyclotomic n K) ↔ Module.finrank K L = n.totient :=
  ⟨IsCyclotomicExtension.finrank L, fun h ↦ irreducible_cyclotomic_of_totient_le_finrank K L h.ge⟩

section BaseChange

variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [NeZero (n : F)]
  {K : Type*} [Field K] [Algebra F K] [FiniteDimensional F K]

/-- Irreducibility of `Φ_n` is preserved by a finite base change of degree coprime to `φ(n)`.

Indeed, inside an algebraic closure of `K`, the cyclotomic extension `F(ζ_n)` has degree `φ(n)`
over `F`. It is therefore linearly disjoint from `K`, so `K(ζ_n)` still has degree `φ(n)` over
`K`.

Source: the coprime-degree linear-disjointness argument in Lang, *Algebra*, Chapter VI, §1. -/
theorem irreducible_cyclotomic_of_coprime_finrank
    (hirr : Irreducible (cyclotomic n F))
    (hcop : n.totient.Coprime (Module.finrank F K)) :
    Irreducible (cyclotomic n K) := by
  let _ : NeZero (n : K) :=
    ⟨by
      rw [← map_natCast (algebraMap F K)]
      simpa using (algebraMap F K).injective.ne (NeZero.ne (n : F))⟩
  let _ : NeZero (n : AlgebraicClosure K) :=
    (inferInstance : NeZero (n : K)).of_injective
      (algebraMap K (AlgebraicClosure K)).injective
  let ζ : AlgebraicClosure K :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n |>.choose
  have hζ : IsPrimitiveRoot ζ n :=
    HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) n |>.choose_spec
  let M := IntermediateField.adjoin F ({ζ} : Set (AlgebraicClosure K))
  let L := IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))
  let _ : IsCyclotomicExtension {n} F M :=
    hζ.intermediateField_adjoin_isCyclotomicExtension F
  let _ : IsCyclotomicExtension {n} K L :=
    hζ.intermediateField_adjoin_isCyclotomicExtension K
  let _ : FiniteDimensional F M := IsCyclotomicExtension.finiteDimensional {n} F M
  let _ : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {n} K L
  have hMfin : Module.finrank F M = n.totient :=
    IsCyclotomicExtension.finrank M hirr
  have hdis : M.LinearDisjoint K :=
    IntermediateField.LinearDisjoint.of_finrank_coprime (hMfin ▸ hcop)
  have hMle : M ≤ L.restrictScalars F := by
    change IntermediateField.adjoin F ({ζ} : Set (AlgebraicClosure K)) ≤
      (IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K))).restrictScalars F
    rw [IntermediateField.adjoin_le_iff]
    exact fun _ hx ↦ IntermediateField.subset_adjoin K _ hx
  have hadj : IntermediateField.adjoin K (M : Set (AlgebraicClosure K)) = L := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      exact fun x hx ↦ hMle hx
    · change IntermediateField.adjoin K ({ζ} : Set (AlgebraicClosure K)) ≤ _
      rw [IntermediateField.adjoin_le_iff]
      intro x hx
      obtain rfl := Set.mem_singleton_iff.mp hx
      apply IntermediateField.subset_adjoin K (M : Set (AlgebraicClosure K))
      change ζ ∈ M
      exact IntermediateField.subset_adjoin F _ (Set.mem_singleton ζ)
  have hrank := hdis.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  rw [hadj, ← Module.finrank_eq_rank' K L, ← Module.finrank_eq_rank' F M] at hrank
  have hfin : Module.finrank K L = Module.finrank F M := by exact_mod_cast hrank
  exact irreducible_cyclotomic_of_totient_le_finrank K L (by rw [hfin, hMfin])

end BaseChange

end IsCyclotomicExtension
