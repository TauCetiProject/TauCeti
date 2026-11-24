/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Antidiag.FinsuppEquiv
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision

/-!
# Hilbert–Samuel functions of formal power series ideals

For an ideal `I` of the formal power series ring `K[[X₁, …, Xₙ]]` over a field, the
Hilbert–Samuel function of `K[[X]] ⧸ I` counts the exponents outside the diagram of initial
exponents `D(I)`, taken with respect to the graded lexicographic order:
`ℓ(K[[X]] ⧸ (I + 𝔪 ^ (ℓ + 1))) = #{α ∉ D(I) | |α| ≤ ℓ}`.

The count comes from Hironaka's formal division. The quotient `K[[X]] ⧸ J` is isomorphic to the
series supported outside `D(J)`, so it has dimension `#(D(J)ᶜ)` whenever this complement is finite
(`MonomialOrder.finrank_quotient_eq_ncard_compl_initialDiagram`, for any monomial order). Since the
graded lexicographic order compares total degrees first, adding the series of order at least `n`
to `I` adds exactly the exponents of degree at least `n` to its diagram
(`MonomialOrder.initialDiagram_degLex_sup_pow_span_range_X`). Finally, the residue field of
`K[[X]]` is `K`, so length over `K[[X]]` agrees with dimension over `K`.

For the zero ideal the count is the number `(ℓ + n).choose n` of monomials of degree at most `ℓ`
in `n` variables.

## Main results

* `Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram`: the Hilbert–Samuel function of
  `K[[X]] ⧸ I` at `ℓ` counts the exponents of degree at most `ℓ` outside `D(I)`.
* `MvPowerSeries.localQuotientHilbertSamuel_bot_eq_choose`: the Hilbert–Samuel function of
  `K[[X]]` is `ℓ ↦ (ℓ + n).choose n`.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239.
-/

public section

open scoped MonomialOrder

namespace Ideal

open MonomialOrder

/-- **The Hilbert–Samuel function counts exponents outside the initial diagram.** For an ideal
`I` of the power series ring over a field, the Hilbert–Samuel function of the quotient by `I` at
`ℓ` is the number of exponents of degree at most `ℓ` outside the graded lexicographic diagram of
initial exponents of `I`. -/
theorem localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram {σ K : Type*} [Field K]
    [Finite σ] [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    I.localQuotientHilbertSamuel ℓ =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ degLex.initialDiagram I).ncard := by
  have hD : (degLex.initialDiagram (I ⊔ IsLocalRing.maximalIdeal _ ^ (ℓ + 1)))ᶜ =
      {α : σ →₀ ℕ | α.degree ≤ ℓ} \ degLex.initialDiagram I := by
    rw [MvPowerSeries.maximalIdeal_eq_span_range_X, initialDiagram_degLex_sup_pow_span_range_X,
      Set.compl_union, Set.sdiff_eq]
    ext α
    simp [and_comm]
  have hfin : (degLex.initialDiagram (I ⊔ IsLocalRing.maximalIdeal _ ^ (ℓ + 1)))ᶜ.Finite :=
    hD ▸ (Finsupp.finite_of_degree_le ℓ).sdiff
  have hlen := TauCeti.finrank_eq_length_mul_finrank_residueField K (MvPowerSeries σ K)
    (MvPowerSeries σ K ⧸ (I ⊔ IsLocalRing.maximalIdeal _ ^ (ℓ + 1)))
  rw [MvPowerSeries.finrank_residueField, mul_one,
    degLex.finrank_quotient_eq_ncard_compl_initialDiagram hfin, hD] at hlen
  rw [hlen, ← localQuotientHilbertSamuel_def,
    ENat.natCast_toNat (I.localQuotientHilbertSamuel_ne_top ℓ)]

end Ideal

namespace MvPowerSeries

/-- The Hilbert–Samuel function of the power series ring in `n` variables over a field is
`ℓ ↦ (ℓ + n).choose n`, the number of monomials of degree at most `ℓ`. -/
@[simp]
theorem localQuotientHilbertSamuel_bot_eq_choose {σ K : Type*} [Fintype σ] [Field K] (ℓ : ℕ) :
    (⊥ : Ideal (MvPowerSeries σ K)).localQuotientHilbertSamuel ℓ =
      (ℓ + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  -- The count does not depend on the choice of a linear order on the variables.
  let : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  rw [Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram,
    MonomialOrder.initialDiagram_bot,
    Set.sdiff_empty, ← TauCeti.ncard_setOf_sum_le σ ℓ]
  congr 1
  refine Set.ncard_congr (fun α _ ↦ (α : σ → ℕ)) (fun α hα ↦ ?_) (fun _ _ _ _ h ↦
    DFunLike.coe_injective h) fun c hc ↦ ⟨Finsupp.equivFunOnFinite.symm c, ?_, ?_⟩
  · simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using hα
  · simpa [Finsupp.degree_eq_sum, Finsupp.sum_fintype] using hc
  · simp

-- `K[[x]] ⧸ (x²)` has Hilbert–Samuel function `1, 2, 2, …`: below `D((x²)) = {2, 3, …}` lie the
-- exponents `0` and `1`.
example {K : Type*} [Field K] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (Ideal.span {monomial (Finsupp.single (0 : Fin 1) 2) (1 : K)}).localQuotientHilbertSamuel ℓ =
      2 := by
  rw [← Set.image_singleton (f := fun α ↦ monomial α (1 : K)),
    Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram,
    MonomialOrder.initialDiagram_span_monomial]
  have h : {α : Fin 1 →₀ ℕ | α.degree ≤ ℓ} \
      ⋃ α ∈ ({Finsupp.single 0 2} : Set (Fin 1 →₀ ℕ)), Set.Ici α =
      {0, Finsupp.single 0 1} := by
    ext α
    obtain ⟨n, rfl⟩ : ∃ n, α = Finsupp.single 0 n := ⟨α 0, Finsupp.ext fun i ↦ by fin_cases i; simp⟩
    simp [Finsupp.single_le_iff]
    omega
  rw [h, Set.ncard_pair (by simp [eq_comm]), Nat.cast_ofNat]

end MvPowerSeries
