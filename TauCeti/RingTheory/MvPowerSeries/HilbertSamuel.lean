/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Antidiag.FinsuppEquiv
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
public import TauCeti.Data.Finsupp.UpperSet

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

In finitely many variables, the Hilbert–Samuel functions realized by ideals of `K[[X]]` form a
well-founded subset of `Lex (ℕ → ℕ∞)`, the lexicographic order comparing two functions at the
least argument where they differ. Hence every lexicographically nonincreasing sequence of them is
eventually constant, and in particular so is every pointwise nonincreasing sequence. Through the
count above, these are the corresponding statements for the counting functions of upper sets of
exponents (`TauCeti.isWF_range_toLex_ncard_sdiff`). The lexicographic order on all of `ℕ → ℕ∞` is
not well-founded, so realizability by ideals in a fixed finite number of variables is essential.
This stabilization is what makes the Hilbert–Samuel function usable as the first entry of an
invariant that decreases under blowing up.

## Main results

* `Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram`: the Hilbert–Samuel function of
  `K[[X]] ⧸ I` at `ℓ` counts the exponents of degree at most `ℓ` outside `D(I)`.
* `MvPowerSeries.localQuotientHilbertSamuel_bot_eq_choose`: the Hilbert–Samuel function of
  `K[[X]]` is `ℓ ↦ (ℓ + n).choose n`.
* `MvPowerSeries.isWF_range_toLex_localQuotientHilbertSamuel`: in finitely many variables, the
  realized Hilbert–Samuel functions form a well-founded subset of the lexicographic order.
* `MvPowerSeries.exists_forall_ge_localQuotientHilbertSamuel_eq_of_antitone`: a lexicographically
  nonincreasing sequence of realized Hilbert–Samuel functions is eventually constant.
* `MvPowerSeries.exists_forall_ge_localQuotientHilbertSamuel_eq_of_forall_le`: a pointwise
  nonincreasing sequence of realized Hilbert–Samuel functions is eventually constant.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239.
* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1.
* Edward Bierstone, Pierre D. Milman and Michael Temkin, *𝒬-universal desingularization*, Asian
  J. Math. 15 (2011), 229–249, §6.1.
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

/-- The Hilbert–Samuel function of `K[[X]] ⧸ I` is the coercion to `ℕ∞` of the counting function
of an upper set of exponents, namely of the graded lexicographic diagram of initial exponents of
`I`. -/
private theorem exists_localQuotientHilbertSamuel_eq_ncard_sdiff {σ K : Type*} [Finite σ]
    [Field K] (I : Ideal (MvPowerSeries σ K)) :
    ∃ D : UpperSet (σ →₀ ℕ), I.localQuotientHilbertSamuel =
      fun ℓ ↦ (({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (D : Set (σ →₀ ℕ))).ncard : ℕ∞) := by
  -- The count does not depend on the choice of a linear order on the variables.
  have := Fintype.ofFinite σ
  let : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  exact ⟨⟨_, MonomialOrder.degLex.isUpperSet_initialDiagram I⟩,
    funext (Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram I)⟩

/-- **Lexicographic well-foundedness of Hilbert–Samuel functions.** In finitely many variables
over a field, the Hilbert–Samuel functions `ℓ ↦ ℓ(K[[X]] ⧸ (I + 𝔪 ^ (ℓ + 1)))` of the ideals `I`
of `K[[X]]` form a well-founded subset of `Lex (ℕ → ℕ∞)`. -/
theorem isWF_range_toLex_localQuotientHilbertSamuel (σ K : Type*) [Finite σ] [Field K] :
    (Set.range fun I : Ideal (MvPowerSeries σ K) ↦ toLex I.localQuotientHilbertSamuel).IsWF := by
  -- Coercing the values from `ℕ` to `ℕ∞` is strictly monotone for the lexicographic orders.
  -- Mathlib has no unfolding lemma for `<` on `Lex (ℕ → β)`, which is `Pi.Lex` by definition, so
  -- the first difference is destructured directly.
  let g : Lex (ℕ → ℕ) → Lex (ℕ → ℕ∞) := fun c ↦ toLex fun ℓ ↦ (ofLex c ℓ : ℕ∞)
  have hg : Monotone g := StrictMono.monotone fun c c' ⟨i, hi, hlt⟩ ↦
    ⟨i, fun j hj ↦ congrArg ((↑) : ℕ → ℕ∞) (hi j hj), Nat.cast_lt.2 hlt⟩
  refine ((TauCeti.isWF_range_toLex_ncard_sdiff (σ := σ)).isPWO.image_of_monotone hg).isWF.mono ?_
  rintro _ ⟨I, rfl⟩
  obtain ⟨D, hD⟩ := exists_localQuotientHilbertSamuel_eq_ncard_sdiff I
  exact ⟨_, ⟨D, rfl⟩, by simp only [hD, g, ofLex_toLex]⟩

/-- **Lexicographic stabilization of Hilbert–Samuel functions.** In finitely many variables over a
field, a sequence of ideals `I j` of `K[[X]]` whose Hilbert–Samuel functions are lexicographically
nonincreasing has eventually constant Hilbert–Samuel function. -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_antitone {σ K : Type*} [Finite σ]
    [Field K] {I : ℕ → Ideal (MvPowerSeries σ K)}
    (h : Antitone fun j ↦ toLex (I j).localQuotientHilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (I j).localQuotientHilbertSamuel = (I j₀).localQuotientHilbertSamuel := by
  have hwf := (isWF_range_toLex_localQuotientHilbertSamuel σ K).mono
    (Set.range_subset_iff.2 fun j ↦ ⟨I j, rfl⟩)
  obtain ⟨j₀, hj₀⟩ := hwf.min_mem (Set.range_nonempty _)
  refine ⟨j₀, fun j hj ↦ ?_⟩
  exact toLex_inj.1 ((h hj).eq_of_not_lt (hj₀ ▸ hwf.not_lt_min _ ⟨j, rfl⟩))

/-- **Pointwise stabilization of Hilbert–Samuel functions.** In finitely many variables over a
field, a sequence of ideals `I j` of `K[[X]]` whose Hilbert–Samuel functions are pointwise
nonincreasing has eventually constant Hilbert–Samuel function. -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_forall_le {σ K : Type*} [Finite σ]
    [Field K] {I : ℕ → Ideal (MvPowerSeries σ K)}
    (h : ∀ j ℓ, (I (j + 1)).localQuotientHilbertSamuel ℓ ≤ (I j).localQuotientHilbertSamuel ℓ) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (I j).localQuotientHilbertSamuel = (I j₀).localQuotientHilbertSamuel :=
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_antitone
    (antitone_nat_of_succ_le fun j ↦ Pi.toLex_monotone (h j))

end MvPowerSeries
