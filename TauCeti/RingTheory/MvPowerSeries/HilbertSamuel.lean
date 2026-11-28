/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finsupp.UpperSet
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import TauCeti.Data.Finsupp.Weight
import TauCeti.Order.PiLex
import TauCeti.RingTheory.MvPowerSeries.Length

/-!
# Hilbert–Samuel functions of formal power series ideals and lexicographic stabilization

For an ideal `I` of the formal power series ring `K[[X₁, …, Xₙ]]` over a field, the
Hilbert–Samuel function of `K[[X]] ⧸ I` counts the exponents outside the diagram of initial
exponents `D(I)`, taken with respect to the graded lexicographic order:
`ℓ(K[[X]] ⧸ (I + 𝔪 ^ (ℓ + 1))) = #{α ∉ D(I) | |α| ≤ ℓ}`
(`Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram`, Bierstone–Milman 1997,
Corollary 3.20).

The count comes from Hironaka's formal division. The quotient `K[[X]] ⧸ J` is isomorphic to the
series supported outside `D(J)`, so it has dimension `#(D(J)ᶜ)` whenever this complement is finite
(`MonomialOrder.finrank_quotient_eq_ncard_compl_initialDiagram`, for any monomial order). Since the
graded lexicographic order compares total degrees first, adding the series of order at least `n`
to `I` adds exactly the exponents of degree at least `n` to its diagram
(`MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow`). Finally, the residue field of
`K[[X]]` is `K`, so length over `K[[X]]` agrees with dimension over `K`.

For the zero ideal the count is the number `(ℓ + n).choose n` of monomials of degree at most `ℓ`
in `n` variables (`MvPowerSeries.localQuotientHilbertSamuel_bot_eq_choose`). Explicit formulas also
hold for coordinate ideals `Ideal.span (X '' S)`, coordinate hyperplanes `Ideal.span {X i}`, and
univariate monomial powers `Ideal.span {X i ^ k}`.

In finitely many variables `σ` (`[Finite σ]`), applying Dickson-lemma stabilization of
degree-bounded complement counts for sequences of upper sets in `σ →₀ ℕ`
(`TauCeti.exists_forall_ge_ncard_sdiff_eq_of_antitone`) to graded lexicographic initial diagrams
yields lexicographic stabilization
(`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le`)
and hence pointwise stabilization (`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_le`)
for Hilbert–Samuel functions of ideals in `MvPowerSeries σ (K j)` across possibly varying
coefficient fields `K j` (Bierstone–Milman 1989, Theorem 5.2.1; Bierstone–Milman–Temkin 2011,
§6.1).

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

* `Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram`: in finitely many variables,
  the Hilbert–Samuel function of `K[[X]] ⧸ I` at `ℓ` counts the exponents of degree at most `ℓ`
  outside `D(I)`.
* `Ideal.localQuotientHilbertSamuel_eq_of_initialDiagram_degLex_eq`: in finitely many variables
  `σ`, ideals over possibly distinct fields with equal `degLex.initialDiagram` have equal
  Hilbert–Samuel functions.
* `MvPowerSeries.localQuotientHilbertSamuel_bot_eq_choose`: the Hilbert–Samuel function of
  `K[[X]]` is `ℓ ↦ (ℓ + n).choose n`.
* `TauCeti.localQuotientHilbertSamuel_span_image_X`,
  `TauCeti.localQuotientHilbertSamuel_span_singleton_X`,
  `TauCeti.localQuotientHilbertSamuel_span_singleton_X_pow_of_subsingleton`: explicit evaluations
  for coordinate ideals `Ideal.span (X '' S)`, coordinate hyperplanes `(X i)`, and univariate
  monomial powers `(X i ^ k)`.
* `MvPowerSeries.isWF_range_toLex_localQuotientHilbertSamuel`: in finitely many variables, the
  realized Hilbert–Samuel functions form a well-founded subset of the lexicographic order.
* `TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le`,
  `TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_le`: lexicographic and pointwise
  stabilization of realized Hilbert–Samuel functions in `MvPowerSeries σ (K j)`.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239, and §9, p. 276.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *𝒬-universal desingularization*,
  Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open scoped MonomialOrder

namespace Ideal

open MonomialOrder

/-- **The Hilbert–Samuel function counts exponents outside the initial diagram.** In finitely
many variables `σ`, for an ideal `I` of the power series ring over a field, the Hilbert–Samuel
function of the quotient by `I` at `ℓ` is the number of exponents of degree at most `ℓ` outside
the graded lexicographic diagram of initial exponents of `I`. -/
theorem localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram {σ K : Type*} [Field K]
    [Finite σ] [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    I.localQuotientHilbertSamuel ℓ =
      ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ degLex.initialDiagram I).ncard := by
  have hD : (degLex.initialDiagram (I ⊔ IsLocalRing.maximalIdeal _ ^ (ℓ + 1)))ᶜ =
      {α : σ →₀ ℕ | α.degree ≤ ℓ} \ degLex.initialDiagram I := by
    rw [initialDiagram_degLex_sup_maximalIdeal_pow, Set.compl_union, Set.sdiff_eq]
    ext α
    simp [and_comm]
  have hfin : (degLex.initialDiagram (I ⊔ IsLocalRing.maximalIdeal _ ^ (ℓ + 1)))ᶜ.Finite :=
    hD ▸ (Finsupp.finite_of_degree_le ℓ).sdiff
  have := hfin.fintype
  have : Module.Finite K (MvPowerSeries σ K ⧸ (I ⊔ IsLocalRing.maximalIdeal _ ^ (ℓ + 1))) :=
    Module.Finite.equiv
      ((degLex.quotientEquivComplementSubmodule _).trans
        (degLex.complementSubmoduleEquivFun _)).symm
  rw [localQuotientHilbertSamuel_def, ← TauCeti.length_mvPowerSeries_restrictScalars,
    Module.length_eq_finrank, degLex.finrank_quotient_eq_ncard_compl_initialDiagram hfin, hD]

/-- In finitely many variables `σ`, two ideals of `MvPowerSeries σ K₁` and `MvPowerSeries σ K₂`
with the same graded lexicographic initial diagram have the same Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_eq_of_initialDiagram_degLex_eq
    {σ K₁ K₂ : Type*} [Field K₁] [Field K₂] [Finite σ] [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPowerSeries σ K₁)) {J : Ideal (MvPowerSeries σ K₂)}
    (h : degLex.initialDiagram I = degLex.initialDiagram J) :
    I.localQuotientHilbertSamuel = J.localQuotientHilbertSamuel := by
  ext n
  rw [localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram,
    localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram, h]

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
    MonomialOrder.initialDiagram_bot, Set.sdiff_empty, ← Nat.card_coe_set_eq, Set.coe_ofPred,
    TauCeti.natCard_degree_le_eq_choose, Nat.card_eq_fintype_card, add_comm]

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
  refine ((TauCeti.isWF_range_toLex_ncard_sdiff (σ := σ)).isPWO.image_of_monotone
    (TauCeti.strictMono_toLex_comp
      fun (_ : ℕ) ↦ (Nat.strictMono_cast : StrictMono (Nat.cast : ℕ → ℕ∞))).monotone).isWF.mono
    ?_
  rintro _ ⟨I, rfl⟩
  obtain ⟨D, hD⟩ := exists_localQuotientHilbertSamuel_eq_ncard_sdiff I
  exact ⟨_, ⟨D, rfl⟩, by simp only [hD, ofLex_toLex]⟩

end MvPowerSeries

namespace TauCeti

section CoordinateIdeals

open MvPowerSeries

/-- For any subset `S : Set σ` of finitely many variables, the Hilbert–Samuel value of the
coordinate ideal `Ideal.span (MvPowerSeries.X '' S)` at degree `n` is
`((Nat.card ↥Sᶜ + n).choose (Nat.card ↥Sᶜ) : ℕ∞)`. -/
@[simp]
theorem localQuotientHilbertSamuel_span_image_X {σ : Type*} (K : Type*) [Field K]
    [Finite σ] (S : Set σ) (n : ℕ) :
    (Ideal.span (X '' S) : Ideal (MvPowerSeries σ K)).localQuotientHilbertSamuel n =
      ((Nat.card ↥Sᶜ + n).choose (Nat.card ↥Sᶜ) : ℕ∞) := by
  classical
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  rw [Ideal.localQuotientHilbertSamuel_eq_ncard_diff_initialDiagram, ← Nat.card_coe_set_eq]
  have hspan : (X '' S : Set (MvPowerSeries σ K)) =
      (fun α ↦ monomial α (1 : K)) '' ((fun i ↦ Finsupp.single i 1) '' S) := by
    ext f
    simp [X_def]
  rw [hspan, MonomialOrder.degLex.initialDiagram_span_monomial]
  have hnotMem : ∀ α : σ →₀ ℕ,
      (α ∉ ⋃ β ∈ (fun i ↦ Finsupp.single i 1) '' S, Set.Ici β) ↔ ↑α.support ⊆ Sᶜ := fun α ↦ by
    simp [Finsupp.single_le_iff, Set.subset_compl_iff_disjoint_right, Set.disjoint_left]
    grind
  let e₁ : ↥({α : σ →₀ ℕ | α.degree ≤ n} \
        ⋃ β ∈ (fun i ↦ Finsupp.single i 1) '' S, Set.Ici β) ≃
      {α : {α : σ →₀ ℕ // ↑α.support ⊆ Sᶜ} // α.val.degree ≤ n} :=
    (Equiv.subtypeEquivRight fun α ↦ and_congr_right fun _ ↦ hnotMem α).trans
      ((Equiv.subtypeEquivRight fun _ ↦ and_comm).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  let e₂ : {α : {α : σ →₀ ℕ // ↑α.support ⊆ Sᶜ} // α.val.degree ≤ n} ≃
      {β : ↥Sᶜ →₀ ℕ // β.degree ≤ n} :=
    Equiv.subtypeEquiv (Finsupp.restrictSupportEquiv Sᶜ ℕ) fun α ↦ by
      have hdeg : ((Finsupp.restrictSupportEquiv Sᶜ ℕ).symm
          (Finsupp.restrictSupportEquiv Sᶜ ℕ α)).val.degree =
          (Finsupp.restrictSupportEquiv Sᶜ ℕ α).degree := by
        rw [Finsupp.restrictSupportEquiv_symm_apply_coe, Finsupp.extendDomain_eq_embDomain_subtype,
          Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
      rw [Equiv.symm_apply_apply] at hdeg
      rw [hdeg]
  rw [Nat.card_congr (e₁.trans e₂), TauCeti.natCard_degree_le_eq_choose]

/-- For any variable `i : σ` in finitely many variables, the Hilbert–Samuel value of
`Ideal.span {MvPowerSeries.X i}` at degree `n` is
`((Nat.card σ - 1 + n).choose (Nat.card σ - 1) : ℕ∞)`. -/
@[simp]
theorem localQuotientHilbertSamuel_span_singleton_X {σ : Type*} (K : Type*) [Field K]
    [Finite σ] (i : σ) (n : ℕ) :
    (Ideal.span {X i} : Ideal (MvPowerSeries σ K)).localQuotientHilbertSamuel n =
      ((Nat.card σ - 1 + n).choose (Nat.card σ - 1) : ℕ∞) := by
  have himg : ({X i} : Set (MvPowerSeries σ K)) = X '' {i} := (Set.image_singleton).symm
  rw [himg, localQuotientHilbertSamuel_span_image_X, Nat.card_coe_set_eq,
    Set.ncard_compl, Set.ncard_singleton]

/-- In a univariate power series ring `MvPowerSeries σ K` (`[Subsingleton σ]`, `i : σ`), the
Hilbert–Samuel value of `Ideal.span {MvPowerSeries.X i ^ k}` at degree `n` equals
`(↑(min (n + 1) k) : ℕ∞)`. -/
theorem localQuotientHilbertSamuel_span_singleton_X_pow_of_subsingleton {σ : Type*}
    (K : Type*) [Field K] [Subsingleton σ] (i : σ) (k n : ℕ) :
    (Ideal.span {X i ^ k} : Ideal (MvPowerSeries σ K)).localQuotientHilbertSamuel n =
      ↑(min (n + 1) k) := by
  let : Unique σ := uniqueOfSubsingleton i
  have hmax : IsLocalRing.maximalIdeal (MvPowerSeries σ K) = Ideal.span {X i} := by
    rw [maximalIdeal_eq_span_range_X,
      show (X : σ → MvPowerSeries σ K) = fun _ ↦ X i from
        funext fun j ↦ congrArg X (Subsingleton.elim j i),
      Set.range_const]
  rw [← Ideal.span_singleton_pow, ← hmax]
  cases k with
  | zero =>
    rw [pow_zero, Ideal.one_eq_top, Ideal.localQuotientHilbertSamuel_top, min_zero, Nat.cast_zero]
  | succ k =>
    rw [localQuotientHilbertSamuel_maximalIdeal_pow_succ,
      localQuotientHilbertSamuel_bot_eq_choose, Fintype.card_unique, Nat.choose_one_right]
    exact congrArg Nat.cast (by omega)

end CoordinateIdeals

section Stabilization

/-- **Lexicographic Hilbert–Samuel stabilization** over `MvPowerSeries σ (K j)` (`[Finite σ]`):
every `toLex`-nonincreasing sequence of Hilbert–Samuel functions realized by ideals `I j`
in `MvPowerSeries σ (K j)` (allowing the coefficient field `K j` to vary with `j`) is eventually
constant (Bierstone–Milman 1989, Theorem 5.2.1). -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le
    {σ : Type*} {K : ℕ → Type*} [∀ j, Field (K j)] [Finite σ]
    (I : ∀ j, Ideal (MvPowerSeries σ (K j)))
    (h : ∀ j, toLex (I (j + 1)).localQuotientHilbertSamuel ≤
      toLex (I j).localQuotientHilbertSamuel) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (I j).localQuotientHilbertSamuel = (I j₀).localQuotientHilbertSamuel := by
  choose D hD using fun j ↦ MvPowerSeries.exists_localQuotientHilbertSamuel_eq_ncard_sdiff (I j)
  have hanti : Antitone fun j ↦ toLex fun ℓ ↦
      ({α : σ →₀ ℕ | α.degree ≤ ℓ} \ (D j : Set (σ →₀ ℕ))).ncard :=
    antitone_nat_of_succ_le fun j ↦
      (strictMono_toLex_comp
        fun (_ : ℕ) ↦ (Nat.strictMono_cast : StrictMono (Nat.cast : ℕ → ℕ∞))).le_iff_le.mp <| by
          simpa only [ofLex_toLex, ← hD] using h j
  obtain ⟨j₀, hj₀⟩ := exists_forall_ge_ncard_sdiff_eq_of_antitone (fun j ↦ (D j).upper) hanti
  refine ⟨j₀, fun j hj ↦ funext fun ℓ ↦ ?_⟩
  rw [hD j, hD j₀]
  exact congrArg Nat.cast (hj₀ j hj ℓ)

/-- **Pointwise Hilbert–Samuel stabilization** over `MvPowerSeries σ (K j)` (`[Finite σ]`): every
pointwise nonincreasing sequence of Hilbert–Samuel functions realized by ideals `I j` in
`MvPowerSeries σ (K j)` is eventually constant. -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_le
    {σ : Type*} {K : ℕ → Type*} [∀ j, Field (K j)] [Finite σ]
    (I : ∀ j, Ideal (MvPowerSeries σ (K j)))
    (h : ∀ j n, (I (j + 1)).localQuotientHilbertSamuel n ≤ (I j).localQuotientHilbertSamuel n) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      (I j).localQuotientHilbertSamuel = (I j₀).localQuotientHilbertSamuel :=
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le I fun j ↦ Pi.toLex_monotone (h j)

end Stabilization

end TauCeti
