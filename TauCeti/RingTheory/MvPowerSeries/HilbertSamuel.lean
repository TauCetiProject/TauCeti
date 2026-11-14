/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Data.Finsupp.PWO
import TauCeti.Data.Finsupp.Weight
import TauCeti.Order.PiLex
import TauCeti.RingTheory.MvPowerSeries.Length

/-!
# Hilbert–Samuel functions of formal power series ideals and lexicographic stabilization

For an ideal `I` in a formal power series ring `MvPowerSeries σ K` over a field `K` in finitely
many variables, Hironaka's formal division theorem identifies `MvPowerSeries σ K ⧸ I` as a
`K`-vector space with the subspace of series supported outside the initial diagram
`MonomialOrder.degLex.initialDiagram I` (`MonomialOrder.quotientEquivComplementSubmodule`,
`MonomialOrder.complementSubmoduleEquivFun`). Passing to `I ⊔ 𝔪 ^ (n + 1)` adjoins all exponents of
total degree at least `n + 1` to the graded lexicographic initial diagram
(`MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow`), while local length over
`MvPowerSeries σ K` agrees with `K`-vector space length (`MvPowerSeries.length_restrictScalars`).
Consequently, `TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I n` counts the exponents
`α : σ →₀ ℕ` of total degree at most `n` outside `degLex.initialDiagram I`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries`, Bierstone–Milman 1997, Corollary 3.20). For
the zero ideal this recovers the binomial count `Nat.choose (Nat.card σ + n) (Nat.card σ)`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`).

Applying Dickson-lemma stabilization of degree-bounded complement counts for sequences of upper
sets in `σ →₀ ℕ` (`TauCeti.exists_forall_ge_card_degree_le_notMem_eq_of_isUpperSet`) to graded
lexicographic initial diagrams yields lexicographic stabilization
(`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_lex`, `TauCeti.hsLexStabilization`) and
hence pointwise stabilization (`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_le`) for
Hilbert–Samuel functions of ideals in `MvPowerSeries σ K` (Bierstone–Milman 1989, Theorem 5.2.1;
Bierstone–Milman–Temkin 2011, §6.1).

## Main results

* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries`: `H_I(n)` equals the `Nat.card` of
  `{α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ degLex.initialDiagram I}`.
* `TauCeti.localQuotientHilbertSamuel_eq_of_initialDiagram_degLex_eq`: ideals with equal
  `degLex.initialDiagram` have equal Hilbert–Samuel functions.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_image_X`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X_pow_of_subsingleton`: explicit
  evaluations for `⊥`, coordinate ideals `Ideal.span (X '' S)`, coordinate hyperplanes `(X i)`, and
  univariate monomial powers `(X i ^ k)`.
* `TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_lex`,
  `TauCeti.hsLexStabilization`,
  `TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_le`: lexicographic and pointwise
  stabilization of realized Hilbert–Samuel functions in `MvPowerSeries σ K` and
  `MvPowerSeries (Fin n) K`.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239, and §9, p. 276.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *$\mathbb{Q}$-universal
  desingularization*, Asian J. Math. 15 (2011), 229–250, §6.1.
-/

public section

open scoped MonomialOrder

namespace TauCeti

section FormalHilbertSamuel

/-- **Bierstone–Milman Corollary 3.20**: over a field `K` in finitely many linearly ordered
variables `σ`, `localQuotientHilbertSamuel (MvPowerSeries σ K) I n` counts the exponents of total
degree at most `n` outside `degLex.initialDiagram I`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I n =
      (Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram I} : ℕ∞) := by
  set J : Ideal (MvPowerSeries σ K) := I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ (n + 1)
  have hmem : ∀ α : σ →₀ ℕ,
      α ∉ MonomialOrder.degLex.initialDiagram J ↔
        α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram I := by
    intro α
    rw [MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow]
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Nat.lt_succ_iff, and_comm]
  let idxEquiv : {α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J} ≃
      {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram I} :=
    Equiv.subtypeEquivRight hmem
  have hsub : {α : σ →₀ ℕ | α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram I} ⊆
      {α : σ →₀ ℕ | α.degree ≤ n} := fun _ hα ↦ hα.1
  have hfin : Finite {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram I} :=
    ((Finsupp.finite_of_degree_le n).subset hsub).to_subtype
  set d := Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram I}
  let finEquiv : {α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J} ≃ Fin d :=
    idxEquiv.trans (Finite.equivFin _)
  let linEquiv : (MvPowerSeries σ K ⧸ J) ≃ₗ[K] (Fin d → K) :=
    ((MonomialOrder.degLex.quotientEquivComplementSubmodule J).trans
      (MonomialOrder.degLex.complementSubmoduleEquivFun J)).trans
      (LinearEquiv.funCongrLeft K K finEquiv.symm)
  rw [localQuotientHilbertSamuel_def, MvPowerSeries.length_restrictScalars (R := K),
    linEquiv.length_eq, Module.length_eq_finrank, Module.finrank_fin_fun]

/-- Two ideals of `MvPowerSeries σ K` with the same graded lexicographic initial diagram have the
same Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_eq_of_initialDiagram_degLex_eq {σ K : Type*} [Field K]
    [Finite σ] [LinearOrder σ] {I J : Ideal (MvPowerSeries σ K)}
    (h : MonomialOrder.degLex.initialDiagram I = MonomialOrder.degLex.initialDiagram J) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I =
      localQuotientHilbertSamuel (MvPowerSeries σ K) J := by
  ext n
  rw [localQuotientHilbertSamuel_mvPowerSeries, localQuotientHilbertSamuel_mvPowerSeries, h]

/-- For the zero ideal in `MvPowerSeries σ K` (`[Finite σ]`), the Hilbert–Samuel value at degree
`n` is `((Nat.card σ + n).choose (Nat.card σ) : ℕ∞)`. -/
@[simp]
theorem localQuotientHilbertSamuel_mvPowerSeries_bot (σ K : Type*) [Field K] [Finite σ] (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) ⊥ n =
      ((Nat.card σ + n).choose (Nat.card σ) : ℕ∞) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  rw [localQuotientHilbertSamuel_mvPowerSeries]
  have hcongr : {α : σ →₀ ℕ //
      α.degree ≤ n ∧ α ∉ MonomialOrder.degLex.initialDiagram (⊥ : Ideal (MvPowerSeries σ K))} ≃
      {α : σ →₀ ℕ // α.degree ≤ n} :=
    Equiv.subtypeEquivRight fun _ ↦ by simp
  rw [Nat.card_congr hcongr, Finsupp.natCard_degree_le]

/-- For any subset `S : Set σ` of finitely many variables, the Hilbert–Samuel value of the
coordinate ideal `Ideal.span (MvPowerSeries.X '' S)` at degree `n` is
`((Nat.card ↥Sᶜ + n).choose (Nat.card ↥Sᶜ) : ℕ∞)`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_span_image_X {σ : Type*} (K : Type*) [Field K]
    [Finite σ] (S : Set σ) (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) (Ideal.span (MvPowerSeries.X '' S)) n =
      ((Nat.card ↥Sᶜ + n).choose (Nat.card ↥Sᶜ) : ℕ∞) := by
  classical
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  rw [localQuotientHilbertSamuel_mvPowerSeries]
  have hspan : (MvPowerSeries.X '' S : Set (MvPowerSeries σ K)) =
      (fun α ↦ MvPowerSeries.monomial α (1 : K)) '' ((fun i ↦ Finsupp.single i 1) '' S) := by
    ext f
    simp [MvPowerSeries.X_def]
  rw [hspan, MonomialOrder.degLex.initialDiagram_span_monomial]
  have hnotMem : ∀ α : σ →₀ ℕ,
      (α ∉ ⋃ β ∈ (fun i ↦ Finsupp.single i 1) '' S, Set.Ici β) ↔ ↑α.support ⊆ Sᶜ := fun α ↦ by
    simp [Finsupp.single_le_iff, Set.subset_compl_iff_disjoint_right, Set.disjoint_left]
    grind
  let e₁ : {α : σ →₀ ℕ //
      α.degree ≤ n ∧ α ∉ ⋃ β ∈ (fun i ↦ Finsupp.single i 1) '' S, Set.Ici β} ≃
      {α : {α : σ →₀ ℕ // ↑α.support ⊆ Sᶜ} // α.1.degree ≤ n} :=
    (Equiv.subtypeEquivRight fun α ↦ and_congr_right fun _ ↦ hnotMem α).trans
      ((Equiv.subtypeEquivRight fun _ ↦ and_comm).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm)
  let e₂ : {α : {α : σ →₀ ℕ // ↑α.support ⊆ Sᶜ} // α.1.degree ≤ n} ≃
      {β : ↥Sᶜ →₀ ℕ // β.degree ≤ n} :=
    Equiv.subtypeEquiv (Finsupp.restrictSupportEquiv Sᶜ ℕ) fun α ↦ by
      have hdeg : ((Finsupp.restrictSupportEquiv Sᶜ ℕ).symm
          (Finsupp.restrictSupportEquiv Sᶜ ℕ α)).1.degree =
          (Finsupp.restrictSupportEquiv Sᶜ ℕ α).degree := by
        rw [Finsupp.restrictSupportEquiv_symm_apply_coe, Finsupp.extendDomain_eq_embDomain_subtype,
          Finsupp.embDomain_eq_mapDomain, Finsupp.degree_mapDomain]
      rw [Equiv.symm_apply_apply] at hdeg
      rw [hdeg]
  rw [Nat.card_congr (e₁.trans e₂), Finsupp.natCard_degree_le]

/-- For any variable `i : σ` in finitely many variables, the Hilbert–Samuel value of
`Ideal.span {MvPowerSeries.X i}` at degree `n` is
`((Nat.card σ - 1 + n).choose (Nat.card σ - 1) : ℕ∞)`. -/
@[simp]
theorem localQuotientHilbertSamuel_mvPowerSeries_span_X {σ : Type*} (K : Type*) [Field K]
    [Finite σ] (i : σ) (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) (Ideal.span {MvPowerSeries.X i}) n =
      ((Nat.card σ - 1 + n).choose (Nat.card σ - 1) : ℕ∞) := by
  have himg : ({MvPowerSeries.X i} : Set (MvPowerSeries σ K)) = MvPowerSeries.X '' {i} :=
    (Set.image_singleton).symm
  rw [himg, localQuotientHilbertSamuel_mvPowerSeries_span_image_X, Nat.card_coe_set_eq,
    Set.ncard_compl, Set.ncard_singleton]

/-- In a univariate power series ring `MvPowerSeries σ K` (`[Subsingleton σ]`, `i : σ`), the
Hilbert–Samuel value of `Ideal.span {X i ^ k}` at degree `n` equals `(↑(min (n + 1) k) : ℕ∞)`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_span_X_pow_of_subsingleton {σ : Type*}
    (K : Type*) [Field K] [Subsingleton σ] (i : σ) (k n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K)
        (Ideal.span {MvPowerSeries.X i ^ k}) n = ↑(min (n + 1) k) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  rw [localQuotientHilbertSamuel_mvPowerSeries]
  have hspan : ({MvPowerSeries.X i ^ k} : Set (MvPowerSeries σ K)) =
      (fun α ↦ MvPowerSeries.monomial α (1 : K)) '' {Finsupp.single i k} := by
    simp [MvPowerSeries.X_pow_eq]
  rw [hspan, MonomialOrder.degLex.initialDiagram_span_monomial, Set.biUnion_singleton]
  have hdeg : ∀ α : σ →₀ ℕ, α.degree = α i := fun α ↦ by
    have hEq : α = Finsupp.single i (α i) := ((Finsupp.uniqueEquiv i).symm_apply_apply α).symm
    conv_lhs => rw [hEq, Finsupp.degree_single]
  let hbij : {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ Set.Ici (Finsupp.single i k)} ≃
      Fin (min (n + 1) k) :=
    (Equiv.subtypeEquiv (Finsupp.uniqueEquiv i) fun α ↦ by
      rw [Set.mem_Ici, Finsupp.single_le_iff, hdeg α, Finsupp.uniqueEquiv_apply, not_le,
        ← Nat.lt_succ_iff, ← lt_min_iff]).trans Fin.equivSubtype.symm
  rw [Nat.card_congr hbij, Nat.card_fin]

end FormalHilbertSamuel

section Stabilization

/-- **Lexicographic Hilbert–Samuel stabilization** over `MvPowerSeries σ K` (`[Finite σ]`): every
lexicographically nonincreasing sequence of Hilbert–Samuel functions realized by ideals in
`MvPowerSeries σ K` is eventually constant (Bierstone–Milman 1989, Theorem 5.2.1). -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_lex {σ K : Type*} [Field K] [Finite σ]
    (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j, toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1))) ≤
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  let D : ℕ → Set (σ →₀ ℕ) := fun j ↦ MonomialOrder.degLex.initialDiagram (I j)
  let dCount (j n : ℕ) : ℕ := Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D j}
  have hval : ∀ j n, localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) n =
      (dCount j n : ℕ∞) := fun j n ↦
    localQuotientHilbertSamuel_mvPowerSeries (I j) n
  have hlex : ∀ j, toLex (dCount (j + 1)) ≤ toLex (dCount j) := fun j ↦ by
    rw [Pi.Lex.toLex_le_toLex]
    rcases Pi.Lex.toLex_le_toLex.mp (h j) with heq | ⟨m, hprev, hltm⟩
    · refine Or.inl (funext fun n ↦ ?_)
      exact Nat.cast_inj.mp ((hval (j + 1) n).symm.trans ((congr_fun heq n).trans (hval j n)))
    · refine Or.inr ⟨m, fun k hk ↦ ?_, ?_⟩
      · exact Nat.cast_inj.mp ((hval (j + 1) k).symm.trans ((hprev k hk).trans (hval j k)))
      · exact Nat.cast_lt.mp ((hval (j + 1) m).symm ▸ (hval j m).symm ▸ hltm)
  obtain ⟨j₀, hj₀⟩ := exists_forall_ge_card_degree_le_notMem_eq_of_isUpperSet D
    (fun j ↦ MonomialOrder.degLex.isUpperSet_initialDiagram (I j)) hlex
  refine ⟨j₀, fun j hj ↦ funext fun n ↦ ?_⟩
  rw [hval j n, hval j₀ n]
  exact congrArg Nat.cast (congr_fun (hj₀ j hj) n)

/-- **Lexicographic Hilbert–Samuel stabilization** in `MvPowerSeries (Fin n) K`: every
lexicographically nonincreasing sequence of realized Hilbert–Samuel functions stabilizes. -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) :=
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_lex I fun j ↦ Pi.Lex.toLex_le_toLex.mpr (h j)

/-- **Pointwise Hilbert–Samuel stabilization** over `MvPowerSeries σ K` (`[Finite σ]`): every
pointwise nonincreasing sequence of Hilbert–Samuel functions realized by ideals in
`MvPowerSeries σ K` is eventually constant. -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_le {σ K : Type*} [Field K] [Finite σ]
    (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j n, localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) n ≤
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) n) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) :=
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_lex I fun j ↦ Pi.toLex_monotone (h j)

end Stabilization

section Examples

/-- For `K⟦X⟧ ⧸ (X²)`, the Hilbert–Samuel function takes value `1` at `0` and `2` for every
`ℓ ≥ 1`. -/
example (K : Type*) [Field K] :
    localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
        (Ideal.span {MvPowerSeries.X 0 ^ 2}) 0 = 1 ∧
      ∀ ℓ, 1 ≤ ℓ →
        localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
          (Ideal.span {MvPowerSeries.X 0 ^ 2}) ℓ = 2 := by
  refine ⟨by simp [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow_of_subsingleton],
    fun ℓ hℓ ↦ ?_⟩
  rw [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow_of_subsingleton, min_eq_right (by omega)]
  rfl

/-- For `I_j = (X ^ max (N - j) 1) ⊆ K⟦X⟧`, the Hilbert–Samuel functions decrease in both orders
and stabilize at the constant function `1` of `K⟦X⟧ ⧸ (X)` for `j ≥ N`. -/
example (K : Type*) [Field K] (N : ℕ) :
    let I : ℕ → Ideal (MvPowerSeries (Fin 1) K) :=
      fun j ↦ Ideal.span {MvPowerSeries.X 0 ^ max (N - j) 1}
    (∀ j ℓ, localQuotientHilbertSamuel _ (I (j + 1)) ℓ ≤ localQuotientHilbertSamuel _ (I j) ℓ) ∧
      ∀ j, N ≤ j →
        localQuotientHilbertSamuel _ (I j) =
          localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
            (Ideal.span {MvPowerSeries.X (0 : Fin 1)}) := by
  intro I
  refine ⟨fun j ℓ ↦ ?_, fun j hj ↦ ?_⟩
  · simp only [I, localQuotientHilbertSamuel_mvPowerSeries_span_X_pow_of_subsingleton, Nat.cast_le]
    omega
  · have hmax : max (N - j) 1 = 1 := by omega
    simp [I, hmax]

/-- In `K⟦X₀, X₁⟧`, the length-three fat point `I₁ = 𝔪²` (`H = (1, 3, 3, 3, …)`) and the smooth
line `I₂ = (X₀)` (`H = (1, 2, 3, 4, …)`) have pointwise incomparable Hilbert–Samuel functions, yet
`H(I₂)` is strictly lexicographically smaller than `H(I₁)`. -/
example (K : Type*) [Field K] :
    let I₁ : Ideal (MvPowerSeries (Fin 2) K) :=
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) K) ^ 2
    let I₂ : Ideal (MvPowerSeries (Fin 2) K) := Ideal.span {MvPowerSeries.X 0}
    let H₁ := localQuotientHilbertSamuel (MvPowerSeries (Fin 2) K) I₁
    let H₂ := localQuotientHilbertSamuel (MvPowerSeries (Fin 2) K) I₂
    ¬ (H₂ ≤ H₁) ∧ ¬ (H₁ ≤ H₂) ∧ Pi.Lex (· < ·) (· < ·) H₂ H₁ := by
  intro I₁ I₂ H₁ H₂
  have hH₁ : ∀ n, 1 ≤ n → H₁ n = 3 := fun n hn ↦ by
    dsimp only [H₁, I₁]
    rw [localQuotientHilbertSamuel_maximalIdeal_pow_succ (A := MvPowerSeries (Fin 2) K) 1 n,
      min_eq_left hn, localQuotientHilbertSamuel_mvPowerSeries_bot, Nat.card_fin]
    decide
  have hH₂ : ∀ n, H₂ n = (n + 1 : ℕ∞) := fun n ↦ by
    simp [H₂, I₂, Nat.add_comm 1 n]
  have hH₁_0 : H₁ 0 = 1 :=
    localQuotientHilbertSamuel_zero_of_ne_top
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.pow_le_self two_ne_zero))
  refine ⟨fun hle ↦ ?_, fun hle ↦ ?_, ⟨1, fun j hj ↦ ?_, ?_⟩⟩
  · have h3 := hle 3
    rw [hH₂ 3, hH₁ 3 (by omega)] at h3
    norm_num at h3
  · have h1 := hle 1
    rw [hH₁ 1 le_rfl, hH₂ 1] at h1
    norm_num at h1
  · obtain rfl : j = 0 := by omega
    rw [hH₂ 0, hH₁_0]
    norm_num
  · rw [hH₂ 1, hH₁ 1 le_rfl]
    norm_num

/-- Realizability as Hilbert–Samuel functions is essential for `hsLexStabilization`: the sequence
`f j ℓ = if j ≤ ℓ then 1 else 0` decreases strictly in the lexicographic order at every step and
never stabilizes, and for `j ≥ 1` none of its terms is realized by any ideal of `A`. -/
example (A : Type*) [CommRing A] [IsLocalRing A] :
    let f : ℕ → ℕ → ℕ∞ := fun j ℓ ↦ if j ≤ ℓ then 1 else 0
    (∀ j, Pi.Lex (· < ·) (· < ·) (f (j + 1)) (f j)) ∧
      (∀ j₀, f (j₀ + 1) ≠ f j₀) ∧
      ∀ j, 1 ≤ j → ∀ I : Ideal A, localQuotientHilbertSamuel A I ≠ f j := by
  intro f
  refine ⟨fun j ↦ ⟨j, fun m hm ↦ ?_, ?_⟩, fun j₀ hEq ↦ ?_, fun j hj I hEq ↦ ?_⟩
  · simp [f, Nat.not_le_of_lt hm, Nat.not_le_of_lt (Nat.lt_succ_of_lt hm)]
  · simp [f]
  · have h := congr_fun hEq j₀
    simp [f] at h
  · have h0 : localQuotientHilbertSamuel A I 0 = 0 := by
      simpa [f, Nat.not_le_of_lt hj] using congr_fun hEq 0
    have htop : I = ⊤ := localQuotientHilbertSamuel_eq_zero_iff.mp h0
    have hj_eq : localQuotientHilbertSamuel A I j = 1 := by
      simpa [f] using congr_fun hEq j
    rw [htop, localQuotientHilbertSamuel_top] at hj_eq
    exact zero_ne_one hj_eq

end Examples

end TauCeti
