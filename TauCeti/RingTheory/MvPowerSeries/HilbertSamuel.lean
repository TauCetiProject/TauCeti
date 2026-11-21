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
`MvPowerSeries σ K` agrees with `K`-vector space length
(`TauCeti.length_mvPowerSeries_restrictScalars`).
Consequently, `TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I n` counts the exponents
`α : σ →₀ ℕ` of total degree at most `n` outside `degLex.initialDiagram I`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries`, Bierstone–Milman 1997, Corollary 3.20). For
the zero ideal this recovers the binomial count `Nat.choose (Nat.card σ + n) (Nat.card σ)`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`).

Applying Dickson-lemma stabilization of degree-bounded complement counts for sequences of upper
sets in `σ →₀ ℕ` (`TauCeti.exists_forall_ge_natCard_degree_le_notMem_eq_of_isUpperSet`) to graded
lexicographic initial diagrams yields lexicographic stabilization
(`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le`, `TauCeti.hsLexStabilization`)
and hence pointwise stabilization (`TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_le`)
for Hilbert–Samuel functions of ideals in `MvPowerSeries σ (K j)` across possibly varying
coefficient fields `K j` (Bierstone–Milman 1989, Theorem 5.2.1; Bierstone–Milman–Temkin 2011,
§6.1).

## Main results

* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries`: `H_I(n)` equals the `Nat.card` of
  `{α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ degLex.initialDiagram I}`.
* `TauCeti.localQuotientHilbertSamuel_eq_of_initialDiagram_degLex_eq`: ideals over possibly
  distinct fields with equal `degLex.initialDiagram` have equal Hilbert–Samuel functions.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_image_X`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X_pow_of_subsingleton`: explicit
  evaluations for `⊥`, coordinate ideals `Ideal.span (X '' S)`, coordinate hyperplanes `(X i)`, and
  univariate monomial powers `(X i ^ k)`.
* `TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le`,
  `TauCeti.hsLexStabilization`,
  `TauCeti.exists_forall_ge_localQuotientHilbertSamuel_eq_of_le`: lexicographic and pointwise
  stabilization of realized Hilbert–Samuel functions in `MvPowerSeries σ (K j)` and
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
  have : Finite {α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J} :=
    .of_equiv _ idxEquiv.symm
  let _ := Fintype.ofFinite {α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J}
  let linEquiv : (MvPowerSeries σ K ⧸ J) ≃ₗ[K]
      ({α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J} → K) :=
    (MonomialOrder.degLex.quotientEquivComplementSubmodule J).trans
      (MonomialOrder.degLex.complementSubmoduleEquivFun J)
  rw [localQuotientHilbertSamuel_def, ← length_mvPowerSeries_restrictScalars (R := K),
    linEquiv.length_eq, Module.length_eq_finrank, Module.finrank_pi,
    ← Nat.card_eq_fintype_card, Nat.card_congr idxEquiv]

/-- Two ideals of `MvPowerSeries σ K₁` and `MvPowerSeries σ K₂` with the same graded lexicographic
initial diagram have the same Hilbert–Samuel function. -/
theorem localQuotientHilbertSamuel_eq_of_initialDiagram_degLex_eq
    {σ : Type*} {K₁ : Type*} {K₂ : Type*} [Field K₁] [Field K₂] [Finite σ] [LinearOrder σ]
    {I : Ideal (MvPowerSeries σ K₁)} {J : Ideal (MvPowerSeries σ K₂)}
    (h : MonomialOrder.degLex.initialDiagram I = MonomialOrder.degLex.initialDiagram J) :
    localQuotientHilbertSamuel (MvPowerSeries σ K₁) I =
      localQuotientHilbertSamuel (MvPowerSeries σ K₂) J := by
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
@[simp]
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

/-- **Lexicographic Hilbert–Samuel stabilization** over `MvPowerSeries σ (K j)` (`[Finite σ]`):
every `toLex`-nonincreasing sequence of Hilbert–Samuel functions realized by ideals `I j`
in `MvPowerSeries σ (K j)` (allowing the coefficient field `K j` to vary with `j`) is eventually
constant (Bierstone–Milman 1989, Theorem 5.2.1). -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le
    {σ : Type*} {K : ℕ → Type*} [∀ j, Field (K j)] [Finite σ]
    (I : ∀ j, Ideal (MvPowerSeries σ (K j)))
    (h : ∀ j, toLex (localQuotientHilbertSamuel (MvPowerSeries σ (K (j + 1))) (I (j + 1))) ≤
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ (K j)) (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ (K j)) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ (K j₀)) (I j₀) := by
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  let D : ℕ → Set (σ →₀ ℕ) := fun j ↦ MonomialOrder.degLex.initialDiagram (I j)
  let dCount (j n : ℕ) : ℕ := Nat.card {α : σ →₀ ℕ // α.degree ≤ n ∧ α ∉ D j}
  have hval : ∀ j n, localQuotientHilbertSamuel (MvPowerSeries σ (K j)) (I j) n =
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
  obtain ⟨j₀, hj₀⟩ := exists_forall_ge_natCard_degree_le_notMem_eq_of_isUpperSet D
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
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le I
    fun j ↦ Pi.Lex.toLex_le_toLex.mpr (h j)

/-- **Pointwise Hilbert–Samuel stabilization** over `MvPowerSeries σ (K j)` (`[Finite σ]`): every
pointwise nonincreasing sequence of Hilbert–Samuel functions realized by ideals `I j` in
`MvPowerSeries σ (K j)` is eventually constant. -/
theorem exists_forall_ge_localQuotientHilbertSamuel_eq_of_le
    {σ : Type*} {K : ℕ → Type*} [∀ j, Field (K j)] [Finite σ]
    (I : ∀ j, Ideal (MvPowerSeries σ (K j)))
    (h : ∀ j n, localQuotientHilbertSamuel (MvPowerSeries σ (K (j + 1))) (I (j + 1)) n ≤
      localQuotientHilbertSamuel (MvPowerSeries σ (K j)) (I j) n) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ (K j)) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ (K j₀)) (I j₀) :=
  exists_forall_ge_localQuotientHilbertSamuel_eq_of_toLex_le I fun j ↦ Pi.toLex_monotone (h j)

end Stabilization

end TauCeti
