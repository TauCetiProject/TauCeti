/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Order.WellFoundedSet
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.MvPowerSeries.Rename
import TauCeti.RingTheory.Length

/-!
# Hilbert–Samuel functions and stabilization in multivariate formal power series rings

Over a field `K` in finitely many variables `σ`, formal division with respect to graded
lexicographic order (`MonomialOrder.degLex`) expresses the local quotient Hilbert–Samuel function
`TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I` at jet cutoff `n` as the number of
monomial exponents of total degree at most `n` outside Hironaka's diagram of initial exponents
`degLex.initialDiagram I` (`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_ncard`).

Specializing to `I = ⊥` recovers `localHilbertSamuel (MvPowerSeries σ K) n =
(n + Fintype.card σ).choose (Fintype.card σ)` (`TauCeti.localHilbertSamuel_mvPowerSeries`), and
specializing to `(X ^ k)` in one variable yields `min (n + 1) k`
(`TauCeti.localQuotientHilbertSamuel_span_X_pow`,
`TauCeti.localQuotientHilbertSamuel_powerSeries_span_X_pow`).

Because `degLex.initialDiagram I` is an upper set in `σ →₀ ℕ`, Dickson's lemma controls the set of
all Hilbert–Samuel functions realized by ideals in a fixed finite-variable power series ring:
`toLex '' Set.range (localQuotientHilbertSamuel (MvPowerSeries σ K))` is well-founded in
`Lex (ℕ → ℕ∞)` (`TauCeti.isWF_toLex_range_localQuotientHilbertSamuel_mvPowerSeries`). Consequently,
every lexicographically nonincreasing sequence of realized Hilbert–Samuel functions eventually
stabilizes (`TauCeti.exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_lex`,
`TauCeti.hsLexStabilization`), and in particular every pointwise nonincreasing sequence stabilizes
(`TauCeti.exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone`). By contrast,
arbitrary sequences in `Lex (ℕ → ℕ∞)` need not stabilize
(`TauCeti.strictAnti_toLex_ite_lt`), showing that realizability in fixed embedding dimension is
essential.

## Main results

* `MvPowerSeries.length_eq_length_base`: over any commutative local ring `A`, `MvPowerSeries σ A`-
  module length agrees with `A`-module length.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_ncard`: for `[LinearOrder σ] [Finite σ]
  [Field K]`, `localQuotientHilbertSamuel (MvPowerSeries σ K) I n` counts `{α | α.degree ≤ n ∧
  α ∉ degLex.initialDiagram I}`.
* `TauCeti.localHilbertSamuel_mvPowerSeries`, `TauCeti.localHilbertSamuel_mvPowerSeries_fin`,
  `TauCeti.localQuotientHilbertSamuel_span_X_pow`: explicit Hilbert–Samuel formulas for `K⟦X_σ⟧`
  and `K⟦X⟧ ⧸ (X ^ k)`.
* `TauCeti.isWF_toLex_range_localQuotientHilbertSamuel_mvPowerSeries`: well-foundedness of realized
  Hilbert–Samuel functions in `Lex (ℕ → ℕ∞)`.
* `TauCeti.exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_lex`,
  `TauCeti.hsLexStabilization`,
  `TauCeti.exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone`: lexicographic
  and pointwise stabilization of realized Hilbert–Samuel functions.

## References

* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239.
* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  10 (1997), 809–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*, Asian J.
  Math. 15 (2011), 229–250, §6.1.
-/

public section

open IsLocalRing MonomialOrder
open scoped MonomialOrder

namespace MvPowerSeries

/-- Over any commutative local ring `A`, `MvPowerSeries σ A` has the same residue field as `A`, so
`MvPowerSeries σ A`-module length equals `A`-module length on any `MvPowerSeries σ A`-module `M`. -/
theorem length_eq_length_base {σ A M : Type*} [CommRing A] [IsLocalRing A] [AddCommGroup M]
    [Module A M] [Module (MvPowerSeries σ A) M] [IsScalarTower A (MvPowerSeries σ A) M] :
    Module.length (MvPowerSeries σ A) M = Module.length A M := by
  have hsurj : Function.Surjective
      (algebraMap (ResidueField A) (ResidueField (MvPowerSeries σ A))) := by
    intro x
    obtain ⟨f, rfl⟩ := residue_surjective x
    refine ⟨residue A (constantCoeff f), ?_⟩
    change ResidueField.map (algebraMap A (MvPowerSeries σ A)) (residue A (constantCoeff f)) =
      residue (MvPowerSeries σ A) f
    rw [ResidueField.map_residue, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    refine Ideal.Quotient.eq.mpr ?_
    rw [maximalIdeal_eq_comap_constantCoeff, Ideal.mem_comap, map_sub, constantCoeff_C, sub_self]
    exact zero_mem _
  have hres : Module.length (ResidueField A) (ResidueField (MvPowerSeries σ A)) = 1 := by
    rw [Module.length_eq_one_iff,
      isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
        (S := ResidueField (MvPowerSeries σ A)) hsurj]
    exact instIsSimpleModule _
  rw [IsLocalRing.length_restrictScalars A (MvPowerSeries σ A) M, hres, mul_one]

end MvPowerSeries

namespace TauCeti

section DegreeBall

/-- In `d = Fintype.card σ` variables, the number of multi-indices `α : σ →₀ ℕ` of total degree at
most `n` is `(n + d).choose d`. -/
private theorem ncard_setOf_degree_le (σ : Type*) [Fintype σ] (n : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ n}.ncard = (n + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  have hset : {α : σ →₀ ℕ | α.degree ≤ n} =
      ↑((Finset.range (n + 1)).biUnion ((Finset.univ : Finset σ).finsuppAntidiag ·)) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp [Finset.card_finsuppAntidiag_nat_eq_multichoose, Nat.sum_range_multichoose]
  · intro k _ l _ hkl
    refine Finset.disjoint_left.mpr fun α hk hl ↦ hkl ?_
    rw [Finset.mem_finsuppAntidiag] at hk hl
    exact hk.1.symm.trans hl.1

end DegreeBall

section CountingFormula

/-- **Bierstone–Milman Corollary 3.20**: for an ideal `I` of `MvPowerSeries σ K` over a field `K` in
finitely many linearly ordered variables `σ`, `localQuotientHilbertSamuel (MvPowerSeries σ K) I n`
is the number of exponents `α : σ →₀ ℕ` with `α.degree ≤ n` and `α ∉ degLex.initialDiagram I`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_eq_ncard {σ K : Type*} [LinearOrder σ] [Finite σ]
    [Field K] (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I n =
      ({α : σ →₀ ℕ | α.degree ≤ n ∧ α ∉ degLex.initialDiagram I}.ncard : ℕ∞) := by
  let J : Ideal (MvPowerSeries σ K) := I ⊔ maximalIdeal (MvPowerSeries σ K) ^ (n + 1)
  have hcompl : (degLex.initialDiagram J)ᶜ =
      {α : σ →₀ ℕ | α.degree ≤ n ∧ α ∉ degLex.initialDiagram I} := by
    ext α
    simp only [J, initialDiagram_degLex_sup_maximalIdeal_pow, Set.mem_compl_iff, Set.mem_union,
      Set.mem_ofPred_eq, not_or, not_le, Nat.lt_succ_iff, and_comm]
  have hfin : (degLex.initialDiagram J)ᶜ.Finite := by
    rw [hcompl]
    exact (Finsupp.finite_of_degree_le n).subset fun _ h ↦ h.1
  cases hfin.nonempty_fintype
  rw [localQuotientHilbertSamuel_def, MvPowerSeries.length_eq_length_base (A := K),
    (degLex.quotientEquivPiNotMemInitialDiagram J).length_eq,
    Module.length_eq_finrank K (↥(degLex.initialDiagram J)ᶜ → K),
    Module.finrank_pi K, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hcompl]

/-- Natural-number form of `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_ncard`. -/
theorem toNat_localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [LinearOrder σ] [Finite σ]
    [Field K] (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    (localQuotientHilbertSamuel (MvPowerSeries σ K) I n).toNat =
      {α : σ →₀ ℕ | α.degree ≤ n ∧ α ∉ degLex.initialDiagram I}.ncard := by
  rw [localQuotientHilbertSamuel_mvPowerSeries_eq_ncard, ENat.toNat_natCast]

/-- In finitely many variables `σ` over a field `K`, every value of
`localQuotientHilbertSamuel (MvPowerSeries σ K) I` is finite. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_lt_top {σ K : Type*} [Finite σ] [Field K]
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I n < ⊤ := by
  obtain ⟨d, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let φ := (MvPowerSeries.renameEquiv (R := K) e).toRingEquiv
  rw [← φ.localQuotientHilbertSamuel_map I, localQuotientHilbertSamuel_mvPowerSeries_eq_ncard]
  exact ENat.natCast_lt_top _

theorem localQuotientHilbertSamuel_mvPowerSeries_ne_top {σ K : Type*} [Finite σ] [Field K]
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I n ≠ ⊤ :=
  (localQuotientHilbertSamuel_mvPowerSeries_lt_top I n).ne

/-- For `K⟦X_σ⟧` in `d = Fintype.card σ` variables over a field `K`,
`localHilbertSamuel (MvPowerSeries σ K) n = (n + d).choose d`. -/
theorem localHilbertSamuel_mvPowerSeries (σ K : Type*) [Fintype σ] [Field K] (n : ℕ) :
    localHilbertSamuel (MvPowerSeries σ K) n =
      ((n + Fintype.card σ).choose (Fintype.card σ) : ℕ) := by
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  rw [(MvPowerSeries.renameEquiv (R := K) e).toRingEquiv.localHilbertSamuel_eq,
    localHilbertSamuel_def, localQuotientHilbertSamuel_mvPowerSeries_eq_ncard]
  simp [ncard_setOf_degree_le]

@[simp]
theorem localHilbertSamuel_mvPowerSeries_fin (K : Type*) [Field K] (d n : ℕ) :
    localHilbertSamuel (MvPowerSeries (Fin d) K) n = ((d + n).choose d : ℕ) := by
  rw [localHilbertSamuel_mvPowerSeries, Fintype.card_fin, add_comm]

/-- Over a field `K` in a single variable `σ` (`[Unique σ]`), the quotient modulo `(X ^ k)` has
Hilbert–Samuel function `n ↦ min (n + 1) k` (in particular, `1` at `n = 0` and `2` for `n ≥ 1`
when `k = 2`). -/
theorem localQuotientHilbertSamuel_span_X_pow {σ K : Type*} [Unique σ] [Field K] (k n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K)
      (Ideal.span {MvPowerSeries.X (default : σ) ^ k}) n = (min (n + 1) k : ℕ) := by
  let e : σ ≃ Fin 1 := Equiv.ofUnique σ (Fin 1)
  let φ := (MvPowerSeries.renameEquiv (R := K) e).toRingEquiv
  have hmap :
      (Ideal.span {MvPowerSeries.X (default : σ) ^ k}).map
        (φ : MvPowerSeries σ K →+* MvPowerSeries (Fin 1) K) =
      Ideal.span {(MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ k} := by
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    have hX : φ (MvPowerSeries.X (default : σ)) = MvPowerSeries.X (0 : Fin 1) := by
      change MvPowerSeries.rename e (MvPowerSeries.X default) = MvPowerSeries.X 0
      rw [MvPowerSeries.rename_X, Subsingleton.elim (e default) 0]
    simp [hX]
  have hspan : Ideal.span {(MvPowerSeries.X (0 : Fin 1) : MvPowerSeries (Fin 1) K) ^ k} =
      Ideal.span ((fun α ↦ MvPowerSeries.monomial α (1 : K)) '' {Finsupp.single 0 k}) := by
    rw [Set.image_singleton, MvPowerSeries.X_pow_eq]
  rw [← φ.localQuotientHilbertSamuel_map, hmap, hspan,
    localQuotientHilbertSamuel_mvPowerSeries_eq_ncard, degLex.initialDiagram_span_monomial]
  have hset : {α : Fin 1 →₀ ℕ |
      α.degree ≤ n ∧ α ∉ ⋃ β ∈ ({Finsupp.single 0 k} : Set (Fin 1 →₀ ℕ)), Set.Ici β} =
      (fun m : ℕ ↦ Finsupp.single (0 : Fin 1) m) '' ↑(Finset.range (min (n + 1) k)) := by
    ext α
    simp only [Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left, Set.mem_Ici, Finsupp.single_le_iff,
      not_le, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, Finset.mem_range, lt_min_iff,
      Nat.lt_succ_iff]
    refine ⟨fun ⟨hdeg, hlt⟩ ↦ ⟨α 0, ⟨?_, hlt⟩, (Finsupp.unique_single α).symm⟩, ?_⟩
    · rwa [Finsupp.unique_single α, Subsingleton.elim (default : Fin 1) 0,
        Finsupp.degree_single] at hdeg
    · rintro ⟨m, ⟨hmn, hmk⟩, rfl⟩
      simp [hmn, hmk]
  have hinj : Function.Injective (fun m : ℕ ↦ Finsupp.single (0 : Fin 1) m) :=
    Finsupp.single_injective 0
  rw [hset, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]

/-- Univariate `PowerSeries` specialization of `TauCeti.localQuotientHilbertSamuel_span_X_pow`. -/
theorem localQuotientHilbertSamuel_powerSeries_span_X_pow (K : Type*) [Field K] (k n : ℕ) :
    localQuotientHilbertSamuel (PowerSeries K) (Ideal.span {PowerSeries.X ^ k}) n =
      (min (n + 1) k : ℕ) :=
  localQuotientHilbertSamuel_span_X_pow (σ := Unit) k n

end CountingFormula

section Stabilization

private noncomputable def diagramCount {σ : Type*} (D : Set (σ →₀ ℕ)) (n : ℕ) : ℕ :=
  {α : σ →₀ ℕ | α.degree ≤ n ∧ α ∉ D}.ncard

/-- By Dickson's lemma and iterative pigeonhole refinement on finite degree balls, the set of
complement-counting functions `n ↦ {α | α.degree ≤ n ∧ α ∉ D}.ncard` of upper sets
`D : Set (σ →₀ ℕ)` in finitely many variables `σ` has no infinite strictly descending sequence in
`Lex (ℕ → ℕ)`. -/
private theorem isWF_toLex_diagramCount {σ : Type*} [Finite σ] :
    (toLex '' {f : ℕ → ℕ | ∃ D : Set (σ →₀ ℕ), IsUpperSet D ∧ f = diagramCount D}).IsWF := by
  classical
  rw [Set.IsWF, Set.wellFoundedOn_iff_no_descending_seq]
  intro g hg_mem
  have hex : ∀ j, ∃ D : Set (σ →₀ ℕ), IsUpperSet D ∧ ofLex (g j) = diagramCount D := by
    intro j
    obtain ⟨f, ⟨D, hD, rfl⟩, hfg⟩ := hg_mem j
    exact ⟨D, hD, congrArg ofLex hfg.symm⟩
  choose D hD hg_eq using hex
  let B (ℓ : ℕ) : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le ℓ).toFinset
  have hpigeon (ℓ : ℕ) (T : Set ℕ) (hT : T.Infinite) :
      ∃ T' : Set ℕ, T'.Infinite ∧ T' ⊆ T ∧
        ∀ m ∈ T', ∀ n ∈ T', ∀ α : σ →₀ ℕ, α.degree ≤ ℓ → (α ∈ D m ↔ α ∈ D n) := by
    have : Infinite T := hT.to_subtype
    let φ : T → (B ℓ → Bool) := fun j α ↦ decide (α.1 ∈ D j.1)
    obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber φ
    have hy_inf : (φ ⁻¹' {y}).Infinite := Set.infinite_coe_iff.mp hy
    refine ⟨Subtype.val '' (φ ⁻¹' {y}), hy_inf.image Subtype.val_injective.injOn, ?_, ?_⟩
    · rintro _ ⟨j, _, rfl⟩
      exact j.2
    · rintro _ ⟨j₁, hj₁, rfl⟩ _ ⟨j₂, hj₂, rfl⟩ α hα
      have hαB : α ∈ B ℓ := (Finsupp.finite_of_degree_le ℓ).mem_toFinset.mpr hα
      have h₁ : decide (α ∈ D j₁.1) = y ⟨α, hαB⟩ := congrFun (Set.mem_preimage.mp hj₁) ⟨α, hαB⟩
      have h₂ : decide (α ∈ D j₂.1) = y ⟨α, hαB⟩ := congrFun (Set.mem_preimage.mp hj₂) ⟨α, hαB⟩
      exact decide_eq_decide.mp (h₁.trans h₂.symm)
  let State (ℓ : ℕ) :=
    {T : Set ℕ // T.Infinite ∧
      ∀ m ∈ T, ∀ n ∈ T, ∀ α : σ →₀ ℕ, α.degree ≤ ℓ → (α ∈ D m ↔ α ∈ D n)}
  let step (ℓ : ℕ) (s : State ℓ) : State (ℓ + 1) := by
    let k₀ : ℕ := Classical.choose s.2.1.nonempty
    have hT₁ : (s.1 \ Set.Iic k₀).Infinite := s.2.1.sdiff (Set.finite_Iic k₀)
    let hex' := hpigeon (ℓ + 1) (s.1 \ Set.Iic k₀) hT₁
    exact ⟨Classical.choose hex', (Classical.choose_spec hex').1, (Classical.choose_spec hex').2.2⟩
  let s₀ : State 0 := by
    let hex₀ := hpigeon 0 Set.univ Set.infinite_univ
    exact ⟨Classical.choose hex₀, (Classical.choose_spec hex₀).1, (Classical.choose_spec hex₀).2.2⟩
  let seq : (ℓ : ℕ) → State ℓ := fun ℓ ↦ Nat.rec s₀ step ℓ
  let k (ℓ : ℕ) : ℕ := Classical.choose (seq ℓ).2.1.nonempty
  have hk_mem (ℓ : ℕ) : k ℓ ∈ (seq ℓ).1 := Classical.choose_spec (seq ℓ).2.1.nonempty
  have hseq_succ (ℓ : ℕ) : (seq (ℓ + 1)).1 ⊆ (seq ℓ).1 \ Set.Iic (k ℓ) :=
    (Classical.choose_spec (hpigeon (ℓ + 1) ((seq ℓ).1 \ Set.Iic (k ℓ))
      ((seq ℓ).2.1.sdiff (Set.finite_Iic (k ℓ))))).2.1
  have hseq_sub {ℓ m : ℕ} (h : ℓ ≤ m) : (seq m).1 ⊆ (seq ℓ).1 := by
    induction h with
    | refl => exact Set.Subset.rfl
    | @step r _ ih => exact fun x hx ↦ ih ((hseq_succ r hx).1)
  have hk_strictMono : StrictMono k :=
    strictMono_nat_of_lt_succ fun ℓ ↦ not_le.mp (hseq_succ ℓ (hk_mem (ℓ + 1))).2
  have hk_mem_of_le {ℓ m : ℕ} (h : ℓ ≤ m) : k m ∈ (seq ℓ).1 := hseq_sub h (hk_mem m)
  let D_inf : Set (σ →₀ ℕ) := {α | α ∈ D (k α.degree)}
  have hagree (ℓ : ℕ) {n : ℕ} (hn : n ∈ (seq ℓ).1) {α : σ →₀ ℕ} (hα : α.degree ≤ ℓ) :
      α ∈ D n ↔ α ∈ D_inf := by
    have h₁ : α ∈ D n ↔ α ∈ D (k ℓ) := (seq ℓ).2.2 n hn (k ℓ) (hk_mem ℓ) α hα
    have h₂ : α ∈ D (k ℓ) ↔ α ∈ D (k α.degree) :=
      (seq α.degree).2.2 (k ℓ) (hk_mem_of_le hα) (k α.degree) (hk_mem α.degree) α le_rfl
    exact h₁.trans h₂
  let V : Set (σ →₀ ℕ) := {α | Minimal (· ∈ D_inf) α}
  have hV : V.Finite := WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  let L : ℕ := hV.toFinset.sup Finsupp.degree
  have hsub_D_inf {n : ℕ} (hn : n ∈ (seq L).1) : D_inf ⊆ D n := by
    intro γ hγ
    obtain ⟨v, hvγ, hvmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D_inf) γ hγ
    have hvL : v.degree ≤ L := Finset.le_sup (f := Finsupp.degree) (hV.mem_toFinset.mpr hvmin)
    exact hD n hvγ ((hagree L hn hvL).mpr hvmin.prop)
  have hex_ne : ∃ m, L ≤ m ∧ D (k m) ≠ D_inf := by
    by_contra! hall
    have hL : D (k L) = D_inf := hall L le_rfl
    have hL1 : D (k (L + 1)) = D_inf := hall (L + 1) (Nat.le_succ L)
    have heq : g (k (L + 1)) = g (k L) := by
      apply ofLex.injective
      rw [hg_eq, hg_eq, hL, hL1]
    exact (g.map_rel_iff.mpr (hk_strictMono (Nat.lt_succ_self L))).ne heq
  obtain ⟨m, hLm, hm_ne⟩ := hex_ne
  have hnot_sub : ¬ D (k m) ⊆ D_inf :=
    fun hsub ↦ hm_ne (Set.Subset.antisymm hsub (hsub_D_inf (hk_mem_of_le hLm)))
  obtain ⟨β, hβm, hβnot⟩ := Set.not_subset.mp hnot_sub
  let r : ℕ := max m β.degree + 1
  have hmr : m < r := Nat.lt_succ_of_le (le_max_left m β.degree)
  have hβr : β.degree ≤ r := (le_max_right m β.degree).trans (Nat.le_succ _)
  have hg_lt : g (k r) < g (k m) := g.map_rel_iff.mpr (hk_strictMono hmr)
  have hcount_le {j : ℕ} (hj : j ≤ β.degree) :
      diagramCount (D (k m)) j ≤ diagramCount (D (k r)) j := by
    refine Set.ncard_le_ncard (fun α hα ↦ ⟨hα.1, fun hαr ↦ hα.2 ?_⟩)
      ((Finsupp.finite_of_degree_le j).subset fun _ h ↦ h.1)
    exact hsub_D_inf (hk_mem_of_le hLm)
      ((hagree r (hk_mem r) (hα.1.trans (hj.trans hβr))).mp hαr)
  have hcount_lt_β : diagramCount (D (k m)) β.degree < diagramCount (D (k r)) β.degree := by
    refine Set.ncard_lt_ncard ⟨fun α hα ↦ ⟨hα.1, fun hαr ↦ hα.2 ?_⟩, ?_⟩
      ((Finsupp.finite_of_degree_le β.degree).subset fun _ h ↦ h.1)
    · exact hsub_D_inf (hk_mem_of_le hLm)
        ((hagree r (hk_mem r) (hα.1.trans hβr)).mp hαr)
    · intro hsub
      have hβ_in_r : β ∈ {α : σ →₀ ℕ | α.degree ≤ β.degree ∧ α ∉ D (k r)} :=
        ⟨le_rfl, fun hβ_in ↦ hβnot ((hagree r (hk_mem r) hβr).mp hβ_in)⟩
      exact (hsub hβ_in_r).2 hβm
  have hex_j : ∃ j, j ≤ β.degree ∧ diagramCount (D (k m)) j < diagramCount (D (k r)) j :=
    ⟨β.degree, le_rfl, hcount_lt_β⟩
  let j₀ : ℕ := Nat.find hex_j
  have hj₀_spec := Nat.find_spec hex_j
  have hg_gt : g (k m) < g (k r) := by
    refine ⟨j₀, fun j hj ↦ ?_, ?_⟩
    · change ofLex (g (k m)) j = ofLex (g (k r)) j
      rw [hg_eq, hg_eq]
      exact le_antisymm (hcount_le (hj.le.trans hj₀_spec.1))
        (not_lt.mp fun hlt ↦ Nat.find_min hex_j hj ⟨hj.le.trans hj₀_spec.1, hlt⟩)
    · change ofLex (g (k m)) j₀ < ofLex (g (k r)) j₀
      rw [hg_eq, hg_eq]
      exact hj₀_spec.2
  exact lt_asymm hg_lt hg_gt

/-- **Well-foundedness of realized Hilbert–Samuel functions** (Bierstone–Milman, *Uniformization of
analytic spaces*, Theorem 5.2.1): in a fixed finite-variable formal power series ring
`MvPowerSeries σ K` over any field `K`, the set of Hilbert–Samuel functions realized by ideals of
`MvPowerSeries σ K` is well-founded under the lexicographic order on `Lex (ℕ → ℕ∞)`. -/
theorem isWF_toLex_range_localQuotientHilbertSamuel_mvPowerSeries (σ K : Type*) [Finite σ]
    [Field K] :
    (toLex '' Set.range (localQuotientHilbertSamuel (MvPowerSeries σ K))).IsWF := by
  obtain ⟨d, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let φ := (MvPowerSeries.renameEquiv (R := K) e).toRingEquiv
  rw [Set.IsWF, Set.wellFoundedOn_iff_no_descending_seq]
  intro g hg_mem
  have hex : ∀ j, ∃ D : Set (Fin d →₀ ℕ), IsUpperSet D ∧
      ∀ n, ofLex (g j) n = (diagramCount D n : ℕ∞) := by
    intro j
    obtain ⟨_, ⟨I, rfl⟩, hgj⟩ := hg_mem j
    refine ⟨degLex.initialDiagram (I.map (φ : MvPowerSeries σ K →+* MvPowerSeries (Fin d) K)),
      degLex.isUpperSet_initialDiagram _, fun n ↦ ?_⟩
    have hgj' : ofLex (g j) = localQuotientHilbertSamuel (MvPowerSeries σ K) I :=
      congrArg ofLex hgj.symm
    rw [hgj', ← φ.localQuotientHilbertSamuel_map I,
      localQuotientHilbertSamuel_mvPowerSeries_eq_ncard]
    rfl
  choose D hD hg_eq using hex
  let g' : ℕ → Lex (ℕ → ℕ) := fun j ↦ toLex (diagramCount (D j))
  have hg'_step : ∀ j, g' (j + 1) < g' j := by
    intro j
    obtain ⟨n₀, hn₀_eq, hn₀_lt⟩ := g.map_rel_iff.mpr (Nat.lt_succ_self j)
    refine ⟨n₀, fun m hm ↦ ?_, ?_⟩
    · have hm_eq : ofLex (g (j + 1)) m = ofLex (g j) m := hn₀_eq m hm
      rw [hg_eq, hg_eq] at hm_eq
      exact Nat.cast_injective hm_eq
    · have hn₀_lt' : ofLex (g (j + 1)) n₀ < ofLex (g j) n₀ := hn₀_lt
      rw [hg_eq, hg_eq] at hn₀_lt'
      exact Nat.cast_lt.mp hn₀_lt'
  exact Set.wellFoundedOn_iff_no_descending_seq.mp (isWF_toLex_diagramCount (σ := Fin d))
    (RelEmbedding.natGT g' hg'_step) fun j ↦ ⟨diagramCount (D j), ⟨D j, hD j, rfl⟩, rfl⟩

/-- **Lexicographic Hilbert–Samuel stabilization**: in `MvPowerSeries σ K` over any field `K` in
finitely many variables `σ`, every lexicographically nonincreasing sequence of Hilbert–Samuel
functions of ideals `I j` is eventually constant. -/
theorem exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_lex {σ K : Type*} [Finite σ]
    [Field K] (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  let F : ℕ → Lex (ℕ → ℕ∞) := fun j ↦ toLex (localQuotientHilbertSamuel _ (I j))
  have hstep (j : ℕ) : F (j + 1) = F j ∨ F (j + 1) < F j :=
    (h j).imp (congrArg toLex) id
  have hle {i m : ℕ} (him : i ≤ m) : F m = F i ∨ F m < F i := by
    induction him with
    | refl => exact Or.inl rfl
    | @step r _ ih =>
      rcases hstep r with heq | hlt
      · rwa [heq]
      · exact Or.inr (ih.elim (fun heq' ↦ heq' ▸ hlt) (hlt.trans ·))
  by_contra! H
  choose next hnext_ge hnext_ne using H
  let k : ℕ → ℕ := fun m ↦ Nat.rec 0 (fun _ r ↦ next r) m
  have hk_step (m : ℕ) : F (k (m + 1)) < F (k m) :=
    (hle (hnext_ge (k m))).resolve_left fun heq ↦ hnext_ne (k m) (ofLex.injective heq)
  exact Set.wellFoundedOn_iff_no_descending_seq.mp
    (isWF_toLex_range_localQuotientHilbertSamuel_mvPowerSeries σ K)
    (RelEmbedding.natGT (fun m ↦ F (k m)) hk_step) fun m ↦ ⟨_, ⟨I (k m), rfl⟩, rfl⟩

/-- **Lexicographic Hilbert–Samuel stabilization** in `MvPowerSeries (Fin n) K` over an arbitrary
field `K` (Bierstone–Milman, *Uniformization of analytic spaces*, Theorem 5.2.1;
Bierstone–Milman–Temkin 2011, §6.1). -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) :=
  exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_lex I h

/-- **Pointwise Hilbert–Samuel stabilization**: in `MvPowerSeries σ K` over any field `K` in
finitely many variables `σ`, every pointwise nonincreasing sequence of Hilbert–Samuel functions of
ideals `I j` is eventually constant. -/
theorem exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone {σ K : Type*}
    [Finite σ] [Field K] (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : Antitone fun j ↦ localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  refine exists_forall_localQuotientHilbertSamuel_mvPowerSeries_eq_of_lex I fun j ↦ ?_
  have hle : toLex (localQuotientHilbertSamuel _ (I (j + 1))) ≤
      toLex (localQuotientHilbertSamuel _ (I j)) :=
    Pi.toLex_monotone (h (Nat.le_succ j))
  exact (le_iff_eq_or_lt.mp hle).imp (congrArg ofLex) id

/-- Realizability by formal ideals in fixed embedding dimension is essential in
`TauCeti.hsLexStabilization`: the indicator functions `ℓ ↦ if ℓ < j then 0 else 1` form an infinite
strictly decreasing sequence in `Lex (ℕ → ℕ∞)`. -/
theorem strictAnti_toLex_ite_lt :
    StrictAnti (fun j : ℕ ↦ toLex (fun ℓ : ℕ ↦ if ℓ < j then (0 : ℕ∞) else 1)) := by
  refine strictAnti_nat_of_succ_lt fun j ↦ ⟨j, fun ℓ hℓ ↦ ?_, ?_⟩
  · simp [hℓ, hℓ.le]
  · simp

end Stabilization

end TauCeti
