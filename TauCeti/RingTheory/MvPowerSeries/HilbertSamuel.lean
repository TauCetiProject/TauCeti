/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Set.Card
import Mathlib.Order.OrderIsoNat
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order
import Mathlib.Topology.Sequences

/-!
# Hilbert–Samuel functions of multivariate power series ideals and lexicographic stabilization

For an ideal `I` of `MvPowerSeries σ K` over a field `K` in finitely many variables `σ`, Hironaka's
formal division theorem identifies the local quotient `MvPowerSeries σ K ⧸ (I ⊔ 𝔪 ^ (ℓ + 1))` with
the `K`-vector space of power series supported on the finite set of exponents `α ∉ D(I)` of total
degree at most `ℓ`, where `D(I) = degLex.initialDiagram I` is the graded-lexicographic diagram of
initial exponents. Because the residue field of `MvPowerSeries σ K` is isomorphic to `K`, the local
module length `TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ` equals the combinatorial
complement count `TauCeti.diagramHilbertSamuel (degLex.initialDiagram I) ℓ`
(`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_diagramHilbertSamuel`).

This identification yields Bierstone and Milman's lexicographic stabilization theorem
(`TauCeti.hsLexStabilization`) and well-orderedness of realized Hilbert–Samuel functions in
`Lex (ℕ → ℕ∞)` (`TauCeti.wellFoundedLT_range_toLex_localQuotientHilbertSamuel_mvPowerSeries`): any
sequence of ideals `I : ℕ → Ideal (MvPowerSeries (Fin n) K)` whose Hilbert–Samuel functions are
nonincreasing in the total lexicographic order `Pi.Lex` is eventually constant in Hilbert–Samuel
function (and likewise over any finite variable type `σ`, as well as for pointwise nonincreasing
sequences).

## Main definitions

* `MonomialOrder.complementSubmoduleEquivPi`: the `R`-linear equivalence between
  `ord.complementSubmodule I` and `{α : σ →₀ ℕ // α ∉ ord.initialDiagram I} → R`.
* `TauCeti.diagramHilbertSamuel`: the count `{α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D}.ncard` of
  exponents outside `D` of total degree at most `ℓ`.

## Main results

* `MvPowerSeries.length_eq_length_field`: over a field `K`, `Module.length (MvPowerSeries σ K) M`
  coincides with `Module.length K M`.
* `MonomialOrder.initialDiagram_degLex_maximalIdeal_pow`,
  `MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow`: the `degLex`-initial diagram of
  `I ⊔ 𝔪 ^ n` is `degLex.initialDiagram I ∪ {α | n ≤ α.degree}`.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_eq_diagramHilbertSamuel`:
  `localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ` equals
  `diagramHilbertSamuel (degLex.initialDiagram I) ℓ`.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`,
  `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X_pow`: explicit formulas for the ambient
  power-series ring (`(ℓ + Nat.card σ).choose (Nat.card σ)`) and univariate monomial powers
  (`min (ℓ + 1) d`).
* `TauCeti.strictAnti_toLex_diagramHilbertSamuel`: `D ↦ toLex (diagramHilbertSamuel D)` is strictly
  antitone under set inclusion.
* `TauCeti.wellFoundedLT_range_toLex_localQuotientHilbertSamuel_mvPowerSeries`,
  `TauCeti.exists_diagramHilbertSamuel_eq_of_antitone_toLex`,
  `TauCeti.exists_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex`,
  `TauCeti.hsLexStabilization`,
  `TauCeti.exists_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone`: well-orderedness in
  `Pi.Lex` and lexicographic and pointwise stabilization of Hilbert–Samuel functions.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239; Theorem 9.2 and Lemma 9.3, p. 276.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*, Asian J.
  Math. 15 (2011), 229–250, §6.1, property (4).
-/

public section

open scoped MonomialOrder PowerSeries

namespace MvPowerSeries

/-- Over a field `K`, the `MvPowerSeries σ K`-length of any `MvPowerSeries σ K`-module `M` equals
its `K`-length. -/
theorem length_eq_length_field {σ K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    [Module (MvPowerSeries σ K) M] [IsScalarTower K (MvPowerSeries σ K) M] :
    Module.length (MvPowerSeries σ K) M = Module.length K M := by
  let R := MvPowerSeries σ K
  have hsurj : Function.Surjective (algebraMap K (IsLocalRing.ResidueField R)) := by
    intro x
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective x
    refine ⟨constantCoeff f, ?_⟩
    rw [IsScalarTower.algebraMap_eq K R (IsLocalRing.ResidueField R), RingHom.comp_apply,
      IsLocalRing.ResidueField.algebraMap_eq, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker,
      map_sub, algebraMap_apply, constantCoeff_C, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField R) = 1 := by
    rw [← Module.length_eq_of_surjective (M := IsLocalRing.ResidueField R)
        (IsLocalRing.residue_surjective (R := K)),
      Module.length_eq_of_surjective (M := IsLocalRing.ResidueField R) hsurj]
    exact Module.length_eq_one_iff.mpr inferInstance
  rw [IsLocalRing.length_restrictScalars K R M, hres, mul_one]

end MvPowerSeries

namespace MonomialOrder

open scoped Classical in
/-- The `R`-linear equivalence identifying `ord.complementSubmodule I` with the product of
coefficient copies of `R` indexed by exponents outside `ord.initialDiagram I`. -/
noncomputable def complementSubmoduleEquivPi {σ R : Type*} [Semiring R] (ord : MonomialOrder σ)
    (I : Ideal (MvPowerSeries σ R)) :
    ord.complementSubmodule I ≃ₗ[R] ({α : σ →₀ ℕ // α ∉ ord.initialDiagram I} → R) where
  toFun f α := MvPowerSeries.coeff α.1 f.1
  invFun c := ⟨(fun α ↦ if h : α ∉ ord.initialDiagram I then c ⟨α, h⟩ else 0 : MvPowerSeries σ R),
    ord.mem_complementSubmodule_iff.mpr fun β hβ ↦ by
      rw [Function.mem_support] at hβ
      exact by_contra fun h ↦ hβ (dite_eq_right h)⟩
  left_inv f := Subtype.ext <| funext fun α ↦ by
    dsimp only
    rw [← MvPowerSeries.coeff_apply f.1 α]
    by_cases h : α ∉ ord.initialDiagram I
    · exact dite_eq_left h
    · rw [dite_eq_right h]
      exact (by_contra fun hne ↦
        h (ord.mem_complementSubmodule_iff.mp f.2 α (MvPowerSeries.mem_support.mpr hne))).symm
  right_inv c := funext fun α ↦ dite_eq_left α.2
  map_add' f g := funext fun α ↦ map_add (MvPowerSeries.coeff α.1) f.1 g.1
  map_smul' r f := funext fun α ↦ map_smul (MvPowerSeries.coeff α.1) r f.1

@[simp]
theorem complementSubmoduleEquivPi_apply {σ R : Type*} [Semiring R] (ord : MonomialOrder σ)
    (I : Ideal (MvPowerSeries σ R)) (f : ord.complementSubmodule I)
    (α : {α : σ →₀ ℕ // α ∉ ord.initialDiagram I}) :
    ord.complementSubmoduleEquivPi I f α = MvPowerSeries.coeff α.1 f.1 := (rfl)

@[simp]
theorem complementSubmoduleEquivPi_symm_coeff {σ R : Type*} [Semiring R] (ord : MonomialOrder σ)
    (I : Ideal (MvPowerSeries σ R)) (c : {α : σ →₀ ℕ // α ∉ ord.initialDiagram I} → R)
    (α : σ →₀ ℕ) [Decidable (α ∉ ord.initialDiagram I)] :
    MvPowerSeries.coeff α ((ord.complementSubmoduleEquivPi I).symm c).1 =
      if h : α ∉ ord.initialDiagram I then c ⟨α, h⟩ else 0 := by
  rw [MvPowerSeries.coeff_apply]
  dsimp [complementSubmoduleEquivPi]
  split_ifs <;> rfl

section DegLexMaximalIdeal

variable {σ K : Type*} [Field K] [Finite σ] [LinearOrder σ]

/-- Over a field in finitely many variables, the `degLex`-initial diagram of `𝔪 ^ n` consists of all
exponents of total degree at least `n`. -/
@[simp]
theorem initialDiagram_degLex_maximalIdeal_pow (n : ℕ) :
    degLex.initialDiagram (IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n) =
      {α : σ →₀ ℕ | n ≤ α.degree} := by
  ext α
  simp only [mem_initialDiagram_iff, Set.mem_ofPred_eq]
  refine ⟨?_, fun hdeg ↦ ?_⟩
  · rintro ⟨f, hf, hf0, rfl⟩
    rw [MvPowerSeries.mem_maximalIdeal_pow_iff_le_order,
      ← degree_initialExp_degLex_eq_order hf0, Nat.cast_le] at hf
    exact hf
  · refine ⟨MvPowerSeries.monomial α 1, ?_, ?_,
      degLex.initialExp_monomial_of_ne_zero α one_ne_zero⟩
    · rw [MvPowerSeries.mem_maximalIdeal_pow_iff_le_order,
        MvPowerSeries.order_monomial_of_ne_zero one_ne_zero, Nat.cast_le]
      exact hdeg
    · intro h0
      simpa using congrArg (MvPowerSeries.coeff α) h0

/-- Over a field in finitely many variables, taking the supremum of an ideal `I` with `𝔪 ^ n`
adjoins to `degLex.initialDiagram I` all exponents of total degree at least `n`. -/
@[simp]
theorem initialDiagram_degLex_sup_maximalIdeal_pow (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    degLex.initialDiagram (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n) =
      degLex.initialDiagram I ∪ {α : σ →₀ ℕ | n ≤ α.degree} := by
  refine Set.Subset.antisymm ?_ (Set.union_subset (degLex.initialDiagram_mono le_sup_left)
    ((initialDiagram_degLex_maximalIdeal_pow n).symm.trans_subset
      (degLex.initialDiagram_mono le_sup_right)))
  intro α hα
  by_cases hdeg : n ≤ α.degree
  · exact Or.inr hdeg
  rw [not_le] at hdeg
  obtain ⟨h, hh, hh0, hexp⟩ := degLex.mem_initialDiagram_iff.mp hα
  obtain ⟨f, hfI, g, hgM, rfl⟩ := Submodule.mem_sup.mp hh
  subst hexp
  set α := degLex.initialExp (f + g)
  have hgord : (n : ℕ∞) ≤ g.order := MvPowerSeries.mem_maximalIdeal_pow_iff_le_order.mp hgM
  have hg0 : ∀ β, β ≼[degLex] α → MvPowerSeries.coeff β g = 0 := by
    intro β hβ
    have hβdeg : β.degree ≤ α.degree := by
      rw [degLex_le_iff, Finsupp.DegLex.le_iff] at hβ
      rcases hβ with hlt | ⟨heq, _⟩
      · exact hlt.le
      · exact heq.le
    exact MvPowerSeries.coeff_of_lt_order
      ((Nat.cast_lt.mpr (hβdeg.trans_lt hdeg)).trans_le hgord)
  have hfα : MvPowerSeries.coeff α f ≠ 0 := by
    have hfg := degLex.coeff_initialExp_ne_zero hh0
    rwa [map_add, hg0 α le_rfl, add_zero] at hfg
  have hf_ne : f ≠ 0 := fun h0 ↦ hfα (by simp [h0])
  refine Or.inl (degLex.mem_initialDiagram_iff.mpr
    ⟨f, hfI, hf_ne, degLex.initialExp_eq_of_coeff_ne_zero_of_forall_lt hfα ?_⟩)
  intro β hβ
  have hfg := degLex.coeff_eq_zero_of_lt_initialExp hβ
  rwa [map_add, hg0 β hβ.le, add_zero] at hfg

end DegLexMaximalIdeal

end MonomialOrder

namespace TauCeti

section DiagramHilbertSamuel

/-- The combinatorial Hilbert–Samuel function of an exponent subset `D : Set (σ →₀ ℕ)`:
`diagramHilbertSamuel D ℓ` counts the exponents `α ∉ D` of total degree at most `ℓ`
(Bierstone–Milman 1997, Corollary 3.20). -/
noncomputable def diagramHilbertSamuel {σ : Type*} (D : Set (σ →₀ ℕ)) (ℓ : ℕ) : ℕ :=
  {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D}.ncard

/-- Defining formula for `TauCeti.diagramHilbertSamuel`. -/
theorem diagramHilbertSamuel_def {σ : Type*} (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    diagramHilbertSamuel D ℓ = {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D}.ncard := (rfl)

/-- The set of exponents outside `D` of total degree at most `ℓ` is finite. -/
theorem finite_degree_le_and_notMem {σ : Type*} [Finite σ] (D : Set (σ →₀ ℕ)) (ℓ : ℕ) :
    {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ D}.Finite :=
  (Finsupp.finite_of_degree_le ℓ).subset fun _ h ↦ h.1

@[simp]
theorem diagramHilbertSamuel_univ {σ : Type*} (ℓ : ℕ) :
    diagramHilbertSamuel (Set.univ : Set (σ →₀ ℕ)) ℓ = 0 := by
  simp [diagramHilbertSamuel]

/-- If `0 ∈ D`, the degree-`0` complement count vanishes. -/
theorem diagramHilbertSamuel_zero_eq_zero_of_zero_mem {σ : Type*} {D : Set (σ →₀ ℕ)}
    (h : (0 : σ →₀ ℕ) ∈ D) : diagramHilbertSamuel D 0 = 0 := by
  have hset : {α : σ →₀ ℕ | α.degree ≤ 0 ∧ α ∉ D} = ∅ := by
    ext α
    simp only [Set.mem_ofPred_eq, Nat.le_zero, Finsupp.degree_eq_zero_iff, Set.mem_empty_iff_false,
      iff_false, not_and]
    rintro rfl
    exact not_not.mpr h
  rw [diagramHilbertSamuel_def, hset]
  exact Set.ncard_empty _

/-- If `0 ∉ D`, the degree-`0` complement count is `1`. -/
theorem diagramHilbertSamuel_zero_eq_one_of_zero_notMem {σ : Type*} {D : Set (σ →₀ ℕ)}
    (h : (0 : σ →₀ ℕ) ∉ D) : diagramHilbertSamuel D 0 = 1 := by
  have hset : {α : σ →₀ ℕ | α.degree ≤ 0 ∧ α ∉ D} = {0} := by
    ext α
    simp only [Set.mem_ofPred_eq, Nat.le_zero, Finsupp.degree_eq_zero_iff, Set.mem_singleton_iff,
      and_iff_left_iff_imp]
    rintro rfl
    exact h
  rw [diagramHilbertSamuel_def, hset]
  exact Set.ncard_singleton _

/-- Enlarging the diagram `D` decreases `diagramHilbertSamuel` pointwise. -/
theorem diagramHilbertSamuel_anti {σ : Type*} [Finite σ] {D₁ D₂ : Set (σ →₀ ℕ)} (h : D₁ ⊆ D₂)
    (ℓ : ℕ) : diagramHilbertSamuel D₂ ℓ ≤ diagramHilbertSamuel D₁ ℓ :=
  Set.ncard_le_ncard (fun _ hα ↦ ⟨hα.1, fun h₂ ↦ hα.2 (h h₂)⟩) (finite_degree_le_and_notMem D₁ ℓ)

/-- For any fixed exponent set `D`, `diagramHilbertSamuel D` is monotone in the degree bound `ℓ`. -/
theorem diagramHilbertSamuel_mono {σ : Type*} [Finite σ] (D : Set (σ →₀ ℕ)) :
    Monotone (diagramHilbertSamuel D) :=
  fun _ ℓ₂ hℓ ↦ Set.ncard_le_ncard (fun _ hα ↦ ⟨hα.1.trans hℓ, hα.2⟩)
    (finite_degree_le_and_notMem D ℓ₂)

/-- The combinatorial Hilbert–Samuel function of the empty diagram counts all exponents of total
degree at most `ℓ`, giving `choose (ℓ + card σ) (card σ)`. -/
@[simp]
theorem diagramHilbertSamuel_empty (σ : Type*) [Finite σ] (ℓ : ℕ) :
    diagramHilbertSamuel (∅ : Set (σ →₀ ℕ)) ℓ = (ℓ + Nat.card σ).choose (Nat.card σ) := by
  classical
  cases nonempty_fintype σ
  have hset : {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ (∅ : Set (σ →₀ ℕ))} =
      ↑((Finset.range (ℓ + 1)).biUnion ((Finset.univ : Finset σ).finsuppAntidiag ·)) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [diagramHilbertSamuel, hset, Set.ncard_coe_finset, Finset.card_biUnion,
    Nat.card_eq_fintype_card]
  · simp [Finset.card_finsuppAntidiag_nat_eq_multichoose, Nat.sum_range_multichoose]
  · intro k _ l _ hkl
    refine Finset.disjoint_left.2 fun s hk hl ↦ hkl ?_
    rw [Finset.mem_finsuppAntidiag] at hk hl
    exact hk.1.symm.trans hl.1

/-- `D ↦ toLex (diagramHilbertSamuel D)` is strictly antitone under set inclusion on
`Set (σ →₀ ℕ)`. -/
theorem strictAnti_toLex_diagramHilbertSamuel {σ : Type*} [Finite σ] :
    StrictAnti (fun D : Set (σ →₀ ℕ) ↦ toLex (diagramHilbertSamuel D)) := by
  intro D₁ D₂ hssub
  classical
  obtain ⟨hsub, hnot⟩ := hssub
  obtain ⟨α₁, hα₁D₂, hα₁D₁⟩ := Set.not_subset.mp hnot
  have hex : ∃ m, ∃ α, (α ∈ D₂ ∧ α ∉ D₁) ∧ α.degree = m :=
    ⟨α₁.degree, α₁, ⟨hα₁D₂, hα₁D₁⟩, rfl⟩
  set m := Nat.find hex
  obtain ⟨α₀, ⟨hα₀D₂, hα₀D₁⟩, hα₀deg⟩ := Nat.find_spec hex
  -- `LT (Lex (ℕ → ℕ))` in `Mathlib.Order.PiLex` is `id`-wrapped `Pi.Lex (· < ·) (· < ·)`.
  refine ⟨m, fun ℓ hℓ ↦ ?_, ?_⟩
  · simp only [Pi.toLex_apply, diagramHilbertSamuel_def]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq]
    refine and_congr_right fun hdeg ↦ ⟨fun hnot₂ h₁ ↦ hnot₂ (hsub h₁), fun hnot₁ h₂ ↦ ?_⟩
    exact (hdeg.trans_lt hℓ).not_ge (Nat.find_min' hex ⟨α, ⟨h₂, hnot₁⟩, rfl⟩)
  · simp only [Pi.toLex_apply]
    refine Set.ncard_lt_ncard ⟨fun _ h ↦ ⟨h.1, fun h₁ ↦ h.2 (hsub h₁)⟩, fun hle ↦ ?_⟩
      (finite_degree_le_and_notMem D₁ m)
    exact (hle ⟨hα₀deg.le, hα₀D₁⟩).2 hα₀D₂

end DiagramHilbertSamuel

section MvPowerSeriesFormula

/-- **Bierstone–Milman Corollary 3.20**: for an ideal `I` of `MvPowerSeries σ K` over a field `K`
in finitely many linearly ordered variables `σ`, the local Hilbert–Samuel value at `ℓ` counts the
exponents `α ∉ degLex.initialDiagram I` of total degree at most `ℓ`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_eq_diagramHilbertSamuel {σ K : Type*} [Field K]
    [Finite σ] [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ =
      (diagramHilbertSamuel (MonomialOrder.degLex.initialDiagram I) ℓ : ℕ∞) := by
  let J : Ideal (MvPowerSeries σ K) := I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ (ℓ + 1)
  let S : Set (σ →₀ ℕ) := {α : σ →₀ ℕ | α.degree ≤ ℓ ∧ α ∉ MonomialOrder.degLex.initialDiagram I}
  have hmem (α : σ →₀ ℕ) : α ∉ MonomialOrder.degLex.initialDiagram J ↔ α ∈ S := by
    rw [MonomialOrder.initialDiagram_degLex_sup_maximalIdeal_pow]
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Nat.lt_succ_iff, S]
    exact and_comm
  let e : {α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J} ≃ S :=
    Equiv.subtypeEquivRight hmem
  have : Finite S := finite_degree_le_and_notMem _ ℓ
  let : Fintype S := Fintype.ofFinite S
  have hK : Module.length K K = 1 := Module.length_eq_one_iff.mpr inferInstance
  calc
    localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ
        = Module.length K (MvPowerSeries σ K ⧸ J) := by
          rw [localQuotientHilbertSamuel_def, MvPowerSeries.length_eq_length_field]
    _ = Module.length K (MonomialOrder.degLex.complementSubmodule J) :=
          (MonomialOrder.degLex.quotientEquivComplementSubmodule J).length_eq
    _ = Module.length K ({α : σ →₀ ℕ // α ∉ MonomialOrder.degLex.initialDiagram J} → K) :=
          (MonomialOrder.degLex.complementSubmoduleEquivPi J).length_eq
    _ = Module.length K (S → K) :=
          (LinearEquiv.piCongrLeft K (fun _ ↦ K) e).length_eq
    _ = (diagramHilbertSamuel (MonomialOrder.degLex.initialDiagram I) ℓ : ℕ∞) := by
          rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, hK, nsmul_one]
          congr 1
          rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
          rfl

@[simp]
theorem toNat_localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [Field K] [Finite σ]
    [LinearOrder σ] (I : Ideal (MvPowerSeries σ K)) (ℓ : ℕ) :
    (localQuotientHilbertSamuel (MvPowerSeries σ K) I ℓ).toNat =
      diagramHilbertSamuel (MonomialOrder.degLex.initialDiagram I) ℓ := by
  rw [localQuotientHilbertSamuel_mvPowerSeries_eq_diagramHilbertSamuel, ENat.toNat_natCast]

/-- The local Hilbert–Samuel function of `MvPowerSeries σ K` over a field `K` in finitely many
variables `σ` equals `choose (ℓ + card σ) (card σ)` at every degree `ℓ`. -/
@[simp]
theorem localQuotientHilbertSamuel_mvPowerSeries_bot (σ K : Type*) [Field K] [Finite σ] (ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) ⊥ ℓ =
      ((ℓ + Nat.card σ).choose (Nat.card σ) : ℕ∞) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let φ : MvPowerSeries σ K ≃+* MvPowerSeries (Fin n) K :=
    (MvPowerSeries.renameEquiv K e).toRingEquiv
  rw [← localQuotientHilbertSamuel_map_equiv φ ⊥ ℓ, Ideal.map_bot,
    localQuotientHilbertSamuel_mvPowerSeries_eq_diagramHilbertSamuel,
    MonomialOrder.initialDiagram_bot, diagramHilbertSamuel_empty, Nat.card_congr e, Nat.card_fin]

/-- In `MvPowerSeries (Fin n) K`, the ambient Hilbert–Samuel value at `ℓ` is `choose (n + ℓ) n`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_fin_bot (K : Type*) [Field K] (n ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries (Fin n) K) ⊥ ℓ = ((n + ℓ).choose n : ℕ∞) := by
  simp [Nat.add_comm]

/-- In a one-variable power-series ring `MvPowerSeries σ K` (`[Unique σ]`), the principal monomial
ideal `(X i ^ d)` has Hilbert–Samuel value `min (ℓ + 1) d` at `ℓ`. -/
@[simp]
theorem localQuotientHilbertSamuel_mvPowerSeries_span_X_pow {σ K : Type*} [Field K] [Unique σ]
    (i : σ) (d ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) (Ideal.span {MvPowerSeries.X i ^ d}) ℓ =
      ((min (ℓ + 1) d : ℕ) : ℕ∞) := by
  let e : σ ≃ Fin 1 := Equiv.ofUnique σ (Fin 1)
  let φ : MvPowerSeries σ K ≃+* MvPowerSeries (Fin 1) K :=
    (MvPowerSeries.renameEquiv K e).toRingEquiv
  have hmap : (Ideal.span {MvPowerSeries.X i ^ d}).map φ =
      Ideal.span ((fun α ↦ MvPowerSeries.monomial α (1 : K)) '' {Finsupp.single 0 d}) := by
    rw [Ideal.map_span, Set.image_singleton, Set.image_singleton]
    congr 2
    rw [map_pow]
    have hX : φ (MvPowerSeries.X i) = MvPowerSeries.rename e (MvPowerSeries.X i) := rfl
    rw [hX, MvPowerSeries.rename_X, Subsingleton.elim (e i) 0, MvPowerSeries.X_pow_eq]
  rw [← localQuotientHilbertSamuel_map_equiv φ _ ℓ, hmap,
    localQuotientHilbertSamuel_mvPowerSeries_eq_diagramHilbertSamuel,
    MonomialOrder.initialDiagram_span_monomial, diagramHilbertSamuel_def]
  have himg : {α : Fin 1 →₀ ℕ | α.degree ≤ ℓ ∧
      α ∉ ⋃ β ∈ ({Finsupp.single 0 d} : Set (Fin 1 →₀ ℕ)), Set.Ici β} =
      (Finsupp.single (0 : Fin 1)) '' ↑(Finset.range (min (ℓ + 1) d)) := by
    ext α
    have hα : α = Finsupp.single 0 (α 0) := Finsupp.unique_single α
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left, Set.mem_Ici,
      Finsupp.single_le_iff, Nat.not_le, Finset.coe_range, Set.mem_image, Set.mem_Iio, lt_min_iff,
      Nat.lt_succ_iff]
    refine ⟨fun ⟨hdeg, hlt⟩ ↦ ⟨α 0, ⟨?_, hlt⟩, hα.symm⟩, ?_⟩
    · rwa [hα, Finsupp.degree_single] at hdeg
    · rintro ⟨k, ⟨hkℓ, hkd⟩, rfl⟩
      simp [hkℓ, hkd]
  rw [himg, Set.ncard_image_of_injective _ (Finsupp.single_injective 0), Set.ncard_coe_finset,
    Finset.card_range]

/-- In `K⟦X⟧`, the principal ideal `(X ^ d)` has Hilbert–Samuel value `min (ℓ + 1) d` at `ℓ`. -/
@[simp]
theorem localQuotientHilbertSamuel_powerSeries_span_X_pow (K : Type*) [Field K] (d ℓ : ℕ) :
    localQuotientHilbertSamuel K⟦X⟧ (Ideal.span {PowerSeries.X ^ d}) ℓ =
      ((min (ℓ + 1) d : ℕ) : ℕ∞) :=
  localQuotientHilbertSamuel_mvPowerSeries_span_X_pow () d ℓ

end MvPowerSeriesFormula

section Stabilization

/-- Every sequence of upward-closed subsets `D : ℕ → Set (σ →₀ ℕ)` in finitely many variables `σ`
admits a subsequence `φ` and a limit upper set `D_lim` such that `D_lim ⊆ D (φ k)` eventually and
`diagramHilbertSamuel (D (φ k)) ℓ` eventually equals `diagramHilbertSamuel D_lim ℓ` in every degree
`ℓ`. -/
theorem exists_strictMono_diagramHilbertSamuel_eventually_eq {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ k, IsUpperSet (D k)) :
    ∃ (φ : ℕ → ℕ) (D_lim : Set (σ →₀ ℕ)), StrictMono φ ∧ IsUpperSet D_lim ∧
      (∀ᶠ k in Filter.atTop, D_lim ⊆ D (φ k)) ∧
      (∀ ℓ, ∀ᶠ k in Filter.atTop,
        diagramHilbertSamuel (D (φ k)) ℓ = diagramHilbertSamuel D_lim ℓ) := by
  classical
  let ind : ℕ → ((σ →₀ ℕ) → Bool) := fun k α ↦ decide (α ∈ D k)
  obtain ⟨b, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq ind
  let D_lim : Set (σ →₀ ℕ) := {α | b α = true}
  have hpt : ∀ α, ∀ᶠ k in Filter.atTop, α ∈ D (φ k) ↔ α ∈ D_lim := by
    intro α
    have hα := (tendsto_pi_nhds.mp hlim) α
    rw [nhds_discrete, Filter.tendsto_pure] at hα
    refine hα.mono fun k hk ↦ ?_
    dsimp only [ind, Function.comp_apply] at hk
    exact decide_eq_true_iff.symm.trans (hk ▸ Iff.rfl)
  have hup : IsUpperSet D_lim := by
    intro α β hle hα
    obtain ⟨k, hkα, hkβ⟩ := ((hpt α).and (hpt β)).exists
    exact hkβ.mp (hD (φ k) hle (hkα.mpr hα))
  have hV : {v : σ →₀ ℕ | Minimal (· ∈ D_lim) v}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  have hsub : ∀ᶠ k in Filter.atTop, D_lim ⊆ D (φ k) := by
    have hv := (Filter.eventually_all_finite hV).mpr fun v hv ↦
      (hpt v).mono fun k hk ↦ hk.mpr hv.prop
    refine hv.mono fun k hk γ hγ ↦ ?_
    obtain ⟨v, hle, hvmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ D_lim) γ hγ
    exact hD (φ k) hle (hk v hvmin)
  have hdeg (ℓ : ℕ) : ∀ᶠ k in Filter.atTop,
      diagramHilbertSamuel (D (φ k)) ℓ = diagramHilbertSamuel D_lim ℓ := by
    have hfin := (Filter.eventually_all_finite (Finsupp.finite_of_degree_le (σ := σ) ℓ)).mpr
      fun α _ ↦ hpt α
    refine hfin.mono fun k hk ↦ ?_
    rw [diagramHilbertSamuel_def, diagramHilbertSamuel_def]
    congr 1
    ext α
    simp only [Set.mem_ofPred_eq]
    exact and_congr_right fun hα ↦ (hk α hα).not
  exact ⟨φ, D_lim, hφ, hup, hsub, hdeg⟩

/-- No sequence of upward-closed subsets of `σ →₀ ℕ` (`[Finite σ]`) has strictly decreasing
combinatorial Hilbert–Samuel functions in `Pi.Lex`. -/
theorem not_strictAnti_toLex_diagramHilbertSamuel {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j)) :
    ¬ StrictAnti (fun j ↦ toLex (diagramHilbertSamuel (D j))) := by
  intro hanti
  obtain ⟨φ, D_lim, hφ, -, hsub, hdeg⟩ := exists_strictMono_diagramHilbertSamuel_eventually_eq hD
  have hanti' : StrictAnti (fun k ↦ toLex (diagramHilbertSamuel (D (φ k)))) :=
    hanti.comp_strictMono hφ
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hsub
  have hk₁_ex : ∃ k₁ ≥ k₀, D_lim ⊂ D (φ k₁) := by
    by_cases h0 : D (φ k₀) = D_lim
    · refine ⟨k₀ + 1, Nat.le_succ k₀, (hk₀ (k₀ + 1) (Nat.le_succ k₀)).ssubset_of_ne ?_⟩
      intro h1
      exact (hanti' (Nat.lt_succ_self k₀)).ne
        (congrArg (fun S ↦ toLex (diagramHilbertSamuel S)) (h1.symm.trans h0.symm))
    · exact ⟨k₀, le_rfl, (hk₀ k₀ le_rfl).ssubset_of_ne (Ne.symm h0)⟩
  obtain ⟨k₁, -, hssub⟩ := hk₁_ex
  obtain ⟨m, hlt_eq, hlt_m⟩ := strictAnti_toLex_diagramHilbertSamuel hssub
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_all_finset (Finset.range (m + 1))).mpr fun ℓ _ ↦ hdeg ℓ)
  let k₂ := max (k₁ + 1) N
  have hagree (ℓ : ℕ) (hℓ : ℓ ≤ m) :
      diagramHilbertSamuel (D (φ k₂)) ℓ = diagramHilbertSamuel D_lim ℓ :=
    hN k₂ (le_max_right _ _) ℓ (Finset.mem_range_succ_iff.mpr hℓ)
  have hlt₁₂ : toLex (diagramHilbertSamuel (D (φ k₁))) <
      toLex (diagramHilbertSamuel (D (φ k₂))) := by
    refine ⟨m, fun ℓ hℓ ↦ (hlt_eq ℓ hℓ).trans (hagree ℓ hℓ.le).symm, ?_⟩
    simp only [Pi.toLex_apply] at hlt_m ⊢
    rwa [hagree m le_rfl]
  exact hlt₁₂.not_gt (hanti' (Nat.lt_succ_iff.mpr (le_refl k₁) |>.trans_le (le_max_left _ _)))

/-- For finitely many variables `σ`, the set of lexicographic Hilbert–Samuel functions of upper sets
in `σ →₀ ℕ` is well-founded under `<`. -/
theorem wellFoundedLT_setOf_isUpperSet_toLex_diagramHilbertSamuel (σ : Type*) [Finite σ] :
    WellFoundedLT {v : Lex (ℕ → ℕ) | ∃ D : Set (σ →₀ ℕ), IsUpperSet D ∧
      toLex (diagramHilbertSamuel D) = v} := by
  refine wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  choose D hD hDf using fun n ↦ (f n).2
  refine not_strictAnti_toLex_diagramHilbertSamuel hD (strictAnti_nat_of_succ_lt fun n ↦ ?_)
  have hlt : (f (n + 1) : Lex (ℕ → ℕ)) < f n := hf n
  rwa [← hDf (n + 1), ← hDf n] at hlt

/-- Any sequence of upward-closed subsets `D : ℕ → Set (σ →₀ ℕ)` in finitely many variables whose
combinatorial Hilbert–Samuel functions are antitone in `Pi.Lex` is eventually constant in
`diagramHilbertSamuel`. -/
theorem exists_diagramHilbertSamuel_eq_of_antitone_toLex {σ : Type*} [Finite σ]
    {D : ℕ → Set (σ →₀ ℕ)} (hD : ∀ j, IsUpperSet (D j))
    (hlex : Antitone (fun j ↦ toLex (diagramHilbertSamuel (D j)))) :
    ∃ j₀, ∀ j, j₀ ≤ j → diagramHilbertSamuel (D j) = diagramHilbertSamuel (D j₀) := by
  have := wellFoundedLT_setOf_isUpperSet_toLex_diagramHilbertSamuel σ
  let f : ℕ → {v : Lex (ℕ → ℕ) | ∃ D' : Set (σ →₀ ℕ), IsUpperSet D' ∧
      toLex (diagramHilbertSamuel D') = v} :=
    fun j ↦ ⟨toLex (diagramHilbertSamuel (D j)), D j, hD j, rfl⟩
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition (f := f) fun i j hij ↦ hlex hij
  exact ⟨j₀, fun j hj ↦ toLex.injective (congrArg Subtype.val (hj₀ j hj)).symm⟩

/-- Over a field `K` in finitely many variables `σ`, the set of lexicographic Hilbert–Samuel
functions realized by ideals of `MvPowerSeries σ K` is well-founded under `<` (and hence well
ordered; Bierstone–Milman–Temkin 2011, §6.1, property (4)). -/
instance wellFoundedLT_range_toLex_localQuotientHilbertSamuel_mvPowerSeries (σ K : Type*)
    [Field K] [Finite σ] :
    WellFoundedLT (Set.range fun I : Ideal (MvPowerSeries σ K) ↦
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) I)) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let φ : MvPowerSeries σ K ≃+* MvPowerSeries (Fin n) K :=
    (MvPowerSeries.renameEquiv K e).toRingEquiv
  have := wellFoundedLT_setOf_isUpperSet_toLex_diagramHilbertSamuel (Fin n)
  refine wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  choose I hIf using fun k ↦ (f k).2
  let g : ℕ → {v : Lex (ℕ → ℕ) | ∃ D : Set (Fin n →₀ ℕ), IsUpperSet D ∧
      toLex (diagramHilbertSamuel D) = v} := fun k ↦
    ⟨toLex (diagramHilbertSamuel (MonomialOrder.degLex.initialDiagram ((I k).map φ))), _,
      MonomialOrder.degLex.isUpperSet_initialDiagram _, rfl⟩
  have hg : StrictAnti g := strictAnti_nat_of_succ_lt fun k ↦ by
    have hlt : (f (k + 1) : Lex (ℕ → ℕ∞)) < f k := hf k
    rw [← hIf (k + 1), ← hIf k] at hlt
    dsimp only at hlt
    have hJI (m : ℕ) : localQuotientHilbertSamuel (MvPowerSeries (Fin n) K) ((I m).map φ) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I m) :=
      funext (localQuotientHilbertSamuel_map_equiv φ (I m))
    have hd (m : ℕ) : (fun ℓ ↦ (localQuotientHilbertSamuel (MvPowerSeries (Fin n) K)
        ((I m).map φ) ℓ).toNat) =
        diagramHilbertSamuel (MonomialOrder.degLex.initialDiagram ((I m).map φ)) :=
      funext (toNat_localQuotientHilbertSamuel_mvPowerSeries _)
    rw [← hJI (k + 1), ← hJI k, ← toLex_toNat_localQuotientHilbertSamuel_lt_iff,
      hd (k + 1), hd k] at hlt
    exact hlt
  exact not_strictAnti_of_wellFoundedLT g hg

/-- Over a field `K` in finitely many variables `σ`, any sequence of ideals of `MvPowerSeries σ K`
whose Hilbert–Samuel functions are antitone in `Pi.Lex` is eventually constant in
`localQuotientHilbertSamuel`. -/
theorem exists_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex {σ K : Type*}
    [Field K] [Finite σ] {I : ℕ → Ideal (MvPowerSeries σ K)}
    (h : Antitone (fun j ↦ toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) := by
  let f : ℕ → Set.range (fun J : Ideal (MvPowerSeries σ K) ↦
      toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) J)) :=
    fun j ↦ ⟨toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)), I j, rfl⟩
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition (f := f) fun i j hij ↦ h hij
  exact ⟨j₀, fun j hj ↦ toLex.injective (congrArg Subtype.val (hj₀ j hj)).symm⟩

/-- **Hilbert–Samuel lexicographic stabilization** (Bierstone–Milman 1989, Theorem 5.2.1;
Bierstone–Milman–Temkin 2011, §6.1, property (4)): every lexicographically nonincreasing sequence
of Hilbert–Samuel functions realized by ideals in `MvPowerSeries (Fin n) K` over a field `K` is
eventually constant. -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  refine exists_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex
    (antitone_nat_of_succ_le fun j ↦ ?_)
  rcases h j with heq | hlt
  · exact (congrArg toLex heq).le
  · exact le_of_lt hlt

/-- **Pointwise Hilbert–Samuel stabilization** (Bierstone–Milman 1989, Theorem 5.2.1): over a field
`K` in finitely many variables `σ`, every pointwise nonincreasing sequence of Hilbert–Samuel
functions realized by ideals in `MvPowerSeries σ K` is eventually constant. -/
theorem exists_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone {σ K : Type*} [Field K]
    [Finite σ] {I : ℕ → Ideal (MvPowerSeries σ K)}
    (h : Antitone (fun j ↦ localQuotientHilbertSamuel (MvPowerSeries σ K) (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) :=
  exists_localQuotientHilbertSamuel_mvPowerSeries_eq_of_antitone_toLex
    (Pi.toLex_monotone.comp_antitone h)

end Stabilization

end TauCeti

section Examples

open MonomialOrder TauCeti

-- In `K⟦X⟧`, `K⟦X⟧ / (X²)` has `H(0) = 1` and `H(ℓ) = 2` for every `ℓ ≥ 1`.
example (K : Type*) [Field K] :
    localQuotientHilbertSamuel K⟦X⟧ (Ideal.span {PowerSeries.X ^ 2}) 0 = 1 ∧
      ∀ ℓ, 1 ≤ ℓ →
        localQuotientHilbertSamuel K⟦X⟧ (Ideal.span {PowerSeries.X ^ 2}) ℓ = 2 := by
  refine ⟨by simp, fun ℓ hℓ ↦ ?_⟩
  rw [localQuotientHilbertSamuel_powerSeries_span_X_pow]
  exact congrArg Nat.cast (min_eq_right (by omega))

-- For `I_j = (X ^ max (N - j) 1) ⊆ K⟦X⟧`, the Hilbert–Samuel functions decrease in both the
-- pointwise and lexicographic orders and stabilize at the function of `K⟦X⟧ / (X)`.
example (K : Type*) [Field K] (N : ℕ) :
    let I : ℕ → Ideal K⟦X⟧ := fun j ↦ Ideal.span {PowerSeries.X ^ max (N - j) 1}
    Antitone (fun j ↦ localQuotientHilbertSamuel K⟦X⟧ (I j)) ∧
      Antitone (fun j ↦ toLex (localQuotientHilbertSamuel K⟦X⟧ (I j))) ∧
      ∀ j, N - 1 ≤ j →
        localQuotientHilbertSamuel K⟦X⟧ (I j) =
          localQuotientHilbertSamuel K⟦X⟧ (Ideal.span {PowerSeries.X}) := by
  intro I
  have hpt : Antitone (fun j ↦ localQuotientHilbertSamuel K⟦X⟧ (I j)) := by
    intro i j hij ℓ
    simp only [I, localQuotientHilbertSamuel_powerSeries_span_X_pow, Nat.cast_le]
    omega
  refine ⟨hpt, Pi.toLex_monotone.comp_antitone hpt, fun j hj ↦ ?_⟩
  ext ℓ
  have hmax : max (N - j) 1 = 1 := by omega
  simp [I, hmax]

-- Realizability as Hilbert–Samuel functions is essential for `hsLexStabilization`: the functions
-- `f j ℓ = if j ≤ ℓ then 1 else 0` form a strictly decreasing sequence in `Pi.Lex` with no
-- stabilization, and for `j ≥ 1` fail even the proper-ideal condition `H(0) = 1`.
example :
    let f : ℕ → ℕ → ℕ := fun j ℓ ↦ if j ≤ ℓ then 1 else 0
    StrictAnti (fun j ↦ toLex (f j)) ∧
      (¬ ∃ j₀, ∀ j, j₀ ≤ j → f j = f j₀) ∧
      ∀ j, 1 ≤ j → f j 0 = 0 := by
  intro f
  have hanti : StrictAnti (fun j ↦ toLex (f j)) := by
    intro i j hij
    refine ⟨i, fun ℓ hℓ ↦ ?_, ?_⟩
    · simp [f, hℓ.not_ge, (hℓ.trans hij).not_ge]
    · simp [f, hij.not_ge]
  refine ⟨hanti, ?_, fun j hj ↦ by simp [f, Nat.not_le.mpr hj]⟩
  rintro ⟨j₀, hj₀⟩
  exact (hanti (Nat.lt_succ_self j₀)).ne (congrArg toLex (hj₀ (j₀ + 1) (Nat.le_succ j₀)))

end Examples
