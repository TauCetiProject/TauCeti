/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Order.WellFoundedSet
public import TauCeti.RingTheory.LocalRing.HilbertSamuel
public import TauCeti.RingTheory.MvPowerSeries.FormalDivision
public import TauCeti.RingTheory.MvPowerSeries.Ideal
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.LocalRing.Length
import TauCeti.Data.Finsupp.Weight
import TauCeti.Order.WellFounded.UpperSetLex

/-!
# Hilbert–Samuel functions and lexicographic stabilization for formal power series

Let `K` be a field and `σ` a finite variable type. The residue field of `MvPowerSeries σ K` is
canonically isomorphic to `K` via the constant coefficient, so the length of any
`MvPowerSeries σ K`-module coincides with its `K`-vector-space dimension
(`MvPowerSeries.length_eq_length_base`).

For any degree-compatible monomial order `m : MonomialOrder σ` (in particular
`MonomialOrder.degLex`), adding the `(n + 1)`-st power of the maximal ideal adjoins all exponents of
total degree at least `n + 1` to the initial diagram
(`MonomialOrder.initialDiagram_sup_maximalIdeal_pow`). Combining Hironaka's formal division quotient
isomorphism `m.quotientEquivComplementSubmodule` with the coefficient coordinate isomorphism
`m.complementSubmoduleLinearEquiv`, the Hilbert–Samuel function
`localQuotientHilbertSamuel (MvPowerSeries σ K) I n` counts the exponents of total degree at most
`n` outside `m.initialDiagram I` (`MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries`).

In particular:

* for the zero ideal `⊥`, `H(n) = choose(card σ + n, card σ)`
  (`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`);
* for a univariate power `(X 0 ^ k) ⊆ K[[x]]`, `H(n) = min (n + 1) k`
  (`TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X_pow`);
* because every initial diagram is upward closed in the well-quasi-ordered monoid `σ →₀ ℕ`, the set
  of realized Hilbert–Samuel functions in `MvPowerSeries σ K` is well-founded for the lexicographic
  order (`TauCeti.wellFoundedOn_range_toLex_localQuotientHilbertSamuel`), so every lexicographically
  or pointwise nonincreasing sequence of realized Hilbert–Samuel functions stabilizes
  (`TauCeti.hsLexStabilization`, `TauCeti.hsPointwiseStabilization`).

## Main definitions

* `MonomialOrder.complementSubmoduleLinearEquiv`: the `R`-linear equivalence identifying series
  supported outside `m.initialDiagram I` with functions `(m.initialDiagram I)ᶜ → R`.

## Main results

* `MvPowerSeries.length_eq_length_base`: over a field `K`, module length over `MvPowerSeries σ K`
  equals `K`-module length.
* `MonomialOrder.initialDiagram_sup_pow_span_range_X`,
  `MonomialOrder.initialDiagram_sup_maximalIdeal_pow`: truncating an ideal by `𝔪 ^ n` adjoins
  `{α | n ≤ α.degree}` to any degree-compatible initial diagram.
* `MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries`,
  `MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries_degLex`: diagram-counting formula for
  the Hilbert–Samuel function of a formal quotient.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_bot`: `H_{K[[X]]}(n) = choose(|σ| + n, |σ|)`.
* `TauCeti.localQuotientHilbertSamuel_mvPowerSeries_span_X_pow`:
  `H_{K[[x]]/(x^k)}(n) = min (n + 1) k`.
* `TauCeti.wellFoundedOn_range_toLex_localQuotientHilbertSamuel`,
  `TauCeti.exists_forall_eq_of_antitone_toLex_localQuotientHilbertSamuel`,
  `TauCeti.hsLexStabilization`, `TauCeti.hsPointwiseStabilization`: lexicographic well-foundedness
  and stabilization of realized Hilbert–Samuel functions in fixed finite embedding dimension.

## References

* Edward Bierstone and Pierre D. Milman, *Uniformization of analytic spaces*, J. Amer. Math. Soc.
  2 (1989), no. 4, 801–836, Theorem 5.2.1, pp. 820–821.
* Edward Bierstone and Pierre D. Milman, *Canonical desingularization in characteristic zero by
  blowing up the maximum strata of a local invariant*, Invent. Math. 128 (1997), 207–302,
  Corollary 3.20, p. 239.
* Edward Bierstone, Pierre D. Milman, and Michael Temkin, *ℚ-universal desingularization*,
  Asian J. Math. 16 (2012), no. 4, 711–740, §6.1.
-/

public section

open scoped MonomialOrder

namespace MvPowerSeries

/-- Over a field `K`, the length of any `MvPowerSeries σ K`-module coincides with its length
(vector-space dimension) over `K`, because the residue field of `MvPowerSeries σ K` is `K`. -/
theorem length_eq_length_base {σ K M : Type*} [Field K] [AddCommGroup M]
    [Module (MvPowerSeries σ K) M] [Module K M] [IsScalarTower K (MvPowerSeries σ K) M] :
    Module.length (MvPowerSeries σ K) M = Module.length K M := by
  have hlen := IsLocalRing.length_restrictScalars K (MvPowerSeries σ K) M
  let φ : IsLocalRing.ResidueField K →ₗ[IsLocalRing.ResidueField K]
      IsLocalRing.ResidueField (MvPowerSeries σ K) :=
    Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField (MvPowerSeries σ K))
  have hφ_bij : Function.Bijective φ := by
    refine ⟨(algebraMap (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField (MvPowerSeries σ K))).injective, fun x ↦ ?_⟩
    obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective x
    refine ⟨IsLocalRing.residue K (constantCoeff f), ?_⟩
    have hmem : C (constantCoeff f) - f ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ K) := by
      rw [maximalIdeal_eq_ker_constantCoeff, RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]
    have hres : IsLocalRing.residue (MvPowerSeries σ K) (C (constantCoeff f)) =
        IsLocalRing.residue (MvPowerSeries σ K) f := by
      rw [← sub_eq_zero, ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    simpa [φ, IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ResidueField.map_residue,
      algebraMap_apply] using hres
  have hres_len : Module.length (IsLocalRing.ResidueField K)
      (IsLocalRing.ResidueField (MvPowerSeries σ K)) = 1 := by
    rw [← (LinearEquiv.ofBijective φ hφ_bij).length_eq, Module.length_eq_rank,
      Module.rank_self, map_one]
  rw [hres_len, mul_one] at hlen
  exact hlen.symm

end MvPowerSeries

namespace MonomialOrder

open scoped Classical in
private noncomputable def complementOfFun {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R))
    (g : ↥(m.initialDiagram I)ᶜ → R) : MvPowerSeries σ R :=
  fun α ↦ if h : α ∈ (m.initialDiagram I)ᶜ then g ⟨α, h⟩ else 0

private theorem coeff_complementOfFun_of_not_mem {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R))
    (g : ↥(m.initialDiagram I)ᶜ → R) {α : σ →₀ ℕ} (hα : α ∉ m.initialDiagram I) :
    MvPowerSeries.coeff α (m.complementOfFun I g) = g ⟨α, hα⟩ := by
  rw [MvPowerSeries.coeff_apply]
  exact dite_eq_left hα

private theorem coeff_complementOfFun_of_mem {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R))
    (g : ↥(m.initialDiagram I)ᶜ → R) {α : σ →₀ ℕ} (hα : α ∈ m.initialDiagram I) :
    MvPowerSeries.coeff α (m.complementOfFun I g) = 0 := by
  rw [MvPowerSeries.coeff_apply]
  exact dite_eq_right (not_not.mpr hα)

/-- Series supported outside `m.initialDiagram I` are `R`-linearly equivalent to functions on the
complement of `m.initialDiagram I`, via reading off coefficients. -/
noncomputable def complementSubmoduleLinearEquiv {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R)) :
    m.complementSubmodule I ≃ₗ[R] (↥(m.initialDiagram I)ᶜ → R) where
  toFun f α := MvPowerSeries.coeff α.1 f.1
  map_add' f g := by ext α; simp
  map_smul' r f := by ext α; simp
  invFun g :=
    ⟨m.complementOfFun I g, by
      rw [m.mem_complementSubmodule_iff]
      intro β hβ hD
      exact MvPowerSeries.mem_support.mp hβ (m.coeff_complementOfFun_of_mem I g hD)⟩
  left_inv f := by
    ext α
    dsimp only
    by_cases h : α ∈ m.initialDiagram I
    · rw [m.coeff_complementOfFun_of_mem I _ h]
      by_contra hne
      exact m.mem_complementSubmodule_iff.mp f.2 α
        (MvPowerSeries.mem_support.mpr (Ne.symm hne)) h
    · exact m.coeff_complementOfFun_of_not_mem I _ h
  right_inv g := by
    ext ⟨α, hα⟩
    exact m.coeff_complementOfFun_of_not_mem I g hα

/-- Evaluating `m.complementSubmoduleLinearEquiv I` reads off the corresponding coefficient. -/
@[simp]
theorem complementSubmoduleLinearEquiv_apply {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R))
    (f : m.complementSubmodule I) (α : ↥(m.initialDiagram I)ᶜ) :
    m.complementSubmoduleLinearEquiv I f α = MvPowerSeries.coeff α.1 f.1 := (rfl)

/-- Outside `m.initialDiagram I`, the inverse of `m.complementSubmoduleLinearEquiv I` recovers the
prescribed coefficient. -/
@[simp]
theorem coeff_complementSubmoduleLinearEquiv_symm_of_not_mem {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R))
    (g : ↥(m.initialDiagram I)ᶜ → R) {α : σ →₀ ℕ} (hα : α ∉ m.initialDiagram I) :
    MvPowerSeries.coeff α ((m.complementSubmoduleLinearEquiv I).symm g : MvPowerSeries σ R) =
      g ⟨α, hα⟩ :=
  m.coeff_complementOfFun_of_not_mem I g hα

/-- Inside `m.initialDiagram I`, the inverse of `m.complementSubmoduleLinearEquiv I` has zero
coefficient. -/
@[simp]
theorem coeff_complementSubmoduleLinearEquiv_symm_of_mem {σ R : Type*} [Semiring R]
    (m : MonomialOrder σ) (I : Ideal (MvPowerSeries σ R))
    (g : ↥(m.initialDiagram I)ᶜ → R) {α : σ →₀ ℕ} (hα : α ∈ m.initialDiagram I) :
    MvPowerSeries.coeff α ((m.complementSubmoduleLinearEquiv I).symm g : MvPowerSeries σ R) =
      0 :=
  m.coeff_complementOfFun_of_mem I g hα

/-- For any degree-compatible monomial order `m` on finitely many variables over a nontrivial
commutative ring, adding the `n`-th power of the variable ideal to `I` adjoins all exponents of
total degree at least `n` to the initial diagram. -/
theorem initialDiagram_sup_pow_span_range_X {σ R : Type*} [Finite σ] [CommRing R] [Nontrivial R]
    (m : MonomialOrder σ) (hdeg : ∀ ⦃α β : σ →₀ ℕ⦄, α ≼[m] β → α.degree ≤ β.degree)
    (I : Ideal (MvPowerSeries σ R)) (n : ℕ) :
    m.initialDiagram (I ⊔ Ideal.span (Set.range MvPowerSeries.X) ^ n) =
      m.initialDiagram I ∪ {α : σ →₀ ℕ | n ≤ α.degree} := by
  ext α
  constructor
  · intro hα
    by_cases hdegα : n ≤ α.degree
    · exact Or.inr hdegα
    · left
      obtain ⟨h, hhmem, hh0, hhexp⟩ := m.mem_initialDiagram_iff.mp hα
      obtain ⟨f, hfI, g, hgX, rfl⟩ := Submodule.mem_sup.mp hhmem
      have hgord : (n : ℕ∞) ≤ g.order :=
        MvPowerSeries.mem_pow_span_range_X_iff_le_order.mp hgX
      have hgcoeff : ∀ β, β ≼[m] α → MvPowerSeries.coeff β g = 0 := fun β hβα ↦ by
        refine MvPowerSeries.coeff_of_lt_order ?_
        have hlt : β.degree < n := (hdeg hβα).trans_lt (Nat.lt_of_not_ge hdegα)
        exact (Nat.cast_lt.mpr hlt).trans_le hgord
      have hcoeff_eq : ∀ β, β ≼[m] α → MvPowerSeries.coeff β f = MvPowerSeries.coeff β (f + g) :=
        fun β hβα ↦ by rw [map_add, hgcoeff β hβα, add_zero]
      have hfα : MvPowerSeries.coeff α f ≠ 0 := by
        rw [hcoeff_eq α le_rfl, ← hhexp]
        exact m.coeff_initialExp_ne_zero hh0
      have hf0 : f ≠ 0 := fun hf ↦ hfα (by simp [hf])
      refine m.mem_initialDiagram_iff.mpr ⟨f, hfI, hf0, ?_⟩
      refine m.initialExp_eq_of_coeff_ne_zero_of_forall_lt hfα fun β hβα ↦ ?_
      rw [hcoeff_eq β hβα.le]
      exact m.coeff_eq_zero_of_lt_initialExp (hhexp.symm ▸ hβα)
  · rintro (hI | hdegα)
    · exact m.initialDiagram_mono le_sup_left hI
    · refine m.mem_initialDiagram_iff.mpr
        ⟨MvPowerSeries.monomial α 1, Ideal.mem_sup_right ?_,
          mt (congrArg (MvPowerSeries.coeff α)) (by simp),
          m.initialExp_monomial_of_ne_zero α one_ne_zero⟩
      rw [MvPowerSeries.mem_pow_span_range_X_iff_le_order,
        MvPowerSeries.order_monomial_of_ne_zero one_ne_zero]
      exact Nat.cast_le.mpr hdegα

/-- Over a field in finitely many variables, adding the `n`-th power of the maximal ideal to `I`
adjoins all exponents of total degree at least `n` to any degree-compatible initial diagram. -/
theorem initialDiagram_sup_maximalIdeal_pow {σ K : Type*} [Finite σ] [Field K]
    (m : MonomialOrder σ) (hdeg : ∀ ⦃α β : σ →₀ ℕ⦄, α ≼[m] β → α.degree ≤ β.degree)
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    m.initialDiagram (I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ n) =
      m.initialDiagram I ∪ {α : σ →₀ ℕ | n ≤ α.degree} := by
  rw [MvPowerSeries.maximalIdeal_eq_span_range_X]
  exact m.initialDiagram_sup_pow_span_range_X hdeg I n

/-- **Diagram-counting formula for the Hilbert–Samuel function** (Bierstone–Milman 1997,
Corollary 3.20): for any degree-compatible monomial order `m` on finitely many variables over a
field `K`, `localQuotientHilbertSamuel (MvPowerSeries σ K) I n` counts the exponents of total
degree at most `n` outside `m.initialDiagram I`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries {σ K : Type*} [Finite σ] [Field K]
    (m : MonomialOrder σ) (hdeg : ∀ ⦃α β : σ →₀ ℕ⦄, α ≼[m] β → α.degree ≤ β.degree)
    (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I n =
      ({α : σ →₀ ℕ | α ∉ m.initialDiagram I ∧ α.degree ≤ n}.ncard : ℕ∞) := by
  set J : Ideal (MvPowerSeries σ K) := I ⊔ IsLocalRing.maximalIdeal (MvPowerSeries σ K) ^ (n + 1)
  have hcompl : (m.initialDiagram J)ᶜ =
      {α : σ →₀ ℕ | α ∉ m.initialDiagram I ∧ α.degree ≤ n} := by
    ext α
    simp only [J, Set.mem_compl_iff, m.initialDiagram_sup_maximalIdeal_pow hdeg, Set.mem_ofPred_eq,
      Set.mem_union, not_or, not_le, Nat.lt_succ_iff]
  have hfin : (m.initialDiagram J)ᶜ.Finite := by
    rw [hcompl]
    exact (Finsupp.finite_of_degree_le n).subset fun _ h ↦ h.2
  have : Fintype ↥(m.initialDiagram J)ᶜ := hfin.fintype
  rw [TauCeti.localQuotientHilbertSamuel_def, MvPowerSeries.length_eq_length_base,
    (m.quotientEquivComplementSubmodule J).length_eq,
    (m.complementSubmoduleLinearEquiv J).length_eq,
    Module.length_eq_rank, rank_fun', map_natCast, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, hcompl]

/-- Specialization of the diagram-counting formula to graded lexicographic order
`MonomialOrder.degLex`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_degLex {σ K : Type*} [Finite σ] [LinearOrder σ]
    [Field K] (I : Ideal (MvPowerSeries σ K)) (n : ℕ) :
    TauCeti.localQuotientHilbertSamuel (MvPowerSeries σ K) I n =
      ({α : σ →₀ ℕ | α ∉ MonomialOrder.degLex.initialDiagram I ∧ α.degree ≤ n}.ncard : ℕ∞) :=
  MonomialOrder.degLex.localQuotientHilbertSamuel_mvPowerSeries
    (fun _ _ h ↦ Finsupp.DegLex.monotone_degree h) I n

end MonomialOrder

namespace TauCeti

/-- The Hilbert–Samuel function of the formal power-series ring `MvPowerSeries σ K` in finitely
many variables is `H(n) = choose(card σ + n, card σ)`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_bot {σ K : Type*} [Finite σ] [Field K] (n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K) ⊥ n =
      ((Nat.card σ + n).choose (Nat.card σ) : ℕ∞) := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries_degLex]
  congr 1
  have hset : {α : σ →₀ ℕ | α ∉ MonomialOrder.degLex.initialDiagram
        (⊥ : Ideal (MvPowerSeries σ K)) ∧ α.degree ≤ n} =
      ↑((Finset.range (n + 1)).biUnion ((Finset.univ : Finset σ).finsuppAntidiag ·)) := by
    ext α
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  · simp [Finset.card_finsuppAntidiag_nat_eq_multichoose, Nat.sum_range_multichoose,
      Nat.card_eq_fintype_card, add_comm]
  · intro a _ b _ hab
    refine Finset.disjoint_left.mpr fun α ha hb ↦ hab ?_
    rw [Finset.mem_finsuppAntidiag] at ha hb
    exact ha.1.symm.trans hb.1

-- For `K[[x₁, …, x_d]]`, `H(ℓ) = choose(d + ℓ, d)`.
example {K : Type*} [Field K] (d ℓ : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries (Fin d) K) ⊥ ℓ = ((d + ℓ).choose d : ℕ∞) := by
  simpa using localQuotientHilbertSamuel_mvPowerSeries_bot (σ := Fin d) (K := K) ℓ

/-- In one variable over a field, the quotient `K[[x]] ⧸ (x ^ k)` has Hilbert–Samuel function
`H(n) = min (n + 1) k` for every `k, n : ℕ`. -/
theorem localQuotientHilbertSamuel_mvPowerSeries_span_X_pow {σ K : Type*} [Unique σ] [Field K]
    (i : σ) (k n : ℕ) :
    localQuotientHilbertSamuel (MvPowerSeries σ K)
      (Ideal.span {MvPowerSeries.X i ^ k}) n = ((min (n + 1) k : ℕ) : ℕ∞) := by
  let _ : LinearOrder σ :=
    LinearOrder.lift' (fun _ : σ ↦ (0 : Fin 1)) (fun _ _ _ ↦ Subsingleton.elim _ _)
  rw [MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries_degLex]
  congr 1
  have hspan : ({MvPowerSeries.monomial (Finsupp.single i k) (1 : K)} :
      Set (MvPowerSeries σ K)) =
      (fun α ↦ MvPowerSeries.monomial α (1 : K)) '' {Finsupp.single i k} := by
    simp
  have hdiag : MonomialOrder.degLex.initialDiagram
      (Ideal.span {MvPowerSeries.X i ^ k} : Ideal (MvPowerSeries σ K)) =
      Set.Ici (Finsupp.single i k) := by
    rw [MvPowerSeries.X_pow_eq, hspan, MonomialOrder.degLex.initialDiagram_span_monomial]
    simp
  rw [hdiag]
  have hbij : {α : σ →₀ ℕ | α ∉ Set.Ici (Finsupp.single i k) ∧ α.degree ≤ n} =
      Finsupp.single i '' (Finset.range (min (n + 1) k) : Set ℕ) := by
    ext α
    have hdegα : α.degree = α i := by
      rw [Finsupp.degree_eq_sum, Fintype.sum_unique, Subsingleton.elim default i]
    have hleα : Finsupp.single i k ≤ α ↔ k ≤ α i := by
      rw [Finsupp.le_def]
      exact ⟨fun h ↦ by simpa using h i, fun h j ↦ by
        rw [Subsingleton.elim j i]; simpa using h⟩
    simp only [Set.mem_ofPred_eq, Set.mem_Ici, hleα, not_le, hdegα, Set.mem_image, Finset.mem_coe,
      Finset.mem_range, lt_min_iff, Nat.lt_succ_iff]
    refine ⟨fun ⟨hlt, hle⟩ ↦ ⟨α i, ⟨hle, hlt⟩, Finsupp.ext fun j ↦ by
      rw [Subsingleton.elim j i, Finsupp.single_eq_same]⟩, ?_⟩
    rintro ⟨m, ⟨hle, hlt⟩, rfl⟩
    simp [hlt, hle]
  rw [hbij, Set.ncard_image_of_injective _ (Finsupp.single_injective i), Set.ncard_coe_finset,
    Finset.card_range]

-- For `K[[x]] / (x²)`, `H(0) = 1` and `H(ℓ) = 2` for `ℓ ≥ 1`.
example {K : Type*} [Field K] :
    localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
      (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 2}) 0 = 1 := by
  simp [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow]

example {K : Type*} [Field K] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
      (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 2}) ℓ = 2 := by
  rw [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow, Nat.min_eq_right (by omega),
    Nat.cast_ofNat]

/-- The set of Hilbert–Samuel functions realized by ideals of `MvPowerSeries σ K` (for finite `σ`
and a field `K`) is well-founded under the lexicographic order on `ℕ → ℕ∞`. -/
theorem wellFoundedOn_range_toLex_localQuotientHilbertSamuel
    (σ K : Type*) [Finite σ] [Field K] :
    Set.WellFoundedOn
      (Set.range fun I : Ideal (MvPowerSeries σ K) ↦
        toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) I))
      (· < ·) := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  let _ : LinearOrder σ := LinearOrder.lift' e e.injective
  rw [Set.WellFoundedOn, wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨f, hf⟩ ↦ ?_⟩
  choose I hI using fun j ↦ (f j).2
  have hstrict : StrictAnti fun j ↦
      toLex fun ℓ ↦ {α : σ →₀ ℕ | α ∉ MonomialOrder.degLex.initialDiagram (I j) ∧
        α.degree ≤ ℓ}.ncard := by
    refine strictAnti_nat_of_succ_lt fun j ↦ ?_
    have hlt : (f (j + 1)).1 < (f j).1 := hf j
    rw [← hI (j + 1), ← hI j] at hlt
    obtain ⟨ℓ, heq, hltℓ⟩ := hlt
    refine ⟨ℓ, fun r hr ↦ ?_, ?_⟩
    · have hr' := heq r hr
      simp only [Pi.toLex_apply,
        MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries_degLex] at hr'
      exact Nat.cast_injective hr'
    · simp only [Pi.toLex_apply,
        MonomialOrder.localQuotientHilbertSamuel_mvPowerSeries_degLex] at hltℓ ⊢
      exact Nat.cast_lt.mp hltℓ
  exact not_strictAnti_toLex_ncard_compl_of_isUpperSet Finsupp.finite_of_degree_le
    (fun j ↦ MonomialOrder.degLex.isUpperSet_initialDiagram (I j)) hstrict

/-- Every lexicographically nonincreasing sequence of Hilbert–Samuel functions realized by ideals
in a fixed finite-variable formal power-series ring `MvPowerSeries σ K` is eventually constant. -/
theorem exists_forall_eq_of_antitone_toLex_localQuotientHilbertSamuel
    {σ K : Type*} [Finite σ] [Field K] (I : ℕ → Ideal (MvPowerSeries σ K))
    (hanti : Antitone fun j ↦ toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) := by
  let S : Set (Lex (ℕ → ℕ∞)) := Set.range fun J : Ideal (MvPowerSeries σ K) ↦
    toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) J)
  have : WellFoundedLT S :=
    WellFounded.mono (r := (· < ·)) (wellFoundedOn_range_toLex_localQuotientHilbertSamuel σ K)
      fun _ _ h ↦ h
  let g : ℕ → S := fun j ↦ ⟨toLex (localQuotientHilbertSamuel (MvPowerSeries σ K) (I j)),
    ⟨I j, rfl⟩⟩
  obtain ⟨j₀, hj₀⟩ := WellFoundedLT.antitone_chain_condition (f := g) fun a b hab ↦ hanti hab
  exact ⟨j₀, fun j hj ↦ toLex.injective (congrArg Subtype.val (hj₀ j hj)).symm⟩

/-- **Lexicographic Hilbert–Samuel stabilization** (Bierstone–Milman 1989, Theorem 5.2.1;
Bierstone–Milman–Temkin 2012, §6.1): every lexicographically nonincreasing sequence of
Hilbert–Samuel functions realized by ideals in `MvPowerSeries (Fin n) K` is eventually constant. -/
theorem hsLexStabilization (K : Type*) [Field K] (n : ℕ)
    (I : ℕ → Ideal (MvPowerSeries (Fin n) K))
    (h : ∀ j, localQuotientHilbertSamuel _ (I (j + 1)) = localQuotientHilbertSamuel _ (I j) ∨
      Pi.Lex (· < ·) (· < ·) (localQuotientHilbertSamuel _ (I (j + 1)))
        (localQuotientHilbertSamuel _ (I j))) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel _ (I j) = localQuotientHilbertSamuel _ (I j₀) := by
  refine exists_forall_eq_of_antitone_toLex_localQuotientHilbertSamuel I ?_
  refine antitone_nat_of_succ_le fun j ↦ ?_
  rcases h j with heq | hlt
  · exact le_of_eq (congrArg toLex heq)
  · exact le_of_lt hlt

/-- **Pointwise Hilbert–Samuel stabilization**: every pointwise nonincreasing sequence of
Hilbert–Samuel functions realized by ideals in `MvPowerSeries σ K` is eventually constant. -/
theorem hsPointwiseStabilization {σ K : Type*} [Finite σ] [Field K]
    (I : ℕ → Ideal (MvPowerSeries σ K))
    (h : ∀ j ℓ, localQuotientHilbertSamuel (MvPowerSeries σ K) (I (j + 1)) ℓ ≤
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) ℓ) :
    ∃ j₀, ∀ j, j₀ ≤ j →
      localQuotientHilbertSamuel (MvPowerSeries σ K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries σ K) (I j₀) :=
  exists_forall_eq_of_antitone_toLex_localQuotientHilbertSamuel I
    (antitone_nat_of_succ_le fun j ↦ Pi.toLex_monotone (h j))

-- For `I_j = (x ^ max (N - j) 1) ⊆ K[[x]]`, the Hilbert–Samuel functions decrease pointwise and
-- stabilize at `K[[x]] / (x)` once `N ≤ j + 1`.
example {K : Type*} [Field K] (N : ℕ) :
    let I : ℕ → Ideal (MvPowerSeries (Fin 1) K) :=
      fun j ↦ Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ max (N - j) 1}
    (∀ j ℓ, localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K) (I (j + 1)) ℓ ≤
      localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K) (I j) ℓ) ∧
    ∀ j, N ≤ j + 1 →
      localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K) (I j) =
        localQuotientHilbertSamuel (MvPowerSeries (Fin 1) K)
          (Ideal.span {MvPowerSeries.X (0 : Fin 1) ^ 1}) := by
  refine ⟨fun j ℓ ↦ ?_, fun j hj ↦ funext fun ℓ ↦ ?_⟩
  · simp only [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow, Nat.cast_le]
    exact min_le_min_left _ (max_le_max_right _ (Nat.sub_le_sub_left (Nat.le_succ j) N))
  · simp only [localQuotientHilbertSamuel_mvPowerSeries_span_X_pow]
    congr 2
    omega

-- Realizability by formal ideals is essential: arbitrary `ℕ → ℕ∞` functions can decrease strictly
-- forever in the lexicographic order.
example : StrictAnti fun j : ℕ ↦ toLex fun ℓ : ℕ ↦ if j ≤ ℓ then (1 : ℕ∞) else 0 :=
  strictAnti_nat_of_succ_lt fun j ↦
    ⟨j, fun r hr ↦ by
      simp only [Pi.toLex_apply]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)],
      by simp⟩

end TauCeti
