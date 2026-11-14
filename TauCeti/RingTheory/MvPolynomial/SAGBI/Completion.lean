/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Finite
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Presentation
import Mathlib.Basic.Finite.Sum

/-!
# Certified SAGBI completion and termination

Let `m` be a monomial order on `σ →₀ ℕ` and `k` a field. Unlike Buchberger completion for ideals
(`MonomialOrder.exists_sPolynomialStep_completion`), SAGBI completion for subalgebras faces two
structural subtleties:

1. Adjoining a nonzero subduction remainder `r` of an element `aeval b P` normalizes `r` to
   `m.monicNormalize r = C (m.leadingCoeff r)⁻¹ * r` and records the scalar `m.leadingCoeff r`
   (and its inverse) in the presentation maps relating the old and enlarged generator families.
2. Submonoids of `σ →₀ ℕ` do not satisfy the ascending chain condition, so strictly enlarging the
   leading-term algebra at each step does not by itself force termination—even when the full
   initial algebra is finitely generated, an unfair selection of relations could neglect a needed
   generator forever, and without finite generation of the initial algebra completion may run
   forever even on a finitely generated subalgebra.

This file develops the presentation maps of subduction-remainder adjunction, defines fair SAGBI
completion sequences (`MonomialOrder.IsFairSAGBISequence`), proves that every fair completion
sequence exhausts `m.leadingExponents` and `m.initialAlgebra` unconditionally and terminates at a
SAGBI basis whenever the initial algebra is finitely generated, constructs a concrete certified
batch completion sequence equipped with surjective presentation retractions from any finite monic
family (and, via `MvPolynomial.rescale`, from any finite nonzero family), and exhibits the
infinite toric-binomial completion chain on `TauCeti.robbianoSweedlerSubalgebra`.

## Main definitions and results

* `MonomialOrder.subductionRetract` and `MonomialOrder.subductionLiftExpr`: the `k`-algebra
  retraction sending each adjoined normalized-remainder variable `X (.inr l)` to
  `C (m.leadingCoeff (r l))⁻¹ * (P l - Q l)`, and the corresponding scalar-retaining lift
  expression `rename Sum.inl (Q l) + C (m.leadingCoeff (r l)) * X (.inr l)`.
* `MonomialOrder.aeval_comp_subductionRetract`,
  `MonomialOrder.ker_subductionRetract_eq_span_of_ne_zero`,
  `MonomialOrder.ker_aeval_sumElim_monicNormalize`, and
  `MonomialOrder.map_subductionRetract_ker_aeval`: factorization of evaluation and exact transport
  of presentation kernels across normalized remainder adjunction.
* `MonomialOrder.IsFairSAGBISequence`: a monotone sequence of monic families generating the same
  subalgebra in which every stage's toric ideal has a binomial generating set whose members are
  eventually subducted with nonzero normalized remainders adjoined.
* `MonomialOrder.IsFairSAGBISequence.iSup_closure_degree_eq_leadingExponents` and
  `MonomialOrder.IsFairSAGBISequence.iSup_adjoin_leadingTerm_eq_initialAlgebra`: any fair
  completion sequence exhausts the leading exponents and initial algebra.
* `MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_of_fg` and
  `MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_iff_fg_leadingExponents`: finite-stage
  termination under finite generation of the initial algebra, and equivalence for sequences of
  finite families.
* `MonomialOrder.sagbiCompletionFamily`, `MonomialOrder.sagbiCompletionRetract`,
  `MonomialOrder.isFairSAGBISequence_sagbiCompletionFamily`, and
  `MonomialOrder.exists_finite_monic_isSAGBIBasis_of_fg`: concrete certified batch completion with
  surjective presentation retractions, including leading-coefficient rescaling for nonmonic finite
  nonzero families.
* `TauCeti.robbianoSweedlerStage`, `TauCeti.isSubduction_robbianoSweedlerStage`, and
  `TauCeti.adjoin_leadingTerm_robbianoSweedlerStage_lt`: explicit infinite sequence of nonzero
  toric-binomial subduction-remainder steps on `TauCeti.robbianoSweedlerSubalgebra`.

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87.
* D. Kapur, K. Madlener, *A completion procedure for computing a canonical basis for a
  k-subalgebra*, in *Computers and Mathematics*, Springer, 1989, 1–11.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
* W. Bruns, A. Conca, M. Lembo, *SAGBI combinatorics of maximal minors and a SAGBI algorithm*,
  arXiv:2504.10019, Section 2.
-/

public section

open MvPolynomial

namespace MonomialOrder

section ZeroRemainder

variable {σ ι R : Type*} [CommSemiring R] {m : MonomialOrder σ}
  {b : ι → MvPolynomial σ R} {Q : MvPolynomial ι R} {r : MvPolynomial σ R}

/-- Every subduction of the zero polynomial has zero remainder, because `0` lies in the additive
submonoid generated by any family of leading exponents. -/
theorem IsSubduction.eq_zero_of_zero (h : m.IsSubduction b 0 Q r) : r = 0 := by
  by_contra hr
  have hdeg : m.degree r = 0 := by
    have hle := h.degree_le
    rw [m.degree_zero] at hle
    exact m.toSyn.injective (le_antisymm hle (by rw [map_zero]; exact m.zero_le _))
  exact h.irreducible 0 (hdeg ▸ m.degree_mem_support hr) (zero_mem _)

end ZeroRemainder

section SubductionRetract

variable {σ ι κ k : Type*} [Field k] (m : MonomialOrder σ)

/-- The `k`-algebra retraction `MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial ι k` recording a
subduction-remainder adjunction step: original variables `X (.inl i)` map to `X i`, and each
adjoined normalized-remainder variable `X (.inr l)` maps to
`C (m.leadingCoeff (r l))⁻¹ * (P l - Q l)`. -/
noncomputable def subductionRetract (P Q : κ → MvPolynomial ι k) (r : κ → MvPolynomial σ k) :
    MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial ι k :=
  aeval (Sum.elim X fun l ↦ C (m.leadingCoeff (r l))⁻¹ * (P l - Q l))

/-- The expression `rename Sum.inl (Q l) + C (m.leadingCoeff (r l)) * X (.inr l)` for
`aeval b (P l)` in the enlarged family `Sum.elim b (m.monicNormalize ∘ r)`, retaining the leading
coefficient of `r l` before normalization. -/
noncomputable def subductionLiftExpr (Q : κ → MvPolynomial ι k) (r : κ → MvPolynomial σ k)
    (l : κ) : MvPolynomial (ι ⊕ κ) k :=
  rename Sum.inl (Q l) + C (m.leadingCoeff (r l)) * X (Sum.inr l)

variable {m} {b : ι → MvPolynomial σ k} {P Q : κ → MvPolynomial ι k} {r : κ → MvPolynomial σ k}

/-- Unfolding lemma for `MonomialOrder.subductionRetract`. -/
theorem subductionRetract_def (P Q : κ → MvPolynomial ι k) (r : κ → MvPolynomial σ k) :
    m.subductionRetract P Q r =
      aeval (Sum.elim X fun l ↦ C (m.leadingCoeff (r l))⁻¹ * (P l - Q l)) :=
  (rfl)

/-- Unfolding lemma for `MonomialOrder.subductionLiftExpr`. -/
theorem subductionLiftExpr_def (Q : κ → MvPolynomial ι k) (r : κ → MvPolynomial σ k) (l : κ) :
    m.subductionLiftExpr Q r l =
      rename Sum.inl (Q l) + C (m.leadingCoeff (r l)) * X (Sum.inr l) :=
  (rfl)

/-- `MonomialOrder.subductionRetract` fixes original generator variables `X (.inl i)`. -/
@[simp]
theorem subductionRetract_X_inl (i : ι) :
    m.subductionRetract P Q r (X (Sum.inl i)) = X i := by
  simp [subductionRetract_def]

/-- `MonomialOrder.subductionRetract` maps each adjoined remainder variable `X (.inr l)` to
`C (m.leadingCoeff (r l))⁻¹ * (P l - Q l)`. -/
@[simp]
theorem subductionRetract_X_inr (l : κ) :
    m.subductionRetract P Q r (X (Sum.inr l)) = C (m.leadingCoeff (r l))⁻¹ * (P l - Q l) := by
  simp [subductionRetract_def]

/-- `MonomialOrder.subductionRetract` is a left inverse to `rename Sum.inl` as a `k`-algebra
homomorphism. -/
theorem subductionRetract_comp_rename_inl :
    (m.subductionRetract P Q r).comp (rename Sum.inl) = AlgHom.id k (MvPolynomial ι k) :=
  algHom_ext fun i ↦ by simp

/-- Applying `MonomialOrder.subductionRetract` to a polynomial in the original variables recovers
that polynomial. -/
@[simp]
theorem subductionRetract_rename_inl (p : MvPolynomial ι k) :
    m.subductionRetract P Q r (rename Sum.inl p) = p :=
  AlgHom.congr_fun m.subductionRetract_comp_rename_inl p

/-- `MonomialOrder.subductionRetract` is surjective. -/
theorem subductionRetract_surjective : Function.Surjective (m.subductionRetract P Q r) :=
  fun p ↦ ⟨rename Sum.inl p, m.subductionRetract_rename_inl p⟩

/-- Evaluating the enlarged family `Sum.elim b (m.monicNormalize ∘ r)` factors through evaluation of
`b` along `m.subductionRetract P Q r`. -/
theorem aeval_comp_subductionRetract
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) :
    (aeval b).comp (m.subductionRetract P Q r) = aeval (Sum.elim b (m.monicNormalize ∘ r)) := by
  refine algHom_ext fun x ↦ ?_
  cases x with
  | inl i => simp
  | inr l =>
    simp only [AlgHom.comp_apply, subductionRetract_X_inr, aeval_X, Sum.elim_inr,
      Function.comp_apply]
    exact ((hs l).monicNormalize_eq_aeval rfl).symm

/-- Adjoining a family of normalized subduction remainders of elements of `k[b]` leaves the
generated subalgebra unchanged. -/
theorem adjoin_range_sumElim_monicNormalize
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) :
    Algebra.adjoin k (Set.range (Sum.elim b (m.monicNormalize ∘ r))) =
      Algebra.adjoin k (Set.range b) := by
  ext f
  simp only [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range,
    ← m.aeval_comp_subductionRetract hs, AlgHom.comp_apply]
  exact ⟨fun ⟨p, hp⟩ ↦ ⟨_, hp⟩, fun ⟨p, hp⟩ ↦ ⟨rename Sum.inl p, by simp [hp]⟩⟩

/-- In the enlarged family `Sum.elim b (m.monicNormalize ∘ r)`, the scalar-retaining expression
`m.subductionLiftExpr Q r l` evaluates back to `aeval b (P l)`. -/
theorem aeval_sumElim_subductionLiftExpr
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) (l : κ) :
    aeval (Sum.elim b (m.monicNormalize ∘ r)) (m.subductionLiftExpr Q r l) = aeval b (P l) := by
  rw [subductionLiftExpr_def, map_add, map_mul, aeval_rename, Sum.elim_comp_inl, aeval_C,
    algebraMap_eq, aeval_X, Sum.elim_inr, Function.comp_apply, C_leadingCoeff_mul_monicNormalize,
    ← (hs l).eq_aeval_add]

/-- Every exponent in the support of `m.subductionLiftExpr Q r l` has weight at most
`m.degree (aeval b (P l))` with respect to `Sum.elim b (m.monicNormalize ∘ r)`. -/
theorem linearCombination_subductionLiftExpr_le
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) (l : κ)
    {w : ι ⊕ κ →₀ ℕ} (hw : w ∈ (m.subductionLiftExpr Q r l).support) :
    Finsupp.linearCombination ℕ (m.degree ∘ Sum.elim b (m.monicNormalize ∘ r)) w ≼[m]
      m.degree (aeval b (P l)) := by
  classical
  rw [subductionLiftExpr_def] at hw
  rcases Finset.mem_union.1 (support_add hw) with hw | hw
  · obtain ⟨u, rfl, hu0⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 hw)
    rw [Finsupp.linearCombination_mapDomain, Function.comp_assoc, Sum.elim_comp_inl]
    exact (hs l).support_le u (mem_support_iff.2 hu0)
  · rw [X, C_mul_monomial, mul_one] at hw
    have hw' : w = Finsupp.single (Sum.inr l) 1 :=
      Finset.mem_singleton.1 (support_monomial_subset hw)
    rw [hw', Finsupp.linearCombination_single, one_smul, Function.comp_apply, Sum.elim_inr,
      Function.comp_apply, degree_monicNormalize]
    exact (hs l).degree_le

/-- The kernel of `m.subductionRetract P Q r` is generated by the graph equations expressing each
new variable `X (.inr l)` as `C (m.leadingCoeff (r l))⁻¹ * (P l - Q l)` in the old variables. -/
theorem ker_subductionRetract (P Q : κ → MvPolynomial ι k) (r : κ → MvPolynomial σ k) :
    RingHom.ker (m.subductionRetract P Q r) =
      Ideal.span (Set.range fun l ↦
        X (Sum.inr l) - rename Sum.inl (C (m.leadingCoeff (r l))⁻¹ * (P l - Q l))) :=
  MvPolynomial.ker_aeval_sumElim _

/-- When every adjoined remainder `r l` is nonzero, clearing `(m.leadingCoeff (r l))⁻¹` identifies
the kernel of `m.subductionRetract P Q r` with the ideal generated by the lifted subduction
equations `rename Sum.inl (P l) - m.subductionLiftExpr Q r l`. -/
theorem ker_subductionRetract_eq_span_of_ne_zero (P Q : κ → MvPolynomial ι k)
    {r : κ → MvPolynomial σ k} (hr : ∀ l, r l ≠ 0) :
    RingHom.ker (m.subductionRetract P Q r) =
      Ideal.span (Set.range fun l ↦ rename Sum.inl (P l) - m.subductionLiftExpr Q r l) := by
  rw [m.ker_subductionRetract]
  have hrel (l : κ) :
      rename Sum.inl (P l) - m.subductionLiftExpr Q r l =
        -C (m.leadingCoeff (r l)) *
          (X (Sum.inr l) - rename Sum.inl (C (m.leadingCoeff (r l))⁻¹ * (P l - Q l))) := by
    have hc : m.leadingCoeff (r l) ≠ 0 := m.leadingCoeff_ne_zero_iff.2 (hr l)
    have hinv : C (m.leadingCoeff (r l)) * C (m.leadingCoeff (r l))⁻¹ =
        (1 : MvPolynomial (ι ⊕ κ) k) := by
      rw [← C_mul, mul_inv_cancel₀ hc, C_1]
    rw [subductionLiftExpr_def, map_mul, rename_C, map_sub, neg_mul, mul_sub, ← mul_assoc, hinv,
      one_mul]
    ring
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_le.2 ?_)
  · rintro _ ⟨l, rfl⟩
    have hc : m.leadingCoeff (r l) ≠ 0 := m.leadingCoeff_ne_zero_iff.2 (hr l)
    have hmem : rename Sum.inl (P l) - m.subductionLiftExpr Q r l ∈
        Ideal.span (Set.range fun l ↦ rename Sum.inl (P l) - m.subductionLiftExpr Q r l) :=
      Ideal.subset_span ⟨l, rfl⟩
    have hmul := Ideal.mul_mem_left _ (-C (m.leadingCoeff (r l))⁻¹) hmem
    rwa [hrel l, ← mul_assoc, neg_mul_neg, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at hmul
  · rintro _ ⟨l, rfl⟩
    dsimp only
    rw [hrel l]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩)

/-- The presentation kernel of the enlarged family `Sum.elim b (m.monicNormalize ∘ r)` is the sum
of the renamed presentation kernel of `b` and the kernel of `m.subductionRetract P Q r`. -/
theorem ker_aeval_sumElim_monicNormalize
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) :
    RingHom.ker (aeval (Sum.elim b (m.monicNormalize ∘ r))) =
      (RingHom.ker (aeval b)).map (rename Sum.inl) ⊔ RingHom.ker (m.subductionRetract P Q r) := by
  refine le_antisymm (fun p hp ↦ ?_) (sup_le ?_ ?_)
  · have hp' : m.subductionRetract P Q r p ∈ RingHom.ker (aeval b) := by
      rwa [RingHom.mem_ker, ← AlgHom.comp_apply, m.aeval_comp_subductionRetract hs]
    have hdecomp : p = rename Sum.inl (m.subductionRetract P Q r p) +
        (p - rename Sum.inl (m.subductionRetract P Q r p)) := by ring
    rw [hdecomp]
    refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hp') ?_
    rw [RingHom.mem_ker, map_sub, m.subductionRetract_rename_inl, sub_self]
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, aeval_rename, Sum.elim_comp_inl]
    exact hp
  · intro p hp
    rw [RingHom.mem_ker, ← m.aeval_comp_subductionRetract hs, AlgHom.comp_apply,
      RingHom.mem_ker.1 hp, map_zero]

/-- Mapping the presentation kernel of `Sum.elim b (m.monicNormalize ∘ r)` along
`m.subductionRetract P Q r` recovers the presentation kernel of `b`. -/
theorem map_subductionRetract_ker_aeval
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) :
    (RingHom.ker (aeval (Sum.elim b (m.monicNormalize ∘ r)))).map (m.subductionRetract P Q r) =
      RingHom.ker (aeval b) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun p hp ↦ ?_) fun p hp ↦ ?_
  · rwa [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, m.aeval_comp_subductionRetract hs]
  · rw [← m.subductionRetract_rename_inl (P := P) (Q := Q) (r := r) p]
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, aeval_rename, Sum.elim_comp_inl]
    exact hp

end SubductionRetract

section FairCompletion

variable {σ k : Type*} [Field k]

/-- A sequence of indexed families `c n : ι n → MvPolynomial σ k` is a *fair SAGBI completion
sequence* for the monomial order `m` if every generator is monic, each stage retains the previous
generators inside the same generated subalgebra, and for every stage `n` there is a binomial
generating set `S` of `TauCeti.toricIdeal k (m.degree ∘ c n)` each of whose binomials is subducted
at some stage `N ≥ n`, with `m.monicNormalize r` appearing in `Set.range (c M)` at some stage
`M ≥ N` whenever the remainder `r` is nonzero. -/
structure IsFairSAGBISequence (m : MonomialOrder σ)
    {ι : ℕ → Type*} (c : ∀ n, ι n → MvPolynomial σ k) : Prop where
  /-- Every generator at every stage is monic. -/
  monic : ∀ n i, m.Monic (c n i)
  /-- Each stage contains all generators of the preceding stage. -/
  range_subset : ∀ n, Set.range (c n) ⊆ Set.range (c (n + 1))
  /-- Generators of stage `n + 1` belong to the subalgebra generated at stage `n`. -/
  subset_adjoin : ∀ n, Set.range (c (n + 1)) ⊆ Algebra.adjoin k (Set.range (c n))
  /-- Every stage's toric ideal admits a binomial generating set whose members are all eventually
  subducted, with any nonzero normalized remainders adjoined at a subsequent stage. -/
  fair : ∀ n, ∃ S : Set ((ι n →₀ ℕ) × (ι n →₀ ℕ)),
    TauCeti.toricIdeal k (fun i ↦ m.degree (c n i)) =
      Ideal.span ((fun p : (ι n →₀ ℕ) × (ι n →₀ ℕ) ↦
        monomial p.1 (1 : k) - monomial p.2 1) '' S) ∧
    ∀ p ∈ S, ∃ N ≥ n, ∃ M ≥ N, ∃ Q r,
      m.IsSubduction (c N) (aeval (c n) (monomial p.1 (1 : k) - monomial p.2 1)) Q r ∧
      (r ≠ 0 → m.monicNormalize r ∈ Set.range (c M))

namespace IsFairSAGBISequence

variable {m : MonomialOrder σ} {ι : ℕ → Type*} {c : ∀ n, ι n → MvPolynomial σ k}

/-- Every stage of a fair SAGBI completion sequence generates the same `k`-subalgebra as stage
`0`. -/
theorem adjoin_eq (h : m.IsFairSAGBISequence c) (n : ℕ) :
    Algebra.adjoin k (Set.range (c n)) = Algebra.adjoin k (Set.range (c 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact (le_antisymm (Algebra.adjoin_le (h.subset_adjoin n))
      (Algebra.adjoin_mono (h.range_subset n))).trans ih

/-- Generator ranges are monotone in the stage index. -/
theorem range_subset_of_le (h : m.IsFairSAGBISequence c) {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂) :
    Set.range (c n₁) ⊆ Set.range (c n₂) := by
  induction hle with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact ih.trans (h.range_subset _)

/-- Any earlier stage reindexes into any later stage. -/
theorem exists_comp_eq_of_le (h : m.IsFairSAGBISequence c) {n₁ n₂ : ℕ} (hle : n₁ ≤ n₂) :
    ∃ τ : ι n₁ → ι n₂, c n₂ ∘ τ = c n₁ := by
  have hmem : ∀ i, ∃ j, c n₂ j = c n₁ i :=
    fun i ↦ h.range_subset_of_le hle (Set.mem_range_self i)
  choose τ hτ using hmem
  exact ⟨τ, funext hτ⟩

/-- Once a toric binomial of stage `n` has been subducted at stage `N ≥ n` and any nonzero
normalized remainder lies in `Set.range (c M)` (`M ≥ N`), it admits a bounded zero-subduction
expression in stage `M`. -/
private theorem exists_aeval_eq_support_lt_of_isSubduction (h : m.IsFairSAGBISequence c)
    {n N M : ℕ} (hNM : N ≤ M) {u v : ι n →₀ ℕ}
    (huv : Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) u =
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) v)
    {Q : MvPolynomial (ι N) k} {r : MvPolynomial σ k}
    (hs : m.IsSubduction (c N) (aeval (c n) (monomial u (1 : k) - monomial v 1)) Q r)
    (hr : r ≠ 0 → m.monicNormalize r ∈ Set.range (c M)) :
    ∃ Q' : MvPolynomial (ι M) k,
      aeval (c M) Q' = aeval (c n) (monomial u (1 : k) - monomial v 1) ∧
      ∀ w ∈ Q'.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) w ≺[m]
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) u := by
  classical
  set f := aeval (c n) (monomial u (1 : k) - monomial v 1)
  rcases m.aeval_monomial_sub_monomial_eq_zero_or_degree_lt (h.monic n) u v
      (by simpa [Function.comp_def] using huv) with hf0 | hflt
  · exact ⟨0, by simp [f, hf0], by simp⟩
  obtain ⟨τ, hτ⟩ := h.exists_comp_eq_of_le hNM
  have hdegτ : (fun i ↦ m.degree (c M i)) ∘ τ = fun i ↦ m.degree (c N i) := by
    funext i
    exact congrArg m.degree (congrFun hτ i)
  rcases eq_or_ne r 0 with rfl | hr0
  · refine ⟨rename τ Q, ?_, fun w hw ↦ ?_⟩
    · rw [aeval_rename, hτ, hs.eq_aeval_add, add_zero]
    · obtain ⟨u₀, rfl, hu₀⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 hw)
      rw [Finsupp.linearCombination_mapDomain, hdegτ]
      exact (hs.support_le u₀ (mem_support_iff.2 hu₀)).trans_lt hflt
  · obtain ⟨i_r, hir⟩ := hr hr0
    refine ⟨rename τ Q + C (m.leadingCoeff r) * X i_r, ?_, fun w hw ↦ ?_⟩
    · rw [map_add, map_mul, aeval_rename, hτ, aeval_C, algebraMap_eq, aeval_X, hir,
        C_leadingCoeff_mul_monicNormalize, ← hs.eq_aeval_add]
    · rcases Finset.mem_union.1 (support_add hw) with hw | hw
      · obtain ⟨u₀, rfl, hu₀⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 hw)
        rw [Finsupp.linearCombination_mapDomain, hdegτ]
        exact (hs.support_le u₀ (mem_support_iff.2 hu₀)).trans_lt hflt
      · rw [X, C_mul_monomial, mul_one] at hw
        rw [Finset.mem_singleton.1 (support_monomial_subset hw), Finsupp.linearCombination_single,
          one_smul, hir, degree_monicNormalize]
        exact hs.degree_le.trans_lt hflt

/-- Decompose the top-weight component `weightedHomogeneousComponent a δ P` as a homogeneous
combination of the binomial generators `S` of `toricIdeal k a` when `(aeval (c n) P).coeff δ = 0`.
-/
private theorem exists_finsupp_sum_mul_toricIdeal_eq_weightedHomogeneousComponent
    (h : m.IsFairSAGBISequence c) {n : ℕ} {S : Set ((ι n →₀ ℕ) × (ι n →₀ ℕ))}
    (hS : TauCeti.toricIdeal k (fun i ↦ m.degree (c n i)) =
      Ideal.span ((fun p : (ι n →₀ ℕ) × (ι n →₀ ℕ) ↦
        monomial p.1 (1 : k) - monomial p.2 1) '' S))
    {P : MvPolynomial (ι n) k} {δ : σ →₀ ℕ}
    (hPδ : ∀ w ∈ P.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) w ≼[m] δ)
    (hδ : (aeval (c n) P).coeff δ = 0) :
    ∃ g : S →₀ MvPolynomial (ι n) k,
      (g.sum fun j q ↦ q * (monomial j.1.1 (1 : k) - monomial j.1.2 1)) =
        weightedHomogeneousComponent (fun i ↦ m.degree (c n i)) δ P ∧
      ∀ j, ∀ x ∈ (g j).support,
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) x +
          Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) j.1.1 = δ := by
  classical
  set a := fun i ↦ m.degree (c n i)
  have hβ (p : S) :
      (monomial p.1.1 (1 : k) - monomial p.1.2 1).IsWeightedHomogeneous a
        (Finsupp.linearCombination ℕ a p.1.1) := by
    have hmem : monomial p.1.1 (1 : k) - monomial p.1.2 1 ∈ TauCeti.toricIdeal k a := by
      rw [hS]
      exact Ideal.subset_span ⟨p.1, p.2, rfl⟩
    have huv := TauCeti.monomial_sub_monomial_mem_toricIdeal_iff.1 hmem
    have hA (w : ι n →₀ ℕ) : Finsupp.weight a w = Finsupp.linearCombination ℕ a w := by
      rw [Finsupp.weight_apply, Finsupp.linearCombination_apply]
    exact (isWeightedHomogeneous_monomial _ _ _ (hA _)).sub
      (isWeightedHomogeneous_monomial _ _ _ ((hA _).trans huv.symm))
  have hspan : TauCeti.toricIdeal k a =
      Ideal.span (Set.range fun p : S ↦ monomial p.1.1 (1 : k) - monomial p.1.2 1) := by
    rw [hS]
    congr 1
    ext q
    simp
  obtain ⟨g, hgP₀, hgA⟩ := exists_finsupp_sum_mul_eq_weightedHomogeneousComponent hβ
    (hspan ▸ weightedHomogeneousComponent_mem_toricIdeal (h.monic n) hPδ hδ) δ
  rw [weightedHomogeneousComponent_eq_self
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)] at hgP₀
  refine ⟨g, hgP₀, fun j x hx ↦ ?_⟩
  simpa [Finsupp.weight_apply, Finsupp.linearCombination_apply] using hgA j x hx

/-- Support-weight bound for the lifted expression replacing the top-weight component of `P` by
bounded zero-subductions `Q'M p`. -/
private theorem linearCombination_stageLift_lt {n M : ℕ} {S : Set ((ι n →₀ ℕ) × (ι n →₀ ℕ))}
    {P : MvPolynomial (ι n) k} {δ : σ →₀ ℕ} {g : S →₀ MvPolynomial (ι n) k}
    {Q'M : S → MvPolynomial (ι M) k} {τ₀ : ι n → ι M} (hτ₀ : c M ∘ τ₀ = c n)
    (hPδ : ∀ w ∈ P.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) w ≼[m] δ)
    (hgA : ∀ j, ∀ x ∈ (g j).support,
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) x +
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) j.1.1 = δ)
    (hQ'Mlt : ∀ p ∈ g.support, ∀ y ∈ (Q'M p).support,
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) y ≺[m]
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) p.1.1)
    {w : ι M →₀ ℕ}
    (hw : w ∈ (rename τ₀ (P - weightedHomogeneousComponent (fun i ↦ m.degree (c n i)) δ P) +
      g.sum fun p q ↦ rename τ₀ q * Q'M p).support) :
    Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) w ≺[m] δ := by
  classical
  set a := fun i ↦ m.degree (c n i)
  have hdegτ₀ (u : ι n →₀ ℕ) :
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) (u.mapDomain τ₀) =
        Finsupp.linearCombination ℕ a u := by
    have hcomp : ((fun i ↦ m.degree (c M i)) ∘ τ₀) = a :=
      funext fun i ↦ congrArg m.degree (congrFun hτ₀ i)
    rw [Finsupp.linearCombination_mapDomain, hcomp]
  rcases Finset.mem_union.1 (support_add hw) with hw | hw
  · obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 hw)
    rw [hdegτ₀]
    have huδ : Finsupp.linearCombination ℕ a u ≠ δ := by
      intro heq
      rw [Finsupp.linearCombination_apply] at heq
      simp [coeff_weightedHomogeneousComponent, Finsupp.weight_apply, heq] at hu
    have huP : u ∈ P.support := mem_support_iff.2 fun h0 ↦ by
      simp [coeff_weightedHomogeneousComponent, h0] at hu
    exact lt_of_le_of_ne (hPδ u huP) fun heq ↦ huδ (m.toSyn.injective heq)
  · obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.1 (support_sum hw)
    obtain ⟨x', hx', y, hy, rfl⟩ := Finset.mem_add.1 (support_mul _ _ hwp)
    obtain ⟨x, rfl, hx⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 hx')
    rw [map_add, hdegτ₀, ← hgA p x (mem_support_iff.2 hx), map_add, map_add]
    exact add_lt_add_right (hQ'Mlt p hp y hy) _

/-- **Top-weight reduction across completion stages.** If `P` at stage `n` has all `c n`-weights
at most `δ` and `(aeval (c n) P).coeff δ = 0`, fairness produces a later stage `M ≥ n` and a
representation `P'` of the same polynomial whose `c M`-weights are strictly below `δ`. -/
private theorem exists_stage_aeval_eq_support_lt (h : m.IsFairSAGBISequence c)
    {n : ℕ} {P : MvPolynomial (ι n) k} {δ : σ →₀ ℕ}
    (hPδ : ∀ w ∈ P.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) w ≼[m] δ)
    (hδ : (aeval (c n) P).coeff δ = 0) :
    ∃ M ≥ n, ∃ P' : MvPolynomial (ι M) k,
      aeval (c M) P' = aeval (c n) P ∧
      ∀ w ∈ P'.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) w ≺[m] δ := by
  classical
  set a := fun i ↦ m.degree (c n i)
  obtain ⟨S, hS, hfair⟩ := h.fair n
  obtain ⟨g, hgP₀, hgA⟩ :=
    h.exists_finsupp_sum_mul_toricIdeal_eq_weightedHomogeneousComponent hS hPδ hδ
  have hsub (p : S) : ∃ (M : ℕ) (Q' : MvPolynomial (ι M) k),
      aeval (c M) Q' = aeval (c n) (monomial p.1.1 (1 : k) - monomial p.1.2 1) ∧
      ∀ w ∈ Q'.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) w ≺[m]
        Finsupp.linearCombination ℕ a p.1.1 := by
    obtain ⟨N, -, M, hNM, Q, r, hs, hr⟩ := hfair p.1 p.2
    have huv : Finsupp.linearCombination ℕ a p.1.1 = Finsupp.linearCombination ℕ a p.1.2 :=
      (TauCeti.monomial_sub_monomial_mem_toricIdeal_iff (R := k)).1
        (hS ▸ Ideal.subset_span ⟨p.1, p.2, rfl⟩)
    obtain ⟨Q', hQ'c, hQ'lt⟩ := h.exists_aeval_eq_support_lt_of_isSubduction hNM huv hs hr
    exact ⟨M, Q', hQ'c, hQ'lt⟩
  choose Mfn Qfn hQfnc hQfnlt using hsub
  set M := n ⊔ g.support.sup Mfn
  have hnM : n ≤ M := le_sup_left
  obtain ⟨τ₀, hτ₀⟩ := h.exists_comp_eq_of_le hnM
  have hτp (p : S) (hp : p ∈ g.support) : ∃ τ : ι (Mfn p) → ι M, c M ∘ τ = c (Mfn p) :=
    h.exists_comp_eq_of_le ((Finset.le_sup hp).trans le_sup_right)
  let Q'M (p : S) : MvPolynomial (ι M) k :=
    if hp : p ∈ g.support then rename (Classical.choose (hτp p hp)) (Qfn p) else 0
  refine ⟨M, hnM, rename τ₀ (P - weightedHomogeneousComponent a δ P) +
      g.sum (fun p q ↦ rename τ₀ q * Q'M p), ?_,
      fun w ↦ linearCombination_stageLift_lt hτ₀ hPδ hgA (fun p hp y hy ↦ ?_)⟩
  · have hsum : (aeval (c M)) (g.sum fun p q ↦ rename τ₀ q * Q'M p) =
        aeval (c n) (weightedHomogeneousComponent a δ P) := by
      rw [← hgP₀, map_finsuppSum, map_finsuppSum, Finsupp.sum, Finsupp.sum]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hτeq := Classical.choose_spec (hτp p hp)
      simp only [Q'M, hp, ↓reduceDIte, map_mul, aeval_rename]
      rw [hτ₀, hτeq, hQfnc p]
    rw [map_add, aeval_rename, hτ₀, hsum, ← map_add, sub_add_cancel]
  · simp only [Q'M, hp, ↓reduceDIte] at hy
    obtain ⟨y₀, rfl, hy₀⟩ := coeff_rename_ne_zero _ _ _ (mem_support_iff.1 hy)
    have hcomp : ((fun i ↦ m.degree (c M i)) ∘ Classical.choose (hτp p hp)) =
        fun i ↦ m.degree (c (Mfn p) i) :=
      funext fun i ↦ congrArg m.degree (congrFun (Classical.choose_spec (hτp p hp)) i)
    rw [Finsupp.linearCombination_mapDomain, hcomp]
    exact hQfnlt p y₀ (mem_support_iff.2 hy₀)

/-- **Exhaustion of leading exponents.** In any fair SAGBI completion sequence, the leading
exponent of every nonzero element of the generated subalgebra eventually lies in the additive
submonoid generated by the leading exponents of some stage `N`. No finiteness hypothesis on the
variables, generators, or initial algebra is required. -/
theorem exists_degree_mem_closure (h : m.IsFairSAGBISequence c)
    {f : MvPolynomial σ k} (hf : f ∈ Algebra.adjoin k (Set.range (c 0))) (hf0 : f ≠ 0) :
    ∃ N : ℕ, m.degree f ∈ AddSubmonoid.closure (Set.range fun i ↦ m.degree (c N i)) := by
  classical
  have key : ∀ (δ : σ →₀ ℕ) (n : ℕ) (P : MvPolynomial (ι n) k),
      aeval (c n) P = f →
      (∀ w ∈ P.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) w ≼[m] δ) →
      ∃ N : ℕ, m.degree f ∈ AddSubmonoid.closure (Set.range fun i ↦ m.degree (c N i)) := by
    intro δ
    induction hd : m.toSyn δ using WellFoundedLT.induction generalizing δ with
    | ind d ih =>
      subst hd
      intro n P hPf hPδ
      by_cases htop : (aeval (c n) P).coeff δ = 0
      · obtain ⟨M, -, P', hP'P, hlt⟩ := h.exists_stage_aeval_eq_support_lt hPδ htop
        have hP'f : aeval (c M) P' = f := hP'P.trans hPf
        have hne : P'.support.Nonempty :=
          support_nonempty.2 fun h0 ↦ hf0 (by rw [← hP'f, h0, map_zero])
        obtain ⟨w₀, hw₀, hmax⟩ := Finset.exists_max_image _
          (fun w ↦ m.toSyn (Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) w)) hne
        exact ih _ (hlt w₀ hw₀) _ rfl M P' hP'f hmax
      · have hdeg : m.degree f = δ := by
          rw [← hPf]
          exact m.toSyn.injective <| le_antisymm (degree_aeval_le_of_forall_le hPδ)
            (m.le_degree (mem_support_iff.2 htop))
        rw [coeff_aeval_of_forall_le (h.monic n) hPδ] at htop
        obtain ⟨w, hw, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero htop
        refine ⟨n, ?_⟩
        rw [hdeg, ← (Finset.mem_filter.1 hw).2]
        exact AddSubmonoid.mem_closure_range_iff.2 ⟨w, Finsupp.linearCombination_apply ℕ w⟩
  rw [Algebra.adjoin_range_eq_range_aeval] at hf
  obtain ⟨P, hP⟩ := hf
  have hne : P.support.Nonempty := support_nonempty.2 fun h0 ↦ hf0 (by rw [← hP, h0, map_zero])
  obtain ⟨w₀, -, hmax⟩ := Finset.exists_max_image _
    (fun w ↦ m.toSyn (Finsupp.linearCombination ℕ (fun i ↦ m.degree (c 0 i)) w)) hne
  exact key _ 0 P hP hmax

/-- For any fair SAGBI completion sequence, the supremum over all stages of the monoids generated
by the stages' leading exponents is the full leading-exponent monoid of `k[c 0]`. -/
theorem iSup_closure_degree_eq_leadingExponents (h : m.IsFairSAGBISequence c) :
    (⨆ n, AddSubmonoid.closure (Set.range fun i ↦ m.degree (c n i))) =
      m.leadingExponents (Algebra.adjoin k (Set.range (c 0))) := by
  refine le_antisymm (iSup_le fun n ↦ AddSubmonoid.closure_le.2 ?_) fun a ha ↦ ?_
  · rintro _ ⟨i, rfl⟩
    refine degree_mem_leadingExponents ?_ (h.monic n i).ne_zero
    rw [← h.adjoin_eq n]
    exact Algebra.subset_adjoin ⟨i, rfl⟩
  · obtain ⟨f, hf, hf0, rfl⟩ := mem_leadingExponents_iff.1 ha
    obtain ⟨N, hN⟩ := h.exists_degree_mem_closure hf hf0
    exact le_iSup (fun n ↦ AddSubmonoid.closure (Set.range fun i ↦ m.degree (c n i))) N hN

/-- For any fair SAGBI completion sequence, the supremum over all stages of the leading-term
subalgebras is the full initial algebra of `k[c 0]`. -/
theorem iSup_adjoin_leadingTerm_eq_initialAlgebra (h : m.IsFairSAGBISequence c) :
    (⨆ n, Algebra.adjoin k (m.leadingTerm '' Set.range (c n))) =
      m.initialAlgebra (Algebra.adjoin k (Set.range (c 0))) := by
  refine le_antisymm (iSup_le fun n ↦ ?_) ?_
  · refine adjoin_leadingTerm_le_initialAlgebra ?_
    rw [← h.adjoin_eq n]
    exact Algebra.subset_adjoin
  · rw [initialAlgebra_def, Algebra.adjoin_le_iff]
    rintro _ ⟨f, hf, rfl⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · simp
    obtain ⟨N, hN⟩ := h.exists_degree_mem_closure hf hf0
    refine le_iSup (fun n ↦ Algebra.adjoin k (m.leadingTerm '' Set.range (c n))) N ?_
    refine leadingTerm_mem_adjoin_leadingTerm_iff.2 (AddSubmonoid.closure_mono ?_ hN)
    rintro _ ⟨i, rfl⟩
    exact ⟨c N i, ⟨⟨i, rfl⟩, (h.monic N i).ne_zero⟩, rfl⟩

/-- **Termination of fair SAGBI completion.** If the monoid of leading exponents of `k[c 0]` is
finitely generated, every fair SAGBI completion sequence `c` reaches a stage `N` from which
onward every `Set.range (c M)` (`M ≥ N`) is a SAGBI basis of `k[c 0]`. -/
theorem exists_isSAGBIBasis_of_fg (h : m.IsFairSAGBISequence c)
    (hfg : (m.leadingExponents (Algebra.adjoin k (Set.range (c 0)))).FG) :
    ∃ N : ℕ, ∀ M ≥ N,
      m.IsSAGBIBasis (Set.range (c M)) (Algebra.adjoin k (Set.range (c 0))) := by
  classical
  obtain ⟨E, hE⟩ := AddSubmonoid.isAddFG_iff.1 hfg
  have hex : ∀ e : E, ∃ n : ℕ,
      (e : σ →₀ ℕ) ∈ AddSubmonoid.closure (Set.range fun i ↦ m.degree (c n i)) := by
    intro e
    have he : (e : σ →₀ ℕ) ∈ m.leadingExponents (Algebra.adjoin k (Set.range (c 0))) :=
      hE ▸ AddSubmonoid.subset_closure e.2
    obtain ⟨f, hf, hf0, hfe⟩ := mem_leadingExponents_iff.1 he
    obtain ⟨n, hn⟩ := h.exists_degree_mem_closure hf hf0
    exact ⟨n, hfe ▸ hn⟩
  choose Nfn hNfn using hex
  refine ⟨E.attach.sup Nfn,
    fun M hM ↦ isSAGBIBasis_iff_degree_mem_closure.2 ⟨?_, fun f hf hf0 ↦ ?_⟩⟩
  · rw [← h.adjoin_eq M]
    exact Algebra.subset_adjoin
  · have hsub : (E : Set (σ →₀ ℕ)) ⊆
        AddSubmonoid.closure (m.degree '' (Set.range (c M) \ {0})) := by
      intro e he
      have hle : Nfn ⟨e, he⟩ ≤ M := (Finset.le_sup (Finset.mem_attach _ ⟨e, he⟩)).trans hM
      refine AddSubmonoid.closure_mono ?_ (hNfn ⟨e, he⟩)
      rintro _ ⟨i, rfl⟩
      exact ⟨c (Nfn ⟨e, he⟩) i,
        ⟨h.range_subset_of_le hle ⟨i, rfl⟩, (h.monic _ i).ne_zero⟩, rfl⟩
    exact (AddSubmonoid.closure_le.2 hsub) (hE ▸ degree_mem_leadingExponents hf hf0)

/-- Fair SAGBI completion terminates whenever the full initial algebra of `k[c 0]` is finitely
generated as a `k`-algebra. -/
theorem exists_isSAGBIBasis_of_fg_initialAlgebra (h : m.IsFairSAGBISequence c)
    (hfg : (m.initialAlgebra (Algebra.adjoin k (Set.range (c 0)))).FG) :
    ∃ N : ℕ, ∀ M ≥ N,
      m.IsSAGBIBasis (Set.range (c M)) (Algebra.adjoin k (Set.range (c 0))) :=
  h.exists_isSAGBIBasis_of_fg (fg_initialAlgebra_iff_fg_leadingExponents.1 hfg)

/-- For a fair SAGBI completion sequence of finite families, some stage is a SAGBI basis of
`k[c 0]` if and only if the leading-exponent monoid of `k[c 0]` is finitely generated. -/
theorem exists_isSAGBIBasis_iff_fg_leadingExponents [∀ n, Finite (ι n)]
    (h : m.IsFairSAGBISequence c) :
    (∃ N : ℕ, m.IsSAGBIBasis (Set.range (c N)) (Algebra.adjoin k (Set.range (c 0)))) ↔
      (m.leadingExponents (Algebra.adjoin k (Set.range (c 0)))).FG := by
  refine ⟨fun ⟨N, hN⟩ ↦ hN.fg_leadingExponents (Set.finite_range (c N)), fun hfg ↦ ?_⟩
  obtain ⟨N, hN⟩ := h.exists_isSAGBIBasis_of_fg hfg
  exact ⟨N, hN N le_rfl⟩

/-- For a fair SAGBI completion sequence of finite families, some stage is a SAGBI basis of
`k[c 0]` if and only if the full initial algebra of `k[c 0]` is finitely generated. -/
theorem exists_isSAGBIBasis_iff_fg_initialAlgebra [∀ n, Finite (ι n)]
    (h : m.IsFairSAGBISequence c) :
    (∃ N : ℕ, m.IsSAGBIBasis (Set.range (c N)) (Algebra.adjoin k (Set.range (c 0)))) ↔
      (m.initialAlgebra (Algebra.adjoin k (Set.range (c 0)))).FG :=
  h.exists_isSAGBIBasis_iff_fg_leadingExponents.trans
    fg_initialAlgebra_iff_fg_leadingExponents.symm

end IsFairSAGBISequence

end FairCompletion

section BatchCompletion

universe u

variable {σ k : Type*} [Field k] {ι₀ : Type u} [Finite ι₀]

private theorem exists_toricBinomials (m : MonomialOrder σ) {ι : Type u} [Finite ι]
    (c : ι → MvPolynomial σ k) :
    ∃ B : Finset ((ι →₀ ℕ) × (ι →₀ ℕ)),
      TauCeti.toricIdeal k (fun i ↦ m.degree (c i)) =
        Ideal.span ((fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦
          monomial p.1 (1 : k) - monomial p.2 1) '' (B : Set _)) := by
  obtain ⟨B, -, hB⟩ := TauCeti.exists_finset_toricIdeal_eq_span fun i ↦ m.degree (c i)
  exact ⟨B, hB k⟩

/-- Chosen finite binomial generating set of the toric ideal of `m.degree ∘ c`. -/
private noncomputable def chosenToricBinomials (m : MonomialOrder σ) {ι : Type u} [Finite ι]
    (c : ι → MvPolynomial σ k) : Finset ((ι →₀ ℕ) × (ι →₀ ℕ)) :=
  (m.exists_toricBinomials c).choose

private theorem chosenToricBinomials_span (m : MonomialOrder σ) {ι : Type u} [Finite ι]
    (c : ι → MvPolynomial σ k) :
    TauCeti.toricIdeal k (fun i ↦ m.degree (c i)) =
      Ideal.span ((fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦
        monomial p.1 (1 : k) - monomial p.2 1) '' (m.chosenToricBinomials c : Set _)) :=
  (m.exists_toricBinomials c).choose_spec

/-- Chosen subduction expression and remainder for `f` with respect to `c`, defaulting to `(0, 0)`
if `c` were ever to contain a zero polynomial. -/
private noncomputable def chosenSubductionPair (m : MonomialOrder σ) {ι : Type u}
    (c : ι → MvPolynomial σ k) (f : MvPolynomial σ k) :
    MvPolynomial ι k × MvPolynomial σ k :=
  open scoped Classical in
  if hc : ∀ i, c i ≠ 0 then
    ((m.exists_isSubduction hc f).choose, (m.exists_isSubduction hc f).choose_spec.choose)
  else (0, 0)

private theorem chosenSubductionPair_spec (m : MonomialOrder σ) {ι : Type u}
    {c : ι → MvPolynomial σ k} (hc : ∀ i, c i ≠ 0) (f : MvPolynomial σ k) :
    m.IsSubduction c f (m.chosenSubductionPair c f).1 (m.chosenSubductionPair c f).2 := by
  unfold chosenSubductionPair
  split_ifs
  exact (m.exists_isSubduction hc f).choose_spec.choose_spec

/-- Internal stage package for concrete certified batch SAGBI completion. -/
private structure BatchStage (c₀ : ι₀ → MvPolynomial σ k) where
  Idx : Type u
  instFinite : Finite Idx
  family : Idx → MvPolynomial σ k
  retract : MvPolynomial Idx k →ₐ[k] MvPolynomial ι₀ k

/-- One batch completion step: subduct all chosen toric-ideal binomial generators of the current
stage, adjoin the monic normalizations of all nonzero remainders, and compose the presentation
retraction with `m.subductionRetract`. -/
private noncomputable def nextBatchStage (m : MonomialOrder σ) {c₀ : ι₀ → MvPolynomial σ k}
    (S : BatchStage c₀) : BatchStage c₀ :=
  haveI : Finite S.Idx := S.instFinite
  let B := m.chosenToricBinomials S.family
  let sub (p : B) :=
    m.chosenSubductionPair S.family (aeval S.family (monomial p.1.1 (1 : k) - monomial p.1.2 1))
  let κ := {p : B // (sub p).2 ≠ 0}
  { Idx := S.Idx ⊕ κ
    instFinite := inferInstance
    family := Sum.elim S.family (m.monicNormalize ∘ fun l ↦ (sub l.1).2)
    retract := S.retract.comp
      (m.subductionRetract (fun l : κ ↦ monomial l.1.1.1 (1 : k) - monomial l.1.1.2 1)
        (fun l ↦ (sub l.1).1) (fun l ↦ (sub l.1).2)) }

private noncomputable def batchStageSeq (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k) :
    ℕ → BatchStage c₀
  | 0 => ⟨ι₀, inferInstance, c₀, AlgHom.id k (MvPolynomial ι₀ k)⟩
  | n + 1 => m.nextBatchStage (m.batchStageSeq c₀ n)

/-- The finite index type of stage `n` of batch SAGBI completion starting from `c₀`. -/
noncomputable def sagbiCompletionIndex (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : Type u :=
  (m.batchStageSeq c₀ n).Idx

/-- Every stage index type `m.sagbiCompletionIndex c₀ n` is finite when `ι₀` is finite. -/
instance instFiniteSagbiCompletionIndex (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : Finite (m.sagbiCompletionIndex c₀ n) :=
  (m.batchStageSeq c₀ n).instFinite

/-- The generator family at stage `n` of batch SAGBI completion starting from `c₀`. -/
noncomputable def sagbiCompletionFamily (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : m.sagbiCompletionIndex c₀ n → MvPolynomial σ k :=
  (m.batchStageSeq c₀ n).family

/-- The surjective presentation retraction from stage `n` of batch SAGBI completion back to the
initial polynomial ring `MvPolynomial ι₀ k`. -/
noncomputable def sagbiCompletionRetract (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : MvPolynomial (m.sagbiCompletionIndex c₀ n) k →ₐ[k] MvPolynomial ι₀ k :=
  (m.batchStageSeq c₀ n).retract

variable {m : MonomialOrder σ} {c₀ : ι₀ → MvPolynomial σ k}

/-- Stage `0` of `m.sagbiCompletionFamily c₀` has the same generator set `Set.range c₀`. -/
@[simp]
theorem range_sagbiCompletionFamily_zero (c₀ : ι₀ → MvPolynomial σ k) :
    Set.range (m.sagbiCompletionFamily c₀ 0) = Set.range c₀ :=
  Set.ext fun _ ↦ Iff.rfl

/-- Every generator at every stage of `m.sagbiCompletionFamily c₀` is monic when `c₀` is monic. -/
theorem monic_sagbiCompletionFamily (hc₀ : ∀ i, m.Monic (c₀ i)) (n : ℕ)
    (i : m.sagbiCompletionIndex c₀ n) :
    m.Monic (m.sagbiCompletionFamily c₀ n i) := by
  induction n with
  | zero => exact hc₀ i
  | succ n ih =>
    cases i with
    | inl j => exact ih j
    | inr l => exact m.monic_monicNormalize l.2

private theorem sagbiCompletionStep_isSubduction (hc₀ : ∀ i, m.Monic (c₀ i)) (n : ℕ)
    (l : {p : m.chosenToricBinomials (m.sagbiCompletionFamily c₀ n) //
      (m.chosenSubductionPair (m.sagbiCompletionFamily c₀ n)
        (aeval (m.sagbiCompletionFamily c₀ n) (monomial p.1.1 (1 : k) - monomial p.1.2 1))).2 ≠
          0}) :
    m.IsSubduction (m.sagbiCompletionFamily c₀ n)
      (aeval (m.sagbiCompletionFamily c₀ n) (monomial l.1.1.1 (1 : k) - monomial l.1.1.2 1))
      (m.chosenSubductionPair (m.sagbiCompletionFamily c₀ n)
        (aeval (m.sagbiCompletionFamily c₀ n) (monomial l.1.1.1 (1 : k) - monomial l.1.1.2 1))).1
      (m.chosenSubductionPair (m.sagbiCompletionFamily c₀ n)
        (aeval (m.sagbiCompletionFamily c₀ n)
          (monomial l.1.1.1 (1 : k) - monomial l.1.1.2 1))).2 :=
  m.chosenSubductionPair_spec (fun i ↦ (m.monic_sagbiCompletionFamily hc₀ n i).ne_zero) _

/-- Every stage's presentation retraction `m.sagbiCompletionRetract c₀ n` is surjective. -/
theorem sagbiCompletionRetract_surjective (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    Function.Surjective (m.sagbiCompletionRetract c₀ n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp subductionRetract_surjective

/-- Evaluating `c₀` after `m.sagbiCompletionRetract c₀ n` equals evaluating stage `n` of
`m.sagbiCompletionFamily c₀`. -/
theorem aeval_comp_sagbiCompletionRetract (hc₀ : ∀ i, m.Monic (c₀ i)) (n : ℕ) :
    (aeval c₀).comp (m.sagbiCompletionRetract c₀ n) = aeval (m.sagbiCompletionFamily c₀ n) := by
  induction n with
  | zero => exact AlgHom.comp_id (aeval c₀)
  | succ n ih =>
    exact (AlgHom.comp_assoc _ _ _).symm.trans
      ((congrArg (AlgHom.comp · _) ih).trans
        (m.aeval_comp_subductionRetract (m.sagbiCompletionStep_isSubduction hc₀ n)))

/-- Mapping the presentation kernel of stage `n` along `m.sagbiCompletionRetract c₀ n` recovers
the presentation kernel of `c₀`. -/
theorem map_sagbiCompletionRetract_ker_aeval (hc₀ : ∀ i, m.Monic (c₀ i)) (n : ℕ) :
    (RingHom.ker (aeval (m.sagbiCompletionFamily c₀ n))).map (m.sagbiCompletionRetract c₀ n) =
      RingHom.ker (aeval c₀) := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun p hp ↦ ?_) fun p hp ↦ ?_
  · rwa [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply,
      m.aeval_comp_sagbiCompletionRetract hc₀ n]
  · obtain ⟨q, rfl⟩ := m.sagbiCompletionRetract_surjective c₀ n p
    refine Ideal.mem_map_of_mem _ ?_
    rwa [RingHom.mem_ker, ← m.aeval_comp_sagbiCompletionRetract hc₀ n, AlgHom.comp_apply]

/-- Batch toric-binomial completion starting from a finite monic family `c₀` is a fair SAGBI
completion sequence. -/
theorem isFairSAGBISequence_sagbiCompletionFamily (hc₀ : ∀ i, m.Monic (c₀ i)) :
    m.IsFairSAGBISequence (m.sagbiCompletionFamily c₀) where
  monic := m.monic_sagbiCompletionFamily hc₀
  range_subset n := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  subset_adjoin n := by
    have hadj : Algebra.adjoin k (Set.range (m.sagbiCompletionFamily c₀ (n + 1))) =
        Algebra.adjoin k (Set.range (m.sagbiCompletionFamily c₀ n)) :=
      m.adjoin_range_sumElim_monicNormalize (m.sagbiCompletionStep_isSubduction hc₀ n)
    rw [← hadj]
    exact Algebra.subset_adjoin
  fair n := by
    refine ⟨(m.chosenToricBinomials (m.sagbiCompletionFamily c₀ n) : Set _),
      m.chosenToricBinomials_span _, fun p hp ↦ ?_⟩
    let pB : m.chosenToricBinomials (m.sagbiCompletionFamily c₀ n) := ⟨p, hp⟩
    let sub := m.chosenSubductionPair (m.sagbiCompletionFamily c₀ n)
      (aeval (m.sagbiCompletionFamily c₀ n) (monomial p.1 (1 : k) - monomial p.2 1))
    refine ⟨n, le_rfl, n + 1, Nat.le_succ n, sub.1, sub.2,
      m.chosenSubductionPair_spec (fun i ↦ (m.monic_sagbiCompletionFamily hc₀ n i).ne_zero) _,
      fun hr ↦ ⟨Sum.inr ⟨pB, hr⟩, rfl⟩⟩

/-- **Certified finite SAGBI completion of a finite nonzero family.** Let
`b : ι₀ → MvPolynomial σ k` be a finite family of nonzero polynomials whose generated subalgebra
`k[b]` has finitely generated leading-exponent monoid. Normalizing `b`, running fair batch
completion to termination, and composing the presentation retraction with
`MvPolynomial.rescale (m.leadingCoeff ∘ b)⁻¹` yields a finite monic SAGBI basis
`c : κ → MvPolynomial σ k` of `k[b]` and a surjective `k`-algebra retraction
`φ : MvPolynomial κ k →ₐ[k] MvPolynomial ι₀ k` with `(aeval b).comp φ = aeval c` and
`(RingHom.ker (aeval c)).map φ = RingHom.ker (aeval b)`. -/
theorem exists_finite_monic_isSAGBIBasis_of_fg {b : ι₀ → MvPolynomial σ k}
    (hb : ∀ i, b i ≠ 0)
    (hfg : (m.leadingExponents (Algebra.adjoin k (Set.range b))).FG) :
    ∃ (κ : Type u) (_ : Finite κ) (c : κ → MvPolynomial σ k)
      (φ : MvPolynomial κ k →ₐ[k] MvPolynomial ι₀ k),
      (∀ l, m.Monic (c l)) ∧
      m.IsSAGBIBasis (Set.range c) (Algebra.adjoin k (Set.range b)) ∧
      Function.Surjective φ ∧
      (aeval b).comp φ = aeval c ∧
      (RingHom.ker (aeval c)).map φ = RingHom.ker (aeval b) := by
  let c₀ : ι₀ → MvPolynomial σ k := m.monicNormalize ∘ b
  have hc₀ : ∀ i, m.Monic (c₀ i) := fun i ↦ m.monic_monicNormalize (hb i)
  have hadj : Algebra.adjoin k (Set.range c₀) = Algebra.adjoin k (Set.range b) := by
    rw [Set.range_comp, adjoin_image_monicNormalize]
  obtain ⟨N, hN⟩ := (m.isFairSAGBISequence_sagbiCompletionFamily hc₀).exists_isSAGBIBasis_of_fg
    (hadj.symm ▸ hfg)
  let Dinv : MvPolynomial ι₀ k →ₐ[k] MvPolynomial ι₀ k :=
    rescale fun i ↦ (m.leadingCoeff (b i))⁻¹
  have hDinv_surj : Function.Surjective Dinv := by
    intro p
    have hmul_one : ((fun i ↦ m.leadingCoeff (b i)) * fun i ↦ (m.leadingCoeff (b i))⁻¹) = 1 :=
      funext fun i ↦ mul_inv_cancel₀ (m.leadingCoeff_ne_zero_iff.2 (hb i))
    exact ⟨rescale (fun i ↦ m.leadingCoeff (b i)) p, by simp [Dinv, rescale_rescale, hmul_one]⟩
  have haeval_Dinv : (aeval b).comp Dinv = aeval c₀ := by
    refine algHom_ext fun i ↦ ?_
    simp [c₀, Dinv, monicNormalize_def]
  let φ := Dinv.comp (m.sagbiCompletionRetract c₀ N)
  have hφ_surj : Function.Surjective φ := hDinv_surj.comp (m.sagbiCompletionRetract_surjective c₀ N)
  have hφ_comp : (aeval b).comp φ = aeval (m.sagbiCompletionFamily c₀ N) := by
    rw [← AlgHom.comp_assoc, haeval_Dinv, m.aeval_comp_sagbiCompletionRetract hc₀ N]
  refine ⟨m.sagbiCompletionIndex c₀ N, inferInstance, m.sagbiCompletionFamily c₀ N, φ,
    m.monic_sagbiCompletionFamily hc₀ N, ?_, hφ_surj, hφ_comp, ?_⟩
  · have hN0 := hN N le_rfl
    rwa [m.range_sagbiCompletionFamily_zero, hadj] at hN0
  · refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun p hp ↦ ?_) fun p hp ↦ ?_
    · rwa [Ideal.mem_comap, RingHom.mem_ker, ← AlgHom.comp_apply, hφ_comp]
    · obtain ⟨q, rfl⟩ := hφ_surj p
      refine Ideal.mem_map_of_mem _ ?_
      rwa [RingHom.mem_ker, ← hφ_comp, AlgHom.comp_apply]

end BatchCompletion

end MonomialOrder

namespace TauCeti

open MonomialOrder

section RobbianoSweedlerInfinite

/-- For the lexicographic order on `Fin 2 →₀ ℕ`, `Finsupp.single 1 1 ≺[lex] Finsupp.single 0 1`
(`X 1 ≺[lex] X 0`). -/
private theorem single_one_lt_single_zero_lex :
    Finsupp.single (1 : Fin 2) 1 ≺[lex] Finsupp.single 0 1 := by
  rw [lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨0, fun j hj ↦ (Fin.not_lt_zero j hj).elim, ?_⟩
  simp

private theorem coeff_X_zero_add_X_one_single_zero {R : Type*} [CommSemiring R] :
    (X 0 + X 1 : MvPolynomial (Fin 2) R).coeff (Finsupp.single 0 1) = 1 := by
  classical
  have hne : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single 0 1 :=
    ne_of_apply_ne (fun f ↦ f 0) (by simp)
  rw [X, X]
  simp [hne]

private theorem degree_X_zero_add_X_one {R : Type*} [CommSemiring R] [Nontrivial R] :
    lex.degree (X 0 + X 1 : MvPolynomial (Fin 2) R) = Finsupp.single 0 1 := by
  classical
  have hcoeff : (X 0 + X 1 : MvPolynomial (Fin 2) R).coeff (Finsupp.single 0 1) = 1 :=
    coeff_X_zero_add_X_one_single_zero
  refine lex.toSyn.injective (le_antisymm (lex.degree_le_iff.2 fun u hu ↦ ?_)
    (lex.le_degree (mem_support_iff.2 (hcoeff.symm ▸ one_ne_zero))))
  rcases Finset.mem_union.1 (support_add hu) with hu | hu
  · rw [X] at hu
    rw [Finset.mem_singleton.1 (support_monomial_subset hu)]
  · rw [X] at hu
    rw [Finset.mem_singleton.1 (support_monomial_subset hu)]
    exact single_one_lt_single_zero_lex.le

private theorem monic_X_zero_add_X_one {R : Type*} [CommSemiring R] [Nontrivial R] :
    lex.Monic (X 0 + X 1 : MvPolynomial (Fin 2) R) := by
  rw [Monic, leadingCoeff, degree_X_zero_add_X_one, coeff_X_zero_add_X_one_single_zero]

private theorem X_zero_mul_X_one_pow_eq_monomial {R : Type*} [CommSemiring R] (m : ℕ) :
    (X 0 * X 1 ^ m : MvPolynomial (Fin 2) R) =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 m) 1 := by
  rw [X, X, monomial_pow, monomial_mul_monomial, one_pow, mul_one, Finsupp.smul_single,
    smul_eq_mul, mul_one]

private theorem degree_X_zero_mul_X_one_pow {R : Type*} [CommSemiring R] [Nontrivial R] (m : ℕ) :
    lex.degree (X 0 * X 1 ^ m : MvPolynomial (Fin 2) R) =
      Finsupp.single 0 1 + Finsupp.single 1 m := by
  classical
  rw [X_zero_mul_X_one_pow_eq_monomial, degree_monomial]
  simp

private theorem monic_X_zero_mul_X_one_pow {R : Type*} [CommSemiring R] [Nontrivial R] (m : ℕ) :
    lex.Monic (X 0 * X 1 ^ m : MvPolynomial (Fin 2) R) := by
  classical
  rw [Monic, leadingCoeff, degree_X_zero_mul_X_one_pow, X_zero_mul_X_one_pow_eq_monomial,
    coeff_monomial]
  simp

/-- Explicit stage `n` (`Fin (n + 3) → MvPolynomial (Fin 2) R`) of one-relation-at-a-time
completion on `robbianoSweedlerSubalgebra R`: index `0` is `X 0 + X 1`, and index `i > 0` is
`X 0 * X 1 ^ (i : ℕ)`. -/
noncomputable def robbianoSweedlerStage (R : Type*) [CommSemiring R] (n : ℕ) (i : Fin (n + 3)) :
    MvPolynomial (Fin 2) R :=
  if (i : ℕ) = 0 then X 0 + X 1 else X 0 * X 1 ^ (i : ℕ)

/-- Stage `0` of `robbianoSweedlerStage R` coincides with the initial generator family
`robbianoSweedlerGen R`. -/
@[simp]
theorem robbianoSweedlerStage_zero_eq (R : Type*) [CommSemiring R] :
    robbianoSweedlerStage R 0 = robbianoSweedlerGen R := by
  funext i
  fin_cases i <;> simp [robbianoSweedlerStage]

/-- Every generator at stage `n` of `robbianoSweedlerStage R` is `lex`-monic over a nontrivial
commutative semiring. -/
theorem monic_robbianoSweedlerStage {R : Type*} [CommSemiring R] [Nontrivial R]
    (n : ℕ) (i : Fin (n + 3)) : lex.Monic (robbianoSweedlerStage R n i) := by
  by_cases hi : (i : ℕ) = 0 <;>
    simp [robbianoSweedlerStage, hi, monic_X_zero_add_X_one, monic_X_zero_mul_X_one_pow]

/-- All three initial generators of `robbianoSweedlerGen R` are `lex`-monic over a nontrivial
commutative semiring. -/
theorem monic_robbianoSweedlerGen {R : Type*} [CommSemiring R] [Nontrivial R] (i : Fin 3) :
    lex.Monic (robbianoSweedlerGen R i) := by
  rw [← robbianoSweedlerStage_zero_eq]
  exact monic_robbianoSweedlerStage 0 i

/-- The `lex`-leading exponent of the `i`-th generator of `robbianoSweedlerStage R n` is `(1, i)`.
-/
theorem degree_robbianoSweedlerStage {R : Type*} [CommSemiring R] [Nontrivial R]
    (n : ℕ) (i : Fin (n + 3)) :
    lex.degree (robbianoSweedlerStage R n i) =
      Finsupp.single 0 1 + Finsupp.single 1 (i : ℕ) := by
  by_cases hi : (i : ℕ) = 0 <;>
    simp [robbianoSweedlerStage, hi, degree_X_zero_add_X_one, degree_X_zero_mul_X_one_pow]

/-- The toric binomial `Y 0 * Y (n + 2) - Y 1 * Y (n + 1)` at stage `n` of
`robbianoSweedlerStage`. -/
noncomputable def robbianoSweedlerBinomial (R : Type*) [CommRing R] (n : ℕ) :
    MvPolynomial (Fin (n + 3)) R :=
  monomial (Finsupp.single 0 1 + Finsupp.single ⟨n + 2, by omega⟩ 1) 1 -
    monomial (Finsupp.single ⟨1, by omega⟩ 1 + Finsupp.single ⟨n + 1, by omega⟩ 1) 1

/-- `robbianoSweedlerBinomial R n` belongs to the toric ideal of the leading exponents of
`robbianoSweedlerStage R n` (both monomials have common leading exponent `(2, n + 2)`). -/
theorem robbianoSweedlerBinomial_mem_toricIdeal {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    robbianoSweedlerBinomial R n ∈
      TauCeti.toricIdeal R (fun i ↦ lex.degree (robbianoSweedlerStage R n i)) := by
  refine TauCeti.monomial_sub_monomial_mem_toricIdeal ?_
  simp only [map_add, Finsupp.linearCombination_single, one_smul, degree_robbianoSweedlerStage]
  ext d
  fin_cases d <;> simp; omega

/-- Evaluating `robbianoSweedlerBinomial R n` at `robbianoSweedlerStage R n` yields the next
monomial `X 0 * X 1 ^ (n + 3)`. -/
theorem aeval_robbianoSweedlerStage_binomial {R : Type*} [CommRing R] (n : ℕ) :
    aeval (robbianoSweedlerStage R n) (robbianoSweedlerBinomial R n) =
      (X 0 * X 1 ^ (n + 3) : MvPolynomial (Fin 2) R) := by
  have hmul (a b : Fin (n + 3)) :
      aeval (robbianoSweedlerStage R n)
        (monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : R)) =
        robbianoSweedlerStage R n a * robbianoSweedlerStage R n b := by
    have hmon : (monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : R)) =
        monomial (Finsupp.single a 1) 1 * monomial (Finsupp.single b 1) 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [hmon, map_mul, aeval_monomial, aeval_monomial, map_one, one_mul, one_mul,
      Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), pow_one, pow_one]
  rw [robbianoSweedlerBinomial, map_sub, hmul, hmul]
  have h0 : robbianoSweedlerStage R n 0 = X 0 + X 1 := by simp [robbianoSweedlerStage]
  have hlast : robbianoSweedlerStage R n ⟨n + 2, by omega⟩ = X 0 * X 1 ^ (n + 2) := by
    simp [robbianoSweedlerStage]
  have h1 : robbianoSweedlerStage R n ⟨1, by omega⟩ = X 0 * X 1 := by
    simp [robbianoSweedlerStage]
  have hprev : robbianoSweedlerStage R n ⟨n + 1, by omega⟩ = X 0 * X 1 ^ (n + 1) := by
    simp [robbianoSweedlerStage]
  rw [h0, hlast, h1, hprev]
  exact robbianoSweedler_step_identity (n + 1)

/-- At every stage `n` over a nontrivial commutative ring, the toric binomial
`robbianoSweedlerBinomial R n` subducts with zero quotient expression `Q = 0` and nonzero
irreducible remainder `X 0 * X 1 ^ (n + 3)`. -/
theorem isSubduction_robbianoSweedlerStage {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    lex.IsSubduction (robbianoSweedlerStage R n)
      (aeval (robbianoSweedlerStage R n) (robbianoSweedlerBinomial R n))
      0 (X 0 * X 1 ^ (n + 3)) := by
  have hbound : ∀ x ∈ AddSubmonoid.closure
      (Set.range (lex.degree ∘ robbianoSweedlerStage R n)), x 1 ≤ (n + 2) * x 0 := by
    intro x hx
    induction hx using AddSubmonoid.closure_induction with
    | mem _ ha =>
      obtain ⟨i, rfl⟩ := ha
      simp only [Function.comp_apply, degree_robbianoSweedlerStage, Finsupp.coe_add, Pi.add_apply,
        Finsupp.single_eq_same, Finsupp.single_eq_of_ne Fin.zero_ne_one,
        Finsupp.single_eq_of_ne Fin.zero_ne_one.symm, add_zero, zero_add, mul_one]
      omega
    | zero => simp
    | add _ _ _ _ ihx ihy =>
      simp only [Finsupp.coe_add, Pi.add_apply, mul_add]
      omega
  refine ⟨by simp [aeval_robbianoSweedlerStage_binomial], by simp, fun a ha hmem ↦ ?_,
    by simp [aeval_robbianoSweedlerStage_binomial]⟩
  rw [X_zero_mul_X_one_pow_eq_monomial] at ha
  have ha' := Finset.mem_singleton.1 (support_monomial_subset ha)
  have hle := hbound a hmem
  rw [ha'] at hle
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne Fin.zero_ne_one, Finsupp.single_eq_of_ne Fin.zero_ne_one.symm,
    add_zero, zero_add, mul_one] at hle
  omega

section Field

variable {k : Type*} [Field k]

/-- No stage of batch SAGBI completion starting from `robbianoSweedlerGen k` is a `lex`-SAGBI
basis of `robbianoSweedlerSubalgebra k`: without finite generation of the initial algebra,
certified completion runs forever even on a three-generator subalgebra of `k[X 0, X 1]`. -/
theorem not_isSAGBIBasis_sagbiCompletionFamily_robbianoSweedler (n : ℕ) :
    ¬ lex.IsSAGBIBasis (Set.range (lex.sagbiCompletionFamily (robbianoSweedlerGen k) n))
      (robbianoSweedlerSubalgebra k) := by
  intro hB
  exact not_fg_leadingExponents_robbianoSweedler (hB.fg_leadingExponents (Set.finite_range _))

/-- Stage `n + 1` of `robbianoSweedlerStage k` is obtained from stage `n` by adjoining the monic
normalization of the nonzero remainder `X 0 * X 1 ^ (n + 3)`. -/
theorem range_robbianoSweedlerStage_succ (n : ℕ) :
    Set.range (robbianoSweedlerStage k (n + 1)) =
      insert (lex.monicNormalize (X 0 * X 1 ^ (n + 3)))
        (Set.range (robbianoSweedlerStage k n)) := by
  rw [(monic_X_zero_mul_X_one_pow (R := k) (n + 3)).monicNormalize_eq]
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · right
      exact ⟨j, by simp [robbianoSweedlerStage]⟩
    · left
      simp [robbianoSweedlerStage]
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last (n + 3), by simp [robbianoSweedlerStage]⟩
    · exact ⟨j.castSucc, by simp [robbianoSweedlerStage]⟩

/-- The leading-term subalgebras of `robbianoSweedlerStage k n` form an infinite strictly
ascending chain of completion steps inside `lex.initialAlgebra (robbianoSweedlerSubalgebra k)`. -/
theorem adjoin_leadingTerm_robbianoSweedlerStage_lt (n : ℕ) :
    Algebra.adjoin k (lex.leadingTerm '' Set.range (robbianoSweedlerStage k n)) <
      Algebra.adjoin k (lex.leadingTerm '' Set.range (robbianoSweedlerStage k (n + 1))) := by
  rw [range_robbianoSweedlerStage_succ]
  exact (isSubduction_robbianoSweedlerStage (R := k) n).adjoin_leadingTerm_lt
    (monic_X_zero_mul_X_one_pow (R := k) (n + 3)).ne_zero

end Field

end RobbianoSweedlerInfinite

end TauCeti
