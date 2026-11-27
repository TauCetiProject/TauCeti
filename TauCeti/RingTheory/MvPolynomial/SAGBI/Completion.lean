/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Adjoin.FG
public import TauCeti.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Criterion
public import TauCeti.RingTheory.MvPolynomial.SAGBI.Finite
import Mathlib.Basic.Finite.Sum
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.Algebra.MvPolynomial.Rename

/-!
# Certified SAGBI completion and termination

Let `m` be a monomial order on `σ →₀ ℕ` and `k` a field. SAGBI completion enlarges a generating
set or family of a subalgebra `A = k[G]` until it becomes a SAGBI basis of `A`. Unlike Buchberger
completion for ideals (`MonomialOrder.exists_sPolynomialStep_completion`), SAGBI completion for
subalgebras faces two structural subtleties:

1. Adjoining a nonzero subduction remainder `r` of an element `f` (such as `aeval b P`) normalizes
   `r` to `m.monicNormalize r = C (m.leadingCoeff r)⁻¹ * r` and records the scalar
   `m.leadingCoeff r` (and its inverse) in the presentation maps relating the old and enlarged
   generator families (`MonomialOrder.IsSubduction.monicNormalize_eq_aeval`,
   `MonomialOrder.subductionRetract`, `MonomialOrder.subductionLiftExpr`).
2. Submonoids of `σ →₀ ℕ` need not satisfy the ascending chain condition (it can fail even for
   two variables), so strictly enlarging the leading-term algebra at each step does not by itself
   force finite-stage stabilization or eventual basisness—even when the full initial algebra is
   finitely generated, an unfair selection of relations could neglect a needed generator forever,
   and without finite generation of the initial algebra completion may run forever even on a
   finitely generated subalgebra (see `TauCeti.RingTheory.MvPolynomial.SAGBI.RobbianoSweedler` for
   the formalized `k[x + y, xy, xy^2]` counterexample).

This file provides two complementary formalizations of SAGBI completion:

* **Single-step set completion** (`MonomialOrder.SubductionStep`): each step subducts a polynomial
  `f` by the current generating set `G` and adjoins `m.monicNormalize r` if `r ≠ 0`, preserving
  `k[G]` when `f ∈ k[G]`, strictly enlarging the leading-term algebra on nontrivial adjunction,
  and yielding a bounded expression for `f`. Starting from a monic generating set `G 0` and
  processing elements `f n ∈ k[G n]`, under fairness on binomial generating families of the stage
  toric ideals, the union of stages is a SAGBI basis
  (`MonomialOrder.isSAGBIBasis_iUnion_of_subductionStep`), and if in addition
  `(m.initialAlgebra (Algebra.adjoin k (G 0))).FG` then some finite stage stabilizes at a SAGBI
  basis (`MonomialOrder.exists_isSAGBIBasis_of_subductionStep`).
* **Presentation-tracked and batch completion** (`MonomialOrder.subductionRetract`,
  `MonomialOrder.IsFairSAGBISequence`, `MonomialOrder.sagbiCompletionFamily`): develops the
  `k`-algebra presentation retractions across normalized remainder adjunctions; proves
  unconditional exhaustion of leading exponents and initial algebras for general fair indexed
  completion sequences (in which each stage-`n` toric-ideal generator is evaluated in stage `n`'s
  family and subducted at a possibly different stage `N`, with any nonzero remainder adjoined at
  some stage `M ≥ N`, allowing batch adjunction of multiple remainders); proves eventual-basis
  attainment (every sufficiently late stage is a SAGBI basis, though arbitrary generator families
  may keep growing) under finite generation of the leading-exponent monoid of `k[c 0]`, indexed
  termination (bijectivity of all sufficiently late stage inclusions) when every newly adjoined
  index is certified by a nonzero subduction remainder
  (`MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_and_bijective_of_fg`), and
  characterizes finite-stage basis attainment for finite stage families by that finite-generation
  condition; constructs the concrete batch completion sequence `MonomialOrder.sagbiCompletionFamily`
  with surjective presentation retractions `MonomialOrder.sagbiCompletionRetract`, proving batch
  fairness (`MonomialOrder.isFairSAGBISequence_sagbiCompletionFamily`) and termination
  (`MonomialOrder.exists_isSAGBIBasis_and_bijective_sagbiCompletionIndexInclusion_of_fg`) for
  finite monic initial families `c₀`; and, distinct from that monic-start fairness theorem, for any
  finite nonzero family `b` whose leading-exponent monoid
  `(m.leadingExponents (Algebra.adjoin k (Set.range b))).FG` is finitely generated (via prior
  monic normalization), deduces existence of a finite monic SAGBI basis `c` of `k[b]` together
  with a surjective presentation homomorphism `φ` satisfying `(aeval b).comp φ = aeval c`
  (`MonomialOrder.exists_finite_monic_isSAGBIBasis_of_fg`).

## Main results

* `MonomialOrder.exists_subductionStep`, `MonomialOrder.SubductionStep.adjoin_eq`,
  `MonomialOrder.SubductionStep.adjoin_leadingTerm_lt`, and
  `MonomialOrder.SubductionStep.exists_aeval_eq`: existence and properties of single-element
  subduction completion steps.
* `MonomialOrder.isSAGBIBasis_iUnion_of_subductionStep`: unconditional convergence of the union
  for fair runs of `SubductionStep` starting from monic generators with `f n ∈ k[G n]`.
* `MonomialOrder.exists_isSAGBIBasis_of_subductionStep`: finite-stage stabilization for such fair
  runs under `(m.initialAlgebra (Algebra.adjoin k (G 0))).FG`.
* `MonomialOrder.subductionRetract`, `MonomialOrder.subductionLiftExpr`,
  `MonomialOrder.aeval_comp_subductionRetract`,
  `MonomialOrder.ker_subductionRetract_eq_span_of_ne_zero`, and
  `MonomialOrder.ker_aeval_sumElim_monicNormalize`: factorization of evaluation and presentation
  kernels across normalized remainder adjunction.
* `MonomialOrder.IsFairSAGBISequence.iSup_closure_degree_eq_leadingExponents` and
  `MonomialOrder.IsFairSAGBISequence.iSup_adjoin_leadingTerm_eq_initialAlgebra`: unconditional
  exhaustion of leading exponents and initial algebras for fair indexed completion sequences.
* `MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_of_fg`,
  `MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_and_bijective_of_fg`, and
  `MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_iff_fg_leadingExponents`: eventual-basis
  attainment under `(m.leadingExponents (Algebra.adjoin k (Set.range (c 0)))).FG`, indexed
  termination (bijectivity of late stage inclusions) when new indices are certified by nonzero
  subduction remainders, and characterization of finite-stage SAGBI-basis attainment for finite
  stage families by finite generation of the leading-exponent monoid.
* `MonomialOrder.sagbiCompletionFamily`, `MonomialOrder.sagbiCompletionRetract`,
  `MonomialOrder.exists_sagbiCompletion_succ`,
  `MonomialOrder.isFairSAGBISequence_sagbiCompletionFamily`,
  `MonomialOrder.exists_isSAGBIBasis_and_bijective_sagbiCompletionIndexInclusion_of_fg`, and
  `MonomialOrder.exists_finite_monic_isSAGBIBasis_of_fg`: concrete certified batch completion
  (with batch fairness and stage-inclusion bijectivity proved for finite monic initial families)
  and, distinct from that, for any finite nonzero family whose leading-exponent monoid is finitely
  generated, existence of a finite monic SAGBI basis with a surjective presentation map.

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

namespace MonomialOrder

open MvPolynomial

section SingleStep

variable {σ k : Type*} [Field k] {m : MonomialOrder σ}

variable (m) in
/-- A step of SAGBI completion processing `f`: subduct `f` by the members of `G`, and adjoin the
monic normalization of the remainder `r` if `r ≠ 0`. The new set `H` is the first argument. -/
def SubductionStep (f : MvPolynomial σ k) (H G : Set (MvPolynomial σ k)) : Prop :=
  ∃ (Q : MvPolynomial G k) (r : MvPolynomial σ k),
    m.IsSubduction ((↑) : G → MvPolynomial σ k) f Q r ∧
      (r = 0 ∧ H = G ∨ r ≠ 0 ∧ H = insert (m.monicNormalize r) G)

/-- The subduction and adjunction certificate of a completion step. -/
theorem subductionStep_iff {f : MvPolynomial σ k} {H G : Set (MvPolynomial σ k)} :
    m.SubductionStep f H G ↔
      ∃ (Q : MvPolynomial G k) (r : MvPolynomial σ k),
        m.IsSubduction ((↑) : G → MvPolynomial σ k) f Q r ∧
          (r = 0 ∧ H = G ∨ r ≠ 0 ∧ H = insert (m.monicNormalize r) G) :=
  Iff.rfl

namespace SubductionStep

variable {f : MvPolynomial σ k} {G H : Set (MvPolynomial σ k)}

/-- A subduction with zero remainder gives a completion step which adjoins nothing. -/
theorem of_remainder_eq_zero {Q : MvPolynomial G k}
    (h : m.IsSubduction ((↑) : G → MvPolynomial σ k) f Q 0) : m.SubductionStep f G G :=
  ⟨Q, 0, h, Or.inl ⟨rfl, rfl⟩⟩

/-- A subduction with nonzero remainder `r` gives a completion step which adjoins the monic
normalization of `r`. -/
theorem of_remainder_ne_zero {Q : MvPolynomial G k} {r : MvPolynomial σ k}
    (h : m.IsSubduction ((↑) : G → MvPolynomial σ k) f Q r) (hr : r ≠ 0) :
    m.SubductionStep f (insert (m.monicNormalize r) G) G :=
  ⟨Q, r, h, Or.inr ⟨hr, rfl⟩⟩

end SubductionStep

/-- Every polynomial can be processed by a completion step, provided the current generators are
nonzero. -/
theorem exists_subductionStep {G : Set (MvPolynomial σ k)} (hG : ∀ g ∈ G, g ≠ 0)
    (f : MvPolynomial σ k) : ∃ H, m.SubductionStep f H G := by
  classical
  obtain ⟨Q, r, h⟩ := m.exists_isSubduction (b := ((↑) : G → MvPolynomial σ k))
    (fun g ↦ hG g g.property) f
  by_cases hr : r = 0
  · exact ⟨G, .of_remainder_eq_zero (hr ▸ h)⟩
  · exact ⟨_, .of_remainder_ne_zero h hr⟩

private theorem linearCombination_degree_rename_eq_of_comp {σ ι μ R : Type*} [CommSemiring R]
    {m : MonomialOrder σ} {b : ι → MvPolynomial σ R} {c : μ → MvPolynomial σ R}
    {τ : ι → μ} (hτ : c ∘ τ = b) {P : MvPolynomial ι R} {w : μ →₀ ℕ}
    (hw : w ∈ (rename τ P).support) :
    ∃ u ∈ P.support,
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) w =
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) u := by
  have hcomp : (fun i ↦ m.degree (c i)) ∘ τ = fun i ↦ m.degree (b i) :=
    funext fun i ↦ congrArg m.degree (congrFun hτ i)
  exact linearCombination_rename_eq_of_comp hcomp hw

private theorem aeval_rename_add_C_mul_X {σ ι μ k : Type*} [Field k] {m : MonomialOrder σ}
    {b : ι → MvPolynomial σ k} {c : μ → MvPolynomial σ k}
    {τ : ι → μ} (hτ : c ∘ τ = b) {i_r : μ} {f : MvPolynomial σ k}
    {Q : MvPolynomial ι k} {r : MvPolynomial σ k}
    (hs : m.IsSubduction b f Q r) (hir : c i_r = m.monicNormalize r) :
    aeval c (rename τ Q + C (m.leadingCoeff r) * X i_r) = f := by
  rw [hs.eq_aeval_add]
  simp [hτ, hir, aeval_rename, C_leadingCoeff_mul_monicNormalize]

private theorem linearCombination_rename_add_C_mul_X_le {σ ι μ k : Type*} [Field k]
    {m : MonomialOrder σ} {b : ι → MvPolynomial σ k} {c : μ → MvPolynomial σ k}
    {τ : ι → μ} (hτ : c ∘ τ = b) {i_r : μ} {f : MvPolynomial σ k}
    {Q : MvPolynomial ι k} {r : MvPolynomial σ k}
    (hs : m.IsSubduction b f Q r) (hir : c i_r = m.monicNormalize r)
    {w : μ →₀ ℕ} (hw : w ∈ (rename τ Q + C (m.leadingCoeff r) * X i_r).support) :
    Finsupp.linearCombination ℕ (fun i ↦ m.degree (c i)) w ≼[m] m.degree f := by
  classical
  rcases Finset.mem_union.1 (support_add hw) with hw | hw
  · obtain ⟨u, hu, heq⟩ := linearCombination_degree_rename_eq_of_comp hτ hw
    rw [heq]
    exact hs.support_le u hu
  · rw [X, C_mul_monomial, mul_one] at hw
    rw [Finset.mem_singleton.1 (support_monomial_subset hw), Finsupp.linearCombination_single,
      one_smul, hir, degree_monicNormalize]
    exact hs.degree_le

namespace SubductionStep

variable {f : MvPolynomial σ k} {G H : Set (MvPolynomial σ k)}

/-- A completion step only adds generators. -/
theorem subset (h : m.SubductionStep f H G) : G ⊆ H := by
  obtain ⟨_, _, _, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := h
  · exact subset_rfl
  · exact Set.subset_insert _ _

/-- Processing an element of the generated algebra does not change that algebra. -/
theorem adjoin_eq (h : m.SubductionStep f H G) (hf : f ∈ Algebra.adjoin k G) :
    Algebra.adjoin k H = Algebra.adjoin k G := by
  obtain ⟨_, _, hs, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := h
  · rfl
  · simpa only [Subtype.range_coe] using
      hs.adjoin_insert_monicNormalize (by simpa only [Subtype.range_coe] using hf)

/-- A completion step keeps a set of generators monic. -/
theorem monic (h : m.SubductionStep f H G) (hG : ∀ g ∈ G, m.Monic g) :
    ∀ g ∈ H, m.Monic g := by
  obtain ⟨_, _, _, ⟨-, rfl⟩ | ⟨hr, rfl⟩⟩ := h
  · exact hG
  · exact Set.forall_mem_insert.2 ⟨monic_monicNormalize hr, hG⟩

/-- A completion step which adjoins a generator strictly enlarges the algebra generated by the
leading terms. -/
theorem adjoin_leadingTerm_lt (h : m.SubductionStep f H G) (hHG : H ≠ G) :
    Algebra.adjoin k (m.leadingTerm '' G) < Algebra.adjoin k (m.leadingTerm '' H) := by
  obtain ⟨_, _, hs, ⟨-, rfl⟩ | ⟨hr, rfl⟩⟩ := h
  · exact absurd rfl hHG
  · simpa only [Subtype.range_coe] using hs.adjoin_leadingTerm_lt hr

/-- Processing an element of `A` by a SAGBI basis of `A` adjoins nothing. -/
theorem eq_of_isSAGBIBasis (h : m.SubductionStep f H G) {A : Subalgebra k (MvPolynomial σ k)}
    (hG : m.IsSAGBIBasis G A) (hf : f ∈ A) : H = G := by
  obtain ⟨_, _, hs, ⟨-, rfl⟩ | ⟨hr, -⟩⟩ := h
  · rfl
  · exact absurd (hs.remainder_eq_zero (by rwa [Subtype.range_coe]) hf) hr

/-- After it is processed, `f` has an expression in the new generators all of whose substituted
monomials have leading exponent at most that of `f`. -/
theorem exists_aeval_eq (h : m.SubductionStep f H G) :
    ∃ P : MvPolynomial H k, aeval ((↑) : H → MvPolynomial σ k) P = f ∧
      ∀ w ∈ P.support,
        Finsupp.linearCombination ℕ (fun g : H ↦ m.degree g.val) w ≼[m] m.degree f := by
  classical
  obtain ⟨Q, r, hs, ⟨rfl, rfl⟩ | ⟨-, rfl⟩⟩ := h
  · exact ⟨Q, by simpa using hs.eq_aeval_add.symm, hs.support_le⟩
  set g := m.monicNormalize r
  refine ⟨rename (Set.inclusion (Set.subset_insert g G)) Q +
    C (m.leadingCoeff r) * X ⟨g, Set.mem_insert g G⟩, ?_, ?_⟩
  · exact aeval_rename_add_C_mul_X (Set.val_comp_inclusion (Set.subset_insert g G)) hs rfl
  · exact fun w hw ↦
      linearCombination_rename_add_C_mul_X_le (Set.val_comp_inclusion (Set.subset_insert g G)) hs
        rfl hw

end SubductionStep

end SingleStep

section SubductionRetract

variable {σ ι κ k : Type*} [Field k] (m : MonomialOrder σ)

/-- The `k`-algebra retraction `MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial ι k` recording a
subduction-remainder adjunction step: original variables `X (.inl i)` map to `X i`, and each
adjoined normalized-remainder variable `X (.inr l)` maps to
`C (m.leadingCoeff (r l))⁻¹ * (P l - Q l)`. -/
noncomputable def subductionRetract (P Q : κ → MvPolynomial ι k) (r : κ → MvPolynomial σ k) :
    MvPolynomial (ι ⊕ κ) k →ₐ[k] MvPolynomial ι k :=
  aeval (Sum.elim X fun l ↦ C (m.leadingCoeff (r l))⁻¹ * (P l - Q l))

/-- The expression `rename Sum.inl (Q l) + C (m.leadingCoeff (r l)) * X (.inr l)` in the enlarged
family `Sum.elim b (m.monicNormalize ∘ r)`, retaining the leading coefficient of `r l` before
normalization. When `(Q l, r l)` is a certified subduction pair for `aeval b (P l)`
(`MonomialOrder.IsSubduction b (aeval b (P l)) (Q l) (r l)`), it evaluates back to `aeval b (P l)`
(`MonomialOrder.aeval_sumElim_subductionLiftExpr`). -/
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
    (m.subductionRetract P Q r).comp (rename Sum.inl) = AlgHom.id k (MvPolynomial ι k) := by
  rw [subductionRetract_def, aeval_comp_rename, Sum.elim_comp_inl, aeval_X_left]

/-- Applying `MonomialOrder.subductionRetract` to a polynomial in the original variables recovers
that polynomial. -/
@[simp]
theorem subductionRetract_rename_inl (p : MvPolynomial ι k) :
    m.subductionRetract P Q r (rename Sum.inl p) = p :=
  AlgHom.congr_fun m.subductionRetract_comp_rename_inl p

/-- `MonomialOrder.subductionRetract` is surjective. -/
theorem subductionRetract_surjective : Function.Surjective (m.subductionRetract P Q r) :=
  Function.LeftInverse.surjective m.subductionRetract_rename_inl

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
      Algebra.adjoin k (Set.range b) :=
  adjoin_range_eq_of_aeval_comp_eq (m.aeval_comp_subductionRetract hs)
    m.subductionRetract_surjective

/-- In the enlarged family `Sum.elim b (m.monicNormalize ∘ r)`, the scalar-retaining expression
`m.subductionLiftExpr Q r l` evaluates back to `aeval b (P l)`. -/
theorem aeval_sumElim_subductionLiftExpr
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) (l : κ) :
    aeval (Sum.elim b (m.monicNormalize ∘ r)) (m.subductionLiftExpr Q r l) = aeval b (P l) :=
  aeval_rename_add_C_mul_X (Sum.elim_comp_inl b (m.monicNormalize ∘ r)) (hs l) rfl

/-- Every exponent in the support of `m.subductionLiftExpr Q r l` has weight at most
`m.degree (aeval b (P l))` with respect to `Sum.elim b (m.monicNormalize ∘ r)`. -/
theorem linearCombination_subductionLiftExpr_le
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) (l : κ)
    {w : ι ⊕ κ →₀ ℕ} (hw : w ∈ (m.subductionLiftExpr Q r l).support) :
    Finsupp.linearCombination ℕ (m.degree ∘ Sum.elim b (m.monicNormalize ∘ r)) w ≼[m]
      m.degree (aeval b (P l)) := by
  rw [subductionLiftExpr_def] at hw
  exact linearCombination_rename_add_C_mul_X_le (Sum.elim_comp_inl b (m.monicNormalize ∘ r))
    (hs l) rfl hw

/-- When every adjoined remainder `r l` is nonzero, clearing `(m.leadingCoeff (r l))⁻¹` identifies
the kernel of `m.subductionRetract P Q r` with the ideal generated by the lifted subduction
equations `rename Sum.inl (P l) - m.subductionLiftExpr Q r l`. -/
theorem ker_subductionRetract_eq_span_of_ne_zero (P Q : κ → MvPolynomial ι k)
    {r : κ → MvPolynomial σ k} (hr : ∀ l, r l ≠ 0) :
    RingHom.ker (m.subductionRetract P Q r) =
      Ideal.span (Set.range fun l ↦ rename Sum.inl (P l) - m.subductionLiftExpr Q r l) := by
  rw [subductionRetract_def, MvPolynomial.ker_aeval_sumElim]
  have hrel (l : κ) :
      rename Sum.inl (P l) - m.subductionLiftExpr Q r l =
        -C (m.leadingCoeff (r l)) *
          (X (Sum.inr l) - rename Sum.inl (C (m.leadingCoeff (r l))⁻¹ * (P l - Q l))) := by
    have hc : m.leadingCoeff (r l) ≠ 0 := m.leadingCoeff_ne_zero_iff.2 (hr l)
    have hinv : C (m.leadingCoeff (r l)) * C (m.leadingCoeff (r l))⁻¹ =
        (1 : MvPolynomial (ι ⊕ κ) k) := by
      rw [← C_mul, mul_inv_cancel₀ hc, C_1]
    calc
      rename Sum.inl (P l) - m.subductionLiftExpr Q r l
        = rename Sum.inl (P l - Q l) - C (m.leadingCoeff (r l)) * X (Sum.inr l) := by
          simp only [subductionLiftExpr_def, map_sub]; ring
      _ = -C (m.leadingCoeff (r l)) * X (Sum.inr l) +
            (C (m.leadingCoeff (r l)) * C (m.leadingCoeff (r l))⁻¹) *
              rename Sum.inl (P l - Q l) := by
          rw [hinv, one_mul]; ring
      _ = -C (m.leadingCoeff (r l)) *
            (X (Sum.inr l) - rename Sum.inl (C (m.leadingCoeff (r l))⁻¹ * (P l - Q l))) := by
          simp only [map_mul, rename_C]; ring
  rw [Ideal.span_range_eq_iSup, Ideal.span_range_eq_iSup]
  refine iSup_congr fun l ↦ ?_
  have hunit : IsUnit (-C (m.leadingCoeff (r l)) : MvPolynomial (ι ⊕ κ) k) :=
    ((m.leadingCoeff_ne_zero_iff.2 (hr l)).isUnit.map C).neg
  rw [hrel l, Ideal.span_singleton_mul_left_unit hunit]

/-- The presentation kernel of the enlarged family `Sum.elim b (m.monicNormalize ∘ r)` is the sum
of the renamed presentation kernel of `b` and the kernel of `m.subductionRetract P Q r`. -/
theorem ker_aeval_sumElim_monicNormalize
    (hs : ∀ l, m.IsSubduction b (aeval b (P l)) (Q l) (r l)) :
    RingHom.ker (aeval (Sum.elim b (m.monicNormalize ∘ r))) =
      (RingHom.ker (aeval b)).map (rename Sum.inl) ⊔ RingHom.ker (m.subductionRetract P Q r) := by
  have hmap : ((RingHom.ker (aeval b)).map (rename (R := k) Sum.inl)).map
      (m.subductionRetract P Q r) = RingHom.ker (aeval b) := by
    rw [Ideal.map_mapₐ, m.subductionRetract_comp_rename_inl]
    exact Ideal.map_id _
  rw [← m.aeval_comp_subductionRetract hs, ← AlgHom.comap_ker]
  conv_lhs => rw [← hmap]
  rw [Ideal.comap_map_of_surjective (m.subductionRetract P Q r) m.subductionRetract_surjective,
    ← RingHom.ker_eq_comap_bot]

end SubductionRetract

section FairCompletion

variable {σ k : Type*} [Field k]

/-- A sequence of indexed families `c n : ι n → MvPolynomial σ k` is a *fair SAGBI completion
sequence* for the monomial order `m` if every generator is monic, each stage retains the previous
generators inside the same generated subalgebra, and for every stage `n` there is a binomial
generating set `S` of `TauCeti.toricIdeal k (m.degree ∘ c n)` such that each binomial in `S` is
evaluated in stage `n`'s family `c n` and subducted at a possibly different stage `N`, with
`m.monicNormalize r` appearing in `Set.range (c M)` at some stage `M ≥ N` whenever the remainder
`r` is nonzero. -/
structure IsFairSAGBISequence (m : MonomialOrder σ)
    {ι : ℕ → Type*} (c : ∀ n, ι n → MvPolynomial σ k) : Prop where
  /-- Every generator at every stage is monic. -/
  monic : ∀ n i, m.Monic (c n i)
  /-- Each stage contains all generators of the preceding stage. -/
  range_subset : ∀ n, Set.range (c n) ⊆ Set.range (c (n + 1))
  /-- Generators of stage `n + 1` belong to the subalgebra generated at stage `n`. -/
  subset_adjoin : ∀ n, Set.range (c (n + 1)) ⊆ Algebra.adjoin k (Set.range (c n))
  /-- Every stage's toric ideal admits a binomial generating set `S` such that each binomial in `S`
  is evaluated in `c n` and subducted at a possibly different stage `N`, with any nonzero
  remainder `r` required to appear (as `m.monicNormalize r`) at some stage `M ≥ N`. -/
  fair : ∀ n, ∃ S : Set ((ι n →₀ ℕ) × (ι n →₀ ℕ)),
    TauCeti.toricIdeal k (fun i ↦ m.degree (c n i)) =
      Ideal.span ((fun p : (ι n →₀ ℕ) × (ι n →₀ ℕ) ↦
        monomial p.1 (1 : k) - monomial p.2 1) '' S) ∧
    ∀ p ∈ S, ∃ N : ℕ, ∃ M ≥ N, ∃ Q r,
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
    Set.range (c n₁) ⊆ Set.range (c n₂) :=
  monotone_nat_of_le_succ h.range_subset hle

/-- Once the evaluation at `c n` of a stage-`n` toric binomial has been subducted against `c N`
and any nonzero normalized remainder lies in `Set.range (c M)` (`M ≥ N`), that evaluation admits a
representation at stage `M` whose `c M`-weights are strictly below the binomial's common weight. -/
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
  obtain ⟨τ, hτ⟩ := Set.range_subset_range_iff_exists_comp.mp (h.range_subset_of_le hNM)
  rcases eq_or_ne r 0 with rfl | hr0
  · refine ⟨rename τ Q, ?_, fun w hw ↦ ?_⟩
    · rw [aeval_rename, ← hτ, hs.eq_aeval_add, add_zero]
    · obtain ⟨u₀, hu₀, heq⟩ := linearCombination_degree_rename_eq_of_comp hτ.symm hw
      rw [heq]
      exact (hs.support_le u₀ hu₀).trans_lt hflt
  · obtain ⟨i_r, hir⟩ := hr hr0
    exact ⟨rename τ Q + C (m.leadingCoeff r) * X i_r,
      aeval_rename_add_C_mul_X hτ.symm hs hir,
      fun w hw ↦ (linearCombination_rename_add_C_mul_X_le hτ.symm hs hir hw).trans_lt hflt⟩

/-- Transport a finite family of stage-wise representations of stage-`n` polynomials to a common
later stage `M ≥ n`, together with the variable inclusion `τ₀ : ι n → ι M`. -/
private theorem exists_common_stage_family (h : m.IsFairSAGBISequence c) {n : ℕ}
    {S : Type*} (s : Finset S) (u v : S → ι n →₀ ℕ)
    (hsub : ∀ p : S, ∃ (M : ℕ) (Q' : MvPolynomial (ι M) k),
      aeval (c M) Q' = aeval (c n) (monomial (u p) (1 : k) - monomial (v p) 1) ∧
      ∀ w ∈ Q'.support, Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) w ≺[m]
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) (u p)) :
    ∃ (M : ℕ) (_ : n ≤ M) (τ₀ : ι n → ι M) (Q'M : S → MvPolynomial (ι M) k),
      c n = c M ∘ τ₀ ∧
      (∀ p ∈ s, aeval (c M) (Q'M p) =
        aeval (c n) (monomial (u p) (1 : k) - monomial (v p) 1)) ∧
      (∀ p ∈ s, ∀ y ∈ (Q'M p).support,
        Finsupp.linearCombination ℕ (fun i ↦ m.degree (c M i)) y ≺[m]
          Finsupp.linearCombination ℕ (fun i ↦ m.degree (c n i)) (u p)) := by
  classical
  choose Mfn Qfn hQfnc hQfnlt using hsub
  set M := n ⊔ s.sup Mfn
  have hnM : n ≤ M := le_sup_left
  obtain ⟨τ₀, hτ₀⟩ := Set.range_subset_range_iff_exists_comp.mp (h.range_subset_of_le hnM)
  have hτp (p : S) (hp : p ∈ s) : ∃ τ : ι (Mfn p) → ι M, c (Mfn p) = c M ∘ τ :=
    Set.range_subset_range_iff_exists_comp.mp
      (h.range_subset_of_le ((Finset.le_sup hp).trans le_sup_right))
  let Q'M (p : S) : MvPolynomial (ι M) k :=
    if hp : p ∈ s then rename (Classical.choose (hτp p hp)) (Qfn p) else 0
  refine ⟨M, hnM, τ₀, Q'M, hτ₀, fun p hp ↦ ?_, fun p hp y hy ↦ ?_⟩
  · have hτeq := Classical.choose_spec (hτp p hp)
    simp only [Q'M, hp, ↓reduceDIte, aeval_rename, ← hτeq, hQfnc p]
  · simp only [Q'M, hp, ↓reduceDIte] at hy
    obtain ⟨y₀, hy₀, heq⟩ :=
      linearCombination_degree_rename_eq_of_comp (Classical.choose_spec (hτp p hp)).symm hy
    rw [heq]
    exact hQfnlt p y₀ hy₀

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
  -- Phase 1: decompose the weight-`δ` component of `P` in the toric ideal of stage `n`.
  obtain ⟨S, hS, hfair⟩ := h.fair n
  have hS' : TauCeti.toricIdeal k a =
      Ideal.span (Set.range fun p : S ↦ monomial p.val.1 (1 : k) - monomial p.val.2 1) := by
    rw [hS, Set.image_eq_range]
  obtain ⟨g, hgP₀, hgA⟩ :=
    exists_finsupp_sum_mul_toricIdeal_eq_weightedHomogeneousComponent (h.monic n) hS' hPδ hδ
  -- Phase 2: obtain bounded stage representations for the binomials in `S` from fairness, then
  -- transport the finite support `g.support` to a common stage `M ≥ n`.
  obtain ⟨M, hnM, τ₀, Q'M, hτ₀, hQ'c, hQ'lt⟩ :=
    h.exists_common_stage_family g.support (fun p : S ↦ p.val.1) (fun p : S ↦ p.val.2) fun p ↦ by
      obtain ⟨N, M, hNM, Q, r, hs, hr⟩ := hfair p.val p.property
      have huv : Finsupp.linearCombination ℕ a p.val.1 = Finsupp.linearCombination ℕ a p.val.2 :=
        TauCeti.linearCombination_eq_of_toricIdeal_eq_span hS' p
      obtain ⟨Q', hQ'c, hQ'lt⟩ := h.exists_aeval_eq_support_lt_of_isSubduction hNM huv hs hr
      exact ⟨M, Q', hQ'c, hQ'lt⟩
  let aM := fun i ↦ m.degree (c M i)
  let g' := g.mapRange (rename τ₀) (map_zero _)
  refine ⟨M, hnM, rename τ₀ (P - weightedHomogeneousComponent a δ P) +
      g.sum (fun p q ↦ rename τ₀ q * Q'M p), ?_, fun w hw ↦ ?_⟩
  · -- Phase 3: verify that replacing the weight-`δ` component by `∑ q * Q'M p` preserves `aeval`.
    have hsum : aeval (c M) (g.sum fun p q ↦ rename τ₀ q * Q'M p) =
        aeval (c n) (weightedHomogeneousComponent a δ P) := by
      rw [← hgP₀, map_finsuppSum, map_finsuppSum, Finsupp.sum, Finsupp.sum]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      rw [map_mul, map_mul, aeval_rename, ← hτ₀, hQ'c p hp]
    rw [map_add, aeval_rename, ← hτ₀, hsum, ← map_add, sub_add_cancel]
  · -- Phase 4: bound all remaining support weights strictly below `δ`.
    have hsub_eq : rename τ₀ (P - weightedHomogeneousComponent a δ P) =
        rename τ₀ P - weightedHomogeneousComponent aM δ (rename τ₀ P) := by
      rw [map_sub, rename_eq_aeval, weightedHomogeneousComponent_aeval (fun i ↦ ?_),
        ← rename_eq_aeval]
      simpa [a, aM, congrFun hτ₀ i] using isWeightedHomogeneous_X k aM (τ₀ i)
    have hsum_eq : (g.sum fun p q ↦ rename τ₀ q * Q'M p) = g'.sum fun p q ↦ q * Q'M p := by
      rw [Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _)]
    rw [hsub_eq, hsum_eq] at hw
    refine linearCombination_sub_weightedHomogeneousComponent_add_sum_lt aM
      (fun p ↦ Finsupp.linearCombination ℕ a p.val.1) ?_ ?_ ?_ hw
    · intro _ hwP
      obtain ⟨u, hu, heq⟩ := linearCombination_degree_rename_eq_of_comp hτ₀.symm hwP
      rw [heq]
      exact hPδ u hu
    · intro p _ x hx
      rw [Finsupp.mapRange_apply] at hx
      obtain ⟨u, hu, heq⟩ := linearCombination_degree_rename_eq_of_comp hτ₀.symm hx
      rw [heq]
      exact hgA p u hu
    · intro p hp y hy
      exact hQ'lt p (Finsupp.support_mapRange hp) y hy

/-- **Exhaustion of leading exponents.** In any fair SAGBI completion sequence, the leading
exponent of every nonzero element of the generated subalgebra eventually lies in the additive
submonoid generated by the leading exponents of some stage `N`. No finiteness hypothesis on the
variables, generators, or initial algebra is required. -/
theorem exists_degree_mem_closure (h : m.IsFairSAGBISequence c)
    {f : MvPolynomial σ k} (hf : f ∈ Algebra.adjoin k (Set.range (c 0))) (hf0 : f ≠ 0) :
    ∃ N : ℕ, m.degree f ∈ AddSubmonoid.closure (Set.range fun i ↦ m.degree (c N i)) := by
  rw [Algebra.adjoin_range_eq_range_aeval] at hf
  obtain ⟨P, rfl⟩ := hf
  exact exists_degree_aeval_mem_closure_of_step h.monic
    (fun hPδ htop ↦ by
      obtain ⟨M, -, P', hP'P, hlt⟩ := h.exists_stage_aeval_eq_support_lt hPδ htop
      exact ⟨M, P', hP'P, hlt⟩)
    hf0

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

/-- **Eventual SAGBI basis under finite generation.** If the monoid of leading exponents of
`k[c 0]` is finitely generated, every fair SAGBI completion sequence `c` reaches a stage `N` from
which onward every stage `Set.range (c M)` (`M ≥ N`) is a SAGBI basis of `k[c 0]`. Note that the
generator families `c M` themselves may keep growing rather than stabilizing. -/
theorem exists_isSAGBIBasis_of_fg (h : m.IsFairSAGBISequence c)
    (hfg : (m.leadingExponents (Algebra.adjoin k (Set.range (c 0)))).FG) :
    ∃ N : ℕ, ∀ M ≥ N,
      m.IsSAGBIBasis (Set.range (c M)) (Algebra.adjoin k (Set.range (c 0))) := by
  classical
  have hunion : m.IsSAGBIBasis (⋃ n, Set.range (c n)) (Algebra.adjoin k (Set.range (c 0))) :=
    IsSAGBIBasis.mk (Set.iUnion_subset fun n ↦ h.adjoin_eq n ▸ Algebra.subset_adjoin)
      (by rw [Set.image_iUnion, Algebra.adjoin_iUnion, h.iSup_adjoin_leadingTerm_eq_initialAlgebra])
  obtain ⟨B, hBsub, hB⟩ :=
    hunion.exists_finset_subset (fg_initialAlgebra_iff_fg_leadingExponents.2 hfg)
  have hdir : Directed (· ⊆ ·) (fun n ↦ Set.range (c n)) :=
    Monotone.directed_le fun _ _ hle ↦ h.range_subset_of_le hle
  obtain ⟨N, hNB⟩ := hdir.exists_mem_subset_of_finset_subset_biUnion hBsub
  exact ⟨N, fun M hM ↦ hB.mono (hNB.trans (h.range_subset_of_le hM))
    (h.adjoin_eq M ▸ Algebra.subset_adjoin)⟩

/-- **Termination of fair indexed SAGBI completion.** Under the hypotheses of
`MonomialOrder.IsFairSAGBISequence.exists_isSAGBIBasis_of_fg`, suppose each stage comes with an
injective index inclusion `τ n : ι n → ι (n + 1)` whose new indices `j ∉ Set.range (τ n)` are
certified by nonzero subduction remainders of elements of `k[c n]` against `c n`. Then from some
stage `N` onward, every stage is a SAGBI basis of `k[c 0]` and every stage inclusion `τ M` is
bijective, so no further indices are adjoined. -/
theorem exists_isSAGBIBasis_and_bijective_of_fg (h : m.IsFairSAGBISequence c)
    (hfg : (m.leadingExponents (Algebra.adjoin k (Set.range (c 0)))).FG)
    {τ : ∀ n, ι n → ι (n + 1)} (hτ : ∀ n, Function.Injective (τ n))
    (hnew : ∀ n (j : ι (n + 1)), j ∉ Set.range (τ n) →
      ∃ f ∈ Algebra.adjoin k (Set.range (c n)),
        ∃ (Q : MvPolynomial (ι n) k) (r : MvPolynomial σ k),
          m.IsSubduction (c n) f Q r ∧ r ≠ 0) :
    ∃ N : ℕ, ∀ M ≥ N,
      m.IsSAGBIBasis (Set.range (c M)) (Algebra.adjoin k (Set.range (c 0))) ∧
        Function.Bijective (τ M) := by
  obtain ⟨N, hN⟩ := h.exists_isSAGBIBasis_of_fg hfg
  refine ⟨N, fun M hM ↦ ⟨hN M hM, hτ M, fun j ↦ ?_⟩⟩
  by_contra hj
  obtain ⟨f, hf, Q, r, hs, hr⟩ := hnew M j hj
  rw [h.adjoin_eq M] at hf
  exact hr (hs.remainder_eq_zero (hN M hM) hf)

/-- For a fair SAGBI completion sequence of finite families, some stage is a SAGBI basis of
`k[c 0]` if and only if the leading-exponent monoid of `k[c 0]` is finitely generated. -/
theorem exists_isSAGBIBasis_iff_fg_leadingExponents [∀ n, Finite (ι n)]
    (h : m.IsFairSAGBISequence c) :
    (∃ N : ℕ, m.IsSAGBIBasis (Set.range (c N)) (Algebra.adjoin k (Set.range (c 0)))) ↔
      (m.leadingExponents (Algebra.adjoin k (Set.range (c 0)))).FG := by
  refine ⟨fun ⟨N, hN⟩ ↦ hN.fg_leadingExponents (Set.finite_range (c N)), fun hfg ↦ ?_⟩
  obtain ⟨N, hN⟩ := h.exists_isSAGBIBasis_of_fg hfg
  exact ⟨N, hN N le_rfl⟩

end IsFairSAGBISequence

end FairCompletion

section Run

variable {σ k : Type*} [Field k] {m : MonomialOrder σ}
  {G : ℕ → Set (MvPolynomial σ k)} {f : ℕ → MvPolynomial σ k}

private theorem monic_of_subductionStep
    (hstep : ∀ n, m.SubductionStep (f n) (G (n + 1)) (G n)) (hG : ∀ g ∈ G 0, m.Monic g)
    (n : ℕ) : ∀ g ∈ G n, m.Monic g := by
  induction n with
  | zero => exact hG
  | succ n ih => exact (hstep n).monic ih

private theorem adjoin_eq_of_subductionStep
    (hstep : ∀ n, m.SubductionStep (f n) (G (n + 1)) (G n))
    (hf : ∀ n, f n ∈ Algebra.adjoin k (G n)) (n : ℕ) :
    Algebra.adjoin k (G n) = Algebra.adjoin k (G 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [(hstep n).adjoin_eq (hf n), ih]

private theorem isFairSAGBISequence_of_subductionStep
    (hstep : ∀ n, m.SubductionStep (f n) (G (n + 1)) (G n))
    (hf : ∀ n, f n ∈ Algebra.adjoin k (G n)) (hG : ∀ g ∈ G 0, m.Monic g)
    {J : ℕ → Type*} {u v : ∀ n, J n → G n →₀ ℕ}
    (hJ : ∀ n, TauCeti.toricIdeal k (fun g : G n ↦ m.degree g.val) =
      Ideal.span (Set.range fun j ↦ monomial (u n j) (1 : k) - monomial (v n j) 1))
    (hfair : ∀ n j, ∃ N, f N =
      aeval ((↑) : G n → MvPolynomial σ k) (monomial (u n j) (1 : k) - monomial (v n j) 1)) :
    m.IsFairSAGBISequence (fun n (g : G n) ↦ g.val) where
  monic n g := monic_of_subductionStep hstep hG n g.val g.property
  range_subset n := by
    simp only [Subtype.range_coe]
    exact (hstep n).subset
  subset_adjoin n := by
    simp only [Subtype.range_coe]
    rw [← (hstep n).adjoin_eq (hf n)]
    exact Algebra.subset_adjoin
  fair n := by
    refine ⟨Set.range fun j ↦ (u n j, v n j), ?_, ?_⟩
    · rw [← Set.range_comp]
      exact hJ n
    · rintro _ ⟨j, rfl⟩
      obtain ⟨N, hN⟩ := hfair n j
      obtain ⟨Q, r, hs, hr⟩ := hstep N
      refine ⟨N, N + 1, Nat.le_succ N, Q, r, hN ▸ hs, fun hr0 ↦ ?_⟩
      rcases hr with ⟨rfl, -⟩ | ⟨-, hGN⟩
      · exact absurd rfl hr0
      · simp only [Subtype.range_coe, hGN]
        exact Set.mem_insert _ _

/-- **Fair SAGBI completion converges.** Consider a run of completion steps
`G (n + 1)` from `G n` processing `f n ∈ k[G n]`, starting from monic generators. Suppose that,
for each stage `n`, binomials `Y^(u n j) - Y^(v n j)` generate the toric ideal of the leading
exponents of `G n`, and that each binomial is evaluated in `G n` and processed at a possibly
different stage `N`. Then the union of all stages is a SAGBI basis of `k[G 0]`. -/
theorem isSAGBIBasis_iUnion_of_subductionStep
    (hstep : ∀ n, m.SubductionStep (f n) (G (n + 1)) (G n))
    (hf : ∀ n, f n ∈ Algebra.adjoin k (G n)) (hG : ∀ g ∈ G 0, m.Monic g)
    {J : ℕ → Type*} {u v : ∀ n, J n → G n →₀ ℕ}
    (hJ : ∀ n, TauCeti.toricIdeal k (fun g : G n ↦ m.degree g.val) =
      Ideal.span (Set.range fun j ↦ monomial (u n j) (1 : k) - monomial (v n j) 1))
    (hfair : ∀ n j, ∃ N, f N =
      aeval ((↑) : G n → MvPolynomial σ k) (monomial (u n j) (1 : k) - monomial (v n j) 1)) :
    m.IsSAGBIBasis (⋃ n, G n) (Algebra.adjoin k (G 0)) := by
  have hseq := isFairSAGBISequence_of_subductionStep hstep hf hG hJ hfair
  refine IsSAGBIBasis.mk (Set.iUnion_subset fun n ↦ ?_) ?_
  · rw [← adjoin_eq_of_subductionStep hstep hf n]
    exact Algebra.subset_adjoin
  · have hsup := hseq.iSup_adjoin_leadingTerm_eq_initialAlgebra
    simp only [Subtype.range_coe] at hsup
    rw [Set.image_iUnion, Algebra.adjoin_iUnion, hsup]

/-- **Termination of SAGBI completion.** Under the hypotheses of
`MonomialOrder.isSAGBIBasis_iUnion_of_subductionStep`, if the initial algebra of `k[G 0]` is
finitely generated, then some stage `G N` is a SAGBI basis of `k[G 0]`, and every later step
adjoins nothing. -/
theorem exists_isSAGBIBasis_of_subductionStep
    (hstep : ∀ n, m.SubductionStep (f n) (G (n + 1)) (G n))
    (hf : ∀ n, f n ∈ Algebra.adjoin k (G n)) (hG : ∀ g ∈ G 0, m.Monic g)
    {J : ℕ → Type*} {u v : ∀ n, J n → G n →₀ ℕ}
    (hJ : ∀ n, TauCeti.toricIdeal k (fun g : G n ↦ m.degree g.val) =
      Ideal.span (Set.range fun j ↦ monomial (u n j) (1 : k) - monomial (v n j) 1))
    (hfair : ∀ n j, ∃ N, f N =
      aeval ((↑) : G n → MvPolynomial σ k) (monomial (u n j) (1 : k) - monomial (v n j) 1))
    (hfg : (m.initialAlgebra (Algebra.adjoin k (G 0))).FG) :
    ∃ N, m.IsSAGBIBasis (G N) (Algebra.adjoin k (G 0)) ∧ ∀ n, N ≤ n → G n = G N := by
  have hseq := isFairSAGBISequence_of_subductionStep hstep hf hG hJ hfair
  have hfg' : (m.leadingExponents (Algebra.adjoin k (Set.range fun g : G 0 ↦ g.val))).FG := by
    rw [Subtype.range_coe]
    exact fg_initialAlgebra_iff_fg_leadingExponents.mp hfg
  obtain ⟨N, hN⟩ := hseq.exists_isSAGBIBasis_of_fg hfg'
  simp only [Subtype.range_coe] at hN
  refine ⟨N, hN N le_rfl, fun i hi ↦ ?_⟩
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i hi ih =>
    have hfi : f i ∈ Algebra.adjoin k (G 0) := adjoin_eq_of_subductionStep hstep hf i ▸ hf i
    rw [(hstep i).eq_of_isSAGBIBasis (hN i hi) hfi, ih]

end Run

section BatchCompletion

universe u v

variable {σ : Type*} {k : Type v} [Field k] {ι₀ : Type u} [Finite ι₀]

/-- Chosen finite binomial generating set of the toric ideal of `m.degree ∘ c`. -/
private noncomputable def chosenToricBinomials (m : MonomialOrder σ) {ι : Type u} [Finite ι]
    (c : ι → MvPolynomial σ k) : Finset ((ι →₀ ℕ) × (ι →₀ ℕ)) :=
  (TauCeti.exists_finset_toricIdeal_eq_span.{v} fun i ↦ m.degree (c i)).choose

private theorem chosenToricBinomials_span (m : MonomialOrder σ) {ι : Type u} [Finite ι]
    (c : ι → MvPolynomial σ k) :
    TauCeti.toricIdeal k (fun i ↦ m.degree (c i)) =
      Ideal.span ((fun p : (ι →₀ ℕ) × (ι →₀ ℕ) ↦
        monomial p.1 (1 : k) - monomial p.2 1) '' (m.chosenToricBinomials c : Set _)) :=
  (TauCeti.exists_finset_toricIdeal_eq_span.{v} fun i ↦ m.degree (c i)).choose_spec.2 k

/-- Chosen subduction expression and remainder for `f` with respect to `c`, obtained by subducting
against the nonzero entries of `c` and renaming back to `ι`. -/
private noncomputable def chosenSubductionPair (m : MonomialOrder σ) {ι : Type u}
    (c : ι → MvPolynomial σ k) (f : MvPolynomial σ k) :
    MvPolynomial ι k × MvPolynomial σ k :=
  have hb : ∀ i : {i : ι // c i ≠ 0}, (c ∘ Subtype.val) i ≠ 0 := fun i ↦ i.property
  open scoped Classical in
  (rename Subtype.val (m.exists_isSubduction hb f).choose,
    (m.exists_isSubduction hb f).choose_spec.choose)

private theorem chosenSubductionPair_fst (m : MonomialOrder σ) {ι : Type u}
    (c : ι → MvPolynomial σ k) (f : MvPolynomial σ k) :
    (m.chosenSubductionPair c f).1 =
      rename Subtype.val
        (m.exists_isSubduction (fun i : {i : ι // c i ≠ 0} ↦ i.property) f).choose :=
  rfl

private theorem chosenSubductionPair_spec (m : MonomialOrder σ) {ι : Type u}
    (c : ι → MvPolynomial σ k) (f : MvPolynomial σ k) :
    m.IsSubduction c f (m.chosenSubductionPair c f).1 (m.chosenSubductionPair c f).2 := by
  have hb : ∀ i : {i : ι // c i ≠ 0}, (c ∘ Subtype.val) i ≠ 0 := fun i ↦ i.property
  have hs : m.IsSubduction (c ∘ Subtype.val) f (m.exists_isSubduction hb f).choose
      (m.exists_isSubduction hb f).choose_spec.choose :=
    (m.exists_isSubduction hb f).choose_spec.choose_spec
  have hclosure : AddSubmonoid.closure (Set.range (m.degree ∘ c)) =
      AddSubmonoid.closure
        (Set.range (m.degree ∘ (c ∘ (Subtype.val : {i : ι // c i ≠ 0} → ι)))) := by
    refine le_antisymm (AddSubmonoid.closure_le.2 ?_) (AddSubmonoid.closure_mono ?_)
    · rintro _ ⟨i, rfl⟩
      by_cases hi : c i = 0
      · simp [hi]
      · exact AddSubmonoid.subset_closure ⟨⟨i, hi⟩, rfl⟩
    · rintro _ ⟨i, rfl⟩
      exact ⟨i.val, rfl⟩
  refine ⟨?_, ?_, ?_, hs.degree_le⟩
  · simpa [chosenSubductionPair, aeval_rename] using hs.eq_aeval_add
  · intro w hw
    rw [chosenSubductionPair_fst] at hw
    obtain ⟨u, hu, heq⟩ := linearCombination_degree_rename_eq_of_comp (c := c) rfl hw
    rw [Function.comp_def, heq]
    exact hs.support_le u hu
  · intro a ha
    rw [hclosure]
    exact hs.irreducible a ha

/-- Internal stage package for concrete certified batch SAGBI completion. -/
private structure BatchStage (c₀ : ι₀ → MvPolynomial σ k) where
  Idx : Type u
  instFinite : Finite Idx
  family : Idx → MvPolynomial σ k
  retract : MvPolynomial Idx k →ₐ[k] MvPolynomial ι₀ k

/-- One batch completion step: evaluate each chosen toric-ideal binomial generator at `S.family`,
subduct the resulting polynomial against `S.family`, adjoin the monic normalizations of all nonzero
remainders, and compose the presentation retraction with `m.subductionRetract`. -/
private noncomputable def nextBatchStage (m : MonomialOrder σ) {c₀ : ι₀ → MvPolynomial σ k}
    (S : BatchStage c₀) : BatchStage c₀ :=
  haveI : Finite S.Idx := S.instFinite
  let B := m.chosenToricBinomials S.family
  let sub (p : B) :=
    m.chosenSubductionPair S.family (aeval S.family (monomial p.val.1 (1 : k) - monomial p.val.2 1))
  let κ := {p : B // (sub p).2 ≠ 0}
  { Idx := S.Idx ⊕ κ
    instFinite := inferInstance
    family := Sum.elim S.family (m.monicNormalize ∘ fun l ↦ (sub l.val).2)
    retract := S.retract.comp
      (m.subductionRetract (fun l : κ ↦ monomial l.val.val.1 (1 : k) - monomial l.val.val.2 1)
        (fun l ↦ (sub l.val).1) (fun l ↦ (sub l.val).2)) }

private noncomputable def batchStageSeq (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k) :
    ℕ → BatchStage c₀
  | 0 => ⟨ι₀, inferInstance, c₀, AlgHom.id k (MvPolynomial ι₀ k)⟩
  | n + 1 => m.nextBatchStage (m.batchStageSeq c₀ n)

/-- The finite index type of stage `n` of batch SAGBI completion starting from `c₀`: stage `0` is
`ι₀`, and stage `n + 1` extends stage `n` by a sum with the subtype of elements in a chosen finite
binomial generating set of `TauCeti.toricIdeal k (m.degree ∘ m.sagbiCompletionFamily c₀ n)` whose
evaluation at `m.sagbiCompletionFamily c₀ n` has nonzero chosen remainder when subducted against
the nonzero entries of `m.sagbiCompletionFamily c₀ n` (`MonomialOrder.exists_sagbiCompletion_succ`).
Monicity of `c₀` is needed for fairness (`MonomialOrder.isFairSAGBISequence_sagbiCompletionFamily`).
-/
noncomputable def sagbiCompletionIndex (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : Type u :=
  (m.batchStageSeq c₀ n).Idx

/-- Every stage index type `m.sagbiCompletionIndex c₀ n` is finite when `ι₀` is finite. -/
instance instFiniteSagbiCompletionIndex (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : Finite (m.sagbiCompletionIndex c₀ n) :=
  (m.batchStageSeq c₀ n).instFinite

/-- The generator family at stage `n` of batch SAGBI completion starting from `c₀`. Stage `0` is
`c₀`; at stage `n + 1`, each binomial in a chosen finite binomial generating set of
`TauCeti.toricIdeal k (m.degree ∘ m.sagbiCompletionFamily c₀ n)` is evaluated at
`m.sagbiCompletionFamily c₀ n`, the resulting polynomial is subducted against
`m.sagbiCompletionFamily c₀ n` (by filtering to its nonzero entries, yielding a certified
`MonomialOrder.IsSubduction` pair via `MonomialOrder.exists_sagbiCompletion_succ`), and
`m.monicNormalize` of every nonzero remainder is adjoined. Monicity of `c₀` is required so that
unscaled toric binomials cancel leading terms and yield a fair completion sequence
(`MonomialOrder.isFairSAGBISequence_sagbiCompletionFamily`). -/
noncomputable def sagbiCompletionFamily (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : m.sagbiCompletionIndex c₀ n → MvPolynomial σ k :=
  (m.batchStageSeq c₀ n).family

/-- The surjective presentation retraction from stage `n` of batch SAGBI completion back to the
initial polynomial ring `MvPolynomial ι₀ k`. Starting from `AlgHom.id` at stage `0`, each step
composes with `MonomialOrder.subductionRetract` for the chosen finite binomial generating set of
`TauCeti.toricIdeal k (m.degree ∘ m.sagbiCompletionFamily c₀ n)` and the chosen subduction pairs of
their evaluations at `m.sagbiCompletionFamily c₀ n` against `m.sagbiCompletionFamily c₀ n` for
nonzero remainders. Filtering zero generators internally makes `MonomialOrder.IsSubduction` hold
unconditionally (`MonomialOrder.exists_sagbiCompletion_succ`), so the exported evaluation
factorization `MonomialOrder.aeval_comp_sagbiCompletionRetract` holds for every finite initial
family `c₀`, while `MonomialOrder.isFairSAGBISequence_sagbiCompletionFamily` assumes monicity of
`c₀` for fairness. -/
noncomputable def sagbiCompletionRetract (m : MonomialOrder σ) (c₀ : ι₀ → MvPolynomial σ k)
    (n : ℕ) : MvPolynomial (m.sagbiCompletionIndex c₀ n) k →ₐ[k] MvPolynomial ι₀ k :=
  (m.batchStageSeq c₀ n).retract

-- Definitional boundary for private `batchStageSeq` / `nextBatchStage`:
-- `sagbiCompletionIndexZeroEquiv`, `sagbiCompletionIndexInclusion`, `sagbiCompletionFamily_zero`,
-- `sagbiCompletionRetract_zero`, and `exists_sagbiCompletion_succ` are the only declarations
-- allowed to unfold `batchStageSeq` / `nextBatchStage` (including via `Equiv.refl _` or `Sum.inl`).
-- All downstream code must go through `sagbiCompletionFamily_zero`, `sagbiCompletionRetract_zero`,
-- and `exists_sagbiCompletion_succ`.

/-- The canonical equivalence identifying `m.sagbiCompletionIndex c₀ 0` with `ι₀`. -/
noncomputable def sagbiCompletionIndexZeroEquiv (m : MonomialOrder σ)
    (c₀ : ι₀ → MvPolynomial σ k) : m.sagbiCompletionIndex c₀ 0 ≃ ι₀ :=
  Equiv.refl ι₀

/-- The canonical inclusion of stage `n` indices into stage `n + 1` of batch SAGBI completion. -/
noncomputable def sagbiCompletionIndexInclusion (m : MonomialOrder σ)
    (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    m.sagbiCompletionIndex c₀ n → m.sagbiCompletionIndex c₀ (n + 1) :=
  Sum.inl

variable {m : MonomialOrder σ} {c₀ : ι₀ → MvPolynomial σ k}

/-- At stage `0`, `m.sagbiCompletionFamily c₀ 0` agrees with `c₀` along
`m.sagbiCompletionIndexZeroEquiv c₀`. -/
@[simp]
theorem sagbiCompletionFamily_zero (i : m.sagbiCompletionIndex c₀ 0) :
    m.sagbiCompletionFamily c₀ 0 i = c₀ (m.sagbiCompletionIndexZeroEquiv c₀ i) := by
  dsimp only [sagbiCompletionFamily, batchStageSeq, sagbiCompletionIndexZeroEquiv]
  rfl

/-- At stage `0`, `m.sagbiCompletionRetract c₀ 0` is variable renaming along
`m.sagbiCompletionIndexZeroEquiv c₀`. -/
@[simp]
theorem sagbiCompletionRetract_zero (c₀ : ι₀ → MvPolynomial σ k) :
    m.sagbiCompletionRetract c₀ 0 = rename (m.sagbiCompletionIndexZeroEquiv c₀) :=
  algHom_ext fun _ ↦ by
    rw [rename_X]
    dsimp only [sagbiCompletionRetract, batchStageSeq, sagbiCompletionIndexZeroEquiv]
    rfl

/-- **Successor-stage characterization of batch SAGBI completion.** Stage `n + 1` chooses a finite
binomial generating set `B` of `TauCeti.toricIdeal k (m.degree ∘ m.sagbiCompletionFamily c₀ n)`,
evaluates each `p ∈ B` at `m.sagbiCompletionFamily c₀ n`, and chooses a subduction pair `(Q p, r p)`
of that evaluated polynomial against `m.sagbiCompletionFamily c₀ n` (certified by
`MonomialOrder.IsSubduction`), decomposes
`m.sagbiCompletionIndex c₀ (n + 1)` via an equivalence
`e : m.sagbiCompletionIndex c₀ n ⊕ {p : B // r p ≠ 0} ≃ m.sagbiCompletionIndex c₀ (n + 1)`
extending `m.sagbiCompletionIndexInclusion c₀ n`, adjoins `m.monicNormalize (r l.1)` on the new
indices, and factors `m.sagbiCompletionRetract c₀ (n + 1)` through `m.sagbiCompletionRetract c₀ n`
and `MonomialOrder.subductionRetract` along `rename e` (yielding its action on old and new
variables via `sagbiCompletionRetract_succ_rename_inclusion` together with `MvPolynomial.rename_X`,
and `subductionRetract_X_inr`). -/
theorem exists_sagbiCompletion_succ (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    ∃ (B : Finset ((m.sagbiCompletionIndex c₀ n →₀ ℕ) × (m.sagbiCompletionIndex c₀ n →₀ ℕ)))
      (Q : B → MvPolynomial (m.sagbiCompletionIndex c₀ n) k)
      (r : B → MvPolynomial σ k)
      (e : m.sagbiCompletionIndex c₀ n ⊕ {p : B // r p ≠ 0} ≃
        m.sagbiCompletionIndex c₀ (n + 1)),
      TauCeti.toricIdeal k (fun i ↦ m.degree (m.sagbiCompletionFamily c₀ n i)) =
        Ideal.span ((fun p : (m.sagbiCompletionIndex c₀ n →₀ ℕ) ×
          (m.sagbiCompletionIndex c₀ n →₀ ℕ) ↦
            monomial p.1 (1 : k) - monomial p.2 1) '' (B : Set _)) ∧
      (∀ p : B, m.IsSubduction (m.sagbiCompletionFamily c₀ n)
        (aeval (m.sagbiCompletionFamily c₀ n) (monomial p.val.1 (1 : k) - monomial p.val.2 1))
        (Q p) (r p)) ∧
      (∀ i, e (Sum.inl i) = m.sagbiCompletionIndexInclusion c₀ n i) ∧
      m.sagbiCompletionFamily c₀ (n + 1) ∘ e =
        Sum.elim (m.sagbiCompletionFamily c₀ n) (m.monicNormalize ∘ fun l ↦ r l.val) ∧
      (m.sagbiCompletionRetract c₀ (n + 1)).comp (rename e) =
        (m.sagbiCompletionRetract c₀ n).comp
          (m.subductionRetract
            (fun l : {p : B // r p ≠ 0} ↦ monomial l.val.val.1 (1 : k) - monomial l.val.val.2 1)
            (fun l ↦ Q l.val) (fun l ↦ r l.val)) := by
  let B := m.chosenToricBinomials (m.sagbiCompletionFamily c₀ n)
  let sub (p : B) := m.chosenSubductionPair (m.sagbiCompletionFamily c₀ n)
    (aeval (m.sagbiCompletionFamily c₀ n) (monomial p.val.1 (1 : k) - monomial p.val.2 1))
  -- Unfolds `sagbiCompletionIndex c₀ (n + 1)` through `batchStageSeq` / `nextBatchStage`.
  let e : m.sagbiCompletionIndex c₀ n ⊕ {p : B // (sub p).2 ≠ 0} ≃
      m.sagbiCompletionIndex c₀ (n + 1) := Equiv.refl _
  refine ⟨B, fun p ↦ (sub p).1, fun p ↦ (sub p).2, e, m.chosenToricBinomials_span _,
    fun p ↦ m.chosenSubductionPair_spec _ _,
    fun _ ↦ by dsimp only [e, sagbiCompletionIndexInclusion]; rfl,
    funext fun _ ↦ by
      dsimp only [Function.comp_def, e, sagbiCompletionFamily, batchStageSeq, nextBatchStage]
      rfl,
    algHom_ext fun _ ↦ by
      rw [AlgHom.comp_apply, rename_X]
      dsimp only [e, sagbiCompletionRetract, batchStageSeq, nextBatchStage]
      rfl⟩

/-- Stage `0` of `m.sagbiCompletionFamily c₀` has the same generator set `Set.range c₀`. -/
@[simp]
theorem range_sagbiCompletionFamily_zero (c₀ : ι₀ → MvPolynomial σ k) :
    Set.range (m.sagbiCompletionFamily c₀ 0) = Set.range c₀ := by
  ext f
  simp only [Set.mem_range, m.sagbiCompletionFamily_zero]
  exact (m.sagbiCompletionIndexZeroEquiv c₀).surjective.exists

/-- The stage-inclusion map `m.sagbiCompletionIndexInclusion c₀ n` is injective. -/
theorem sagbiCompletionIndexInclusion_injective (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    Function.Injective (m.sagbiCompletionIndexInclusion c₀ n) := by
  obtain ⟨_, _, _, e, -, -, he_inl, -, -⟩ := m.exists_sagbiCompletion_succ c₀ n
  exact fun _ _ hij ↦ Sum.inl_injective (e.injective (by rwa [he_inl, he_inl]))

/-- On old stage-`n` indices, `m.sagbiCompletionFamily c₀ (n + 1)` reproduces
`m.sagbiCompletionFamily c₀ n`. -/
@[simp]
theorem sagbiCompletionFamily_succ_inclusion (n : ℕ) (i : m.sagbiCompletionIndex c₀ n) :
    m.sagbiCompletionFamily c₀ (n + 1) (m.sagbiCompletionIndexInclusion c₀ n i) =
      m.sagbiCompletionFamily c₀ n i := by
  obtain ⟨_, _, _, e, -, -, he_inl, hfam, -⟩ := m.exists_sagbiCompletion_succ c₀ n
  rw [← he_inl, ← Function.comp_apply (f := m.sagbiCompletionFamily c₀ (n + 1)), hfam,
    Sum.elim_inl]

/-- Composing `m.sagbiCompletionRetract c₀ (n + 1)` with variable renaming along
`m.sagbiCompletionIndexInclusion c₀ n` recovers `m.sagbiCompletionRetract c₀ n`. -/
theorem sagbiCompletionRetract_succ_comp_rename_inclusion (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    (m.sagbiCompletionRetract c₀ (n + 1)).comp (rename (m.sagbiCompletionIndexInclusion c₀ n)) =
      m.sagbiCompletionRetract c₀ n := by
  obtain ⟨_, _, _, e, -, -, he_inl, -, hret⟩ := m.exists_sagbiCompletion_succ c₀ n
  exact algHom_ext fun i ↦ by simpa [← he_inl] using AlgHom.congr_fun hret (X (Sum.inl i))

/-- Evaluating `m.sagbiCompletionRetract c₀ (n + 1)` on a polynomial renamed from stage `n` agrees
with `m.sagbiCompletionRetract c₀ n`. -/
@[simp]
theorem sagbiCompletionRetract_succ_rename_inclusion (n : ℕ)
    (p : MvPolynomial (m.sagbiCompletionIndex c₀ n) k) :
    m.sagbiCompletionRetract c₀ (n + 1) (rename (m.sagbiCompletionIndexInclusion c₀ n) p) =
      m.sagbiCompletionRetract c₀ n p :=
  AlgHom.congr_fun (m.sagbiCompletionRetract_succ_comp_rename_inclusion c₀ n) p

/-- Every generator at every stage of `m.sagbiCompletionFamily c₀` is monic when `c₀` is monic. -/
theorem monic_sagbiCompletionFamily (hc₀ : ∀ i, m.Monic (c₀ i)) (n : ℕ)
    (i : m.sagbiCompletionIndex c₀ n) :
    m.Monic (m.sagbiCompletionFamily c₀ n i) := by
  induction n with
  | zero => rw [m.sagbiCompletionFamily_zero]; exact hc₀ _
  | succ n ih =>
    obtain ⟨_, _, r, e, -, -, -, hfam, -⟩ := m.exists_sagbiCompletion_succ c₀ n
    obtain ⟨x, rfl⟩ := e.surjective i
    rw [← Function.comp_apply (f := m.sagbiCompletionFamily c₀ (n + 1)), hfam]
    cases x with
    | inl j => rw [Sum.elim_inl]; exact ih j
    | inr l => rw [Sum.elim_inr, Function.comp_apply]; exact m.monic_monicNormalize l.property

/-- Every stage's presentation retraction `m.sagbiCompletionRetract c₀ n` is surjective. -/
theorem sagbiCompletionRetract_surjective (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    Function.Surjective (m.sagbiCompletionRetract c₀ n) := by
  induction n with
  | zero =>
    rw [m.sagbiCompletionRetract_zero]
    exact rename_surjective _ (m.sagbiCompletionIndexZeroEquiv c₀).surjective
  | succ n ih =>
    obtain ⟨_, _, _, e, -, -, -, -, hret⟩ := m.exists_sagbiCompletion_succ c₀ n
    refine Function.Surjective.of_comp (g := rename e) ?_
    rw [← AlgHom.coe_comp, hret, AlgHom.coe_comp]
    exact ih.comp subductionRetract_surjective

/-- Evaluating `c₀` after `m.sagbiCompletionRetract c₀ n` equals evaluating stage `n` of
`m.sagbiCompletionFamily c₀`. -/
theorem aeval_comp_sagbiCompletionRetract (c₀ : ι₀ → MvPolynomial σ k) (n : ℕ) :
    (aeval c₀).comp (m.sagbiCompletionRetract c₀ n) = aeval (m.sagbiCompletionFamily c₀ n) := by
  induction n with
  | zero => exact algHom_ext fun _ ↦ by simp
  | succ n ih =>
    obtain ⟨B, Q, r, e, -, hsub, -, hfam, hret⟩ := m.exists_sagbiCompletion_succ c₀ n
    have hs := fun l : {p : B // r p ≠ 0} ↦ hsub l.val
    refine (AlgHom.cancel_right (rename_surjective e e.surjective)).mp ?_
    rw [AlgHom.comp_assoc, hret, ← AlgHom.comp_assoc, ih,
      m.aeval_comp_subductionRetract hs, ← hfam, aeval_comp_rename]

/-- Batch toric-binomial completion starting from a finite monic family `c₀` is a fair SAGBI
completion sequence. -/
theorem isFairSAGBISequence_sagbiCompletionFamily (hc₀ : ∀ i, m.Monic (c₀ i)) :
    m.IsFairSAGBISequence (m.sagbiCompletionFamily c₀) where
  monic := m.monic_sagbiCompletionFamily hc₀
  range_subset n := fun _ ⟨i, hi⟩ ↦
    ⟨m.sagbiCompletionIndexInclusion c₀ n i, (m.sagbiCompletionFamily_succ_inclusion n i).trans hi⟩
  subset_adjoin n := by
    rw [adjoin_range_eq_of_aeval_comp_eq (m.aeval_comp_sagbiCompletionRetract c₀ n)
        (m.sagbiCompletionRetract_surjective c₀ n),
      ← adjoin_range_eq_of_aeval_comp_eq (m.aeval_comp_sagbiCompletionRetract c₀ (n + 1))
        (m.sagbiCompletionRetract_surjective c₀ (n + 1))]
    exact Algebra.subset_adjoin
  fair n := by
    obtain ⟨B, Q, r, e, hB, hsub, -, hfam, -⟩ := m.exists_sagbiCompletion_succ c₀ n
    refine ⟨(B : Set _), hB, fun p hp ↦ ?_⟩
    refine ⟨n, n + 1, Nat.le_succ n, Q ⟨p, hp⟩, r ⟨p, hp⟩, hsub ⟨p, hp⟩, fun hr ↦ ?_⟩
    refine ⟨e (Sum.inr ⟨⟨p, hp⟩, hr⟩), ?_⟩
    rw [← Function.comp_apply (f := m.sagbiCompletionFamily c₀ (n + 1)), hfam, Sum.elim_inr,
      Function.comp_apply]

/-- **Termination of certified batch SAGBI completion.** Starting from a finite monic family
`c₀`, if the leading-exponent monoid of `k[c₀]` is finitely generated, then there exists a stage
`N` such that for every `M ≥ N`, `m.sagbiCompletionFamily c₀ M` is a SAGBI basis of `k[c₀]` and
the stage index inclusion `m.sagbiCompletionIndexInclusion c₀ M` is bijective (so batch completion
adjoins no further generators). -/
theorem exists_isSAGBIBasis_and_bijective_sagbiCompletionIndexInclusion_of_fg
    (hc₀ : ∀ i, m.Monic (c₀ i))
    (hfg : (m.leadingExponents (Algebra.adjoin k (Set.range c₀))).FG) :
    ∃ N : ℕ, ∀ M ≥ N,
      m.IsSAGBIBasis (Set.range (m.sagbiCompletionFamily c₀ M)) (Algebra.adjoin k (Set.range c₀)) ∧
        Function.Bijective (m.sagbiCompletionIndexInclusion c₀ M) := by
  have hfair := m.isFairSAGBISequence_sagbiCompletionFamily hc₀
  have hfg' :
      (m.leadingExponents (Algebra.adjoin k (Set.range (m.sagbiCompletionFamily c₀ 0)))).FG := by
    rwa [m.range_sagbiCompletionFamily_zero]
  refine (hfair.exists_isSAGBIBasis_and_bijective_of_fg hfg'
    (m.sagbiCompletionIndexInclusion_injective c₀) fun n j hj ↦ ?_).imp fun N hN M hM ↦ ?_
  · obtain ⟨B, Q, r, e, -, hsub, he_inl, -, -⟩ := m.exists_sagbiCompletion_succ c₀ n
    obtain ⟨x, rfl⟩ := e.surjective j
    cases x with
    | inl i => exact absurd ⟨i, (he_inl i).symm⟩ hj
    | inr l =>
      refine ⟨aeval (m.sagbiCompletionFamily c₀ n)
        (monomial l.val.val.1 (1 : k) - monomial l.val.val.2 1), ?_, Q l.val, r l.val,
        hsub l.val, l.property⟩
      rw [Algebra.adjoin_range_eq_range_aeval]
      exact Set.mem_range_self _
  · simpa only [m.range_sagbiCompletionFamily_zero] using hN M hM

/-- **Certified finite SAGBI completion of a finite nonzero family.** If
`b : ι₀ → MvPolynomial σ k` is a finite family of nonzero polynomials whose generated subalgebra
`k[b]` has finitely generated leading-exponent monoid, then there exist a finite monic SAGBI basis
`c : κ → MvPolynomial σ k` of `k[b]` and a surjective `k`-algebra homomorphism
`φ : MvPolynomial κ k →ₐ[k] MvPolynomial ι₀ k` satisfying `(aeval b).comp φ = aeval c`. -/
theorem exists_finite_monic_isSAGBIBasis_of_fg {b : ι₀ → MvPolynomial σ k}
    (hb : ∀ i, b i ≠ 0)
    (hfg : (m.leadingExponents (Algebra.adjoin k (Set.range b))).FG) :
    ∃ (κ : Type u) (_ : Finite κ) (c : κ → MvPolynomial σ k)
      (φ : MvPolynomial κ k →ₐ[k] MvPolynomial ι₀ k),
      (∀ l, m.Monic (c l)) ∧
      m.IsSAGBIBasis (Set.range c) (Algebra.adjoin k (Set.range b)) ∧
      Function.Surjective φ ∧
      (aeval b).comp φ = aeval c := by
  let c₀ : ι₀ → MvPolynomial σ k := m.monicNormalize ∘ b
  have hc₀ : ∀ i, m.Monic (c₀ i) := fun i ↦ m.monic_monicNormalize (hb i)
  have hadj : Algebra.adjoin k (Set.range c₀) = Algebra.adjoin k (Set.range b) := by
    rw [Set.range_comp, adjoin_image_monicNormalize]
  obtain ⟨N, hN⟩ := (m.isFairSAGBISequence_sagbiCompletionFamily hc₀).exists_isSAGBIBasis_of_fg
    (hadj.symm ▸ hfg)
  let D : MvPolynomial ι₀ k ≃ₐ[k] MvPolynomial ι₀ k :=
    rescaleEquiv fun i ↦ Units.mk0 _ (m.leadingCoeff_ne_zero_iff.2 (hb i))
  have haeval_Dinv : (aeval b).comp (D.symm : MvPolynomial ι₀ k →ₐ[k] MvPolynomial ι₀ k) =
      aeval c₀ :=
    algHom_ext fun i ↦ by simp [D, c₀, monicNormalize_def]
  let φ := (D.symm : MvPolynomial ι₀ k →ₐ[k] MvPolynomial ι₀ k).comp
    (m.sagbiCompletionRetract c₀ N)
  refine ⟨m.sagbiCompletionIndex c₀ N, inferInstance, m.sagbiCompletionFamily c₀ N, φ,
    m.monic_sagbiCompletionFamily hc₀ N, ?_,
    D.symm.surjective.comp (m.sagbiCompletionRetract_surjective c₀ N), ?_⟩
  · have hN0 := hN N le_rfl
    rwa [m.range_sagbiCompletionFamily_zero, hadj] at hN0
  · rw [← AlgHom.comp_assoc, haeval_Dinv, m.aeval_comp_sagbiCompletionRetract c₀ N]

end BatchCompletion

end MonomialOrder
