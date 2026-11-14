/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.SAGBI.Monic
import Mathlib.Algebra.Algebra.Subalgebra.Directed
import Mathlib.Data.Nat.Pairing

/-!
# Certified SAGBI completion and termination

Let `m` be a monomial order on `σ →₀ ℕ` and `k` a field. Unlike Buchberger's algorithm for ideals
(`MonomialOrder.SPolynomialStep` in
`TauCeti.RingTheory.MvPolynomial.Groebner.SPolynomialCompletion`), SAGBI completion for a
subalgebra `A ⊆ MvPolynomial σ k` faces two genuine obstructions (proved sharp in
`TauCeti.RingTheory.MvPolynomial.SAGBI.Counterexamples`):

1. **Non-Noetherianity of submonoids of `σ →₀ ℕ`.** Even when `A` and its initial algebra
   `m.initialAlgebra A` are finitely generated (indeed even when `A = ⊤` inside
   `MvPolynomial (Fin 2) k`), an unfair choice of binomial relations can strictly enlarge the
   leading-term subalgebra infinitely many times. Fairness of relation processing is therefore
   indispensable.
2. **Non-finitely generated initial algebras.** Even when `A` is finitely generated inside
   `MvPolynomial (Fin 2) k` and relations are processed fairly, `m.initialAlgebra A` need not be
   finitely generated, in which case `A` admits no finite SAGBI basis and every fair completion
   sequence takes infinitely many strict steps.

This file develops finite-generation equivalences for initial algebras, certified SAGBI completion
steps, fair completion sequences, and termination equivalences over a field, with no finiteness
hypothesis on the variable type `σ` and without requiring the starting generators to be monic or
nonzero (tracking presentations across remainder adjunction is provided in
`TauCeti.RingTheory.MvPolynomial.SAGBI.Remainder`).

## Main definitions and results

* **Finite generation of the initial algebra:**
  * `MonomialOrder.fg_initialAlgebra_iff_fg_leadingExponents`,
    `MonomialOrder.exists_finset_isSAGBIBasis_iff_fg_leadingExponents`, and
    `MonomialOrder.exists_finset_isSAGBIBasis_iff_fg_initialAlgebra`: `A` admits a finite SAGBI
    basis if and only if `m.leadingExponents A` (equivalently `m.initialAlgebra A`) is finitely
    generated.
* **SAGBI completion steps, fair schedules, and termination:**
  * `MonomialOrder.SAGBIStep` and `MonomialOrder.BinomialSAGBIStep`: certified completion steps
    adjoining `m.monicNormalize r` for a nonzero subduction remainder `r` of an algebra element or
    of a leading-coefficient-rescaled toric binomial of the nonzero current generators.
  * `MonomialOrder.isSAGBIBasis_iff_no_sagbiStep` and
    `MonomialOrder.isSAGBIBasis_iff_no_binomialSAGBIStep`: a finite family is terminal for either
    step relation if and only if it is a SAGBI basis of the subalgebra it generates.
  * `MonomialOrder.IsFairSAGBICompletion`: a countable sequence of `SAGBIStep` enlargements that
    fairly processes a binomial generating set of the leading-exponent toric ideal of every stage.
  * `MonomialOrder.IsFairSAGBICompletion.isSAGBIBasis_iUnion`: the union of any fair SAGBI
    completion sequence is unconditionally a SAGBI basis of the initial generated subalgebra.
  * `MonomialOrder.exists_isFairSAGBICompletion`: every finite polynomial set admits an explicit
    fair completion sequence driven by `MonomialOrder.BinomialSAGBIStep`.
  * `MonomialOrder.IsFairSAGBICompletion.exists_isSAGBIBasis_iff_fg_initialAlgebra` and
    `MonomialOrder.exists_binomialSAGBIStep_completion_iff_fg_initialAlgebra`: fair SAGBI
    completion stabilizes at a finite SAGBI basis (and a finite certified binomial completion path
    exists) if and only if the initial algebra is finitely generated.

## References

* L. Robbiano, M. Sweedler, *Subalgebra bases*, in *Commutative Algebra (Salvador, 1988)*,
  Lecture Notes in Mathematics 1430, Springer, 1990, 61–87, §2–§4.
* D. Kapur, K. Madlener, *A completion procedure for computing a canonical basis for a
  k-subalgebra*, in *Computers and Mathematics*, Springer, 1989, 1–11.
* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 11.
* W. Bruns, A. Conca, M. Lembo, *SAGBI combinatorics of maximal minors and a SAGBI algorithm*,
  2025, arXiv:2504.10019, Section 2.
-/

public section

namespace MonomialOrder

open MvPolynomial

/-! ### Finite generation of the initial algebra and finite SAGBI bases -/

section FiniteGeneration

variable {σ k : Type*} [Field k] (m : MonomialOrder σ) (A : Subalgebra k (MvPolynomial σ k))

/-- Over a field, the initial algebra `m.initialAlgebra A` is finitely generated as a `k`-algebra if
and only if the additive submonoid `m.leadingExponents A` is finitely generated. -/
theorem fg_initialAlgebra_iff_fg_leadingExponents :
    (m.initialAlgebra A).FG ↔ (m.leadingExponents A).FG :=
  (Subalgebra.fg_iff_finiteType _).trans
    ⟨fun h ↦ AddMonoidAlgebra.finiteType_iff_fg.1 (h.equiv (m.initialAlgebraEquiv A).symm),
      fun h ↦ (AddMonoidAlgebra.finiteType_iff_fg.2 h).equiv (m.initialAlgebraEquiv A)⟩

/-- Over a field, a subalgebra `A` admits a finite SAGBI basis if and only if its leading-exponent
monoid `m.leadingExponents A` is finitely generated. -/
theorem exists_finset_isSAGBIBasis_iff_fg_leadingExponents :
    (∃ B : Finset (MvPolynomial σ k), m.IsSAGBIBasis (B : Set (MvPolynomial σ k)) A) ↔
      (m.leadingExponents A).FG := by
  classical
  constructor
  · rintro ⟨B, hB⟩
    refine (AddSubmonoid.fg_iff _).2 ⟨m.degree '' ((B : Set (MvPolynomial σ k)) \ {0}), ?_,
      B.finite_toSet.sdiff.image m.degree⟩
    refine le_antisymm (AddSubmonoid.closure_le.2 ?_) fun a ha ↦ ?_
    · rintro _ ⟨f, ⟨hfB, hf0⟩, rfl⟩
      exact m.degree_mem_leadingExponents (hB.subset hfB) hf0
    · obtain ⟨f, hfA, hf0, rfl⟩ := m.mem_leadingExponents_iff.1 ha
      exact (isSAGBIBasis_iff_degree_mem_closure.1 hB).2 f hfA hf0
  · intro hfg
    obtain ⟨S, hS, hSfin⟩ := (AddSubmonoid.fg_iff _).1 hfg
    let E := hSfin.toFinset
    have hE : AddSubmonoid.closure (E : Set (σ →₀ ℕ)) = m.leadingExponents A := by
      simpa [E] using hS
    choose g hgA hg0 hgdeg using fun e : E ↦
      m.mem_leadingExponents_iff.1 (hE ▸ AddSubmonoid.subset_closure (Finset.mem_coe.2 e.2))
    refine ⟨Finset.univ.image g, isSAGBIBasis_iff_degree_mem_closure.2 ⟨?_, fun f hfA hf0 ↦ ?_⟩⟩
    · intro x hx
      obtain ⟨e, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact hgA e
    · have hmem : m.degree f ∈ AddSubmonoid.closure (E : Set (σ →₀ ℕ)) := by
        rw [hE]
        exact m.degree_mem_leadingExponents hfA hf0
      refine AddSubmonoid.closure_mono ?_ hmem
      intro a ha
      have haE : a ∈ E := Finset.mem_coe.1 ha
      refine ⟨g ⟨a, haE⟩, ⟨?_, hg0 ⟨a, haE⟩⟩, hgdeg ⟨a, haE⟩⟩
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem g (Finset.mem_univ _))

/-- Over a field, a subalgebra `A` admits a finite SAGBI basis if and only if its initial algebra
`m.initialAlgebra A` is finitely generated. -/
theorem exists_finset_isSAGBIBasis_iff_fg_initialAlgebra :
    (∃ B : Finset (MvPolynomial σ k), m.IsSAGBIBasis (B : Set (MvPolynomial σ k)) A) ↔
      (m.initialAlgebra A).FG :=
  (m.exists_finset_isSAGBIBasis_iff_fg_leadingExponents A).trans
    (m.fg_initialAlgebra_iff_fg_leadingExponents A).symm

/-- Any subalgebra admitting a finite SAGBI basis has finitely generated initial algebra. -/
theorem IsSAGBIBasis.fg_initialAlgebra_of_finite {m : MonomialOrder σ}
    {B : Set (MvPolynomial σ k)} {A : Subalgebra k (MvPolynomial σ k)}
    (hfin : B.Finite) (h : m.IsSAGBIBasis B A) : (m.initialAlgebra A).FG :=
  (m.exists_finset_isSAGBIBasis_iff_fg_initialAlgebra A).1
    ⟨hfin.toFinset, by rwa [Set.Finite.coe_toFinset]⟩

end FiniteGeneration

/-! ### Certified SAGBI completion steps, fair schedules, and termination -/

section Completion

variable {σ k : Type*} [Field k]

/-- A certified SAGBI completion step: adjoin the monic normalization of a nonzero subduction
remainder of an element of the subalgebra generated by `G` with respect to the nonzero members of
`G`. As in `MonomialOrder.RemainderStep`, the enlarged finite family comes first. -/
def SAGBIStep (m : MonomialOrder σ) (H G : Finset (MvPolynomial σ k)) : Prop :=
  ∃ (f : MvPolynomial σ k)
    (Q : MvPolynomial ↥((G : Set (MvPolynomial σ k)) \ {0}) k)
    (r : MvPolynomial σ k),
    f ∈ Algebra.adjoin k (G : Set (MvPolynomial σ k)) ∧
    m.IsSubduction (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
      f Q r ∧
    r ≠ 0 ∧
    (H : Set (MvPolynomial σ k)) = insert (m.monicNormalize r) (G : Set (MvPolynomial σ k))

/-- Unfolding lemma for `MonomialOrder.SAGBIStep`. -/
theorem sagbiStep_iff {m : MonomialOrder σ} {H G : Finset (MvPolynomial σ k)} :
    m.SAGBIStep H G ↔
      ∃ (f : MvPolynomial σ k)
        (Q : MvPolynomial ↥((G : Set (MvPolynomial σ k)) \ {0}) k)
        (r : MvPolynomial σ k),
        f ∈ Algebra.adjoin k (G : Set (MvPolynomial σ k)) ∧
        m.IsSubduction (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
          f Q r ∧
        r ≠ 0 ∧
        (H : Set (MvPolynomial σ k)) = insert (m.monicNormalize r) (G : Set (MvPolynomial σ k)) :=
  Iff.rfl

namespace SAGBIStep

variable {m : MonomialOrder σ} {H G : Finset (MvPolynomial σ k)}

/-- Build a `SAGBIStep` from a subduction certificate with nonzero remainder. -/
theorem of_isSubduction [DecidableEq (MvPolynomial σ k)] {f r : MvPolynomial σ k}
    {Q : MvPolynomial ↥((G : Set (MvPolynomial σ k)) \ {0}) k}
    (hf : f ∈ Algebra.adjoin k (G : Set (MvPolynomial σ k)))
    (hs : m.IsSubduction (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
      f Q r)
    (hr : r ≠ 0) :
    m.SAGBIStep (insert (m.monicNormalize r) G) G :=
  ⟨f, Q, r, hf, hs, hr, Finset.coe_insert _ _⟩

/-- A `SAGBIStep` retains all previous generators. -/
theorem subset (h : m.SAGBIStep H G) : G ⊆ H := by
  obtain ⟨_, _, r, _, _, _, hH⟩ := h
  exact Finset.coe_subset.1 (hH ▸ Set.subset_insert (m.monicNormalize r) _)

/-- A `SAGBIStep` preserves the generated `k`-subalgebra. -/
theorem adjoin_eq (h : m.SAGBIStep H G) :
    Algebra.adjoin k (H : Set (MvPolynomial σ k)) =
      Algebra.adjoin k (G : Set (MvPolynomial σ k)) := by
  obtain ⟨f, Q, r, hf, hs, _, hH⟩ := h
  rw [hH]
  refine le_antisymm (Algebra.adjoin_le (Set.insert_subset_iff.2 ⟨?_, Algebra.subset_adjoin⟩))
    (Algebra.adjoin_mono (Set.subset_insert _ _))
  have hb : Set.range (Subtype.val : ↥((G : Set _) \ {0}) → MvPolynomial σ k) ⊆
      Algebra.adjoin k (G : Set (MvPolynomial σ k)) := by
    rw [Subtype.range_coe]
    exact Set.sdiff_subset.trans Algebra.subset_adjoin
  exact m.monicNormalize_mem_iff.2 ((hs.remainder_mem_iff hb).2 hf)

/-- A `SAGBIStep` strictly enlarges the subalgebra generated by the leading terms. -/
theorem adjoin_leadingTerm_lt (h : m.SAGBIStep H G) :
    Algebra.adjoin k (m.leadingTerm '' (G : Set (MvPolynomial σ k))) <
      Algebra.adjoin k (m.leadingTerm '' (H : Set (MvPolynomial σ k))) := by
  obtain ⟨f, Q, r, _, hs, hr, hH⟩ := h
  rw [hH, ← m.adjoin_image_leadingTerm_sdiff_singleton_zero (G : Set (MvPolynomial σ k)),
    ← m.adjoin_image_leadingTerm_sdiff_singleton_zero
      (insert (m.monicNormalize r) (G : Set (MvPolynomial σ k)))]
  have hins : (insert (m.monicNormalize r) (G : Set (MvPolynomial σ k))) \ {0} =
      insert (m.monicNormalize r) ((G : Set (MvPolynomial σ k)) \ {0}) :=
    Set.insert_sdiff_of_notMem _ (by simp [hr])
  rw [hins, ← Subtype.range_coe (s := (G : Set (MvPolynomial σ k)) \ {0})]
  exact hs.adjoin_leadingTerm_lt hr

end SAGBIStep

/-- Along a reflexive-transitive chain of `SAGBIStep`s, every previous generator is retained. -/
theorem subset_of_reflTransGen_sagbiStep {m : MonomialOrder σ}
    {H G : Finset (MvPolynomial σ k)} (h : Relation.ReflTransGen m.SAGBIStep H G) : G ⊆ H := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail _ hstep ih => exact hstep.subset.trans ih

/-- Along a reflexive-transitive chain of `SAGBIStep`s, the generated subalgebra is invariant. -/
theorem adjoin_eq_of_reflTransGen_sagbiStep {m : MonomialOrder σ}
    {H G : Finset (MvPolynomial σ k)} (h : Relation.ReflTransGen m.SAGBIStep H G) :
    Algebra.adjoin k (H : Set (MvPolynomial σ k)) =
      Algebra.adjoin k (G : Set (MvPolynomial σ k)) := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans hstep.adjoin_eq

/-- A certified binomial SAGBI completion step: select a toric relation `u, v` among the leading
exponents of the nonzero members of `G`, subduct the inverse-leading-coefficient rescaled binomial
`aeval Subtype.val (rescale (fun i ↦ (m.leadingCoeff i.1)⁻¹) (Y^u - Y^v))` against `G \ {0}`, and
adjoin `m.monicNormalize r` for its nonzero remainder `r`. -/
def BinomialSAGBIStep (m : MonomialOrder σ) (H G : Finset (MvPolynomial σ k)) : Prop :=
  ∃ (u v : ↥((G : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ)
    (Q : MvPolynomial ↥((G : Set (MvPolynomial σ k)) \ {0}) k)
    (r : MvPolynomial σ k),
    Finsupp.linearCombination ℕ
        (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) u =
      Finsupp.linearCombination ℕ
        (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) v ∧
    m.IsSubduction (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
      (aeval (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
        (rescale (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
          (monomial u (1 : k) - monomial v 1))) Q r ∧
    r ≠ 0 ∧
    (H : Set (MvPolynomial σ k)) = insert (m.monicNormalize r) (G : Set (MvPolynomial σ k))

/-- Unfolding lemma for `MonomialOrder.BinomialSAGBIStep`. -/
theorem binomialSAGBIStep_iff {m : MonomialOrder σ} {H G : Finset (MvPolynomial σ k)} :
    m.BinomialSAGBIStep H G ↔
      ∃ (u v : ↥((G : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ)
        (Q : MvPolynomial ↥((G : Set (MvPolynomial σ k)) \ {0}) k)
        (r : MvPolynomial σ k),
        Finsupp.linearCombination ℕ
            (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) u =
          Finsupp.linearCombination ℕ
            (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) v ∧
        m.IsSubduction (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
          (aeval (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
            (rescale (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
              (monomial u (1 : k) - monomial v 1))) Q r ∧
        r ≠ 0 ∧
        (H : Set (MvPolynomial σ k)) = insert (m.monicNormalize r) (G : Set (MvPolynomial σ k)) :=
  Iff.rfl

namespace BinomialSAGBIStep

variable {m : MonomialOrder σ} {H G : Finset (MvPolynomial σ k)}

/-- Every `BinomialSAGBIStep` is a `SAGBIStep`. -/
theorem toSAGBIStep (h : m.BinomialSAGBIStep H G) : m.SAGBIStep H G := by
  obtain ⟨u, v, Q, r, _, hs, hr, hH⟩ := h
  refine ⟨_, Q, r, ?_, hs, hr, hH⟩
  have hmem :
      aeval (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
        (rescale (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
          (monomial u (1 : k) - monomial v 1)) ∈
        (aeval (R := k)
          (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)).range :=
    ⟨_, rfl⟩
  rw [aeval_range, Subtype.range_coe] at hmem
  exact Algebra.adjoin_mono Set.sdiff_subset hmem

/-- A `BinomialSAGBIStep` retains all previous generators. -/
theorem subset (h : m.BinomialSAGBIStep H G) : G ⊆ H :=
  h.toSAGBIStep.subset

/-- A `BinomialSAGBIStep` preserves the generated `k`-subalgebra. -/
theorem adjoin_eq (h : m.BinomialSAGBIStep H G) :
    Algebra.adjoin k (H : Set (MvPolynomial σ k)) =
      Algebra.adjoin k (G : Set (MvPolynomial σ k)) :=
  h.toSAGBIStep.adjoin_eq

/-- A `BinomialSAGBIStep` strictly enlarges the subalgebra generated by the leading terms. -/
theorem adjoin_leadingTerm_lt (h : m.BinomialSAGBIStep H G) :
    Algebra.adjoin k (m.leadingTerm '' (G : Set (MvPolynomial σ k))) <
      Algebra.adjoin k (m.leadingTerm '' (H : Set (MvPolynomial σ k))) :=
  h.toSAGBIStep.adjoin_leadingTerm_lt

end BinomialSAGBIStep

/-- For a family of nonzero polynomials `b`, any rescaled binomial `D_ℓ⁻¹ (Y^u - Y^v)` with
`A u = A v` evaluates under `aeval b` to `0` or to a polynomial of leading exponent strictly below
`A u`. -/
private theorem aeval_rescale_sub_eq_zero_or_degree_lt {ι : Type*} (m : MonomialOrder σ)
    {b : ι → MvPolynomial σ k} (hb : ∀ i, b i ≠ 0) {u v : ι →₀ ℕ}
    (huv : Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) u =
      Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) v) :
    aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹) (monomial u (1 : k) - monomial v 1)) = 0 ∨
      m.degree (aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial u (1 : k) - monomial v 1))) ≺[m]
          Finsupp.linearCombination ℕ (fun i ↦ m.degree (b i)) u := by
  rw [m.aeval_rescale_inv_leadingCoeff b]
  have hc (i : ι) : m.Monic (m.monicNormalize (b i)) := m.monic_monicNormalize (hb i)
  simpa only [Function.comp_def, degree_monicNormalize] using
    m.aeval_monomial_sub_monomial_eq_zero_or_degree_lt hc u v
      (by simpa only [Function.comp_def, degree_monicNormalize] using huv)

/-- Evaluating a leading-coefficient-rescaled binomial along a subtype inclusion `S ⊆ T` commutes
with `Finsupp.mapDomain`. -/
private theorem aeval_rescale_mapDomain_sub {S T : Set (MvPolynomial σ k)} (m : MonomialOrder σ)
    (hST : S ⊆ T) (u v : ↥(S \ {0}) →₀ ℕ) :
    let ι : ↥(S \ {0}) → ↥(T \ {0}) := fun x ↦ ⟨x.1, hST x.2.1, x.2.2⟩
    aeval (Subtype.val : ↥(T \ {0}) → MvPolynomial σ k)
      (rescale (fun i : ↥(T \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
        (monomial (u.mapDomain ι) (1 : k) - monomial (v.mapDomain ι) 1)) =
    aeval (Subtype.val : ↥(S \ {0}) → MvPolynomial σ k)
      (rescale (fun i : ↥(S \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
        (monomial u (1 : k) - monomial v 1)) := by
  intro ι
  have hren : monomial (u.mapDomain ι) (1 : k) - monomial (v.mapDomain ι) 1 =
      rename ι (monomial u (1 : k) - monomial v 1) := by
    simp [map_sub, rename_monomial]
  have hcomm :
      (rescale (fun i : ↥(T \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)).comp (rename ι) =
      (rename ι).comp (rescale fun i : ↥(S \ {0}) ↦ (m.leadingCoeff i.1)⁻¹) :=
    algHom_ext fun x ↦ by simp [ι]
  rw [hren]
  exact (congrArg (aeval (Subtype.val : ↥(T \ {0}) → MvPolynomial σ k))
    (AlgHom.congr_fun hcomm (monomial u (1 : k) - monomial v 1))).trans (aeval_rename ι _ _)

/-- A finite polynomial family is terminal for `BinomialSAGBIStep` if and only if it is a SAGBI
basis of the subalgebra it generates. Neither monicity nor nonvanishing of the members of `G` is
assumed. -/
theorem isSAGBIBasis_iff_no_binomialSAGBIStep (m : MonomialOrder σ)
    (G : Finset (MvPolynomial σ k)) :
    m.IsSAGBIBasis (G : Set (MvPolynomial σ k))
      (Algebra.adjoin k (G : Set (MvPolynomial σ k))) ↔
      ∀ H, ¬ m.BinomialSAGBIStep H G := by
  classical
  set b : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k := Subtype.val
  have hb : ∀ i, b i ≠ 0 := fun i ↦ i.2.2
  refine ⟨fun h H hstep ↦ ?_, fun hno ↦ ?_⟩
  · obtain ⟨f, Q, r, hf, hs, hr, -⟩ := hstep.toSAGBIStep
    have hB : m.IsSAGBIBasis (Set.range b) (Algebra.adjoin k (G : Set (MvPolynomial σ k))) := by
      rw [Subtype.range_coe]
      exact isSAGBIBasis_sdiff_singleton_zero.2 h
    exact hr (hs.remainder_eq_zero hB hf)
  · obtain ⟨P, hP_eq, hP_span⟩ := TauCeti.exists_finset_toricIdeal_eq_span fun i ↦ m.degree (b i)
    have hJ : TauCeti.toricIdeal k (fun i ↦ m.degree (b i)) =
        Ideal.span (Set.range fun j : P ↦ monomial j.1.1 (1 : k) - monomial j.1.2 1) := by
      rw [hP_span k]
      apply congrArg Ideal.span
      ext x
      simp
    have hB : m.IsSAGBIBasis (Set.range b) (Algebra.adjoin k (Set.range b)) := by
      refine (isSAGBIBasis_range_iff_forall_exists_aeval_rescale hb hJ).2 fun j ↦ ?_
      set f := aeval b (rescale (fun i ↦ (m.leadingCoeff (b i))⁻¹)
        (monomial j.1.1 (1 : k) - monomial j.1.2 1))
      obtain ⟨Q, r, hs⟩ := m.exists_isSubduction hb f
      have hr0 : r = 0 := by
        by_contra hr
        exact hno (insert (m.monicNormalize r) G)
          ⟨j.1.1, j.1.2, Q, r, hP_eq j.1 j.2, hs, hr, Finset.coe_insert _ _⟩
      exact hs.exists_aeval_eq_of_range_subset subset_rfl (fun h ↦ (h hr0).elim)
        (aeval_rescale_sub_eq_zero_or_degree_lt m hb (hP_eq j.1 j.2))
    rw [Subtype.range_coe, ← Algebra.adjoin_insert_zero k ((G : Set (MvPolynomial σ k)) \ {0}),
      Set.insert_sdiff_singleton, Algebra.adjoin_insert_zero] at hB
    exact isSAGBIBasis_sdiff_singleton_zero.1 hB

/-- A finite polynomial family is terminal for `SAGBIStep` if and only if it is a SAGBI basis of
the subalgebra it generates. -/
theorem isSAGBIBasis_iff_no_sagbiStep (m : MonomialOrder σ) (G : Finset (MvPolynomial σ k)) :
    m.IsSAGBIBasis (G : Set (MvPolynomial σ k))
      (Algebra.adjoin k (G : Set (MvPolynomial σ k))) ↔
      ∀ H, ¬ m.SAGBIStep H G := by
  refine ⟨fun h H hstep ↦ ?_, fun hno ↦
    (m.isSAGBIBasis_iff_no_binomialSAGBIStep G).2 fun H hstep ↦ hno H hstep.toSAGBIStep⟩
  obtain ⟨f, Q, r, hf, hs, hr, -⟩ := hstep
  have hB : m.IsSAGBIBasis
      (Set.range (Subtype.val : ↥((G : Set _) \ {0}) → MvPolynomial σ k))
      (Algebra.adjoin k (G : Set (MvPolynomial σ k))) := by
    rw [Subtype.range_coe]
    exact isSAGBIBasis_sdiff_singleton_zero.2 h
  exact hr (hs.remainder_eq_zero hB hf)

/-- If `G` admits no outgoing `SAGBIStep`, then any `SAGBIStep`-chain starting from `G` is trivial.
-/
theorem eq_of_reflTransGen_sagbiStep_of_forall_not {m : MonomialOrder σ}
    {H G : Finset (MvPolynomial σ k)} (hrt : Relation.ReflTransGen m.SAGBIStep H G)
    (hno : ∀ K, ¬ m.SAGBIStep K G) : H = G := by
  cases hrt with
  | refl => rfl
  | tail _ hstep => exact (hno _ hstep).elim

/-- A countable sequence `B : ℕ → Finset (MvPolynomial σ k)` is a **fair SAGBI completion** if:
1. each transition from `B n` to `B (n + 1)` is a finite chain of certified `SAGBIStep`s (allowing
   stuttering `B (n + 1) = B n` as well as single-step or pass-by-pass adjunctions), and
2. for every stage `n`, there exists a finite binomial generating set `P` of the leading-exponent
   toric ideal of `B n \ {0}` such that every binomial `(u, v) ∈ P` is eventually subducted at some
   stage `N ≥ n`, with `m.monicNormalize r ∈ B (N + 1)` whenever its remainder `r` is nonzero. -/
structure IsFairSAGBICompletion (m : MonomialOrder σ)
    (B : ℕ → Finset (MvPolynomial σ k)) : Prop where
  /-- Every stage transitions to the next by zero or more certified `SAGBIStep`s. -/
  step : ∀ n, Relation.ReflTransGen m.SAGBIStep (B (n + 1)) (B n)
  /-- Every stage admits a finite binomial generating set of its leading-exponent toric ideal each
  of whose relations is processed by subduction at some later stage. -/
  fair : ∀ n,
    ∃ P : Finset ((↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
        (↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ)),
      (∀ p ∈ P,
        Finsupp.linearCombination ℕ
            (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.1 =
          Finsupp.linearCombination ℕ
            (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.2) ∧
      TauCeti.toricIdeal k
          (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) =
        Ideal.span ((fun p : (↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
            (↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ↦
          monomial p.1 (1 : k) - monomial p.2 1) '' (P : Set _)) ∧
      ∀ p ∈ P, ∃ N ≥ n,
        ∃ (Q : MvPolynomial ↥((B N : Set (MvPolynomial σ k)) \ {0}) k) (r : MvPolynomial σ k),
          m.IsSubduction (Subtype.val : ↥((B N : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
            (aeval (Subtype.val : ↥((B n : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
              (rescale (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
                (monomial p.1 (1 : k) - monomial p.2 1))) Q r ∧
          (r ≠ 0 → m.monicNormalize r ∈ B (N + 1))

namespace IsFairSAGBICompletion

variable {m : MonomialOrder σ} {B : ℕ → Finset (MvPolynomial σ k)}

/-- Every stage of a fair SAGBI completion is reached from `B 0` by `SAGBIStep`s. -/
theorem reflTransGen_zero (hB : m.IsFairSAGBICompletion B) (n : ℕ) :
    Relation.ReflTransGen m.SAGBIStep (B n) (B 0) := by
  induction n with
  | zero => exact .refl
  | succ n ih => exact (hB.step n).trans ih

/-- Every later stage of a fair SAGBI completion is reached from any earlier stage by
`SAGBIStep`s. -/
theorem reflTransGen_of_le (hB : m.IsFairSAGBICompletion B) {i j : ℕ} (hij : i ≤ j) :
    Relation.ReflTransGen m.SAGBIStep (B j) (B i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact .refl
  | succ d ih => exact (hB.step (i + d)).trans ih

/-- A fair SAGBI completion sequence is monotone with respect to finite-set inclusion. -/
theorem monotone (hB : m.IsFairSAGBICompletion B) : Monotone B :=
  fun _ _ hij ↦ subset_of_reflTransGen_sagbiStep (hB.reflTransGen_of_le hij)

/-- Every stage of a fair SAGBI completion generates the same subalgebra as `B 0`. -/
theorem adjoin_eq (hB : m.IsFairSAGBICompletion B) (n : ℕ) :
    Algebra.adjoin k (B n : Set (MvPolynomial σ k)) =
      Algebra.adjoin k (B 0 : Set (MvPolynomial σ k)) :=
  adjoin_eq_of_reflTransGen_sagbiStep (hB.reflTransGen_zero n)

/-- Pushing a finitely supported exponent vector on a directed union back to a finite stage. -/
private theorem exists_stage_mapDomain_eq (hB : m.IsFairSAGBICompletion B)
    (u v : ↥((⋃ n, (B n : Set (MvPolynomial σ k))) \ {0}) →₀ ℕ) :
    ∃ n : ℕ, ∃ u₀ v₀ : ↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ,
      u₀.mapDomain (fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨n, x.2.1⟩, x.2.2⟩) = u ∧
      v₀.mapDomain (fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨n, x.2.1⟩, x.2.2⟩) = v := by
  classical
  let U := (⋃ n, (B n : Set (MvPolynomial σ k))) \ {0}
  choose stage hstage using fun x : ↥U ↦ Set.mem_iUnion.1 x.2.1
  let n := (u.support ∪ v.support).sup stage
  have hmem (x : ↥U) (hx : x ∈ u.support ∪ v.support) :
      x.1 ∈ (B n : Set (MvPolynomial σ k)) \ {0} :=
    ⟨hB.monotone (Finset.le_sup (f := stage) hx) (hstage x), x.2.2⟩
  let ι : ↥((B n : Set (MvPolynomial σ k)) \ {0}) → ↥U :=
    fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨n, x.2.1⟩, x.2.2⟩
  have hι : Function.Injective ι :=
    fun _ _ hxy ↦ Subtype.ext (congrArg (Subtype.val : ↥U → MvPolynomial σ k) hxy)
  have hrange_u : (u.support : Set ↥U) ⊆ Set.range ι := fun x hx ↦
    ⟨⟨x.1, hmem x (Finset.mem_union_left _ hx)⟩, Subtype.ext rfl⟩
  have hrange_v : (v.support : Set ↥U) ⊆ Set.range ι := fun x hx ↦
    ⟨⟨x.1, hmem x (Finset.mem_union_right _ hx)⟩, Subtype.ext rfl⟩
  exact ⟨n, u.comapDomain ι hι.injOn, v.comapDomain ι hι.injOn,
    Finsupp.mapDomain_comapDomain ι hι u hrange_u,
    Finsupp.mapDomain_comapDomain ι hι v hrange_v⟩

/-- If `P n` generates the leading-exponent toric ideal of `B n \ {0}` at every stage `n`, then
their images in the union `⋃ n, B n` generate the leading-exponent toric ideal of
`(⋃ n, B n) \ {0}`. -/
private theorem toricIdeal_iUnion_eq_span (hB : m.IsFairSAGBICompletion B)
    (P : ∀ n, Finset ((↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
      (↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ)))
    (hP_eq : ∀ n, ∀ p ∈ P n,
      Finsupp.linearCombination ℕ
          (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.1 =
        Finsupp.linearCombination ℕ
          (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.2)
    (hP_span : ∀ n,
      TauCeti.toricIdeal k (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) =
        Ideal.span ((fun p : (↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
            (↥((B n : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ↦
          monomial p.1 (1 : k) - monomial p.2 1) '' (P n : Set _))) :
    TauCeti.toricIdeal k
        (fun i : ↥((⋃ n, (B n : Set (MvPolynomial σ k))) \ {0}) ↦ m.degree i.1) =
      Ideal.span (Set.range fun j : Σ n : ℕ, ↥(P n) ↦
        monomial
            (j.2.1.1.mapDomain fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨j.1, x.2.1⟩, x.2.2⟩) (1 : k) -
          monomial
            (j.2.1.2.mapDomain fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨j.1, x.2.1⟩, x.2.2⟩) 1) := by
  let ι (n : ℕ) : ↥((B n : Set (MvPolynomial σ k)) \ {0}) →
      ↥((⋃ l, (B l : Set (MvPolynomial σ k))) \ {0}) :=
    fun x ↦ ⟨x.1, Set.mem_iUnion.2 ⟨n, x.2.1⟩, x.2.2⟩
  refine le_antisymm ?_ (Ideal.span_le.2 ?_)
  · rw [TauCeti.toricIdeal_eq_span]
    refine Ideal.span_le.2 ?_
    rintro _ ⟨u, v, huv, rfl⟩
    obtain ⟨n, u₀, v₀, rfl, rfl⟩ := hB.exists_stage_mapDomain_eq u v
    have huv₀ :
        Finsupp.linearCombination ℕ
            (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) u₀ =
          Finsupp.linearCombination ℕ
            (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) v₀ := by
      simpa [Finsupp.linearCombination_mapDomain, Function.comp_def, ι] using huv
    have hmem₀ := TauCeti.monomial_sub_monomial_mem_toricIdeal (R := k) huv₀
    rw [hP_span n] at hmem₀
    have hmap := Ideal.mem_map_of_mem (rename (ι n)) hmem₀
    rw [Ideal.map_span, map_sub, rename_monomial, rename_monomial] at hmap
    refine (Ideal.span_mono ?_) hmap
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨⟨n, ⟨p, hp⟩⟩, by simp [ι, map_sub, rename_monomial]⟩
  · rintro _ ⟨⟨n, ⟨p, hp⟩⟩, rfl⟩
    refine TauCeti.monomial_sub_monomial_mem_toricIdeal ?_
    simpa [Finsupp.linearCombination_mapDomain, Function.comp_def, ι] using hP_eq n p hp

/-- **Soundness of fair SAGBI completion.** For any fair SAGBI completion `B`, the countable union
`⋃ n, B n` is unconditionally a SAGBI basis of `Algebra.adjoin k (B 0)`, even when the initial
algebra is not finitely generated. -/
theorem isSAGBIBasis_iUnion (hB : m.IsFairSAGBICompletion B) :
    m.IsSAGBIBasis (⋃ n, (B n : Set (MvPolynomial σ k)))
      (Algebra.adjoin k (B 0 : Set (MvPolynomial σ k))) := by
  classical
  set U := ⋃ n, (B n : Set (MvPolynomial σ k))
  have hUA : Algebra.adjoin k U = Algebra.adjoin k (B 0 : Set (MvPolynomial σ k)) := by
    refine le_antisymm (Algebra.adjoin_le fun f hf ↦ ?_)
      (Algebra.adjoin_mono (Set.subset_iUnion (fun n ↦ (B n : Set (MvPolynomial σ k))) 0))
    obtain ⟨n, hfn⟩ := Set.mem_iUnion.1 hf
    rw [← hB.adjoin_eq n]
    exact Algebra.subset_adjoin hfn
  have hU0 : Algebra.adjoin k (U \ {0}) = Algebra.adjoin k U := by
    rw [← Algebra.adjoin_insert_zero k (U \ {0}), Set.insert_sdiff_singleton,
      Algebra.adjoin_insert_zero]
  rw [← hUA, ← isSAGBIBasis_sdiff_singleton_zero, ← hU0,
    ← Subtype.range_coe (s := U \ {0})]
  choose P hP_eq hP_span hP_fair using hB.fair
  refine (isSAGBIBasis_range_iff_forall_exists_aeval_rescale (fun i ↦ i.2.2)
    (hB.toricIdeal_iUnion_eq_span P hP_eq hP_span)).2 fun ⟨n, ⟨p, hp⟩⟩ ↦ ?_
  obtain ⟨N, _, Q, r, hs, hrB⟩ := hP_fair n p hp
  have hsub_n : (B n : Set (MvPolynomial σ k)) ⊆ U :=
    Set.subset_iUnion (fun l ↦ (B l : Set (MvPolynomial σ k))) n
  have hfeq := aeval_rescale_mapDomain_sub m hsub_n p.1 p.2
  have hdeg_u :
      Finsupp.linearCombination ℕ (fun i : ↥(U \ {0}) ↦ m.degree i.1)
          (p.1.mapDomain fun x ↦ ⟨x.1, hsub_n x.2.1, x.2.2⟩) =
        Finsupp.linearCombination ℕ
          (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.1 := by
    simp [Finsupp.linearCombination_mapDomain, Function.comp_def]
  rw [hfeq, hdeg_u]
  refine hs.exists_aeval_eq_of_range_subset ?_ ?_
    (aeval_rescale_sub_eq_zero_or_degree_lt m (fun i ↦ i.2.2) (hP_eq n p hp))
  · rw [Subtype.range_coe, Subtype.range_coe]
    exact fun x hx ↦ ⟨Set.mem_iUnion.2 ⟨N, hx.1⟩, hx.2⟩
  · intro hr0
    rw [Subtype.range_coe]
    exact ⟨Set.mem_iUnion.2 ⟨N + 1, hrB hr0⟩, by simp [hr0]⟩

/-- **Termination of fair SAGBI completion.** A fair SAGBI completion sequence `B` stabilizes at a
finite SAGBI basis `B N` of `Algebra.adjoin k (B 0)` if and only if the initial algebra of
`Algebra.adjoin k (B 0)` is finitely generated. -/
theorem exists_isSAGBIBasis_iff_fg_initialAlgebra (hB : m.IsFairSAGBICompletion B) :
    (m.initialAlgebra (Algebra.adjoin k (B 0 : Set (MvPolynomial σ k)))).FG ↔
      ∃ N, m.IsSAGBIBasis (B N : Set (MvPolynomial σ k))
        (Algebra.adjoin k (B 0 : Set (MvPolynomial σ k))) ∧
        ∀ n ≥ N, B n = B N := by
  refine ⟨fun hfg ↦ ?_, fun ⟨N, hBN, _⟩ ↦
    (m.exists_finset_isSAGBIBasis_iff_fg_initialAlgebra _).1 ⟨B N, hBN⟩⟩
  classical
  obtain ⟨S, hS⟩ := hfg
  let L (n : ℕ) : Subalgebra k (MvPolynomial σ k) :=
    Algebra.adjoin k (m.leadingTerm '' (B n : Set (MvPolynomial σ k)))
  have hL_mono : Monotone L := fun _ _ hij ↦
    Algebra.adjoin_mono (Set.image_mono (Finset.coe_subset.2 (hB.monotone hij)))
  have hiSup : (⨆ n, L n) =
      m.initialAlgebra (Algebra.adjoin k (B 0 : Set (MvPolynomial σ k))) := by
    rw [← hB.isSAGBIBasis_iUnion.adjoin_leadingTerm, Set.image_iUnion, Algebra.adjoin_iUnion]
  have hS_mem (s : S) : ∃ n, s.1 ∈ L n := by
    have hs : s.1 ∈ (⨆ n, L n : Subalgebra k (MvPolynomial σ k)) := by
      rw [hiSup, ← hS]
      exact Algebra.subset_adjoin s.2
    exact Set.mem_iUnion.1 ((Subalgebra.coe_iSup_of_directed hL_mono.directed_le) ▸ hs)
  choose stage hstage using hS_mem
  let N := S.attach.sup stage
  have hBN : m.IsSAGBIBasis (B N : Set (MvPolynomial σ k))
      (Algebra.adjoin k (B 0 : Set (MvPolynomial σ k))) := by
    refine isSAGBIBasis_iff_initialAlgebra_le.2 ⟨?_, ?_⟩
    · rw [← hB.adjoin_eq N]
      exact Algebra.subset_adjoin
    · rw [← hS]
      exact Algebra.adjoin_le fun s hs ↦
        hL_mono (Finset.le_sup (f := stage) (Finset.mem_attach S ⟨s, hs⟩)) (hstage ⟨s, hs⟩)
  have hno : ∀ H, ¬ m.SAGBIStep H (B N) := by
    rw [← m.isSAGBIBasis_iff_no_sagbiStep (B N), hB.adjoin_eq N]
    exact hBN
  exact ⟨N, hBN, fun n hn ↦
    eq_of_reflTransGen_sagbiStep_of_forall_not (hB.reflTransGen_of_le hn) hno⟩

end IsFairSAGBICompletion

/-- Specialized finite binomial generation of the leading-exponent toric ideal over `k`, fixing the
coefficient universe to that of `k`. -/
private theorem exists_finset_toricIdeal_field (m : MonomialOrder σ)
    (F : Finset (MvPolynomial σ k)) :
    ∃ P : Finset ((↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
        (↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ)),
      (∀ p ∈ P,
        Finsupp.linearCombination ℕ
            (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.1 =
          Finsupp.linearCombination ℕ
            (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.2) ∧
      TauCeti.toricIdeal k (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) =
        Ideal.span ((fun p : (↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
            (↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ↦
          monomial p.1 (1 : k) - monomial p.2 1) '' (P : Set _)) := by
  obtain ⟨P, h1, h2⟩ := TauCeti.exists_finset_toricIdeal_eq_span
    (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1)
  exact ⟨P, h1, h2 k⟩

private noncomputable def chosenToricPairs (m : MonomialOrder σ)
    (F : Finset (MvPolynomial σ k)) :
    Finset ((↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
      (↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ)) :=
  (exists_finset_toricIdeal_field (k := k) m F).choose

private theorem chosenToricPairs_spec (m : MonomialOrder σ) (F : Finset (MvPolynomial σ k)) :
    (∀ p ∈ chosenToricPairs (k := k) m F,
      Finsupp.linearCombination ℕ
          (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.1 =
        Finsupp.linearCombination ℕ
          (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) p.2) ∧
    TauCeti.toricIdeal k (fun i : ↥((F : Set (MvPolynomial σ k)) \ {0}) ↦ m.degree i.1) =
      Ideal.span ((fun p : (↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ×
          (↥((F : Set (MvPolynomial σ k)) \ {0}) →₀ ℕ) ↦
        monomial p.1 (1 : k) - monomial p.2 1) '' (chosenToricPairs (k := k) m F : Set _)) :=
  (exists_finset_toricIdeal_field (k := k) m F).choose_spec

/-- Chosen subduction expression and remainder of `f` against `G \ {0}`. -/
private noncomputable def chosenSubduction (m : MonomialOrder σ)
    (G : Finset (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    MvPolynomial ↥((G : Set (MvPolynomial σ k)) \ {0}) k × MvPolynomial σ k :=
  let h := m.exists_isSubduction
    (b := (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k))
    (fun i ↦ i.2.2) f
  (h.choose, h.choose_spec.choose)

private theorem chosenSubduction_spec (m : MonomialOrder σ)
    (G : Finset (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    m.IsSubduction (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
      f (chosenSubduction m G f).1 (chosenSubduction m G f).2 :=
  (m.exists_isSubduction
    (b := (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k))
    (fun i ↦ i.2.2) f).choose_spec.choose_spec

/-- Single dovetailed step processing the `idx`-th chosen toric pair of an earlier stage `F`
against the current stage `G` (when `F ⊆ G`). -/
private noncomputable def dovetailStep [DecidableEq (MvPolynomial σ k)] (m : MonomialOrder σ)
    (F G : Finset (MvPolynomial σ k)) (idx : ℕ) : Finset (MvPolynomial σ k) :=
  if hsub : F ⊆ G then
    match (chosenToricPairs (k := k) m F).toList[idx]? with
    | none => G
    | some p =>
      let ι : ↥((F : Set (MvPolynomial σ k)) \ {0}) → ↥((G : Set (MvPolynomial σ k)) \ {0}) :=
        fun x ↦ ⟨x.1, Finset.coe_subset.2 hsub x.2.1, x.2.2⟩
      let f := aeval (Subtype.val : ↥((G : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
        (rescale (fun i : ↥((G : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
          (monomial (p.1.mapDomain ι) (1 : k) - monomial (p.2.mapDomain ι) 1))
      let sr := chosenSubduction m G f
      if sr.2 = 0 then G else insert (m.monicNormalize sr.2) G
  else G

/-- Explicit dovetailed SAGBI completion sequence starting at `G₀`, scheduled by `Nat.unpair`. -/
private noncomputable def fairSAGBISeq [DecidableEq (MvPolynomial σ k)] (m : MonomialOrder σ)
    (G₀ : Finset (MvPolynomial σ k)) : ℕ → Finset (MvPolynomial σ k)
  | 0 => G₀
  | n + 1 =>
    have : (Nat.unpair n).1 < n + 1 := Nat.lt_succ_of_le (Nat.unpair_left_le n)
    dovetailStep m (fairSAGBISeq m G₀ (Nat.unpair n).1) (fairSAGBISeq m G₀ n) (Nat.unpair n).2

private theorem dovetailStep_eq_or_binomialSAGBIStep [DecidableEq (MvPolynomial σ k)]
    (m : MonomialOrder σ) (F G : Finset (MvPolynomial σ k)) (idx : ℕ) :
    dovetailStep m F G idx = G ∨ m.BinomialSAGBIStep (dovetailStep m F G idx) G := by
  unfold dovetailStep
  split_ifs with hsub
  · cases hget : (chosenToricPairs (k := k) m F).toList[idx]? with
    | none => exact .inl rfl
    | some p =>
      dsimp only
      split_ifs with hr0
      · exact .inl rfl
      · right
        have hp : p ∈ chosenToricPairs (k := k) m F :=
          Finset.mem_toList.1 (List.mem_of_getElem? hget)
        let ι : ↥((F : Set (MvPolynomial σ k)) \ {0}) → ↥((G : Set (MvPolynomial σ k)) \ {0}) :=
          fun x ↦ ⟨x.1, Finset.coe_subset.2 hsub x.2.1, x.2.2⟩
        refine ⟨p.1.mapDomain ι, p.2.mapDomain ι, _, _, ?_,
          chosenSubduction_spec m G _, hr0, Finset.coe_insert _ _⟩
        simpa [Finsupp.linearCombination_mapDomain, Function.comp_def, ι] using
          (chosenToricPairs_spec (k := k) m F).1 p hp
  · exact .inl rfl

/-- **Existence of fair binomial SAGBI completion.** Every finite set `G₀` of polynomials over a
field admits a fair SAGBI completion sequence starting at `G₀` in which each transition is either
an equality `B (n + 1) = B n` or a single certified `BinomialSAGBIStep`. -/
theorem exists_isFairSAGBICompletion (m : MonomialOrder σ) (G₀ : Finset (MvPolynomial σ k)) :
    ∃ B : ℕ → Finset (MvPolynomial σ k),
      B 0 = G₀ ∧
      (∀ n, B (n + 1) = B n ∨ m.BinomialSAGBIStep (B (n + 1)) (B n)) ∧
      m.IsFairSAGBICompletion B := by
  classical
  let B := fairSAGBISeq m G₀
  have hstep_bin (n : ℕ) : B (n + 1) = B n ∨ m.BinomialSAGBIStep (B (n + 1)) (B n) := by
    simpa [B, fairSAGBISeq] using
      dovetailStep_eq_or_binomialSAGBIStep m (B (Nat.unpair n).1) (B n) (Nat.unpair n).2
  have hstep_rt (n : ℕ) : Relation.ReflTransGen m.SAGBIStep (B (n + 1)) (B n) :=
    (hstep_bin n).elim (fun h ↦ h ▸ .refl) fun h ↦ .single h.toSAGBIStep
  have hmono : Monotone B := monotone_nat_of_le_succ fun n ↦
    (hstep_bin n).elim Eq.ge BinomialSAGBIStep.subset
  refine ⟨B, by simp [B, fairSAGBISeq], hstep_bin, ⟨hstep_rt, fun n ↦ ?_⟩⟩
  refine ⟨chosenToricPairs (k := k) m (B n), (chosenToricPairs_spec (k := k) m (B n)).1,
    (chosenToricPairs_spec (k := k) m (B n)).2, fun p hp ↦ ?_⟩
  obtain ⟨idx, hidx, hget_elem⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hp)
  let N := Nat.pair n idx
  have hnN : n ≤ N := Nat.left_le_pair n idx
  have hsub : B n ⊆ B N := hmono hnN
  have hget : (chosenToricPairs (k := k) m (B n)).toList[idx]? = some p := by
    rw [List.getElem?_eq_getElem hidx, hget_elem]
  let ι : ↥((B n : Set (MvPolynomial σ k)) \ {0}) → ↥((B N : Set (MvPolynomial σ k)) \ {0}) :=
    fun x ↦ ⟨x.1, Finset.coe_subset.2 hsub x.2.1, x.2.2⟩
  let fN := aeval (Subtype.val : ↥((B N : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
    (rescale (fun i : ↥((B N : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
      (monomial (p.1.mapDomain ι) (1 : k) - monomial (p.2.mapDomain ι) 1))
  have hf_eq : fN = aeval (Subtype.val : ↥((B n : Set (MvPolynomial σ k)) \ {0}) → MvPolynomial σ k)
      (rescale (fun i : ↥((B n : Set (MvPolynomial σ k)) \ {0}) ↦ (m.leadingCoeff i.1)⁻¹)
        (monomial p.1 (1 : k) - monomial p.2 1)) :=
    aeval_rescale_mapDomain_sub m (Finset.coe_subset.2 hsub) p.1 p.2
  refine ⟨N, hnN, (chosenSubduction m (B N) fN).1, (chosenSubduction m (B N) fN).2,
    hf_eq ▸ chosenSubduction_spec m (B N) fN, fun hr0 ↦ ?_⟩
  have hBN1 : B (N + 1) = dovetailStep m (B n) (B N) idx := by
    simp [B, fairSAGBISeq, N, Nat.unpair_pair]
  rw [hBN1]
  unfold dovetailStep
  rw [dite_eq_left hsub, hget]
  dsimp only
  split_ifs with h0
  · exact (hr0 h0).elim
  · exact Finset.mem_insert_self _ _

/-- **Finite certified binomial SAGBI completion.** A finite set `G` of polynomials over a field
admits a finite chain of certified `BinomialSAGBIStep`s ending at a SAGBI basis of
`Algebra.adjoin k G` if and only if `m.initialAlgebra (Algebra.adjoin k G)` is finitely generated.
-/
theorem exists_binomialSAGBIStep_completion_iff_fg_initialAlgebra (m : MonomialOrder σ)
    (G : Finset (MvPolynomial σ k)) :
    (∃ H : Finset (MvPolynomial σ k),
      Relation.ReflTransGen m.BinomialSAGBIStep H G ∧
      G ⊆ H ∧
      m.IsSAGBIBasis (H : Set (MvPolynomial σ k))
        (Algebra.adjoin k (G : Set (MvPolynomial σ k)))) ↔
    (m.initialAlgebra (Algebra.adjoin k (G : Set (MvPolynomial σ k)))).FG := by
  refine ⟨fun ⟨H, _, _, hH⟩ ↦
    (m.exists_finset_isSAGBIBasis_iff_fg_initialAlgebra _).1 ⟨H, hH⟩, fun hfg ↦ ?_⟩
  obtain ⟨B, rfl, hbin, hB⟩ := m.exists_isFairSAGBICompletion G
  obtain ⟨N, hBN, -⟩ := (hB.exists_isSAGBIBasis_iff_fg_initialAlgebra).1 hfg
  have hrt (n : ℕ) : Relation.ReflTransGen m.BinomialSAGBIStep (B n) (B 0) := by
    induction n with
    | zero => exact .refl
    | succ n ih =>
      rcases hbin n with heq | hs
      · rwa [heq]
      · exact Relation.ReflTransGen.head hs ih
  exact ⟨B N, hrt N, hB.monotone (Nat.zero_le N), hBN⟩

end Completion

end MonomialOrder
