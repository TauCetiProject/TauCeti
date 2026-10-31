/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Groebner.Buchberger
public import TauCeti.Data.Finsupp.MonomialOrder.Weight

/-!
# Finite comparison certificates for Gröbner bases

A zero remainder has a finite standard representation. Keeping the leading exponents of its
polynomials and the degree bounds in that representation requires only finitely many strict
monomial comparisons. For a finite Gröbner basis, collect these comparisons for all its
S-polynomials. Any monomial order satisfying the collected comparisons has the same Gröbner
basis and the same entire ideal of leading terms, not just the same leading terms of the chosen
generators.

The comparisons also admit a strictly positive integral weight vector. They give finite strict
linear inequalities whose solutions certify stability: every monomial order respecting those
weight comparisons preserves the Gröbner basis. No single weight is claimed to represent the
original order on all monomials, and no weight-initial form is identified with a leading term.

## Main results

* `MonomialOrder.IsRemainder.exists_finset_comparisons`: finite comparisons preserving a zero
  remainder and the leading exponents of its finite divisor set.
* `MonomialOrder.IsGroebnerBasis.exists_finset_comparisons`: finite comparisons preserving a
  finite Gröbner basis and its leading-term ideal.
* `MonomialOrder.IsGroebnerBasis.exists_pos_weight_preserving`: a strictly positive integral
  weight whose strict comparisons suffice for the same stability conclusion.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, AMS, 1996, Chapter 2
  (Gröbner cones and finite comparison inequalities).
* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 2, §6
  (Buchberger's criterion and standard representations).
-/

public section

namespace MonomialOrder

open MvPolynomial

variable {σ R : Type*} {m : MonomialOrder σ}

section CommSemiring

variable [CommSemiring R] {B : Set (MvPolynomial σ R)}

/-- A zero remainder on division by a finite set has a finite comparison certificate. Every order
satisfying its strict comparisons preserves the zero remainder and the leading exponents of all
divisors. The certificate retains the degree bounds of a standard representation. -/
theorem IsRemainder.exists_finset_comparisons {f : MvPolynomial σ R}
    (h : m.IsRemainder f B 0) (hB : B.Finite) :
    ∃ C : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)),
      (∀ p ∈ C, p.1 ≺[m] p.2) ∧
      ∀ n : MonomialOrder σ, (∀ p ∈ C, p.1 ≺[n] p.2) →
        n.IsRemainder f B 0 ∧ ∀ b ∈ B, n.degree b = m.degree b := by
  classical
  let := hB.fintype
  obtain ⟨q, hq, hbound⟩ := h.exists_linearCombination
  -- Include supports to fix leading exponents, and sums to transfer representation bounds.
  let S : B → Finset (σ →₀ ℕ) := fun b ↦
    (insert (m.degree (b : MvPolynomial σ R)) (b : MvPolynomial σ R).support ∪
      insert (m.degree (q b)) (q b).support) ∪
      {m.degree (b : MvPolynomial σ R) + m.degree (q b)}
  let F := insert (m.degree f) f.support ∪ Finset.univ.biUnion S
  have hfF : insert (m.degree f) f.support ⊆ F := Finset.subset_union_left
  have hbF (b : B) : S b ⊆ F :=
    (Finset.subset_biUnion_of_mem S (Finset.mem_univ b)).trans Finset.subset_union_right
  -- Strict comparisons between these exponents also preserve all their weak comparisons.
  let C := (F ×ˢ F).filter fun p ↦ p.1 ≺[m] p.2
  refine ⟨C, fun p hp ↦ (Finset.mem_filter.1 hp).2, fun n hn ↦ ?_⟩
  have hcomp (a) (ha : a ∈ F) (b) (hb : b ∈ F) (hab : a ≺[m] b) : a ≺[n] b :=
    hn (a, b) (Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩)
  have hle : MonotoneOn (n.toSyn ∘ m.toSyn.symm) (m.toSyn.symm ⁻¹' (↑F : Set _)) :=
    StrictMonoOn.monotoneOn fun a ha b hb hab ↦ hcomp _ ha _ hb (by simpa using hab)
  have hd (p : MvPolynomial σ R) (hp : insert (m.degree p) p.support ⊆ F) :
      n.degree p = m.degree p :=
    m.degree_eq_of_forall_mem_lt n p hcomp (fun _ ha ↦ hp (Finset.mem_insert_of_mem ha))
      (hp (Finset.mem_insert_self _ _))
  have hdb (b : B) : n.degree (b : MvPolynomial σ R) = m.degree (b : MvPolynomial σ R) :=
    hd _ ((Finset.subset_union_left.trans Finset.subset_union_left).trans (hbF b))
  have hdq (b : B) : n.degree (q b) = m.degree (q b) :=
    hd _ ((Finset.subset_union_right.trans Finset.subset_union_left).trans (hbF b))
  -- Reuse the same quotients; zero factors need no degree comparison.
  refine ⟨isRemainder_iff.2 ⟨⟨q, hq, fun b ↦ ?_⟩, by simp⟩,
    fun b hb ↦ hdb ⟨b, hb⟩⟩
  by_cases hb0 : (b : MvPolynomial σ R) = 0
  · simp [hb0]
  by_cases hqb0 : q b = 0
  · simp [hqb0]
  have hf0 : f ≠ 0 := by
    intro hf0
    have := hbound b
    simp [hf0, hb0, hqb0] at this
  apply (toWithBotSyn_withBotDegree_add_le_iff hb0 hqb0 hf0).2
  rw [hdb, hdq, hd _ hfF, ← map_add]
  have hbound' : m.degree (b : MvPolynomial σ R) + m.degree (q b) ≼[m] m.degree f := by
    simpa only [map_add] using
      (toWithBotSyn_withBotDegree_add_le_iff hb0 hqb0 hf0).1 (hbound b)
  simpa only [Function.comp_apply, AddEquiv.symm_apply_apply] using
    hle (a := m.toSyn _) (b := m.toSyn _) (by
      simpa using hbF b (Finset.mem_union_right _ (Finset.mem_singleton_self _))) (by
      simpa using hfF (Finset.mem_insert_self _ _)) hbound'

end CommSemiring

section CommRing

variable [CommRing R] {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}

/-- A finite Gröbner basis with unit leading coefficients has a finite strict comparison
certificate. Every monomial order satisfying the certificate preserves both the Gröbner basis
and the entire ideal of leading terms. This includes the empty basis and the zero ideal. -/
theorem IsGroebnerBasis.exists_finset_comparisons (h : m.IsGroebnerBasis G I)
    (hG : G.Finite) (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∃ C : Finset ((σ →₀ ℕ) × (σ →₀ ℕ)),
      (∀ p ∈ C, p.1 ≺[m] p.2) ∧
      ∀ n : MonomialOrder σ, (∀ p ∈ C, p.1 ≺[n] p.2) →
        n.IsGroebnerBasis G I ∧
        Ideal.span (n.leadingTerm '' (I : Set (MvPolynomial σ R))) =
          Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) := by
  classical
  let := hG.fintype
  have hc (p : G × G) :=
    (h.isRemainder_sPolynomial_zero p.1.2 p.2.2).exists_finset_comparisons hG
  choose C hCm hCn using hc
  let D := Finset.univ.biUnion C
  refine ⟨D, fun p hp ↦ ?_, fun n hn ↦ ?_⟩
  · obtain ⟨j, -, hp⟩ := Finset.mem_biUnion.1 hp
    exact hCm j p hp
  have hC (j : G × G) := hCn j n fun p hp ↦
    hn p (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hp⟩)
  have hd (g : MvPolynomial σ R) (hg : g ∈ G) : n.degree g = m.degree g :=
    (hC (⟨g, hg⟩, ⟨g, hg⟩)).2 g hg
  have hlt (g : MvPolynomial σ R) (hg : g ∈ G) : n.leadingTerm g = m.leadingTerm g :=
    m.leadingTerm_eq_of_degree_eq n (hd g hg)
  have hnG : n.IsGroebnerBasis G I := by
    rw [h.ideal_eq_span]
    apply isGroebnerBasis_span_of_isRemainder_sPolynomial_zero
    · intro g hg hg0
      rw [m.leadingCoeff_eq_of_degree_eq n (hd g hg)]
      exact hu g hg hg0
    · intro g₁ hg₁ g₂ hg₂
      rw [m.sPolynomial_eq_of_degree_eq n (hd g₁ hg₁) (hd g₂ hg₂)]
      exact (hC (⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩)).1
  refine ⟨hnG, ?_⟩
  rw [hnG.span_leadingTerm_image, h.span_leadingTerm_image]
  congr 1
  exact Set.image_congr hlt

/-- A finite Gröbner basis with unit leading coefficients admits a positive integral weight
whose strict comparisons certify stability. Every monomial order respecting all strict weight
comparisons has this Gröbner basis and its original leading-term ideal. See also
`IsGroebnerBasis.exists_finset_comparisons` for the finite comparison certificate. -/
theorem IsGroebnerBasis.exists_pos_weight_preserving (h : m.IsGroebnerBasis G I)
    (hG : G.Finite) (hu : ∀ g ∈ G, g ≠ 0 → IsUnit (m.leadingCoeff g)) :
    ∃ w : σ → ℕ, (∀ i, 0 < w i) ∧
      ∀ n : MonomialOrder σ,
        (∀ a b, Finsupp.weight w a < Finsupp.weight w b → a ≺[n] b) →
        n.IsGroebnerBasis G I ∧
        Ideal.span (n.leadingTerm '' (I : Set (MvPolynomial σ R))) =
          Ideal.span (m.leadingTerm '' (I : Set (MvPolynomial σ R))) := by
  obtain ⟨C, hCm, hCn⟩ := h.exists_finset_comparisons hG hu
  obtain ⟨w, hw, hcomp⟩ := m.exists_pos_weight_lt
    (a := fun p : C ↦ p.1.1) (b := fun p : C ↦ p.1.2) fun p ↦ hCm p p.2
  exact ⟨w, hw, fun n hn ↦ hCn n fun p hp ↦ hn _ _ (hcomp ⟨p, hp⟩)⟩

end CommRing

end MonomialOrder
