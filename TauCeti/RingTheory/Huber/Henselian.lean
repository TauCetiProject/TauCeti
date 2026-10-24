/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.Huber.RingOfDefinition
import TauCeti.RingTheory.Subring.SpanSingleton

/-!
# Power-bounded subrings of complete Tate rings are Henselian

Let `A` be a complete Hausdorff Huber ring and `ϖ` a pseudouniformiser of `A`. This file shows
that the subring `A°` of power-bounded elements is Henselian along `ϖ A°`, and more generally that
so is every open subring `B ⊆ A°` containing `ϖ`, along `ϖ B`. This is the form of Hensel's lemma
used for finite étale algebras over complete Tate rings: a monic polynomial over `A°` with a simple
root modulo `ϖ` has a root in `A°` lifting it.

The proof has two steps.

* A ring of definition `A₀` containing `ϖ` is `ϖ`-adically complete
  (`TauCeti.Huber.PairOfDefinition.isAdicComplete_span_singleton`): its topology is the `ϖ`-adic
  one, and being open in the complete ring `A` it is closed, hence complete. So `(A₀, ϖ A₀)` is a
  Henselian pair by Mathlib's `IsAdicComplete.henselianRing`.
* An open subring `B ⊆ A°` is the directed union of the rings of definition it contains: finitely
  many elements of `B` generate a bounded subring, which lies in a ring of definition inside `B`
  (Wedhorn's Corollary 6.4(4), `TauCeti.Huber.exists_pairOfDefinition_le_le`). A monic polynomial
  over `B` with a simple root modulo `ϖ`, together with the witnesses of both conditions, therefore
  comes from one such ring of definition, where the previous step finds the root.

The second step is needed because `A°` itself need not be `ϖ`-adically separated when `A` is not
uniform: in `ℚ_p[ε]/(ε²)` the nilpotent `ε` lies in `ϖⁿ A°` for every `n`. Mathlib's
`IsAdicComplete.henselianRing` therefore does not apply to `A°` directly.

## Main results

* `TauCeti.Huber.PairOfDefinition.isAdicComplete_span_singleton`: a ring of definition containing
  a pseudouniformiser `ϖ` is `ϖ`-adically complete.
* `TauCeti.Huber.PairOfDefinition.henselianRing`: such a ring of definition is Henselian along `ϖ`.
* `TauCeti.Huber.henselianRing_of_isOpen_subring`: an open subring of `A°` containing `ϖ` is
  Henselian along `ϖ`.
* `TauCeti.Huber.henselianRing_powerBoundedSubring`: `A°` is Henselian along `ϖ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 6.14 and
  Corollary 6.4.
* P. Scholze, *Étale cohomology of diamonds*, proof of Lemma 15.3.
-/

public section

open Polynomial

namespace TauCeti.Huber

variable {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [T0Space A] [IsTopologicalRing A] {ϖ : A}

namespace PairOfDefinition

/-- **A ring of definition containing a pseudouniformiser `ϖ` is `ϖ`-adically complete.** In a
complete Hausdorff topological ring, every ring of definition `A₀` with `ϖ ∈ A₀` is complete and
separated for the `ϖ A₀`-adic topology. -/
theorem isAdicComplete_span_singleton (P : PairOfDefinition A) (hϖ : IsPseudoUniformizer ϖ)
    (hϖP : ϖ ∈ P.ringOfDefinition) :
    IsAdicComplete (Ideal.span {(⟨ϖ, hϖP⟩ : P.ringOfDefinition)}) P.ringOfDefinition := by
  set Q := ofIsPseudoUniformizer _ P.isOpen_ringOfDefinition P.isBounded_ringOfDefinition hϖ hϖP
  -- `Q` has ring of definition `P.ringOfDefinition` and ideal of definition `ϖ A₀`; identify the
  -- latter with the span of `ϖ` over the ring of definition of `Q`, then transport.
  have key : ∀ (R : Subring A) (_ : R = P.ringOfDefinition) (J : Ideal R),
      (∀ x : R, x ∈ J ↔ ∃ y ∈ P.ringOfDefinition, ϖ * y = x) → IsAdicComplete J R →
        IsAdicComplete (Ideal.span {(⟨ϖ, hϖP⟩ : P.ringOfDefinition)}) P.ringOfDefinition := by
    rintro R rfl J hJ hR
    obtain rfl : J = Ideal.span {(⟨ϖ, hϖP⟩ : P.ringOfDefinition)} := by
      ext x
      rw [hJ, P.ringOfDefinition.mem_span_singleton_iff hϖP]
    exact hR
  exact key Q.ringOfDefinition (ofIsPseudoUniformizer_ringOfDefinition ..) Q.idealOfDefinition
    (fun _ ↦ mem_ofIsPseudoUniformizer_idealOfDefinition ..) Q.isAdicComplete_idealOfDefinition

/-- **A ring of definition containing a pseudouniformiser `ϖ` is Henselian along `ϖ`**, in a
complete Hausdorff ring. -/
theorem henselianRing (P : PairOfDefinition A) (hϖ : IsPseudoUniformizer ϖ)
    (hϖP : ϖ ∈ P.ringOfDefinition) :
    HenselianRing P.ringOfDefinition (Ideal.span {(⟨ϖ, hϖP⟩ : P.ringOfDefinition)}) :=
  have := P.isAdicComplete_span_singleton hϖ hϖP
  inferInstance

end PairOfDefinition

variable [IsHuberRing A]

/-- Finitely many elements of an open subring `B ⊆ A°` containing a pseudouniformiser `ϖ` lie in a
subring `C ⊆ B` containing `ϖ` that is Henselian along `ϖ`: a ring of definition inside `B`. -/
private theorem exists_henselianRing_subring {B : Subring A} (hB : IsOpen (B : Set A))
    (hBA : B ≤ powerBoundedSubring A) (hϖ : IsPseudoUniformizer ϖ) (hϖB : ϖ ∈ B) (T : Finset A)
    (hT : (T : Set A) ⊆ B) :
    ∃ (C : Subring A) (_ : C ≤ B) (hϖC : ϖ ∈ C),
      (T : Set A) ⊆ C ∧ HenselianRing C (Ideal.span {(⟨ϖ, hϖC⟩ : C)}) := by
  classical
  -- The finite set `T ∪ {ϖ}` of power-bounded elements generates a bounded subring of `B`.
  have hT' : ((insert ϖ T : Finset A) : Set A) ⊆ B := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hϖB hT
  obtain ⟨Q, hQ, hQB⟩ := exists_pairOfDefinition_le_le
    (isBounded_subringClosure (insert ϖ T).finite_toSet fun t ht ↦
      mem_powerBoundedSubring.mp (hBA (hT' ht))) hB
    ((Subring.closure_le).mpr hT')
  have hsub : ((insert ϖ T : Finset A) : Set A) ⊆ Q.ringOfDefinition :=
    Subring.subset_closure.trans hQ
  have hϖQ : ϖ ∈ Q.ringOfDefinition := hsub (by simp)
  exact ⟨Q.ringOfDefinition, hQB, hϖQ, fun t ht ↦ hsub (by simp [Finset.mem_coe.mp ht]),
    Q.henselianRing hϖ hϖQ⟩

/-- **An open subring of `A°` containing a pseudouniformiser `ϖ` is Henselian along `ϖ`.** Let `A`
be a complete Hausdorff Huber ring, `ϖ` a pseudouniformiser and `B ⊆ A°` an open subring with
`ϖ ∈ B`. Then `(B, ϖ B)` is a Henselian pair.

Rings of definition containing `ϖ` are the case `B = A₀`
(`TauCeti.Huber.PairOfDefinition.henselianRing`), and `A°` is the case `B = A°`
(`TauCeti.Huber.henselianRing_powerBoundedSubring`). The hypothesis `B ⊆ A°` cannot be dropped:
for `B = A` the ideal `ϖ A` is the unit ideal. -/
theorem henselianRing_of_isOpen_subring {B : Subring A} (hB : IsOpen (B : Set A))
    (hBA : B ≤ powerBoundedSubring A) (hϖ : IsPseudoUniformizer ϖ) (hϖB : ϖ ∈ B) :
    HenselianRing B (Ideal.span {(⟨ϖ, hϖB⟩ : B)}) where
  jac x hx := by
    classical
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    refine Ideal.mem_jacobson_bot.mpr fun y ↦ ?_
    obtain ⟨C, hCB, hϖC, hT, hC⟩ := exists_henselianRing_subring hB hBA hϖ hϖB {(a : A), (y : A)}
      (by simp [Set.insert_subset_iff])
    have ha : (a : A) ∈ C := hT (by simp)
    have hy : (y : A) ∈ C := hT (by simp)
    -- `a * ϖ` lies in the Jacobson radical of `C`, so `a * ϖ * y + 1` is a unit there.
    have hu := Ideal.mem_jacobson_bot.mp
      (hC.jac (Ideal.mul_mem_left _ ⟨a, ha⟩ (Ideal.mem_span_singleton_self _))) ⟨y, hy⟩
    have := hu.map (Subring.inclusion hCB)
    rw [map_add, map_mul, map_mul, map_one] at this
    exact this
  is_henselian P hP a₀ h₁ h₂ := by
    classical
    -- Unfold both hypotheses into elements of `B`: `P(a₀) = d * ϖ` and
    -- `P'(a₀) * u - 1 = c * ϖ`.
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h₁
    obtain ⟨v, hv⟩ := h₂.exists_right_inv
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq] at hv
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hv
    -- Put the coefficients of `P` and the elements `a₀, d, u, c` into one Henselian `C ⊆ B`.
    obtain ⟨C, hCB, hϖC, hT, hC⟩ := exists_henselianRing_subring hB hBA hϖ hϖB
      ({(a₀ : A), (d : A), (u : A), (c : A)} ∪ P.support.image fun n ↦ (P.coeff n : A))
      (by
        simp only [Finset.coe_union, Finset.coe_insert, Finset.coe_singleton, Finset.coe_image,
          Set.union_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
        exact ⟨⟨a₀.2, d.2, u.2, c.2⟩, by rintro _ ⟨n, -, rfl⟩; exact (P.coeff n).2⟩)
    set φ : C →+* B := Subring.inclusion hCB
    have hφ : Function.Injective φ := Subring.inclusion_injective hCB
    have hmem : ∀ x : B, (x : A) ∈ C → ∃ y : C, φ y = x := fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨a₀', ha₀'⟩ := hmem a₀ (hT (by simp))
    obtain ⟨d', hd'⟩ := hmem d (hT (by simp))
    obtain ⟨u', hu'⟩ := hmem u (hT (by simp))
    obtain ⟨c', hc'⟩ := hmem c (hT (by simp))
    have hϖφ : φ ⟨ϖ, hϖC⟩ = ⟨ϖ, hϖB⟩ := rfl
    -- Lift `P` to a monic polynomial `Q` over `C`.
    obtain ⟨Q, hQP, -, hQ⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts P).mpr fun n ↦ by
        by_cases hn : n ∈ P.support
        · exact hmem _ (hT (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn)))
        · exact ⟨0, by simp [notMem_support_iff.mp hn]⟩) hP
    subst hQP ha₀' hd' hu' hc'
    -- Both conditions descend to `C` by injectivity of `φ`.
    have h₁' : Q.eval a₀' ∈ Ideal.span {(⟨ϖ, hϖC⟩ : C)} :=
      Ideal.mem_span_singleton'.mpr ⟨d', hφ (by rw [map_mul, hϖφ, hd, eval_map_apply])⟩
    have h₂' : IsUnit (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖC⟩ : C)})
        (Q.derivative.eval a₀')) := by
      refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ u') ?_
      rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      refine Ideal.mem_span_singleton'.mpr ⟨c', hφ ?_⟩
      rw [map_mul, hϖφ, hc, map_sub, map_mul, map_one, derivative_map, eval_map_apply]
    obtain ⟨a, ha, haa₀⟩ := hC.is_henselian Q hQ a₀' h₁' h₂'
    refine ⟨φ a, by rw [IsRoot.def, eval_map_apply, ha.eq_zero, map_zero], ?_⟩
    have := Ideal.mem_map_of_mem φ haa₀
    rwa [map_sub, Ideal.map_span, Set.image_singleton, hϖφ] at this

/-- **The power-bounded subring of a complete Tate ring is Henselian along a pseudouniformiser.**
Let `A` be a complete Hausdorff Huber ring and `ϖ` a pseudouniformiser of `A`, which is
power-bounded because it is topologically nilpotent. Then `(A°, ϖ A°)` is a Henselian pair: a monic
polynomial over `A°` with a simple root modulo `ϖ` has a root in `A°` lifting it. -/
theorem henselianRing_powerBoundedSubring (hϖ : IsPseudoUniformizer ϖ) :
    HenselianRing (powerBoundedSubring A)
      (Ideal.span {(⟨ϖ, mem_powerBoundedSubring.mpr
        (.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent)⟩ : powerBoundedSubring A)}) :=
  henselianRing_of_isOpen_subring (isOpen_powerBoundedSubring A) le_rfl hϖ _

end TauCeti.Huber
