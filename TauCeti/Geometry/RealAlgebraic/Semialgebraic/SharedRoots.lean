/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.RootCount
import TauCeti.Algebra.MvPolynomial.Rename

/-!
# Semialgebraic descriptions of shared roots

The shared roots of a finite polynomial family are the union of the distinct roots of its
nonzero specializations. Their number, and their number below a polynomial threshold, have
finite polynomial sign descriptions. In cylinder coordinates this gives the graph of each
ordered shared root and every complementary sector, including the two unbounded sectors.

At each parameter, only the active (nonzero) specializations enter the product. Stratifying
by this active subfamily reduces the descriptions to the uniform single-polynomial root
formulas. No closure under projection, constancy of degrees, or continuity of roots is needed.
Repeated roots and roots shared by several members are counted once. A nullified member is
omitted: its entire zero set is not part of the finite shared root set. When all members are
nullified, or the family is empty, the shared root set is empty and sector zero is the whole
fiber.

## References

S. Basu, R. Pollack, and M.-F. Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapters 10 and 11
(uniform sign descriptions and the roots of an active polynomial family).
-/

public section

open Polynomial Set TauCeti

namespace Finset

variable {σ R : Type*}

section Domain

variable [CommRing R] [IsDomain R] [LinearOrder R]

/-- Membership in the shared distinct root set at a polynomial threshold is semialgebraic.
Zero specializations are omitted, rather than contributing their entire zero set. -/
theorem isSemialgebraic_setOf_mem_biUnion_roots_map_eval
    (F : Finset (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) :
    IsSemialgebraic {x : σ → R |
      MvPolynomial.eval x T ∈ F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset} := by
  classical
  have h : {x : σ → R |
      MvPolynomial.eval x T ∈ F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset} =
      ⋃ P ∈ F, {x | P.map (MvPolynomial.eval x) ≠ 0} ∩
        {x | MvPolynomial.eval x (P.eval T) = 0} := by
    ext x
    simp only [mem_ofPred_eq, mem_biUnion, Multiset.mem_toFinset, mem_roots', IsRoot.def,
      eval_map_apply, mem_iUnion, mem_inter_iff, exists_prop]
  rw [h]
  exact .biUnion F.finite_toSet fun P _ =>
    (isSemialgebraic_setOf_map_eval_eq_zero P).compl.inter (isSemialgebraic_eval_eq_zero _)

/-- Reduce a condition on shared roots to conditions on the products of the active subfamilies.
This helper keeps the finite stratification common to the total and below-threshold counts. -/
private theorem isSemialgebraic_setOf_biUnion_roots_map_eval
    (F : Finset (MvPolynomial σ R)[X]) (φ : (σ → R) → Finset R → Prop)
    (hφ : ∀ Q : (MvPolynomial σ R)[X],
      IsSemialgebraic {x | φ x (Q.map (MvPolynomial.eval x)).roots.toFinset}) :
    IsSemialgebraic {x | φ x (F.biUnion fun P =>
      (P.map (MvPolynomial.eval x)).roots.toFinset)} := by
  classical
  let active := fun (A : Finset (MvPolynomial σ R)[X]) =>
    {x : σ → R | ∀ P ∈ F, P ∈ A ↔ P.map (MvPolynomial.eval x) ≠ 0}
  have hactive (A : Finset (MvPolynomial σ R)[X]) : IsSemialgebraic (active A) := by
    have hP (P : (MvPolynomial σ R)[X]) :
        IsSemialgebraic {x : σ → R | P ∈ A ↔ P.map (MvPolynomial.eval x) ≠ 0} := by
      by_cases hPA : P ∈ A
      · simpa only [hPA, true_iff, compl_ofPred] using
          (isSemialgebraic_setOf_map_eval_eq_zero P).compl
      · simpa only [hPA, false_iff, not_not] using isSemialgebraic_setOf_map_eval_eq_zero P
    simpa only [active, ofPred_forall, Finset.mem_coe] using
      IsSemialgebraic.biInter F.finite_toSet (fun P _ => hP P)
  have hroots (A : Finset (MvPolynomial σ R)[X]) (hA : A ⊆ F) (x : σ → R)
      (hx : x ∈ active A) :
      ((∏ P ∈ A, P).map (MvPolynomial.eval x)).roots.toFinset =
        F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset := by
    have hne : ∀ P ∈ A, P.map (MvPolynomial.eval x) ≠ 0 :=
      fun P hP => (hx P (hA hP)).mp hP
    rw [Polynomial.map_prod, roots_prod _ _ (prod_ne_zero_iff.mpr hne), bind_toFinset,
      A.val_toFinset]
    ext r
    simp only [mem_biUnion, Multiset.mem_toFinset]
    constructor
    · rintro ⟨P, hP, hr⟩
      exact ⟨P, hA hP, hr⟩
    · rintro ⟨P, hP, hr⟩
      exact ⟨P, (hx P hP).mpr (ne_zero_of_mem_roots hr), hr⟩
  have h : {x | φ x (F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset)} =
      ⋃ A ∈ F.powerset, active A ∩
        {x | φ x ((∏ P ∈ A, P).map (MvPolynomial.eval x)).roots.toFinset} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_powerset]
    constructor
    · intro hx
      let A := F.filter fun P => P.map (MvPolynomial.eval x) ≠ 0
      have hxA : x ∈ active A := by
        intro P hP
        simp only [A, mem_filter, hP, true_and]
      exact ⟨A, filter_subset _ _, hxA, by rw [hroots A (filter_subset _ _) x hxA]; exact hx⟩
    · rintro ⟨A, hA, hxA, hx⟩
      rwa [hroots A hA x hxA] at hx
  rw [h]
  exact .biUnion F.powerset.finite_toSet fun A _ => (hactive A).inter (hφ _)

end Domain

section RealClosed

variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The number of shared distinct roots is semialgebraic in the parameters, even when members
are nullified or their degrees drop. An empty active subfamily has count zero. -/
theorem isSemialgebraic_setOf_card_biUnion_roots_map_eval
    (F : Finset (MvPolynomial σ R)[X]) (k : ℕ) :
    IsSemialgebraic {x : σ → R |
      (F.biUnion fun P => (P.map (MvPolynomial.eval x)).roots.toFinset).card = k} := by
  classical
  exact isSemialgebraic_setOf_biUnion_roots_map_eval F (fun _ s => s.card = k)
    (fun Q => isSemialgebraic_setOf_card_roots_map_eval Q k)

/-- The number of shared distinct roots strictly below a polynomial threshold is semialgebraic.
The strict inequality includes the case where the threshold is itself a shared root. -/
theorem isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt
    (F : Finset (MvPolynomial σ R)[X]) (T : MvPolynomial σ R) (k : ℕ) :
    IsSemialgebraic {x : σ → R |
      {r ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval x)).roots.toFinset) |
        r < MvPolynomial.eval x T}.card = k} := by
  classical
  exact isSemialgebraic_setOf_biUnion_roots_map_eval F
    (fun x s => (s.filter fun r => r < MvPolynomial.eval x T).card = k)
    (fun Q => isSemialgebraic_setOf_card_roots_map_eval_lt Q T k)

variable {n : ℕ}

/-- The graph of the `i`th ordered shared distinct root, counted from zero, is semialgebraic
in cylinder coordinates. Where fewer than `i + 1` shared roots exist the fiber is empty. -/
theorem isSemialgebraic_setOf_mem_biUnion_roots_card_lt
    (F : Finset (MvPolynomial (Fin n) R)[X]) (i : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      y 0 ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
      {r ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
        r < y 0}.card = i} := by
  classical
  let G := F.image fun P => P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert (G.isSemialgebraic_setOf_mem_biUnion_roots_map_eval (MvPolynomial.X 0)).inter
    (G.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt (MvPolynomial.X 0) i) using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, G, image_biUnion, map_eval_map_rename,
    MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

/-- The locus of the `j`th shared-root sector, counted from below, is semialgebraic.
Sector zero is the whole fiber if no active member has a root. -/
theorem isSemialgebraic_setOf_notMem_biUnion_roots_card_lt
    (F : Finset (MvPolynomial (Fin n) R)[X]) (j : ℕ) :
    IsSemialgebraic {y : Fin (n + 1) → R |
      y 0 ∉ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) ∧
      {r ∈ F.biUnion (fun P => (P.map (MvPolynomial.eval (Fin.tail y))).roots.toFinset) |
        r < y 0}.card = j} := by
  classical
  let G := F.image fun P => P.map (MvPolynomial.rename (R := R) Fin.succ).toRingHom
  convert (G.isSemialgebraic_setOf_mem_biUnion_roots_map_eval (MvPolynomial.X 0)).compl.inter
    (G.isSemialgebraic_setOf_card_biUnion_roots_map_eval_lt (MvPolynomial.X 0) j) using 1
  ext y
  simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, G, image_biUnion, map_eval_map_rename,
    MvPolynomial.eval_X, Fin.tail_def, Function.comp_def]

end RealClosed

end Finset
