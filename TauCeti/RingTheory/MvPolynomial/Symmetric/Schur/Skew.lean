/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Young.SkewTableau
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic

/-!
# Skew Schur polynomials

The skew Schur polynomial of `outer / inner` is the weight generating function of its
semistandard tableaux in a finite alphabet. This file supplies the tableau-sum definition over
any commutative semiring, its coefficients and homogeneity, its agreement with the native Schur
polynomial on straight shapes, and stability under setting the last variable to zero.
These identities allow straight and skew tableau generating functions to be used together.

Containment is built into the tableau type: if `inner ≤ outer` fails the polynomial is zero.
For `inner = outer` there is one empty tableau, contributing `1`, including in zero variables.
No symmetry or Littlewood–Richardson expansion is asserted here.

## References

* W. Fulton, *Young Tableaux*, Cambridge University Press (1997), §5.1.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, second edition, Chapter I, §5.
-/

public section

namespace TauCeti

open Finset MvPolynomial

namespace BoundedSkewSSYT

variable {n m : ℕ} {inner outer : YoungDiagram}

/-- The weight of a bounded skew tableau, as a monomial exponent on its finite alphabet. -/
noncomputable def weight (T : BoundedSkewSSYT n inner outer) : Fin n →₀ ℕ :=
  Finsupp.comapDomain Fin.val T.1.content Fin.val_injective.injOn

/-- Weight coordinates are the multiplicities of the corresponding letters. -/
@[simp]
theorem weight_apply (T : BoundedSkewSSYT n inner outer) (i : Fin n) :
    T.weight i = T.1.content i :=
  Finsupp.comapDomain_apply _ _ _ _

/-- Extending the finite weight by zero recovers the natural-number content. -/
theorem mapDomain_weight (T : BoundedSkewSSYT n inner outer) :
    Finsupp.mapDomain Fin.val T.weight = T.1.content := by
  apply Finsupp.mapDomain_comapDomain _ Fin.val_injective
  intro k hk
  refine ⟨⟨k, ?_⟩, rfl⟩
  by_contra hn
  exact (Finsupp.mem_support_iff.mp hk) (T.content_eq_zero (by omega))

/-- Every skew cell contributes exactly one to the sum of the weight. -/
theorem sum_weight (T : BoundedSkewSSYT n inner outer) :
    ∑ i, T.weight i = outer.card - inner.card := by
  have h := T.1.sum_content
  rw [← T.mapDomain_weight, Finsupp.sum_mapDomain_index (fun _ => rfl)
    (fun _ _ _ => rfl)] at h
  exact (Finsupp.sum_fintype _ _ (fun _ => rfl)).symm.trans h

/-- A weight coordinate is positive exactly when some skew cell carries that letter. -/
theorem weight_pos_iff (T : BoundedSkewSSYT n inner outer) (k : Fin n) :
    0 < T.weight k ↔ ∃ c ∈ outer.cells \ inner.cells, T.1 c.1 c.2 = k := by
  rw [weight_apply, SkewSemistandardYoungTableau.content_apply, Finset.card_pos]
  exact Finset.filter_nonempty_iff

/-- Enlarging the alphabet extends the weight by zero. -/
theorem weight_castLE (h : n ≤ m) (T : BoundedSkewSSYT n inner outer) :
    (T.castLE h).weight = Finsupp.mapDomain (Fin.castLE h) T.weight := by
  apply (Finsupp.mapDomain_injective Fin.val_injective)
  rw [mapDomain_weight, coe_castLE, ← Finsupp.mapDomain_comp]
  exact T.mapDomain_weight.symm

/-- The straight-shape comparison preserves weight. -/
@[simp]
theorem weight_botEquiv (T : BoundedSkewSSYT n ⊥ outer) :
    BoundedSSYT.weight (botEquiv n outer T) = T.weight := by
  ext i
  simp only [BoundedSSYT.weight_apply, weight_apply,
    SemistandardYoungTableau.content_apply, SkewSemistandardYoungTableau.content_apply,
    botEquiv_apply, YoungDiagram.cells_bot, Finset.sdiff_empty]

end BoundedSkewSSYT

variable (n : ℕ) (R : Type*) [CommSemiring R] (inner outer : YoungDiagram)

/-- The skew Schur polynomial of `outer / inner` in `n` variables: one weight monomial
for each bounded semistandard skew tableau. -/
noncomputable def skewSchurPoly : MvPolynomial (Fin n) R :=
  ∑ T : BoundedSkewSSYT n inner outer, monomial T.weight 1

/-- The tableau-sum characterization of a skew Schur polynomial. -/
theorem skewSchurPoly_eq_sum :
    skewSchurPoly n R inner outer =
      ∑ T : BoundedSkewSSYT n inner outer, monomial T.weight 1 :=
  (rfl)

variable {n R inner outer}

/-- A skew Schur coefficient counts bounded tableaux of the given weight. -/
theorem coeff_skewSchurPoly (d : Fin n →₀ ℕ) :
    (skewSchurPoly n R inner outer).coeff d =
      (Nat.card {T : BoundedSkewSSYT n inner outer // T.weight = d} : R) := by
  classical
  simp [skewSchurPoly_eq_sum, coeff_monomial, Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.sum_boole]

/-- Skew Schur polynomials are homogeneous of degree the number of skew cells. -/
theorem isHomogeneous_skewSchurPoly :
    (skewSchurPoly n R inner outer).IsHomogeneous (outer.card - inner.card) :=
  IsHomogeneous.sum _ _ _ fun T _ =>
    isHomogeneous_monomial _ ((Finsupp.degree_eq_sum _).trans T.sum_weight)

/-- Changing coefficients commutes with the skew Schur polynomial. -/
@[simp]
theorem map_skewSchurPoly {S : Type*} [CommSemiring S] (f : R →+* S) :
    MvPolynomial.map f (skewSchurPoly n R inner outer) = skewSchurPoly n S inner outer := by
  simp [skewSchurPoly_eq_sum, map_sum, map_monomial]

/-- Evaluation of a skew Schur polynomial is the sum of its tableau weights. -/
theorem eval_skewSchurPoly (x : Fin n → R) :
    eval x (skewSchurPoly n R inner outer) =
      ∑ T : BoundedSkewSSYT n inner outer, ∏ i, x i ^ T.weight i := by
  rw [skewSchurPoly_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun T _ => by
    rw [eval_monomial, one_mul]
    exact Finsupp.prod_fintype _ _ fun _ => pow_zero _

/-- Evaluation at one counts the bounded skew tableaux. -/
@[simp]
theorem eval_one_skewSchurPoly :
    eval (fun _ => (1 : R)) (skewSchurPoly n R inner outer) =
      (Nat.card (BoundedSkewSSYT n inner outer) : R) := by
  simp [eval_skewSchurPoly, Nat.card_eq_fintype_card]

/-- A nonexistent skew shape has no tableau monomials. -/
theorem skewSchurPoly_eq_zero_of_not_le (h : ¬ inner ≤ outer) :
    skewSchurPoly n R inner outer = 0 := by
  have : IsEmpty (BoundedSkewSSYT n inner outer) := BoundedSkewSSYT.isEmpty_of_not_le h
  simp [skewSchurPoly_eq_sum]

/-- The empty skew shape contributes the constant polynomial one. -/
@[simp]
theorem skewSchurPoly_self (μ : YoungDiagram) : skewSchurPoly n R μ μ = 1 := by
  have hw (T : BoundedSkewSSYT n μ μ) : T.weight = 0 := by
    ext i
    simp [BoundedSkewSSYT.weight_apply, SkewSemistandardYoungTableau.content_apply]
  simp [skewSchurPoly_eq_sum, hw]

/-- A straight skew Schur polynomial is the native diagram-indexed Schur polynomial. -/
@[simp]
theorem skewSchurPoly_bot : skewSchurPoly n R ⊥ outer = diagramSchurPoly n R outer := by
  rw [skewSchurPoly_eq_sum, diagramSchurPoly_eq_sum]
  exact (Fintype.sum_equiv (BoundedSkewSSYT.botEquiv n outer) _ _
    fun T => by rw [BoundedSkewSSYT.weight_botEquiv])

/-- Setting the last variable to zero discards exactly the tableaux using the last letter,
leaving the skew Schur polynomial in the smaller alphabet.

Not a `simp` lemma: substituting polynomials for the variables, `simp` rewrites `aeval` to
`bind₁` by `MvPolynomial.aeval_eq_bind₁`, so this left-hand side is not in `simp`-normal form. -/
theorem aeval_snoc_zero_skewSchurPoly :
    aeval (Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0)
      (skewSchurPoly (n + 1) R inner outer) = skewSchurPoly n R inner outer := by
  classical
  rw [skewSchurPoly_eq_sum, map_sum, skewSchurPoly_eq_sum]
  symm
  apply Fintype.sum_of_injective (BoundedSkewSSYT.castLE (Nat.le_succ n))
    (BoundedSkewSSYT.castLE_injective _) _ _
  · intro T hT
    have hw : T.weight (Fin.last n) ≠ 0 := by
      intro hw
      apply hT
      apply (BoundedSkewSSYT.exists_castLE_iff _ T).mpr
      intro i j hc
      have hne : T.1 i j ≠ n := fun he =>
        (Nat.ne_of_gt ((T.weight_pos_iff (Fin.last n)).mpr ⟨(i, j), hc, he⟩)) hw
      have := T.entry_lt hc
      omega
    rw [aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    exact Finset.prod_eq_zero (Finset.mem_univ (Fin.last n))
      (by rw [Fin.snoc_last, zero_pow hw])
  · intro T
    rw [BoundedSkewSSYT.weight_castLE, ← rename_monomial, aeval_rename]
    have hx : Fin.snoc (X : Fin n → MvPolynomial (Fin n) R) 0 ∘
        Fin.castLE (Nat.le_succ n) = X := by
      funext i
      have hi : Fin.castLE (Nat.le_succ n) i = i.castSucc := Fin.ext rfl
      simp only [Function.comp_apply, hi, Fin.snoc_castSucc]
    rw [hx, aeval_X_left_apply]

end TauCeti
