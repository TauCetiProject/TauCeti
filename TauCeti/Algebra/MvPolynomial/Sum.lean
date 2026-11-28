/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Polynomials in two families of variables

`MvPolynomial.eval₂_sumAlgEquiv` evaluates a polynomial after one family of variables
has been moved into the coefficient ring by Mathlib's `MvPolynomial.sumAlgEquiv`.
This permits coefficient extraction with respect to one family while retaining polynomial
dependence on the other. `MvPolynomial.sumAlgEquiv_map` shows that this separation commutes with
mapping coefficients along a ring homomorphism.

A polynomial in variables `σ ⊕ τ` involves only finitely many variables of the second family;
Mathlib's `MvPolynomial.exists_fin_right_rename` renames it from a polynomial in `σ ⊕ Fin m`
along an injective map `Fin m → τ`. When the second family is read as existentially quantified
witnesses, `MvPolynomial.exists_eval_rename_sumMap_eq_zero_iff` shows that renaming the witnesses
along an injective map does not change which assignments of the first family admit a root.
Together they reduce an existential polynomial condition with arbitrarily many witness variables
to one with finitely many, as in the finite normal form of Diophantine sets.
-/

public section

namespace MvPolynomial

variable {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]

/-- Evaluating the two variable families separately agrees with joint evaluation. -/
theorem eval₂_sumAlgEquiv (f : R →+* S) (x : σ → S) (y : τ → S)
    (p : MvPolynomial (σ ⊕ τ) R) :
    eval₂ (eval₂Hom f y) x (sumAlgEquiv R σ τ p) = eval₂ f (Sum.elim x y) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp]

/-- Evaluating a polynomial after substituting an algebra map into its coefficient variables
agrees with evaluating all variables at once. -/
@[simp]
theorem aevalTower_map_sumAlgEquiv {A : Type*} [CommSemiring A] [Algebra R A] [Algebra R S]
    (p : MvPolynomial (σ ⊕ τ) R) (q : MvPolynomial τ R →ₐ[R] A)
    (y : A →ₐ[R] S) (x : σ → S) :
    aevalTower y x (map q (sumAlgEquiv R σ τ p)) =
      aeval (Sum.elim x (fun i ↦ y (q (X i)))) p := by
  have h : (y : A →+* S).comp (q : MvPolynomial τ R →+* A) =
      eval₂Hom (algebraMap R S) (fun i ↦ y (q (X i))) :=
    congrArg AlgHom.toRingHom (aeval_unique (y.comp q))
  calc
    _ = eval₂ (y : A →+* S) x (map q (sumAlgEquiv R σ τ p)) := (rfl)
    _ = eval₂ (eval₂Hom (algebraMap R S) (fun i ↦ y (q (X i)))) x
        (sumAlgEquiv R σ τ p) := by rw [eval₂_map, h]
    _ = _ := eval₂_sumAlgEquiv _ _ _ _

/-- Separating two families of variables commutes with mapping the coefficients: the
coefficient map acts on the polynomial coefficients in the second family. -/
theorem sumAlgEquiv_map (f : R →+* S) (p : MvPolynomial (σ ⊕ τ) R) :
    sumAlgEquiv S σ τ (map f p) = map (map f) (sumAlgEquiv R σ τ p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => cases i <;> simp [hp]

/-- Reading the variables of `τ` as existential witnesses with values `c y` for `y : W`,
renaming them along an injective map `f` does not change which assignments `x` of `σ` admit a
root. -/
theorem exists_eval_rename_sumMap_eq_zero_iff {τ' W : Type*} [Nonempty W] (c : W → R)
    (x : σ → R) {f : τ → τ'} (hf : Function.Injective f) (q : MvPolynomial (σ ⊕ τ) R) :
    (∃ y : τ' → W, eval (Sum.elim x (c ∘ y)) (rename (Sum.map id f) q) = 0) ↔
      ∃ z : τ → W, eval (Sum.elim x (c ∘ z)) q = 0 := by
  have key (y : τ' → W) : eval (Sum.elim x (c ∘ y)) (rename (Sum.map id f) q) =
      eval (Sum.elim x (c ∘ (y ∘ f))) q := by
    rw [eval_rename, Sum.elim_comp_map, Function.comp_id, Function.comp_assoc]
  simp only [key]
  exact (hf.surjective_comp_right.exists (p := fun z ↦ eval (Sum.elim x (c ∘ z)) q = 0)).symm

end MvPolynomial
