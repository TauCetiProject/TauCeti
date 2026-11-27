/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LinearHomComplex.ExactPairing
public import TauCeti.Algebra.Homology.Monoidal.TwistedPairing

/-!
# The cap pairing and its sewing coevaluation

Let `o` be the orientation line of a capped orbit, of degree `μ`, with a dual `o'`, and let `λ`
be a fixed line of degree `n` with a second line `λ'` paired with it into a line `V` of degree
`2n`, the complex orientation line of a tangent space of a symplectic manifold of dimension `2n`.
The **cap lines** of the orbit are

`C⁺ = o ⊗ λ` and `C⁻ = λ' ⊗ o'`,

of degrees `n + μ` and `n - μ`. This file constructs the **cap pairing** `γ : C⁺ ⊗ C⁻ ⟶ V` and its
**sewing coevaluation** `q : V ⟶ C⁻ ⊗ C⁺`, and proves their zigzag identities: `(C⁻, C⁺)` is a
pairing twisted by `V` (`TauCeti.Floer.capPairing`, a `TauCeti.TwistedPairing`). The data are any
exact pairing of `o` and `o'` and any pairing `P` of `λ` and `λ'` twisted by `V`, with evaluation
`λ' ⊗ λ ⟶ V`, in a symmetric monoidal category; for orientation lines, `λ'` is the bidual of `λ`
and `o'` the dual complex of `o`.

The construction has two steps.

* **The negative-first evaluation** `C⁻ ⊗ C⁺ ⟶ V` contracts `o' ⊗ o` by the evaluation of `o` and
  then pairs `λ' ⊗ λ` into `V` by `P`. Together with the coevaluation that expands `o ⊗ o'` around
  the coevaluation `V ⟶ λ ⊗ λ'` of `P`, it makes `(C⁺, C⁻)` a pairing twisted by `V`
  (`TauCeti.TwistedPairing.tensor`). For `o'` the dual complex of a complex of modules `o`, the
  evaluation of `o` is the unsigned evaluation `φ ⊗ a ↦ φ(a)`
  (`TauCeti.linearHomComplexEvaluation`, the evaluation of `TauCeti.exactPairingLinearHomComplex`),
  and no braiding enters the negative-first evaluation.
* **The cap pairing** is the braided swap of that pairing
  (`TauCeti.TwistedPairing.swap`): its evaluation `γ` is the Koszul interchange of `C⁺` and `C⁻`
  followed by the negative-first evaluation (`TauCeti.Floer.capPairing_evaluation`), and its
  coevaluation `q` is the coevaluation of the negative-first evaluation followed by the same
  interchange (`TauCeti.Floer.capPairing_coevaluation`).

For cochain complexes of modules with the Koszul braiding, the interchange of factors of degrees
`p` and `q` carries the sign `(-1)^(p q)`, so on the summand `C⁺_p ⊗ C⁻_q` the cap pairing is
`(-1)^(p q)` times the negative-first evaluation after the unsigned flip
(`TauCeti.Floer.ιTensorObj_capPairing_evaluation_f`, from the general
`TauCeti.TwistedPairing.ιTensorObj_swap_evaluation_f`). In cochain degrees the cap lines of
homological degrees `n + μ` and `n - μ` sit in degrees `-(n + μ)` and `μ - n`, and the sign is
`(-1)^(μ + n)` (`TauCeti.Floer.ιTensorObj_capPairing_evaluation_f_of_eq`): the cap pairing and the
negative-first evaluation differ exactly when `μ + n` is odd, and they agree at the complex minimum
of a quadratic Hamiltonian, where `μ = -n`. Since `q` is followed by the same interchange, it
carries the same coefficient: where the coevaluation of the negative-first evaluation lands in the
summand `C⁺_p ⊗ C⁻_q`, the sewing coevaluation is `(-1)^(p q)` times it followed by the unsigned
flip (`TauCeti.Floer.capPairing_coevaluation_f`), and `(-1)^(μ + n)` times it on the cap lines
(`TauCeti.Floer.capPairing_coevaluation_f_of_eq`).

Every morphism here is a morphism of complexes, so the cap pairing and its coevaluation commute
with the differentials.

## Main definitions

* `TauCeti.Floer.capPairing`: the cap pairing and its sewing coevaluation, as a pairing of
  `C⁻ = λ' ⊗ o'` and `C⁺ = o ⊗ λ` twisted by `V`.

## Main results

* `TauCeti.Floer.capPairing_evaluation` and `TauCeti.Floer.capPairing_coevaluation`: the cap
  pairing and its coevaluation are the negative-first evaluation and its coevaluation composed
  with the interchange of `C⁺` and `C⁻`.
* `TauCeti.Floer.ιTensorObj_capPairing_evaluation_f` and
  `TauCeti.Floer.ιTensorObj_capPairing_evaluation_f_of_eq`: the Koszul sign of the cap pairing on
  complexes of modules, `(-1)^(μ + n)` on the cap lines.
* `TauCeti.Floer.capPairing_coevaluation_f` and `TauCeti.Floer.capPairing_coevaluation_f_of_eq`:
  the same Koszul sign for the sewing coevaluation.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, second edition,
  AMS Colloquium Publications 52, 2012, Appendix A.2, on determinant lines.
* P. Etingof, S. Gelaki, D. Nikshych and V. Ostrik, *Tensor categories*, Mathematical Surveys and
  Monographs 205, AMS, 2015, Section 2.10, on exact pairings and the zigzag identities.
-/

public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace TauCeti.Floer

section Symmetric

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- The **cap pairing** of the cap lines `C⁺ = o ⊗ λ` and `C⁻ = λ' ⊗ o'`, for an exact pairing of
`o` and `o'` and a pairing `P` of `λ` and `λ'` twisted by `V`: the pairing of `C⁻` and `C⁺` twisted
by `V` whose evaluation `C⁺ ⊗ C⁻ ⟶ V` is the interchange of `C⁺` and `C⁻` followed by the
negative-first evaluation, and whose coevaluation `V ⟶ C⁻ ⊗ C⁺` is the sewing map. It is the swap
of the tensor product of the pairing of `o` and `o'` with `P`. -/
def capPairing (o o' : C) [ExactPairing o o'] {l l' V : C} (P : TwistedPairing l l' V) :
    TwistedPairing (l' ⊗ o') (o ⊗ l) V :=
  (P.tensor (X₁ := o) (Y₁ := o')).swap

variable (o o' : C) [ExactPairing o o'] {l l' V : C} (P : TwistedPairing l l' V)

/-- The cap pairing `C⁺ ⊗ C⁻ ⟶ V` is the interchange of `C⁺` and `C⁻` followed by the
negative-first evaluation `C⁻ ⊗ C⁺ ⟶ V`, which contracts `o' ⊗ o` and then pairs `λ' ⊗ λ`. -/
@[simp]
theorem capPairing_evaluation :
    (capPairing o o' P).evaluation =
      (β_ (o ⊗ l) (l' ⊗ o')).hom ≫ 𝟙 _ ⊗≫ l' ◁ (ε_ o o' ▷ l) ⊗≫ P.evaluation := by
  rw [capPairing, TwistedPairing.swap_evaluation, TwistedPairing.tensor_evaluation]

/-- The sewing coevaluation `V ⟶ C⁻ ⊗ C⁺` of the cap pairing is the coevaluation of the
negative-first evaluation, which expands `V` into `λ ⊗ λ'` inside `o ⊗ o'`, followed by the
interchange of `C⁺` and `C⁻`. -/
@[simp]
theorem capPairing_coevaluation :
    (capPairing o o' P).coevaluation =
      ((λ_ V).inv ≫ η_ o o' ▷ V ⊗≫ o ◁ ((β_ o' V).hom ≫ P.coevaluation ▷ o') ⊗≫ 𝟙 _) ≫
        (β_ (o ⊗ l) (l' ⊗ o')).hom := by
  rw [capPairing, TwistedPairing.swap_coevaluation, TwistedPairing.tensor_coevaluation,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding (l' ⊗ o') (o ⊗ l)]

end Symmetric

section Complexes

variable {R : Type v} [CommRing R] (O O' : CochainComplex (ModuleCat.{v} R) ℤ)
  [ExactPairing O O'] {L L' V : CochainComplex (ModuleCat.{v} R) ℤ} (P : TwistedPairing L L' V)

/-- On the cap lines, in cochain degrees `p = -(n + μ)` and `q = μ - n`, the Koszul sign
`(-1)^(p q)` is `(-1)^(μ + n)`. -/
private theorem negOnePow_mul_eq_negOnePow_add (μ n p q : ℤ) (hp : p = -(n + μ))
    (hq : q = μ - n) : (p * q).negOnePow = (μ + n).negOnePow := by
  have hpq : p * q = n * n - μ * μ := by subst hp hq; ring
  rw [hpq, Int.negOnePow_sub, Int.negOnePow_mul_self, Int.negOnePow_mul_self, Int.negOnePow_add,
    mul_comm n.negOnePow]

/-- **The Koszul sign of the cap pairing.** For cochain complexes of modules, on the summand
`C⁺_p ⊗ C⁻_q` of degree `j = p + q`, the cap pairing is `(-1)^(p q)` times the unsigned flip into
`C⁻_q ⊗ C⁺_p` followed by the negative-first evaluation. -/
theorem ιTensorObj_capPairing_evaluation_f (p q j : ℤ) (h : p + q = j) :
    HomologicalComplex.ιTensorObj (O ⊗ L) (L' ⊗ O') p q j h ≫
        (capPairing O (O') P).evaluation.f j =
      (p * q).negOnePow • ((β_ ((O ⊗ L).X p) ((L' ⊗ O').X q)).hom ≫
        HomologicalComplex.ιTensorObj (L' ⊗ O') (O ⊗ L) q p j (by omega) ≫
          (P.tensor (X₁ := O) (Y₁ := O')).evaluation.f j) :=
  TwistedPairing.ιTensorObj_swap_evaluation_f _ p q j h

/-- **The coefficient `(-1)^(μ + n)` of the cap pairing.** On the cap lines of homological degrees
`n + μ` and `n - μ`, which sit in cochain degrees `-(n + μ)` and `μ - n`, the cap pairing is
`(-1)^(μ + n)` times the unsigned flip followed by the negative-first evaluation. -/
theorem ιTensorObj_capPairing_evaluation_f_of_eq (μ n p q j : ℤ) (hp : p = -(n + μ))
    (hq : q = μ - n) (h : p + q = j) :
    HomologicalComplex.ιTensorObj (O ⊗ L) (L' ⊗ O') p q j h ≫
        (capPairing O (O') P).evaluation.f j =
      (μ + n).negOnePow • ((β_ ((O ⊗ L).X p) ((L' ⊗ O').X q)).hom ≫
        HomologicalComplex.ιTensorObj (L' ⊗ O') (O ⊗ L) q p j (by omega) ≫
          (P.tensor (X₁ := O) (Y₁ := O')).evaluation.f j) := by
  rw [ιTensorObj_capPairing_evaluation_f, negOnePow_mul_eq_negOnePow_add μ n p q hp hq]

/-- **The Koszul sign of the sewing coevaluation.** For cochain complexes of modules, if the
coevaluation of the negative-first evaluation in degree `j` is `g` followed by the inclusion of the
summand `C⁺_p ⊗ C⁻_q`, then the sewing coevaluation in degree `j` is `(-1)^(p q)` times `g`
followed by the unsigned flip into `C⁻_q ⊗ C⁺_p`. -/
theorem capPairing_coevaluation_f (p q j : ℤ) (h : p + q = j)
    (g : V.X j ⟶ (O ⊗ L).X p ⊗ (L' ⊗ O').X q)
    (hg : (P.tensor (X₁ := O) (Y₁ := O')).coevaluation.f j =
      g ≫ HomologicalComplex.ιTensorObj (O ⊗ L) (L' ⊗ O') p q j h) :
    (capPairing O (O') P).coevaluation.f j =
      (p * q).negOnePow • (g ≫ (β_ ((O ⊗ L).X p) ((L' ⊗ O').X q)).hom ≫
        HomologicalComplex.ιTensorObj (L' ⊗ O') (O ⊗ L) q p j (by omega)) :=
  TwistedPairing.swap_coevaluation_f_of_coevaluation_f_eq _ p q j h g hg

/-- **The coefficient `(-1)^(μ + n)` of the sewing coevaluation.** If the coevaluation of the
negative-first evaluation lands in the cap lines, in cochain degrees `-(n + μ)` and `μ - n`, then
the sewing coevaluation is `(-1)^(μ + n)` times it followed by the unsigned flip. -/
theorem capPairing_coevaluation_f_of_eq (μ n p q j : ℤ) (hp : p = -(n + μ)) (hq : q = μ - n)
    (h : p + q = j) (g : V.X j ⟶ (O ⊗ L).X p ⊗ (L' ⊗ O').X q)
    (hg : (P.tensor (X₁ := O) (Y₁ := O')).coevaluation.f j =
      g ≫ HomologicalComplex.ιTensorObj (O ⊗ L) (L' ⊗ O') p q j h) :
    (capPairing O (O') P).coevaluation.f j =
      (μ + n).negOnePow • (g ≫ (β_ ((O ⊗ L).X p) ((L' ⊗ O').X q)).hom ≫
        HomologicalComplex.ιTensorObj (L' ⊗ O') (O ⊗ L) q p j (by omega)) := by
  rw [capPairing_coevaluation_f O O' P p q j h g hg, negOnePow_mul_eq_negOnePow_add μ n p q hp hq]

end Complexes

end TauCeti.Floer
