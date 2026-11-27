/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Sum
public import TauCeti.NumberTheory.Dioph.MvPolynomial

/-!
# The finite normal form of Diophantine sets

Mathlib's `Dioph S`, for `S ⊆ ℕ^α`, asks for a witness type `β` in the universe of `α` and a
native polynomial function `p : Poly (α ⊕ β)` such that `x ∈ S` exactly when `p (x, y) = 0` for
some `y : β → ℕ`. The witness type may be infinite. This file shows that `S` is Diophantine
exactly when it is cut out by an integer polynomial `p : MvPolynomial (α ⊕ Fin m) ℤ` with
finitely many witnesses:

  `x ∈ S ↔ ∃ y : Fin m → ℕ, p (x, y) = 0`,

the evaluation taking place at the integer casts of `x` and `y`. The input type `α` is
arbitrary, possibly infinite, and the input variables are never renamed. Effective coding of
such polynomials, which the theorem of Matiyasevich, Robinson, Davis and Putnam needs, works with
this finite syntax.

The proof passes from `Poly` to `MvPolynomial` by `MvPolynomial.polyEquiv`, keeps only the
finitely many witness variables the polynomial involves (`MvPolynomial.exists_fin_rename_sumMap`)
and transports roots along the injective renaming of witnesses
(`MvPolynomial.exists_eval_rename_sumMap_eq_zero_iff`). The normal form is an existence
statement; it gives no procedure recovering `m` or `p` from a proof of `Dioph S`.

## Main results

* `Dioph.exists_fin_mvPolynomial`: a Diophantine set has a finite integer polynomial normal
  form.
* `Dioph.of_mvPolynomial`: conversely, a set cut out by an integer polynomial with witnesses of
  any type, in any universe, is Diophantine.
* `TauCeti.dioph_iff_exists_fin_mvPolynomial`: the finite normal form characterizes `Dioph`.

## References

* B. Poonen, *Undecidability in number theory*, Notices Amer. Math. Soc. 55 (2008),
  Definition 1 and footnote 4.
* The statement follows C. Freer's Lean development *hilbert10*, file `NormalForm.lean`
  (`dioph_iff_exists_fin_mvPolynomial`).
-/

public section

open MvPolynomial

universe u

variable {α : Type u} {S : Set (α → ℕ)}

namespace Dioph

/-- A Diophantine set is cut out by an integer polynomial with finitely many witness
variables. -/
theorem exists_fin_mvPolynomial (d : Dioph S) :
    ∃ (m : ℕ) (p : MvPolynomial (α ⊕ Fin m) ℤ),
      ∀ x, x ∈ S ↔ ∃ y : Fin m → ℕ, eval (Nat.cast ∘ Sum.elim x y) p = 0 := by
  obtain ⟨β, p, hp⟩ := d
  obtain ⟨m, f, hf, q, hq⟩ := exists_fin_rename_sumMap ((polyEquiv _).symm p)
  refine ⟨m, q, fun x ↦ (hp x).trans ?_⟩
  simp only [Sum.comp_elim]
  rw [← exists_eval_rename_sumMap_eq_zero_iff Nat.cast _ hf, ← hq]
  simp only [← Sum.comp_elim, eval_polyEquiv_symm]

/-- A set cut out by an integer polynomial, with natural witnesses indexed by any type `β` in
any universe, is Diophantine. -/
theorem of_mvPolynomial {β : Type*} (p : MvPolynomial (α ⊕ β) ℤ)
    (hp : ∀ x, x ∈ S ↔ ∃ y : β → ℕ, eval (Nat.cast ∘ Sum.elim x y) p = 0) : Dioph S := by
  obtain ⟨m, f, hf, q, rfl⟩ := exists_fin_rename_sumMap p
  refine ⟨ULift.{u} (Fin m), toPoly (rename (Sum.map id ULift.up) q), fun x ↦ (hp x).trans ?_⟩
  simp only [toPoly_apply, Sum.comp_elim]
  rw [exists_eval_rename_sumMap_eq_zero_iff Nat.cast _ hf,
    exists_eval_rename_sumMap_eq_zero_iff Nat.cast _ ULift.up_injective]

end Dioph

namespace TauCeti

/-- **Finite Diophantine normal form.** A set `S ⊆ ℕ^α` is Diophantine exactly when it is cut
out by an integer polynomial with finitely many natural witnesses. -/
theorem dioph_iff_exists_fin_mvPolynomial :
    Dioph S ↔ ∃ (m : ℕ) (p : MvPolynomial (α ⊕ Fin m) ℤ),
      ∀ x, x ∈ S ↔ ∃ y : Fin m → ℕ, eval (Nat.cast ∘ Sum.elim x y) p = 0 :=
  ⟨Dioph.exists_fin_mvPolynomial, fun ⟨_, p, hp⟩ ↦ Dioph.of_mvPolynomial p hp⟩

end TauCeti
