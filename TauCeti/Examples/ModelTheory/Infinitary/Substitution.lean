/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.Substitution

/-!
# Substitution and relabelling regression examples

These importing-module checks exercise substitution of terms with function symbols, mixed
free/bound relabelling, the last-slot binding convention, and infinite and empty branching.
Only the public operation and realization equations are used.
-/

public section

namespace TauCeti

open FirstOrder Language
open BoundedFormulaInf

universe u v uι w

-- Substitution of a function term under a quantifier, not merely renaming variables.
example {L : Language.{u, v}} {ι : Type uι} {M : Type w} [L.Structure M]
    (c : L.Functions 1) (v : Unit → M) :
    (subst
      ((Language.BoundedFormulaInf.equal (.var (.inl ()))
        (.var (.inr (0 : Fin 1)))).all : L.FormulaInf ι Unit)
      (fun _ => .func c (fun _ => .var ()))).Realize v Fin.elim0 ↔
      ∀ y : M, Structure.funMap c (fun _ => v ()) = y := by
  simp [Fin.snoc_zero]

-- An actual infinite conjunction remains an infinite conjunction after substitution.
example {L : Language.{u, v}} {M : Type w} [L.Structure M]
    (f : ℕ → L.Term Unit) (v : Unit → M) :
    (subst
      (.iInf (fun k => .equal (.var (.inl k)) (.var (.inr (0 : Fin 1))))) f).Realize
        v (fun _ => v ()) ↔ ∀ k, (f k).realize v = v () := by
  simp

-- Relabelling uses both summands of its target and shifts an existing bound slot.
example {L : Language.{u, v}} {ι : Type uι} {M : Type w} [L.Structure M]
    (v : Unit → M) (xs : Fin 2 → M) :
    (relabel (fun b : Bool => if b then Sum.inl () else Sum.inr (0 : Fin 1))
      ((.equal (.var (.inl true)) (.var (.inr (0 : Fin 1)))) ⊓
        (.equal (.var (.inl false)) (.var (.inr (0 : Fin 1)))) :
          L.BoundedFormulaInf ι Bool 1)).Realize v xs ↔
      v () = xs 1 ∧ xs 0 = xs 1 := by
  rw [realize_relabel]
  simp

-- The new slot is not captured by a quantifier: the latter still binds the last slot.
example {L : Language.{u, v}} {ι : Type uι} {M : Type w} [L.Structure M]
    (v : Empty → M) (xs : Fin 1 → M) :
    (relabel (fun _ : Unit => Sum.inr (0 : Fin 1))
      ((Language.BoundedFormulaInf.equal (.var (.inl ()))
        (.var (.inr (0 : Fin 1)))).all :
        L.FormulaInf ι Unit)).Realize v xs ↔ ∀ y : M, xs 0 = y := by
  rw [realize_relabel]
  simp [Fin.snoc_zero]

-- Empty branching remains semantically neutral under either operation.
example {L : Language.{u, v}} {M : Type w} [L.Structure M]
    (f : Unit → L.Term Unit) (v : Unit → M) :
    (subst (.iInf (fun i : Empty => i.elim) : L.FormulaInf Empty Unit) f).Realize
      v Fin.elim0 := by
  simp

example {L : Language.{u, v}} {M : Type w} [L.Structure M]
    (g : Unit → Unit ⊕ Fin 1) (v : Unit → M) (xs : Fin 1 → M) :
    ¬ (relabel g (.iSup (fun i : Empty => i.elim) : L.FormulaInf Empty Unit)).Realize v xs := by
  simp

end TauCeti
