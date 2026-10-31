/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.ModelExistence.ModelExistence
import TauCeti.ModelTheory.Infinitary.Encoding

/-!
# Model existence applied to an atomic diagram

In a structure whose elements are all named by Henkin constants, the true atomic and negated
atomic sentences form a countable member of the satisfaction consistency property. Model
existence therefore realizes that diagram in a countable nonempty structure in any universe,
again with all elements named. Function symbols of arbitrary finite arity are allowed.

Unlike the full infinitary theory of the structure, this diagram is countable: the atomic
sentences form a countable type and taking their negations preserves countability.
-/

universe u v w w'

namespace TauCeti

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} [Countable (Σ n, L.Functions n)]
  [Countable (Σ n, L.Relations n)]

-- Apply the model existence engine, rather than merely transporting the given model.
example (M : Type w) [L[[ℕ]].Structure M]
    (hM : Function.Surjective fun c : ℕ => (L.con c : M)) :
    ∃ (N : Type w') (_ : L[[ℕ]].Structure N), Countable N ∧ Nonempty N ∧
      Theoryω.Model {φ : L[[ℕ]].Sentenceω |
        (φ.IsAtomic ∨ ∃ ψ : L[[ℕ]].Sentenceω, ψ.IsAtomic ∧ φ = ψ.not) ∧
          SentenceInf.Realize φ M} N ∧
      Function.Surjective (fun c : ℕ => (L.con c : N)) := by
  have : Countable (Σ n, L[[ℕ]].Relations n) :=
    (Sum.inr_injective (α := Σ n, L[[ℕ]].Functions n)).countable
  have : Countable (Σ n, L[[ℕ]].Functions n) :=
    (Sum.inl_injective (β := Σ n, L[[ℕ]].Relations n)).countable
  have hA : {φ : L[[ℕ]].Sentenceω | φ.IsAtomic}.Countable :=
    Set.countable_coe_iff.1 (BoundedFormulaInf.countable_subtype_isAtomic
      (L := L[[ℕ]]) (ι := ℕ) (α := Empty) (n := 0))
  let D : L[[ℕ]].Theoryω := {φ |
    (φ.IsAtomic ∨ ∃ ψ : L[[ℕ]].Sentenceω, ψ.IsAtomic ∧ φ = ψ.not) ∧
      SentenceInf.Realize φ M}
  have hD : D.Model M := Theoryω.model_iff.2 fun _ hφ => hφ.2
  have hDc : D.Countable := by
    apply (hA.union (hA.image BoundedFormulaInf.not)).mono
    rintro φ ⟨hφ | ⟨ψ, hψ, rfl⟩, _⟩
    · exact Or.inl hφ
    · exact Or.inr ⟨ψ, hψ, rfl⟩
  exact (ConsistencyProperty.ofModel M hM).model_existence
    (ConsistencyProperty.mem_ofModel_iff.2 hD) hDc

end TauCeti
