/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Etale.FiniteEtaleSplit.Basic
public import TauCeti.RingTheory.Idempotents.DirectLimit

/-!
# Totally split models over a finite stage

Every totally split algebra over a directed colimit of commutative rings is the base change
of a totally split algebra over a stage, above any prescribed index. The construction lifts
the finitely many idempotents in a splitting presentation simultaneously. It retains all the
factors, including zero factors, so the number of sheets may vary on clopen components.

This is object descent within the class of totally split algebras. It does not assert that a
given algebra over an earlier stage is itself totally split at a later stage: that also
requires descending the isomorphism between that algebra and the totally split model.
-/

public section

open TensorProduct

universe v u

namespace Ring.DirectLimit

variable {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι] {G : ι → Type u}
  [∀ i, CommRing (G i)] {f : ∀ i j, i ≤ j → G i →+* G j}
  [DirectedSystem G (f · · ·)]

/-- A totally split algebra over a directed colimit has a totally split model over a stage
above any prescribed index. No finiteness hypothesis on the rings or flatness hypothesis on
the transition maps is required. -/
theorem exists_isTotallySplit_algEquiv_tensorProduct (T : Type*) [CommRing T]
    [Algebra (DirectLimit G (f · · ·)) T]
    (hT : TauCeti.Algebra.IsTotallySplit (DirectLimit G (f · · ·)) T) (i : ι) :
    ∃ j, i ≤ j ∧ ∃ (Tj : Type u) (_ : CommRing Tj) (_ : Algebra (G j) Tj),
      TauCeti.Algebra.IsTotallySplit (G j) Tj ∧
        letI := (of G (f · · ·) j).toAlgebra
        Nonempty (T ≃ₐ[DirectLimit G (f · · ·)] DirectLimit G (f · · ·) ⊗[G j] Tj) := by
  obtain ⟨m, e, he, ⟨φ⟩⟩ := TauCeti.Algebra.isTotallySplit_iff.mp hT
  obtain ⟨j, hij, e', he', hmap⟩ := exists_idempotents e he i
  let Tj := (k : Fin m) → G j ⧸ Ideal.span {1 - e' k}
  let := (of G (f · · ·) j).toAlgebra
  have hTj : TauCeti.Algebra.IsTotallySplit (G j) Tj :=
    TauCeti.Algebra.IsTotallySplit.of_algEquiv_pi e' he' (AlgEquiv.refl : Tj ≃ₐ[G j] Tj)
  let ψ : DirectLimit G (f · · ·) ⊗[G j] Tj ≃ₐ[DirectLimit G (f · · ·)]
      ((k : Fin m) → DirectLimit G (f · · ·) ⧸ Ideal.span {1 - e k}) :=
    (Algebra.TensorProduct.piRight (G j) _ _ _).trans <| AlgEquiv.piCongrRight fun k ↦
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot _ (Ideal.span {1 - e' k})).symm.trans
        (Ideal.quotientEquivAlgOfEq _ (by
          simp [Ideal.map_span, RingHom.algebraMap_toAlgebra, hmap]))
  exact ⟨j, hij, Tj, inferInstance, inferInstance, hTj, ⟨φ.trans ψ.symm⟩⟩

end Ring.DirectLimit
