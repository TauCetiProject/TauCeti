/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.SimpleModule.WedderburnArtin
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import TauCeti.RingTheory.Idempotents.Corner.Basic
import TauCeti.RingTheory.Idempotents.Matrix
import TauCeti.RingTheory.TwoSidedIdeal.Full

/-!
# A full idempotent with a basic corner in a semisimple ring

Every semisimple ring `R` has a **full** idempotent `e`, one with `TwoSidedIdeal.span {e} = ⊤`,
whose corner ring `eRe` is a finite product of division rings. By Artin–Wedderburn,
`R ≅ ∏ᵢ Matₙᵢ(Dᵢ)`; taking the matrix unit `E₁₁` in every block gives an idempotent whose corner
is `∏ᵢ Dᵢ`, and it is full because each `E₁₁` is full in its block.

A full idempotent makes `R` Morita equivalent to its corner `eRe`
(`IsIdempotentElem.isMoritaEquivalent_corner`), and a product of division rings is the
semisimple case of a basic ring (`TauCeti.isBasic_iff_pi_divisionRing`). So this is the selection
step of the reduction of a finite-dimensional algebra `A` to a basic one: an idempotent chosen
here in the semisimple quotient `A ⧸ Ring.jacobson A` lifts to a full idempotent of `A`, whose
corner is then basic. In module-theoretic terms, the left ideal `R e` constructed here is a sum of
one copy of each simple `R`-module, matching the classical description of the basic algebra as
the endomorphism ring of one indecomposable projective per simple module.

## Main results

* `IsSemisimpleRing.exists_isIdempotentElem_full_corner_ringEquiv_pi_divisionRing`: a semisimple
  ring has a full idempotent whose corner is a finite product of division rings.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, CUP (2006), Section I.6.
* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189, Springer (1999), §18B.
-/

public section

namespace IsSemisimpleRing

universe u

/-- **A semisimple ring has a full idempotent whose corner is a finite product of division
rings.** Writing `R ≅ ∏ᵢ Matₙᵢ(Dᵢ)` by Artin–Wedderburn, the idempotent is the matrix unit `E₁₁`
of every block: its corner is `∏ᵢ Dᵢ`, and it generates `R` as a two-sided ideal. -/
theorem exists_isIdempotentElem_full_corner_ringEquiv_pi_divisionRing (R : Type u) [Ring R]
    [IsSemisimpleRing R] :
    ∃ (e : R) (he : IsIdempotentElem e), TwoSidedIdeal.span {e} = ⊤ ∧
      ∃ (n : ℕ) (D : Fin n → Type u) (_ : ∀ i, DivisionRing (D i)),
        Nonempty (he.Corner ≃+* ∀ i, D i) := by
  classical
  obtain ⟨n, D, d, hD, hd, ⟨φ⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
  -- The matrix unit `E₁₁` in every Wedderburn block.
  let o (i : Fin n) : Fin (d i) := ⟨0, (hd i).pos⟩
  let E : ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i) := fun i ↦ Matrix.single (o i) (o i) 1
  have hE : IsIdempotentElem E :=
    Pi.isIdempotentElem_iff.mpr fun i ↦ Matrix.isIdempotentElem_single_one (o i)
  have hEfull : TwoSidedIdeal.span {E} = ⊤ :=
    TwoSidedIdeal.span_eq_top_iff_forall_span_image_eval_eq_top.mpr fun i ↦ by
      simpa [Set.image_singleton, E] using Matrix.twoSidedIdeal_span_single_one_eq_top (o i)
  refine ⟨φ.symm E, hE.map φ.symm, by simpa using TwoSidedIdeal.span_image_eq_top φ.symm hEfull,
    n, D, hD, ⟨?_⟩⟩
  exact (hE.cornerEquiv φ.symm).symm.trans <| hE.cornerPiEquiv.trans <|
    RingEquiv.piCongrRight fun i ↦ Matrix.cornerSingleOneEquiv (o i)

end IsSemisimpleRing
