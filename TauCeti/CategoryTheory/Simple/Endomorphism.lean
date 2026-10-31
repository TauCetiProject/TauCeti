/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# A converse to Schur's lemma when subobjects split

In a preadditive category with kernels in which every object is injective, an object is
simple exactly when its endomorphism ring is nontrivial and every nonzero endomorphism is a
unit. This criterion retains division endomorphism rings larger than the coefficient field,
as occur for representations over nonsplitting fields.

The nontriviality condition excludes zero objects. Splitting is essential for the converse:
an arbitrary object with a division endomorphism ring need not be simple.
`CategoryTheory.simple_of_ringEquiv_end` transports this criterion along a ring isomorphism
from a division ring. In a `k`-linear category with kernels in which every object is injective,
a one-dimensional endomorphism space suffices for simplicity over any field `k`
(`CategoryTheory.simple_of_finrank_end_eq_one`); algebraic closure is not needed.

## Finite-dimensional representations

After importing `Mathlib.RepresentationTheory.FinGroupCharZero`, apply
`CategoryTheory.simple_iff_nontrivial_end_and_isUnit V` directly to `V : FDRep k G`,
where `k` is a field, `G` is a finite group, and `[NeZero (Nat.card G : k)]`.
Mathlib's Maschke instance supplies injectivity of every such representation. In particular,
taking `V := TauCeti.indFDRep A` gives the endomorphism-division criterion for induction
over arbitrary fields whose characteristic does not divide the group order; neither
characteristic zero nor algebraic closure is needed.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §2.2, Schur's lemma.
* Mathlib's `CategoryTheory.isIso_of_hom_simple` supplies the forward implication.
  The converse uses the retraction argument of `FDRep.simple_iff_end_is_rank_one`, replacing
  its scalar-endomorphism hypothesis by invertibility of nonzero endomorphisms.
* `Module.nonempty_algEquiv_iff_finrank_eq_one` identifies a one-dimensional
  endomorphism algebra with the coefficient field.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasKernels C]

/-- If every object is injective, simplicity is equivalent to having a nontrivial
endomorphism ring in which every nonzero element is a unit. -/
theorem simple_iff_nontrivial_end_and_isUnit [∀ Y : C, Injective Y] (X : C) :
    Simple X ↔ Nontrivial (End X) ∧ ∀ f : End X, f ≠ 0 → IsUnit f := by
  constructor
  · intro h
    exact ⟨inferInstance, fun f hf => isUnit_iff_ne_zero.mpr hf⟩
  · rintro ⟨hX, hunit⟩
    have := hX
    refine ⟨fun {Y} f _ => ⟨fun hi hf => ?_, fun hf => ?_⟩⟩
    · have hzero : (1 : End X) = 0 := by
        apply End.ext
        simpa using congrArg (fun g : Y ⟶ X => inv f ≫ g) hf
      exact one_ne_zero hzero
    · let r := Injective.factorThru (𝟙 Y) f
      have hfr : f ≫ r = 𝟙 Y := Injective.comp_factorThru (𝟙 Y) f
      have hp : r ≫ f ≠ 0 := by
        intro h
        apply hf
        calc
          f = (f ≫ r) ≫ f := by rw [hfr, Category.id_comp]
          _ = 0 := by rw [Category.assoc, h, comp_zero]
      have hu : IsUnit (End.of (r ≫ f)) :=
        hunit _ (fun h => hp (congrArg End.asHom h))
      have : IsIso (r ≫ f) := (isUnit_iff_isIso _).mp hu
      have : Epi f := epi_of_epi r f
      have : IsSplitMono f := IsSplitMono.mk' ⟨r, hfr⟩
      exact isIso_of_epi_of_isSplitMono f

/-- If every object is injective, an object whose endomorphism ring is isomorphic to
 a division ring is simple. -/
theorem simple_of_ringEquiv_end [∀ Y : C, Injective Y] (X : C) {D : Type*}
    [DivisionRing D] (e : D ≃+* End X) : Simple X := by
  have : Nontrivial (End X) := e.symm.toEquiv.nontrivial
  refine (simple_iff_nontrivial_end_and_isUnit X).mpr ⟨inferInstance, fun f hf => ?_⟩
  have hne : e.symm f ≠ 0 := by simpa using hf
  simpa using (isUnit_iff_ne_zero.mpr hne).map e.toMonoidHom

/-- If every object is injective, a one-dimensional endomorphism space forces
simplicity over any field. The converse requires a scalar-Schur hypothesis. -/
theorem simple_of_finrank_end_eq_one (k : Type*) [Field k] [Linear k C]
    [∀ Y : C, Injective Y] (X : C) (h : Module.finrank k (X ⟶ X) = 1) :
    Simple X := by
  have hEnd : Module.finrank k (End X) = 1 :=
    (End.linearEquiv (R := k) (X := X)).finrank_eq.trans h
  obtain ⟨e⟩ := (Module.nonempty_algEquiv_iff_finrank_eq_one (R := k) (S := End X)).mpr hEnd
  exact simple_of_ringEquiv_end X e.toRingEquiv

end CategoryTheory
