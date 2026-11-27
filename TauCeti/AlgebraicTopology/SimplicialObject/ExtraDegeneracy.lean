/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
public import TauCeti.AlgebraicTopology.DoldKan.ModuleCat

/-!
# Augmented simplicial modules with an extra degeneracy on underlying sets

Let `X` be an augmented simplicial module over a ring `R`. Mathlib's
`SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv` shows that an extra degeneracy of `X`
in the category of modules makes the augmentation `C(X) ⟶ X₋₁[0]` of the alternating face map
complex a homotopy equivalence. This file shows that an extra degeneracy of the underlying
augmented simplicial *set* already makes the augmentation a quasi-isomorphism
(`SimplicialObject.Augmented.ExtraDegeneracy.quasiIso_ε_of_forget`). The extra degeneracy need not
be additive, so it does not give a contracting homotopy of `C(X)`; this is the situation of the
standard polynomial resolution of a commutative algebra, whose extra degeneracy sends an element to
the polynomial variable it indexes.

## Main results

* `SimplicialObject.Augmented.ExtraDegeneracy.quasiIso_ε_of_forget`: an extra degeneracy of the
  underlying augmented simplicial set makes the augmentation of the alternating face map complex a
  quasi-isomorphism.

## Implementation notes

In positive degrees, `C(X)` is exact as soon as every simplex `x` with all faces zero is a boundary
(`SimplicialObject.alternatingFaceMapComplex_exactAt_succ_iff`). For such `x`, the simplicial
identities for the extra degeneracy `s` show that `s x - s 0` has all faces `δᵢ`, `i ≥ 1`, zero and
face `δ₀` equal to `x`, so its differential is `x`. The subtraction of `s 0` is needed because `s`
is only a map of sets. In degree zero, the section `s'` of the augmentation gives surjectivity on
homology, and the same correction bounds the elements of the kernel of the augmentation.

## References

This builds on Joël Riou's Mathlib API for extra degeneracies
(`Mathlib.AlgebraicTopology.ExtraDegeneracy`) and for the Dold–Kan projector `DoldKan.PInfty`,
through `SimplicialObject.alternatingFaceMapComplex_exactAt_succ_iff`.
-/

public section

open CategoryTheory Opposite Simplicial AlgebraicTopology

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

universe u

variable {R : Type*} [Ring R] {X : Augmented (ModuleCat.{u} R)}
  (ed : ExtraDegeneracy (((whiskering _ _).obj (forget (ModuleCat R))).obj X))

include ed

/-- The extra degeneracy `s n`, as a map between the underlying sets of the terms of `X.left`.
The terms of the underlying simplicial set of `X.left` are these sets by definition, so this only
changes the stated type of `ed.s n`, which lets the module operations of `X.left` apply to its
values. -/
private def sElem (n : ℕ) : X.left _⦋n⦌ → X.left _⦋n + 1⦌ := ed.s n

/-- The section `s'` of the augmentation, as a map from the underlying set of `X.right` to that of
the term of degree zero of `X.left`; as for `sElem`, only the stated type changes. -/
private def s'Elem : X.right → X.left _⦋0⦌ := ed.s'

private lemma hom_app_s'Elem (a : X.right) : X.hom.app (op ⦋0⦌) (ed.s'Elem a) = a :=
  congr($(ed.s'_comp_ε) a)

private lemma δ₀_sElem (n : ℕ) (x : X.left _⦋n⦌) : X.left.δ 0 (ed.sElem n x) = x :=
  congr($(ed.s_comp_δ₀ n) x)

private lemma δ_succ_sElem (n : ℕ) (i : Fin (n + 2)) (x : X.left _⦋n + 1⦌) :
    X.left.δ i.succ (ed.sElem (n + 1) x) = ed.sElem n (X.left.δ i x) :=
  congr($(ed.s_comp_δ n i) x)

private lemma δ₁_sElem_zero (x : X.left _⦋0⦌) :
    X.left.δ 1 (ed.sElem 0 x) = ed.s'Elem (X.hom.app (op ⦋0⦌) x) :=
  congr($(ed.s₀_comp_δ₁) x)

/-- In positive degrees, a simplex all of whose faces vanish is the boundary of `s x - s 0`. -/
private lemma exists_d_eq_of_δ_eq_zero {n : ℕ} {x : X.left _⦋n + 1⦌}
    (hx : ∀ i : Fin (n + 2), X.left.δ i x = 0) :
    ∃ y : X.left _⦋n + 2⦌,
      ((alternatingFaceMapComplex (ModuleCat R)).obj X.left).d (n + 2) (n + 1) y = x := by
  refine ⟨ed.sElem (n + 1) x - ed.sElem (n + 1) 0,
    (X.left.alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero fun i ↦ ?_).trans ?_⟩
  · simp [δ_succ_sElem, hx]
  · simp [δ₀_sElem]

/-- In degree zero, an element killed by the augmentation is the boundary of `s x - s 0`. -/
private lemma exists_d_eq_of_hom_app_eq_zero {x : X.left _⦋0⦌} (hx : X.hom.app (op ⦋0⦌) x = 0) :
    ∃ y : X.left _⦋1⦌, ((alternatingFaceMapComplex (ModuleCat R)).obj X.left).d 1 0 y = x := by
  refine ⟨ed.sElem 0 x - ed.sElem 0 0,
    (X.left.alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero fun i ↦ ?_).trans ?_⟩
  · simp [Fin.fin_one_eq_zero i, δ₁_sElem_zero, hx]
  · simp [δ₀_sElem]

/-- **Resolutions from extra degeneracies on sets.** If the underlying augmented simplicial set of
an augmented simplicial module `X` admits an extra degeneracy, then the augmentation
`C(X) ⟶ X₋₁[0]` of the alternating face map complex is a quasi-isomorphism. The extra degeneracy
is not assumed to be additive. -/
theorem quasiIso_ε_of_forget : QuasiIso (AlternatingFaceMapComplex.ε.app X) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (ChainComplex.prev ℕ 0)
      ChainComplex.next_nat_zero]
    refine ⟨fun a _ ↦ ⟨ed.s'Elem a, ?_, 0, ?_⟩, fun x _ b hb ↦ ed.exists_d_eq_of_hom_app_eq_zero ?_⟩
    · rw [HomologicalComplex.shape _ 0 0 (by simp)]
      exact LinearMap.zero_apply _
    · simp only [map_zero, AlternatingFaceMapComplex.ε_app_f_zero]
      rw [hom_app_s'Elem, sub_self]
    · rw [← AlternatingFaceMapComplex.ε_app_f_zero, ← hb]
      simp [HomologicalComplex.single_obj_d]
  | succ n =>
    exact (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ n)).2
      ((X.left.alternatingFaceMapComplex_exactAt_succ_iff).2 fun _ ↦ ed.exists_d_eq_of_δ_eq_zero)

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy
