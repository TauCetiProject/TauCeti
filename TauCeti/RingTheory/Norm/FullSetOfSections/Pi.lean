/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.FullSetOfSections.Basic
public import TauCeti.RingTheory.TensorProduct.Pi

/-!
# Full sets of sections of disjoint unions

For a finite family of finite flat algebras, a family of sections assigned to the factors is
full on their product exactly when each component family is full. Geometrically this says
that fullness on a finite disjoint union can be tested on each open-and-closed component.

This componentwise criterion is used when a finite étale quotient is split and its fibres
are studied separately. The algebras need not be globally free and the component families
may be empty.

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.8 and 1.11.
-/

public section

open TensorProduct

namespace TauCeti

universe u v w

variable {A : Type u} [CommRing A] {κ : Type v} [Fintype κ]
  {B : κ → Type w} [∀ k, CommRing (B k)] [∀ k, Algebra A (B k)]
  {ι : κ → Type*} [∀ k, Fintype (ι k)]
  (s : ∀ k, ι k → B k →ₐ[A] A)

private theorem isFullSetOfSections_pi_iff_of_free
    [∀ k, Module.Free A (B k)] [∀ k, Module.Finite A (B k)] :
    (IsFullSetOfSections fun p : Σ k, ι k ↦
      (s p.1 p.2).comp (Pi.evalAlgHom A B p.1)) ↔
      ∀ k, IsFullSetOfSections (s k) := by
  classical
  constructor
  · intro h k
    rw [isFullSetOfSections_iff]
    intro T _ _ _ f
    let e := Algebra.TensorProduct.piRight A T T B
    let x : ∀ j, T ⊗[A] B j := Function.update 1 k f
    have hx := h.norm_eq T (e.symm x)
    rw [← Algebra.norm_eq_of_algEquiv e, e.apply_symm_apply, Algebra.norm_pi,
      Fintype.prod_sigma] at hx
    dsimp only [e] at hx
    simp only [AlgHom.sectionBaseChange_comp_evalAlgHom, AlgEquiv.apply_symm_apply] at hx
    have hn : (∏ j, Algebra.norm T (x j)) = Algebra.norm T f := by
      simpa [x] using (Fintype.prod_eq_single (f := fun j ↦ Algebra.norm T (x j)) k
        (fun j hj ↦ by simp [x, hj]))
    have hs : (∏ j, ∏ i, (s j i).sectionBaseChange T (x j)) =
        ∏ i, (s k i).sectionBaseChange T f := by
      simpa [x] using (Fintype.prod_eq_single
        (f := fun j ↦ ∏ i, (s j i).sectionBaseChange T (x j)) k
        (fun j hj ↦ by simp [x, hj]))
    exact hn.symm.trans (hx.trans hs)
  · intro h
    rw [isFullSetOfSections_iff]
    intro T _ _ _ f
    rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.piRight A T T B),
      Algebra.norm_pi, Fintype.prod_sigma]
    simp_rw [(h _).norm_eq T, AlgHom.sectionBaseChange_comp_evalAlgHom]

/-- **Disjoint unions** (Katz–Mazur 1.8.4). Fullness of a family on a finite disjoint union
is equivalent to fullness on each component. The sections of the product algebra are indexed by
the disjoint union of the component index types and factor through the corresponding projections. -/
theorem isFullSetOfSections_pi_iff [∀ k, Module.Finite A (B k)] [∀ k, Module.Flat A (B k)] :
    (IsFullSetOfSections fun p : Σ k, ι k ↦
      (s p.1 p.2).comp (Pi.evalAlgHom A B p.1)) ↔
      ∀ k, IsFullSetOfSections (s k) := by
  classical
  have : Module.Flat A (∀ k, B k) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A)).symm
  have transport (T : Type u) [CommRing T] [Algebra A T] :
      (IsFullSetOfSections fun p : Σ k, ι k ↦
        ((s p.1 p.2).comp (Pi.evalAlgHom A B p.1)).sectionBaseChange T) ↔
      IsFullSetOfSections fun p : Σ k, ι k ↦
        ((s p.1 p.2).sectionBaseChange T).comp
          (Pi.evalAlgHom T (fun k ↦ T ⊗[A] B k) p.1) := by
    rw [← isFullSetOfSections_comp_algEquiv_iff (Algebra.TensorProduct.piRight A T T B)]
    apply Iff.of_eq
    congr 1
    funext p
    apply AlgHom.ext
    intro x
    exact (s p.1 p.2).sectionBaseChange_comp_evalAlgHom T x
  have local_iff (P : Ideal A) [P.IsMaximal] :
      (IsFullSetOfSections fun p : Σ k, ι k ↦
        ((s p.1 p.2).comp (Pi.evalAlgHom A B p.1)).sectionBaseChange
          (Localization.AtPrime P)) ↔
      ∀ k, IsFullSetOfSections fun i ↦ (s k i).sectionBaseChange (Localization.AtPrime P) := by
    have : ∀ j, Module.Free (Localization.AtPrime P) (Localization.AtPrime P ⊗[A] B j) :=
      fun j ↦ Module.free_of_flat_of_isLocalRing
    exact (transport _).trans (isFullSetOfSections_pi_iff_of_free
      (fun j i ↦ (s j i).sectionBaseChange (Localization.AtPrime P)))
  constructor
  · intro h k
    exact IsFullSetOfSections.of_localization_maximal fun P _ ↦
      (local_iff P).mp (h.baseChange _) k
  · intro h
    exact IsFullSetOfSections.of_localization_maximal fun P _ ↦
      (local_iff P).mpr fun k ↦ (h k).baseChange _

end TauCeti
