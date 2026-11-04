/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.FullSetOfSections.Basic
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Etale.Basic
import TauCeti.RingTheory.Etale.Discriminant
import TauCeti.Algebra.Algebra.Pi
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Smooth.Flat

/-!
# Full sets of sections of finite étale algebras

For a finite étale algebra `B` over a ring `A`, a family of sections `sᵢ : B →ₐ[A] A`
is full precisely when evaluation `b ↦ (sᵢ(b))ᵢ` is bijective. Thus, in the étale case,
a full set labels the disjoint copies of the base, without repetitions. This is the
splitting interpretation used in the étale-quotient criterion for generators of extensions.
No reducedness assumption on the base, or invertibility assumption on the rank, is needed.

The trace identity of a full set identifies its trace matrix with the Gram matrix of
evaluation. Étaleness makes its discriminant a unit, so evaluation is invertible locally
on the base. Conversely, an evaluation isomorphism transports the full set of coordinate
projections on a product of copies of the base.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §§1.8 and 1.11,
  especially the étale splitting argument in 1.11.2.
-/

public section

open scoped TensorProduct
open Matrix

namespace TauCeti

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type*} [Fintype ι] {s : ι → B →ₐ[A] A}

/-- In a basis indexed by a full set of sections, the algebra's discriminant is the
square of the determinant of the evaluation matrix. -/
theorem IsFullSetOfSections.discr_eq_det_pi_sq (h : IsFullSetOfSections s)
    [DecidableEq ι] (b : Module.Basis ι A B) :
    Algebra.discr A b = (Matrix.of fun i j ↦ s i (b j)).det ^ 2 := by
  classical
  have : Module.Free A B := .of_basis b
  have : Module.Finite A B := .of_basis b
  have ht : Algebra.traceMatrix A b =
      (Matrix.of fun i j ↦ s i (b j))ᵀ * (Matrix.of fun i j ↦ s i (b j)) := by
    ext i j
    simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, h.trace_eq_sum,
      Matrix.mul_apply]
  rw [Algebra.discr_def, ht, Matrix.det_mul, Matrix.det_transpose, pow_two]

section Free

variable [Module.Free A B] [Module.Finite A B]

-- Match the basis index with the cardinality of the full set.
private theorem IsFullSetOfSections.bijective_pi_of_free [Algebra.Etale A B]
    (h : IsFullSetOfSections s) : Function.Bijective (AlgHom.pi s) := by
  classical
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton B := Module.subsingleton A B
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  let b := (Module.Free.chooseBasis A B).reindex (Fintype.equivOfCardEq
    ((Module.finrank_eq_card_chooseBasisIndex A B).symm.trans h.card_eq_finrank.symm))
  -- The evaluation matrix is invertible because its Gram determinant is a unit.
  apply _root_.AlgHom.pi_bijective_of_isUnit_det s b
  have hd := (Algebra.etale_iff_isUnit_discr A B b).mp inferInstance
  rw [h.discr_eq_det_pi_sq b] at hd
  exact (isUnit_pow_iff two_ne_zero).mp hd

end Free

/-- Evaluation at a full set of sections of a finite étale algebra is bijective, even
when the algebra is not globally free over the base. -/
theorem IsFullSetOfSections.bijective_pi [Module.Finite A B] [Algebra.Etale A B]
    (h : IsFullSetOfSections s) : Function.Bijective (AlgHom.pi s) := by
  classical
  let T (P : Ideal A) [P.IsMaximal] := Localization.AtPrime P
  let f (P : Ideal A) [P.IsMaximal] := TensorProduct.mk A (T P) B 1
  let g (P : Ideal A) [P.IsMaximal] := TensorProduct.mk A (T P) (ι → A) 1
  apply bijective_of_isLocalized_maximal (fun P _ ↦ T P ⊗[A] B) f
    (fun P _ ↦ T P ⊗[A] (ι → A)) g (AlgHom.pi s).toLinearMap
  intro P _
  have : Module.Free (T P) (T P ⊗[A] B) := Module.free_of_flat_of_isLocalRing
  let e := Algebra.TensorProduct.piScalarRight A (T P) (T P) ι
  let q := AlgHom.pi fun i ↦ (s i).sectionBaseChange (T P)
  have hq : Function.Bijective q := (h.baseChange (T P)).bijective_pi_of_free
  have he : (IsLocalizedModule.map P.primeCompl (f P) (g P)) (AlgHom.pi s).toLinearMap =
      (e.symm.toLinearMap.comp q.toLinearMap).restrictScalars A := by
    apply IsLocalizedModule.linearMap_ext P.primeCompl (f P) (g P)
    apply LinearMap.ext
    intro b
    simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply,
      LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]
    apply e.injective
    ext i
    simp [f, g, e, q, Algebra.smul_def]
  rw [he]
  exact e.symm.bijective.comp hq

/-- A family of sections of a finite étale algebra is full if and only if its evaluation
map identifies the algebra with the product of copies of the base indexed by the family. -/
theorem isFullSetOfSections_iff_bijective_pi [Module.Finite A B] [Algebra.Etale A B] :
    IsFullSetOfSections s ↔ Function.Bijective (AlgHom.pi s) :=
  ⟨fun h ↦ h.bijective_pi, isFullSetOfSections_of_bijective_pi⟩

end TauCeti
