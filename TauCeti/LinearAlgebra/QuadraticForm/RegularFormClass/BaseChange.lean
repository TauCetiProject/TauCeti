/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Free
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Basic

/-!
# Base change of regular-form classes

Extending scalars sends a diagonal presentation to the presentation obtained by mapping each
unit coefficient. This gives a canonical additive map on isometry classes of regular quadratic
forms, compatible with identity extensions and scalar towers.

## Main definitions

* `TauCeti.RegularFormPresentation.baseChange`: extension of a diagonal presentation.
* `TauCeti.RegularFormClass.baseChange`: extension of an isometry class of regular forms.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
-/

public section
noncomputable section

open scoped TensorProduct
open QuadraticMap QuadraticForm

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-! ### Base change of presentations -/

/-- Extend a diagonal presentation along a field extension by mapping each unit coefficient. -/
@[reducible]
def RegularFormPresentation.baseChange (L : Type v) [Field L] [Algebra K L]
    (p : RegularFormPresentation K) : RegularFormPresentation L :=
  ⟨p.1, fun i ↦ Units.map (algebraMap K L) (p.2 i)⟩

/-- Base change is computed by mapping the coefficients of a presentation. -/
@[simp]
theorem RegularFormPresentation.baseChange_mk (n : ℕ) (w : Fin n → Kˣ) :
    RegularFormPresentation.baseChange L ⟨n, w⟩ =
      ⟨n, fun i ↦ Units.map (algebraMap K L) (w i)⟩ := (rfl)

/-- Base change does not alter the rank of a presentation. -/
@[simp]
theorem RegularFormPresentation.fst_baseChange (p : RegularFormPresentation K) :
    (p.baseChange L).1 = p.1 := (rfl)

/-- The coefficients of a base-changed presentation are the images of the original
coefficients. -/
@[simp]
theorem RegularFormPresentation.baseChange_apply (p : RegularFormPresentation K) (i : Fin p.1) :
    ((p.baseChange L).2 (Fin.cast (RegularFormPresentation.fst_baseChange p).symm i) : L) =
      algebraMap K L (p.2 i : K) := (rfl)

/-- Extending a presentation along the identity extension changes nothing. -/
@[simp]
theorem RegularFormPresentation.baseChange_self (p : RegularFormPresentation K) :
    p.baseChange K = p := by
  apply Sigma.ext rfl
  apply heq_of_eq
  funext i
  apply Units.ext
  simp

/-- Successive base changes agree with base change along the composite extension. -/
@[simp]
theorem RegularFormPresentation.baseChange_baseChange {M : Type w} [Field M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] (p : RegularFormPresentation K) :
    (p.baseChange L).baseChange M = p.baseChange M := by
  rcases p with ⟨n, w⟩
  rw [RegularFormPresentation.baseChange_mk, RegularFormPresentation.baseChange_mk]
  congr 1
  funext i
  apply Units.ext
  rw [Units.coe_map, Units.coe_map, Units.coe_map]
  exact (IsScalarTower.algebraMap_apply K L M (w i)).symm

variable [Invertible (2 : K)]

/-- Extending the scalars of a presented form gives the form presented by the mapped
coefficients. -/
def presentedFormBaseChangeIsometryEquiv (p : RegularFormPresentation K) :
    ((presentedForm p).baseChange L).IsometryEquiv (presentedForm (p.baseChange L)) := by
  rcases p with ⟨n, w⟩
  exact
    { toLinearEquiv :=
        Algebra.TensorProduct.equivPiOfFiniteBasis L (Pi.basisFun K (Fin n))
      map_app' := fun x ↦ by
        have h : (presentedForm (RegularFormPresentation.baseChange L
            (⟨n, w⟩ : RegularFormPresentation K))).comp
            (Algebra.TensorProduct.equivPiOfFiniteBasis L
              (Pi.basisFun K (Fin n))).toLinearMap =
              (presentedForm (⟨n, w⟩ : RegularFormPresentation K)).baseChange L := by
          apply _root_.baseChange_ext
          intro a
          have heval : (Algebra.TensorProduct.equivPiOfFiniteBasis L
              (Pi.basisFun K (Fin n))).toLinearMap (1 ⊗ₜ a) =
                fun i ↦ algebraMap K L (a i) := by
            ext i
            simp [Algebra.TensorProduct.equivPiOfFiniteBasis, Algebra.smul_def]
          rw [QuadraticMap.comp_apply, QuadraticForm.baseChange_tmul, heval,
            presentedForm_apply, presentedForm_apply]
          simp [Algebra.smul_def, map_sum, map_mul]
        exact DFunLike.congr_fun h x }

/-- Base change of presented forms, stated as `QuadraticMap.Equivalent`. -/
theorem equivalent_presentedForm_baseChange (p : RegularFormPresentation K) :
    ((presentedForm p).baseChange L).Equivalent (presentedForm (p.baseChange L)) :=
  ⟨presentedFormBaseChangeIsometryEquiv p⟩

/-! ### Base change of regular-form classes -/

/-- Extend an isometry class of regular quadratic forms along a field extension. -/
def RegularFormClass.baseChange (L : Type v) [Field L] [Algebra K L] :
    RegularFormClass K → RegularFormClass L :=
  Quotient.map (RegularFormPresentation.baseChange L) fun p q h ↦ by
    exact (equivalent_presentedForm_baseChange p).symm.trans
      ((h.baseChange L).trans (equivalent_presentedForm_baseChange q))

/-- Base change is computed by mapping a representative presentation. -/
@[simp]
theorem RegularFormClass.baseChange_mk (p : RegularFormPresentation K) :
    RegularFormClass.baseChange L (Quotient.mk (regularFormSetoid K) p) =
      Quotient.mk (regularFormSetoid L) (p.baseChange L) := (rfl)

/-- Extending a regular-form class along the identity extension changes nothing. -/
@[simp]
theorem RegularFormClass.baseChange_self (c : RegularFormClass K) : c.baseChange K = c := by
  induction c using Quotient.inductionOn with
  | _ p => simp

/-- Successive base changes of regular-form classes agree with the composite extension. -/
@[simp]
theorem RegularFormClass.baseChange_baseChange {M : Type w} [Field M] [Algebra L M]
    [Algebra K M] [IsScalarTower K L M] (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    (c.baseChange L).baseChange M = c.baseChange M := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  induction c using Quotient.inductionOn with
  | _ p =>
    rw [RegularFormClass.baseChange_mk, RegularFormClass.baseChange_mk,
      RegularFormClass.baseChange_mk, RegularFormPresentation.baseChange_baseChange]

/-- Base change preserves rank. -/
@[simp]
theorem RegularFormClass.rank_baseChange (c : RegularFormClass K) :
    RegularFormClass.rank (c.baseChange L) = RegularFormClass.rank c := by
  induction c using Quotient.inductionOn with
  | _ p => simp

/-- Base change preserves orthogonal sums. -/
@[simp]
theorem RegularFormClass.baseChange_add (c d : RegularFormClass K) :
    (c + d).baseChange L = c.baseChange L + d.baseChange L := by
  induction c using Quotient.inductionOn with
  | _ p =>
    induction d using Quotient.inductionOn with
    | _ q =>
      rw [RegularFormClass.mk_add_mk, RegularFormClass.baseChange_mk,
        RegularFormClass.baseChange_mk, RegularFormClass.baseChange_mk,
        RegularFormClass.mk_add_mk, RegularFormClass.mk_eq_mk_iff]
      have hprod :
          (((presentedForm p).baseChange L).prod
            ((presentedForm q).baseChange L)).Equivalent
              ((presentedForm (p.baseChange L)).prod (presentedForm (q.baseChange L))) :=
        (equivalent_presentedForm_baseChange p).prod
          (equivalent_presentedForm_baseChange q)
      have hbaseProd :
          (_root_.QuadraticForm.baseChange L
            ((presentedForm p).prod (presentedForm q))).Equivalent
              (((presentedForm p).baseChange L).prod ((presentedForm q).baseChange L)) :=
        ⟨QuadraticForm.baseChangeProd (A := L) (presentedForm p) (presentedForm q)⟩
      exact (equivalent_presentedForm_baseChange _).symm.trans
        (((equivalent_presentedForm_append_prod p q).baseChange L).trans
          (hbaseProd.trans
            (hprod.trans
              (equivalent_presentedForm_append_prod (p.baseChange L) (q.baseChange L)).symm)))

/-- Base change preserves the zero class. -/
@[simp]
theorem RegularFormClass.baseChange_zero :
    RegularFormClass.baseChange L (0 : RegularFormClass K) = 0 := by
  rw [RegularFormClass.zero_def, RegularFormClass.baseChange_mk,
    RegularFormClass.zero_def, RegularFormClass.mk_eq_mk_iff]
  have h : presentedForm (RegularFormPresentation.baseChange L
      (⟨0, Fin.elim0⟩ : RegularFormPresentation K)) =
      presentedForm (⟨0, Fin.elim0⟩ : RegularFormPresentation L) := by
    congr 1
    refine Sigma.ext (x := RegularFormPresentation.baseChange L
      (⟨0, Fin.elim0⟩ : RegularFormPresentation K))
      (y := (⟨0, Fin.elim0⟩ : RegularFormPresentation L)) rfl ?_
    apply heq_of_eq
    funext i
    exact Fin.elim0 i
  rw [h]

-- Not `@[simp]`: `RegularFormClass K` is a semiring in downstream modules, where
-- `nsmul_eq_mul` rewrites the left-hand side and makes this declaration fail `simpNF`.
/-- Base change preserves finite orthogonal sums. -/
theorem RegularFormClass.baseChange_nsmul (n : ℕ) (c : RegularFormClass K) :
    (n • c).baseChange L = n • c.baseChange L := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul', RegularFormClass.baseChange_add, ih, succ_nsmul']

/-- Base change of regular-form classes as an additive monoid homomorphism. -/
def RegularFormClass.baseChangeAddMonoidHom (L : Type v) [Field L] [Algebra K L] :
    RegularFormClass K →+ RegularFormClass L where
  toFun := RegularFormClass.baseChange L
  map_zero' := RegularFormClass.baseChange_zero
  map_add' := RegularFormClass.baseChange_add

/-- The class-level construction agrees with base change of a regular quadratic form. -/
theorem RegularFormClass.baseChange_formClass {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.baseChange L (formClass Q hQ) =
      formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  obtain ⟨p, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [formClass_mk Q hQ p hp, RegularFormClass.baseChange_mk,
    ← formClass_presentedForm (p.baseChange L)]
  exact (formClass_eq_iff _ _ _ _).mpr
    ((hp.baseChange L).trans (equivalent_presentedForm_baseChange p)).symm

end TauCeti
