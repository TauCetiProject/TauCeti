/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Free
public import TauCeti.LinearAlgebra.QuadraticForm.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

/-!
# Base change of the Witt decomposition

Extending scalars sends a diagonal presentation to the presentation obtained by mapping each
unit coefficient.  This gives a canonical additive map on isometry classes of regular quadratic
forms.  The hyperbolic plane is preserved, so the Witt index cannot decrease under a field
extension.  It is unchanged when the anisotropic part remains anisotropic after base change.

## Main definitions

* `TauCeti.RegularFormPresentation.baseChange`: extension of a diagonal presentation.
* `TauCeti.RegularFormClass.baseChange`: extension of an isometry class of regular forms.

## Main results

* `TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange`: the Witt index cannot decrease.
* `TauCeti.RegularFormClass.wittIndex_baseChange_eq`: the index is unchanged when the extended
  anisotropic part is anisotropic.
* `QuadraticForm.wittIndex_le_wittIndex_baseChange`: the corresponding inequality for a regular
  quadratic form.
* `QuadraticForm.wittIndex_baseChange_eq`: the corresponding equality for a regular quadratic
  form whose anisotropic part remains anisotropic.

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

/-- Base change preserves finite orthogonal sums. -/
@[simp]
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

/-- Base change preserves the hyperbolic class. -/
@[simp]
theorem RegularFormClass.baseChange_hyperbolicClass :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.baseChange L (hyperbolicClass K) = hyperbolicClass L := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← formClass_hyperbolicPlane, RegularFormClass.baseChange_formClass,
    ← formClass_hyperbolicPlane]
  apply (formClass_eq_iff _ _ _ _).mpr
  have hK : hyperbolicPlane K =
      presentedForm (⟨2, ![1, -1]⟩ : RegularFormPresentation K) :=
    presentedForm_one_neg_one.symm
  have hL : presentedForm (RegularFormPresentation.baseChange L
      (⟨2, ![1, -1]⟩ : RegularFormPresentation K)) = hyperbolicPlane L := by
    rw [← presentedForm_one_neg_one]
    congr 1
    refine Sigma.ext (x := RegularFormPresentation.baseChange L
      (⟨2, ![1, -1]⟩ : RegularFormPresentation K))
      (y := (⟨2, ![1, -1]⟩ : RegularFormPresentation L)) rfl ?_
    apply heq_of_eq
    funext i
    apply Units.ext
    fin_cases i <;> simp
  rw [hK]
  exact (equivalent_presentedForm_baseChange _).trans (by
    rw [hL]
    exact QuadraticMap.Equivalent.refl _)

/-! ### Witt index -/

/-- The Witt index cannot decrease after extending the base field. -/
theorem RegularFormClass.wittIndex_le_wittIndex_baseChange (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.wittIndex c ≤ RegularFormClass.wittIndex (c.baseChange L) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  have hdecomp := congrArg (RegularFormClass.baseChange L)
    (RegularFormClass.wittDecomposition c)
  simp only [RegularFormClass.baseChange_add, RegularFormClass.baseChange_nsmul,
    RegularFormClass.baseChange_hyperbolicClass] at hdecomp
  have h := RegularFormClass.wittIndex_nsmul_hyperbolicClass_add
    (K := L) (RegularFormClass.wittIndex c) (c.anisotropicPart.baseChange L)
  rw [hdecomp, h]
  exact Nat.le_add_right _ _

/-- If the anisotropic part remains anisotropic after base change, the Witt index is unchanged. -/
theorem RegularFormClass.wittIndex_baseChange_eq (c : RegularFormClass K)
    (ha : RegularFormClass.Anisotropic (c.anisotropicPart.baseChange L)) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.wittIndex (c.baseChange L) = RegularFormClass.wittIndex c := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  have hdecomp := congrArg (RegularFormClass.baseChange L)
    (RegularFormClass.wittDecomposition c)
  simp only [RegularFormClass.baseChange_add, RegularFormClass.baseChange_nsmul,
    RegularFormClass.baseChange_hyperbolicClass] at hdecomp
  apply RegularFormClass.wittIndex_eq ha
  exact hdecomp

end TauCeti

namespace QuadraticForm

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [Invertible (2 : K)]

/-- The Witt index of a regular quadratic form cannot decrease after extending scalars. -/
theorem wittIndex_le_wittIndex_baseChange {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.RegularFormClass.wittIndex (TauCeti.formClass Q hQ) ≤
      TauCeti.RegularFormClass.wittIndex
        (TauCeti.formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← TauCeti.RegularFormClass.baseChange_formClass Q hQ]
  exact TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange _

/-- If the anisotropic part remains anisotropic after extending scalars, the Witt index of a
regular quadratic form is unchanged. -/
theorem wittIndex_baseChange_eq {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate)
    (ha : TauCeti.RegularFormClass.Anisotropic
      ((TauCeti.formClass Q hQ).anisotropicPart.baseChange L)) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.RegularFormClass.wittIndex
        (TauCeti.formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) =
      TauCeti.RegularFormClass.wittIndex (TauCeti.formClass Q hQ) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← TauCeti.RegularFormClass.baseChange_formClass Q hQ]
  exact TauCeti.RegularFormClass.wittIndex_baseChange_eq _ ha

end QuadraticForm
