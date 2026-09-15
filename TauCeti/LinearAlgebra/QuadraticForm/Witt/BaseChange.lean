/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition

/-!
# Base change of the Witt decomposition

Scalar extension preserves the hyperbolic plane, so the Witt index cannot decrease under a field
extension.  It is unchanged when the anisotropic part remains anisotropic after base change.

## Main results

* `TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange`: the Witt index cannot decrease.
* `TauCeti.RegularFormClass.wittIndex_baseChange_eq_iff`: the index is unchanged exactly when the
  extended anisotropic part is anisotropic.
* `QuadraticForm.wittIndex_le_wittIndex_baseChange`: the corresponding inequality for a regular
  quadratic form.
* `QuadraticForm.wittIndex_baseChange_eq_iff`: the corresponding equivalence for a regular
  quadratic form.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4.
-/

public section
noncomputable section

open QuadraticMap QuadraticForm

namespace TauCeti

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

variable [Invertible (2 : K)]

/-- Base change preserves the hyperbolic class. -/
@[simp]
theorem RegularFormClass.baseChange_hyperbolicClass :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.baseChange L (hyperbolicClass K) = hyperbolicClass L := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← formClass_hyperbolicPlane, QuadraticForm.formClass_baseChange,
    ← formClass_hyperbolicPlane]
  apply (formClass_eq_iff _ _ _ _).mpr
  have hK : hyperbolicPlane K =
      presentedForm (⟨2, ![1, -1]⟩ : RegularFormPresentation K) :=
    presentedForm_one_neg_one.symm
  have hp : RegularFormPresentation.baseChange L
      (⟨2, ![1, -1]⟩ : RegularFormPresentation K) =
      (⟨2, ![1, -1]⟩ : RegularFormPresentation L) := by
    rw [RegularFormPresentation.baseChange_mk]
    congr 1
    funext i
    apply Units.ext
    fin_cases i <;> simp
  rw [hK]
  exact (equivalent_presentedForm_baseChange _).trans (by
    rw [hp, presentedForm_one_neg_one]
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

/-- The anisotropic part commutes with base change when its base change remains anisotropic. -/
theorem RegularFormClass.anisotropicPart_baseChange (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.Anisotropic (c.anisotropicPart.baseChange L) →
      RegularFormClass.anisotropicPart (c.baseChange L) = c.anisotropicPart.baseChange L := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  intro ha
  have hdecomp := congrArg (RegularFormClass.baseChange L)
    (RegularFormClass.wittDecomposition c)
  simp only [RegularFormClass.baseChange_add, RegularFormClass.baseChange_nsmul,
    RegularFormClass.baseChange_hyperbolicClass] at hdecomp
  exact RegularFormClass.anisotropicPart_eq ha hdecomp

/-- The Witt index is unchanged after base change exactly when the extended anisotropic part
remains anisotropic. -/
theorem RegularFormClass.wittIndex_baseChange_eq_iff (c : RegularFormClass K) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    RegularFormClass.wittIndex (c.baseChange L) = RegularFormClass.wittIndex c ↔
      RegularFormClass.Anisotropic (c.anisotropicPart.baseChange L) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  have hdecomp := congrArg (RegularFormClass.baseChange L)
    (RegularFormClass.wittDecomposition c)
  simp only [RegularFormClass.baseChange_add, RegularFormClass.baseChange_nsmul,
    RegularFormClass.baseChange_hyperbolicClass] at hdecomp
  rw [hdecomp, RegularFormClass.wittIndex_nsmul_hyperbolicClass_add]
  constructor
  · intro h
    rw [← RegularFormClass.wittIndex_eq_zero_iff]
    omega
  · intro ha
    have hzero := RegularFormClass.wittIndex_eq_zero_iff.mpr ha
    omega

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
  rw [← Q.formClass_baseChange hQ]
  exact TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange _

/-- The Witt index of a regular quadratic form is unchanged after extending scalars exactly when
the extended anisotropic part remains anisotropic. -/
theorem wittIndex_baseChange_eq_iff {V : Type w} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : _root_.QuadraticForm K V) (hQ : Q.Nondegenerate) :
    letI : Invertible (2 : L) :=
      (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
    TauCeti.RegularFormClass.wittIndex
        (TauCeti.formClass (Q.baseChange L) (QuadraticForm.Nondegenerate.baseChange hQ)) =
      TauCeti.RegularFormClass.wittIndex (TauCeti.formClass Q hQ) ↔
        TauCeti.RegularFormClass.Anisotropic
          ((TauCeti.formClass Q hQ).anisotropicPart.baseChange L) := by
  let _ : Invertible (2 : L) :=
    (Invertible.map (algebraMap K L) 2).copy 2 (map_ofNat _ _).symm
  rw [← Q.formClass_baseChange hQ]
  exact TauCeti.RegularFormClass.wittIndex_baseChange_eq_iff _

end QuadraticForm
