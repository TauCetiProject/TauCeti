/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Cyclotomic.CompatibleTower.Basic
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.MaximalRealSubfield

/-!
# Maximal real subfields of a compatible cyclotomic tower

The inclusions of full cyclotomic fields induce inclusions of their maximal real subfields.
These algebras are finite, commute with rational scalars, and compose along divisibility chains.
The norm square is supplied in general by
`TauCeti.NumberField.norm_norm_maximalRealSubfield_comm`.
-/

public section

noncomputable section

open IntermediateField _root_.NumberField

namespace TauCeti.CompatibleCyclotomicTower

variable {Ω : Type*} [Field Ω] [CharZero Ω] (T : CompatibleCyclotomicTower Ω)

/-- The maximal real subfield of the rational cyclotomic field at level `m`. -/
abbrev realField (m : ℕ) [NeZero m] : Subfield (T.field ℚ m) :=
  maximalRealSubfield (T.field ℚ m)

/-- The real cyclotomic field is abelian over `ℚ`. -/
instance isAbelianGalois_realField (m : ℕ) [NeZero m] : IsAbelianGalois ℚ (T.realField m) := by
  have := IsCyclotomicExtension.isAbelianGalois {m} ℚ (T.field ℚ m)
  exact IsAbelianGalois.of_algHom (T.realField m).subtype.toRatAlgHom

/-- For `m ∣ n`, the algebra on `K_n⁺` over `K_m⁺` induced by the full-field inclusion. -/
abbrev realFieldAlgebra {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) :
    Algebra (T.realField m) (T.realField n) :=
  letI := T.fieldAlgebra ℚ h
  NumberField.maximalRealSubfieldAlgebra (T.field ℚ m) (T.field ℚ n)

/-- Real-level inclusions are compatible with rational scalars. -/
theorem isScalarTower_realFieldAlgebra {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) :
    letI := T.realFieldAlgebra h
    IsScalarTower ℚ (T.realField m) (T.realField n) := by
  let := T.fieldAlgebra ℚ h
  exact NumberField.isScalarTower_maximalRealSubfieldAlgebra _ _

/-- Real-level inclusions are finite. -/
theorem finite_realFieldAlgebra {m n : ℕ} [NeZero m] [NeZero n] (h : m ∣ n) :
    letI := T.realFieldAlgebra h
    Module.Finite (T.realField m) (T.realField n) := by
  let := T.fieldAlgebra ℚ h
  exact NumberField.finite_maximalRealSubfieldAlgebra _ _

/-- Real-level inclusions compose along a divisibility chain. -/
theorem isScalarTower_realFieldAlgebra_realFieldAlgebra {m n k : ℕ}
    [NeZero m] [NeZero n] [NeZero k] (hmn : m ∣ n) (hnk : n ∣ k) :
    letI := T.realFieldAlgebra hmn
    letI := T.realFieldAlgebra hnk
    letI := T.realFieldAlgebra (hmn.trans hnk)
    IsScalarTower (T.realField m) (T.realField n) (T.realField k) := by
  let := T.realFieldAlgebra hmn
  let := T.realFieldAlgebra hnk
  let := T.realFieldAlgebra (hmn.trans hnk)
  let := T.fieldAlgebra ℚ hmn
  let := T.fieldAlgebra ℚ hnk
  let := T.fieldAlgebra ℚ (hmn.trans hnk)
  have := T.isScalarTower_fieldAlgebra_fieldAlgebra ℚ hmn hnk
  apply IsScalarTower.of_algebraMap_eq
  intro x
  apply Subtype.ext
  simp only [NumberField.coe_algebraMap_maximalRealSubfield]
  exact IsScalarTower.algebraMap_apply (T.field ℚ m) (T.field ℚ n) (T.field ℚ k) _

end TauCeti.CompatibleCyclotomicTower
