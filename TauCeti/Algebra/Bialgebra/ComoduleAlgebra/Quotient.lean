/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Subcomodule.Quotient
import TauCeti.Algebra.TensorProduct.MapLinear

/-!
# Quotients of comodule algebras

The quotient by a coaction-stable two-sided ideal inherits a comodule algebra structure, on the
ordinary ideal quotient. Its coaction is characterized on quotient classes by applying
the quotient map to the first tensor factor. The underlying comodule and its laws come
from the quotient by a subcomodule.
-/

public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

variable {R H A : Type*} [CommRing R] [Semiring H] [Bialgebra R H]
  [Ring A] [Algebra R A] [ComoduleAlgebra R H A]

/-- The comodule algebra structure on the quotient by a coaction-stable two-sided ideal. -/
@[implicit_reducible]
noncomputable def quotient (I : Ideal A) [I.IsTwoSided]
    (hI : ∀ a ∈ I, Comodule.coact (R := R) (C := H) a ∈
      I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H)) :
    ComoduleAlgebra R H (A ⧸ I) := by
  let N : Subcomodule R H A :=
    { carrier := I.restrictScalars R
      coact_mem' := by
        intro a ha
        rw [← LinearMap.rTensor_def, ← Ideal.map_includeLeft_eq]
        exact hI a ha }
  letI : Comodule R H (A ⧸ I) := Subcomodule.instComoduleQuotient N
  have hcoact (a : A) :
      Comodule.coact (R := R) (C := H) (Ideal.Quotient.mk I a) =
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R H)
          (Comodule.coact (R := R) (C := H) a) := by
    rw [Algebra.TensorProduct.map_apply_eq_map]
    exact N.quotientCoact_mk a
  exact
    { coact_one := by
        rw [← map_one (Ideal.Quotient.mk I), hcoact, coact_one, map_one]
      coact_mul := by
        intro a b
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
        rw [← map_mul, hcoact, coact_mul, map_mul, hcoact, hcoact] }

/-- The quotient coaction applies the quotient map to the first tensor factor. -/
@[simp]
theorem quotient_coact_mk (I : Ideal A) [I.IsTwoSided]
    (hI : ∀ a ∈ I, Comodule.coact (R := R) (C := H) a ∈
      I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H)) (a : A) :
    letI := quotient I hI
    Comodule.coact (R := R) (C := H) (Ideal.Quotient.mk I a) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R H)
        (Comodule.coact (R := R) (C := H) a) := by
  rw [Algebra.TensorProduct.map_apply_eq_map]
  exact Subcomodule.quotientCoact_mk _ a

/-- The quotient map intertwines the original and quotient algebra coactions. -/
@[simp]
theorem quotient_coactAlgHom_comp_mk (I : Ideal A) [I.IsTwoSided]
    (hI : ∀ a ∈ I, Comodule.coact (R := R) (C := H) a ∈
      I.map (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] H)) :
    letI := quotient I hI
    (coactAlgHom R H (A ⧸ I)).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (AlgHom.id R H)).comp
        (coactAlgHom R H A) := by
  ext a
  simp only [AlgHom.comp_apply, coactAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    quotient_coact_mk]

end TauCeti.ComoduleAlgebra
