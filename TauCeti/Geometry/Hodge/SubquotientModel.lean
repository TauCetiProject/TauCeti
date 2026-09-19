/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import TauCeti.Geometry.Hodge.BaseChange

/-!
# Base-change models of rational subspaces and their quotients

Pure and mixed Hodge structures live on an integral module `Vℤ` together with abstract models
`Vℚ` and `Vℂ` of its rational and complex scalar extensions. To regard a sub-object or a quotient
of such a structure — a kernel, an image, a cokernel — as a structure of the same kind, one needs
the same three carriers for it. This file builds them for a rational subspace `U ⊆ Vℚ`:

* the sub-object is carried by the integral vectors `integralSubmodule ιℚ U` of `U`, by `U`
  itself, and by the complexification `rationalToComplexSubmodule hℚ hℂ U` of `U`;
* the quotient is carried by `Vℤ ⧸ integralSubmodule ιℚ U`, by `Vℚ ⧸ U`, and by
  `Vℂ ⧸ rationalToComplexSubmodule hℚ hℂ U`.

In both cases the restricted, respectively induced, structure maps are base changes. For the
rational model of the sub-object this is the statement that `U` is the localization of its
integral vectors, since a rational vector becomes integral after clearing a denominator; it holds
without any freeness or torsion hypothesis on `Vℤ`. The complex model of the sub-object follows
from the tower `ℤ → ℚ → ℂ`, and both quotient models from right exactness of the tensor product.
The inputs are Mathlib's localization of submodules (`Submodule.localized'` and its Galois
insertion `Submodule.localized'gi`), `isLocalizedModule_iff_isBaseChange`, and
`IsBaseChange.of_right_exact`.

The models are compatible with the ambient data: the complexification of the inclusion `U → Vℚ`
and of the projection `Vℚ → Vℚ ⧸ U` are the inclusion and the projection of the complex models,
and the lattice conjugation of each model is the one induced by the ambient lattice conjugation.

## Main declarations

* `TauCeti.Hodge.integralSubmodule`: the integral vectors of a rational subspace.
* `TauCeti.Hodge.isBaseChange_integralSubmoduleToRational` and
  `TauCeti.Hodge.isBaseChange_integralSubmoduleToComplex`: a rational subspace and its
  complexification are the rational and complex scalar extensions of its integral vectors.
* `TauCeti.Hodge.isBaseChange_integralQuotientToRational` and
  `TauCeti.Hodge.isBaseChange_integralQuotientToComplex`: the same for the quotients.
* `TauCeti.Hodge.rationalMapToComplex_subtype` and `TauCeti.Hodge.rationalMapToComplex_mkQ`: the
  inclusion and the projection complexify to the inclusion and the projection.
* `TauCeti.Hodge.rationalToComplexSubmodule_comap_subtype`: complexification commutes with
  taking the trace of a rational subspace on another.
* `TauCeti.Hodge.rationalToComplexSubmodule_map_mkQ`: complexification commutes with passing to
  the image of a rational subspace in a quotient.
* `TauCeti.Hodge.latticeConjugation_integralSubmoduleToComplex` and
  `TauCeti.Hodge.latticeConjugation_integralQuotientToComplex`: the lattice conjugations of the
  models are induced by the ambient one.
-/

public section

namespace TauCeti.Hodge

open scoped TensorProduct

universe u v w

variable {Vℤ : Type u} {Vℚ : Type v} {Vℂ : Type w}
variable [AddCommGroup Vℤ]
variable [AddCommGroup Vℚ] [Module ℚ Vℚ]
variable [AddCommGroup Vℂ] [Module ℂ Vℂ]
variable {ιℚ : Vℤ →ₗ[ℤ] Vℚ} {ιℂ : Vℤ →ₗ[ℤ] Vℂ}

section Rational

variable (ιℚ) in
/-- The integral vectors of a rational subspace `U`: those vectors of the integral module whose
rationalization lies in `U`. -/
def integralSubmodule (U : Submodule ℚ Vℚ) : Submodule ℤ Vℤ :=
  (U.restrictScalars ℤ).comap ιℚ

@[simp]
theorem mem_integralSubmodule {U : Submodule ℚ Vℚ} {x : Vℤ} :
    x ∈ integralSubmodule ιℚ U ↔ ιℚ x ∈ U :=
  Iff.rfl

variable (ιℚ) in
/-- The rationalization map restricted to the integral vectors of a rational subspace. -/
def integralSubmoduleToRational (U : Submodule ℚ Vℚ) : integralSubmodule ιℚ U →ₗ[ℤ] U :=
  ιℚ.restrict (q := U.restrictScalars ℤ) fun _ hx ↦ hx

@[simp]
theorem coe_integralSubmoduleToRational (U : Submodule ℚ Vℚ) (x : integralSubmodule ιℚ U) :
    (integralSubmoduleToRational ιℚ U x : Vℚ) = ιℚ x :=
  (rfl)

variable (ιℚ) in
/-- The map induced by rationalization on the quotients by a rational subspace and by its
integral vectors. -/
def integralQuotientToRational (U : Submodule ℚ Vℚ) :
    Vℤ ⧸ integralSubmodule ιℚ U →ₗ[ℤ] Vℚ ⧸ U :=
  (integralSubmodule ιℚ U).mapQ (U.restrictScalars ℤ) ιℚ fun _ hx ↦ hx

@[simp]
theorem integralQuotientToRational_mk (U : Submodule ℚ Vℚ) (x : Vℤ) :
    integralQuotientToRational ιℚ U (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ιℚ x) :=
  (rfl)

variable (hℚ : IsBaseChange ℚ ιℚ)
include hℚ

/-- A rational subspace is the localization, hence the rational scalar extension, of its
integral vectors. -/
theorem isBaseChange_integralSubmoduleToRational (U : Submodule ℚ Vℚ) :
    IsBaseChange ℚ (integralSubmoduleToRational ιℚ U) := by
  have := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ ιℚ).2 hℚ
  -- Mathlib localizes the integral vectors of `U` onto the subspace `localized' … U'`, which is
  -- `U` again because `U` is already a rational subspace (`localized'gi` is a Galois insertion);
  -- our map is Mathlib's localization map followed by that identification.
  have hU := (Submodule.localized'gi ℚ (nonZeroDivisors ℤ) ιℚ).l_u_eq U
  exact (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).1 <|
    IsLocalizedModule.of_linearEquiv (nonZeroDivisors ℤ)
      ((integralSubmodule ιℚ U).toLocalized' ℚ (nonZeroDivisors ℤ) ιℚ)
      ((LinearEquiv.ofEq _ _ hU).restrictScalars ℤ)

/-- The quotient of the rational model by a rational subspace is the rational scalar extension of
the quotient of the integral module by the integral vectors of that subspace. -/
theorem isBaseChange_integralQuotientToRational (U : Submodule ℚ Vℚ) :
    IsBaseChange ℚ (integralQuotientToRational ιℚ U) :=
  IsBaseChange.of_right_exact ℚ (integralSubmoduleToRational ιℚ U) ιℚ _
    (f := (integralSubmodule ιℚ U).subtype) (g := (integralSubmodule ιℚ U).mkQ)
    (f' := U.subtype) (g' := U.mkQ) (by ext; rfl) (by ext; rfl)
    (isBaseChange_integralSubmoduleToRational hℚ U) hℚ
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)

end Rational

section Complex

variable (hℚ : IsBaseChange ℚ ιℚ) (hℂ : IsBaseChange ℂ ιℂ)

/-- The complexification map carries the integral vectors of a rational subspace into its
complexification. -/
theorem ι_mem_rationalToComplexSubmodule {U : Submodule ℚ Vℚ} {x : Vℤ}
    (hx : x ∈ integralSubmodule ιℚ U) : ιℂ x ∈ rationalToComplexSubmodule hℚ hℂ U := by
  rw [← rationalToComplexLinearEquiv_one_tmul_ι hℚ hℂ]
  exact rationalToComplexLinearEquiv_one_tmul_mem hℚ hℂ hx

/-- The complexification map restricted to the integral vectors of a rational subspace, with
values in the complexification of that subspace. -/
noncomputable def integralSubmoduleToComplex (U : Submodule ℚ Vℚ) :
    integralSubmodule ιℚ U →ₗ[ℤ] rationalToComplexSubmodule hℚ hℂ U :=
  ιℂ.restrict (q := (rationalToComplexSubmodule hℚ hℂ U).restrictScalars ℤ) fun _ hx ↦
    ι_mem_rationalToComplexSubmodule hℚ hℂ hx

@[simp]
theorem coe_integralSubmoduleToComplex (U : Submodule ℚ Vℚ) (x : integralSubmodule ιℚ U) :
    (integralSubmoduleToComplex hℚ hℂ U x : Vℂ) = ιℂ x :=
  (rfl)

/-- The map induced by complexification on the quotients by the complexification of a rational
subspace and by its integral vectors. -/
noncomputable def integralQuotientToComplex (U : Submodule ℚ Vℚ) :
    Vℤ ⧸ integralSubmodule ιℚ U →ₗ[ℤ] Vℂ ⧸ rationalToComplexSubmodule hℚ hℂ U :=
  (integralSubmodule ιℚ U).mapQ ((rationalToComplexSubmodule hℚ hℂ U).restrictScalars ℤ) ιℂ
    fun _ hx ↦ ι_mem_rationalToComplexSubmodule hℚ hℂ hx

@[simp]
theorem integralQuotientToComplex_mk (U : Submodule ℚ Vℚ) (x : Vℤ) :
    integralQuotientToComplex hℚ hℂ U (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ιℂ x) :=
  (rfl)

/-- The complexification of a rational subspace is the complex scalar extension of its integral
vectors: extend first to `U` over `ℚ`, then to the complexification of `U` over `ℂ`. -/
theorem isBaseChange_integralSubmoduleToComplex (U : Submodule ℚ Vℚ) :
    IsBaseChange ℂ (integralSubmoduleToComplex hℚ hℂ U) := by
  refine IsBaseChange.of_equiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℂ ℂ _).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℂ ℂ)
        (isBaseChange_integralSubmoduleToRational hℚ U).equiv ≪≫ₗ
      rationalToComplexSubmoduleEquiv hℚ hℂ U) fun x ↦ ?_
  ext
  simp

/-- The quotient of the complex model by the complexification of a rational subspace is the
complex scalar extension of the quotient of the integral module by the integral vectors of that
subspace. -/
theorem isBaseChange_integralQuotientToComplex (U : Submodule ℚ Vℚ) :
    IsBaseChange ℂ (integralQuotientToComplex hℚ hℂ U) :=
  IsBaseChange.of_right_exact ℂ (integralSubmoduleToComplex hℚ hℂ U) ιℂ _
    (f := (integralSubmodule ιℚ U).subtype) (g := (integralSubmodule ιℚ U).mkQ)
    (f' := (rationalToComplexSubmodule hℚ hℂ U).subtype)
    (g' := (rationalToComplexSubmodule hℚ hℂ U).mkQ) (by ext; rfl) (by ext; rfl)
    (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) hℂ
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)

/-- Complexifying the inclusion of a rational subspace, between the models of the subspace and
the ambient models, gives the inclusion of its complexification. -/
@[simp]
theorem rationalMapToComplex_subtype (U : Submodule ℚ Vℚ) :
    rationalMapToComplex (isBaseChange_integralSubmoduleToRational hℚ U)
        (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) hℚ hℂ U.subtype =
      (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  refine (isBaseChange_integralSubmoduleToComplex hℚ hℂ U).algHom_ext _ _ fun x ↦ ?_
  rw [← rationalToComplexLinearEquiv_one_tmul_ι (isBaseChange_integralSubmoduleToRational hℚ U)
    (isBaseChange_integralSubmoduleToComplex hℚ hℂ U),
    rationalMapToComplex_rationalToComplexLinearEquiv_tmul]
  simp

/-- Complexifying the projection onto the quotient by a rational subspace, between the ambient
models and the models of the quotient, gives the projection onto the quotient by its
complexification. -/
@[simp]
theorem rationalMapToComplex_mkQ (U : Submodule ℚ Vℚ) :
    rationalMapToComplex hℚ hℂ (isBaseChange_integralQuotientToRational hℚ U)
        (isBaseChange_integralQuotientToComplex hℚ hℂ U) U.mkQ =
      (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  refine hℂ.algHom_ext _ _ fun x ↦ ?_
  rw [← rationalToComplexLinearEquiv_one_tmul_ι hℚ hℂ,
    rationalMapToComplex_rationalToComplexLinearEquiv_tmul]
  -- Both sides are the image of the class of `x` under the complex structure map of the quotient.
  simpa using rationalToComplexLinearEquiv_one_tmul_ι
    (isBaseChange_integralQuotientToRational hℚ U)
    (isBaseChange_integralQuotientToComplex hℚ hℂ U) (Submodule.Quotient.mk x)

/-- Complexifying the trace of a rational subspace `V` on a rational subspace `U` gives the trace
of the complexification of `V` on the complexification of `U`. -/
theorem rationalToComplexSubmodule_comap_subtype (U V : Submodule ℚ Vℚ) :
    rationalToComplexSubmodule (isBaseChange_integralSubmoduleToRational hℚ U)
      (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) (V.comap U.subtype) =
      (rationalToComplexSubmodule hℚ hℂ V).comap (rationalToComplexSubmodule hℚ hℂ U).subtype := by
  apply Submodule.map_injective_of_injective
    (rationalToComplexSubmodule hℚ hℂ U).subtype_injective
  conv_lhs =>
    rw [← rationalMapToComplex_subtype hℚ hℂ U, map_rationalToComplexSubmodule]
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, rationalToComplexSubmodule_inf]

/-- Complexifying the image of a rational subspace in a quotient gives the image of its
complexification in the corresponding complex quotient. -/
theorem rationalToComplexSubmodule_map_mkQ (U V : Submodule ℚ Vℚ) :
    rationalToComplexSubmodule (isBaseChange_integralQuotientToRational hℚ U)
        (isBaseChange_integralQuotientToComplex hℚ hℂ U) (V.map U.mkQ) =
      (rationalToComplexSubmodule hℚ hℂ V).map
        (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  rw [← map_rationalToComplexSubmodule hℚ hℂ
    (isBaseChange_integralQuotientToRational hℚ U)
    (isBaseChange_integralQuotientToComplex hℚ hℂ U), rationalMapToComplex_mkQ]

/-- Lattice conjugation preserves the complexification of a rational subspace, in the form taken
by `TauCeti.Hodge.Conjugation.restrict` and `TauCeti.Hodge.Conjugation.quotient`. -/
theorem latticeConjugation_mem_rationalToComplexSubmodule (U : Submodule ℚ Vℚ) :
    ∀ x ∈ rationalToComplexSubmodule hℚ hℂ U,
      (latticeConjugation hℂ).toEquiv x ∈ rationalToComplexSubmodule hℚ hℂ U := fun x hx ↦ by
  rw [latticeConjugation_toEquiv_apply, ← rationalToComplexSubmodule_conj hℚ hℂ U]
  exact Submodule.mem_map_of_mem hx

/-- Lattice conjugation on the complex model of a rational subspace is computed in the ambient
complex model. -/
@[simp]
theorem coe_latticeConj_integralSubmoduleToComplex (U : Submodule ℚ Vℚ)
    (x : rationalToComplexSubmodule hℚ hℂ U) :
    (latticeConj (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) x : Vℂ) =
      latticeConj hℂ x := by
  rw [← latticeConj_unique (isBaseChange_integralSubmoduleToComplex hℚ hℂ U)
    ((latticeConjugation hℂ).restrict
      (latticeConjugation_mem_rationalToComplexSubmodule hℚ hℂ U)).toEquiv.toLinearMap
    fun v ↦ Subtype.ext (by simp)]
  simp

/-- Lattice conjugation on the complex model of a quotient by a rational subspace acts on classes
through the ambient lattice conjugation. -/
@[simp]
theorem latticeConj_integralQuotientToComplex_mk (U : Submodule ℚ Vℚ) (x : Vℂ) :
    latticeConj (isBaseChange_integralQuotientToComplex hℚ hℂ U) (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (latticeConj hℂ x) := by
  rw [← latticeConj_unique (isBaseChange_integralQuotientToComplex hℚ hℂ U)
    ((latticeConjugation hℂ).quotient
      (latticeConjugation_mem_rationalToComplexSubmodule hℚ hℂ U)).toEquiv.toLinearMap
    fun v ↦ by
      induction v using Submodule.Quotient.induction_on
      simp]
  simp

/-- Conjugating the image of a complex subspace in a quotient is the image of its conjugate. -/
theorem map_latticeConj_integralQuotientToComplex (U : Submodule ℚ Vℚ)
    (A : Submodule ℂ Vℂ) :
    (A.map (rationalToComplexSubmodule hℚ hℂ U).mkQ).map
        (latticeConj (isBaseChange_integralQuotientToComplex hℚ hℂ U)) =
      (A.map (latticeConj hℂ)).map (rationalToComplexSubmodule hℚ hℂ U).mkQ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨latticeConj hℂ x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Submodule.Quotient.mk x, ⟨x, hx, rfl⟩, by simp⟩

/-- The lattice conjugation of the complex model of a rational subspace is the restriction of
the ambient lattice conjugation. -/
theorem latticeConjugation_integralSubmoduleToComplex (U : Submodule ℚ Vℚ) :
    latticeConjugation (isBaseChange_integralSubmoduleToComplex hℚ hℂ U) =
      (latticeConjugation hℂ).restrict
        (latticeConjugation_mem_rationalToComplexSubmodule hℚ hℂ U) := by
  ext x
  simp

/-- The lattice conjugation of the complex model of a quotient by a rational subspace is induced
by the ambient lattice conjugation. -/
theorem latticeConjugation_integralQuotientToComplex (U : Submodule ℚ Vℚ) :
    latticeConjugation (isBaseChange_integralQuotientToComplex hℚ hℂ U) =
      (latticeConjugation hℂ).quotient
        (latticeConjugation_mem_rationalToComplexSubmodule hℚ hℂ U) := by
  ext x
  induction x using Submodule.Quotient.induction_on
  simp

end Complex

end TauCeti.Hodge
