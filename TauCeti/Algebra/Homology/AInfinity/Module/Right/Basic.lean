/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.GradedCoderivation
public import TauCeti.Algebra.Homology.AInfinity.Algebra.CoaugmentedBar
public import TauCeti.LinearAlgebra.TensorCoalgebra.Coaugmented.Grading

/-!
# Right A-infinity modules: the suspended bar differential

A right `A∞` module over an `A∞` algebra `A` is stored on its cofree right bar comodule

`sM ⊗ Tᶜ(sA)`.

Its structure map is a degree-one square-zero coderivation over the bar differential of `A`.
The co-Leibniz law includes the Koszul sign obtained when the algebra bar differential crosses the
left comodule factor.  Using the coaugmented tensor coalgebra is essential: the empty word records
the unary module operation.

This file packages that primary suspended definition.  The Taylor map is obtained by applying the
coalgebra counit after the bar differential.  It is not stored separately: coderivations over a
fixed coalgebra operator on a cofree comodule are determined by this component, which gives the
extensionality theorem below.  The square-zero law can likewise be checked after applying the
counit, giving the suspended module Stasheff equation in the form
`taylor ∘ barDifferential = 0`.

## Main definitions

* `TauCeti.AInfinityRightModule`: a right `A∞` module in suspended bar form.
* `TauCeti.AInfinityRightModule.barGrading`: the total grading on `sM ⊗ Tᶜ(sA)`.
* `TauCeti.AInfinityRightModule.taylor`: the cogenerator component of the module bar
  differential.
* `TauCeti.AInfinityRightModule.ofBarDifferential`: construct a module by checking the
  square-zero law on its Taylor component.

The convention follows Getzler--Jones, *A-infinity algebras and the cyclic bar complex*,
Sections 1--2, and Keller, *Introduction to A-infinity algebras and modules*, Section 4.
-/

public section

open scoped TensorProduct

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [AddCommGroup A] [Module R A] [AddCommGroup M] [Module R M]

namespace AInfinityRightModule

/-- The total suspended grading on the cofree bar comodule `sM ⊗ Tᶜ(sA)`. -/
noncomputable def barGrading (AA : AInfinityAlgebra R A) (G : InternalGrading R M) :
    InternalGrading R (M ⊗[R] TensorWords R A) :=
  (G.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1))

/-- The degree-`p` part of the bar-comodule grading is the total-degree part of the suspended
module grading and the suspended tensor-word grading. -/
@[simp]
theorem barGrading_piece (AA : AInfinityAlgebra R A) (G : InternalGrading R M) (p : ℤ) :
    (barGrading AA G).piece p =
      ((G.shift 1).tensorProduct (TensorWords.grading (AA.grading.shift 1))).piece p :=
  (rfl)

end AInfinityRightModule

attribute [local instance] Comodule.cofree

/-- A right `A∞` module over `AA`, stored as a square-zero degree-one coderivation on the
cofree right bar comodule `sM ⊗ Tᶜ(sA)` over the bar coderivation of `AA`.

The carrier types model suspension by shifting their internal gradings; no new carrier type is
introduced.  Thus `barDifferential` acts on `M ⊗ Tᶜ(A)`, while `barGrading` interprets that
carrier as `sM ⊗ Tᶜ(sA)`. -/
structure AInfinityRightModule (AA : AInfinityAlgebra R A) (M : Type uM)
    [AddCommGroup M] [Module R M] where
  /-- The internal cohomological grading of the module carrier. -/
  grading : InternalGrading R M
  /-- The suspended module bar differential on the cofree right bar comodule. -/
  barDifferential :
    (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A
  /-- The module bar differential has degree one for the total suspended grading. -/
  isHomogeneous_barDifferential :
    LinearMap.IsHomogeneous barDifferential
      (AInfinityRightModule.barGrading AA grading).piece
      (AInfinityRightModule.barGrading AA grading).piece 1
  /-- The module bar differential is a coderivation over the algebra bar differential. -/
  isGradedCoderivation_barDifferential :
    Comodule.IsGradedCoderivationOver (AInfinityRightModule.barGrading AA grading) 1
      AA.coaugmentedBarDifferential barDifferential
  /-- The module bar differential squares to zero. -/
  bar_square_zero : barDifferential ∘ₗ barDifferential = 0

namespace AInfinityRightModule

variable {AA : AInfinityAlgebra R A}

/-- The Taylor map of a right `A∞` module, obtained by applying the tensor-coalgebra counit to
the output of its bar differential.  On the summand `sM ⊗ (sA)^⊗n`, this is the suspended
arity-`n + 1` module operation. -/
noncomputable def taylor (MM : AInfinityRightModule AA M) :
    (M ⊗[R] TensorWords R A) →ₗ[R] M :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ MM.barDifferential

/-- The Taylor map is the counit component of the module bar differential. -/
theorem taylor_def (MM : AInfinityRightModule AA M) :
    MM.taylor =
      (TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ
          MM.barDifferential :=
  (rfl)

/-- Evaluating the Taylor map means applying the bar differential, then the coalgebra counit, and
finally the right unitor. -/
@[simp]
theorem taylor_apply (MM : AInfinityRightModule AA M)
    (x : M ⊗[R] TensorWords R A) :
    MM.taylor x = (TensorProduct.rid R M)
      ((Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M
        (MM.barDifferential x)) :=
  (rfl)

/-- The Taylor map has degree one from the total suspended bar-comodule grading to the suspended
module grading. -/
theorem isHomogeneous_taylor (MM : AInfinityRightModule AA M) :
    LinearMap.IsHomogeneous MM.taylor (barGrading AA MM.grading).piece
      (MM.grading.shift 1).piece 1 := by
  rw [taylor_def]
  exact (TensorWords.isHomogeneous_rid_comp_lTensor_counit (MM.grading.shift 1)
    (AA.grading.shift 1)).comp
    MM.isHomogeneous_barDifferential

/-- The stored module bar differential squares to zero. -/
@[simp]
theorem barDifferential_sq (MM : AInfinityRightModule AA M) :
    MM.barDifferential ∘ₗ MM.barDifferential = 0 :=
  MM.bar_square_zero

/-- The Taylor component of the square of the module bar differential vanishes.  This is the
suspended form of all right-module Stasheff identities. -/
@[simp]
theorem taylor_comp_barDifferential (MM : AInfinityRightModule AA M) :
    MM.taylor ∘ₗ MM.barDifferential = 0 := by
  rw [taylor_def, LinearMap.comp_assoc, LinearMap.comp_assoc,
    MM.barDifferential_sq, LinearMap.comp_zero, LinearMap.comp_zero]

/-- A degree-one coderivation over the algebra bar differential squares to zero if and only if
its Taylor component after one further application vanishes. -/
theorem barDifferential_sq_iff_taylor_comp_eq_zero (G : InternalGrading R M)
    (D : (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
    (hD : LinearMap.IsHomogeneous D (barGrading AA G).piece (barGrading AA G).piece 1)
    (hcod : Comodule.IsGradedCoderivationOver (barGrading AA G) 1
      AA.coaugmentedBarDifferential D) :
    D ∘ₗ D = 0 ↔
      ((TensorProduct.rid R M).toLinearMap ∘ₗ
          (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ D) ∘ₗ D = 0 := by
  rw [← LinearMap.comp_assoc]
  exact hcod.square_eq_zero_iff_counit (barGrading AA G)
    AA.coaugmentedBarDifferential D hD AA.coaugmentedBarDifferential_sq

/-- Construct a right `A∞` module from a homogeneous coderivation over the algebra bar
differential.  By cofreeness, it suffices to check the square-zero law on the Taylor component. -/
noncomputable def ofBarDifferential (G : InternalGrading R M)
    (D : (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
    (hD : LinearMap.IsHomogeneous D (barGrading AA G).piece (barGrading AA G).piece 1)
    (hcod : Comodule.IsGradedCoderivationOver (barGrading AA G) 1
      AA.coaugmentedBarDifferential D)
    (hsq : ((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ D) ∘ₗ D = 0) :
    AInfinityRightModule AA M where
  grading := G
  barDifferential := D
  isHomogeneous_barDifferential := hD
  isGradedCoderivation_barDifferential := hcod
  bar_square_zero := (barDifferential_sq_iff_taylor_comp_eq_zero G D hD hcod).2 hsq

@[simp]
theorem ofBarDifferential_grading (G : InternalGrading R M)
    (D : (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
    (hD : LinearMap.IsHomogeneous D (barGrading AA G).piece (barGrading AA G).piece 1)
    (hcod : Comodule.IsGradedCoderivationOver (barGrading AA G) 1
      AA.coaugmentedBarDifferential D)
    (hsq : ((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ D) ∘ₗ D = 0) :
    (ofBarDifferential G D hD hcod hsq).grading = G :=
  (rfl)

@[simp]
theorem ofBarDifferential_barDifferential (G : InternalGrading R M)
    (D : (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
    (hD : LinearMap.IsHomogeneous D (barGrading AA G).piece (barGrading AA G).piece 1)
    (hcod : Comodule.IsGradedCoderivationOver (barGrading AA G) 1
      AA.coaugmentedBarDifferential D)
    (hsq : ((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ D) ∘ₗ D = 0) :
    (ofBarDifferential G D hD hcod hsq).barDifferential = D :=
  (rfl)

@[simp]
theorem ofBarDifferential_taylor (G : InternalGrading R M)
    (D : (M ⊗[R] TensorWords R A) →ₗ[R] M ⊗[R] TensorWords R A)
    (hD : LinearMap.IsHomogeneous D (barGrading AA G).piece (barGrading AA G).piece 1)
    (hcod : Comodule.IsGradedCoderivationOver (barGrading AA G) 1
      AA.coaugmentedBarDifferential D)
    (hsq : ((TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ D) ∘ₗ D = 0) :
    (ofBarDifferential G D hD hcod hsq).taylor =
      (TensorProduct.rid R M).toLinearMap ∘ₗ
        (Coalgebra.counit (R := R) (A := TensorWords R A)).lTensor M ∘ₗ D :=
  (rfl)

/-- Right `A∞` modules on a fixed carrier are determined by their grading and Taylor map.  In
particular, the stored bar differential contains no data beyond its cogenerator component. -/
@[ext]
theorem ext {MM NN : AInfinityRightModule AA M} (hG : MM.grading = NN.grading)
    (htaylor : MM.taylor = NN.taylor) : MM = NN := by
  cases MM with
  | mk G D hD hcod hsq =>
    cases NN with
    | mk H E hE hecod hesq =>
      simp only at hG htaylor
      subst H
      have hDE : D = E := hcod.eq_of_counit_comp_eq (barGrading AA G)
        AA.coaugmentedBarDifferential D E hecod htaylor
      subst E
      rfl

end AInfinityRightModule

end TauCeti
