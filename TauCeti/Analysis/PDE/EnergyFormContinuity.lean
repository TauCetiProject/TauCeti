/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyFormLinearity

/-!
# Continuity of pointwise PDE energy integrands in the coefficients

The finite-dimensional weak-form integrand
`energyIntegrand A b c` is linear in the principal, drift, and mass coefficients.  This file
bundles that linearity as continuous linear maps from coefficient spaces to spaces of
continuous bilinear maps.

This is a pointwise prerequisite for Lane D of the PDE roadmap.  Once the weak energy form is
defined by integrating `x ↦ energyIntegrand (a x) (b x) (c x)` over a domain, continuous
coefficient fields and continuous perturbation families should give continuous integrand
families without unfolding the jet form.

## Main declarations

* `TauCeti.PDE.matrixBilinearFormLinear`, `TauCeti.PDE.driftFormLinear`, and
  `TauCeti.PDE.massFormLinear`: the coefficient-to-form maps as continuous linear maps.
* `TauCeti.PDE.energyIntegrandLinear`: the full coefficient triple-to-integrand map as a
  continuous linear map.
* `TauCeti.PDE.continuous_matrixBilinearForm`, `TauCeti.PDE.continuous_driftForm`,
  `TauCeti.PDE.continuous_massForm`, and `TauCeti.PDE.continuous_energyIntegrand`: continuity
  of the corresponding unbundled maps.
* `Continuous.energyIntegrand`, `ContinuousOn.energyIntegrand`, and the lower-order analogues:
  composition lemmas for coefficient fields.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- The principal coefficient matrix-to-bilinear-form map as a continuous linear map. -/
@[expose]
noncomputable def matrixBilinearFormLinear :
    Matrix n n ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := matrixBilinearForm
      map_add' := by
        intro A B
        ext η ξ
        exact matrixBilinearForm_add_apply A B η ξ
      map_smul' := by
        intro r A
        ext η ξ
        exact matrixBilinearForm_smul_apply r A η ξ }

/-- Applying `matrixBilinearFormLinear` recovers `matrixBilinearForm`. -/
@[simp]
lemma matrixBilinearFormLinear_apply (A : Matrix n n ℝ) :
    matrixBilinearFormLinear (n := n) A = matrixBilinearForm A :=
  rfl

/-- The drift coefficient-to-form map as a continuous linear map. -/
@[expose]
noncomputable def driftFormLinear :
    EuclideanSpace ℝ n →L[ℝ] ℝ →L[ℝ] EuclideanSpace ℝ n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := driftForm
      map_add' := by
        intro b d
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro ξ
        simp [driftForm_apply, inner_add_left]
        ring
      map_smul' := by
        intro r b
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro ξ
        simp [driftForm_apply, inner_smul_left, smul_eq_mul]
        ring }

omit [DecidableEq n] in
/-- Applying `driftFormLinear` recovers `driftForm`. -/
@[simp]
lemma driftFormLinear_apply (b : EuclideanSpace ℝ n) :
    driftFormLinear (n := n) b = driftForm b :=
  rfl

/-- The mass coefficient-to-form map as a continuous linear map. -/
@[expose]
noncomputable def massFormLinear : ℝ →L[ℝ] ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := massForm
      map_add' := by
        intro c e
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        simp [massForm_apply]
        ring
      map_smul' := by
        intro r c
        apply ContinuousLinearMap.ext
        intro u
        apply ContinuousLinearMap.ext
        intro v
        simp [massForm_apply, smul_eq_mul]
        ring }

/-- Applying `massFormLinear` recovers `massForm`. -/
@[simp]
lemma massFormLinear_apply (c : ℝ) : massFormLinear c = massForm c :=
  rfl

/-- The coefficient triple-to-energy-integrand map as a continuous linear map. -/
@[expose]
noncomputable def energyIntegrandLinear :
    (Matrix n n ℝ × EuclideanSpace ℝ n × ℝ) →L[ℝ]
      (ℝ × EuclideanSpace ℝ n) →L[ℝ] (ℝ × EuclideanSpace ℝ n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => energyIntegrand p.1 p.2.1 p.2.2
      map_add' := by
        rintro ⟨A, b, c⟩ ⟨B, d, e⟩
        apply ContinuousLinearMap.ext
        intro U
        apply ContinuousLinearMap.ext
        intro V
        exact energyIntegrand_add_apply A B b d c e U V
      map_smul' := by
        rintro r ⟨A, b, c⟩
        apply ContinuousLinearMap.ext
        intro U
        apply ContinuousLinearMap.ext
        intro V
        exact energyIntegrand_smul_apply A b c r U V }

/-- Applying `energyIntegrandLinear` recovers `energyIntegrand` for the coefficient triple. -/
@[simp]
lemma energyIntegrandLinear_apply (A : Matrix n n ℝ) (b : EuclideanSpace ℝ n) (c : ℝ) :
    energyIntegrandLinear (n := n) (A, b, c) = energyIntegrand A b c :=
  rfl

/-- The principal coefficient-to-bilinear-form map is continuous. -/
lemma continuous_matrixBilinearForm :
    Continuous (fun A : Matrix n n ℝ => matrixBilinearForm A) :=
  (matrixBilinearFormLinear (n := n)).continuous

omit [DecidableEq n] in
/-- The drift coefficient-to-form map is continuous. -/
lemma continuous_driftForm :
    Continuous (fun b : EuclideanSpace ℝ n => driftForm b) :=
  (driftFormLinear (n := n)).continuous.congr fun b => (driftFormLinear_apply b)

/-- The mass coefficient-to-form map is continuous. -/
lemma continuous_massForm : Continuous (fun c : ℝ => massForm c) :=
  massFormLinear.continuous.congr fun c => massFormLinear_apply c

/-- The full coefficient triple-to-energy-integrand map is continuous. -/
lemma continuous_energyIntegrand :
    Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n × ℝ =>
      energyIntegrand p.1 p.2.1 p.2.2) :=
  (energyIntegrandLinear (n := n)).continuous.congr fun p =>
    energyIntegrandLinear_apply p.1 p.2.1 p.2.2

variable [TopologicalSpace X]

namespace Continuous

/-- A continuous principal coefficient field gives a continuous field of principal bilinear
forms. -/
lemma matrixBilinearForm {a : X → Matrix n n ℝ} (ha : Continuous a) :
    Continuous (fun x => PDE.matrixBilinearForm (a x)) :=
  continuous_matrixBilinearForm.comp ha

omit [DecidableEq n] in
/-- A continuous drift coefficient field gives a continuous field of drift forms. -/
lemma driftForm {b : X → EuclideanSpace ℝ n} (hb : Continuous b) :
    Continuous (fun x => PDE.driftForm (b x)) :=
  continuous_driftForm.comp hb

/-- A continuous mass coefficient field gives a continuous field of mass forms. -/
lemma massForm {c : X → ℝ} (hc : Continuous c) :
    Continuous (fun x => PDE.massForm (c x)) :=
  continuous_massForm.comp hc

/-- Continuous coefficient fields give a continuous field of full pointwise energy
integrands. -/
lemma energyIntegrand {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => PDE.energyIntegrand (a x) (b x) (c x)) :=
  continuous_energyIntegrand.comp (ha.prodMk (hb.prodMk hc))

end Continuous

namespace ContinuousOn

/-- A continuous principal coefficient field on a set gives a continuous field of principal
bilinear forms on that set. -/
lemma matrixBilinearForm {s : Set X} {a : X → Matrix n n ℝ} (ha : ContinuousOn a s) :
    ContinuousOn (fun x => PDE.matrixBilinearForm (a x)) s :=
  continuous_matrixBilinearForm.comp_continuousOn ha

omit [DecidableEq n] in
/-- A continuous drift coefficient field on a set gives a continuous field of drift forms on
that set. -/
lemma driftForm {s : Set X} {b : X → EuclideanSpace ℝ n} (hb : ContinuousOn b s) :
    ContinuousOn (fun x => PDE.driftForm (b x)) s :=
  continuous_driftForm.comp_continuousOn hb

/-- A continuous mass coefficient field on a set gives a continuous field of mass forms on
that set. -/
lemma massForm {s : Set X} {c : X → ℝ} (hc : ContinuousOn c s) :
    ContinuousOn (fun x => PDE.massForm (c x)) s :=
  continuous_massForm.comp_continuousOn hc

/-- Continuous coefficient fields on a set give a continuous field of full pointwise energy
integrands on that set. -/
lemma energyIntegrand {s : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n}
    {c : X → ℝ} (ha : ContinuousOn a s) (hb : ContinuousOn b s) (hc : ContinuousOn c s) :
    ContinuousOn (fun x => PDE.energyIntegrand (a x) (b x) (c x)) s :=
  continuous_energyIntegrand.comp_continuousOn (ha.prodMk (hb.prodMk hc))

end ContinuousOn

end PDE

end TauCeti
