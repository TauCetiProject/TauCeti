/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Symplectic.StandardCompatible
public import TauCeti.Geometry.Symplectic.SymplecticTransport
public import TauCeti.Geometry.Symplectic.Lagrangian.Basic

/-!
# The standard compatible triple on the complex line

The complex line serves both as the local model for holomorphic-curve domains and as the
one-dimensional target model for elementary checks. `TauCeti.Geometry.Symplectic.StandardCompatible`
builds the standard compatible triple on a doubled real inner-product space `V × V`; this file
transports the case `V = ℝ` across Mathlib's real-linear equivalence
`Complex.equivRealProdCLM.symm`.

The resulting almost complex structure on `ℂ` is multiplication by `Complex.I`, and the
transported symplectic form is the standard area form
`ω(z, w) = z.re * w.im - z.im * w.re`. Compatibility is inherited from the transported standard
model, giving a concrete non-vacuous model for the pointwise `J`-holomorphic and energy API.
The sign of `Im (J 1)` classifies the two orientation components of plane complex structures;
conjugating the coordinates exchanges them.

## Main declarations

* `TauCeti.stdComplexSymplecticForm`: the standard symplectic area form on `ℂ`.
* `TauCeti.isComplexLinearMap_equivRealProdCLM_symm` and
  `TauCeti.isSymplectomorphism_equivRealProdCLM_symm`: the coordinate equivalence preserves
  the standard complex and symplectic structures.
* `TauCeti.stdComplexSymplecticForm_compatible`: compatibility of the standard area form with
  the standard complex structure.
* `TauCeti.stdComplexSymplecticForm_apply_ofComplexModule`: area paired with multiplication
  by `I` is the norm square.
* `TauCeti.stdComplexSymplecticForm_tames_iff_im_pos` and
  `TauCeti.stdComplexSymplecticForm_tames_or_tames_transport_conj`: the orientation criterion
  and coverage of both components by the usual and conjugate real coordinates.
* `TauCeti.isLagrangian_stdComplexSymplecticForm_of_finrank_eq_one`: every real line in `ℂ`
  is Lagrangian for the standard area form.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: the standard complex line is `ℝ²` with `J(x, y) = (-y, x)` and
`ω((x₁, y₁), (x₂, y₂)) = x₁ y₂ - y₁ x₂`.
-/

public section

namespace TauCeti

open Complex Module

/-- The standard symplectic area form on `ℂ`, transported from the standard form on `ℝ × ℝ`. -/
noncomputable def stdComplexSymplecticForm : SymplecticForm ℂ :=
  (stdSymplecticForm (V := ℝ)).transport Complex.equivRealProdCLM.symm.toLinearEquiv

private lemma product_transport_equivRealProdCLM_symm_eq_ofComplexModule :
    (AlmostComplexStructure.product ℝ).transport
        Complex.equivRealProdCLM.symm.toLinearEquiv =
      AlmostComplexStructure.ofComplexModule ℂ := by
  refine AlmostComplexStructure.ext fun z => ?_
  apply Complex.ext <;>
    simp [AlmostComplexStructure.ofComplexModule_apply, Complex.equivRealProdCLM_symm_apply,
      Complex.mul_re, Complex.mul_im]

/-- The real-coordinate equivalence from `ℝ × ℝ` to `ℂ` is complex-linear for the standard
complex structures. -/
lemma isComplexLinearMap_equivRealProdCLM_symm :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.ofComplexModule ℂ)
      Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact AlmostComplexStructure.isComplexLinearMap_transport (AlmostComplexStructure.product ℝ)
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The real-coordinate equivalence from `ℂ` to `ℝ × ℝ` is complex-linear for the standard
complex structures. -/
lemma isComplexLinearMap_equivRealProdCLM :
    IsComplexLinearMap (AlmostComplexStructure.ofComplexModule ℂ)
      (AlmostComplexStructure.product ℝ)
      Complex.equivRealProdCLM.toLinearEquiv.toLinearMap := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact AlmostComplexStructure.isComplexLinearMap_symm_transport (AlmostComplexStructure.product ℝ)
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard symplectic form on `ℂ` is the usual coordinate area form. -/
@[simp]
lemma stdComplexSymplecticForm_apply (z w : ℂ) :
    stdComplexSymplecticForm z w = z.re * w.im - z.im * w.re := by
  simp [stdComplexSymplecticForm]
  ring

/-- The associated compatible metric on `ℂ` is the standard real dot product. -/
lemma stdComplexSymplecticForm_associatedBilinForm (z w : ℂ) :
    stdComplexSymplecticForm.associatedBilinForm (AlmostComplexStructure.ofComplexModule ℂ) z w =
      z.re * w.re + z.im * w.im := by
  simp [SymplecticForm.associatedBilinForm_apply, AlmostComplexStructure.ofComplexModule_apply]

/-- The real-coordinate equivalence from `ℝ × ℝ` to `ℂ` is a symplectomorphism for the
standard symplectic forms. -/
lemma isSymplectomorphism_equivRealProdCLM_symm :
    SymplecticForm.IsSymplectomorphism (stdSymplecticForm (V := ℝ)) stdComplexSymplecticForm
      Complex.equivRealProdCLM.symm.toLinearEquiv := by
  exact (SymplecticForm.isSymplectomorphism_iff_transport_eq
    (ω₁ := stdSymplecticForm (V := ℝ)) (ω₂ := stdComplexSymplecticForm)
    (e := Complex.equivRealProdCLM.symm.toLinearEquiv)).mpr rfl

/-- The real-coordinate equivalence from `ℂ` to `ℝ × ℝ` is a symplectomorphism for the
standard symplectic forms. -/
lemma isSymplectomorphism_equivRealProdCLM :
    SymplecticForm.IsSymplectomorphism stdComplexSymplecticForm (stdSymplecticForm (V := ℝ))
      Complex.equivRealProdCLM.toLinearEquiv :=
  isSymplectomorphism_equivRealProdCLM_symm.symm

/-- The standard symplectic form on `ℂ` is invariant under multiplication by `I`. -/
lemma stdComplexSymplecticForm_invariant :
    stdComplexSymplecticForm.Invariant (AlmostComplexStructure.ofComplexModule ℂ) := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact (stdSymplecticForm_invariant_product (V := ℝ)).transport
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard symplectic form on `ℂ` tames multiplication by `I`. -/
lemma stdComplexSymplecticForm_tames :
    stdComplexSymplecticForm.Tames (AlmostComplexStructure.ofComplexModule ℂ) := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact (stdSymplecticForm_tames_product (V := ℝ)).transport
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard symplectic area form on `ℂ` is compatible with the standard complex structure. -/
lemma stdComplexSymplecticForm_compatible :
    stdComplexSymplecticForm.Compatible (AlmostComplexStructure.ofComplexModule ℂ) := by
  rw [← product_transport_equivRealProdCLM_symm_eq_ofComplexModule]
  exact (stdSymplecticForm_compatible_product (V := ℝ)).transport
    Complex.equivRealProdCLM.symm.toLinearEquiv

/-- The standard area form paired with the standard complex structure is the norm square. -/
theorem stdComplexSymplecticForm_apply_ofComplexModule (z : ℂ) :
    stdComplexSymplecticForm z (AlmostComplexStructure.ofComplexModule ℂ z) =
      Complex.normSq z := by
  simp [stdComplexSymplecticForm_apply, AlmostComplexStructure.ofComplexModule_apply,
    Complex.normSq_apply]

private noncomputable def planeBasis (J : AlmostComplexStructure ℂ) : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank' ![1, J 1]
    (J.linearIndependent_pair one_ne_zero) (by simp)

private theorem planeBasis_apply (J : AlmostComplexStructure ℂ) :
    ⇑(planeBasis J) = ![1, J 1] :=
  coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _

/-- A plane complex structure cannot send one to a real vector: its square is minus the identity.
Thus there are exactly two choices of orientation for the scalar coefficient chart. -/
theorem AlmostComplexStructure.im_apply_one_ne_zero (J : AlmostComplexStructure ℂ) :
    (J 1).im ≠ 0 := by
  intro h
  have he := congrArg Complex.im ((planeBasis J).sum_repr Complex.I)
  simp [Fin.sum_univ_two, planeBasis_apply, h, Complex.real_smul] at he

/-- The orientation component of a complex structure on the real plane is detected at one.
The standard area form tames exactly the component for which `Im (J 1)` is positive. -/
theorem stdComplexSymplecticForm_tames_iff_im_pos (J : AlmostComplexStructure ℂ) :
    stdComplexSymplecticForm.Tames J ↔ 0 < (J 1).im := by
  constructor
  · intro h
    simpa using h 1 one_ne_zero
  · intro h z hz
    let x := (planeBasis J).repr z 0
    let y := (planeBasis J).repr z 1
    have he : z = x • (1 : ℂ) + y • J 1 := by
      simpa [x, y, Fin.sum_univ_two, planeBasis_apply] using
        ((planeBasis J).sum_repr z).symm
    have hxy : x ≠ 0 ∨ y ≠ 0 := by
      by_contra! hxy
      exact hz (by simpa [hxy.1, hxy.2] using he)
    have hsq : 0 < x ^ 2 + y ^ 2 := by
      rcases hxy with hx | hy
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg y)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg x) (sq_pos_of_ne_zero hy)
    rw [he, map_add, map_smul, map_smul, J.apply_apply]
    have ha : stdComplexSymplecticForm (x • (1 : ℂ) + y • J 1)
        (x • J 1 + y • -(1 : ℂ)) = (x ^ 2 + y ^ 2) * (J 1).im := by
      simp [stdComplexSymplecticForm_apply, Complex.real_smul]
      ring
    rw [ha]
    exact mul_pos hsq h

/-- The opposite standard structure lies outside the positive component. -/
theorem stdComplexSymplecticForm_not_tames_neg :
    ¬ stdComplexSymplecticForm.Tames (-(AlmostComplexStructure.ofComplexModule ℂ)) := by
  rw [stdComplexSymplecticForm_tames_iff_im_pos]
  simp [AlmostComplexStructure.ofComplexModule_apply]

/-- Conjugating the real chart puts exactly the negative component in the positive chart.
Thus the scalar unit-disc chart is used only after choosing the complex orientation. -/
theorem stdComplexSymplecticForm_tames_transport_conj_iff (J : AlmostComplexStructure ℂ) :
    stdComplexSymplecticForm.Tames (J.transport Complex.conjCLE.toLinearEquiv) ↔
      (J 1).im < 0 := by
  rw [stdComplexSymplecticForm_tames_iff_im_pos]
  simp

/-- Every plane complex structure belongs to the positive scalar chart after either keeping
or conjugating the real coordinates. -/
theorem stdComplexSymplecticForm_tames_or_tames_transport_conj (J : AlmostComplexStructure ℂ) :
    stdComplexSymplecticForm.Tames J ∨
      stdComplexSymplecticForm.Tames (J.transport Complex.conjCLE.toLinearEquiv) := by
  rw [stdComplexSymplecticForm_tames_iff_im_pos, stdComplexSymplecticForm_tames_transport_conj_iff]
  exact (lt_or_gt_of_ne (AlmostComplexStructure.im_apply_one_ne_zero J)).symm

/-- Every real one-dimensional subspace of the complex plane is Lagrangian for its
standard symplectic area form. -/
theorem isLagrangian_stdComplexSymplecticForm_of_finrank_eq_one {L : Submodule ℝ ℂ}
    (hL : Module.finrank ℝ L = 1) : stdComplexSymplecticForm.IsLagrangian L := by
  have hne : L ≠ ⊥ := by
    intro h
    have hz : Module.finrank ℝ L = 0 := Submodule.finrank_eq_zero.2 h
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0
  have hi : stdComplexSymplecticForm.IsIsotropic L := by
    rw [hs, SymplecticForm.isIsotropic_span_iff]
    simpa only [Set.mem_singleton_iff, forall_eq] using stdComplexSymplecticForm.isAlt v
  exact hi.isLagrangian_of_finrank (by simp [hL])

end TauCeti
