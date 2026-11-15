/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorAlgebra.DegreeScaling
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

/-!
# Rescaling the spinor module of a polarization

For a polarization `V = W ⊕ W' ⊕ L` of a quadratic space and a unit `r` of the base ring, the
degree scaling `T_r` of `⋀ W`, which multiplies the `p`-th exterior power by `r ^ p`, conjugates the
spinor representation `TauCeti.spinAction` into another representation of the same Clifford
algebra on the same carrier. In it a vector `x` of `W` acts by `r` times exterior multiplication,
a vector `y` of `W'` by `r⁻¹` times contraction, and a vector of the remainder as before.

This is how the normalization of a Fock action is changed. The native action contracts against
the polar form `QuadraticMap.polar Q`; when `Q` is the negative `-g` of a metric, this is
`-2 g`, and the degree scaling by `√2` turns the native action into the symmetric
`√2`-normalized one, in which creation and contraction against `g` carry the same factor.

## Main definitions

* `TauCeti.SpinPolarizationData.scaledSpinAction`: the conjugate of `TauCeti.spinAction` by the
  degree scaling by `r`.

## Main results

* `TauCeti.SpinPolarizationData.degreeScaling_comp_spinAction`: the degree scaling intertwines
  the spinor representation with its rescaled form.
* `TauCeti.SpinPolarizationData.scaledSpinAction_ι_coe_W`,
  `TauCeti.SpinPolarizationData.scaledSpinAction_ι_coe_W'` and
  `TauCeti.SpinPolarizationData.scaledSpinAction_ι_coe_line`: the three summands act by `r` times
  exterior multiplication, `r⁻¹` times contraction, and the unchanged parity operator.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open CliffordAlgebra ExteriorAlgebra
open TauCeti.ExteriorAlgebra

namespace TauCeti.SpinPolarizationData

universe u v

variable {K : Type u} [CommRing K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)

/-- **The rescaled spinor representation**: the conjugate of the spinor representation
`TauCeti.spinAction Q P` by the degree scaling of `⋀ W` by the unit `r`. A vector of `W` acts by
`r` times exterior multiplication, a vector of `W'` by `r⁻¹` times contraction, and a vector of
the orthogonal remainder by the unchanged parity operator. -/
noncomputable def scaledSpinAction (r : Kˣ) :
    CliffordAlgebra Q →ₐ[K] Module.End K (ExteriorAlgebra K P.W) :=
  ((degreeScaling r).toLinearEquiv.conjAlgEquiv K).toAlgHom.comp (spinAction Q P)

/-- The rescaled spinor representation is the conjugate of the spinor representation by the
degree scaling. -/
theorem scaledSpinAction_apply (r : Kˣ) (a : CliffordAlgebra Q) (s : ExteriorAlgebra K P.W) :
    P.scaledSpinAction r a s = degreeScaling r (spinAction Q P a (degreeScaling r⁻¹ s)) := by
  simp only [scaledSpinAction, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
    LinearEquiv.conjAlgEquiv_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.coe_toLinearEquiv, degreeScaling_symm]

/-- **The degree scaling intertwines the spinor representation with its rescaled form**:
`T_r ∘ spinAction a = scaledSpinAction r a ∘ T_r`. -/
theorem degreeScaling_comp_spinAction (r : Kˣ) (a : CliffordAlgebra Q) :
    (degreeScaling r).toLinearMap ∘ₗ spinAction Q P a =
      P.scaledSpinAction r a ∘ₗ (degreeScaling r).toLinearMap := by
  refine LinearMap.ext fun s ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, scaledSpinAction_apply, ← degreeScaling_symm,
    AlgEquiv.toLinearMap_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]

/-- The rescaling by the unit `1` is the spinor representation itself. -/
@[simp]
theorem scaledSpinAction_one : P.scaledSpinAction 1 = spinAction Q P := by
  refine AlgHom.ext fun a ↦ LinearMap.ext fun s ↦ ?_
  rw [scaledSpinAction_apply, inv_one, degreeScaling_one, AlgEquiv.coe_refl, id_eq, id_eq]

/-- In the rescaled spinor representation a vector of `W` acts by `r` times exterior
multiplication. -/
@[simp]
theorem scaledSpinAction_ι_coe_W (r : Kˣ) (x : P.W) :
    P.scaledSpinAction r (CliffordAlgebra.ι Q x) = (r : K) • P.wedge x := by
  refine LinearMap.ext fun s ↦ ?_
  rw [scaledSpinAction_apply, spinAction_ι_wedge, map_mul, degreeScaling_ι,
    ← degreeScaling_symm, AlgEquiv.apply_symm_apply, smul_mul_assoc, LinearMap.smul_apply,
    wedge_apply]

/-- In the rescaled spinor representation a vector of `W'` acts by `r⁻¹` times contraction. -/
@[simp]
theorem scaledSpinAction_ι_coe_W' (r : Kˣ) (y : P.W') :
    P.scaledSpinAction r (CliffordAlgebra.ι Q y) = ((r⁻¹ : Kˣ) : K) • P.contract y := by
  refine LinearMap.ext fun s ↦ ?_
  rw [scaledSpinAction_apply, spinAction_ι_contract, degreeScaling_contractLeft,
    ← degreeScaling_symm, AlgEquiv.apply_symm_apply, LinearMap.smul_apply, contract_apply]

/-- In the rescaled spinor representation a vector of the orthogonal remainder still acts by its
scalar coordinate times the parity operator. -/
@[simp]
theorem scaledSpinAction_ι_coe_line (r : Kˣ) (z : P.line) :
    P.scaledSpinAction r (CliffordAlgebra.ι Q z) = P.lineOperator z := by
  refine LinearMap.ext fun s ↦ ?_
  rw [scaledSpinAction_apply, spinAction_ι_lineOperator, map_smul, degreeScaling_involute,
    ← degreeScaling_symm, AlgEquiv.apply_symm_apply, lineOperator_apply]

end TauCeti.SpinPolarizationData
