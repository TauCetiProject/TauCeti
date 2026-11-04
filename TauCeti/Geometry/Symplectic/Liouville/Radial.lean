/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Symplectic.Liouville.Linear
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The radial Liouville structure of a symplectic vector space

Let `ω` be a linear symplectic form on a finite-dimensional real vector space `V`, regarded as the
constant symplectic form `TauCeti.SymplecticForm.constSmooth ω` on `V`. Its **radial primitive**
(`TauCeti.SymplecticForm.radialPrimitive`) is the smooth one-form

`λₓ(v) = ω(x, v) / 2`,

with `dλ = ω` (`TauCeti.SymplecticForm.mextDeriv_radialPrimitive`). Its Liouville field is half
the position field, `ι_Z ω = λ` for `Z(x) = x / 2`
(`TauCeti.SymplecticForm.constSmooth_interior_two_inv_smul`).

## Main definitions

* `TauCeti.SymplecticForm.radialPrimitive`: the one-form `λₓ(v) = ω(x, v) / 2`.

## Main results

* `TauCeti.SymplecticForm.mextDeriv_radialPrimitive`: `dλ = ω`.
* `TauCeti.SymplecticForm.constSmooth_interior_two_inv_smul`: `ι_Z ω = λ` for `Z(x) = x / 2`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (the radial Liouville vector field of a symplectic vector space).
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The **radial primitive** `λₓ(v) = ω(x, v) / 2` of a linear symplectic form `ω`, as a smooth
one-form on `V`. Its exterior derivative is the constant form `ω`
(`TauCeti.SymplecticForm.mextDeriv_radialPrimitive`). -/
def radialPrimitive : SmoothForm 𝓘(ℝ, V) V ℝ 1 :=
  ⟨fun x ↦ ContinuousLinearMap.liouvilleFormCLM ω.toBilinForm.toContinuousBilinearMap x,
    (isSmoothForm_modelSpace_iff.mpr
      (ContinuousLinearMap.liouvilleFormCLM _).contDiff).mem_smoothBundleForms⟩

private theorem radialPrimitive_toRoughForm :
    ω.radialPrimitive.1 =
      fun x ↦ ContinuousLinearMap.liouvilleFormCLM ω.toBilinForm.toContinuousBilinearMap x :=
  (rfl)

/-- The radial primitive evaluates as `λₓ(v) = ω(x, v) / 2`. -/
@[simp]
theorem radialPrimitive_apply (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    ω.radialPrimitive.1 x ![v] = 2⁻¹ * ω x v := by
  rw [radialPrimitive_toRoughForm]
  refine (ContinuousLinearMap.liouvilleFormCLM_apply _ x ![v]).trans ?_
  simp only [LinearMap.toContinuousBilinearMap_apply, smul_eq_mul]
  -- `![v] 0` is `v` by `Matrix.cons_val_zero`, which cannot rewrite here because `![v]` is typed
  -- in `V` while `v` lives in `TangentSpace 𝓘(ℝ, V) x`.
  rfl

/-- **The radial primitive is a primitive**: `dλ = ω`. -/
@[simp]
theorem mextDeriv_radialPrimitive : mextDeriv ω.radialPrimitive.1 = ω.constSmooth.1 := by
  funext x
  ext v
  rw [mextDeriv_eq_extDeriv]
  refine (ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _ two_ne_zero
    (fun u w ↦ by simpa using (ω.neg_eq w u).symm) x v).trans ?_
  have h := ω.constSmooth_apply x (v 0) (v 1)
  rw [SmoothBundleForm.eval₂_apply] at h
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  conv_rhs => rw [hv]
  exact h.symm

/-- The Liouville field of the radial primitive is half the position field:
`ι_Z ω = λ` for `Z(x) = x / 2`. -/
theorem constSmooth_interior_two_inv_smul :
    RoughForm.interior (I := 𝓘(ℝ, V)) (fun x : V ↦ (2⁻¹ : ℝ) • x) ω.constSmooth.1 =
      ω.radialPrimitive.1 := by
  funext x
  ext v
  have hv : v = ![v 0] := by
    funext i
    fin_cases i
    rfl
  refine (RoughForm.interior_apply _ _ x v).trans ?_
  rw [hv, radialPrimitive_apply]
  refine ((SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans (ω.constSmooth_apply _ _ _)).trans ?_
  -- `v 0` lives in `TangentSpace 𝓘(ℝ, V) x`, which blocks `rw`/`simp` with `map_smul₂`.
  exact (LinearMap.map_smul₂ ω.toBilinForm _ x (v 0)).trans (smul_eq_mul _ _)

end SymplecticForm

end TauCeti
