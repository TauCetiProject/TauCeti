/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
public import TauCeti.LinearAlgebra.Determinant.Endomorphism

/-!
# The canonical trivialization of the determinant line of a complex endomorphism

Let `T` be a complex-linear endomorphism of a finite-dimensional complex vector space `V`. The
determinant line `det T = det (ker T) ⊗ (det (coker T))^*` of its real restriction carries two
orientations which involve no choices:

* the canonical trivialization `det T ≃ ℝ` (`LinearMap.detLineEndEquiv`), which identifies
  `det T` with `det V ⊗ (det V)^*` through the exact sequence `0 → ker T → V → V → coker T → 0`
  and then contracts;
* the complex orientation (`LinearMap.IsComplexPositiveDetLine`), given by complex bases of the
  kernel and the cokernel.

They agree: the canonical trivialization is positive exactly on the complex positive elements
(`LinearMap.detLineEndEquiv_pos_iff_isComplexPositiveDetLine`). Indeed the four-term isomorphism
of an exact sequence of complex vector spaces respects complex orientations
(`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr`), and the contraction
`β ⊗ φ ↦ φ β` is positive on a complex positive `β ∈ det V` and a complex positive functional
`φ` on `det V`. For bijective `T` this is the positivity of `det T` over `ℝ`, which is
`|det T|²` over `ℂ`; the statement also covers the case where `T` has a kernel, which the
determinant does not see.

This is the normalization by which the canonical trivialization serves as an orientation of a
family of determinant lines whose members at complex-linear points carry their complex
orientations. For instance, when the kernel and cokernel of a differential operator are
identified with those of a finite endomorphism, as for linear periodic equations and their
return maps in `TauCeti.Analysis.ODE.Periodic`, the orientation induced by the canonical
trivialization is the complex one whenever the operator is complex linear.

## Main results

* `LinearMap.IsComplexPositiveDetLine.detLineEndEquiv_pos`: the canonical trivialization is
  positive on complex positive elements.
* `LinearMap.detLineEndEquiv_pos_iff_isComplexPositiveDetLine`: an element of the determinant
  line is complex positive exactly when its canonical trivialization is positive.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles and the complex
  orientation of complex-linear Fredholm operators).
-/

public section

noncomputable section

open Module TensorProduct TauCeti

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  -- Real finite-dimensionality follows from the complex one through the scalar tower, but
  -- `LinearMap.detLineEndEquiv` takes it as an instance argument.
  [FiniteDimensional ℝ V] {T : V →ₗ[ℂ] V} {z : (T.restrictScalars ℝ).detLine}

/-- **The canonical trivialization of a complex endomorphism is complex positive.** For a
complex-linear endomorphism `T` of a finite-dimensional complex vector space, the canonical
trivialization of the determinant line of its real restriction (`LinearMap.detLineEndEquiv`) is
positive on every complex positive element. -/
theorem IsComplexPositiveDetLine.detLineEndEquiv_pos (hz : T.IsComplexPositiveDetLine z) :
    0 < (T.restrictScalars ℝ).detLineEndEquiv z := by
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  have : FiniteDimensional ℝ (ker T) := Module.Finite.trans ℂ (ker T)
  -- The image of a complex positive `β ⊗ φ ∈ det V ⊗ (det V)^*` under the four-term isomorphism
  -- of `0 → ker T → V → V → coker T → 0` is complex positive.
  obtain ⟨β, hβ⟩ := exists_isComplexPositive (E := V)
  obtain ⟨φ, hφ⟩ := exists_isComplexPositiveDual (E := V)
  have hw := isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr
    (f := (ker T).subtype) (g := T) (h := (range T).mkQ) (ker T).injective_subtype
    T.exact_subtype_ker_map T.exact_map_mkQ_range (range T).mkQ_surjective
    (ker (T.restrictScalars ℝ)).injective_subtype (T.restrictScalars ℝ).exact_subtype_ker_map
    (T.restrictScalars ℝ).exact_map_mkQ_range (range (T.restrictScalars ℝ)).mkQ_surjective
    (T.kerRestrictScalarsEquiv ℝ) (LinearEquiv.refl ℝ V) (T.cokerRestrictScalarsEquiv ℝ).symm
    (LinearMap.ext fun x ↦ coe_kerRestrictScalarsEquiv_apply ℝ T x) (LinearMap.ext fun _ ↦ rfl)
    (LinearMap.ext fun y ↦ (cokerRestrictScalarsEquiv_symm_mk ℝ T y).symm)
    (hβ.isComplexPositiveTMulDual_tmul hφ)
  rw [LinearEquiv.detLineCongr_refl, LinearEquiv.rTensor_refl_apply] at hw
  -- The transport in `hw` is `LinearMap.detLineRestrictScalarsEquiv`.
  rw [← detLineRestrictScalarsEquiv_def, ← isComplexPositiveDetLine_iff] at hw
  -- `z` is a positive multiple of that image, on which the trivialization is `φ β > 0`.
  obtain ⟨c, hc, rfl⟩ := IsComplexPositiveDetLine.exists_pos_smul_eq (f := T) hw hz
  rw [map_smul, detLineEndEquiv_detLineFourTermEquiv, smul_eq_mul]
  exact mul_pos hc ((hβ.isComplexPositiveDual_iff).1 hφ)

/-- **The canonical trivialization of a complex endomorphism is its complex orientation.** An
element of the determinant line of the real restriction of a complex-linear endomorphism `T` is
complex positive exactly when the canonical trivialization `LinearMap.detLineEndEquiv` takes a
positive value on it. -/
theorem detLineEndEquiv_pos_iff_isComplexPositiveDetLine :
    0 < (T.restrictScalars ℝ).detLineEndEquiv z ↔ T.IsComplexPositiveDetLine z := by
  have : FiniteDimensional ℂ V := Module.Finite.of_restrictScalars_finite ℝ ℂ V
  refine ⟨fun h ↦ ?_, IsComplexPositiveDetLine.detLineEndEquiv_pos⟩
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact h.false
  refine (isComplexPositiveDetLine_or_isComplexPositiveDetLine_neg hz).resolve_right fun hneg ↦ ?_
  have := hneg.detLineEndEquiv_pos
  rw [map_neg (T.restrictScalars ℝ).detLineEndEquiv z] at this
  linarith

end LinearMap
