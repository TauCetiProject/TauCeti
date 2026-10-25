/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integration on compactly supported cohomology and the Poincaré pairing

On an oriented boundaryless manifold, Stokes' theorem says that the exterior derivative of a
compactly supported form integrates to zero. Hence integration of compactly supported closed
top forms descends to a linear map `∫_M : H^n_c(M) → ℝ` on compactly supported de Rham
cohomology, computed on classes by integrating a representative.

Composing it with the wedge product `H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` gives the Poincaré
pairing `⟨[φ], [ψ]⟩ = ∫_M φ ∧ ψ` between de Rham cohomology and compactly supported de Rham
cohomology in complementary degrees `k + l = n`. Poincaré duality, which is not proved here,
asserts that this pairing identifies `H^k_dR(M)` with the dual of `H^l_c(M)`.

Both maps need the manifold to be boundaryless. On `M = [0, 1]` the form `dx` is exact, yet the
representative formula pairs it with the class of the constant function `1` to give
`∫₀¹ dx = 1`; integration does not descend to cohomology there.

## Main definitions and results

* `TauCeti.integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms`: on a boundaryless
  manifold, the exterior derivative of a compactly supported form integrates to zero.
* `TauCeti.compactlySupportedDeRhamCohomology.integral`: integration `H^n_c(M) → ℝ`, computed on
  classes by `TauCeti.compactlySupportedDeRhamCohomology.integral_mk`.
* `TauCeti.poincarePairing`: the pairing `H^k_dR(M) → H^l_c(M) → ℝ`, the wedge product followed
  by integration (`TauCeti.poincarePairing_apply`), computed on classes by
  `TauCeti.poincarePairing_mk`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17, the integration map on
  compactly supported top-degree cohomology, and Problems 18-6 to 18-8 (Poincaré duality).
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] {k l n : ℕ}

/-- On an oriented boundaryless manifold, the exterior derivative of a compactly supported smooth
form integrates to zero. This is Stokes' theorem for compactly supported exact top forms. -/
theorem integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms
    (o : Manifold.Orientation I M (Fin n)) {φ : SmoothForm I M ℝ n}
    (hφ : φ ∈ exactCompactlySupportedForms I M n) : integralTopForm o φ.1 = 0 := by
  cases n with
  | zero =>
    rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hφ
    rw [hφ]
    exact integralTopForm_zero o
  | succ n =>
    rw [exactCompactlySupportedForms_succ, Submodule.mem_map] at hφ
    obtain ⟨β, hβ, rfl⟩ := hφ
    rw [mextDerivₗ_apply]
    exact integralTopForm_mextDeriv_eq_zero o (β.isSmoothForm.of_le (by simp))
      ((mem_compactlySupportedForms I).mp hβ)

namespace compactlySupportedDeRhamCohomology

/-- Integration of compactly supported closed top forms, as a linear map. -/
private def integralClosedForms (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedClosedForms I M n →ₗ[ℝ] ℝ where
  toFun φ := integralTopForm o φ.1.1
  map_add' φ ψ := integralTopForm_add o (φ.1.isSmoothForm.of_le (by simp))
    (ψ.1.isSmoothForm.of_le (by simp))
    ((mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp φ.2).1)
    ((mem_compactlySupportedForms I).mp ((mem_compactlySupportedClosedForms I).mp ψ.2).1)
  map_smul' c φ := integralTopForm_smul o c φ.1.1

/-- Compactly supported exact top forms are killed by integration. -/
private theorem ker_mk_le_ker_integralClosedForms (o : Manifold.Orientation I M (Fin n)) :
    LinearMap.ker (mk I (M := M) n) ≤ LinearMap.ker (integralClosedForms o) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  exact integralTopForm_eq_zero_of_mem_exactCompactlySupportedForms o hφ

/-- Integration `H^n_c(M) → ℝ` over an oriented boundaryless manifold, induced by integrating
compactly supported closed top forms. -/
def integral (o : Manifold.Orientation I M (Fin n)) :
    compactlySupportedDeRhamCohomology I M n →ₗ[ℝ] ℝ :=
  LinearMap.liftOfSurjective (R := ℝ) (M := compactlySupportedClosedForms I M n)
    (M₂ := compactlySupportedDeRhamCohomology I M n) (M₃ := ℝ) (f := mk I (M := M) n)
    (mk_surjective I n) ⟨integralClosedForms o, ker_mk_le_ker_integralClosedForms o⟩

/-- The integral of the class of a compactly supported closed top form is the integral of the
form. -/
@[simp]
theorem integral_mk (o : Manifold.Orientation I M (Fin n))
    (φ : compactlySupportedClosedForms I M n) :
    integral o (mk I n φ) = integralTopForm o φ.1.1 :=
  LinearMap.equivOfSurjective_apply _ _

end compactlySupportedDeRhamCohomology

variable (I M) in
/-- The Poincaré pairing `H^k_dR(M) → H^l_c(M) → ℝ` on an oriented boundaryless manifold of
dimension `k + l`, sending classes `[φ]` and `[ψ]` to `∫_M φ ∧ ψ`. It is the wedge product
`H^k_dR(M) → H^l_c(M) → H^(k+l)_c(M)` followed by integration. -/
def poincarePairing (o : Manifold.Orientation I M (Fin (k + l))) :
    deRhamCohomology I M ℝ k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M l →ₗ[ℝ] ℝ :=
  (compactlySupportedDeRhamCohomology.wedge I M k l).compr₂
    (compactlySupportedDeRhamCohomology.integral o)

/-- The Poincaré pairing of two classes is the integral of their wedge product. -/
theorem poincarePairing_apply (o : Manifold.Orientation I M (Fin (k + l)))
    (x : deRhamCohomology I M ℝ k) (y : compactlySupportedDeRhamCohomology I M l) :
    poincarePairing I M o x y =
      compactlySupportedDeRhamCohomology.integral o
        (compactlySupportedDeRhamCohomology.wedge I M k l x y) :=
  (rfl)

/-- The Poincaré pairing of the classes of a closed form `φ` and a compactly supported closed
form `ψ` is `∫_M φ ∧ ψ`. -/
@[simp]
theorem poincarePairing_mk (o : Manifold.Orientation I M (Fin (k + l)))
    (φ : closedForms I M ℝ k) (ψ : compactlySupportedClosedForms I M l) :
    poincarePairing I M o (deRhamCohomology.mk I k φ)
        (compactlySupportedDeRhamCohomology.mk I l ψ) =
      integralTopForm o ((φ.1 : RoughForm I M ℝ k).wedge ψ.1.1) := by
  rw [poincarePairing_apply, compactlySupportedDeRhamCohomology.wedge_mk,
    compactlySupportedDeRhamCohomology.integral_mk, SmoothForm.coe_wedge]

end TauCeti
