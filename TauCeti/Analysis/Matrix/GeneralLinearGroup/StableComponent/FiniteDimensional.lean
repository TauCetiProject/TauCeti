/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.Connected
public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Polar
public import TauCeti.Topology.Algebra.Star.Unitary

/-!
# The stable component group of a finite-dimensional C⋆-algebra is trivial

An element of a finite-dimensional algebra over a field is integral, so its spectrum is finite
(`spectrum.finite_of_finiteDimensional`). A unitary `u` of a unital C⋆-algebra whose spectrum
misses a point `z` of the unit circle is joined to `1` by a path of unitaries
(`Unitary.joined_one_of_notMem_spectrum`): rotating, `-1` is not in the spectrum of `-z⋆ u`, so
`‖-z⋆ u - 1‖ < 2` and Mathlib's exponential path joins `-z⋆ u` to `1`, while scalar rotations
join `u` to `-z⋆ u`. In a finite-dimensional C⋆-algebra every unitary therefore lies in the
identity component of the unitary group.

Applied to the finite-dimensional C⋆-algebras of matrices over a finite-dimensional C⋆-algebra
`A`, and with the polar decomposition of invertible matrices, every class of the stable component
group `π₀ GL_∞(A)` is trivial: `K₁(A) = 0` for finite-dimensional `A`
(`TauCeti.StableComponentGroup.subsingleton_of_finiteDimensional`).

## Main statements

* `spectrum.finite_of_finiteDimensional`: elements of finite-dimensional algebras have finite
  spectrum.
* `Unitary.joined_one_of_notMem_spectrum`, `Unitary.joined_one_of_finite_spectrum`: unitaries whose
  spectrum misses a point of the circle are joined to `1`.
* `TauCeti.StableComponentGroup.subsingleton_of_finiteDimensional`: the stable component group of
  a finite-dimensional C⋆-algebra is trivial.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §8.1.
-/

public section

open Polynomial

/-- An element of a finite-dimensional algebra over a field has finite spectrum: it is integral,
and its spectrum consists of roots of its monic annihilating polynomial. -/
theorem spectrum.finite_of_finiteDimensional {𝕜 A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    [FiniteDimensional 𝕜 A] (a : A) : (spectrum 𝕜 a).Finite := by
  nontriviality A
  obtain ⟨p, hp, hpa⟩ := Algebra.IsIntegral.isIntegral (R := 𝕜) a
  refine (Polynomial.finite_setOfPred_isRoot hp.ne_zero).subset fun k hk ↦ ?_
  have := spectrum.subset_polynomial_aeval a p ⟨k, hk, rfl⟩
  rw [← aeval_def] at hpa
  rw [hpa, spectrum.zero_eq, Set.mem_singleton_iff] at this
  exact this

section Unitary

variable {A : Type*} [CStarAlgebra A]

/-- Multiplying a unitary by a unimodular scalar `w ≠ -1` stays in its path component. -/
private theorem Unitary.joined_smul (v : unitary A) {w : ℂ} (hw : w ∈ unitary ℂ) (hw₁ : w ≠ -1) :
    Joined v ⟨w • (v : A), Unitary.smul_mem_of_mem hw v.prop⟩ := by
  refine Unitary.joined _ _ ?_
  have h : ‖w - 1‖ < 2 := by
    rw [Unitary.norm_sub_one_lt_two_iff hw]
    have : spectrum ℂ w = {w} := by simpa using spectrum.scalar_eq (A := ℂ) w
    rw [this, Set.mem_singleton_iff]
    exact hw₁.symm
  have hv : ‖(v : A)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial A with _ | _
    · simp [Subsingleton.elim (v : A) 0]
    · exact (CStarRing.norm_coe_unitary v).le
  calc ‖w • (v : A) - v‖ = ‖(w - 1) • (v : A)‖ := by rw [sub_smul, one_smul]
    _ ≤ ‖w - 1‖ * ‖(v : A)‖ := norm_smul_le _ _
    _ ≤ ‖w - 1‖ * 1 := by gcongr
    _ < 2 := by rwa [mul_one]

/-- **Unitaries whose spectrum misses a point of the circle are joined to `1`.** If `‖z‖ = 1` and
`z ∉ σ(u)`, then `-1 ∉ σ(-z⋆ u)`, so `-z⋆ u` is joined to `1` by an exponential path, and `u` is
joined to `-z⋆ u` by scalar rotations. -/
theorem Unitary.joined_one_of_notMem_spectrum (u : unitary A) {z : ℂ} (hz : ‖z‖ = 1)
    (hzu : z ∉ spectrum ℂ (u : A)) : Joined 1 u := by
  have hz' : z ∈ unitary ℂ := by
    rw [Unitary.mem_iff_star_mul_self, RCLike.star_def, RCLike.conj_mul, hz]
    simp
  set Z : unitary ℂ := ⟨z, hz'⟩
  set c : ℂ := ((-star Z : unitary ℂ) : ℂ)
  have hc : c ∈ unitary ℂ := (-star Z).prop
  have hc' : c = -star z := rfl
  have hcz : star c * c = 1 := Unitary.star_mul_self_of_mem hc
  set v : unitary A := ⟨c • (u : A), Unitary.smul_mem_of_mem hc u.prop⟩
  -- `-1 ∉ σ(c u) = c σ(u)`, since `-1 = c w` forces `w = z`.
  have hv : Joined 1 v := by
    refine Unitary.joined _ _ ?_
    rw [OneMemClass.coe_one, Unitary.norm_sub_one_lt_two_iff v.prop]
    have hc₀ : c ≠ 0 := by rintro h; simp [h] at hcz
    rw [show (v : A) = (Units.mk0 c hc₀ : ℂˣ) • (u : A) from rfl, spectrum.unit_smul_eq_smul]
    rintro ⟨w, hw, hcw⟩
    refine hzu ?_
    have hzz : star z * z = 1 := Unitary.star_mul_self_of_mem hz'
    have : w = z := by
      simp only [Units.val_mk0, smul_eq_mul, hc'] at hcw
      linear_combination (-w) * hzz - z * hcw
    exact this ▸ hw
  -- `u = c⋆ v`, reached from `v` by one or two scalar rotations.
  have hu : (u : A) = star c • (v : A) := by
    simp only [v, smul_smul, hcz, one_smul]
  refine hv.trans ?_
  by_cases hc₁ : star c = -1
  · have hI : Complex.I ∈ unitary ℂ := by
      rw [Unitary.mem_iff_star_mul_self, RCLike.star_def, RCLike.conj_mul]
      simp
    refine (Unitary.joined_smul v hI (by simp [Complex.ext_iff])).trans ?_
    convert Unitary.joined_smul _ hI (by simp [Complex.ext_iff]) using 1
    ext
    simp only [hu, hc₁, smul_smul, Complex.I_mul_I]
  · convert Unitary.joined_smul v (Unitary.star_mem hc) hc₁ using 1
    exact Subtype.ext hu

/-- A unitary with finite spectrum is joined to `1` by a path of unitaries: its spectrum misses a
point of the infinite unit circle. -/
theorem Unitary.joined_one_of_finite_spectrum (u : unitary A)
    (h : (spectrum ℂ (u : A)).Finite) : Joined 1 u := by
  have hinf : (Metric.sphere (0 : ℂ) 1).Infinite :=
    IsPreconnected.infinite_of_nontrivial (isConnected_sphere (E := ℂ)
      (by rw [Complex.rank_real_complex]; norm_num) 0 zero_le_one).isPreconnected
      ⟨1, by simp, -1, by simp, by norm_num⟩
  obtain ⟨z, hz, hzu⟩ := hinf.exists_notMem_finite h
  exact Unitary.joined_one_of_notMem_spectrum u (by simpa using hz) hzu

end Unitary

namespace TauCeti.StableComponentGroup

variable {A : Type*} [CStarAlgebra A]

/-- **`K₁` of a finite-dimensional C⋆-algebra vanishes**: its stable component group is trivial.
Every class is that of a unitary matrix, which has finite spectrum in the finite-dimensional
C⋆-algebra of matrices, so it is joined to `1`. -/
theorem subsingleton_of_finiteDimensional [FiniteDimensional ℂ A] :
    Subsingleton (StableComponentGroup A) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  suffices h : ∀ x : StableComponentGroup A, x = 1 from ⟨fun x y ↦ (h x).trans (h y).symm⟩
  intro x
  obtain ⟨n, u, hu, rfl⟩ := exists_mem_unitary_mk_eq x
  have : FiniteDimensional ℂ (CStarMatrix (Fin n) (Fin n) A) :=
    LinearEquiv.finiteDimensional (CStarMatrix.ofMatrixₗ (R := ℂ))
  set U : unitary (CStarMatrix (Fin n) (Fin n) A) :=
    ⟨CStarMatrix.ofMatrix (u : Matrix (Fin n) (Fin n) A), by
      rw [← CStarMatrix.ofMatrix_symm_mem_unitary_iff]; exact hu⟩
  have hU := Unitary.joined_one_of_finite_spectrum U (spectrum.finite_of_finiteDimensional _)
  have hj : Joined 1 u := by
    convert hU.map ((map_continuous (Matrix.GeneralLinearGroup.toCStarMatrixUnits (n := Fin n)
      (A := A)).symm).comp Unitary.continuous_toUnits) using 1
    · simp
    · ext : 1
      simp [U]
  simpa using mk_eq_one_of_mem_connectedComponentOfOne (by
    simpa using hj.inv_mul_mem_connectedComponentOfOne)

end TauCeti.StableComponentGroup
