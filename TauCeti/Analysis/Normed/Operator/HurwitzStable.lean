/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Algebra.Exponential
public import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Exponential decay of Hurwitz-stable operators

An operator on a finite-dimensional space is *Hurwitz stable* when all its complex eigenvalues lie
in the open left half-plane. The flow `t ↦ exp (t • T)` of such an operator then decays
exponentially: `‖exp (t • T)‖ ≤ K * Real.exp (-α * t)` for `t ≥ 0`, with `α > 0`. This is the
linear estimate behind exponential dichotomies of hyperbolic equilibria.

Over `ℂ` the eigenvalue condition is stated on the spectrum
(`ContinuousLinearMap.exists_norm_exp_smul_le_of_forall_mem_spectrum_re_neg`). Every point of the
spectrum of `exp T` is `exp z` for an eigenvalue `z` of `T`
(`ContinuousLinearMap.exists_mem_spectrum_eq_exp_of_mem_spectrum_exp`, and
`ContinuousLinearMap.spectrum_exp` for the resulting equality of sets): `T` commutes with
`exp T`, so it preserves an eigenspace of `exp T` and has an eigenvector there. Hence the
spectral radius of `exp T` is less than one, Gelfand's formula gives some power `exp T ^ n` of
norm less than one, and the semigroup law spreads this contraction over all times
(`TauCeti.exists_norm_exp_smul_le_of_norm_exp_smul_lt_one`).

Over `ℝ` the complex eigenvalues are the complex roots of the polynomials annihilating the
operator, and the condition is stated that way
(`ContinuousLinearMap.exists_norm_exp_smul_le_of_aeval_eq_zero`): if `p(B) = 0` for a real
polynomial `p` whose complex roots all have negative real part, the flow of `B` decays
exponentially. The proof passes to the complexification of `B`, realized as the complex matrix of
`B` in a basis, and applies the complex result.

## References

* M. W. Hirsch, S. Smale and R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, third edition, Academic Press, 2013, Chapter 7.
-/

public section

open NormedSpace Polynomial

namespace ContinuousLinearMap

section Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

/-- In finite dimensions, every point of the spectrum of `exp T` is the exponential of a point of
the spectrum of `T`. -/
theorem exists_mem_spectrum_eq_exp_of_mem_spectrum_exp (T : F →L[ℂ] F) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (exp T)) : ∃ z ∈ spectrum ℂ T, μ = exp z := by
  rw [spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  -- `T` preserves the `μ`-eigenspace of `exp T` and has an eigenvector `w` there.
  have hcomm : Commute ((exp T : F →L[ℂ] F) : F →ₗ[ℂ] F) (T : F →ₗ[ℂ] F) :=
    congrArg (fun S : F →L[ℂ] F ↦ (S : F →ₗ[ℂ] F)) ((Commute.refl T).exp_left).eq
  have hmaps := Module.End.mapsTo_genEigenspace_of_comm hcomm μ 1
  have : Nontrivial (Module.End.eigenspace ((exp T : F →L[ℂ] F) : F →ₗ[ℂ] F) μ) :=
    Submodule.nontrivial_iff_ne_bot.mpr hμ
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue
    ((T : F →ₗ[ℂ] F).restrict fun _ hx ↦ hmaps hx)
  obtain ⟨⟨w, hwW⟩, hw⟩ := hz.exists_hasEigenvector
  have hTw : T w = z • w := by
    simpa [LinearMap.coe_restrict_apply] using congrArg Subtype.val hw.apply_eq_smul
  have hw0 : w ≠ 0 := fun h ↦ hw.2 (Subtype.ext h)
  refine ⟨z, ?_, ?_⟩
  · rw [spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum]
    exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr hTw, hw0⟩
  · have h : exp T w = μ • w := Module.End.mem_eigenspace_iff.mp hwW
    rw [T.exp_apply_of_apply_eq_smul hTw] at h
    exact (smul_left_injective ℂ hw0 h).symm

/-- **Spectral mapping for the exponential, in finite dimensions.** The spectrum of `exp T` is the
image of the spectrum of `T` under the exponential. -/
theorem spectrum_exp (T : F →L[ℂ] F) : spectrum ℂ (exp T) = exp '' spectrum ℂ T := by
  refine Set.Subset.antisymm (fun μ hμ ↦ ?_) ?_
  · obtain ⟨z, hz, rfl⟩ := exists_mem_spectrum_eq_exp_of_mem_spectrum_exp T hμ
    exact ⟨z, hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have := FiniteDimensional.complete ℂ F
    exact spectrum.exp_mem_exp T hz

/-- **Exponential decay for a Hurwitz-stable complex operator.** If every point of the spectrum of
an operator `T` on a finite-dimensional complex space has negative real part, then
`‖exp (t • T)‖ ≤ K * Real.exp (-α * t)` for all `t ≥ 0`, with constants `K` and `α > 0`. -/
theorem exists_norm_exp_smul_le_of_forall_mem_spectrum_re_neg (T : F →L[ℂ] F)
    (h : ∀ z ∈ spectrum ℂ T, z.re < 0) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • T)‖ ≤ K * Real.exp (-α * t) := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · refine ⟨0, 1, one_pos, fun t _ ↦ ?_⟩
    rw [Subsingleton.elim (exp (t • T)) 0, norm_zero, zero_mul]
  have hρ : spectralRadius ℂ (exp T) < 1 := by
    have := spectrum.spectralRadius_lt_of_forall_lt (exp T) (r := 1) fun μ hμ ↦ by
      obtain ⟨z, hz, rfl⟩ := exists_mem_spectrum_eq_exp_of_mem_spectrum_exp T hμ
      rw [← NNReal.coe_lt_coe, coe_nnnorm, ← Complex.exp_eq_exp_ℂ, Complex.norm_exp,
        NNReal.coe_one, Real.exp_lt_one_iff]
      exact h z hz
    simpa using this
  -- By Gelfand's formula some power `exp T ^ n = exp (n • T)` has norm less than one.
  obtain ⟨n, hn, hn0⟩ := ((spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius
    (exp T)).eventually (gt_mem_nhds hρ)).and (Filter.eventually_gt_atTop 0) |>.exists
  have hlt : ‖exp ((n : ℝ) • T)‖ < 1 := by
    let +nondep : NormedAlgebra ℚ (F →L[ℂ] F) := .restrictScalars ℚ ℂ _
    rw [Nat.cast_smul_eq_nsmul, exp_nsmul, ← coe_nnnorm, ← NNReal.coe_one, NNReal.coe_lt_coe,
      ← ENNReal.coe_lt_coe, ENNReal.coe_one]
    by_contra hge
    exact (ENNReal.one_le_rpow (le_of_not_gt hge)
      (one_div_pos.mpr (Nat.cast_pos.mpr hn0))).not_gt hn
  exact TauCeti.exists_norm_exp_smul_le_of_norm_exp_smul_lt_one T (Nat.cast_pos.mpr hn0) hlt

end Complex

section Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The complexification of operators on a finite-dimensional real space, realized on matrices
in a fixed basis: an injective real algebra map into the operators on `ℂⁿ`. -/
private noncomputable def complexify :
    (E →L[ℝ] E) →ₐ[ℝ] ((Fin (Module.finrank ℝ E) → ℂ) →L[ℂ] (Fin (Module.finrank ℝ E) → ℂ)) :=
  ((Module.End.toContinuousLinearMap _).restrictScalars ℝ).toAlgHom.comp <|
    ((Matrix.toLinAlgEquiv' (R := ℂ)).restrictScalars ℝ).toAlgHom.comp <|
      (Algebra.ofId ℝ ℂ).mapMatrix.comp <|
        (LinearMap.toMatrixAlgEquiv (Module.finBasis ℝ E)).toAlgHom.comp
          (Module.End.toContinuousLinearMap E).symm.toAlgHom

private theorem complexify_injective : Function.Injective (complexify (E := E)) := by
  simp only [complexify, AlgHom.coe_comp]
  exact (AlgEquiv.injective _).comp <| (AlgEquiv.injective _).comp <|
    (Matrix.map_injective Complex.ofReal_injective).comp <|
      (AlgEquiv.injective _).comp (AlgEquiv.injective _)

/-- The complexification of a real operator annihilated by a real polynomial `p` has its
spectrum among the complex roots of `p`. -/
private theorem aeval_eq_zero_of_mem_spectrum_complexify {B : E →L[ℝ] E} {p : ℝ[X]}
    (hp : aeval B p = 0) {z : ℂ} (hz : z ∈ spectrum ℂ (complexify B)) : aeval z p = 0 := by
  rw [spectrum_eq, ← Module.End.hasEigenvalue_iff_mem_spectrum] at hz
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have h := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap ℝ ℂ)) hv
  rw [eval_map_algebraMap] at h
  have h1 : aeval (complexify B) (p.map (algebraMap ℝ ℂ)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, hp, map_zero]
  -- Pass from the operator to its underlying linear map, through an algebra equivalence.
  have hsymm : (Module.End.toContinuousLinearMap _).symm (complexify B) =
      (complexify B : (Fin (Module.finrank ℝ E) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ E) → ℂ)) :=
    rfl
  rw [← hsymm, aeval_algHom_apply, h1, map_zero, LinearMap.zero_apply] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hv.2

/-- **Exponential decay for a Hurwitz-stable real operator.** If an operator `B` on a
finite-dimensional real space is annihilated by a real polynomial `p` whose complex roots all have
negative real part, then `‖exp (t • B)‖ ≤ K * Real.exp (-α * t)` for all `t ≥ 0`, with constants
`K` and `α > 0`. -/
theorem exists_norm_exp_smul_le_of_aeval_eq_zero (B : E →L[ℝ] E) {p : ℝ[X]}
    (hp : aeval B p = 0) (hroots : ∀ z : ℂ, aeval z p = 0 → z.re < 0) :
    ∃ K α : ℝ, 0 < α ∧ ∀ t : ℝ, 0 ≤ t → ‖exp (t • B)‖ ≤ K * Real.exp (-α * t) := by
  obtain ⟨K, α, hα, hK⟩ := exists_norm_exp_smul_le_of_forall_mem_spectrum_re_neg (complexify B)
    fun z hz ↦ hroots z (aeval_eq_zero_of_mem_spectrum_complexify hp hz)
  -- The complexification is injective and linear on a finite-dimensional space, so it bounds
  -- norms from below, and it commutes with the exponential.
  obtain ⟨C, -, hanti⟩ := LinearMap.exists_antilipschitzWith
    (complexify (E := E)).toLinearMap (LinearMap.ker_eq_bot.mpr complexify_injective)
  refine ⟨C * K, α, hα, fun t ht ↦ ?_⟩
  have hmap : complexify (exp (t • B)) = exp (t • complexify B) := by
    let +nondep : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
    let +nondep : NormedAlgebra ℚ ((Fin (Module.finrank ℝ E) → ℂ) →L[ℂ]
      (Fin (Module.finrank ℝ E) → ℂ)) := .restrictScalars ℚ ℂ _
    rw [map_exp complexify (complexify (E := E)).toLinearMap.continuous_of_finiteDimensional,
      map_smul]
  calc ‖exp (t • B)‖ ≤ C * ‖complexify (exp (t • B))‖ :=
        ZeroHomClass.bound_of_antilipschitz (complexify (E := E)).toLinearMap hanti _
    _ ≤ C * (K * Real.exp (-α * t)) := by rw [hmap]; gcongr; exact hK t ht
    _ = C * K * Real.exp (-α * t) := by ring

end Real

end ContinuousLinearMap
