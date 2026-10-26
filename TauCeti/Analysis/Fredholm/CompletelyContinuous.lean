/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.FiniteRank
public import TauCeti.Analysis.Normed.Operator.CompletelyContinuous
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The Fredholm alternative for completely continuous operators

On a Banach space over a complete nontrivially normed field, `1 - u` is Fredholm of index zero
whenever `u` is a norm limit of operators of finite rank. In particular, injectivity, surjectivity
and invertibility of `1 - u` are equivalent, and every nonzero spectral value of `u` is an
eigenvalue. These statements apply over nonarchimedean fields without local compactness or
spherical completeness.

The native `ContinuousLinearMap.IsFredholm` conclusion includes strictness, closed range,
finite-dimensional kernel and cokernel, and a continuous complement to the kernel.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3, 7.
-/

public section

namespace TauCeti

open ContinuousLinearMap

variable {K E : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
  {u : E →L[K] E}

-- Approximate `u` by a finite-rank `v` with `‖u - v‖ < 1`. Neumann inversion makes
-- `1 - (u - v)` invertible, so `1 - u` is an invertible operator plus a finite-rank map.
-- The Fredholm and index conclusions below follow by finite-rank perturbation.
private theorem exists_equiv_add_hasFiniteRange (hu : u.IsCompletelyContinuous) :
    ∃ (e : E ≃L[K] E) (w : E →L[K] E),
      LinearMap.HasFiniteRange (w : E →ₗ[K] E) ∧ (e : E →L[K] E) + w = 1 - u := by
  obtain ⟨v, hv, huv⟩ := isCompletelyContinuous_iff.mp hu (1 / 2) one_half_pos
  have huv' : ‖u - v‖ < 1 :=
    (opNorm_le_bound _ (by positivity) (by simpa using huv)).trans_lt one_half_lt_one
  let e := ContinuousLinearEquiv.ofUnit (Units.oneSub (u - v) huv')
  -- The forward map of ofUnit is the unit's value, identified by val_oneSub.
  have he : (e : E →L[K] E) = 1 - (u - v) := by
    ext x
    exact congrArg (fun f : E →L[K] E ↦ f x) (Units.val_oneSub (u - v) huv')
  refine ⟨e, -v, by simpa using hv.hasFiniteRange.neg, ?_⟩
  rw [he]
  abel

end TauCeti

namespace ContinuousLinearMap

variable {K E : Type*} [NontriviallyNormedField K] [CompleteSpace K]
  [NormedAddCommGroup E] [NormedSpace K E] [CompleteSpace E]
  {u : E →L[K] E}

/-- A completely continuous perturbation of the identity is a Fredholm operator, over any
complete nontrivially normed field. -/
theorem IsCompletelyContinuous.isFredholm_one_sub (hu : u.IsCompletelyContinuous) :
    IsFredholm (1 - u) := by
  obtain ⟨e, w, hw, he⟩ := TauCeti.exists_equiv_add_hasFiniteRange hu
  rw [← he]
  exact e.isFredholm.add_hasFiniteRange hw

/-- A completely continuous perturbation of the identity has Fredholm index zero. -/
@[simp]
theorem IsCompletelyContinuous.index_one_sub_eq_zero (hu : u.IsCompletelyContinuous) :
    (1 - u).index = 0 := by
  obtain ⟨e, w, hw, he⟩ := TauCeti.exists_equiv_add_hasFiniteRange hu
  rw [← he, index_add_of_hasFiniteRange e.isFredholm hw, e.index_eq_zero]

/-- For a completely continuous `u`, injectivity of `1 - u` is equivalent to invertibility. -/
theorem IsCompletelyContinuous.isUnit_one_sub_iff_injective (hu : u.IsCompletelyContinuous) :
    IsUnit (1 - u) ↔ Function.Injective (1 - u : E →L[K] E) := by
  refine ⟨fun h ↦ (isUnit_iff_bijective.mp h).injective, fun hinj ↦ ?_⟩
  have hfin := hu.isFredholm_one_sub.finite_coker
  have hindex := hu.index_one_sub_eq_zero
  rw [index_of_injective _ hinj] at hindex
  have hdim : Module.finrank K (E ⧸ (1 - u : E →L[K] E).range) = 0 := by omega
  have htop : (1 - u : E →L[K] E).range = ⊤ := by
    have := Module.finrank_zero_iff.mp hdim
    exact Submodule.Quotient.subsingleton_iff.mp inferInstance
  exact isUnit_iff_bijective.mpr ⟨hinj, LinearMap.range_eq_top.mp htop⟩

/-- For a completely continuous `u`, surjectivity of `1 - u` is equivalent to invertibility. -/
theorem IsCompletelyContinuous.isUnit_one_sub_iff_surjective (hu : u.IsCompletelyContinuous) :
    IsUnit (1 - u) ↔ Function.Surjective (1 - u : E →L[K] E) := by
  refine ⟨fun h ↦ (isUnit_iff_bijective.mp h).surjective, fun hsurj ↦ ?_⟩
  exact isUnit_iff_bijective.mpr <|
    bijective_of_surjective_of_index_eq_zero _ hu.isFredholm_one_sub.finite_ker hsurj
      hu.index_one_sub_eq_zero

/-- Every nonzero spectral value of a completely continuous operator is an eigenvalue.
The spectrum is the spectrum in the algebra of continuous endomorphisms. -/
theorem IsCompletelyContinuous.hasEigenvalue_iff_mem_spectrum (hu : u.IsCompletelyContinuous)
    {μ : K} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (u : Module.End K E) μ ↔ μ ∈ spectrum K u := by
  have hker : (1 - μ⁻¹ • u : E →L[K] E).ker =
      Module.End.eigenspace (u : Module.End K E) μ := by
    ext x
    simp only [LinearMap.mem_ker, coe_coe, sub_apply, smul_apply,
      sub_eq_zero, eq_inv_smul_iff₀ hμ, Module.End.mem_eigenspace_iff]
    exact eq_comm
  have hscale : μ ∈ spectrum K u ↔ 1 ∈ spectrum K (μ⁻¹ • u) := by
    simpa [Units.smul_def, smul_eq_mul, hμ] using
      (spectrum.smul_mem_smul_iff (a := u) (s := μ)
        (r := Units.mk0 μ⁻¹ (inv_ne_zero hμ))).symm
  rw [hscale, spectrum.mem_iff, map_one, (hu.smul μ⁻¹).isUnit_one_sub_iff_injective]
  simpa only [Module.End.hasEigenvalue_iff, hker, coe_coe] using
    not_congr (LinearMap.ker_eq_bot (f := (1 - μ⁻¹ • u : E →L[K] E).toLinearMap))

end ContinuousLinearMap
