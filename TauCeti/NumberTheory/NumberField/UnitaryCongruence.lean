/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
import TauCeti.Analysis.Matrix.UnitaryGroup.Trace
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

/-!
# Matrices conjugate to unitary matrices and congruent to one modulo a large ideal

Let `K` be a number field and `γ` a square matrix over `K` of size `n` whose image `φ(γ)` under
every complex embedding `φ` is conjugate to a unitary matrix. Invariance of the trace under
conjugation gives `‖φ (tr (γ - 1))‖ ≤ 2n` for every `φ`. If
`tr (γ - 1)` lies in an integral ideal `I` of norm `N(I) > (2n)^[K:ℚ]`, then it is `0`: otherwise
its norm, the product of these conjugates, would be a nonzero multiple of `N(I)` of absolute value
at most `(2n)^[K:ℚ]` (`NumberField.RingOfIntegers.absNorm_le_pow_of_mem`). So `re tr φ(γ) = n`,
which forces `φ(γ) = 1` and `γ = 1`.

The congruence condition can be read adelically. If `x⁻¹ γ x ≡ 1` modulo `IÔ` for some
`x ∈ GL_n(𝔸_f)`, where `Ô` is the ring of integral finite adeles, then `tr (γ - 1)` is
`tr (x⁻¹ γ x - 1) ∈ IÔ`, and `K ∩ IÔ = I`.

For a CM field, the hypothesis holds for every `γ` with `γᴴ γ = 1`; see
`TauCeti.NumberTheory.NumberField.CMField.UnitaryCongruence`.

## Main results

* `NumberField.eq_one_of_trace_sub_one_mem_of_archimedean_unitary`: a matrix conjugate to a
  unitary matrix at every complex embedding is the identity if `tr (γ - 1)` lies in an ideal
  of norm `> (2n)^[K:ℚ]`.
* `NumberField.eq_one_of_conj_sub_one_mem_completedIdeal_of_archimedean_unitary`: the adelic
  form, for `x⁻¹ γ x ≡ 1` modulo `IÔ`.
-/

public section

open Module Matrix IsDedekindDomain
open scoped IsDedekindDomain.FiniteAdeleRing

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A ring homomorphism carries `tr (γ - 1)` to `tr (f(γ) - 1)`. -/
private theorem map_trace_sub_one {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (γ : Matrix n n R) : f (γ - 1).trace = (γ.map f - 1).trace := by
  simp [trace]

/-- Over a number field `K`, let `γ` be a square matrix of size `n` whose image under every
complex embedding is conjugate to a unitary matrix. If `tr (γ - 1)` is an element `t` of an
integral ideal `I` with `N(I) > (2n)^[K:ℚ]`, then `γ = 1`. -/
theorem eq_one_of_trace_sub_one_mem_of_archimedean_unitary {γ : Matrix n n K}
    (hγ : ∀ φ : K →+* ℂ, ∃ u : GL n ℂ,
      ((↑u⁻¹ : Matrix n n ℂ) * γ.map φ * (u : Matrix n n ℂ)) ∈ unitaryGroup n ℂ)
    {I : Ideal (𝓞 K)}
    (hI : (2 * Fintype.card n) ^ finrank ℚ K < Ideal.absNorm I) {t : 𝓞 K} (ht : t ∈ I)
    (htr : (t : K) = (γ - 1).trace) : γ = 1 := by
  have hφ (φ : K →+* ℂ) : φ t = (γ.map φ - 1).trace := by
    rw [htr, map_trace_sub_one]
  have hnorm (φ : K →+* ℂ) : ‖φ t‖ ≤ 2 * Fintype.card n := by
    obtain ⟨u, hu⟩ := hγ φ
    rw [hφ φ, trace_sub]
    simpa only [trace_sub, trace_units_conj'] using norm_trace_sub_one_le_of_mem_unitaryGroup hu
  have ht0 : t = 0 := by
    by_contra h0
    have hle := RingOfIntegers.absNorm_le_pow_of_mem ht h0 hnorm
    have hlt : ((2 * Fintype.card n : ℕ) : ℝ) ^ finrank ℚ K < Ideal.absNorm I := by
      exact_mod_cast hI
    push_cast at hlt
    exact hlt.not_ge hle
  let φ : K →+* ℂ := Classical.choice inferInstance
  obtain ⟨u, hu⟩ := hγ φ
  have htr' : (γ.map φ).trace = Fintype.card n := by
    have h0 : (0 : ℂ) = (γ.map φ).trace - Fintype.card n := by
      simpa [ht0, trace_sub] using hφ φ
    exact sub_eq_zero.mp h0.symm
  have hu1 := eq_one_of_re_trace_eq_card hu (by rw [trace_units_conj' u, htr']; simp)
  have h1 : γ.map φ = 1 := by
    simpa [← mul_assoc, ← Units.val_mul] using
      congrArg (fun A : Matrix n n ℂ ↦ (u : Matrix n n ℂ) * A * (↑u⁻¹ : Matrix n n ℂ)) hu1
  exact Matrix.map_injective φ.injective (h1.trans (Matrix.map_one _ φ.map_zero φ.map_one).symm)

/-- **Adelic form.** Over a number field `K`, let `γ` be a square matrix of size `n` whose image
under every complex embedding is conjugate to a unitary matrix, and `I` an integral ideal with
`N(I) > (2n)^[K:ℚ]`. If
`x⁻¹ γ x ≡ 1` modulo `IÔ` for some `x ∈ GL_n(𝔸_f)`, that is, every entry of `x⁻¹ γ x - 1` is an
element of the completion `IÔ` of `I` in the integral finite adeles, then `γ = 1`. -/
theorem eq_one_of_conj_sub_one_mem_completedIdeal_of_archimedean_unitary
    {γ : Matrix n n K} (hγ : ∀ φ : K →+* ℂ, ∃ u : GL n ℂ,
      ((↑u⁻¹ : Matrix n n ℂ) * γ.map φ * (u : Matrix n n ℂ)) ∈ unitaryGroup n ℂ)
    {I : Ideal (𝓞 K)} (hI : (2 * Fintype.card n) ^ finrank ℚ K < Ideal.absNorm I)
    (x : GL n 𝔸ᶠ[𝓞 K, K])
    (hx : ∀ i j, ∃ c ∈ FiniteAdeleRing.completedIdeal K I, (c : 𝔸ᶠ[𝓞 K, K]) =
      (((x⁻¹ : GL n 𝔸ᶠ[𝓞 K, K]) : Matrix n n 𝔸ᶠ[𝓞 K, K]) *
        γ.map (algebraMap K 𝔸ᶠ[𝓞 K, K]) * (x : Matrix n n 𝔸ᶠ[𝓞 K, K]) - 1) i j) :
    γ = 1 := by
  choose c hcI hc using hx
  have htr : ((∑ i, c i i : FiniteAdeleRing.integralAdeles (𝓞 K) K) : 𝔸ᶠ[𝓞 K, K]) =
      algebraMap K 𝔸ᶠ[𝓞 K, K] (γ - 1).trace := by
    rw [map_trace_sub_one, trace_sub, ← trace_units_conj' x (γ.map _), ← trace_sub]
    simp [trace, hc]
  obtain ⟨t, ht, htr'⟩ := FiniteAdeleRing.exists_mem_algebraMap_eq_of_mem_completedIdeal
    (fun h ↦ by simp [h] at hI) (sum_mem fun i _ ↦ hcI i i) htr
  exact eq_one_of_trace_sub_one_mem_of_archimedean_unitary hγ hI ht htr'

end NumberField
