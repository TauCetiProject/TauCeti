/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Symplectic.Hamiltonian.Integrable

/-!
# Completeness of Hamiltonian vector fields with proper first integrals

Let `σ` be a nondegenerate two-form on a finite-dimensional boundaryless manifold `M`, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. A first integral `g` of a `C²`
Hamiltonian `f` is constant along the whole maximal integral curve of the Hamiltonian vector field
`X_f` through each point.

Consequently, if a family `G : M → (ι → ℝ)` of first integrals of `f` is a proper map, every
maximal integral curve of `X_f` stays in a compact fibre of `G`, and the extension criterion for
integral curves makes `X_f` complete. No regularity of the fibres is needed, so critical levels
are allowed. Two cases are singled out: a proper `C²` Hamiltonian has a complete Hamiltonian
vector field, by conservation of energy; and if a completely integrable system
`F : M → (ι → ℝ)` is a proper map, the Hamiltonian vector field of each of its integrals `F_i` is
complete. The last statement is the completeness input of the Liouville–Arnold theorem: the
Hamiltonian flows of the integrals of a proper integrable system are defined for all time. It
applies to the harmonic oscillator on the plane.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `IsFirstIntegral.apply_maximalIntegralCurve`: conservation of a first integral along a maximal
  integral curve of a Hamiltonian vector field.
* `IsNondegenerate.isCompleteVectorField_hamiltonianVectorField_of_isProperMap`: a Hamiltonian
  vector field with a proper family of first integrals is complete.
* `IsNondegenerate.isCompleteVectorField_hamiltonianVectorField_of_isProperMap_self`: the
  Hamiltonian vector field of a proper Hamiltonian is complete.
* `IsIntegrableSystem.isCompleteVectorField_hamiltonianVectorField_of_isProperMap`: the
  Hamiltonian vector fields of the integrals of a proper integrable system are complete.

In the namespace `TauCeti`:

* `isCompleteVectorField_hamiltonianVectorField_harmonicOscillator`: the harmonic oscillator
  flow is complete.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 49.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 9.16 and
  Lemma 9.19.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} {f g : M → ℝ} {x : M} {t : ℝ}

/-- **Conservation of first integrals along maximal integral curves.** A differentiable first
integral `g` of a `C²` Hamiltonian `f` takes the same value at every point of the maximal integral
curve of the Hamiltonian vector field of `f` through `x` as at `x`. -/
theorem IsFirstIntegral.apply_maximalIntegralCurve (hg : σ.IsFirstIntegral f g)
    (hσ : σ.IsNondegenerate) (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg' : MDifferentiable I 𝓘(ℝ) g)
    (ht : t ∈ maximalIntegralCurveInterval (σ.hamiltonianVectorField f) x) :
    g (maximalIntegralCurve (σ.hamiltonianVectorField f) x t) = g x := by
  have hv := hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp)
    (by rwa [one_add_one_eq_two])
  have h0 := zero_mem_maximalIntegralCurveInterval (x := x) hv.contMDiffAt
  rw [hg.apply_eq_of_isMIntegralCurveOn hσ isOpen_maximalIntegralCurveInterval
    isPreconnected_maximalIntegralCurveInterval (isMIntegralCurveOn_maximalIntegralCurve hv)
    (fun _ _ ↦ hg' _) h0 ht, maximalIntegralCurve_zero h0]

namespace IsNondegenerate

variable (hσ : σ.IsNondegenerate)
include hσ

/-- **A Hamiltonian vector field with a proper family of first integrals is complete.** If the
functions `G_i = G (·) i` are differentiable first integrals of a `C²` Hamiltonian `f` and
`G : M → (ι → ℝ)` is a proper map, then every maximal integral curve of the Hamiltonian vector
field of `f` stays in a compact fibre of `G`, so the field is complete. -/
theorem isCompleteVectorField_hamiltonianVectorField_of_isProperMap (hf : ContMDiff I 𝓘(ℝ) 2 f)
    {ι : Type*} {G : M → ι → ℝ} (hG : IsProperMap G) (hGf : ∀ i, σ.IsFirstIntegral f (G · i))
    (hG' : ∀ i, MDifferentiable I 𝓘(ℝ) (G · i)) :
    IsCompleteVectorField (σ.hamiltonianVectorField f) :=
  isCompleteVectorField_of_isProperMap
    (hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by rwa [one_add_one_eq_two])) hG
    fun _ _ ht ↦ funext fun i ↦ (hGf i).apply_maximalIntegralCurve hσ hf (hG' i) ht

/-- **A proper Hamiltonian has a complete Hamiltonian vector field.** By conservation of energy,
each maximal integral curve of the Hamiltonian vector field of a proper `C²` Hamiltonian `f`
stays in a compact level set of `f`. -/
theorem isCompleteVectorField_hamiltonianVectorField_of_isProperMap_self
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hfp : IsProperMap f) :
    IsCompleteVectorField (σ.hamiltonianVectorField f) :=
  isCompleteVectorField_of_isProperMap
    (hσ.contMDiff_hamiltonianVectorField (n := 1) (by simp) (by rwa [one_add_one_eq_two])) hfp
    fun _ _ ht ↦ (isFirstIntegral_self f).apply_maximalIntegralCurve hσ hf
      (hf.mdifferentiable (by simp)) ht

end IsNondegenerate

/-- **The Hamiltonian flows of a proper integrable system are complete.** If a completely
integrable system `F : M → (ι → ℝ)` is a proper map, then the Hamiltonian vector field of each
integral `F_i` is complete: its integral curves stay in the compact common levels of `F`, which
may be critical. -/
theorem IsIntegrableSystem.isCompleteVectorField_hamiltonianVectorField_of_isProperMap
    {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (h : σ.IsIntegrableSystem F) (hσ : σ.IsNondegenerate)
    (hF : IsProperMap F) (i : ι) : IsCompleteVectorField (σ.hamiltonianVectorField (F · i)) :=
  have hFi (j : ι) : ContMDiff I 𝓘(ℝ) ∞ (F · j) := contMDiff_pi_module_iff.1 h.contMDiff j
  hσ.isCompleteVectorField_hamiltonianVectorField_of_isProperMap ((hFi i).of_le (by simp)) hF
    (h.isFirstIntegral i) fun j ↦ (hFi j).mdifferentiable (by simp)

end SmoothTwoForm

/-- **The harmonic oscillator flow is complete.** The Hamiltonian vector field of the energy
`(q² + p²) / 2` on the plane, with its standard symplectic form, is complete, because the energy
is a proper integrable system (`TauCeti.isProperMap_harmonicOscillator`). -/
theorem isCompleteVectorField_hamiltonianVectorField_harmonicOscillator :
    IsCompleteVectorField ((stdSymplecticForm (V := ℝ)).constSmooth.hamiltonianVectorField
      fun z : ℝ × ℝ ↦ (z.1 ^ 2 + z.2 ^ 2) / 2) :=
  isIntegrableSystem_harmonicOscillator.isCompleteVectorField_hamiltonianVectorField_of_isProperMap
    (SymplecticForm.isNondegenerate_constSmooth _) isProperMap_harmonicOscillator 0

end TauCeti
