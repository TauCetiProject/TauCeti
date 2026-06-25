/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel
public import TauCeti.Analysis.PositiveDefinite.KernelClosure
public import Mathlib.Data.NNReal.Basic

/-!
# Positive-definite functions on `[0, ∞) × V`

This file records the Berg--Christensen--Ressel semigroup-group positive-definiteness predicate
for functions on `ℝ≥0 × V`. For an additive group `V`, the intended involution is
`(t, v) ↦ (t, -v)`, so the finite quadratic forms use the entries
`F (tᵢ + tⱼ, vᵢ - vⱼ)`.

The generic positive-definite-kernel predicate already captures the finite Gram-matrix condition.
Here we name its BCR specialization for the kernel
`K p q = F (p.1 + q.1, p.2 - q.2)`, rather than installing a global negation `StarAddMonoid`
instance on every additive group `V`, which would conflict with Mathlib's ordinary star
conventions. The result is the named hypothesis needed for the BCR Laplace--Fourier
representation target in the `OneParameterSemigroups` roadmap.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Objects: the roadmap asks
for `IsSemigroupGroupPD` as the positive-definite predicate on `ℝ≥0 × V` with involution
`(t, a)⋆ = (t, -a)`.

## Main declarations

* `TauCeti.IsSemigroupGroupPD`: the BCR positive-definiteness predicate on `ℝ≥0 × V`.
* `TauCeti.isSemigroupGroupPD_def`: the definitional bridge to the associated
  positive-definite kernel.
* `TauCeti.isSemigroupGroupPD_iff`: the finite quadratic-form characterization.
* `TauCeti.IsSemigroupGroupPD.quadForm_two_nonneg`: the `2 × 2` BCR Hermitian sub-form is
  nonnegative.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F G : ℝ≥0 × V → ℂ}

/-- A function on `ℝ≥0 × V` is semigroup-group positive definite, in the
Berg--Christensen--Ressel sense, if all finite quadratic forms formed using the involution
`(t, v) ↦ (t, -v)` are nonnegative:
`∑ᵢⱼ cᵢ conj(cⱼ) F(tᵢ + tⱼ, vᵢ - vⱼ) ≥ 0`. -/
def IsSemigroupGroupPD (F : ℝ≥0 × V → ℂ) : Prop :=
  IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2)

/-- The definitional bridge from semigroup-group positive definiteness to the associated
positive-definite kernel. -/
theorem isSemigroupGroupPD_def :
    IsSemigroupGroupPD F ↔
      IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) :=
  Iff.rfl

/-- The kernel associated to a semigroup-group positive-definite function is positive definite. -/
theorem IsSemigroupGroupPD.isPositiveDefiniteKernel (hF : IsSemigroupGroupPD F) :
    IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2) :=
  isSemigroupGroupPD_def.mp hF

/-- Build a semigroup-group positive-definite function from the associated positive-definite
kernel. -/
theorem IsSemigroupGroupPD.of_isPositiveDefiniteKernel
    (hF : IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2)) :
    IsSemigroupGroupPD F :=
  isSemigroupGroupPD_def.mpr hF

/-- The finite quadratic-form characterization of semigroup-group positive definiteness. -/
theorem isSemigroupGroupPD_iff :
    IsSemigroupGroupPD F ↔
      (∀ p q : ℝ≥0 × V, conj (F (p.1 + q.1, p.2 - q.2))
        = F (q.1 + p.1, q.2 - p.2)) ∧
        ∀ {ι : Type*} [Fintype ι] (c : ι → ℂ) (p : ι → ℝ≥0 × V),
          0 ≤ ∑ i, ∑ j, c i * conj (c j) *
            F ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
  classical
  constructor
  · intro hF
    refine ⟨fun p q => isPositiveDefiniteKernel_conj_symm hF p q, ?_⟩
    intro ι _ c p
    have hpos := (isPositiveDefiniteKernel_iff.mp hF.isPositiveDefiniteKernel).2 p
      (fun i => conj (c i))
    simpa only [Complex.conj_conj] using hpos
  · rintro ⟨hsymm, hpos⟩
    exact IsSemigroupGroupPD.of_isPositiveDefiniteKernel <| isPositiveDefiniteKernel_iff.mpr
      ⟨hsymm, fun p x => by
        have h := hpos (fun i => conj (x i)) p
        simpa only [Complex.conj_conj] using h⟩

namespace IsSemigroupGroupPD

/-- The `2 × 2` BCR Hermitian sub-form at two points. -/
theorem quadForm_two_nonneg (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (p.1 + p.1, p.2 - p.2)
      + c₀ * conj c₁ * F (p.1 + q.1, p.2 - q.2)
      + c₁ * conj c₀ * F (q.1 + p.1, q.2 - p.2)
      + c₁ * conj c₁ * F (q.1 + q.1, q.2 - q.2) := by
  have h := (isSemigroupGroupPD_iff.mp hF).2 ![c₀, c₁] ![p, q]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact le_of_le_of_eq h (by ring)

end IsSemigroupGroupPD

end TauCeti
