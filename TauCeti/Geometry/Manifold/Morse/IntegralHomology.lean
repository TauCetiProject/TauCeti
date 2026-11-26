/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Perfect
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
import TauCeti.AlgebraicTopology.Singular.Coefficients.PrimeField
import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# Integral homology from a Morse function with even indices

Let `M` be a compact boundaryless manifold carrying a Morse function `f` all of whose critical
points have even index. By the lacunary principle `f` is perfect over every division ring, so the
odd Betti numbers of `M` vanish over every field
(`TauCeti.IsMorse.bettiNumber_eq_zero_of_odd`), in particular over every prime field `𝔽_p`. This
file deduces the integral statement:

* the integral homology `Hⱼ(M; ℤ)` vanishes in odd degrees
  (`TauCeti.IsMorse.isZero_singularHomology_int_of_odd`);
* it is a free abelian group of finite rank in every degree
  (`TauCeti.IsMorse.free_singularHomology_int`, `TauCeti.IsMorse.finite_singularHomology_int`).

The argument uses no cell structure beyond finiteness. A compact manifold carrying a Morse function
has finite CW type (`TauCeti.IsMorse.finiteCWType`), so its integral homology is finitely generated
(`TauCeti.finite_singularHomology_int_of_finiteCWType`). In the coefficient long exact sequence of
`0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/p ⟶ 0`, vanishing of `Hⱼ₊₁(M; 𝔽_p)` for odd `j + 1` makes multiplication by `p`
injective on `Hⱼ(M; ℤ)`, and vanishing of `Hⱼ(M; 𝔽_p)` for odd `j` makes it onto. A finitely
generated abelian group on which every prime acts injectively is free, and one on which every prime
acts surjectively is zero (`TopCat.isTorsionFree_singularHomology_of_forall_isZero_zmod`,
`TopCat.isZero_singularHomology_of_forall_isZero_zmod`).

## Main results

* `TauCeti.IsMorse.finite_singularHomology_int`: the integral homology of a compact manifold
  carrying a Morse function is finitely generated.
* `TauCeti.IsMorse.isZero_singularHomology_int_of_odd`: if all indices are even, the odd-degree
  integral homology vanishes.
* `TauCeti.IsMorse.free_singularHomology_int`: if all indices are even, the integral homology is
  free in every degree.

## References

* R. Bott, *Lectures on Morse theory, old and new*, Bull. Amer. Math. Soc. (N.S.) 7 (1982),
  331–358, §1 (the lacunary principle).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.A (the universal coefficient theorem and change of coefficients).
-/

public section

open CategoryTheory Limits AlgebraicTopology Module
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E H : Type*} {M : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}

/-- **Integral homology is finitely generated in the presence of a Morse function.** A compact
boundaryless manifold `M` carrying a Morse function has finitely generated integral homology
`Hⱼ(M; ℤ)` in every degree. -/
theorem IsMorse.finite_singularHomology_int (hf : IsMorse I f) (j : ℕ) :
    Module.Finite ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  have := hf.finiteCWType
  exact finite_singularHomology_int_of_finiteCWType M j

/-- For a Morse function with only even indices on a compact boundaryless manifold `M`, the
homology of `M` with coefficients in the integer module `ℤ/p`, for a prime `p`, vanishes in odd
degrees. -/
private theorem IsMorse.isZero_singularHomology_zmod_of_odd (hf : IsMorse I f)
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x)) {p : ℕ} (hp : p.Prime)
    {j : ℕ} (hj : Odd j) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} (ZMod p)))).obj (TopCat.of M)) := by
  have : Fact p.Prime := ⟨hp⟩
  -- the homology over the field `𝔽_p` is finite-dimensional of dimension the odd Betti number `0`
  have := (hf.isPerfectMorse_of_even (k := ULift.{u} (ZMod p)) heven).finite_singularHomology j
  have h := hf.bettiNumber_eq_zero_of_odd (k := ULift.{u} (ZMod p)) heven hj
  rw [bettiNumber_def, finrank_zero_iff] at h
  exact ((TopCat.of M).isZero_singularHomology_zmod_iff_of_ringEquiv p ULift.ringEquiv j).2
    (ModuleCat.isZero_of_subsingleton _)

/-- **Odd integral homology vanishes for a Morse function with only even indices.** On a compact
boundaryless manifold `M` carrying a Morse function all of whose critical points have even index,
`Hⱼ(M; ℤ) = 0` for every odd `j`. -/
theorem IsMorse.isZero_singularHomology_int_of_odd (hf : IsMorse I f)
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x)) {j : ℕ} (hj : Odd j) :
    IsZero (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  have := hf.finite_singularHomology_int j
  exact (TopCat.of M).isZero_singularHomology_of_forall_isZero_zmod j fun _ hp ↦
    hf.isZero_singularHomology_zmod_of_odd heven hp hj

/-- **Integral homology is free for a Morse function with only even indices.** On a compact
boundaryless manifold `M` carrying a Morse function all of whose critical points have even index,
`Hⱼ(M; ℤ)` is a free abelian group in every degree: it is zero in odd degrees, and in even degrees
it is finitely generated and torsion-free. -/
theorem IsMorse.free_singularHomology_int (hf : IsMorse I f)
    (heven : ∀ x ∈ criticalPoints I f, Even (manifoldMorseIndex I f x)) (j : ℕ) :
    Module.Free ℤ (((singularHomologyFunctor (ModuleCat.{u} ℤ) j).obj
      (ModuleCat.of ℤ (ULift.{u} ℤ))).obj (TopCat.of M)) := by
  have := hf.finite_singularHomology_int j
  rcases Nat.even_or_odd j with hj | hj
  · -- in even degree `j`, the prime field homology vanishes in the odd degree `j + 1`
    have := (TopCat.of M).isTorsionFree_singularHomology_of_forall_isZero_zmod j fun _ hp ↦
      hf.isZero_singularHomology_zmod_of_odd heven hp hj.add_one
    infer_instance
  · have := ModuleCat.isZero_iff_subsingleton.1 (hf.isZero_singularHomology_int_of_odd heven hj)
    infer_instance

end TauCeti
