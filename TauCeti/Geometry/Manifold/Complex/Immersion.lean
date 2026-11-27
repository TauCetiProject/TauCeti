/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Holomorphic immersion normal forms and regularity promotion of complex embeddings

Because a holomorphic map on an open subset of a finite-dimensional boundaryless complex manifold is
complex analytic (`MDifferentiableOn.contMDiffOn`, `MDifferentiable.contMDiff`), at any point of an
open holomorphy domain between `C¹` complex manifolds a map has a `C^n` (`1 ≤ n`, including `n = ∞`
and `n = ω`) immersion normal form if and only if its complex differential `mfderiv I J f x` is
injective (`TauCeti.isImmersionAt_iff_injective_mfderiv_of_mdifferentiableOn`), and globally an
`MDifferentiable` map with everywhere injective differential is a `C^n` immersion for every `n`
(`MDifferentiable.isImmersion_of_injective_mfderiv`). If it is also a topological embedding, it
promotes to a `C^n` smooth embedding
(`MDifferentiable.isSmoothEmbedding_of_isEmbedding_of_injective_mfderiv`,
`TauCeti.SmoothEmbedding.ofMDifferentiable`), and any complex `SmoothEmbedding` of nonzero
regularity `m₀ ≠ 0` promotes to arbitrary regularity `n : ℕ∞ω` via
`TauCeti.SmoothEmbedding.ofNeZero`.

This file is the immersion and embedding counterpart of
`TauCeti.Geometry.Manifold.Complex.Submersion`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed., North-Holland,
  1990, Section 2.1.
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.1.
-/

public noncomputable section

open Function Topology Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  [TopologicalSpace G] {J : ModelWithCorners ℂ F G} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]

section C1

variable [IsManifold I 1 M] [IsManifold J 1 N]

/-- At a point of an open holomorphy domain between `C¹` complex manifolds, the existence of a
`C^n` (`1 ≤ n`, including `n = ∞` and `n = ω`) immersion normal form is equivalent to injectivity of
the complex differential. -/
theorem isImmersionAt_iff_injective_mfderiv_of_mdifferentiableOn
    {f : M → N} {U : Set M} {x : M} {n : ℕ∞ω}
    (hf : MDifferentiableOn I J f U) (hU : IsOpen U) (hx : x ∈ U) (hn : 1 ≤ n) :
    IsImmersionAt I J n f x ↔ Injective (mfderiv I J f x) := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  have : IsManifold I n M := IsManifold.of_ne_zero n one_ne_zero inferInstance
  have : IsManifold J n N := IsManifold.of_ne_zero n one_ne_zero inferInstance
  exact (hf.contMDiffOn hU).isImmersionAt_iff_injective_mfderiv hU hx hn

/-- A holomorphic (`MDifferentiable`) map between `C¹` complex manifolds with injective complex
differential everywhere is a `C^n` immersion for every `n : ℕ∞ω`, including `n = ∞` and `n = ω`. -/
theorem _root_.MDifferentiable.isImmersion_of_injective_mfderiv {f : M → N}
    (hf : MDifferentiable I J f) (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    IsImmersion I J n f := by
  have : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  have : IsManifold I (max n 1) M := IsManifold.of_ne_zero (max n 1) one_ne_zero inferInstance
  have : IsManifold J (max n 1) N := IsManifold.of_ne_zero (max n 1) one_ne_zero inferInstance
  exact ((hf.contMDiff (n := max n 1)).isImmersion_of_injective_mfderiv (le_max_right n 1)
    hdf).of_le (le_max_left n 1)

/-- A holomorphic topological embedding between `C¹` complex manifolds with injective complex
differential everywhere is a `C^n` smooth embedding for every `n : ℕ∞ω` (`∞` and `ω` included). -/
theorem _root_.MDifferentiable.isSmoothEmbedding_of_isEmbedding_of_injective_mfderiv {f : M → N}
    (hf : MDifferentiable I J f) (hemb : IsEmbedding f)
    (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω) :
    IsSmoothEmbedding I J n f :=
  ⟨hf.isImmersion_of_injective_mfderiv hdf n, hemb⟩

namespace SmoothEmbedding

variable (f : M → N) (hf : MDifferentiable I J f) (hemb : IsEmbedding f)
  (hdf : ∀ x, Injective (mfderiv I J f x)) (n : ℕ∞ω)

/-- Bundle a holomorphic (`MDifferentiable`) topological embedding with injective complex
differential into a `SmoothEmbedding I J n M N` of arbitrary smoothness order `n : ℕ∞ω` (in
particular `n = ∞` or `n = ω`). -/
def ofMDifferentiable : SmoothEmbedding I J n M N :=
  haveI : IsManifold I n M := IsManifold.of_ne_zero n one_ne_zero inferInstance
  haveI : IsManifold J n N := IsManifold.of_ne_zero n one_ne_zero inferInstance
  haveI : CompleteSpace F := FiniteDimensional.completeSpace ℂ F
  ofIsSmoothEmbedding f (hf.isSmoothEmbedding_of_isEmbedding_of_injective_mfderiv hemb hdf n)

@[simp] theorem coe_ofMDifferentiable :
    ⇑(ofMDifferentiable (I := I) (J := J) f hf hemb hdf n) = f := by
  rw [ofMDifferentiable.eq_def, coe_ofIsSmoothEmbedding]

@[simp] theorem ofMDifferentiable_apply (x : M) :
    ofMDifferentiable (I := I) (J := J) f hf hemb hdf n x = f x := by
  rw [ofMDifferentiable.eq_def, ofIsSmoothEmbedding_apply]

end SmoothEmbedding

end C1

namespace SmoothEmbedding

variable {m₀ : ℕ∞ω} [IsManifold I m₀ M] [IsManifold J m₀ N]
  (f : SmoothEmbedding I J m₀ M N) (hm₀ : m₀ ≠ 0) (n : ℕ∞ω)

/-- Promote a positive-regularity (`m₀ ≠ 0`) complex embedding to any smoothness order `n : ℕ∞ω`,
including `n = ∞` and complex-analytic order `n = ω`, matching `IsManifold.of_ne_zero`. -/
def ofNeZero : SmoothEmbedding I J n M N :=
  letI : IsManifold I 1 M := IsManifold.of_ne_zero 1 hm₀ inferInstance
  letI : IsManifold J 1 N := IsManifold.of_ne_zero 1 hm₀ inferInstance
  ofMDifferentiable f (f.contMDiff.mdifferentiable hm₀) f.isEmbedding
    (f.isImmersion.mfderiv_injective hm₀) n

@[simp] theorem coe_ofNeZero : ⇑(f.ofNeZero hm₀ n) = f := by
  simp only [ofNeZero, ofMDifferentiable, coe_ofIsSmoothEmbedding]

@[simp] theorem ofNeZero_apply (x : M) : f.ofNeZero hm₀ n x = f x :=
  congrFun (f.coe_ofNeZero hm₀ n) x

end SmoothEmbedding

end TauCeti
