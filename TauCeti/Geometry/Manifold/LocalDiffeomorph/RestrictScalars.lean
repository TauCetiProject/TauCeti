/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

-- Access the body of `IsLocalDiffeomorphAt` to destructure and rebuild its witness.
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Restricting the scalars of local diffeomorphisms

Let `𝕜'` be a normed algebra over `𝕜`, and let the model spaces be normed spaces over both fields,
compatibly. A partial `C^n` diffeomorphism for the trivial models over `𝕜'` is, with the same
underlying partial equivalence, a partial `C^n` diffeomorphism for the trivial models over `𝕜`.
Consequently a local `C^n` diffeomorphism over `𝕜'` (at a point, on a set, or globally) is a local
`C^n` diffeomorphism over `𝕜`.

The main example is a local biholomorphism between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`, which is a local diffeomorphism between the underlying real manifolds modelled on
`𝓘(ℝ, E)` and `𝓘(ℝ, E')`.

## Main definitions

* `PartialDiffeomorph.restrictScalars`: a partial diffeomorphism over `𝕜'` regarded as a partial
  diffeomorphism over `𝕜`.

## Main results

* `IsLocalDiffeomorphAt.restrictScalars`, `IsLocalDiffeomorphOn.restrictScalars`,
  `IsLocalDiffeomorph.restrictScalars`: a local diffeomorphism over `𝕜'` is a local diffeomorphism
  over `𝕜`.
-/

public section

open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E'] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] {n : WithTop ℕ∞}

variable (𝕜)

namespace PartialDiffeomorph

/-- A partial `C^n` diffeomorphism for the trivial models over `𝕜'` is a partial `C^n`
diffeomorphism for the trivial models over the smaller field `𝕜`, with the same underlying partial
equivalence. -/
def restrictScalars (Φ : PartialDiffeomorph 𝓘(𝕜', E) 𝓘(𝕜', E') M N n) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') M N n where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.restrictScalars 𝕜
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.restrictScalars 𝕜

variable (Φ : PartialDiffeomorph 𝓘(𝕜', E) 𝓘(𝕜', E') M N n)

/-- Restricting the scalars of a partial diffeomorphism does not change its underlying partial
equivalence. -/
@[simp]
theorem restrictScalars_toPartialEquiv :
    (Φ.restrictScalars 𝕜).toPartialEquiv = Φ.toPartialEquiv :=
  (rfl)

/-- Restricting scalars commutes with taking the inverse partial diffeomorphism. -/
@[simp]
theorem restrictScalars_symm : (Φ.restrictScalars 𝕜).symm = Φ.symm.restrictScalars 𝕜 :=
  (rfl)

end PartialDiffeomorph

variable {f : M → N} {s : Set M} {x : M}

/-- A local `C^n` diffeomorphism at a point for the trivial models over `𝕜'` is a local `C^n`
diffeomorphism at that point for the trivial models over the smaller field `𝕜`. -/
theorem IsLocalDiffeomorphAt.restrictScalars
    (h : IsLocalDiffeomorphAt 𝓘(𝕜', E) 𝓘(𝕜', E') n f x) :
    IsLocalDiffeomorphAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x := by
  obtain ⟨Φ, hx, hf⟩ := h
  exact ⟨Φ.restrictScalars 𝕜, hx, hf⟩

/-- A local `C^n` diffeomorphism on a set for the trivial models over `𝕜'` is a local `C^n`
diffeomorphism on that set for the trivial models over the smaller field `𝕜`. -/
theorem IsLocalDiffeomorphOn.restrictScalars
    (h : IsLocalDiffeomorphOn 𝓘(𝕜', E) 𝓘(𝕜', E') n f s) :
    IsLocalDiffeomorphOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s :=
  fun x ↦ (h x).restrictScalars 𝕜

/-- A local `C^n` diffeomorphism for the trivial models over `𝕜'` is a local `C^n` diffeomorphism
for the trivial models over the smaller field `𝕜`. For instance, a local biholomorphism between
complex manifolds is a local diffeomorphism of the underlying real manifolds. -/
theorem IsLocalDiffeomorph.restrictScalars (h : IsLocalDiffeomorph 𝓘(𝕜', E) 𝓘(𝕜', E') n f) :
    IsLocalDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E') n f :=
  fun x ↦ (h x).restrictScalars 𝕜
