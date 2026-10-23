/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Geometry.Manifold.ContMDiff.RestrictScalars

/-!
# Restricting the scalars of diffeomorphisms

Let `𝕜'` be a normed algebra over `𝕜`, and let the model spaces be normed spaces over both fields,
compatibly. A `C^n` diffeomorphism for the trivial models over `𝕜'` is, with the same underlying
equivalence, a `C^n` diffeomorphism for the trivial models over `𝕜`, since a `C^n` map over `𝕜'` is
`C^n` over `𝕜` (`ContMDiff.restrictScalars`). This file bundles that diffeomorphism and records its
compatibility with the identity, inverses, and composition.

The main example is a biholomorphism between complex manifolds modelled on `𝓘(ℂ, E)` and
`𝓘(ℂ, E')`, which is a diffeomorphism between the underlying real manifolds modelled on
`𝓘(ℝ, E)` and `𝓘(ℝ, E')`.

## Main definitions

* `Diffeomorph.restrictScalars`: a diffeomorphism over `𝕜'` regarded as a diffeomorphism over `𝕜`.

## Main results

* `Diffeomorph.coe_restrictScalars`: it has the same underlying map.
* `Diffeomorph.restrictScalars_refl`, `Diffeomorph.restrictScalars_symm`,
  `Diffeomorph.restrictScalars_trans`: restriction of scalars commutes with the identity, inverses,
  and composition.
-/

public section

open Function
open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  [IsScalarTower 𝕜 𝕜' E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedSpace 𝕜' E'] [IsScalarTower 𝕜 𝕜' E'] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {N : Type*} [TopologicalSpace N] [ChartedSpace E' N] {P : Type*}
  [TopologicalSpace P] [ChartedSpace F P] {n : WithTop ℕ∞}

namespace Diffeomorph

variable (𝕜)

/-- A `C^n` diffeomorphism for the trivial models over `𝕜'` is a `C^n` diffeomorphism for the
trivial models over the smaller field `𝕜`, with the same underlying equivalence. For instance, a
biholomorphism between complex manifolds is a diffeomorphism of the underlying real manifolds. -/
def restrictScalars (Φ : M ≃ₘ^n⟮𝓘(𝕜', E), 𝓘(𝕜', E')⟯ N) : M ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E')⟯ N where
  toEquiv := Φ.toEquiv
  contMDiff_toFun := Φ.contMDiff.restrictScalars 𝕜
  contMDiff_invFun := Φ.symm.contMDiff.restrictScalars 𝕜

variable (Φ : M ≃ₘ^n⟮𝓘(𝕜', E), 𝓘(𝕜', E')⟯ N)

/-- Restricting the scalars of a diffeomorphism does not change its underlying equivalence. -/
@[simp]
theorem restrictScalars_toEquiv : (Φ.restrictScalars 𝕜).toEquiv = Φ.toEquiv :=
  (rfl)

/-- Restricting the scalars of a diffeomorphism does not change its underlying map. -/
@[simp]
theorem coe_restrictScalars : ⇑(Φ.restrictScalars 𝕜) = Φ :=
  (rfl)

/-- Restricting the scalars of a diffeomorphism does not change its underlying homeomorphism. -/
@[simp]
theorem restrictScalars_toHomeomorph :
    (Φ.restrictScalars 𝕜).toHomeomorph = Φ.toHomeomorph :=
  (rfl)

/-- Restricting the scalars of diffeomorphisms is injective. -/
theorem restrictScalars_injective :
    Injective (restrictScalars 𝕜 : (M ≃ₘ^n⟮𝓘(𝕜', E), 𝓘(𝕜', E')⟯ N) → _) :=
  fun _ _ h ↦ ext fun x ↦ DFunLike.congr_fun h x

/-- Restricting the scalars of the identity diffeomorphism gives the identity diffeomorphism. -/
@[simp]
theorem restrictScalars_refl :
    (Diffeomorph.refl 𝓘(𝕜', E) M n).restrictScalars 𝕜 = Diffeomorph.refl 𝓘(𝕜, E) M n :=
  (rfl)

/-- Restricting scalars commutes with taking the inverse diffeomorphism. -/
@[simp]
theorem restrictScalars_symm : (Φ.restrictScalars 𝕜).symm = Φ.symm.restrictScalars 𝕜 :=
  (rfl)

/-- Restricting scalars commutes with the composition of diffeomorphisms. -/
@[simp]
theorem restrictScalars_trans (Ψ : N ≃ₘ^n⟮𝓘(𝕜', E'), 𝓘(𝕜', F)⟯ P) :
    (Φ.trans Ψ).restrictScalars 𝕜 = (Φ.restrictScalars 𝕜).trans (Ψ.restrictScalars 𝕜) :=
  (rfl)

end Diffeomorph
