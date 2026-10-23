/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp

/-!
# Continuity of composition of diffeomorphisms

For compact source manifolds with locally compact models, composition of `C^n` diffeomorphisms
is jointly continuous for the weak Whitney topology, since the forgetful map to `C^n` maps is an
embedding and composition of `C^n` maps is continuous
(`ContMDiffMap.continuous_comp_manifoldWeakWhitney`). In particular the self-diffeomorphisms of
a compact manifold form a topological monoid. Continuity of inversion is a separate matter, as
it needs an inverse-function estimate.

## Main results

* `Diffeomorph.continuous_trans`: composition of diffeomorphisms is jointly continuous.
* `Diffeomorph.continuousMul`: the self-diffeomorphisms of a compact manifold have jointly
  continuous multiplication; it is a scoped instance in `TauCeti.DiffeomorphWeakWhitney`.
-/

public section

open scoped Manifold ContDiff TauCeti.ManifoldWeakWhitney TauCeti.DiffeomorphWeakWhitney

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
  {n : ℕ∞ω}

/-- The underlying `C^n` map of a composite of diffeomorphisms is the composite of the underlying
`C^n` maps. -/
@[simp]
theorem toContMDiffMap_trans (f : M ≃ₘ^n⟮I, J⟯ N) (g : N ≃ₘ^n⟮J, I'⟯ P) :
    (f.trans g).toContMDiffMap = g.toContMDiffMap.comp f.toContMDiffMap := (rfl)

variable [CompactSpace M] [CompactSpace N] [LocallyCompactSpace E] [LocallyCompactSpace F]
  [IsManifold I n M] [IsManifold J n N] [IsManifold I' n P]

/-- Composition of diffeomorphisms is jointly continuous for the weak Whitney topology. -/
theorem continuous_trans :
    Continuous fun p : (M ≃ₘ^n⟮I, J⟯ N) × (N ≃ₘ^n⟮J, I'⟯ P) ↦ p.1.trans p.2 := by
  refine continuous_weakWhitney_iff.mpr ?_
  simp only [toContMDiffMap_trans]
  exact ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp
    ((continuous_toContMDiffMap.comp continuous_snd).prodMk
      (continuous_toContMDiffMap.comp continuous_fst))

/-- Multiplication of self-diffeomorphisms of a compact manifold is jointly continuous for the
weak Whitney topology. -/
theorem continuousMul : ContinuousMul (M ≃ₘ^n⟮I, I⟯ M) :=
  ⟨continuous_trans.comp continuous_swap⟩

scoped[TauCeti.DiffeomorphWeakWhitney] attribute [instance] Diffeomorph.continuousMul

end Diffeomorph
