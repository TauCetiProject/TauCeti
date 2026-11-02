/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic

/-!
# Postcomposing smooth isotopies with local diffeomorphisms

A smooth isotopy whose motion stays in a set `s`, postcomposed with a map which is a local
diffeomorphism at every point of `s` and a topological embedding on `s`, is again a smooth
isotopy. The map need not be defined smoothly, or injective, away from `s`, so this applies to the
inverse of a chart on a motion confined to the chart's target, and to radial contractions of a
model space.

This is the smooth counterpart of `TauCeti.Isotopy.postcomp`, where any topological embedding may
be applied; here the time slices must remain smooth embeddings, which
`TauCeti.isSmoothEmbedding_isLocalDiffeomorphAt_comp` provides.

## Main definitions

* `TauCeti.SmoothIsotopy.postcomp`: postcompose a smooth isotopy confined to `s` with a map which
  is a local diffeomorphism along `s` and a topological embedding on `s`.
-/

public section

noncomputable section

namespace TauCeti.SmoothIsotopy

open Manifold Set Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J n P]
  {f₀ f₁ : C^n⟮I, M; J, N⟯}

/-- Postcompose a smooth isotopy with a map `k` which is a local diffeomorphism at every point of
a set `s` containing the motion, and a topological embedding on `s`. The endpoints `g₀` and `g₁`
are supplied as bundled maps agreeing with `k ∘ f₀` and `k ∘ f₁`, since `k` itself need not be
smooth away from `s`. -/
def postcomp (K : SmoothIsotopy f₀ f₁) (k : N → P) {s : Set N} (hKs : ∀ p, K p ∈ s)
    (hk : ∀ y ∈ s, IsLocalDiffeomorphAt J J n k y) (hks : IsEmbedding (s.domRestrict k))
    (g₀ g₁ : C^n⟮I, M; J, P⟯) (hg₀ : ∀ x, g₀ x = k (f₀ x)) (hg₁ : ∀ x, g₁ x = k (f₁ x)) :
    SmoothIsotopy g₀ g₁ where
  toContMDiffMap := ⟨fun p => k (K p), by
    intro p
    exact (hk _ (hKs p)).contMDiffAt.comp p K.contMDiff.contMDiffAt⟩
  map_zero_left x := (congrArg k (K.apply_zero x)).trans (hg₀ x).symm
  map_one_left x := (congrArg k (K.apply_one x)).trans (hg₁ x).symm
  isSmoothEmbedding t :=
    isSmoothEmbedding_isLocalDiffeomorphAt_comp (f := fun x => K (t, x)) (k := k)
      (fun x => hk _ (hKs (t, x))) (range_subset_iff.2 fun x => hKs (t, x)) hks
      (K.isSmoothEmbedding t)

@[simp]
theorem postcomp_apply (K : SmoothIsotopy f₀ f₁) (k : N → P) {s : Set N} (hKs : ∀ p, K p ∈ s)
    (hk : ∀ y ∈ s, IsLocalDiffeomorphAt J J n k y) (hks : IsEmbedding (s.domRestrict k))
    (g₀ g₁ : C^n⟮I, M; J, P⟯) (hg₀ : ∀ x, g₀ x = k (f₀ x)) (hg₁ : ∀ x, g₁ x = k (f₁ x))
    (p : unitInterval × M) : K.postcomp k hKs hk hks g₀ g₁ hg₀ hg₁ p = k (K p) := (rfl)

end TauCeti.SmoothIsotopy
