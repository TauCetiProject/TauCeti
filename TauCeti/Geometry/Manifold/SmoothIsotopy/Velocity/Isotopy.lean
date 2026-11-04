/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Basic
public import TauCeti.Geometry.Manifold.SmoothIsotopy.Velocity.Basic

/-!
# Ambient velocity on a compact part of a smooth isotopy

A smooth isotopy of a possibly noncompact boundaryless manifold has a compactly supported
ambient velocity field on each compact subset of its source. Run the isotopy over the real
line using `Real.smoothTransition`, so the resulting motion is stationary before time zero
and after time one. Every point of the chosen compact subset then follows an integral curve
of a single jointly smooth time-dependent vector field with support in a fixed compact set.

For an open-disc isotopy, choose a closed ball as the compact subset. This supplies the
velocity field used to extend the motion of that closed disc to an ambient isotopy; no
manifold structure on the closed disc, or compactness of the open source, is required.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §1,
  Theorems 1.3--1.4 and their proof.
-/

public section

open Set Manifold Bundle
open scoped Manifold ContDiff

namespace TauCeti

variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [I.Boundaryless] [J.Boundaryless] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]

/-- On any compact subset of its boundaryless source, a smooth isotopy run at the time
`Real.smoothTransition t` moves each point along a compactly supported ambient vector field.
The field is jointly `C^m` in time and space for `1 ≤ m` and `m + 1 ≤ n`. -/
theorem SmoothIsotopy.exists_ambientVelocityField {n m : ℕ∞} [IsManifold I n M]
    {f₀ f₁ : C^n⟮I, M; J, N⟯}
    (F : SmoothIsotopy f₀ f₁) {A : Set M} (hA : IsCompact A) (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    ∃ X : ℝ → (y : N) → TangentSpace J y, ∃ K : Set N, IsCompact K ∧
      (∀ t, ∀ y ∉ K, X t y = 0) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod J) J.tangent m
        (fun p : ℝ × N => (⟨p.2, X p.1 p.2⟩ : TangentBundle J N)) ∧
      ∀ t, ∀ x ∈ A, HasMFDerivAt 𝓘(ℝ, ℝ) J
        (fun s => F (⟨Real.smoothTransition s, Real.smoothTransition.nonneg _,
          Real.smoothTransition.le_one _⟩, x)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (F (⟨Real.smoothTransition t,
          Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩, x)))) := by
  let σ : ℝ → unitInterval := fun s =>
    ⟨Real.smoothTransition s, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hσ : ContMDiff 𝓘(ℝ, ℝ) (𝓡∂ 1) n σ :=
    contMDiff_id.smoothTransition (by exact_mod_cast le_top)
  have hσ₀ : ∀ t ≤ 0, σ t = σ 0 := fun t ht => Subtype.ext <| by
    simp only [σ, Real.smoothTransition.zero_of_nonpos ht, Real.smoothTransition.zero]
  have hσ₁ : ∀ t, 1 ≤ t → σ t = σ 1 := fun t ht => Subtype.ext <| by
    simp only [σ, Real.smoothTransition.one_of_one_le ht, Real.smoothTransition.one]
  exact TauCeti.exists_ambientVelocityField (G := fun q => F (σ q.1, q.2))
    (F.contMDiff.comp ((hσ.comp contMDiff_fst).prodMk contMDiff_snd))
    (fun t => F.isSmoothEmbedding (σ t)) hA (fun t ht x _ => by rw [hσ₀ t ht])
    (fun t ht x _ => by rw [hσ₁ t ht]) hm hmn

end TauCeti
