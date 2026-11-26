/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Manifold.Distribution.Levi.Bundle

/-!
# The Levi form of a contact structure as a bundle isomorphism

Let `ξ` be a contact structure (`TauCeti.IsContactDistribution`) on a nonempty manifold `M`, a
hyperplane field of rank `dim M - 1` with nondegenerate Levi form. Its contact line `L = TM ⧸ ξ` is
a line bundle (`TauCeti.IsContMDiffDistribution.quotientPrebundle`, with `r = 1`). This file shows
that the Levi form identifies `ξ` with `Hom(ξ, L)` as smooth vector bundles: the map of total
spaces `(x, u) ↦ (x, L_ξ x (u, ·))` is a bundle diffeomorphism
(`TauCeti.IsContactDistribution.exists_bundleDiffeomorph_distributionLeviFormL`). It is the case
`r = 1` of `TauCeti.exists_bundleDiffeomorph_distributionLeviFormL_iff`.

## Main results

* `TauCeti.IsContactDistribution.exists_bundleDiffeomorph_distributionLeviFormL`: for a `C^m`
  contact structure `ξ` and `n + 1 ≤ m`, the Levi form is a `C^n` bundle isomorphism
  `ξ ≅ Hom(ξ, TM ⧸ ξ)`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge Studies in Advanced Mathematics 109
  (2008), Section 1.1 (contact structures as maximally non-integrable hyperplane fields).
-/

public section

noncomputable section

open Function Bundle Module
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M] {m n : ℕ∞ω} {D : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- **The Levi form of a contact structure is a bundle isomorphism `ξ ≅ Hom(ξ, L)`.** For a `C^m`
contact structure `ξ` on a nonempty manifold and `n + 1 ≤ m`, the map of total spaces
`ξ → Hom(ξ, TM ⧸ ξ)`, `(x, u) ↦ (x, L_ξ x (u, ·))`, is a `C^n` diffeomorphism, that is a `C^n`
isomorphism from `ξ` onto the Hom bundle into its contact line `L = TM ⧸ ξ`. -/
theorem IsContactDistribution.exists_bundleDiffeomorph_distributionLeviFormL [Nonempty M]
    [IsManifold I (n + 1 + 1) M] (hD : IsContactDistribution I m D) (hnm : n + 1 ≤ m) :
    letI := (hD.isContMDiffDistribution.of_le hnm).fiberBundle
    letI := (hD.isContMDiffDistribution.of_le hnm).vectorBundle
    letI := ((hD.isContMDiffDistribution.of_le hnm).quotientPrebundle
      hD.finrank_sub_one_add_one).totalSpaceTopology
    letI := ((hD.isContMDiffDistribution.of_le hnm).quotientPrebundle
      hD.finrank_sub_one_add_one).toFiberBundle
    letI := ((hD.isContMDiffDistribution.of_le hnm).quotientPrebundle
      hD.finrank_sub_one_add_one).toVectorBundle
    ∃ Φ : TotalSpace (Fin (finrank ℝ E - 1) → ℝ) (fun x ↦ D x) ≃ₘ^n⟮
        I.prod 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ),
        I.prod 𝓘(ℝ, (Fin (finrank ℝ E - 1) → ℝ) →L[ℝ] (Fin 1 → ℝ))⟯
        TotalSpace ((Fin (finrank ℝ E - 1) → ℝ) →L[ℝ] (Fin 1 → ℝ))
          (fun x ↦ D x →L[ℝ] TangentSpace I x ⧸ D x),
      ⇑Φ = fun p ↦ TotalSpace.mk' ((Fin (finrank ℝ E - 1) → ℝ) →L[ℝ] (Fin 1 → ℝ))
        (E := fun x ↦ D x →L[ℝ] TangentSpace I x ⧸ D x) p.proj
        (distributionLeviFormL D p.proj p.snd) :=
  (exists_bundleDiffeomorph_distributionLeviFormL_iff (hD.isContMDiffDistribution.of_le hnm)
    hD.finrank_sub_one_add_one).2 hD.bijective_distributionLeviForm

end TauCeti
