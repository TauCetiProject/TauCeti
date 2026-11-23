/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.DegreeRaising
public import TauCeti.AlgebraicTopology.Sphere.Stiefel.DoubleLoop

/-!
# The degree-raising map on the double loops swept by orthonormal two-frames

Let `p` be a point of the unit sphere `Sⁿ` of a real inner product space `E`, and let
`Σ_p = V₂(p^⊥)` be the Stiefel manifold of orthonormal two-frames of the tangent space `p^⊥`.
Barraud–Damian–Humilière–Oancea (Example 6.16) attach to each frame `x` a double loop `σ_x` at
`p` (`TauCeti.stiefelDoubleLoop`), and their Proposition 6.17 asserts that the class
`σ_{p*}[Σ_p] ∈ H_{2n-3}(Ω²Sⁿ)` is nonzero for even `n`. Its proof applies the degree-raising map
`β_* : H_*(Ω²Sⁿ) → H_{*+1}(ΩSⁿ)` (`TauCeti.degreeRaising`) and computes

`β_* σ_{p*}[Σ_p] = (α ∘ τ)_*[Σ_p × S¹]`,

where `τ : Σ_p × S¹ → S^{n-1} × S^{n-1}` is the Stiefel rotation family
(`TauCeti.stiefelRotationFamily`) and `α (u, w) = γ_w · γ_u⁻¹` is the loop going to `-p` along the
meridian in the direction `w` and back along the meridian in the direction `u`
(`TauCeti.meridianLoop`). This file proves this identity, for every class of `Σ_p` and every
commutative coefficient ring.

The degree-raising map sends the image `ℓ_* c` of a class under a family `ℓ : A → Ω²X` of double
loops to the image of `[S¹] × c` under the evaluation `S¹ × A → ΩX`, `(z, a) ↦ ℓ a (z)`
(`TauCeti.map_comp_degreeRaising_eq_evalCircle`). For the family `σ`, this evaluation is the map
`A × S¹ → ΩX` of the loops of loops `σ_x` with the factors exchanged
(`TauCeti.BasedTopologicalSpace.evalCircle_comp_prodMap`), and that map is homotopic to `α ∘ τ`
(`TauCeti.homotopic_loopFamilyCircleMap_stiefelDoubleLoop`), so the two maps agree on homology.
The cross product is taken with the fundamental class of the circle on the left, as in the
definition of `β_*`, so `α ∘ τ` appears composed with the exchange of factors
`S¹ × Σ_p → Σ_p × S¹`.

## Main results

* `TauCeti.map_stiefelDoubleLoop_comp_degreeRaising`: `β_*(σ_{p*} c)` is the image of `[S¹] × c`
  under `α ∘ τ`, composed with the exchange of factors.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.2, Example 6.16 and the proof of
  Proposition 6.17.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Metric

namespace TauCeti

variable (R : Type) [CommRing R] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (p : sphere (0 : E) 1) (q n : ℕ) (h : 1 + q = n)

/-- **The degree-raising map on the Stiefel double loops** (Barraud–Damian–Humilière–Oancea, proof
of Proposition 6.17). For the family `σ_p : V₂(p^⊥) → Ω²Sⁿ` of double loops
(`TauCeti.stiefelDoubleLoop`) and a class `c` of `V₂(p^⊥)`, the degree-raising map sends `σ_{p*} c`
to the image of `[S¹] × c` under `α ∘ τ` (`TauCeti.meridianLoopRotation`), composed with the
exchange of factors `S¹ × V₂(p^⊥) → V₂(p^⊥) × S¹`. -/
@[reassoc]
theorem map_stiefelDoubleLoop_comp_degreeRaising :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) q).obj (𝟙_ _)).map
        (TopCat.ofHom ⟨stiefelDoubleLoop p, continuous_stiefelDoubleLoop p⟩ :
          TopCat.of (stiefel (ℝ ∙ (p : E))ᗮ 2) ⟶
            TopCat.of
              ((⟨sphere (0 : E) 1, p⟩ : BasedTopologicalSpace).iteratedLoopSpace 2).carrier) ≫
        degreeRaising (𝟙_ (ModuleCat.{0} R)) ⟨sphere (0 : E) 1, p⟩ q n h =
      (λ_ _).inv ≫ (circleFundamentalClass (𝟙_ (ModuleCat.{0} R)) ▷ _) ≫
        TopCat.singularHomologyCross (C := ModuleCat.{0} R) (TopCat.of Sphere1)
          (TopCat.of (stiefel (ℝ ∙ (p : E))ᗮ 2)) (𝟙_ _) (𝟙_ _) 1 q n h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map
          (λ_ (𝟙_ _)).hom).app _ ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
          (TopCat.ofHom ((meridianLoopRotation p).comp ContinuousMap.prodSwap)) := by
  -- The evaluation of the double loops on the circle is the map of the loops of loops `σ_x`,
  -- which is homotopic to `α ∘ τ`.
  rw [map_comp_degreeRaising_eq_evalCircle]
  refine congrArg (fun f ↦ _ ≫ _ ≫ _ ≫ _ ≫ f) ?_
  rw [TopCat.hom_ofHom, BasedTopologicalSpace.evalCircle_comp_prodMap
    (X := ⟨sphere (0 : E) 1, p⟩) (stiefelDoubleLoop p) (continuous_stiefelDoubleLoop p)]
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (C := ModuleCat.{0} R)
    ((homotopic_loopFamilyCircleMap_stiefelDoubleLoop p).comp
      (ContinuousMap.Homotopic.refl ContinuousMap.prodSwap)).some _ n

end TauCeti
