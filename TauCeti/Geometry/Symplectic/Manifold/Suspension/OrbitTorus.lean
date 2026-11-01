/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.AddCircle
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.AlmostComplex
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Horizontal

/-!
# Orbit tori are pseudoholomorphic

Let `φ` be a diffeomorphism of a locally compact Hausdorff smooth manifold `M`, let
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` be its smooth mapping torus, with suspension vector
field `T = ∂_t`, and let `X_φ = (ℝ / ℤ)_s × Y_φ`. A point `x` of positive period `d` of `φ` gives
the closed orbit `γ : ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`, of the suspension flow and its orbit torus

`u : (ℝ / ℤ) × (ℝ / dℤ) → X_φ`, `(s, θ) ↦ (s, γ θ)`

(`TauCeti.SmoothMappingTorus.orbitTorus`). Give the parameter torus its standard almost complex
structure `j`, with `j ∂_s = ∂_θ` (`TauCeti.SmoothAlmostComplexStructure.addCircleProd`). The
differential of `u` sends `∂_s` to `∂_s` and `∂_θ` to `T`, so for an almost complex structure `J`
on `X_φ` the Cauchy–Riemann equation `du ∘ j = J ∘ du` at a point says exactly that
`J ∂_s = T` there (`TauCeti.SmoothMappingTorus.isPseudoholomorphicAt_orbitTorus_iff`).
No condition on the restriction of `J` to the vertical directions is involved.

In particular the orbit torus is pseudoholomorphic for every block almost complex structure
descended from a vertical family of almost complex structures satisfying the seam identity
(`TauCeti.SmoothMappingTorus.isPseudoholomorphic_orbitTorus_suspensionAlmostComplexStructure`).
When `d` is the least period of `x`, the orbit torus is moreover a smooth embedding
(`TauCeti.SmoothMappingTorus.isSmoothEmbedding_orbitTorus_iff`), so a periodic orbit of `φ` of
least period `d` gives an embedded pseudoholomorphic torus in `X_φ`. For a multiple of the least
period the orbit torus is a multiple cover of that embedded torus, and it is pseudoholomorphic
too. These are the tori that the classification of compact pseudoholomorphic curves of zero
vertical area in `X_φ` produces.

## Main results

* `TauCeti.SmoothMappingTorus.isPseudoholomorphicAt_orbitTorus_iff`: the orbit torus is
  pseudoholomorphic at a point exactly when `J ∂_s = T` at its image.
* `TauCeti.SmoothMappingTorus.isPseudoholomorphic_orbitTorus_iff`: the global version.
* `TauCeti.SmoothMappingTorus.isPseudoholomorphic_orbitTorus_suspensionAlmostComplexStructure`:
  the orbit torus is pseudoholomorphic for the descended block structure.

## References

* E. Ionel and T. Parker, *Gromov invariants and symplectic maps*, Mathematische Annalen
  314 (1999), 127–158 (pseudoholomorphic tori associated to periodic orbits).
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (admissible almost complex structures and the
  cylinders over closed orbits).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  {φ : M ≃ₘ⟮I, I⟯ M} {x : M} {d : ℕ} (hx : IsPeriodicPt φ d x) [Fact (0 < (d : ℝ))]
  {J : SmoothAlmostComplexStructure (𝓘(ℝ).prod (𝓘(ℝ).prod I))
    (UnitAddCircle × SmoothMappingTorus φ)}

/-- The orbit torus `(s, θ) ↦ (s, γ θ)` is pseudoholomorphic at `p`, for the standard structure of
the parameter torus, exactly when `J` sends `∂_s` to the suspension vector field `T` at the image
of `p`. -/
theorem isPseudoholomorphicAt_orbitTorus_iff (p : UnitAddCircle × AddCircle (d : ℝ)) :
    IsPseudoholomorphicAt (SmoothAlmostComplexStructure.addCircleProd 1 d) J (orbitTorus φ hx) p ↔
      J (orbitTorus φ hx p) ((Manifold.tangentSpaceProdEquiv _).symm ((1 : ℝ), 0)) =
        (Manifold.tangentSpaceProdEquiv _).symm
          ((0 : ℝ), timeVectorField φ (orbitTorus φ hx p).2) := by
  rw [isPseudoholomorphicAt_iff_mfderiv]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨((contMDiff_orbitTorus (n := ∞) hx) p).mdifferentiableAt (by simp),
    fun w ↦ ?_⟩⟩
  · -- The Cauchy–Riemann equation on `∂_s` reads `T = J ∂_s`.
    have h1 := h.2 ((Manifold.tangentSpaceProdEquiv p).symm ((1 : ℝ), (0 : ℝ)))
    rw [SmoothAlmostComplexStructure.addCircleProd_apply, mfderiv_orbitTorus_apply,
      mfderiv_orbitTorus_apply, neg_zero, one_smul, zero_smul] at h1
    exact h1.symm
  · -- Write `w = a ∂_s + b ∂_θ`, so `du w = a ∂_s + b T` and `du (j w) = -b ∂_s + a T`.
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℝ, w = (Manifold.tangentSpaceProdEquiv p).symm (a, b) :=
      ⟨(Manifold.tangentSpaceProdEquiv p w).1, (Manifold.tangentSpaceProdEquiv p w).2,
        ((Manifold.tangentSpaceProdEquiv p).symm_apply_apply w).symm⟩
    rw [SmoothAlmostComplexStructure.addCircleProd_apply, mfderiv_orbitTorus_apply,
      mfderiv_orbitTorus_apply]
    set q := orbitTorus φ hx p
    set e := Manifold.tangentSpaceProdEquiv (I := 𝓘(ℝ)) (J := 𝓘(ℝ).prod I) q
    set S := e.symm ((1 : ℝ), (0 : TangentSpace (𝓘(ℝ).prod I) q.2))
    set T := e.symm ((0 : ℝ), timeVectorField φ q.2)
    have hsplit (a b : ℝ) : e.symm (a, b • timeVectorField φ q.2) = a • S + b • T := by
      rw [← map_smul, ← map_smul, ← map_add]
      congr 1
      -- The first components are real numbers, where scalar multiplication is multiplication.
      exact Prod.ext (by ring : a = a * 1 + b * 0) (by simp)
    -- `J` is linear, `J ∂_s = T` and hence `J T = J (J ∂_s) = -∂_s`.
    have hT : J q T = -S := apply_symm_zero_timeVectorField h
    beta_reduce at h hT ⊢
    rw [hsplit, hsplit, map_add, map_smul, map_smul, h, hT, smul_neg, neg_smul, add_comm]

/-- The orbit torus `(s, θ) ↦ (s, γ θ)` is pseudoholomorphic, for the standard structure of the
parameter torus, exactly when `J` sends `∂_s` to the suspension vector field `T` along its image.
-/
theorem isPseudoholomorphic_orbitTorus_iff :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.addCircleProd 1 d) J (orbitTorus φ hx) ↔
      ∀ q ∈ Set.range (orbitTorus φ hx),
        J q ((Manifold.tangentSpaceProdEquiv q).symm ((1 : ℝ), 0)) =
          (Manifold.tangentSpaceProdEquiv q).symm ((0 : ℝ), timeVectorField φ q.2) := by
  rw [isPseudoholomorphic_iff, Set.forall_mem_range]
  exact forall_congr' (isPseudoholomorphicAt_orbitTorus_iff hx)

/-- The orbit torus `(s, θ) ↦ (s, γ θ)` of a closed orbit of the suspension flow is
pseudoholomorphic for every block almost complex structure on `(ℝ / ℤ) × Y_φ` descended from a
vertical family `K` that is periodic in `s` and satisfies the seam identity in `t`. -/
theorem isPseudoholomorphic_orbitTorus_suspensionAlmostComplexStructure [FiniteDimensional ℝ E]
    {K : ∀ p : (ℝ × ℝ) × M, AlmostComplexStructure (TangentSpace I p.2)}
    (hK : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun p ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (K p).toLinearMap.toContinuousLinearMap))
    (hs : ∀ p : (ℝ × ℝ) × M, K (p.1 + (1, 0), p.2) = K p)
    (ht : ∀ (p : (ℝ × ℝ) × M) (v : TangentSpace I p.2),
      mfderiv I I φ.symm p.2 (K p v) = K (p.1 + (0, 1), φ.symm p.2) (mfderiv I I φ.symm p.2 v)) :
    IsPseudoholomorphic (SmoothAlmostComplexStructure.addCircleProd 1 d)
      (suspensionAlmostComplexStructure φ hK hs ht) (orbitTorus φ hx) :=
  (isPseudoholomorphic_orbitTorus_iff hx).2 fun q _ ↦
    suspensionAlmostComplexStructure_apply_symm_one_zero φ hK hs ht q

end TauCeti.SmoothMappingTorus
