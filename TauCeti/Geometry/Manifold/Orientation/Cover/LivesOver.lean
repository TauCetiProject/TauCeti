/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LivesOver
public import TauCeti.Geometry.Manifold.Orientation.Cover.FundamentalClass
import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass

/-!
# The twisted fundamental class lives over the fundamental class at every point

Let `M` be a compact boundaryless smooth manifold of dimension `n + 1`, orientable or not, with
orientation double cover `π : M' → M` and orientation-twisted fundamental class
`[M]_or ∈ Hₙ₊₁(M; o(TM))` (`TauCeti.Manifold.OrientationCover.twistedFundamentalClass`). This file
shows that `[M]_or` lives over the fundamental class of `M` at every point `b`: its localization

`Hₙ₊₁(M; o(TM)) → Hₙ₊₁(M, M ∖ {b}; o(TM))`

is nonzero
(`TauCeti.Manifold.OrientationCover.livesOverFundamentalClass_id_twistedFundamentalClass`).
This is the case of a point fibre of the notion
`TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass`, which is stated with coefficients
twisted by the orientation system precisely so that it applies over a base with no integral
fundamental class, such as `ℝP²`, where `Hₙ₊₁(M; ℤ) = 0`
(`TauCeti.subsingleton_singularHomology_of_isEmpty_homologicalOrientation`).

The proof reads `[M]_or` on the cover. Reading functions on the fibres of `π` as formal sums of
sheets carries `[M]_or` to the class of `[M']` in the homology of `M` twisted by the permutation
local system `ℤ[π⁻¹ x]`, and localization commutes with this change of coefficients. Relative to
the complement of `b`, the twisted homology of `M` with coefficients in `ℤ[π⁻¹ x]` is the relative
singular homology of `(M', M' ∖ π⁻¹(b))`, compatibly with the absolute comparison
(`IsCoveringMap.singularHomologyπ_comp_singularPairHomologyPermutationIso_hom`). So the
localization of `[M]_or` at `b` vanishes only if the image of `[M']` in
`Hₙ₊₁(M', M' ∖ π⁻¹(b); ℤ)` does, and then so does its further image in the local homology
`Hₙ₊₁(M', M' ∖ {x}; ℤ)` at a point `x` over `b`. That image is the local orientation of `M'` at
`x`, which is nonzero.

## Main results

* `TauCeti.Manifold.OrientationCover.livesOverFundamentalClass_id_twistedFundamentalClass`: the
  orientation-twisted fundamental class lives over the fundamental class at every point.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.H, the orientation
  local system and the fundamental class of a nonorientable manifold with twisted coefficients.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Definition 2.3).
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module TauCeti.LocalCoefficientSystem
open scoped Manifold

namespace TauCeti.Manifold.OrientationCover

variable {E M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M] {n : ℕ}
  (hE : finrank ℝ E = n + 1) [CompactSpace M]

/-- The image of the fundamental class `[M']` of the orientation cover in the relative homology
`Hₙ₊₁(M', M' ∖ π⁻¹(b); ℤ)` is nonzero: its further image in the local homology at a point over `b`
is a local orientation. -/
private theorem singularHomologyπ_coverFundamentalClass_ne_zero (b : M) :
    ((TopPair.ofSubset (projHom (E := E) M ⁻¹' ((id : M → M) ⁻¹' {b})ᶜ)).singularHomologyπ
      (ModuleCat.of ℤ ℤ) (n + 1)).hom (coverFundamentalClass M hE) ≠ 0 := by
  obtain ⟨x, hx⟩ := VectorBundleOrientationCover.surjective_proj (F := E)
    (E := (TangentSpace 𝓘(ℝ, E) : M → Type)) (Fintype.card_fin _) b
  -- The cover has a fundamental class with coefficients in `ℤ`, transported from `ULift ℤ`.
  have hfund : IsFundamentalClass (coverFundamentalClass M hE) := by
    rw [coverFundamentalClass_def, uliftIntHomologyIso_hom]
    exact (isFundamentalClass_singularHomologyFunctor_map_app_iff uliftIntIso _).2
      ((homologicalOrientation hE).isFundamentalClass_fundamentalClass hE)
  have hloc := hfund.singularHomologyToLocalHomology_ne_zero hE x
  intro h
  apply hloc
  -- The complement of the fibre over `b` lies in the complement of `x`, so the local image at `x`
  -- factors through the relative class over the complement of the fibre.
  have hsub : Set.MapsTo (𝟙 (TopCat.of (OrientationCover 𝓘(ℝ, E) M)))
      (projHom (E := E) M ⁻¹' ((id : M → M) ⁻¹' {b})ᶜ) {x}ᶜ := fun y hy hyx ↦
    hy (by obtain rfl : y = x := hyx; exact hx)
  rw [singularHomologyToLocalHomology_eq_singularHomologyπ,
    ← TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id (ModuleCat.of ℤ ℤ) hsub]
  exact (congrArg (ModuleCat.Hom.hom (TopPair.singularHomologyMap (TopPair.ofSubsetMap _ hsub)
    (ModuleCat.of ℤ ℤ) (n + 1))) h).trans (map_zero _)

/-- **The twisted fundamental class lives over the fundamental class at every point**: the
localization `Hₙ₊₁(M; o(TM)) → Hₙ₊₁(M, M ∖ {b}; o(TM))` sends the orientation-twisted fundamental
class `[M]_or` to a nonzero class, for every point `b` of `M`. This holds whether or not `M` is
orientable. -/
theorem livesOverFundamentalClass_id_twistedFundamentalClass (b : M) :
    ((isCoveringMap_projHom E M).signLocalSystem ℤ _
      VectorBundleOrientationCover.proj_comp_deck).LivesOverFundamentalClass (id : M → M) b
        (twistedFundamentalClass M hE) := by
  refine LivesOverFundamentalClass.of_twistedHomologyCoefficientMap
    ((isCoveringMap_projHom E M).signLocalSystemToPermutation ℤ
      VectorBundleOrientationCover.proj_comp_deck (finite_preimage_projHom M)) ?_
  -- Read on the cover, the twisted fundamental class is `[M']`.
  have hcover := congrArg ((isCoveringMap_projHom E M).singularHomologyPermutationIso ℤ
    (n + 1)).hom.hom (singularHomologyPermutationIso_inv_twistedFundamentalClass hE)
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply] at hcover
  -- Relative to the complement of `b`, the homology of `M` twisted by the permutation system is
  -- the relative homology of the cover, so a vanishing localization would kill the image of `[M']`.
  refine (LocalCoefficientSystem.livesOverFundamentalClass_iff
    ((isCoveringMap_projHom E M).permutationLocalSystem ℤ)
      (id : M → M) b _).2 fun h ↦ ?_
  refine singularHomologyπ_coverFundamentalClass_ne_zero hE b <|
    (ModuleCat.mono_iff_injective ((isCoveringMap_projHom E M).singularPairHomologyPermutationIso
      ℤ ((id : M → M) ⁻¹' {b})ᶜ (n + 1)).hom).1 inferInstance ?_
  exact (congrArg (fun φ ↦ φ.hom (coverFundamentalClass M hE))
    ((isCoveringMap_projHom E M).singularHomologyπ_comp_singularPairHomologyPermutationIso_hom ℤ
      ((id : M → M) ⁻¹' {b})ᶜ (n + 1))).trans <|
    ((congrArg _ hcover.symm).trans h).trans (map_zero (ModuleCat.Hom.hom
      ((isCoveringMap_projHom E M).singularPairHomologyPermutationIso ℤ ((id : M → M) ⁻¹' {b})ᶜ
        (n + 1)).hom)).symm

end TauCeti.Manifold.OrientationCover
