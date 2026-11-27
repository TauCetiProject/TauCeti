/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.TopColumn
public import TauCeti.Geometry.Manifold.Morse.DG.TwistedComplex

/-!
# The component of the DG Morse complex at the maximum

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, and let
`𝓕 ⊗ ⟨Crit f⟩` be its DG Morse complex (`TauCeti.IsAdaptedPseudoGradient.dgMorseComplex`) with
coefficients in a DG local system `𝓕`. Every critical point has Morse index at most `n`
(`TauCeti.manifoldMorseIndex_le_finrank`), and the twisted differential never raises the index,
so the coefficient `α_{x_max}` of a cycle `Σ_x α_x ⊗ x` at a critical point `x_max` of index `n`
is a cycle of `𝓕`. The **component at the maximum**
(`TauCeti.IsAdaptedPseudoGradient.dgMorseMaxComponent`) sends the class of the cycle to the class
of `α_{x_max}` in the cohomology of `𝓕`, in degree `k + n` for a class of degree `k`
(`TauCeti.IsAdaptedPseudoGradient.coe_dgMorseMaxComponent` and
`TauCeti.TwistingCocycle.topComponentCohomology_homologyπ`); it vanishes on the class of the cycle
exactly when `α_{x_max}` is a boundary of `𝓕`
(`TauCeti.IsAdaptedPseudoGradient.dgMorseMaxComponent_homologyπ_eq_zero_iff`). In the homological
grading `C_k = C^{-k}` of DG Morse homology it is a map `H_k(M; 𝓕) → H_{k - n}(𝓕)`.

Suppose that `x_max` is the only critical point of index `n`, as for a Morse function with a unique
local maximum. Then the component at the maximum detects exactly the classes that do not come from
the critical points of lower index: it vanishes on a class exactly when the class comes from the
subcomplex spanned by the critical points of index at most `n - 1`
(`TauCeti.IsAdaptedPseudoGradient.dgMorseMaxComponent_eq_zero_iff`), equivalently when the class
vanishes on the top column `E^∞_{n,*}` of the index spectral sequence
(`TauCeti.IsAdaptedPseudoGradient.indexToTopColumnEInfty_eq_zero_iff_dgMorseMaxComponent_eq_zero`).
These are the twisted-complex statements
`TauCeti.TwistingCocycle.topComponentCohomology_eq_zero_iff` and
`TauCeti.TwistingCocycle.indexToTopColumnEInfty_eq_zero_iff_topComponentCohomology_eq_zero` for the
Barraud–Cornea cocycle.

Barraud, Damian, Humilière and Oancea characterize the classes living over the fundamental class
of the base by their component at the maximum (Proposition 2.5) and by the top column of the
spectral sequence (Proposition 2.6). This file gives the Morse side of that characterization: the
identification of the component at the maximum with the shriek map of the inclusion of a point is
not made here.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.dgMorseMaxComponent`: the component at a critical point of
  maximal index, `Hᵏ(𝓕 ⊗ ⟨Crit f⟩) → H^{k + n}(𝓕)`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.dgMorseMaxComponent_homologyπ_eq_zero_iff`: it vanishes on the
  class of a cycle exactly when the coefficient at the maximum is a boundary.
* `TauCeti.IsAdaptedPseudoGradient.dgMorseMaxComponent_eq_zero_iff`: at the only critical point of
  maximal index, it vanishes exactly on the classes coming from the critical points of lower index.
* `TauCeti.IsAdaptedPseudoGradient.indexToTopColumnEInfty_eq_zero_iff_dgMorseMaxComponent_eq_zero`:
  and exactly on the classes vanishing on the top column of the index spectral sequence.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Propositions 2.5 and 2.6.
-/

public section

noncomputable section

open CategoryTheory Set HomologicalComplex Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}

/-- The Morse index of `f` at every point is at most `(n - 1) + 1`, for `n` the dimension of `M`:
`TauCeti.manifoldMorseIndex_le_finrank` in the integer grading of the DG Morse complex, as the
bound on the indices of the generators under which the top column of its index spectral sequence
is taken. -/
theorem natCast_manifoldMorseIndex_le_finrank_sub_one_add_one (x : M) :
    (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) ≤ (finrank ℝ E : ℤ) - 1 + 1 := by
  rw [sub_add_cancel]
  exact_mod_cast manifoldMorseIndex_le_finrank

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  {Y : Type*} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)
  {R : Type*} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  (S : TwistingChainSystem (fun x : criticalPoints 𝓘(ℝ, E) f ↦
    (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ)) (hX.morseBrokenTrajectorySpaceComp hc) R)
  (𝓕 : DGLocalSystem Y y₀ R) {xmax : criticalPoints 𝓘(ℝ, E) f}
  (hmax : manifoldMorseIndex 𝓘(ℝ, E) f xmax = finrank ℝ E)

/-- **The component of the DG Morse complex at a critical point of maximal index** `n`, the
dimension of `M`: the map `Hᵏ(𝓕 ⊗ ⟨Crit f⟩) → H^{k + n}(𝓕)` sending the class of a cycle
`Σ_x α_x ⊗ x` to the class of `α_{x_max}`
(`TauCeti.IsAdaptedPseudoGradient.coe_dgMorseMaxComponent`,
`TauCeti.TwistingCocycle.topComponentCohomology_homologyπ`). -/
def dgMorseMaxComponent (k : ℤ) :
    (hX.dgMorseComplex hf hdense hθ hc S 𝓕).homology k →ₗ[R]
      𝓕.isDGRightModule.cohomologyGrading (k + finrank ℝ E) :=
  (LinearEquiv.ofEq _ _ (by rw [sub_add_cancel])).toLinearMap ∘ₗ
    (hX.barraudCorneaCocycle hf hdense hθ hc S).topComponentCohomology 𝓕.differential
      𝓕.isDGRightModule (fun x ↦ natCast_manifoldMorseIndex_le_finrank_sub_one_add_one (f := f) x)
      ⟨xmax, by rw [sub_add_cancel, hmax]⟩ k

/-- The component at the maximum is `TauCeti.TwistingCocycle.topComponentCohomology` for the
Barraud–Cornea cocycle, read in degree `k + n`: on the class of a cycle it is the class of its
coefficient at the maximum (`TauCeti.TwistingCocycle.topComponentCohomology_homologyπ`). -/
theorem coe_dgMorseMaxComponent {k : ℤ} (α : (hX.dgMorseComplex hf hdense hθ hc S 𝓕).homology k) :
    (hX.dgMorseMaxComponent hf hdense hθ hc S 𝓕 hmax k α : 𝓕.isDGRightModule.Cohomology) =
      (hX.barraudCorneaCocycle hf hdense hθ hc S).topComponentCohomology 𝓕.differential
        𝓕.isDGRightModule (fun x ↦ natCast_manifoldMorseIndex_le_finrank_sub_one_add_one (f := f) x)
        ⟨xmax, by rw [sub_add_cancel, hmax]⟩ k α :=
  (rfl)

/-- The component at the maximum vanishes exactly when
`TauCeti.TwistingCocycle.topComponentCohomology` does. -/
private theorem dgMorseMaxComponent_eq_zero_iff_topComponentCohomology {k : ℤ}
    (α : (hX.dgMorseComplex hf hdense hθ hc S 𝓕).homology k) :
    hX.dgMorseMaxComponent hf hdense hθ hc S 𝓕 hmax k α = 0 ↔
      (hX.barraudCorneaCocycle hf hdense hθ hc S).topComponentCohomology 𝓕.differential
        𝓕.isDGRightModule (fun x ↦ natCast_manifoldMorseIndex_le_finrank_sub_one_add_one (f := f) x)
        ⟨xmax, by rw [sub_add_cancel, hmax]⟩ k α = 0 := by
  rw [← Submodule.coe_eq_zero, coe_dgMorseMaxComponent, Submodule.coe_eq_zero]

/-- **The chain-level form of the component at the maximum.** The component at the maximum
vanishes on the class of a cycle `g = Σ_x α_x ⊗ x` of the DG Morse complex exactly when the
coefficient `α_{x_max}` is a boundary of `𝓕`. -/
theorem dgMorseMaxComponent_homologyπ_eq_zero_iff {k : ℤ}
    (g : (hX.dgMorseComplex hf hdense hθ hc S 𝓕).X k)
    (hg : ((hX.dgMorseComplex hf hdense hθ hc S 𝓕).d k (k + 1)).hom g = 0) :
    hX.dgMorseMaxComponent hf hdense hθ hc S 𝓕 hmax k
        (((hX.dgMorseComplex hf hdense hθ hc S 𝓕).homologyπ k).hom
          ((hX.dgMorseComplex hf hdense hθ hc S 𝓕).moduleCatCyclesMk g (k + 1) (by simp) hg)) =
        0 ↔
      (twistedCochainComplexXEquiv (hX.barraudCorneaCocycle hf hdense hθ hc S).mem_graded
          (hX.barraudCorneaCocycle hf hdense hθ hc S).twisting 𝓕.isDGRightModule k g :
            criticalPoints 𝓘(ℝ, E) f → 𝓕) xmax ∈ LinearMap.range 𝓕.differential :=
  (hX.dgMorseMaxComponent_eq_zero_iff_topComponentCohomology hf hdense hθ hc S 𝓕 hmax _).trans
    ((hX.barraudCorneaCocycle hf hdense hθ hc S).topComponentCohomology_homologyπ_eq_zero_iff
      _ _ _ _ g hg)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  [Fintype (criticalPoints 𝓘(ℝ, E) f)] in
/-- A critical point of index `(n - 1) + 1` is the only critical point `x_max` of index `n`. -/
private theorem eq_of_natCast_manifoldMorseIndex_eq
    (huniq : ∀ x : criticalPoints 𝓘(ℝ, E) f, manifoldMorseIndex 𝓘(ℝ, E) f x = finrank ℝ E →
      x = xmax)
    (y : {x : criticalPoints 𝓘(ℝ, E) f //
      (manifoldMorseIndex 𝓘(ℝ, E) f x : ℤ) = (finrank ℝ E : ℤ) - 1 + 1}) :
    (y : criticalPoints 𝓘(ℝ, E) f) = xmax := by
  refine huniq y ?_
  have h : (manifoldMorseIndex 𝓘(ℝ, E) f y : ℤ) = finrank ℝ E :=
    y.property.trans (sub_add_cancel _ _)
  exact_mod_cast h

/-- **The component at the only critical point of maximal index detects the classes that do not
come from lower index.** If `x_max` is the only critical point of index `n`, the dimension of `M`,
a DG Morse cohomology class has zero component at `x_max` exactly when it comes from the subcomplex
spanned by the critical points of index at most `n - 1`. -/
theorem dgMorseMaxComponent_eq_zero_iff
    (huniq : ∀ x : criticalPoints 𝓘(ℝ, E) f, manifoldMorseIndex 𝓘(ℝ, E) f x = finrank ℝ E →
      x = xmax)
    {k : ℤ} (α : (hX.dgMorseComplex hf hdense hθ hc S 𝓕).homology k) :
    hX.dgMorseMaxComponent hf hdense hθ hc S 𝓕 hmax k α = 0 ↔
      α ∈ LinearMap.range (homologyMap ((hX.barraudCorneaCocycle hf hdense hθ hc S)
        |>.twistedIndexCochainComplexι 𝓕.isDGRightModule ((finrank ℝ E : ℤ) - 1)) k).hom :=
  (hX.dgMorseMaxComponent_eq_zero_iff_topComponentCohomology hf hdense hθ hc S 𝓕 hmax α).trans
    ((hX.barraudCorneaCocycle hf hdense hθ hc S).topComponentCohomology_eq_zero_iff _ _ _ _
      (fun y ↦ Subtype.ext (eq_of_natCast_manifoldMorseIndex_eq huniq y)) α)

/-- **The component at the only critical point of maximal index detects the top column.** If
`x_max` is the only critical point of index `n`, the dimension of `M`, a DG Morse cohomology class
vanishes on the top column `E^∞_{n,*}` of the index spectral sequence exactly when its component
at `x_max` vanishes. -/
theorem indexToTopColumnEInfty_eq_zero_iff_dgMorseMaxComponent_eq_zero
    (huniq : ∀ x : criticalPoints 𝓘(ℝ, E) f, manifoldMorseIndex 𝓘(ℝ, E) f x = finrank ℝ E →
      x = xmax)
    {k : ℤ} (α : (hX.dgMorseComplex hf hdense hθ hc S 𝓕).homology k) :
    ((hX.barraudCorneaCocycle hf hdense hθ hc S).indexToTopColumnEInfty 𝓕.differential
        𝓕.isDGRightModule
        (fun x ↦ natCast_manifoldMorseIndex_le_finrank_sub_one_add_one (f := f) x) k).hom α = 0 ↔
      hX.dgMorseMaxComponent hf hdense hθ hc S 𝓕 hmax k α = 0 :=
  ((hX.barraudCorneaCocycle hf hdense hθ hc S)
    |>.indexToTopColumnEInfty_eq_zero_iff_topComponentCohomology_eq_zero _ _ _ _
      (fun y ↦ Subtype.ext (eq_of_natCast_manifoldMorseIndex_eq huniq y)) α).trans
    (hX.dgMorseMaxComponent_eq_zero_iff_topComponentCohomology hf hdense hθ hc S 𝓕 hmax α).symm

end IsAdaptedPseudoGradient

end TauCeti
