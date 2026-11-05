/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Functor
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality

/-!
# Naturality of the standard trivializations of twisting sheaves

Let `g : 𝒜 →+*ᵍ ℬ` be a graded ring homomorphism with `ℬ₊ ≤ 𝒜₊.map g`, and let `f ∈ 𝒜₁`. On the
standard open `D₊(f)` of `Proj 𝒜`, multiplication by `fⁿ` trivializes `𝒪(n)`
(`AlgebraicGeometry.Proj.twistingSheaf.chartSectionsLinearEquiv`), and on `D₊(g f)` of `Proj ℬ`,
multiplication by `(g f)ⁿ` trivializes `𝒪(n)`. This file proves that the pullback of sections of
twisting sheaves along `Proj.map g hg` (`AlgebraicGeometry.Proj.twistingSheaf.comap`) sends `fⁿ` to
`(g f)ⁿ`, so that in these coordinates it is the pullback of functions along `Proj.map g hg`.

This is the chart computation behind the fact that a graded map surjective in positive degrees
pulls `𝒪(1)` back to `𝒪(1)` (Stacks, Lemma 01N1): over the degree-one standard opens both sides are
free on the corresponding generators, and the comparison map matches the generators.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.le_basicOpen_map`: an open lying over `D₊(f)` lies in
  `D₊(g f)`.
* `AlgebraicGeometry.Proj.twistingSheaf.comap_chartGenerator`: the pullback of the standard
  generator `fⁿ` is the standard generator `(g f)ⁿ`.
* `AlgebraicGeometry.Proj.twistingSheaf.comap_chartSectionsLinearEquiv`: in standard chart
  coordinates, the pullback of sections of `𝒪(n)` is the pullback of functions.
* `AlgebraicGeometry.Proj.twistingSheaf.twistingSheafMap_app_chartGenerator`: the morphism of
  twisting sheaves sends the standard generator `fⁿ` to the standard generator `(g f)ⁿ`.

## References

* [The Stacks Project, Lemma 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

public section

noncomputable section

namespace AlgebraicGeometry.Proj.twistingSheaf

open HomogeneousIdeal

universe u

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g) (n : ℤ) {f : A} (hf : f ∈ 𝒜 1)
  {U : (Proj 𝒜).Opens} (hU : U ≤ basicOpen 𝒜 f) {V : (Proj ℬ).Opens}
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap g hg ⁻¹' U.1)

include hU hUV in
/-- An open of `Proj ℬ` lying over an open contained in `D₊(f)` is contained in `D₊(g f)`. -/
theorem le_basicOpen_map : V ≤ basicOpen ℬ (g f) :=
  fun _ hy ↦ hU (hUV hy)

/-- **The pullback of the standard generator `fⁿ` is the standard generator `(g f)ⁿ`.** -/
@[simp]
theorem comap_chartGenerator :
    comap g hg hUV (chartGenerator n f hf U hU) =
      chartGenerator n (g f) (Graded.map_mem g hf) V (le_basicOpen_map g hg hU hUV) := by
  refine ext fun (y : V) ↦ ?_
  simp only [comap_apply, chartGenerator_apply]
  refine (ProjectiveSpectrum.TwistingSheaf.localizationsMap_mk g hg _ _ _).trans ?_
  simp only [map_pow]

/-- **In standard chart coordinates the pullback of sections of `𝒪(n)` is the pullback of
functions**: the section `a • fⁿ` pulls back to `(Proj.map g hg)^* a • (g f)ⁿ`. -/
theorem comap_chartSectionsLinearEquiv (a : Γ(Proj 𝒜, U)) :
    comap g hg hUV (chartSectionsLinearEquiv n f hf U hU a) =
      chartSectionsLinearEquiv n (g f) (Graded.map_mem g hf) V (le_basicOpen_map g hg hU hUV)
        ((map g hg).appLE U V hUV a) := by
  rw [chartSectionsLinearEquiv_apply, chartSectionsLinearEquiv_apply, comap_smul,
    comap_chartGenerator]

/-- The morphism of twisting sheaves induced by `g`, read in standard chart coordinates on an open
`W ≤ D₊(f)`, is the pullback of functions along `Proj.map g hg`. -/
theorem twistingSheafMap_app_chartSectionsLinearEquiv {W : (Proj 𝒜).Opens}
    (hW : W ≤ basicOpen 𝒜 f) (a : Γ(Proj 𝒜, W)) :
    Scheme.Modules.Hom.app (twistingSheafMap g hg n) W (chartSectionsLinearEquiv n f hf W hW a) =
      chartSectionsLinearEquiv n (g f) (Graded.map_mem g hf) (map g hg ⁻¹ᵁ W)
        (le_basicOpen_map g hg hW Set.Subset.rfl) ((map g hg).app W a) := by
  rw [twistingSheafMap_app, Scheme.Hom.app_eq_appLE]
  exact comap_chartSectionsLinearEquiv g hg n hf hW Set.Subset.rfl a

/-- The morphism of twisting sheaves induced by `g` sends the standard generator `fⁿ` on an open
`W ≤ D₊(f)` to the standard generator `(g f)ⁿ` on its preimage. -/
theorem twistingSheafMap_app_chartGenerator {W : (Proj 𝒜).Opens} (hW : W ≤ basicOpen 𝒜 f) :
    Scheme.Modules.Hom.app (twistingSheafMap g hg n) W (chartGenerator n f hf W hW) =
      chartGenerator n (g f) (Graded.map_mem g hf) (map g hg ⁻¹ᵁ W)
        (le_basicOpen_map g hg hW Set.Subset.rfl) := by
  rw [twistingSheafMap_app]
  exact comap_chartGenerator g hg n hf hW Set.Subset.rfl

end AlgebraicGeometry.Proj.twistingSheaf
