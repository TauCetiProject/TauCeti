/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.Cohomology.Cap.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.FundamentalClass
public import TauCeti.CategoryTheory.Monoidal.Preadditive

/-!
# Capping with the fundamental class of a star-convex compact subset of a vector space

Let `F` be a finite-dimensional real normed space of dimension `d`, with a homological orientation
`o`, and let `K ⊆ F` be compact and star-convex about a point `y ∈ K`. Capping with the fundamental
class `μ_K ∈ H_d(F, F ∖ K; ℤ)` of `o` along `K` is bijective

`Hᵖ(F, F ∖ K; L) ⟶ H_q(F; L)`,  `p + q = d`,

for every abelian group `L`
(`TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClassOn_of_starConvex`). This is
the base case `M = ℝⁿ` of Hatcher's proof of Poincaré duality for noncompact manifolds
(Theorem 3.35): the duality map of `ℝⁿ` is the direct limit of these maps over compact
star-convex sets, which are cofinal among compact sets.

The two sides are concentrated in a single degree. Removing `K` or removing `y` gives homotopy
equivalent complements, so `Hᵖ(F, F ∖ K; L)` is the local cohomology `Hᵖ(F, F ∖ {y}; L)`
(`TauCeti.isIso_singularCohomologyMap_compl_of_starConvex`), which vanishes for `p ≠ d`; and `F`
is contractible, so `H_q(F; L)` vanishes for `q ≠ 0`. By naturality of the relative cap product,
capping with `μ_K` corresponds to capping with its restriction to `y`, the local orientation
`o y`. In the remaining degree `p = d`, `q = 0`, the augmentation `ε : H₀(F; L) ⟶ L` of a cap
product into degree zero is the Kronecker pairing (`TopPair.singularCap_comp_singularHomology₀ε`),
and the Kronecker pairing with a local orientation identifies `Hᵈ(F, F ∖ {y}; L)` with `L`
(`TauCeti.LocalOrientation.cohomologyEquiv`).

In particular, for an orientation `ω` of `F`, of dimension `n + 1`, capping the local orientation
selected by `ω` with the local cohomology generator selected by `ω` gives a class of augmentation
one in `H₀(F; ℤ)` (`Orientation.singularCap_localCohomologyClass_localOrientation`).

## Main results

* `Orientation.singularCap_localCohomologyClass_localOrientation`: `ε (μ₀ ⌢ u₀) = 1` for the local
  orientation `μ₀` and the local cohomology generator `u₀` selected by an orientation.
* `TauCeti.HomologicalOrientation.bijective_singularCap_fundamentalClassOn_of_starConvex`: capping
  with the fundamental class along a compact star-convex set is bijective in all degrees.

## Implementation notes

The coefficient conventions are those of `TauCeti.HomologicalOrientation.fundamentalClassOn`:
singular chains have the integral coefficients `ModuleCat.of ℤ (ULift ℤ)`, `Hᵖ(-; L)` is computed
from cochains on them with values in `L`, and the cap product pairs the two along the right
unitors `ℤ ⟶ ℤ ⊗ 𝟙` and `L ⊗ 𝟙 ⟶ L`. Instance search finds the `ℤ`-linear structure of
`ModuleCat ℤ` as a preadditive category, which is monoidal linear by the local instance
`CategoryTheory.MonoidalPreadditive.monoidalLinearInt`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the proof of Theorem 3.35, case `M = ℝⁿ`.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Module Simplicial

attribute [local instance] MonoidalPreadditive.monoidalLinearInt

namespace Orientation

open TauCeti

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}

/-- **Capping the local orientation with the dual local cohomology generator**: for an orientation
`ω` of a real normed space `F` of dimension `n + 1`, the cap product `μ₀ ⌢ u₀` of the local
orientation `μ₀ ∈ Hₙ₊₁(F, F ∖ {0}; ℤ)` and the local cohomology generator
`u₀ ∈ Hⁿ⁺¹(F, F ∖ {0}; ℤ)` selected by `ω` has augmentation one in `H₀(F; ℤ) ≅ ℤ`. -/
theorem singularCap_localCohomologyClass_localOrientation (ω : Orientation ℝ F (Fin (n + 1)))
    (hF : finrank ℝ F = n + 1) :
    (TopCat.of F).singularHomology₀ε (ModuleCat.of ℤ (ULift.{0} ℤ))
        (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of F))).singularCap ℤ (ρ_ _).inv (ρ_ _).hom
          (n + 1) 0 (n + 1) rfl (ω.localCohomologyClass hF)).hom
            (ω.localOrientation hF).val) = 1 :=
  (ConcreteCategory.congr_hom (TopPair.singularCap_comp_singularHomology₀ε _ ℤ (n + 1) rfl
    (ω.localCohomologyClass hF)) _).trans (ω.kronecker_localCohomologyClass hF)

end Orientation

namespace TauCeti.HomologicalOrientation

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {d : ℕ}
  (o : HomologicalOrientation F F d) (hd : finrank ℝ F = d) (L : ModuleCat.{0} ℤ)

/-- **Capping with the fundamental class along a compact star-convex set is bijective**: for a
compact set `K` in a finite-dimensional real normed space `F` of dimension `d`, star-convex about
a point `y ∈ K`, capping with the fundamental class `μ_K` of a homological orientation along `K`
is bijective `Hᵖ(F, F ∖ K; L) ⟶ H_q(F; L)` for every abelian group `L` and all `p + q = d`. -/
theorem bijective_singularCap_fundamentalClassOn_of_starConvex {K : Set F} (hK : IsCompact K)
    {y : F} (hKy : StarConvex ℝ y K) (hy : y ∈ K) (p q : ℕ) (h : p + q = d) :
    Function.Bijective fun α : (TopPair.ofSubset (Kᶜ : Set (TopCat.of F))).singularCohomology
        (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p ↦
      ((TopPair.ofSubset (Kᶜ : Set (TopCat.of F))).singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q d h
        α).hom (o.fundamentalClassOn hd hK) := by
  let P := TopPair.ofSubset (Kᶜ : Set (TopCat.of F))
  let Q := TopPair.ofSubset ({y}ᶜ : Set (TopCat.of F))
  let f : P ⟶ Q := TopPair.ofSubsetMap (𝟙 (TopCat.of F))
    (Set.compl_subset_compl.2 (Set.singleton_subset_iff.2 hy))
  -- Capping with the local orientation at `y`.
  let g : Q.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p →
      ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).obj (TopCat.of F) :=
    fun β ↦ (Q.singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q d h β).hom (o y).val
  -- By naturality of the cap product, capping the pull-back of a class with `μ_K` is capping the
  -- class with the restriction of `μ_K` to `y`, the local orientation at `y`.
  have hfg : (fun α ↦ (P.singularCap ℤ (ρ_ _).inv (ρ_ L).hom p q d h α).hom
      (o.fundamentalClassOn hd hK)) ∘ TopPair.singularCohomologyMap f p = g := by
    funext β
    have hfst : ((singularHomologyFunctor (ModuleCat.{0} ℤ) q).obj L).map (TopPair.Hom.fst f) =
        𝟙 _ := by
      rw [show TopPair.Hom.fst f = 𝟙 (TopCat.of F) from TopPair.ofSubsetMap_fst _ _]
      exact CategoryTheory.Functor.map_id _ _
    have hμ := o.localHomologyRestriction_fundamentalClassOn hd hK hy
    rw [localHomologyRestriction_def] at hμ
    have := ConcreteCategory.congr_hom (TopPair.singularCap_naturality f ℤ (ρ_ _).inv (ρ_ L).hom
      p q d h β) (o.fundamentalClassOn hd hK)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfst, hμ] at this
    exact (ConcreteCategory.id_apply _).symm.trans this
  have hf : IsIso (TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ)) (k := ℤ)
      (M := L) f p) :=
    isIso_singularCohomologyMap_compl_of_starConvex _ ℤ L hKy hy hK.isBounded p
  have hfb : Function.Bijective (TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{0} ℤ))
      (k := ℤ) (M := L) f p) :=
    ((asIso (TopPair.singularCohomologyMap f p)).toLinearEquiv).bijective
  refine (Function.Bijective.of_comp_iff _ hfb).1 ?_
  rw [hfg]
  have hy' : y ∈ (OpenPartialHomeomorph.refl F).source := Set.mem_univ y
  obtain rfl | hq := eq_or_ne q 0
  · -- In the top degree, the augmentation of the cap product with `o y` is the Kronecker pairing
    -- with `o y`, which identifies `Hᵈ(F, F ∖ {y}; L)` with `L`.
    obtain rfl : p = d := by omega
    subst hd
    let ε := asIso ((TopCat.of F).singularHomology₀ε L)
    refine (Function.Bijective.of_comp_iff' ε.toLinearEquiv.bijective g).1 ?_
    have hεg : ε.toLinearEquiv ∘ g =
        (o y).cohomologyEquiv (OpenPartialHomeomorph.refl F) hy' L := by
      funext β
      rw [Function.comp_apply, LocalOrientation.cohomologyEquiv_apply]
      exact ConcreteCategory.congr_hom (Q.singularCap_comp_singularHomology₀ε ℤ _ h β) _
    rw [hεg]
    exact LinearEquiv.bijective _
  · -- Otherwise both sides vanish: local cohomology is concentrated in degree `d`, and the
    -- homology of `F` in degree zero.
    -- `TauCeti.isZero_singularCohomology_complSingleton_of_ne` computes cohomology with the
    -- `ℤ`-linear structure of `ModuleCat ℤ` as a category of modules; it agrees with the one of a
    -- preadditive category, as a `ℤ`-module structure is unique.
    have : Subsingleton (Linear ℤ (ModuleCat.{0} ℤ)) := ⟨by
      rintro ⟨_, _, _⟩ ⟨_, _, _⟩
      congr
      exact Subsingleton.elim _ _⟩
    have h₁ : IsZero (Q.singularCohomology (ModuleCat.of ℤ (ULift.{0} ℤ)) ℤ L p) := by
      convert isZero_singularCohomology_complSingleton_of_ne (ModuleCat.of ℤ (ULift.{0} ℤ)) L
        (OpenPartialHomeomorph.refl F) hy' hd (by omega : p ≠ d)
    have h₂ := isZero_singularHomologyFunctor_of_contractibleSpace L (TopCat.of F) hq
    exact ⟨fun _ _ _ ↦ @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h₁) _ _,
      fun _ ↦ ⟨0, @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero h₂) _ _⟩⟩

end TauCeti.HomologicalOrientation
