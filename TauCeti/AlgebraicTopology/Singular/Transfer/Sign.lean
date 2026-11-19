/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient.Sign.Permutation
public import TauCeti.AlgebraicTopology.Singular.Transfer.PermutationLocalSystem
public import TauCeti.AlgebraicTopology.Singular.Twisted.Coefficients

/-!
# Singular homology of a double cover and the sign local system

Let `p : E ⟶ B` be a covering map and `σ : E → E` a continuous involution over `B`. The singular
homology of `E` is the homology of `B` twisted by the permutation local system of `p`
(`IsCoveringMap.singularHomologyPermutationIso`), and under this identification `σ_*` is induced
by the endomorphism moving the sheets by `σ`
(`IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom`). Antisymmetrization from the
permutation local system to the sign local system of `σ`
(`IsCoveringMap.permutationLocalSystemToSign`) changes sign when precomposed with that
endomorphism. So the composite

`Hₖ(E; R) ≅ Hₖ(B; R[p⁻¹ b]) ⟶ Hₖ(B; sign)`

satisfies `σ_* c ↦ -(image of c)`
(`IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`). When the fibres
are finite, reading functions on fibres as formal sums of sheets gives a morphism back
(`IsCoveringMap.signLocalSystemToPermutation`), and the round trip on `Hₖ(E; R)` is `1 - σ_*`
(`IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`).

When every fibre is a pair `{e, σ e}` with `σ e ≠ e`, the short exact sequence
`0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` (`IsCoveringMap.shortExact_signPermutationShortComplex`) has a
coefficient long exact sequence. It shows that a class `c ∈ Hₖ(E; R)` with `p_* c = 0` comes from
`Hₖ(B; sign)`
(`IsCoveringMap.exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq`), from a
unique class when `Hₖ₊₁(B; R) = 0`
(`IsCoveringMap.injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation`).

For the orientation double cover of a manifold with its deck involution, the sign local system is
the orientation local system, and the class of the fundamental class of the orientation cover is
the fundamental class of the manifold with orientation-twisted coefficients
(`TauCeti.Geometry.Manifold.Orientation.Cover.FundamentalClass`).

## Main results

* `IsCoveringMap.homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign`: antisymmetrizing
  the image of `σ_* c` gives the negative of antisymmetrizing the image of `c`.
* `IsCoveringMap.singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation`: the round
  trip through the sign local system is `1 - σ_*`.
* `IsCoveringMap.exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq` and
  `IsCoveringMap.injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation`: classes of
  a double cover killed by `p_*` come from the sign local system, uniquely when
  `Hₖ₊₁(B; R) = 0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H, for homology with local coefficients, the local
  system of a covering space and the orientation local system of a manifold.
-/

public section

noncomputable section

open CategoryTheory TauCeti.LocalCoefficientSystem

universe u

namespace IsCoveringMap

variable {E B : TopCat.{u}} {p : E ⟶ B} (hp : IsCoveringMap p) (R : Type u) [Ring R]
  {σ : C(E, E)} (hσ : ⇑p ∘ ⇑σ = ⇑p) (hσσ : Function.Involutive σ)

/-- **Antisymmetrizing anti-commutes with an involution over the base**: for the composite
`Hₖ(E; R) ≅ Hₖ(B; R[p⁻¹ b]) ⟶ Hₖ(B; sign)`, the image of `σ_* c` is the negative of the image
of `c`. -/
theorem homologyMap_comp_singularHomologyPermutationIso_hom_comp_toSign (k : ℕ) :
    SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k ≫
        (hp.singularHomologyPermutationIso R k).hom ≫
          twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k =
      -((hp.singularHomologyPermutationIso R k).hom ≫
          twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k) := by
  rw [homologyMap_comp_singularHomologyPermutationIso_hom_assoc hp R σ hσ,
    ← twistedHomologyCoefficientMap_comp, permutationLocalSystemFiberMap_comp_toSign,
    twistedHomologyCoefficientMap_neg, Preadditive.comp_neg]

variable (hfin : ∀ b, Finite (p ⁻¹' {b}))

/-- **The round trip through the sign local system is `1 - σ_*`**: antisymmetrizing the image of
a class `c ∈ Hₖ(E; R)` in `Hₖ(B; R[p⁻¹ b])`, reading it back as a formal sum of sheets and
returning to `Hₖ(E; R)` gives `c - σ_* c`. -/
theorem singularHomologyPermutationIso_hom_comp_toSign_comp_toPermutation (k : ℕ) :
    (hp.singularHomologyPermutationIso R k).hom ≫
        twistedHomologyCoefficientMap (hp.permutationLocalSystemToSign R hσ hσσ) k ≫
          twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k ≫
            (hp.singularHomologyPermutationIso R k).inv =
      𝟙 _ - SSet.homologyMap (TopCat.toSSet.map (TopCat.ofHom σ)) (ModuleCat.of R R) k := by
  rw [← twistedHomologyCoefficientMap_comp_assoc,
    permutationLocalSystemToSign_comp_toPermutation, twistedHomologyCoefficientMap_sub,
    twistedHomologyCoefficientMap_id, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Iso.hom_inv_id, ← homologyMap_comp_singularHomologyPermutationIso_hom_assoc,
    Iso.hom_inv_id, Category.comp_id]

section DoubleCover

variable (hfix : ∀ e, σ e ≠ e) (hfib : ∀ e e', p e' = p e → e' = e ∨ e' = σ e)
  (hsurj : Function.Surjective p)

include hσσ hfix hfib hsurj in
/-- **Reading sign classes as classes of the cover is injective below a vanishing degree**: for a
double cover, if `Hₖ₊₁(B; R) = 0` then the map `Hₖ(B; sign) ⟶ Hₖ(B; R[p⁻¹ b])` reading functions
on fibres as formal sums of sheets is injective, by the coefficient long exact sequence of
`0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0`. -/
theorem injective_twistedHomologyCoefficientMap_signLocalSystemToPermutation (k : ℕ)
    (hk : Limits.IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) (k + 1)).obj
      (ModuleCat.of R R)).obj B)) :
    Function.Injective
      (twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k).hom := by
  have hS := hp.shortExact_signPermutationShortComplex R hσ hσσ hfin hfix hfib hsurj
  have := (hS.twistedHomology_exact₁ (k + 1) k rfl).mono_g
    ((hk.of_iso (twistedHomologyConstantIso B (ModuleCat.of R R) (k + 1))).eq_of_src _ _)
  exact (ModuleCat.mono_iff_injective _).1 this

include hσσ hfix hfib hsurj in
/-- **Classes of the cover killed by the projection come from the sign local system**: for a
double cover, a class `c ∈ Hₖ(E; R)` with `p_* c = 0` is, as a class of `B` twisted by the
permutation local system, the image of a class of `Hₖ(B; sign)` read as formal sums of sheets.
This is exactness of the coefficient long exact sequence of `0 ⟶ sign ⟶ R[p⁻¹ b] ⟶ R ⟶ 0` at
`Hₖ(B; R[p⁻¹ b])`. -/
theorem exists_twistedHomologyCoefficientMap_signLocalSystemToPermutation_eq (k : ℕ)
    (c : ((TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R))
    (hc : (SSet.homologyMap (TopCat.toSSet.map p) (ModuleCat.of R R) k).hom c = 0) :
    ∃ g, (twistedHomologyCoefficientMap (hp.signLocalSystemToPermutation R hσ hfin) k).hom g =
      (hp.singularHomologyPermutationIso R k).hom.hom c := by
  have hS := hp.shortExact_signPermutationShortComplex R hσ hσσ hfin hfix hfib hsurj
  refine (ShortComplex.moduleCat_exact_iff _).1 (hS.twistedHomology_exact₂ k) _ ?_
  -- The augmentation of the image of `c` is `p_* c = 0`.
  have h := congrArg (fun φ ↦ φ.hom c) (hp.singularHomologyPermutationIso_hom_comp_augmentation R k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine (ModuleCat.mono_iff_injective
    (twistedHomologyConstantIso B (ModuleCat.of R R) k).hom).1 inferInstance ?_
  exact h.trans (hc.trans (map_zero _).symm)

end DoubleCover

end IsCoveringMap
