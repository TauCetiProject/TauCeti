/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.Algebraize

/-!
# Affine charts of a base change and their finiteness

Let `f : X ⟶ S` be a morphism of schemes, `U` an affine open of `S`, `V ⊆ f⁻¹ U` an affine open
of `X`, and `R` a `Γ(S, U)`-algebra. Then `Spec (R ⊗[Γ(S, U)] Γ(X, V))` is an open of the base
change `X ×[S] Spec R`, with the evident projections, and for `e : R ⊗[Γ(S, U)] Γ(X, V)` the image
of the basic open `D(e)` is finite over `Spec R` as soon as `R → (R ⊗[Γ(S, U)] Γ(X, V))[1/e]` is
finite (`AlgebraicGeometry.exists_isOpenImmersion_tensor_isFinite`).

This is the chart in which an algebraic statement about `Γ(S, U) → Γ(X, V)`, such as Stacks 00UJ,
is turned into a finite open of a base change of `f`. It is the chart used in Mathlib's
`AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt` (Andrew Yang).

## References

* [Stacks Project, Tag 00UJ](https://stacks.math.columbia.edu/tag/00UJ)
-/

public section

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

universe u

/-- For affine opens `V ⊆ f⁻¹ U` and a `Γ(S, U)`-algebra `R`, the chart
`Spec (R ⊗[Γ(S, U)] Γ(X, V))` is an open of `X ×[S] Spec R`, with the evident projections, and
the image of `D(e)` is finite over `Spec R` whenever `R → (R ⊗[Γ(S, U)] Γ(X, V))[1/e]` is finite.
-/
lemma exists_isOpenImmersion_tensor_isFinite {X S : Scheme.{u}} (f : X ⟶ S)
    {U : S.Opens} (hU : IsAffineOpen U) {V : X.Opens} (hV : IsAffineOpen V) (hUV : V ≤ f ⁻¹ᵁ U)
    (R : Type u) [CommRing R] [Algebra Γ(S, U) R] :
    letI := (f.appLE U V hUV).hom.toAlgebra
    ∃ g : Spec ↧(R ⊗[Γ(S, U)] Γ(X, V)) ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) R)) ≫ hU.fromSpec),
      ∃ _ : IsOpenImmersion g, g ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫ hV.fromSpec ∧
      g ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(S, U)] Γ(X, V)))) ∧
      ∀ e : R ⊗[Γ(S, U)] Γ(X, V), (algebraMap R (Localization.Away e)).Finite →
        IsFinite ((g ''ᵁ PrimeSpectrum.basicOpen e).ι ≫ pullback.snd _ _) := by
  algebraize [(f.appLE U V hUV).hom]
  let φ : Γ(S, U) ⟶ ↧R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  let e₁ : Spec ↧(R ⊗ Γ(X, V)) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  have he₂ : e₁.hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(S, U)] Γ(X, V)))) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullbackSpecIso_inv_fst' ..
  let g : Spec ↧(R ⊗[Γ(S, U)] Γ(X, V)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  have : IsOpenImmersion g := by
    have := Scheme.pullback_map_isOpenImmersion (Spec.map (f.appLE U V hUV)) (Spec.map φ) f
      (Spec.map φ ≫ hU.fromSpec) hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
    exact IsOpenImmersion.comp _ _
  have hgfst : g ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫ hV.fromSpec := by
    simp [g, reassoc_of% he₁]
  have hgsnd : g ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(S, U)] Γ(X, V)))) := by
    simp [g, he₂]
  refine ⟨g, inferInstance, hgfst, hgsnd, fun e he ↦ ?_⟩
  -- The open `g(D(e))` is the image of `Spec (R ⊗ Γ(X, V))[1/e]`, which is finite over `Spec R`.
  let ι : Spec ↧(Localization.Away e) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
  have hrange : ι.opensRange = g ''ᵁ PrimeSpectrum.basicOpen e := by
    simp only [Scheme.Hom.opensRange_comp, ι]
    congr 1
    exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
  have hι : ι ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away e))) := by
    rw [Category.assoc, hgsnd, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]
  have : MorphismProperty.RespectsIso @IsFinite.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [← hrange, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
    (Scheme.Hom.isoOpensRange _).hom, Scheme.Hom.isoOpensRange_hom_ι_assoc, hι,
    IsFinite.SpecMap_iff]
  exact he


end AlgebraicGeometry
