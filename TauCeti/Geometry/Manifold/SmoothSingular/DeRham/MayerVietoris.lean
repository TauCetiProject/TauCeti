/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Basic
public import TauCeti.Geometry.Manifold.DeRham.MayerVietoris
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.SmoothSingular.MayerVietoris
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Module
import TauCeti.Geometry.Manifold.SmoothSingular.DeRham.Theorem

/-!
# The de Rham homomorphism and the Mayer–Vietoris connecting maps

Let `M` be a Hausdorff `σ`-compact smooth manifold modelled on a finite-dimensional real model
with corners, and let `U` and `V` be open subsets with `U ⊔ V = ⊤`. This file proves that the de
Rham homomorphism `TauCeti.deRhamHom` intertwines the connecting map
`TauCeti.deRhamCohomology.mayerVietorisδ : H^k_dR(U ⊓ V) → H^{k+1}_dR(U ⊔ V)` of de Rham
cohomology with the connecting map `TopCat.singularCohomologyMayerVietorisδ` of singular cohomology
(`TauCeti.deRhamHom_map_mayerVietorisδ`). Together with the naturality of the de Rham homomorphism
under restriction, this makes the de Rham homomorphism a map from the de Rham Mayer–Vietoris
sequence to the singular one, so by the five lemma it is bijective on `M` once it is bijective on
`U`, on `V` and on `U ⊓ V` (`TauCeti.bijective_deRhamHom_of_sup_eq_top`). This is the
Mayer–Vietoris step of the de Rham theorem.

**The proof.** Integration of forms over smooth singular simplices is a morphism from the
Mayer–Vietoris short exact sequence of de Rham complexes
`Ω^•(U ⊔ V) ⟶ Ω^•(U) ⊞ Ω^•(V) ⟶ Ω^•(U ⊓ V)` (`TauCeti.mayerVietorisShortComplex`) to the cochain
Mayer–Vietoris sequence of the pushout square of smooth singular simplices of `U ⊓ V`, `U`, `V`
and of the smooth singular simplices of `M` lying in `U` or in `V`
(`TauCeti.isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex`). On the first
term it is integration over `M` followed by restriction to those small smooth simplices. That this
is a morphism of short complexes is the naturality of integration
(`TauCeti.deRhamIntegration_naturality`); since connecting morphisms are natural, integration
carries the de Rham connecting map to the cochain connecting map of the smooth square.

On the singular side, the inclusion of the smooth square into the square of singular simplices of
`U ⊓ V`, `U`, `V` and of the singular simplices of `M` lying in `U` or in `V` is a map of pushout
squares, so the cochain connecting maps of the two squares correspond under restriction
(`SSet.mayerVietorisCochainδ_naturality`). The singular connecting map is, after restriction to
the singular simplices lying in `U` or in `V`, the cochain connecting map of the singular square
(`TopCat.singularCohomologyMayerVietorisδ_comp_homologyMap`).

Both sides of the identity are therefore equal after restriction from all singular simplices of
`M` to its smooth simplices lying in `U` or in `V`. That restriction is a quasi-isomorphism
(`TauCeti.quasiIso_cochainComplexMap_smallSmoothSingularSubcomplex_ι`), by the smoothing theorem
and the small-chain theorem for affinely stable subcomplexes, so it is injective on cohomology.

## Main results

* `TauCeti.deRhamHom_map_mayerVietorisδ`: for open subsets `U` and `V` with `U ⊔ V = ⊤`, the de
  Rham homomorphism carries the de Rham Mayer–Vietoris connecting map to the singular one.
* `TauCeti.bijective_deRhamHom_of_sup_eq_top`: if the de Rham homomorphism is bijective in every
  degree on `U`, on `V` and on `U ⊓ V`, where `U ⊔ V = ⊤`, then it is bijective in every degree on
  `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 18.13 and the proof of Theorem 18.14.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace SSet.Subcomplex
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
/-- Integrating over `M` a form on `U ⊔ V = ⊤` and restricting to the smooth simplices of an open
subset `W` lying in a member of the cover is restricting the form to `W` and integrating over
`W`. -/
private theorem integration_toSmallSmoothSingularSubcomplex (U V W : Opens M) (hUV : U ⊔ V = ⊤)
    (hWUV : W ≤ U ⊔ V) {i : Fin 2} (hW : (W : Set M) ⊆ ![(U : Set M), (V : Set M)] i) :
    deRhamComplex.map (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm
        (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm.contMDiff ≫
      deRhamIntegration I M ≫
        SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
          (homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
            ![(U : Set M), (V : Set M)])) ≫
          SSet.cochainComplexMap (toSmallSmoothSingularSubcomplex I _ hW) =
      deRhamComplex.map (Opens.inclusion hWUV) (contMDiff_inclusion _) ≫
        deRhamIntegration I W := by
  rw [← SSet.cochainComplexMap_comp, toSmallSmoothSingularSubcomplex_homOfLE_left,
    ← deRhamIntegration_naturality, ← Category.assoc, ← deRhamComplex.map_comp]
  congr 2
  exact funext fun x ↦ Subtype.ext (Diffeomorph.coe_ofTop_symm_apply (x : M))

/-- Integration of forms over smooth singular simplices, as a morphism from the Mayer–Vietoris
short complex of de Rham complexes of an open cover `U ⊔ V = ⊤` to the cochain Mayer–Vietoris
sequence of the smooth singular simplices of `U ⊓ V`, `U`, `V` and of the smooth singular simplices
of `M` lying in `U` or in `V`. On the first term it is integration over `M`, through `U ⊔ V = M`,
followed by restriction to those small smooth simplices. -/
private def mayerVietorisIntegration (U V : Opens M) (hUV : U ⊔ V = ⊤) :
    mayerVietorisShortComplex I U V ⟶
      SSet.mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V).toCommSq
    where
  τ₁ := (deRhamComplex.map (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm
      (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm.contMDiff ≫
    deRhamIntegration I M ≫
      SSet.cochainComplexMap
        (homOfLE (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
          ![(U : Set M), (V : Set M)])) : deRhamComplex I (U ⊔ V : Opens M) ⟶ _)
  τ₂ := biprod.map (deRhamIntegration I U) (deRhamIntegration I V)
  τ₃ := deRhamIntegration I (U ⊓ V : Opens M)
  comm₁₂ := by
    -- Restricting to `U` (or `V`) and integrating is integrating over `M` and restricting to the
    -- smooth simplices of `U` (or `V`), by naturality of integration.
    -- Expose the first maps of the two short complexes as biproduct lifts. The de Rham one is
    -- unfolded rather than rewritten with `mayerVietorisShortComplex_f`, since the composites in
    -- the goal are typed by the terms `(mayerVietorisShortComplex I U V).Xᵢ`, which a rewrite of
    -- the map alone would leave ill-typed; the singular one is an `abbrev`.
    dsimp only [mayerVietorisShortComplex]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
      exact integration_toSmallSmoothSingularSubcomplex I U V U hUV le_sup_left _
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
      exact integration_toSmallSmoothSingularSubcomplex I U V V hUV le_sup_right _
  comm₂₃ := by
    -- Expose the second maps of the two short complexes as biproduct descents, unfolding the de
    -- Rham short complex as in `comm₁₂`.
    dsimp only [mayerVietorisShortComplex]
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc,
        deRhamIntegration_naturality]
    · rw [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, deRhamIntegration_naturality]

/-- On the de Rham side: restricted to the smooth singular simplices of `M` lying in `U` or in `V`,
the de Rham homomorphism of the image of `c` under the de Rham connecting map is the cochain
connecting map of the smooth square applied to the integration of `c`, since integration is a
morphism of the Mayer–Vietoris short exact sequences. -/
private theorem homologyMap_ι_deRhamHom_map_mayerVietorisδ (U V : Opens M) (hUV : U ⊔ V = ⊤)
    (k : ℕ) (c : deRhamCohomology I (U ⊓ V : Opens M) k) :
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
          (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι) (k + 1)
        (deRhamHom I M (k + 1)
          (deRhamCohomology.map (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm
            (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm.contMDiff (k + 1)
            (deRhamCohomology.mayerVietorisδ I U V k c))) =
      SSet.mayerVietorisCochainδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) k (k + 1)
        rfl (deRhamCohomology.integration I (U ⊓ V : Opens M) k c) := by
  let Φ := mayerVietorisIntegration I U V hUV
  have hS₁ := mayerVietorisShortComplex_shortExact (I := I) U V
  have hS₂ := SSet.shortExact_mayerVietorisCochainShortComplex (ModuleCat.of ℝ ℝ) ℝ
    (ModuleCat.of ℝ ℝ)
    (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V)
  have hdR := ConcreteCategory.congr_hom
    (HomologicalComplex.HomologySequence.δ_naturality Φ hS₁ hS₂ k (k + 1) rfl) c
  -- Evaluate the composites at `c`. Rewriting with `ConcreteCategory.comp_apply` fails here, since
  -- `c` is typed as a de Rham class rather than as a homology class of the short complex's term.
  change HomologicalComplex.homologyMap Φ.τ₁ (k + 1) (hS₁.δ k (k + 1) rfl c) =
    hS₂.δ k (k + 1) rfl (HomologicalComplex.homologyMap Φ.τ₃ k c) at hdR
  have hint : deRhamCohomology.integration I (U ⊓ V : Opens M) k c =
      HomologicalComplex.homologyMap Φ.τ₃ k c :=
    (ConcreteCategory.congr_hom
      (deRhamCohomology.homologyMap_deRhamIntegration I (U ⊓ V : Opens M) k) c).symm
  -- Restriction to small smooth simplices factors through smooth simplices, where the de Rham
  -- homomorphism is integration.
  rw [← homOfLE_ι (smallSmoothSingularSubcomplex_le_smoothSingularSubcomplex I
      ![(U : Set M), (V : Set M)]), SSet.cochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply,
    homologyMap_cochainComplexMap_deRhamHom,
    SSet.mayerVietorisCochainδ_def (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) _ k (k + 1) rfl, hint]
  refine Eq.trans ?_ ((congrArg _ (ConcreteCategory.congr_hom
    (deRhamCohomology.ofHom_mayerVietorisδ (I := I) U V k) c)).trans hdR)
  -- Unfold the first component of `Φ`, a composite of three cochain maps.
  change _ = HomologicalComplex.homologyMap (deRhamComplex.map _ _ ≫ deRhamIntegration I M ≫
    SSet.cochainComplexMap _) (k + 1) _
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, deRhamComplex.homologyMap_map,
    deRhamCohomology.homologyMap_deRhamIntegration, ModuleCat.ofHom_apply, ModuleCat.ofHom_apply,
    ModuleCat.ofHom_apply]

omit [SigmaCompactSpace M] in
/-- On the singular side: restricted to the smooth singular simplices of `M` lying in `U` or in
`V`, the singular connecting map of the de Rham homomorphism of `c` is the cochain connecting map
of the smooth square applied to the integration of `c`, by naturality of cochain connecting maps
under the inclusion of the smooth square into the singular one. -/
private theorem homologyMap_ι_singularCohomologyMayerVietorisδ_deRhamHom (U V : Opens M)
    (hUV : U ⊔ V = ⊤) [SigmaCompactSpace (U ⊓ V : Opens M)] (k : ℕ)
    (c : deRhamCohomology I (U ⊓ V : Opens M) k) :
    HomologicalComplex.homologyMap
        (SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
          (smallSmoothSingularSubcomplex I ![(U : Set M), (V : Set M)]).ι) (k + 1)
        (TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
          (X := TopCat.of M) U.isOpen V.isOpen
          (by rw [← Opens.coe_sup, hUV, Opens.coe_top]) k (k + 1) rfl
          (deRhamHom I (U ⊓ V : Opens M) k c)) =
      SSet.mayerVietorisCochainδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V) k (k + 1)
        rfl (deRhamCohomology.integration I (U ⊓ V : Opens M) k c) := by
  have hsing := ConcreteCategory.congr_hom
    (SSet.mayerVietorisCochainδ_naturality (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
      (sq := isPushout_smoothSingularSubcomplex_inter_smallSmoothSingularSubcomplex I U V)
      (sq' := TopCat.isPushout_toSSet_inter_smallSingularSubcomplex (X := TopCat.of M)
        (U : Set M) (V : Set M))
      (ht := smoothSingularSubcomplexMap_inclusion_ι (inf_le_left : U ⊓ V ≤ U))
      (hl := smoothSingularSubcomplexMap_inclusion_ι (inf_le_right : U ⊓ V ≤ V))
      (hr := toSmallSmoothSingularSubcomplex_homOfLE_right _ _)
      (hb := toSmallSmoothSingularSubcomplex_homOfLE_right _ _) (n := k) (m := k + 1) (h := rfl))
    (deRhamHom I (U ⊓ V : Opens M) k c)
  have hδ := ConcreteCategory.congr_hom
    (TopCat.singularCohomologyMayerVietorisδ_comp_homologyMap (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen
      (by rw [← Opens.coe_sup, hUV, Opens.coe_top]) k (k + 1) rfl)
    (deRhamHom I (U ⊓ V : Opens M) k c)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hsing
  rw [ConcreteCategory.comp_apply] at hδ
  -- Restriction to small smooth simplices factors through small singular simplices.
  rw [← homOfLE_ι (smallSmoothSingularSubcomplex_le_smallSingularSubcomplex I
      ![(U : Set M), (V : Set M)]), SSet.cochainComplexMap_comp,
    HomologicalComplex.homologyMap_comp, ConcreteCategory.comp_apply, hδ, hsing,
    homologyMap_cochainComplexMap_deRhamHom]

/-- **The de Rham homomorphism intertwines the Mayer–Vietoris connecting maps.** Let `U` and `V`
be open subsets of `M` with `U ⊔ V = ⊤`. For a de Rham class `c` on `U ⊓ V`, the de Rham
homomorphism of `M` sends the image of `c` under the de Rham Mayer–Vietoris connecting map,
carried from `U ⊔ V` to `M`, to the image under the singular Mayer–Vietoris connecting map of the
de Rham homomorphism of `U ⊓ V` applied to `c`. The `σ`-compactness of `U ⊓ V`, which the de Rham
homomorphism of `U ⊓ V` requires, holds automatically
(`TauCeti.Manifold.sigmaCompactSpace_opens`). -/
theorem deRhamHom_map_mayerVietorisδ (U V : Opens M) (hUV : U ⊔ V = ⊤)
    [SigmaCompactSpace (U ⊓ V : Opens M)] (k : ℕ)
    (c : deRhamCohomology I (U ⊓ V : Opens M) k) :
    deRhamHom I M (k + 1)
        (deRhamCohomology.map (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm
          (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm.contMDiff (k + 1)
          (deRhamCohomology.mayerVietorisδ I U V k c)) =
      TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (X := TopCat.of M) U.isOpen V.isOpen
        (by rw [← Opens.coe_sup, hUV, Opens.coe_top]) k (k + 1) rfl
        (deRhamHom I (U ⊓ V : Opens M) k c) := by
  have := quasiIso_cochainComplexMap_smallSmoothSingularSubcomplex_ι I M (ModuleCat.of ℝ ℝ) ℝ
    (ModuleCat.of ℝ ℝ) ![(U : Set M), (V : Set M)] (U.isOpen.vecCons V.isOpen)
    (by rw [Set.iUnion_vecCons_pair, ← Opens.coe_sup, hUV, Opens.coe_top])
  -- Both sides agree after restriction to the smooth simplices lying in `U` or in `V`, which is a
  -- quasi-isomorphism and so injective on cohomology.
  exact (ModuleCat.mono_iff_injective _).1 inferInstance
    ((homologyMap_ι_deRhamHom_map_mayerVietorisδ I U V hUV k c).trans
      (homologyMap_ι_singularCohomologyMayerVietorisδ_deRhamHom I U V hUV k c).symm)

/-- The de Rham homomorphism of an open subset `W ≤ U ⊔ V = ⊤` of `M`, applied to the restriction
to `W` of a class on `U ⊔ V` carried from `M`, is the singular restriction to `W` of the de Rham
homomorphism of `M` applied to that class. -/
private theorem deRhamHom_map_inclusion_equivOfDiffeomorph_symm (U V W : Opens M)
    (hUV : U ⊔ V = ⊤) (hW : W ≤ U ⊔ V) [SigmaCompactSpace W] (k : ℕ)
    (x : deRhamCohomology I M k) :
    deRhamHom I W k (deRhamCohomology.map (Opens.inclusion hW) (contMDiff_inclusion hW) k
        ((deRhamCohomology.equivOfDiffeomorph
          (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm k).symm x)) =
      TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal (W : Set M))) k
        (deRhamHom I M k x) := by
  set T := Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV
  have hcomp : (T.symm.symm ∘ Opens.inclusion hW : W → M) = Subtype.val := funext fun y ↦ by
    have hy : Opens.inclusion hW y = T.symm (y : M) :=
      Subtype.ext (Diffeomorph.coe_ofTop_symm_apply (y : M)).symm
    rw [Function.comp_apply, hy, Diffeomorph.symm_apply_apply]
  have h := LinearMap.congr_fun (deRhamCohomology.map_comp (Opens.inclusion hW) T.symm.symm
    (contMDiff_inclusion hW) T.symm.symm.contMDiff k) x
  rw [LinearMap.comp_apply] at h
  rw [deRhamCohomology.equivOfDiffeomorph_symm_apply, ← h,
    deRhamCohomology.map_congr _ contMDiff_subtypeVal hcomp]
  exact deRhamHom_map contMDiff_subtypeVal k x

omit [SigmaCompactSpace M] in
/-- The de Rham homomorphism carries the difference of the de Rham restrictions from `U` and `V`
to `U ⊓ V` to the difference of the singular restrictions. -/
private theorem singularCohomologyMayerVietorisFromProd_comp_prodMap_deRhamHom (U V : Opens M)
    [SigmaCompactSpace U] [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)] (n : ℕ) :
    TopCat.singularCohomologyMayerVietorisFromProd (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (X := TopCat.of M) U V n ∘ₗ (deRhamHom I U n).prodMap (deRhamHom I V n) =
      deRhamHom I (U ⊓ V : Opens M) n ∘ₗ deRhamCohomology.mayerVietorisFromProd I U V n := by
  refine LinearMap.ext fun x ↦ ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.prodMap_apply,
    TopCat.singularCohomologyMayerVietorisFromProd_apply,
    deRhamCohomology.mayerVietorisFromProd_apply, map_sub, deRhamHom_map (contMDiff_inclusion _),
    deRhamHom_map (contMDiff_inclusion _)]
  -- The inclusions of `U ⊓ V` as an open subset and as the intersection `U ∩ V` are the same
  -- continuous map.
  rfl

/-- **The Mayer–Vietoris step of the de Rham theorem.** Let `U` and `V` be open subsets of `M`
with `U ⊔ V = ⊤`. If the de Rham homomorphism is bijective in every degree on `U`, on `V` and on
`U ⊓ V`, then it is bijective in every degree on `M`. In degree zero this holds on every manifold
(`TauCeti.bijective_deRhamHom_zero`); in positive degrees it is the five lemma applied to the
Mayer–Vietoris sequences, which the de Rham homomorphism intertwines
(`TauCeti.deRhamHom_map_mayerVietorisδ`). The `σ`-compactness of the open subsets holds
automatically (`TauCeti.Manifold.sigmaCompactSpace_opens`). -/
theorem bijective_deRhamHom_of_sup_eq_top (U V : Opens M) (hUV : U ⊔ V = ⊤)
    [SigmaCompactSpace U] [SigmaCompactSpace V] [SigmaCompactSpace (U ⊓ V : Opens M)]
    (hU : ∀ k, Function.Bijective (deRhamHom I U k))
    (hV : ∀ k, Function.Bijective (deRhamHom I V k))
    (hUV' : ∀ k, Function.Bijective (deRhamHom I (U ⊓ V : Opens M) k)) (k : ℕ) :
    Function.Bijective (deRhamHom I M k) := by
  obtain _ | n := k
  · exact bijective_deRhamHom_zero I M
  let e := deRhamCohomology.equivOfDiffeomorph
    (Diffeomorph.ofTop (I := I) (n := ∞) (U ⊔ V) hUV).symm (n + 1)
  have hcov : (U : Set M) ∪ V = Set.univ := by rw [← Opens.coe_sup, hUV, Opens.coe_top]
  -- The five lemma, for the de Rham sequence carried to `M` and the singular sequence.
  refine LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := deRhamCohomology.mayerVietorisFromProd I U V n)
    (f₂ := (e : _ →ₗ[ℝ] _) ∘ₗ deRhamCohomology.mayerVietorisδ I U V n)
    (f₃ := deRhamCohomology.mayerVietorisToProd I U V (n + 1) ∘ₗ (e.symm : _ →ₗ[ℝ] _))
    (f₄ := deRhamCohomology.mayerVietorisFromProd I U V (n + 1))
    (i₁ := (deRhamHom I U n).prodMap (deRhamHom I V n))
    (i₂ := deRhamHom I (U ⊓ V : Opens M) n) (i₃ := deRhamHom I M (n + 1))
    (i₄ := (deRhamHom I U (n + 1)).prodMap (deRhamHom I V (n + 1)))
    (i₅ := deRhamHom I (U ⊓ V : Opens M) (n + 1))
    (hf₁ := LinearEquiv.postcomp_exact_iff_exact.2
      (deRhamCohomology.exact_mayerVietorisFromProd_δ U V n))
    (hf₂ := (LinearEquiv.conj_exact_iff_exact _ _ e).2
      (deRhamCohomology.exact_mayerVietorisδ_toProd U V n))
    (hf₃ := LinearEquiv.precomp_exact_iff_exact.2
      (deRhamCohomology.exact_mayerVietorisToProd_fromProd U V (n + 1)))
    (hg₁ := TopCat.exact_singularCohomologyMayerVietorisFromProd_δ (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov n (n + 1) rfl)
    (hg₂ := TopCat.exact_singularCohomologyMayerVietorisδ_toProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov n (n + 1) rfl)
    (hg₃ := TopCat.exact_singularCohomologyMayerVietorisToProd_fromProd (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) (X := TopCat.of M) U.isOpen V.isOpen hcov (n + 1))
    (hc₁ := ?_) (hc₂ := ?_) (hc₃ := ?_) (hc₄ := ?_)
    (hi₁ := ?_) (hi₂ := hUV' n) (hi₄ := ?_) (hi₅ := (hUV' (n + 1)).1)
  -- The de Rham homomorphism commutes with restrictions and with the connecting maps.
  · exact singularCohomologyMayerVietorisFromProd_comp_prodMap_deRhamHom I U V n
  · refine LinearMap.ext fun c ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e,
      deRhamCohomology.equivOfDiffeomorph_apply]
    exact (deRhamHom_map_mayerVietorisδ I U V hUV n c).symm
  · refine LinearMap.ext fun x ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.prodMap_apply,
      TopCat.singularCohomologyMayerVietorisToProd_apply, LinearEquiv.coe_coe,
      deRhamCohomology.mayerVietorisToProd_apply,
      deRhamHom_map_inclusion_equivOfDiffeomorph_symm I U V U hUV le_sup_left,
      deRhamHom_map_inclusion_equivOfDiffeomorph_symm I U V V hUV le_sup_right]
  · exact singularCohomologyMayerVietorisFromProd_comp_prodMap_deRhamHom I U V (n + 1)
  · rw [LinearMap.coe_prodMap]
    exact (hU n).2.prodMap (hV n).2
  · rw [LinearMap.coe_prodMap]
    exact (hU (n + 1)).prodMap (hV (n + 1))

end TauCeti
