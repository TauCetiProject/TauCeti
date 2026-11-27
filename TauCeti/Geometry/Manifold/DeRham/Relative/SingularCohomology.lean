/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.HomotopyCategory.MappingCocone.ShortExact
public import TauCeti.Geometry.Manifold.DeRham.Relative.Integration
public import TauCeti.Geometry.Manifold.SmoothSingular.Relative
public import TauCeti.Geometry.Manifold.SmoothSingular.SingularCohomology

/-!
# The relative de Rham homomorphism

Let `W` be an open subset of a manifold `M`. Relative integration
`TauCeti.relativeDeRhamIntegration` is a cochain map from the relative de Rham complex of `(M, W)`
to the mapping cocone `TauCeti.relativeSmoothCochainComplex I W` of the restriction of real smooth
singular cochains from `M` to `W`. That cocone is a model of, but not literally, the relative
smooth singular cochain complex `Hom(C^∞(M)/C^∞(W), ℝ)`, the cochains of the smooth singular pair
`TauCeti.smoothSingularPair I W`; this file compares the two.

Restriction of smooth cochains is surjective: the smooth simplices of `W` are among those of `M`,
and a cochain on them extends by zero. So the cochains of the pair form a short exact sequence

`0 → C^*(M, W) → C^*(M) → C^*(W) → 0`,

which we extend by zero to `ℤ` (`TauCeti.smoothCochainShortComplex`). Its first map is the
inclusion of relative cochains (`TauCeti.smoothCochainShortComplex_f`) and its second map is the
restriction of smooth cochains (`TauCeti.smoothCochainShortComplex_g`). For any short exact
sequence the first map lifts to the mapping cocone of the second, `a ↦ (a, 0)`, and this lift is a
quasi-isomorphism (`CochainComplex.mappingCocone.quasiIso_lift_of_shortExact`). The lift
`TauCeti.relativeSmoothCochainLift I W` thus identifies the cohomology of the cocone with smooth
relative cohomology (`TauCeti.relativeSmoothCohomologyIso`). There is no canonical cochain map in
the other direction.

Relative integration followed on cohomology by the inverse of this lift is
`TauCeti.relativeDeRhamCohomology.integration`, from `H^n(M, W)` to smooth relative cohomology. It
is compatible with both long exact sequences of the pair:

* with the maps to absolute cohomology, `H^n(M, W) → H^n_dR(M)`
  (`TauCeti.relativeDeRhamCohomology.π`) and `H^n_∞(M, W) → H^n_∞(M)`, where absolute integration
  is `TauCeti.deRhamCohomology.integration`
  (`TauCeti.relativeDeRhamCohomology.homologyMap_cochainComplexπ_integration`);
* with the connecting maps, sign included: the de Rham connecting map is `δ [b] = -[(0, b)]`
  (`TauCeti.relativeDeRhamCohomology.δ_mk`), and integration carries it to the connecting map of
  the short exact sequence of smooth cochains
  (`TauCeti.relativeDeRhamCohomology.integration_δ`).

The sign works out because the lift carries the connecting map of the sequence to the class of
`inr b`, which in relative coordinates is `(0, -b)`
(`CochainComplex.mappingCocone.moduleCat_homologyMap_lift_δ_homologyπ`).

On a Hausdorff `σ`-compact manifold modelled on a finite-dimensional real model with corners, the
relative smoothing theorem identifies smooth relative cohomology with relative singular cohomology
(`TauCeti.smoothSingularRelativeCohomologyIso`). Composing with its inverse gives the **relative de
Rham homomorphism**

`TauCeti.relativeDeRhamHom I W n : H^n(M, W) →ₗ[ℝ] Hⁿ(M, W; ℝ)`,

compatible with the absolute de Rham homomorphism `TauCeti.deRhamHom`
(`TauCeti.singularCohomologyπ_relativeDeRhamHom`) and with the connecting maps of relative
singular cohomology (`TauCeti.relativeDeRhamHom_δ`).

## Main definitions and results

* `TauCeti.smoothCochainShortComplex I W`: the short exact sequence of real smooth singular
  cochains of the pair `(M, W)`, extended by zero to `ℤ`.
* `TauCeti.relativeSmoothCochainLift I W`: the quasi-isomorphism from relative smooth cochains to
  the mapping cocone of restriction.
* `TauCeti.relativeSmoothCohomologyIso I W n`: the induced isomorphism on cohomology.
* `TauCeti.relativeDeRhamCohomology.integration I W n`: relative integration on cohomology, with
  values in smooth relative cohomology.
* `TauCeti.relativeDeRhamHom I W n`: the relative de Rham homomorphism into relative singular
  cohomology.
* `TauCeti.relativeDeRhamCohomology.homologyMap_cochainComplexπ_integration`,
  `TauCeti.singularCohomologyπ_relativeDeRhamHom`: compatibility with the maps to absolute
  cohomology.
* `TauCeti.relativeDeRhamCohomology.integration_δ`, `TauCeti.relativeDeRhamHom_δ`: compatibility
  with the connecting maps.

## References

* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, Graduate Texts in Mathematics
  82, Springer, 1982, Chapter I, §6 (the relative de Rham complex as a mapping cocone).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 18 (the de Rham homomorphism).
-/

public section

noncomputable section

open CategoryTheory HomologicalComplex TopologicalSpace
open scoped ContDiff

namespace TauCeti

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type} [TopologicalSpace M] [ChartedSpace H M] (W : Opens M)

/-- The complex of real smooth singular chains of `X`. -/
local notation "𝒮[" X "]" =>
  SSet.chainComplex (smoothSingularSubcomplex I X : SSet) (ModuleCat.of ℝ ℝ)

/-- The complex of real smooth singular cochains of `X`. -/
local notation "𝒞[" X "]" => ChainComplex.linearYonedaObj 𝒮[X] ℝ (ModuleCat.of ℝ ℝ)

/-- The complex of real smooth relative singular cochains of the pair `(M, U)`. -/
local notation "𝒞ᵣ[" U "]" => ChainComplex.linearYonedaObj
  (SSetPair.chainComplex (smoothSingularPair I U) (ModuleCat.of ℝ ℝ)) ℝ (ModuleCat.of ℝ ℝ)

/-- Relative smooth cochains restrict to zero on `W`. -/
theorem extendMap_cochainComplexπ_comp_smoothCochainRestriction :
    extendMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
      (smoothSingularPair I W)) ComplexShape.embeddingUpNat ≫ smoothCochainRestriction I W = 0 := by
  rw [smoothCochainRestriction_def]
  exact (extendMap_comp _ _ _).symm.trans ((congrArg (extendMap · ComplexShape.embeddingUpNat)
    (((smoothSingularPair I W).chainComplexShortComplex (ModuleCat.of ℝ ℝ)).op.map
      (ChainComplex.linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ))).zero).trans (extendMap_zero _ _ _))

/-- The sequence `0 → C^*(M, W) → C^*(M) → C^*(W) → 0` of real smooth singular cochains of the open
pair `(M, W)`, extended by zero to `ℤ`: the inclusion of relative cochains followed by the
restriction of cochains to `W`. It is short exact (`shortExact_smoothCochainShortComplex`). -/
abbrev smoothCochainShortComplex : ShortComplex (CochainComplex (ModuleCat ℝ) ℤ) :=
  ShortComplex.mk (X₁ := 𝒞ᵣ[W].extend ComplexShape.embeddingUpNat)
    (X₂ := 𝒞[M].extend ComplexShape.embeddingUpNat) (X₃ := 𝒞[W].extend ComplexShape.embeddingUpNat)
    (extendMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
      (smoothSingularPair I W)) ComplexShape.embeddingUpNat)
    (smoothCochainRestriction I W) (extendMap_cochainComplexπ_comp_smoothCochainRestriction I W)

/-- The first map of the sequence of smooth cochains of the pair is the inclusion of relative
cochains. -/
theorem smoothCochainShortComplex_f :
    (smoothCochainShortComplex I W).f =
      extendMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (smoothSingularPair I W)) ComplexShape.embeddingUpNat :=
  (rfl)

/-- The second map of the sequence of smooth cochains of the pair is the restriction of smooth
cochains to `W`. -/
theorem smoothCochainShortComplex_g :
    (smoothCochainShortComplex I W).g = smoothCochainRestriction I W :=
  (rfl)

/-- The second map of the image under `Hom(-, ℝ)` of the sequence of smooth chains of the pair is
precomposition with the chain map induced by the inclusion of `W`. -/
private theorem smoothSingularPair_chainComplexShortComplex_op_map_g :
    (((smoothSingularPair I W).chainComplexShortComplex (ModuleCat.of ℝ ℝ)).op.map
      (ChainComplex.linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ))).g =
      SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ) (M := ModuleCat.of ℝ ℝ)
        (smoothSingularSubcomplexMap (Subtype.val : W → M) contMDiff_subtypeVal) := by
  -- The second map of the opposite sequence is the first map `SSet.chainComplexMap P.hom` of the
  -- sequence of chains, and `P.hom` is the map induced by the inclusion of `W`.
  dsimp only [ShortComplex.map_g, ShortComplex.op_g, smoothSingularPair_hom]
  -- `SSet.cochainComplexMap` is by definition the image under `Hom(-, ℝ)` of the induced chain map;
  -- the two sides differ only in how source and target are written, which agree by
  -- `smoothSingularPair_left` and `smoothSingularPair_right`.
  rfl

/-- The sequence of smooth cochains of the pair is the extension to `ℤ` of the image under
`Hom(-, ℝ)` of the sequence of smooth chains; the identifications are identities. -/
private def extendSmoothCochainShortComplexIso :
    (((smoothSingularPair I W).chainComplexShortComplex (ModuleCat.of ℝ ℝ)).op.map
      (ChainComplex.linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ))).map
        (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat ℝ)) ≅
      smoothCochainShortComplex I W :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    -- `SSetPair.cochainComplexπ` is by definition the image under `Hom(-, ℝ)` of
    -- `SSetPair.chainComplexπ`, the first map of the opposite sequence of chains.
    (by simp only [Iso.refl_hom]; rfl)
    (by
      rw [Iso.refl_hom, Iso.refl_hom, ShortComplex.map_g, ComplexShape.Embedding.extendFunctor_map,
        smoothSingularPair_chainComplexShortComplex_op_map_g]
      -- The identities only re-type objects, which agree by `smoothSingularPair_left`/`_right`.
      exact (Category.id_comp _).trans ((smoothCochainRestriction_def I W).trans
        (Category.comp_id _).symm))

/-- The sequence of smooth cochains of an open pair is short exact: restriction of cochains to the
smooth simplices of `W` is surjective, since a cochain on them extends by zero. -/
theorem shortExact_smoothCochainShortComplex : (smoothCochainShortComplex I W).ShortExact :=
  ShortComplex.shortExact_of_iso (extendSmoothCochainShortComplexIso I W)
    ((ChainComplex.shortExact_map_linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ)
      ((smoothSingularPair I W).shortExact_chainComplexShortComplex (ModuleCat.of ℝ ℝ))).extend
        ComplexShape.embeddingUpNat)

/-- The connecting map of the sequence of smooth cochains of the pair is the connecting map of the
extension to `ℤ` of the sequence of smooth chains under `Hom(-, ℝ)`. -/
private theorem δ_shortExact_smoothCochainShortComplex (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (shortExact_smoothCochainShortComplex I W).δ n₀ n₁ h =
      ((ChainComplex.shortExact_map_linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ)
        ((smoothSingularPair I W).shortExact_chainComplexShortComplex (ModuleCat.of ℝ ℝ))).extend
          ComplexShape.embeddingUpNat).δ n₀ n₁ h := by
  -- Naturality of the connecting map along `extendSmoothCochainShortComplexIso`, whose components
  -- are identities and so induce identities on cohomology.
  have h₁ : homologyMap (extendSmoothCochainShortComplexIso I W).hom.τ₁ n₁ = 𝟙 _ :=
    homologyMap_id _ _
  have h₃ : homologyMap (extendSmoothCochainShortComplexIso I W).hom.τ₃ n₀ = 𝟙 _ :=
    homologyMap_id _ _
  have := HomologySequence.δ_naturality (extendSmoothCochainShortComplexIso I W).hom
    ((ChainComplex.shortExact_map_linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ)
      ((smoothSingularPair I W).shortExact_chainComplexShortComplex (ModuleCat.of ℝ ℝ))).extend
        ComplexShape.embeddingUpNat) (shortExact_smoothCochainShortComplex I W) n₀ n₁ h
  rw [h₁, h₃] at this
  exact ((Category.id_comp _).symm.trans this.symm).trans (Category.comp_id _)

/-- The lift of the relative smooth cochains of `(M, W)` to the mapping cocone of the restriction
of smooth cochains: a relative cochain `a` goes to `(a, 0)`. It is a quasi-isomorphism. -/
def relativeSmoothCochainLift :
    𝒞ᵣ[W].extend ComplexShape.embeddingUpNat ⟶ relativeSmoothCochainComplex I W :=
  CochainComplex.mappingCocone.lift (smoothCochainShortComplex I W).g
    (smoothCochainShortComplex I W).f 0 (by
      simpa using congrArg CochainComplex.HomComplex.Cochain.ofHom
        (extendMap_cochainComplexπ_comp_smoothCochainRestriction I W))

/-- The lift of relative smooth cochains to the mapping cocone of restriction is a
quasi-isomorphism, since the sequence of smooth cochains of the pair is short exact. -/
instance : QuasiIso (relativeSmoothCochainLift I W) :=
  CochainComplex.mappingCocone.quasiIso_lift_of_shortExact
    (shortExact_smoothCochainShortComplex I W)

/-- Composed with the first projection of the cocone, the lift is the inclusion of relative smooth
cochains into the smooth cochains of `M`. -/
@[reassoc (attr := simp)]
theorem relativeSmoothCochainLift_fst :
    relativeSmoothCochainLift I W ≫
        CochainComplex.mappingCocone.fst (smoothCochainRestriction I W) =
      extendMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (smoothSingularPair I W)) ComplexShape.embeddingUpNat :=
  CochainComplex.mappingCocone.lift_fst _ _ _ _

/-- The cohomology of the mapping cocone of the restriction of smooth cochains is the smooth
relative cohomology of `(M, W)`, through the lift `relativeSmoothCochainLift`. -/
def relativeSmoothCohomologyIso (n : ℕ) :
    (relativeSmoothCochainComplex I W).homology n ≅ 𝒞ᵣ[W].homology n :=
  (asIso (homologyMap (relativeSmoothCochainLift I W) n)).symm ≪≫
    𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl

/-- Read on the extended complex of relative smooth cochains, the identification
`relativeSmoothCohomologyIso` is inverse to the map on cohomology of the lift. -/
theorem homologyMap_relativeSmoothCochainLift_extendHomologyIso_inv (n : ℕ)
    (x : (relativeSmoothCochainComplex I W).homology n) :
    homologyMap (relativeSmoothCochainLift I W) n
        ((𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl).inv
          ((relativeSmoothCohomologyIso I W n).hom x)) = x := by
  simp [relativeSmoothCohomologyIso]

section Integration

variable [IsManifold I 2 M]

namespace relativeDeRhamCohomology

/-- **Relative integration on cohomology.** The map from the relative de Rham cohomology
`H^n(M, W)` to the smooth relative singular cohomology of `(M, W)` induced by relative integration
`TauCeti.relativeDeRhamIntegration`, followed by the inverse of the lift of relative smooth cochains
to the mapping cocone of restriction. -/
def integration (n : ℕ) : relativeDeRhamCohomology I W n →ₗ[ℝ] 𝒞ᵣ[W].homology n :=
  (homologyMap (relativeDeRhamIntegration I W) n ≫ (relativeSmoothCohomologyIso I W n).hom).hom

/-- Relative integration on cohomology is the map induced by relative integration, followed by the
inverse of the lift of relative smooth cochains. -/
theorem ofHom_integration (n : ℕ) :
    ModuleCat.ofHom (integration I W n) =
      homologyMap (relativeDeRhamIntegration I W) n ≫ (relativeSmoothCohomologyIso I W n).hom :=
  (rfl)

/-- The lift of the relative integral of a class to the mapping cocone of restriction is the class
of its relative integral. -/
theorem homologyMap_relativeSmoothCochainLift_integration (n : ℕ)
    (x : relativeDeRhamCohomology I W n) :
    homologyMap (relativeSmoothCochainLift I W) n
        ((𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl).inv
          (integration I W n x)) =
      homologyMap (relativeDeRhamIntegration I W) n x :=
  homologyMap_relativeSmoothCochainLift_extendHomologyIso_inv I W n _

/-- **Relative integration and the maps to absolute cohomology.** Restricted from relative to
absolute smooth cochains, the relative integral of a class of `H^n(M, W)` is the integral of its
image in `H^n_dR(M)`. -/
theorem homologyMap_cochainComplexπ_integration (n : ℕ) (x : relativeDeRhamCohomology I W n) :
    homologyMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (smoothSingularPair I W)) n (integration I W n x) =
      deRhamCohomology.integration I M n (π I W n x) := by
  -- Write the relative integral of `x` as the image of a class `v` of the extended complex of
  -- relative smooth cochains, whose lift is the class of the relative integral of `x`.
  set v := (𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl).inv
    (integration I W n x)
  have hv : integration I W n x =
      (𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl).hom v :=
    (Iso.inv_hom_id_apply _ _).symm
  have hℓ := homologyMap_relativeSmoothCochainLift_integration I W n x
  -- Move the inclusion of relative cochains to the extended complexes, write it as the lift
  -- followed by the first projection, and pass the first projection through relative integration.
  have h₁ := ConcreteCategory.congr_hom (extendHomologyIso_hom_naturality
    (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) (smoothSingularPair I W))
    ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl) v
  have h₂ := ConcreteCategory.congr_hom (congrArg (homologyMap · (n : ℤ))
    (relativeSmoothCochainLift_fst I W)) v
  have h₃ := ConcreteCategory.congr_hom (congrArg (homologyMap · (n : ℤ))
    (relativeDeRhamIntegration_fst I W)) x
  have h₄ := ConcreteCategory.congr_hom (extendHomologyIso_hom_naturality
    (deRhamIntegration I M) ComplexShape.embeddingUpNat (j' := (n : ℤ)) rfl)
    (homologyMap (CochainComplex.mappingCocone.fst (deRhamRestriction I W)) n x)
  simp only [ConcreteCategory.comp_apply, homologyMap_comp] at h₁ h₂ h₃ h₄
  rw [hv]
  refine h₁.symm.trans ((congrArg (𝒞[M].extendHomologyIso ComplexShape.embeddingUpNat
    (j' := (n : ℤ)) rfl).hom h₂.symm).trans ?_)
  rw [hℓ, h₃, h₄]
  exact (ConcreteCategory.congr_hom (deRhamCohomology.homologyMap_deRhamIntegration I M n) _).trans
    (congrArg (deRhamCohomology.integration I M n)
      (ConcreteCategory.congr_hom (ofHom_π I W n) x).symm)

/-- The relative integral of `(0, β)` is `-inr (∫ β)` in the mapping cocone of restriction. -/
private theorem relativeDeRhamIntegration_f_coord_symm_zero (k : ℕ) (β : SmoothForm I W ℝ k) :
    (relativeDeRhamIntegration I W).f (k + 1 : ℕ)
        ((relativeDeRhamComplex.coord I W k).symm (0, β)) =
      -(CochainComplex.mappingCocone.inr (smoothCochainRestriction I W)).val.v k (k + 1 : ℕ) rfl
        ((extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).inv (integrationCochain β.val)) := by
  apply (CochainComplex.mappingCocone.relativeCoordinates (smoothCochainRestriction I W)
    (k + 1 : ℕ) k (by push_cast; lia)).injective
  -- In relative coordinates the left side integrates the coordinates `(0, β)` of `(0, β)`, and
  -- the right side is `(0, ∫ β)`.
  rw [relativeCoordinates_relativeDeRhamIntegration_f, map_neg,
    CochainComplex.mappingCocone.relativeCoordinates_inr_v, relativeDeRhamComplex.coord_symm_apply,
    map_zero, zero_add, relativeDeRhamComplex.relativeCoordinates_inr]
  simp only [deRhamComplexExtendXEquiv_symm_apply,
    extendMap_f (deRhamIntegration I W) ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl,
    ModuleCat.comp_apply, Iso.inv_hom_id_apply, map_zero, Prod.neg_mk, neg_zero, neg_neg,
    Prod.mk.injEq, true_and]
  -- What remains is the integral of `β`, carried into the extended complex.
  exact congrArg (extendXIso 𝒞[W] ComplexShape.embeddingUpNat (i := k) (i' := (k : ℤ)) rfl).inv
    (deRhamIntegration_f_inv_apply I W k β)

/-- **Relative integration and the connecting maps.** The relative integral of the de Rham
connecting map `δ [b] = -[(0, b)]` of a class on `W` is the connecting map of the long exact
sequence of smooth cochains of the pair applied to the integral of the class, with no sign. -/
theorem integration_δ (k : ℕ) (c : deRhamCohomology I W k) :
    integration I W (k + 1) (δ I W k c) =
      (ChainComplex.shortExact_map_linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ)
        ((smoothSingularPair I W).shortExact_chainComplexShortComplex (ModuleCat.of ℝ ℝ))).δ k
          (k + 1) (by simp) (deRhamCohomology.integration I W k c) := by
  obtain ⟨b, rfl⟩ := deRhamCohomology.mk_surjective I k c
  -- The integration cocycle of `b`, as a cycle `z` of the extended cochains of `W`.
  set z := (𝒞[W].extendCyclesIso ComplexShape.embeddingUpNat (j := k) (j' := (k : ℤ)) rfl).inv
    (integrationCocycle I W k b)
  have hz : (𝒞[W].extendHomologyIso ComplexShape.embeddingUpNat (j' := (k : ℤ)) rfl).hom
      ((𝒞[W].extend ComplexShape.embeddingUpNat).homologyπ k z) =
        deRhamCohomology.integration I W k (deRhamCohomology.mk I k b) := by
    rw [deRhamCohomology.integration_mk, ← ModuleCat.comp_apply, homologyπ_extendHomologyIso_hom,
      ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  have hzi : (𝒞[W].extend ComplexShape.embeddingUpNat).iCycles k z =
      (extendXIso 𝒞[W] ComplexShape.embeddingUpNat rfl).inv (integrationCochain b.val.val) := by
    rw [← ModuleCat.comp_apply, extendCyclesIso_inv_iCycles, ModuleCat.comp_apply,
      iCycles_integrationCocycle]
  -- Pass from the connecting map of the unextended sequence to that of the cocone model.
  have hS₀ := ChainComplex.shortExact_map_linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ)
    ((smoothSingularPair I W).shortExact_chainComplexShortComplex (ModuleCat.of ℝ ℝ))
  have hδ : (𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat
        (j' := ((k + 1 : ℕ) : ℤ)) rfl).hom ((hS₀.extend ComplexShape.embeddingUpNat).δ k
          (k + 1 : ℕ) rfl ((𝒞[W].extend ComplexShape.embeddingUpNat).homologyπ k z)) =
      hS₀.δ k (k + 1) (by simp) ((𝒞[W].extendHomologyIso ComplexShape.embeddingUpNat
        (j' := (k : ℤ)) rfl).hom ((𝒞[W].extend ComplexShape.embeddingUpNat).homologyπ k z)) :=
    ConcreteCategory.congr_hom (hS₀.extend_δ_comp_extendHomologyIso_hom ComplexShape.embeddingUpNat
      (i := k) (j := k + 1) (by simp) rfl rfl rfl) _
  rw [← hz, ← hδ, ← δ_shortExact_smoothCochainShortComplex]
  -- Both sides are now read through the lift; on the cocone, both are the class of `inr (∫ b)`.
  have hℓ := CochainComplex.mappingCocone.moduleCat_homologyMap_lift_δ_homologyπ
    (shortExact_smoothCochainShortComplex I W) k (k + 1 : ℕ) rfl z
  -- Compare the lifts of the two sides to the cocone.
  rw [← Iso.inv_hom_id_apply (𝒞ᵣ[W].extendHomologyIso ComplexShape.embeddingUpNat
    (j' := ((k + 1 : ℕ) : ℤ)) rfl) (integration I W (k + 1) _)]
  congr 1
  apply (ModuleCat.mono_iff_injective
    (homologyMap (relativeSmoothCochainLift I W) (k + 1 : ℕ))).1 inferInstance
  refine (homologyMap_relativeSmoothCochainLift_integration I W (k + 1) _).trans
    (Eq.trans ?_ hℓ.symm)
  rw [δ_mk, map_neg, mk_apply, homologyMap_homologyπ_moduleCatCyclesMk, ← map_neg]
  congr 1
  apply moduleCat_iCycles_injective
  rw [map_neg, iCycles_moduleCatCyclesMk, iCycles_moduleCatCyclesMk,
    relativeDeRhamIntegration_f_coord_symm_zero, neg_neg, hzi]

end relativeDeRhamCohomology

end Integration

section SingularCohomology

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

open relativeDeRhamCohomology

/-- **The relative de Rham homomorphism** `H^n(M, W) →ₗ[ℝ] Hⁿ(M, W; ℝ)` of an open subset `W` of a
Hausdorff `σ`-compact smooth manifold `M` modelled on a finite-dimensional real model with corners:
relative integration, followed by the inverse of the relative smoothing isomorphism
`TauCeti.smoothSingularRelativeCohomologyIso` from relative singular cohomology to smooth relative
cohomology. -/
def relativeDeRhamHom (n : ℕ) : relativeDeRhamCohomology I W n →ₗ[ℝ]
    (TopPair.ofSubset (W : Set (TopCat.of M))).singularCohomology (ModuleCat.of ℝ ℝ) ℝ
      (ModuleCat.of ℝ ℝ) n :=
  (smoothSingularRelativeCohomologyIso I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) W n).inv.hom ∘ₗ
    integration I W n

/-- The relative de Rham homomorphism is relative integration followed by the inverse of the
relative smoothing isomorphism. -/
theorem relativeDeRhamHom_apply (n : ℕ) (x : relativeDeRhamCohomology I W n) :
    relativeDeRhamHom I W n x =
      (smoothSingularRelativeCohomologyIso I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) W n).inv
        (integration I W n x) :=
  (rfl)

/-- Restricted to smooth relative singular chains, the relative de Rham homomorphism is relative
integration. This determines it, since this restriction is the isomorphism
`TauCeti.smoothSingularRelativeCohomologyIso`. -/
@[simp]
theorem homologyMap_cochainComplexMap_relativeDeRhamHom (n : ℕ)
    (x : relativeDeRhamCohomology I W n) :
    homologyMap (SSetPair.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
        (M := ModuleCat.of ℝ ℝ) (smoothSingularPairι I W)) n (relativeDeRhamHom I W n x) =
      integration I W n x := by
  rw [← smoothSingularRelativeCohomologyIso_hom, relativeDeRhamHom_apply, Iso.inv_hom_id_apply]

/-- **The relative de Rham homomorphism and the maps to absolute cohomology.** The image in
`Hⁿ(M; ℝ)` of the relative de Rham homomorphism of a class of `H^n(M, W)` is the absolute de Rham
homomorphism of its image in `H^n_dR(M)`. -/
theorem singularCohomologyπ_relativeDeRhamHom (n : ℕ) (x : relativeDeRhamCohomology I W n) :
    (TopPair.ofSubset (W : Set (TopCat.of M))).singularCohomologyπ (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ) n (relativeDeRhamHom I W n x) =
      deRhamHom I M n (π I W n x) := by
  have h : (smoothSingularCohomologyIso I M (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) n).hom
      ((TopPair.ofSubset (W : Set (TopCat.of M))).singularCohomologyπ (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ) n (relativeDeRhamHom I W n x)) =
      homologyMap (SSetPair.cochainComplexπ (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ)
        (smoothSingularPair I W)) n
          ((smoothSingularRelativeCohomologyIso I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) W n).hom
            (relativeDeRhamHom I W n x)) :=
    ConcreteCategory.congr_hom (singularCohomologyπ_comp_smoothSingularCohomologyIso_hom I
      (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) W n) _
  rw [relativeDeRhamHom_apply, Iso.inv_hom_id_apply, homologyMap_cochainComplexπ_integration] at h
  rw [relativeDeRhamHom_apply, deRhamHom_apply, ← h]
  exact (Iso.hom_inv_id_apply _ _).symm

/-- **The relative de Rham homomorphism and the connecting maps.** The relative de Rham
homomorphism of the de Rham connecting map `δ [b] = -[(0, b)]` of a class on `W` is the connecting
map of relative singular cohomology applied to the de Rham homomorphism of the class. -/
theorem relativeDeRhamHom_δ [SigmaCompactSpace W] (k : ℕ) (c : deRhamCohomology I W k) :
    relativeDeRhamHom I W (k + 1) (δ I W k c) =
      ((TopPair.ofSubset (W : Set (TopCat.of M))).singularCohomologyδ (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ) k (k + 1)) (deRhamHom I W k c) := by
  have h : (smoothSingularRelativeCohomologyIso I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) W
      (k + 1)).hom
      (((TopPair.ofSubset (W : Set (TopCat.of M))).singularCohomologyδ (ModuleCat.of ℝ ℝ) ℝ
        (ModuleCat.of ℝ ℝ) k (k + 1)) (deRhamHom I W k c)) =
      (ChainComplex.shortExact_map_linearYonedaFunctor ℝ (ModuleCat.of ℝ ℝ)
        ((smoothSingularPair I W).shortExact_chainComplexShortComplex (ModuleCat.of ℝ ℝ))).δ k
          (k + 1) (by simp) (homologyMap (SSet.cochainComplexMap (R := ModuleCat.of ℝ ℝ) (k := ℝ)
            (M := ModuleCat.of ℝ ℝ) (smoothSingularSubcomplex I W).ι) k (deRhamHom I W k c)) :=
    ConcreteCategory.congr_hom (singularCohomologyδ_comp_smoothSingularRelativeCohomologyIso_hom
      I (ModuleCat.of ℝ ℝ) ℝ (ModuleCat.of ℝ ℝ) W k (k + 1)) _
  rw [homologyMap_cochainComplexMap_deRhamHom, ← integration_δ] at h
  rw [relativeDeRhamHom_apply, ← h]
  exact Iso.hom_inv_id_apply _ _

end SingularCohomology

end TauCeti
