/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DifferentialForm.Support

/-!
# Compactly supported de Rham cohomology

Smooth real-valued forms with compact topological support form a submodule of all smooth forms.
The exterior derivative does not enlarge supports, so these forms are a subcomplex of the de Rham
complex, the compactly supported de Rham complex; its cohomology is compactly supported de Rham
cohomology `H^•_c`.

The subcomplex inclusion induces the comparison `H^•_c(M) → H^•_dR(M)`, an isomorphism on compact
manifolds, where every form is compactly supported. Pullback along a smooth proper map preserves
compact support, so `H^•_c` is contravariant for smooth proper maps. Pullback along a general smooth
map does not preserve compact support: the constant map `ℝ → pt` pulls the constant function `1`
back to a function without compact support.

## Main definitions

* `TauCeti.compactlySupportedForms I M k`: compactly supported smooth `k`-forms.
* `TauCeti.compactlySupportedDeRhamComplex I M`: the compactly supported de Rham complex.
* `TauCeti.compactlySupportedDeRhamCohomology I M k`: its cohomology.
* `TauCeti.compactlySupportedDeRhamComplex.ι`: the inclusion into the de Rham complex.
* `TauCeti.compactlySupportedDeRhamComplex.map`: the cochain map induced by a smooth proper map,
  with the induced map `TauCeti.compactlySupportedDeRhamCohomology.map` on cohomology.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17,
  "Cohomology with Compact Support".
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

section Forms

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [IsManifold I 1 M]

variable (M) in
/-- The submodule of smooth real-valued `k`-forms with compact topological support. -/
def compactlySupportedForms (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k) where
  carrier := {φ | IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1)}
  add_mem' {φ ψ} hφ hψ :=
    (hφ.union hψ).of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) _)
      (_root_.tsupport_add (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1 ψ.1)
  zero_mem' := by
    -- Identify the dependent zero section with a fixed-codomain zero function so that
    -- the function `tsupport_zero` simplification applies.
    change IsCompact (_root_.tsupport (0 : M → E [⋀^Fin k]→L[ℝ] ℝ))
    simp
  smul_mem' c φ hφ :=
    hφ.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) _)
      (RoughForm.tsupport_smul_subset c φ.1)

/-- A smooth form is compactly supported when its topological support is compact. -/
@[simp]
theorem mem_compactlySupportedForms {k : ℕ} {φ : SmoothForm I M ℝ k} :
    φ ∈ compactlySupportedForms I M k ↔
      IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1) :=
  Iff.rfl

/-- On a compact manifold every smooth form is compactly supported. -/
@[simp]
theorem compactlySupportedForms_eq_top [CompactSpace M] (k : ℕ) :
    compactlySupportedForms I M k = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ (mem_compactlySupportedForms I).mpr
    (isCompact_univ.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) _)
      (Set.subset_univ _))

end Forms

section Complex

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

namespace compactlySupportedForms

variable (M) in
/-- The exterior derivative of compactly supported smooth forms, which does not enlarge
supports. -/
def mextDerivₗ (k : ℕ) :
    compactlySupportedForms I M k →ₗ[ℝ] compactlySupportedForms I M (k + 1) :=
  (TauCeti.mextDerivₗ I (M := M) (F := ℝ) k).restrict fun φ hφ ↦ by
    rw [mem_compactlySupportedForms, mextDerivₗ_apply]
    exact RoughForm.isCompact_tsupport_mextDeriv hφ

/-- The exterior derivative of a compactly supported form is its exterior derivative as a smooth
form. -/
@[simp]
theorem coe_mextDerivₗ (k : ℕ) (φ : compactlySupportedForms I M k) :
    (mextDerivₗ I M k φ : SmoothForm I M ℝ (k + 1)) = TauCeti.mextDerivₗ I k φ :=
  (rfl)

/-- Successive exterior derivatives of compactly supported forms compose to zero. -/
@[simp]
theorem mextDerivₗ_comp_mextDerivₗ (k : ℕ) :
    (mextDerivₗ I M (k + 1)).comp (mextDerivₗ I M k) = 0 := by
  ext φ : 1
  apply Subtype.ext
  simp only [LinearMap.comp_apply, coe_mextDerivₗ, LinearMap.zero_apply, Submodule.coe_zero]
  exact LinearMap.congr_fun (TauCeti.mextDerivₗ_comp_mextDerivₗ I (M := M) (F := ℝ) k) φ.1

end compactlySupportedForms

variable (M) in
/-- The compactly supported de Rham complex: compactly supported smooth real-valued forms with the
exterior derivative. -/
def compactlySupportedDeRhamComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (compactlySupportedForms I M k))
    (fun k ↦ ModuleCat.ofHom (compactlySupportedForms.mextDerivₗ I M k))
    (fun k ↦ ModuleCat.hom_ext (compactlySupportedForms.mextDerivₗ_comp_mextDerivₗ I k))

/-- The canonical identification of the degree-`k` object with compactly supported smooth
`k`-forms. -/
def compactlySupportedDeRhamComplexXIso (k : ℕ) :
    (compactlySupportedDeRhamComplex I M).X k ≅
      ModuleCat.of ℝ (compactlySupportedForms I M k) :=
  Iso.refl _

/-- Under the canonical identifications of the objects, the differential of the compactly
supported de Rham complex is the exterior derivative. -/
@[reassoc]
theorem compactlySupportedDeRhamComplex_d (k : ℕ) :
    (compactlySupportedDeRhamComplex I M).d k (k + 1) ≫
        (compactlySupportedDeRhamComplexXIso I (M := M) (k + 1)).hom =
      (compactlySupportedDeRhamComplexXIso I (M := M) k).hom ≫
        ModuleCat.ofHom (compactlySupportedForms.mextDerivₗ I M k) := by
  dsimp +instances [compactlySupportedDeRhamComplexXIso, compactlySupportedDeRhamComplex]
  simp

variable (M) in
/-- Compactly supported de Rham cohomology is the categorical homology of the compactly
supported de Rham complex. -/
abbrev compactlySupportedDeRhamCohomology (k : ℕ) : Type _ :=
  (compactlySupportedDeRhamComplex I M).homology k

namespace compactlySupportedDeRhamComplex

variable (M) in
/-- The inclusion of the compactly supported de Rham complex into the de Rham complex. -/
def ι : compactlySupportedDeRhamComplex I M ⟶ deRhamComplex I M :=
  CochainComplex.ofHom
    (fun k ↦ (compactlySupportedDeRhamComplexXIso I k).hom ≫
      ModuleCat.ofHom (compactlySupportedForms I M k).subtype ≫ (deRhamComplexXIso I k).inv)
    fun k ↦ by
      rw [← cancel_mono (deRhamComplexXIso I (M := M) (k + 1)).hom]
      simp only [Category.assoc, deRhamComplex_d, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id, compactlySupportedDeRhamComplex_d_assoc]
      ext φ : 2
      simp

/-- Under the canonical identifications of the objects, the inclusion is the inclusion of
compactly supported forms into smooth forms. -/
@[reassoc]
theorem ι_f (k : ℕ) :
    (ι I M).f k ≫ (deRhamComplexXIso I (M := M) k).hom =
      (compactlySupportedDeRhamComplexXIso I (M := M) k).hom ≫
        ModuleCat.ofHom (compactlySupportedForms I M k).subtype := by
  simp [ι]

/-- On a compact manifold the compactly supported de Rham complex is the de Rham complex. -/
instance isIso_ι [CompactSpace M] : IsIso (ι I M) := by
  have (k : ℕ) : IsIso (ModuleCat.ofHom (compactlySupportedForms I M k).subtype :
      ModuleCat.of ℝ (compactlySupportedForms I M k) ⟶ ModuleCat.of ℝ (SmoothForm I M ℝ k)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨Subtype.val_injective, fun φ ↦ ⟨⟨φ, ?_⟩, rfl⟩⟩
    simp
  have (k : ℕ) : IsIso ((ι I M).f k) := by
    dsimp [ι]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

end compactlySupportedDeRhamComplex

namespace compactlySupportedDeRhamCohomology

variable (M) in
/-- The comparison map from compactly supported to ordinary de Rham cohomology, induced by the
inclusion of complexes. -/
def toDeRhamCohomology (k : ℕ) :
    compactlySupportedDeRhamCohomology I M k →ₗ[ℝ] deRhamCohomology I M k :=
  (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.ι I M) k).hom

/-- On a compact manifold compactly supported and ordinary de Rham cohomology agree. -/
theorem bijective_toDeRhamCohomology [CompactSpace M] (k : ℕ) :
    Function.Bijective (toDeRhamCohomology I M k) :=
  (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end compactlySupportedDeRhamCohomology

end Complex

section Pullback

variable {E H E' H' E'' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {I'' : ModelWithCorners ℝ E'' H''}
  {M M' M'' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace M''] [ChartedSpace H'' M'']

namespace compactlySupportedForms

variable [IsManifold I 1 M] [IsManifold I' 1 M'] [IsManifold I'' 1 M'']

/-- Pullback of compactly supported smooth forms along a smooth proper map. -/
def mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    compactlySupportedForms I' M' k →ₗ[ℝ] compactlySupportedForms I M k :=
  (SmoothForm.mpullback (F := ℝ) (k := k) f hf).restrict fun φ hφ ↦ by
    rw [mem_compactlySupportedForms, SmoothForm.coe_mpullback]
    exact RoughForm.isCompact_tsupport_mpullback hp hφ

/-- The pullback of a compactly supported form is its pullback as a smooth form. -/
@[simp]
theorem coe_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ)
    (φ : compactlySupportedForms I' M' k) :
    (mpullback f hf hp k φ : SmoothForm I M ℝ k) = SmoothForm.mpullback f hf φ :=
  (rfl)

/-- Pullback of compactly supported forms by the identity is the identity linear map. -/
@[simp]
theorem mpullback_id (k : ℕ) :
    mpullback (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id isProperMap_id k =
      LinearMap.id := by
  ext φ : 1
  apply Subtype.ext
  simp

/-- Pullback of compactly supported forms reverses composition. -/
theorem mpullback_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) (hfp : IsProperMap f) (hgp : IsProperMap g) (k : ℕ) :
    mpullback (g ∘ f) (hg.comp hf) (hgp.comp hfp) k =
      (mpullback f hf hfp k).comp (mpullback g hg hgp k) := by
  ext φ : 1
  apply Subtype.ext
  simpa using LinearMap.congr_fun (SmoothForm.mpullback_comp (F := ℝ) (k := k) f g hf hg) φ.1

end compactlySupportedForms

/-- Pullback of compactly supported forms along a smooth proper map commutes with the exterior
derivative. -/
theorem compactlySupportedForms.mextDerivₗ_mpullback [IsManifold I 2 M] [IsManifold I' 2 M']
    (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ)
    (φ : compactlySupportedForms I' M' k) :
    mextDerivₗ I M k (mpullback f hf hp k φ) = mpullback f hf hp (k + 1) (mextDerivₗ I' M' k φ) :=
  Subtype.ext (SmoothForm.mextDerivₗ_mpullback f hf k φ.1)

end Pullback

section PullbackComplex

/-! The induced cochain maps compare complexes in one universe, so the model spaces share a
universe, as do the manifolds. -/

universe u v

variable {E E' E'' : Type u} {H H' H'' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'}
  {I'' : ModelWithCorners ℝ E'' H''}
  {M M' M'' : Type v}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 2 M']
  [TopologicalSpace M''] [ChartedSpace H'' M''] [IsManifold I'' 2 M'']

namespace compactlySupportedDeRhamComplex

/-- The cochain map between compactly supported de Rham complexes induced by a smooth proper
map. -/
def map (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) :
    compactlySupportedDeRhamComplex I' M' ⟶ compactlySupportedDeRhamComplex I M :=
  CochainComplex.ofHom
    (fun k ↦ (compactlySupportedDeRhamComplexXIso I' k).hom ≫
      ModuleCat.ofHom (compactlySupportedForms.mpullback f hf hp k) ≫
        (compactlySupportedDeRhamComplexXIso I k).inv)
    fun k ↦ by
      rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (M := M) (k + 1)).hom]
      simp only [Category.assoc, compactlySupportedDeRhamComplex_d, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id, compactlySupportedDeRhamComplex_d_assoc]
      ext φ : 2
      simpa using compactlySupportedForms.mextDerivₗ_mpullback f hf hp k
        ((compactlySupportedDeRhamComplexXIso I' k).hom φ)

/-- Under the canonical identifications of the objects, the induced cochain map is pullback of
compactly supported forms. -/
@[reassoc]
theorem map_f (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    (map f hf hp).f k ≫ (compactlySupportedDeRhamComplexXIso I (M := M) k).hom =
      (compactlySupportedDeRhamComplexXIso I' (M := M') k).hom ≫
        ModuleCat.ofHom (compactlySupportedForms.mpullback f hf hp k) := by
  simp [map]

/-- The cochain map induced by the identity is the identity. -/
@[simp]
theorem map_id :
    map (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id isProperMap_id = 𝟙 _ := by
  ext k : 1
  rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (M := M) k).hom, map_f,
    compactlySupportedForms.mpullback_id]
  simp

/-- The induced cochain maps reverse composition of smooth proper maps. -/
theorem map_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) (hfp : IsProperMap f) (hgp : IsProperMap g) :
    map (g ∘ f) (hg.comp hf) (hgp.comp hfp) = map g hg hgp ≫ map f hf hfp := by
  ext k : 1
  rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (M := M) k).hom,
    HomologicalComplex.comp_f, Category.assoc, map_f, map_f, map_f_assoc,
    compactlySupportedForms.mpullback_comp f g hf hg hfp hgp]
  -- This is `ModuleCat.ofHom_comp`, which `rw` cannot match against the submodule instances.
  rfl

end compactlySupportedDeRhamComplex

namespace compactlySupportedDeRhamCohomology

/-- The contravariant map on compactly supported de Rham cohomology induced by a smooth proper
map. -/
def map (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    compactlySupportedDeRhamCohomology I' M' k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M k :=
  (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.map f hf hp) k).hom

/-- The map on compactly supported cohomology induced by the identity is the identity. -/
@[simp]
theorem map_id (k : ℕ) :
    map (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id isProperMap_id k =
      LinearMap.id := by
  rw [map, compactlySupportedDeRhamComplex.map_id, HomologicalComplex.homologyMap_id,
    ModuleCat.hom_id]

/-- Pullback on compactly supported cohomology reverses composition of smooth proper maps. -/
theorem map_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) (hfp : IsProperMap f) (hgp : IsProperMap g) (k : ℕ) :
    map (g ∘ f) (hg.comp hf) (hgp.comp hfp) k = (map f hf hfp k).comp (map g hg hgp k) := by
  simp only [map, compactlySupportedDeRhamComplex.map_comp f g hf hg hfp hgp,
    HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]

end compactlySupportedDeRhamCohomology

end PullbackComplex

end TauCeti
