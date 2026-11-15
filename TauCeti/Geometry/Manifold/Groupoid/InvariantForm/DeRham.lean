/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Geometry.Manifold.Groupoid.InvariantForm.Support

/-!
# Invariant and coarse-compact de Rham complexes of presentations

On a smooth quiver or category `C`, invariant differential forms and invariant forms with compact
coarse support form cochain complexes `TauCeti.Quiver.invariantDeRhamComplex` and
`TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex` in `CochainComplex (ModuleCat ℝ) ℕ` with
cohomologies `TauCeti.Quiver.invariantDeRhamCohomology` and
`TauCeti.Quiver.compactlySupportedInvariantDeRhamCohomology`; their canonical comparison morphism
`TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex.ι` is an isomorphism when the coarse space
is compact. Smooth prefunctors contravariantly pull back `invariantDeRhamComplex`
(`Prefunctor.invariantDeRhamComplexMap`), smooth functors with proper coarse map pull back
`compactlySupportedInvariantDeRhamComplex`
(`CategoryTheory.Functor.compactlySupportedInvariantDeRhamComplexMap`), smooth natural
transformations identify both induced maps, and full essentially surjective étale refinements induce
isomorphisms on both complexes and linear equivalences in every cohomology degree.

## References

* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Section 2.1.
* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Sections 2–3.
-/

public noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti.Quiver

variable {E H A K C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K] [TopologicalSpace C]
  [ChartedSpace H C]

section InvariantComplex

variable [Quiver C] [TopologicalSpace (_root_.Quiver.Total C)]
  [ChartedSpace K (_root_.Quiver.Total C)] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ A K)
  [IsManifold I ∞ C] [IsManifold J ∞ (_root_.Quiver.Total C)]
  (hs : ContMDiff J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C))
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The nonnegative cochain complex of `V`-valued invariant smooth differential forms on `C`. -/
def invariantDeRhamComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (invariantForms I J hs ht V k))
    (fun k ↦ ModuleCat.ofHom (invariantForms.mextDerivₗ I J hs ht V k))
    (fun k ↦ ModuleCat.hom_ext (invariantForms.mextDerivₗ_comp_mextDerivₗ I J hs ht V k))

/-- Canonical identification of `(invariantDeRhamComplex I J hs ht V).X k` with `invariantForms`. -/
def invariantDeRhamComplexXIso (k : ℕ) :
    (invariantDeRhamComplex I J hs ht V).X k ≅ ModuleCat.of ℝ (invariantForms I J hs ht V k) := by
  unfold invariantDeRhamComplex; exact Iso.refl _

/-- Under `invariantDeRhamComplexXIso`, the differential is `invariantForms.mextDerivₗ`. -/
@[reassoc]
theorem invariantDeRhamComplex_d (k : ℕ) :
    (invariantDeRhamComplex I J hs ht V).d k (k + 1) ≫
        (invariantDeRhamComplexXIso I J hs ht V (k + 1)).hom =
      (invariantDeRhamComplexXIso I J hs ht V k).hom ≫
        ModuleCat.ofHom (invariantForms.mextDerivₗ I J hs ht V k) := by
  dsimp +instances [invariantDeRhamComplexXIso, invariantDeRhamComplex]; simp

/-- Degree-`k` cohomology of the invariant de Rham complex of `C`. -/
abbrev invariantDeRhamCohomology (k : ℕ) : Type _ :=
  (invariantDeRhamComplex I J hs ht V).homology k

end InvariantComplex

section CompactSupportComplex

variable [Category C] [TopologicalSpace (_root_.Quiver.Total C)]
  [ChartedSpace K (_root_.Quiver.Total C)] (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ A K)
  [IsManifold I ∞ C] [IsManifold J ∞ (_root_.Quiver.Total C)]
  (hs : ContMDiff J I ∞ (_root_.Quiver.Total.left : _root_.Quiver.Total C → C))
  (ht : ContMDiff J I ∞ (_root_.Quiver.Total.right : _root_.Quiver.Total C → C))
  (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cochain complex of `V`-valued invariant smooth forms on `C` with compact coarse support. -/
def compactlySupportedInvariantDeRhamComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (compactlySupportedInvariantForms I J hs ht V k))
    (fun k ↦ ModuleCat.ofHom (compactlySupportedInvariantForms.mextDerivₗ I J hs ht V k))
    (fun k ↦ ModuleCat.hom_ext
      (compactlySupportedInvariantForms.mextDerivₗ_comp_mextDerivₗ I J hs ht V k))

/-- Canonical identification of `(compactlySupportedInvariantDeRhamComplex I J hs ht V).X k`. -/
def compactlySupportedInvariantDeRhamComplexXIso (k : ℕ) :
    (compactlySupportedInvariantDeRhamComplex I J hs ht V).X k ≅
      ModuleCat.of ℝ (compactlySupportedInvariantForms I J hs ht V k) := by
  unfold compactlySupportedInvariantDeRhamComplex; exact Iso.refl _

/-- Under `compactlySupportedInvariantDeRhamComplexXIso`, the differential is
`compactlySupportedInvariantForms.mextDerivₗ`. -/
@[reassoc]
theorem compactlySupportedInvariantDeRhamComplex_d (k : ℕ) :
    (compactlySupportedInvariantDeRhamComplex I J hs ht V).d k (k + 1) ≫
        (compactlySupportedInvariantDeRhamComplexXIso I J hs ht V (k + 1)).hom =
      (compactlySupportedInvariantDeRhamComplexXIso I J hs ht V k).hom ≫
        ModuleCat.ofHom (compactlySupportedInvariantForms.mextDerivₗ I J hs ht V k) := by
  dsimp +instances [compactlySupportedInvariantDeRhamComplexXIso,
    compactlySupportedInvariantDeRhamComplex]; simp

/-- Degree-`k` cohomology of the compact-coarse-support invariant de Rham complex of `C`. -/
abbrev compactlySupportedInvariantDeRhamCohomology (k : ℕ) : Type _ :=
  (compactlySupportedInvariantDeRhamComplex I J hs ht V).homology k

/-- Inclusion of `compactlySupportedInvariantDeRhamComplex` into `invariantDeRhamComplex`. -/
def compactlySupportedInvariantDeRhamComplex.ι :
    compactlySupportedInvariantDeRhamComplex I J hs ht V ⟶ invariantDeRhamComplex I J hs ht V :=
  CochainComplex.ofHom
    (fun k ↦ (compactlySupportedInvariantDeRhamComplexXIso I J hs ht V k).hom ≫
      ModuleCat.ofHom (Submodule.inclusion (compactlySupportedInvariantForms_le_invariantForms
        (I := I) (J := J) (hs := hs) (ht := ht) (V := V) (k := k))) ≫
      (invariantDeRhamComplexXIso I J hs ht V k).inv)
    fun k ↦ by
      rw [← cancel_mono (invariantDeRhamComplexXIso I J hs ht V (k + 1)).hom]
      simp only [Category.assoc, invariantDeRhamComplex_d, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id, compactlySupportedInvariantDeRhamComplex_d_assoc]
      ext φ : 2; apply Subtype.ext
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        Submodule.coe_inclusion, invariantForms.coe_mextDerivₗ,
        compactlySupportedInvariantForms.coe_mextDerivₗ]

/-- Under `XIso`, `ι` acts by `Submodule.inclusion` into `invariantForms`. -/
@[reassoc]
theorem compactlySupportedInvariantDeRhamComplex.ι_f (k : ℕ) :
    (compactlySupportedInvariantDeRhamComplex.ι I J hs ht V).f k ≫
        (invariantDeRhamComplexXIso I J hs ht V k).hom =
      (compactlySupportedInvariantDeRhamComplexXIso I J hs ht V k).hom ≫
        ModuleCat.ofHom (Submodule.inclusion (compactlySupportedInvariantForms_le_invariantForms
          (I := I) (J := J) (hs := hs) (ht := ht) (V := V) (k := k))) := by
  simp [compactlySupportedInvariantDeRhamComplex.ι]

/-- When `Quotient (isIsomorphicSetoid C)` is compact, `ι` is an isomorphism of complexes. -/
instance compactlySupportedInvariantDeRhamComplex.isIso_ι
    [CompactSpace (Quotient (isIsomorphicSetoid C))] :
    IsIso (compactlySupportedInvariantDeRhamComplex.ι I J hs ht V) := by
  have hbij (k : ℕ) : IsIso (ModuleCat.ofHom (Submodule.inclusion
      (compactlySupportedInvariantForms_le_invariantForms
        (I := I) (J := J) (hs := hs) (ht := ht) (V := V) (k := k))) :
      ModuleCat.of ℝ (compactlySupportedInvariantForms I J hs ht V k) ⟶
        ModuleCat.of ℝ (invariantForms I J hs ht V k)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨Submodule.inclusion_injective (compactlySupportedInvariantForms_le_invariantForms
        (I := I) (J := J) (hs := hs) (ht := ht) (V := V) (k := k)),
      fun φ ↦ ⟨⟨φ.1, by simpa only [compactlySupportedInvariantForms_eq_invariantForms] using φ.2⟩,
        Subtype.ext rfl⟩⟩
  have (k : ℕ) : IsIso ((compactlySupportedInvariantDeRhamComplex.ι I J hs ht V).f k) := by
    dsimp [compactlySupportedInvariantDeRhamComplex.ι]; infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Comparison linear map from compact-coarse-support to ordinary invariant de Rham cohomology. -/
def compactlySupportedInvariantDeRhamCohomology.toInvariantDeRhamCohomology (k : ℕ) :
    compactlySupportedInvariantDeRhamCohomology I J hs ht V k →ₗ[ℝ]
      invariantDeRhamCohomology I J hs ht V k :=
  (HomologicalComplex.homologyMap (compactlySupportedInvariantDeRhamComplex.ι I J hs ht V) k).hom

/-- When the coarse space is compact, coarse-compact and ordinary invariant cohomology agree. -/
theorem compactlySupportedInvariantDeRhamCohomology.toInvariantDeRhamCohomology_bijective
    [CompactSpace (Quotient (isIsomorphicSetoid C))] (k : ℕ) :
    Function.Bijective
      (compactlySupportedInvariantDeRhamCohomology.toInvariantDeRhamCohomology I J hs ht V k) :=
  ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (compactlySupportedInvariantDeRhamComplex.ι I J hs ht V) k)

end CompactSupportComplex

end TauCeti.Quiver

section ChainMaps

/-! Cochain morphisms in `CochainComplex (ModuleCat ℝ) ℕ` share model universe `uE` and `uC`. -/

universe v uE uC uV

variable {E E' : Type uE} {H H' A A' K K' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace K]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [NormedAddCommGroup A'] [NormedSpace ℝ A'] [TopologicalSpace K']

namespace Prefunctor

variable {C D : Type uC} [Quiver C] [Quiver D] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
  [ChartedSpace H C] [ChartedSpace K (Quiver.Total C)]
  [ChartedSpace H' D] [ChartedSpace K' (Quiver.Total D)]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ A K}
  {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ A' K'}
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]
  {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Contravariant cochain map on `invariantDeRhamComplex` induced by a smooth prefunctor. -/
def invariantDeRhamComplexMap (Φ : C ⥤q D) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal) :
    TauCeti.Quiver.invariantDeRhamComplex I' J' hs' ht' V ⟶
      TauCeti.Quiver.invariantDeRhamComplex I J hs ht V :=
  CochainComplex.ofHom
    (fun k ↦ (TauCeti.Quiver.invariantDeRhamComplexXIso I' J' hs' ht' V k).hom ≫
      ModuleCat.ofHom (Φ.invariantFormsPullback (hs := hs) (ht := ht)
        (hs' := hs') (ht' := ht') (V := V) (k := k) hΦ hΦ₁) ≫
      (TauCeti.Quiver.invariantDeRhamComplexXIso I J hs ht V k).inv)
    fun k ↦ by
      rw [← cancel_mono (TauCeti.Quiver.invariantDeRhamComplexXIso I J hs ht V (k + 1)).hom]
      simp only [Category.assoc, TauCeti.Quiver.invariantDeRhamComplex_d, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id, TauCeti.Quiver.invariantDeRhamComplex_d_assoc]
      ext φ : 2; simpa using Φ.mextDerivₗ_invariantFormsPullback hΦ hΦ₁
        ((TauCeti.Quiver.invariantDeRhamComplexXIso I' J' hs' ht' V k).hom φ)

/-- Under `invariantDeRhamComplexXIso`, `invariantDeRhamComplexMap` acts by form pullback. -/
@[reassoc]
theorem invariantDeRhamComplexMap_f (Φ : C ⥤q D) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal) (k : ℕ) :
    (Φ.invariantDeRhamComplexMap (hs := hs) (ht := ht) (hs' := hs') (ht' := ht')
        (V := V) hΦ hΦ₁).f k ≫
        (TauCeti.Quiver.invariantDeRhamComplexXIso I J hs ht V k).hom =
      (TauCeti.Quiver.invariantDeRhamComplexXIso I' J' hs' ht' V k).hom ≫
        ModuleCat.ofHom (Φ.invariantFormsPullback (hs := hs) (ht := ht)
          (hs' := hs') (ht' := ht') (V := V) (k := k) hΦ hΦ₁) := by
  simp [invariantDeRhamComplexMap]

/-- The identity prefunctor induces the identity cochain map on `invariantDeRhamComplex`. -/
@[simp]
theorem invariantDeRhamComplexMap_id :
    (𝟭q C).invariantDeRhamComplexMap (hs := hs) (ht := ht) (hs' := hs) (ht' := ht)
        (V := V) contMDiff_id contMDiff_id = 𝟙 _ := by
  ext k : 1; dsimp [invariantDeRhamComplexMap]; rw [invariantFormsPullback_id]; simp

/-- Induced cochain maps on `invariantDeRhamComplex` reverse composition of smooth prefunctors. -/
theorem invariantDeRhamComplexMap_comp {E'' : Type uE} {H'' A'' K'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    [NormedAddCommGroup A''] [NormedSpace ℝ A''] [TopologicalSpace K'']
    {B : Type uC} [Quiver B] [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
    [ChartedSpace H'' B] [ChartedSpace K'' (Quiver.Total B)]
    {I'' : ModelWithCorners ℝ E'' H''} {J'' : ModelWithCorners ℝ A'' K''}
    [IsManifold I'' ∞ B] [IsManifold J'' ∞ (Quiver.Total B)]
    {hs'' : ContMDiff J'' I'' ∞ (Quiver.Total.left : Quiver.Total B → B)}
    {ht'' : ContMDiff J'' I'' ∞ (Quiver.Total.right : Quiver.Total B → B)}
    (Φ : C ⥤q D) (Ψ : D ⥤q B) (hΦ : ContMDiff I I' ∞ Φ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.mapTotal) (hΨ : ContMDiff I' I'' ∞ Ψ.obj)
    (hΨ₁ : ContMDiff J' J'' ∞ Ψ.mapTotal) :
    (Φ ⋙q Ψ).invariantDeRhamComplexMap (hs := hs) (ht := ht) (hs' := hs'') (ht' := ht'')
        (V := V) (hΨ.comp hΦ) (Prefunctor.mapTotal_comp Φ Ψ ▸ hΨ₁.comp hΦ₁) =
      Ψ.invariantDeRhamComplexMap (hs := hs') (ht := ht') hΨ hΨ₁ ≫
        Φ.invariantDeRhamComplexMap hΦ hΦ₁ := by
  ext k : 1; rw [HomologicalComplex.comp_f]; dsimp [invariantDeRhamComplexMap]
  rw [invariantFormsPullback_comp (hs' := hs') (ht' := ht') Φ Ψ hΦ hΦ₁ hΨ hΨ₁]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]; rfl

end Prefunctor

section CategoryChainMaps

variable {C D : Type uC} [Category.{v} C] [Category.{v} D] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace (Quiver.Total C)] [TopologicalSpace (Quiver.Total D)]
  [ChartedSpace H C] [ChartedSpace K (Quiver.Total C)]
  [ChartedSpace H' D] [ChartedSpace K' (Quiver.Total D)]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ A K}
  {I' : ModelWithCorners ℝ E' H'} {J' : ModelWithCorners ℝ A' K'}
  [IsManifold I ∞ C] [IsManifold J ∞ (Quiver.Total C)]
  [IsManifold I' ∞ D] [IsManifold J' ∞ (Quiver.Total D)]

namespace CategoryTheory.Functor

section ProperMap

variable {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Cochain map on `compactlySupportedInvariantDeRhamComplex` from a coarse-proper functor. -/
def compactlySupportedInvariantDeRhamComplexMap (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom)) :
    TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex I' J' hs' ht' V ⟶
      TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex I J hs ht V :=
  CochainComplex.ofHom
    (fun k ↦ (TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I' J' hs' ht' V k).hom ≫
      ModuleCat.ofHom (Φ.compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht)
        (hs' := hs') (ht' := ht') (V := V) (k := k) hΦ hΦ₁ hp) ≫
      (TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I J hs ht V k).inv)
    fun k ↦ by
      rw [← cancel_mono
        (TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I J hs ht V (k + 1)).hom]
      simp only [Category.assoc, TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex_d,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
        TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex_d_assoc]
      ext φ : 2; simpa using Φ.mextDerivₗ_compactlySupportedInvariantFormsPullback hΦ hΦ₁ hp
        ((TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I' J' hs' ht' V k).hom φ)

/-- Under `compactlySupportedInvariantDeRhamComplexXIso`, the map acts by form pullback. -/
@[reassoc]
theorem compactlySupportedInvariantDeRhamComplexMap_f (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom)) (k : ℕ) :
    (Φ.compactlySupportedInvariantDeRhamComplexMap (hs := hs) (ht := ht) (hs' := hs') (ht' := ht')
        (V := V) hΦ hΦ₁ hp).f k ≫
        (TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I J hs ht V k).hom =
      (TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I' J' hs' ht' V k).hom ≫
        ModuleCat.ofHom (Φ.compactlySupportedInvariantFormsPullback (hs := hs) (ht := ht)
          (hs' := hs') (ht' := ht') (V := V) (k := k) hΦ hΦ₁ hp) := by
  simp [compactlySupportedInvariantDeRhamComplexMap]

/-- The identity functor acts as the identity on `compactlySupportedInvariantDeRhamComplex`. -/
@[simp]
theorem compactlySupportedInvariantDeRhamComplexMap_id :
    (𝟭 C).compactlySupportedInvariantDeRhamComplexMap
        (hs := hs) (ht := ht) (hs' := hs) (ht' := ht) (V := V) contMDiff_id contMDiff_id (by
          change IsProperMap (X := Quotient (isIsomorphicSetoid C))
            (Y := Quotient (isIsomorphicSetoid C)) (isomorphismClasses.map (𝟙 (Cat.of C)))
          rw [isomorphismClasses.map_id]; exact isProperMap_id) = 𝟙 _ := by
  ext k : 1; dsimp [compactlySupportedInvariantDeRhamComplexMap]
  rw [compactlySupportedInvariantFormsPullback_id]; simp

/-- Induced cochain maps reverse composition of smooth functors with proper coarse maps. -/
theorem compactlySupportedInvariantDeRhamComplexMap_comp {E'' : Type uE} {H'' A'' K'' : Type*}
    [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
    [NormedAddCommGroup A''] [NormedSpace ℝ A''] [TopologicalSpace K'']
    {B : Type uC} [Category.{v} B] [TopologicalSpace B] [TopologicalSpace (Quiver.Total B)]
    [ChartedSpace H'' B] [ChartedSpace K'' (Quiver.Total B)]
    {I'' : ModelWithCorners ℝ E'' H''} {J'' : ModelWithCorners ℝ A'' K''}
    [IsManifold I'' ∞ B] [IsManifold J'' ∞ (Quiver.Total B)]
    {hs'' : ContMDiff J'' I'' ∞ (Quiver.Total.left : Quiver.Total B → B)}
    {ht'' : ContMDiff J'' I'' ∞ (Quiver.Total.right : Quiver.Total B → B)}
    (Φ : C ⥤ D) (Ψ : D ⥤ B)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ : ContMDiff I' I'' ∞ Ψ.obj) (hΨ₁ : ContMDiff J' J'' ∞ Ψ.toPrefunctor.mapTotal)
    (hpΦ : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    (hpΨ : IsProperMap (X := Quotient (isIsomorphicSetoid D))
      (Y := Quotient (isIsomorphicSetoid B)) (isomorphismClasses.map Ψ.toCatHom)) :
    (Φ ⋙ Ψ).compactlySupportedInvariantDeRhamComplexMap
        (hs := hs) (ht := ht) (hs' := hs'') (ht' := ht'') (V := V) (hΨ.comp hΦ)
        (Prefunctor.mapTotal_comp Φ.toPrefunctor Ψ.toPrefunctor ▸ hΨ₁.comp hΦ₁) (by
          change IsProperMap (X := Quotient (isIsomorphicSetoid C))
            (Y := Quotient (isIsomorphicSetoid B))
            (isomorphismClasses.map (Φ.toCatHom ≫ Ψ.toCatHom))
          rw [isomorphismClasses.map_comp]; exact hpΨ.comp hpΦ) =
      Ψ.compactlySupportedInvariantDeRhamComplexMap (hs := hs') (ht := ht') hΨ hΨ₁ hpΨ ≫
        Φ.compactlySupportedInvariantDeRhamComplexMap hΦ hΦ₁ hpΦ := by
  ext k : 1; rw [HomologicalComplex.comp_f]; dsimp [compactlySupportedInvariantDeRhamComplexMap]
  rw [compactlySupportedInvariantFormsPullback_comp (hs' := hs') (ht' := ht')
    Φ Ψ hΦ hΦ₁ hΨ hΨ₁ hpΦ hpΨ]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]; rfl

/-- Pullback on `compactlySupportedInvariantDeRhamComplex` commutes with the inclusion `ι`. -/
@[reassoc]
theorem compactlySupportedInvariantDeRhamComplexMap_ι (Φ : C ⥤ D)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom)) :
    Φ.compactlySupportedInvariantDeRhamComplexMap
        (hs := hs) (ht := ht) (hs' := hs') (ht' := ht') (V := V) hΦ hΦ₁ hp ≫
        TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex.ι I J hs ht V =
      TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex.ι I' J' hs' ht' V ≫
        Φ.toPrefunctor.invariantDeRhamComplexMap hΦ hΦ₁ := by
  ext k : 1
  rw [← cancel_mono (TauCeti.Quiver.invariantDeRhamComplexXIso I J hs ht V k).hom,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc, Category.assoc,
    TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex.ι_f,
    compactlySupportedInvariantDeRhamComplexMap_f_assoc, Prefunctor.invariantDeRhamComplexMap_f,
    TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex.ι_f_assoc]
  ext φ : 2; apply Subtype.ext
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    Submodule.coe_inclusion, Prefunctor.coe_invariantFormsPullback,
    coe_compactlySupportedInvariantFormsPullback]; rfl

end ProperMap

section EtaleIso

variable [IsGroupoid D] [TauCeti.IsTopologicalGroupoid D]
  (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]

open TauCeti

/-- A full, essentially surjective étale refinement induces an isomorphism on
`invariantDeRhamComplex`. -/
theorem isIso_invariantDeRhamComplexMap (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    IsIso (Φ.toPrefunctor.invariantDeRhamComplexMap
      (hs := hs.contMDiff) (ht := ht) (hs' := hs'.contMDiff) (ht' := ht'.contMDiff)
      (V := V) hΦ.contMDiff hΦ₁) := by
  have hbij (k : ℕ) : IsIso (ModuleCat.ofHom
      (Φ.toPrefunctor.invariantFormsPullback (hs := hs.contMDiff) (ht := ht)
        (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) (k := k) hΦ.contMDiff hΦ₁) :
      ModuleCat.of ℝ (TauCeti.Quiver.invariantForms I' J' hs'.contMDiff ht'.contMDiff V k) ⟶
        ModuleCat.of ℝ (TauCeti.Quiver.invariantForms I J hs.contMDiff ht V k)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨Φ.invariantFormsPullback_injective hΦ hΦ₁ ht',
      Φ.invariantFormsPullback_surjective hs ht hs' ht' hΦ hΦ₁⟩
  have (k : ℕ) : IsIso ((Φ.toPrefunctor.invariantDeRhamComplexMap (hs := hs.contMDiff) (ht := ht)
      (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) hΦ.contMDiff hΦ₁).f k) := by
    dsimp [Prefunctor.invariantDeRhamComplexMap]; infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Étale-refinement isomorphism of invariant de Rham complexes.** -/
def invariantDeRhamComplexIso (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    TauCeti.Quiver.invariantDeRhamComplex I' J' hs'.contMDiff ht'.contMDiff V ≅
      TauCeti.Quiver.invariantDeRhamComplex I J hs.contMDiff ht V :=
  have := Φ.isIso_invariantDeRhamComplexMap V hs ht hs' ht' hΦ hΦ₁
  asIso (Φ.toPrefunctor.invariantDeRhamComplexMap (hs := hs.contMDiff) (ht := ht)
    (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) hΦ.contMDiff hΦ₁)

/-- The forward morphism of `invariantDeRhamComplexIso` is `invariantDeRhamComplexMap`. -/
@[simp]
theorem invariantDeRhamComplexIso_hom (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    (Φ.invariantDeRhamComplexIso V hs ht hs' ht' hΦ hΦ₁).hom =
      Φ.toPrefunctor.invariantDeRhamComplexMap (hs := hs.contMDiff) (ht := ht)
        (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) hΦ.contMDiff hΦ₁ := (rfl)

/-- **Étale-refinement linear equivalence on invariant de Rham cohomology.** -/
def invariantDeRhamCohomologyEquiv (Φ : C ⥤ D) [Φ.Full] [Φ.EssSurj]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (k : ℕ) :
    TauCeti.Quiver.invariantDeRhamCohomology I' J' hs'.contMDiff ht'.contMDiff V k ≃ₗ[ℝ]
      TauCeti.Quiver.invariantDeRhamCohomology I J hs.contMDiff ht V k :=
  (HomologicalComplex.homologyMapIso
    (Φ.invariantDeRhamComplexIso V hs ht hs' ht' hΦ hΦ₁) k).toLinearEquiv

/-- A full, essentially surjective étale refinement reflecting isomorphisms induces an isomorphism
on `compactlySupportedInvariantDeRhamComplex`. -/
theorem isIso_compactlySupportedInvariantDeRhamComplexMap (Φ : C ⥤ D)
    [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom)) :
    IsIso (Φ.compactlySupportedInvariantDeRhamComplexMap
      (hs := hs.contMDiff) (ht := ht) (hs' := hs'.contMDiff) (ht' := ht'.contMDiff)
      (V := V) hΦ.contMDiff hΦ₁ hp) := by
  have hbij (k : ℕ) : IsIso (ModuleCat.ofHom
      (Φ.compactlySupportedInvariantFormsPullback (hs := hs.contMDiff) (ht := ht)
        (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) (k := k) hΦ.contMDiff hΦ₁ hp) :
      ModuleCat.of ℝ
          (TauCeti.Quiver.compactlySupportedInvariantForms I' J' hs'.contMDiff ht'.contMDiff V k) ⟶
        ModuleCat.of ℝ
          (TauCeti.Quiver.compactlySupportedInvariantForms I J hs.contMDiff ht V k)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    convert (Φ.compactlySupportedInvariantFormsEquiv hs ht hs' ht' hΦ hΦ₁
      (V := V) (k := k)).bijective
    ext φ : 2
    simp only [ModuleCat.hom_ofHom, coe_compactlySupportedInvariantFormsPullback,
      coe_compactlySupportedInvariantFormsEquiv_apply]
  have (k : ℕ) : IsIso ((Φ.compactlySupportedInvariantDeRhamComplexMap (hs := hs.contMDiff)
      (ht := ht) (hs' := hs'.contMDiff) (ht' := ht'.contMDiff)
      (V := V) hΦ.contMDiff hΦ₁ hp).f k) := by
    dsimp [compactlySupportedInvariantDeRhamComplexMap]; infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **Étale-refinement isomorphism of compact-coarse-support invariant de Rham complexes.** -/
def compactlySupportedInvariantDeRhamComplexIso (Φ : C ⥤ D)
    [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal) :
    TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex I' J' hs'.contMDiff ht'.contMDiff V ≅
      TauCeti.Quiver.compactlySupportedInvariantDeRhamComplex I J hs.contMDiff ht V :=
  let hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom) :=
    coe_isomorphismClassesHomeomorphOfEssSurj Φ hΦ.contMDiff.continuous hΦ.isOpenMap
      hs'.contMDiff.continuous ht'.isOpenMap ▸
      (Φ.isomorphismClassesHomeomorphOfEssSurj hΦ.contMDiff.continuous hΦ.isOpenMap
        hs'.contMDiff.continuous ht'.isOpenMap).isProperMap
  have := Φ.isIso_compactlySupportedInvariantDeRhamComplexMap V hs ht hs' ht' hΦ hΦ₁ hp
  asIso (Φ.compactlySupportedInvariantDeRhamComplexMap (hs := hs.contMDiff) (ht := ht)
    (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) hΦ.contMDiff hΦ₁ hp)

/-- Forward morphism of `compactlySupportedInvariantDeRhamComplexIso` is the pullback map. -/
theorem compactlySupportedInvariantDeRhamComplexIso_hom (Φ : C ⥤ D)
    [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hp : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom)) :
    (Φ.compactlySupportedInvariantDeRhamComplexIso V hs ht hs' ht' hΦ hΦ₁).hom =
      Φ.compactlySupportedInvariantDeRhamComplexMap (hs := hs.contMDiff) (ht := ht)
        (hs' := hs'.contMDiff) (ht' := ht'.contMDiff) (V := V) hΦ.contMDiff hΦ₁ hp := (rfl)

/-- **Étale-refinement linear equivalence on compact-coarse-support de Rham cohomology.** -/
def compactlySupportedInvariantDeRhamCohomologyEquiv (Φ : C ⥤ D)
    [Φ.Full] [Φ.EssSurj] [Φ.ReflectsIsomorphisms]
    (hs : IsLocalDiffeomorph J I ∞ (Quiver.Total.left : Quiver.Total C → C))
    (ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C))
    (hs' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.left : Quiver.Total D → D))
    (ht' : IsLocalDiffeomorph J' I' ∞ (Quiver.Total.right : Quiver.Total D → D))
    (hΦ : IsLocalDiffeomorph I I' ∞ Φ.obj) (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (k : ℕ) :
    TauCeti.Quiver.compactlySupportedInvariantDeRhamCohomology
        I' J' hs'.contMDiff ht'.contMDiff V k ≃ₗ[ℝ]
      TauCeti.Quiver.compactlySupportedInvariantDeRhamCohomology I J hs.contMDiff ht V k :=
  (HomologicalComplex.homologyMapIso
    (Φ.compactlySupportedInvariantDeRhamComplexIso V hs ht hs' ht' hΦ hΦ₁) k).toLinearEquiv

end EtaleIso

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {hs : ContMDiff J I ∞ (Quiver.Total.left : Quiver.Total C → C)}
  {ht : ContMDiff J I ∞ (Quiver.Total.right : Quiver.Total C → C)}
  {hs' : ContMDiff J' I' ∞ (Quiver.Total.left : Quiver.Total D → D)}
  {ht' : ContMDiff J' I' ∞ (Quiver.Total.right : Quiver.Total D → D)}
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ Ψ : C ⥤ D}

/-- Smooth natural transformations identify induced cochain maps on `invariantDeRhamComplex`. -/
theorem invariantDeRhamComplexMap_eq (η : Φ ⟶ Ψ)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΨ : ContMDiff I I' ∞ Ψ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ₁ : ContMDiff J J' ∞ Ψ.toPrefunctor.mapTotal)
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D)) :
    Φ.toPrefunctor.invariantDeRhamComplexMap
        (hs := hs) (ht := ht) (hs' := hs') (ht' := ht') (V := V) hΦ hΦ₁ =
      Ψ.toPrefunctor.invariantDeRhamComplexMap hΨ hΨ₁ := by
  ext k : 1; rw [← cancel_mono (TauCeti.Quiver.invariantDeRhamComplexXIso I J hs ht V k).hom,
    Prefunctor.invariantDeRhamComplexMap_f, Prefunctor.invariantDeRhamComplexMap_f,
    η.invariantFormsPullback_eq hΦ hΨ hΦ₁ hΨ₁ hη]

/-- Smooth natural transformations identify cochain maps on coarse-compact complexes. -/
theorem compactlySupportedInvariantDeRhamComplexMap_eq (η : Φ ⟶ Ψ)
    (hΦ : ContMDiff I I' ∞ Φ.obj) (hΨ : ContMDiff I I' ∞ Ψ.obj)
    (hΦ₁ : ContMDiff J J' ∞ Φ.toPrefunctor.mapTotal)
    (hΨ₁ : ContMDiff J J' ∞ Ψ.toPrefunctor.mapTotal)
    (hpΦ : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Φ.toCatHom))
    (hpΨ : IsProperMap (X := Quotient (isIsomorphicSetoid C))
      (Y := Quotient (isIsomorphicSetoid D)) (isomorphismClasses.map Ψ.toCatHom))
    (hη : ContMDiff I J' ∞ fun x ↦ (⟨Φ.obj x, Ψ.obj x, η.app x⟩ : Quiver.Total D)) :
    Φ.compactlySupportedInvariantDeRhamComplexMap
        (hs := hs) (ht := ht) (hs' := hs') (ht' := ht') (V := V) hΦ hΦ₁ hpΦ =
      Ψ.compactlySupportedInvariantDeRhamComplexMap hΨ hΨ₁ hpΨ := by
  ext k : 1; rw [← cancel_mono
      (TauCeti.Quiver.compactlySupportedInvariantDeRhamComplexXIso I J hs ht V k).hom,
    Functor.compactlySupportedInvariantDeRhamComplexMap_f,
    Functor.compactlySupportedInvariantDeRhamComplexMap_f,
    η.compactlySupportedInvariantFormsPullback_eq hΦ hΨ hΦ₁ hΨ₁ hpΦ hpΨ hη]

end CategoryTheory.NatTrans

end CategoryChainMaps

end ChainMaps
