/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens

/-!
# Extension by zero of compactly supported forms

For open subsets `U ≤ W` of a Hausdorff manifold, a compactly supported smooth form on `U` extends
by zero to a compactly supported smooth form on `W`: the image of its support is compact, hence
closed in `W`, so the extension vanishes near every point of `W` outside `U`. The exterior
derivative commutes with extension by zero, so extension by zero is a cochain map
`Ω_c^•(U) ⟶ Ω_c^•(W)` and induces a map `H^•_c(U) → H^•_c(W)`. These maps are functorial in the
inclusion. This covariant functoriality of compactly supported de Rham cohomology along open
inclusions is opposite to the contravariant functoriality of de Rham cohomology, and provides the
arrows of the compactly supported Mayer–Vietoris sequence.

The Hausdorff hypothesis cannot be dropped. On the line with two origins, a bump function supported
near one origin, in the chart omitting the other, is compactly supported on that chart, but its
extension by zero is discontinuous at the other origin.

## Main definitions and results

* `TauCeti.compactlySupportedForms.extendByZero`: extension by zero of compactly supported smooth
  forms along an inclusion of open subsets.
* `TauCeti.compactlySupportedForms.extendByZero_injective` and
  `TauCeti.compactlySupportedForms.mem_range_extendByZero_iff`: it is injective, and its image
  consists of the compactly supported forms supported in the smaller open subset.
* `TauCeti.compactlySupportedForms.mextDerivₗ_extendByZero`: it commutes with the exterior
  derivative.
* `TauCeti.compactlySupportedDeRhamComplex.extendByZero`: the induced cochain map of compactly
  supported de Rham complexes.
* `TauCeti.compactlySupportedDeRhamCohomology.extendByZero`: the induced map on compactly supported
  de Rham cohomology, computed on classes by `extendByZero_mk`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17,
  "Cohomology with Compact Support".
* R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*, GTM 82, §2.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

namespace compactlySupportedForms

section Forms

variable [IsManifold I 1 M]

/-- Extension by zero of compactly supported smooth forms along an inclusion `U ≤ W` of open
subsets of a Hausdorff manifold. -/
def extendByZero {U W : Opens M} (h : U ≤ W) (k : ℕ) :
    compactlySupportedForms I U k →ₗ[ℝ] compactlySupportedForms I W k where
  toFun φ :=
    ⟨⟨RoughForm.extendByZero W φ.1.1,
        (φ.1.isSmoothForm.extendByZero h fun _ hx ↦
          RoughForm.eventually_extendByZero_eq_zero h ((mem_compactlySupportedForms I).mp φ.2)
            hx).mem_smoothForms⟩,
      (mem_compactlySupportedForms I).mpr <|
        RoughForm.isCompact_tsupport_extendByZero h ((mem_compactlySupportedForms I).mp φ.2)⟩
  map_add' φ ψ := Subtype.ext <| Subtype.ext <| RoughForm.extendByZero_add W φ.1.1 ψ.1.1
  map_smul' c φ := Subtype.ext <| Subtype.ext <| RoughForm.extendByZero_smul W c φ.1.1

/-- The extension by zero of a compactly supported form is its extension by zero as a rough
form. -/
@[simp]
theorem coe_extendByZero {U W : Opens M} (h : U ≤ W) (k : ℕ) (φ : compactlySupportedForms I U k) :
    ((extendByZero h k φ : SmoothForm I W ℝ k) : RoughForm I W ℝ k) =
      RoughForm.extendByZero W (φ : SmoothForm I U ℝ k).1 :=
  (rfl)

/-- Extension by zero from an open subset to itself is the identity. -/
@[simp]
theorem extendByZero_self (U : Opens M) (k : ℕ) :
    extendByZero (I := I) (le_refl U) k = LinearMap.id :=
  LinearMap.ext fun φ ↦ Subtype.ext <| Subtype.ext <| RoughForm.extendByZero_self φ.1.1

/-- Extending by zero in two steps along `U ≤ V ≤ W` is extending by zero from `U` to `W`. -/
@[simp]
theorem extendByZero_extendByZero {U V W : Opens M} (h₁ : U ≤ V) (h₂ : V ≤ W) (k : ℕ)
    (φ : compactlySupportedForms I U k) :
    extendByZero h₂ k (extendByZero h₁ k φ) = extendByZero (h₁.trans h₂) k φ :=
  Subtype.ext <| Subtype.ext <| RoughForm.extendByZero_extendByZero h₁ W φ.1.1

/-- Extension by zero of compactly supported forms is injective: restricting the extension back to
the smaller open subset recovers the form. -/
theorem extendByZero_injective {U W : Opens M} (h : U ≤ W) (k : ℕ) :
    Function.Injective (extendByZero (I := I) h k) := fun φ ψ hφψ ↦ by
  have := congrArg (fun χ : compactlySupportedForms I W k ↦
    TauCeti.mpullback I I (Opens.inclusion h) (χ : SmoothForm I W ℝ k).1) hφψ
  simp only [coe_extendByZero, RoughForm.mpullback_inclusion_extendByZero] at this
  exact Subtype.ext (Subtype.ext this)

/-- A compactly supported form on `W` is the extension by zero of a compactly supported form on an
open subset `U ≤ W` exactly when its support lies in `U`. -/
theorem mem_range_extendByZero_iff {U W : Opens M} (h : U ≤ W) {k : ℕ}
    {φ : compactlySupportedForms I W k} :
    φ ∈ LinearMap.range (extendByZero h k) ↔
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (φ : SmoothForm I W ℝ k).1 ⊆
        {x | (x : M) ∈ U} := by
  refine ⟨?_, fun hφ ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩
    refine (RoughForm.tsupport_extendByZero_subset h
      ((mem_compactlySupportedForms I).mp ψ.2)).trans ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  -- The restriction of `φ` to `U` is compactly supported, since the support of `φ` is a compact
  -- subset of the image of the embedding of `U` in `W`.
  let ψ : SmoothForm I U ℝ k :=
    SmoothForm.mpullback (I := I) (I' := I) (Opens.inclusion h) (contMDiff_inclusion _) φ
  have hψ : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) ψ.1) := by
    rw [SmoothForm.coe_mpullback]
    exact (Topology.IsInducing.isCompact_preimage' (f := Opens.inclusion h)
        (Topology.IsEmbedding.inclusion h).isInducing ((mem_compactlySupportedForms I).mp φ.2)
        fun x hx ↦ ⟨⟨x, hφ hx⟩, rfl⟩).of_isClosed_subset (_root_.isClosed_tsupport _)
        (RoughForm.tsupport_mpullback_subset_preimage (f := Opens.inclusion h)
          (continuous_inclusion h) _)
  refine ⟨⟨ψ, (mem_compactlySupportedForms I).mpr hψ⟩, Subtype.ext <| Subtype.ext ?_⟩
  funext x
  by_cases hx : (x : M) ∈ U
  · rw [coe_extendByZero, RoughForm.extendByZero_apply_of_mem _ hx, SmoothForm.coe_mpullback,
      mpullback_inclusion_apply]
    -- The inclusion of `U` in `W` sends `⟨x, hx⟩` to `⟨x, h hx⟩`, which is `x` by eta for
    -- subtypes; both hold by definition.
    rfl
  · rw [coe_extendByZero, RoughForm.extendByZero_apply_of_notMem _ hx]
    exact (_root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ)
      fun hx' ↦ hx (hφ hx')).symm

end Forms

/-- Extension by zero of compactly supported forms commutes with the exterior derivative. -/
theorem mextDerivₗ_extendByZero [IsManifold I 2 M] {U W : Opens M} (h : U ≤ W) (k : ℕ)
    (φ : compactlySupportedForms I U k) :
    mextDerivₗ I W k (extendByZero h k φ) = extendByZero h (k + 1) (mextDerivₗ I U k φ) :=
  Subtype.ext <| Subtype.ext <| by
    simp only [coe_mextDerivₗ, mextDerivₗ_apply, coe_extendByZero]
    exact RoughForm.mextDeriv_extendByZero h fun _ hx ↦
      RoughForm.eventually_extendByZero_eq_zero h ((mem_compactlySupportedForms I).mp φ.2) hx

end compactlySupportedForms

variable [IsManifold I 2 M]

namespace compactlySupportedClosedForms

/-- Extension by zero of compactly supported closed forms along an inclusion `U ≤ W` of open
subsets of a Hausdorff manifold. -/
def extendByZero {U W : Opens M} (h : U ≤ W) (k : ℕ) :
    compactlySupportedClosedForms I U k →ₗ[ℝ] compactlySupportedClosedForms I W k :=
  LinearMap.codRestrict _
    ((compactlySupportedForms I W k).subtype ∘ₗ compactlySupportedForms.extendByZero h k ∘ₗ
      Submodule.inclusion (compactlySupportedClosedForms_le_compactlySupportedForms I k))
    fun φ ↦ by
      have hcs := compactlySupportedClosedForms_le_compactlySupportedForms I k φ.2
      have hφ : compactlySupportedForms.mextDerivₗ I U k ⟨φ.1, hcs⟩ = 0 := Subtype.ext <| by
        rw [compactlySupportedForms.coe_mextDerivₗ, Submodule.coe_zero]
        exact (mem_closedForms_iff_mextDerivₗ_eq_zero I φ.1).mp
          (compactlySupportedClosedForms_le_closedForms I k φ.2)
      have h0 := congrArg Subtype.val
        (compactlySupportedForms.mextDerivₗ_extendByZero h k ⟨φ.1, hcs⟩)
      rw [hφ, map_zero, compactlySupportedForms.coe_mextDerivₗ, Submodule.coe_zero] at h0
      exact (mem_compactlySupportedClosedForms I).mpr
        ⟨(compactlySupportedForms.extendByZero h k ⟨φ.1, hcs⟩).2,
          (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr h0⟩

/-- The extension by zero of a compactly supported closed form is its extension by zero as a
rough form. -/
@[simp]
theorem coe_extendByZero {U W : Opens M} (h : U ≤ W) (k : ℕ)
    (φ : compactlySupportedClosedForms I U k) :
    ((extendByZero h k φ : SmoothForm I W ℝ k) : RoughForm I W ℝ k) =
      RoughForm.extendByZero W (φ : SmoothForm I U ℝ k).1 :=
  (rfl)

end compactlySupportedClosedForms

namespace compactlySupportedDeRhamComplex

/-- The cochain map between compactly supported de Rham complexes given by extension by zero along
an inclusion `U ≤ W` of open subsets of a Hausdorff manifold. -/
def extendByZero {U W : Opens M} (h : U ≤ W) :
    compactlySupportedDeRhamComplex I U ⟶ compactlySupportedDeRhamComplex I W :=
  CochainComplex.ofHom
    (fun k ↦ (compactlySupportedDeRhamComplexXIso I k).hom ≫
      ModuleCat.ofHom (compactlySupportedForms.extendByZero h k) ≫
        (compactlySupportedDeRhamComplexXIso I k).inv)
    fun k ↦ by
      rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (M := W) (k + 1)).hom]
      simp only [Category.assoc, compactlySupportedDeRhamComplex_d, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id, compactlySupportedDeRhamComplex_d_assoc]
      ext φ : 2
      simpa using compactlySupportedForms.mextDerivₗ_extendByZero h k
        ((compactlySupportedDeRhamComplexXIso I k).hom φ)

/-- Under the canonical identifications of the objects, the cochain map is extension by zero of
compactly supported forms. -/
@[reassoc]
theorem extendByZero_f {U W : Opens M} (h : U ≤ W) (k : ℕ) :
    (extendByZero (I := I) h).f k ≫ (compactlySupportedDeRhamComplexXIso I (M := W) k).hom =
      (compactlySupportedDeRhamComplexXIso I (M := U) k).hom ≫
        ModuleCat.ofHom (compactlySupportedForms.extendByZero h k) := by
  simp [extendByZero]

/-- Extension by zero from an open subset to itself is the identity cochain map. -/
@[simp]
theorem extendByZero_self (U : Opens M) : extendByZero (I := I) (le_refl U) = 𝟙 _ := by
  ext k : 1
  rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (M := U) k).hom, extendByZero_f,
    compactlySupportedForms.extendByZero_self]
  simp

/-- The cochain maps of extension by zero compose along `U ≤ V ≤ W`. -/
@[simp]
theorem extendByZero_comp_extendByZero {U V W : Opens M} (h₁ : U ≤ V) (h₂ : V ≤ W) :
    extendByZero (I := I) h₁ ≫ extendByZero h₂ = extendByZero (h₁.trans h₂) := by
  ext k : 1
  rw [← cancel_mono (compactlySupportedDeRhamComplexXIso I (M := W) k).hom,
    HomologicalComplex.comp_f, Category.assoc, extendByZero_f, extendByZero_f_assoc,
    extendByZero_f]
  ext φ : 2
  simp

end compactlySupportedDeRhamComplex

namespace compactlySupportedDeRhamCohomology

/-- The map on compactly supported de Rham cohomology induced by extension by zero along an
inclusion `U ≤ W` of open subsets of a Hausdorff manifold. -/
def extendByZero {U W : Opens M} (h : U ≤ W) (k : ℕ) :
    compactlySupportedDeRhamCohomology I U k →ₗ[ℝ] compactlySupportedDeRhamCohomology I W k :=
  (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.extendByZero h) k).hom

/-- Extension by zero sends the class of a compactly supported closed form to the class of its
extension by zero. -/
@[simp]
theorem extendByZero_mk {U W : Opens M} (h : U ≤ W) (k : ℕ)
    (φ : compactlySupportedClosedForms I U k) :
    extendByZero h k (mk I k φ) = mk I k (compactlySupportedClosedForms.extendByZero h k φ) := by
  rw [extendByZero, mk_eq_moduleCatHomologyClass, mk_eq_moduleCatHomologyClass]
  refine HomologicalComplex.homologyMap_moduleCatHomologyClass
    (Z' := compactlySupportedClosedForms I W k) _ _ _
    (compactlySupportedDeRhamComplex.extendByZero (I := I) h) _ _
    (compactlySupportedClosedForms.extendByZero h k) (fun φ ↦ ?_) φ
  have h' := ConcreteCategory.congr_hom
    ((Iso.eq_comp_inv _).mpr (compactlySupportedDeRhamComplex.extendByZero_f (I := I) h k))
    ((compactlySupportedDeRhamComplexXIso I k).inv (Submodule.inclusion
      (compactlySupportedClosedForms_le_compactlySupportedForms I k) φ))
  simp only [Category.assoc, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, Iso.inv_hom_id_apply] at h'
  -- Both sides are the extension by zero of `φ`; the identification of objects is `Iso.refl`.
  exact h'.trans (congrArg (compactlySupportedDeRhamComplexXIso I k).inv.hom (Subtype.ext rfl))

/-- Extension by zero from an open subset to itself is the identity on compactly supported
cohomology. -/
@[simp]
theorem extendByZero_self (U : Opens M) (k : ℕ) :
    extendByZero (I := I) (le_refl U) k = LinearMap.id := by
  rw [extendByZero, compactlySupportedDeRhamComplex.extendByZero_self,
    HomologicalComplex.homologyMap_id, ModuleCat.hom_id]

/-- Extending by zero in two steps along `U ≤ V ≤ W` is extending by zero from `U` to `W` on
compactly supported cohomology. -/
@[simp]
theorem extendByZero_extendByZero {U V W : Opens M} (h₁ : U ≤ V) (h₂ : V ≤ W) (k : ℕ)
    (c : compactlySupportedDeRhamCohomology I U k) :
    extendByZero h₂ k (extendByZero h₁ k c) = extendByZero (h₁.trans h₂) k c := by
  rw [extendByZero, extendByZero, extendByZero,
    ← compactlySupportedDeRhamComplex.extendByZero_comp_extendByZero h₁ h₂,
    HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

end compactlySupportedDeRhamCohomology

/-- The map induced on cohomology by the cochain map of extension by zero is extension by zero on
compactly supported cohomology. -/
theorem compactlySupportedDeRhamComplex.homologyMap_extendByZero {U W : Opens M} (h : U ≤ W)
    (k : ℕ) :
    HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.extendByZero (I := I) h) k =
      ModuleCat.ofHom (compactlySupportedDeRhamCohomology.extendByZero h k) :=
  (rfl)

end TauCeti
