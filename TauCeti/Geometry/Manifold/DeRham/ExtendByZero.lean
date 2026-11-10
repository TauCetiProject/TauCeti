/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.DifferentialForm.Opens
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Topology.Sets.Opens
import TauCeti.Geometry.Manifold.DeRham.DegreeZero
import TauCeti.Geometry.Manifold.DifferentialForm.Support
import Mathlib.Geometry.Manifold.PartitionOfUnity

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
* `TauCeti.compactlySupportedForms.exists_sum_extendByZero`: every compactly supported form is
  a finite sum of extensions by zero from an arbitrary open cover.
* `TauCeti.compactlySupportedForms.mextDerivₗ_extendByZero`: it commutes with the exterior
  derivative.
* `TauCeti.compactlySupportedDeRhamComplex.extendByZero`: the induced cochain map of compactly
  supported de Rham complexes.
* `TauCeti.compactlySupportedDeRhamCohomology.extendByZero`: the induced map on compactly supported
  de Rham cohomology, computed on classes by `extendByZero_mk`.
* `TauCeti.compactlySupportedDeRhamCohomology.exists_sum_extendByZero`: in degree at least the
  model dimension, every class is a finite sum of extensions by zero from an open cover.
* `TauCeti.compactlySupportedDeRhamCohomology.extendByZeroTop`: extension by zero from an open
  subset into the whole manifold on compactly supported cohomology. A class of a form supported in
  `U` comes from `U` (`mk_mem_range_extendByZeroTop`), and in the top degree the classes from the
  members of an open cover span (`eq_top_of_forall_range_extendByZeroTop_le`).
* `TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms` and
  `TauCeti.mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_closedForms`: let `η` be a
  smooth form on `W`, exact on an open subset `U ≤ W`, and let a smooth function on `W` vanish near
  `W \ U` and equal one off a compact set. Then `dη` is the exterior derivative of a compactly
  supported form. In degree zero it suffices that `W \ U` is compact, `U` is preconnected and `η`
  is locally constant on `U`.

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
            hx).mem_smoothBundleForms⟩,
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

/-- A compactly supported smooth form on an open subset is a finite sum of extensions by zero
from any open cover. The summands need not be closed, even if the original form is closed. -/
theorem exists_sum_extendByZero [FiniteDimensional ℝ E] [IsManifold I ∞ M]
    {W : Opens M} [SigmaCompactSpace W] {ι : Type*} (U : ι → Opens M)
    (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U) (k : ℕ)
    (φ : compactlySupportedForms I W k) :
    ∃ s : Finset ι, ∃ ψ : ∀ i, compactlySupportedForms I (U i) k,
      φ = ∑ i ∈ s, extendByZero (hU i) k (ψ i) := by
  classical
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology W := ChartedSpace.secondCountable_of_sigmaCompact H W
  have : LocallyCompactSpace W := ChartedSpace.locallyCompactSpace H W
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i ↦ {x : W | (x : M) ∈ U i})
    (fun i ↦ (U i).isOpen.preimage continuous_subtype_val) (fun x _ ↦ by
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover x.2)
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  -- Use the model-fibre view for function-support lemmas, whose codomain is nondependent.
  let θ (i : ι) : compactlySupportedForms I W k :=
    ⟨⟨fun x ↦ ρ i x • φ.1.1 x,
        (φ.1.isSmoothForm.fun_smul (ρ i).contMDiff).mem_smoothBundleForms⟩,
      (mem_compactlySupportedForms I).mpr <|
        ((mem_compactlySupportedForms I).mp φ.2).of_isClosed_subset (isClosed_tsupport _)
          (_root_.tsupport_smul_subset_right (ρ i)
            (show W → E [⋀^Fin k]→L[ℝ] ℝ from φ.1.1))⟩
  have hθ (i : ι) : θ i ∈ LinearMap.range (extendByZero (hU i) k) :=
    (mem_range_extendByZero_iff (hU i)).mpr <|
      (_root_.tsupport_smul_subset_left (ρ i)
        (show W → E [⋀^Fin k]→L[ℝ] ℝ from φ.1.1)).trans (hρ i)
  choose ψ hψ using hθ
  obtain ⟨s, hs, -⟩ := RoughForm.exists_finset_partition_eq φ.1.1
    ((mem_compactlySupportedForms I).mp φ.2) ρ.toPartitionOfUnity
  refine ⟨s, ψ, ?_⟩
  simp_rw [hψ]
  refine Subtype.ext <| Subtype.ext ?_
  exact hs.trans (by ext x; simp [θ])

/-- Extension by zero of compactly supported forms commutes with the exterior derivative. -/
theorem mextDerivₗ_extendByZero [IsManifold I 2 M] {U W : Opens M} (h : U ≤ W) (k : ℕ)
    (φ : compactlySupportedForms I U k) :
    mextDerivₗ I W k (extendByZero h k φ) = extendByZero h (k + 1) (mextDerivₗ I U k φ) :=
  Subtype.ext <| Subtype.ext <| by
    simp only [coe_mextDerivₗ, mextDerivₗ_apply, coe_extendByZero]
    exact RoughForm.mextDeriv_extendByZero h fun _ hx ↦
      RoughForm.eventually_extendByZero_eq_zero h ((mem_compactlySupportedForms I).mp φ.2) hx

end compactlySupportedForms

section ClosedForms

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

/-- Viewing a compactly supported form as closed in top degree commutes with extension by zero. -/
@[simp]
theorem compactlySupportedForms.toClosedOfFinrankLe_extendByZero [FiniteDimensional ℝ E]
    {U W : Opens M} (h : U ≤ W) {k : ℕ} (hk : Module.finrank ℝ E ≤ k)
    (φ : compactlySupportedForms I U k) :
    toClosedOfFinrankLe I hk (extendByZero h k φ) =
      compactlySupportedClosedForms.extendByZero h k (toClosedOfFinrankLe I hk φ) := by
  apply Subtype.ext ∘ Subtype.ext
  simp only [coe_toClosedOfFinrankLe, coe_extendByZero,
    compactlySupportedClosedForms.coe_extendByZero]

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

/-- Every compactly supported class in degree at least the model dimension is a finite sum of
classes extended by zero from the members of an arbitrary open cover. -/
theorem exists_sum_extendByZero [FiniteDimensional ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    {W : Opens M} [SigmaCompactSpace W] {ι : Type*} (U : ι → Opens M)
    (hU : ∀ i, U i ≤ W) (hcover : W ≤ iSup U) {n : ℕ} (hn : Module.finrank ℝ E ≤ n)
    (c : compactlySupportedDeRhamCohomology I W n) :
    ∃ s : Finset ι, ∃ d : ∀ i, compactlySupportedDeRhamCohomology I (U i) n,
      c = ∑ i ∈ s, extendByZero (hU i) n (d i) := by
  classical
  obtain ⟨φ, rfl⟩ := mk_surjective I n c
  let φc : compactlySupportedForms I W n :=
    ⟨φ.1, (compactlySupportedClosedForms_le_compactlySupportedForms I n) φ.2⟩
  obtain ⟨s, ψ, hψ⟩ := compactlySupportedForms.exists_sum_extendByZero U hU hcover n φc
  refine ⟨s, fun i ↦ mk I n (compactlySupportedForms.toClosedOfFinrankLe I hn (ψ i)), ?_⟩
  have hφ := congrArg (compactlySupportedForms.toClosedOfFinrankLe I hn) hψ
  simp only [map_sum, compactlySupportedForms.toClosedOfFinrankLe_extendByZero] at hφ
  have heq : compactlySupportedForms.toClosedOfFinrankLe I hn φc = φ :=
    Subtype.ext (compactlySupportedForms.coe_toClosedOfFinrankLe I hn φc)
  rw [heq] at hφ
  rw [hφ, map_sum]
  simp only [extendByZero_mk]

end compactlySupportedDeRhamCohomology

/-- The map induced on cohomology by the cochain map of extension by zero is extension by zero on
compactly supported cohomology. -/
theorem compactlySupportedDeRhamComplex.homologyMap_extendByZero {U W : Opens M} (h : U ≤ W)
    (k : ℕ) :
    HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.extendByZero (I := I) h) k =
      ModuleCat.ofHom (compactlySupportedDeRhamCohomology.extendByZero h k) :=
  (rfl)

/-! ### Compactly supported primitives from exactness near infinity

Let `U ≤ W` be open subsets whose difference `W \ U` stays in a compact set. A form `η` on `W`
whose restriction to `U` is exact, `η = dθ` on `U`, differs from a compactly supported form by an
exact form: for a smooth function `ρ` on `W` vanishing near `W \ U` and equal to one off a compact
set, the form `η - d(ρ θ)`, with `ρ θ` extended by zero from `U`, vanishes wherever `ρ` is
identically one. Hence `dη` is the exterior derivative of a compactly supported form. In degree
zero the same holds when `U` is preconnected and `η` is locally constant on `U`: then `η` is
constant on `U`, and subtracting that constant leaves a form supported in `W \ U`. -/

section ExactNearInfinity

omit [T2Space M]

open Topology

variable {U W : Opens M} (h : U ≤ W)

/-- Let `ρ` be a smooth function on `W` that vanishes near every point of `W` outside `U` and
such that `1 - ρ` has compact support. If a smooth form `η` on `W` is exact on `U`, then `dη` is
the exterior derivative of a compactly supported form on `W`. -/
theorem mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_exactForms {ρ : W → ℝ}
    (hρ : ContMDiff I 𝓘(ℝ) ∞ ρ) (hρU : ∀ x : W, (x : M) ∉ U → ∀ᶠ y in 𝓝 x, ρ y = 0)
    (hρc : HasCompactSupport fun x ↦ 1 - ρ x) {k : ℕ} {η : SmoothForm I W ℝ (k + 1)}
    (hη : SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) η ∈
      exactForms I U (k + 1)) :
    mextDerivₗ I (k + 1) η ∈ exactCompactlySupportedForms I W (k + 2) := by
  rw [exactForms_succ] at hη
  obtain ⟨θ, hθ⟩ := hη
  -- The cut-off primitive `ρ θ`, extended by zero from `U` to `W`.
  let μ : SmoothForm I W ℝ k :=
    ⟨RoughForm.extendByZero W fun y : U ↦ ρ (Opens.inclusion h y) • θ.1 y,
      (θ.isSmoothForm.extendByZero_smul h hρ hρU).mem_smoothBundleForms⟩
  rw [exactCompactlySupportedForms_succ]
  refine ⟨η - mextDerivₗ I k μ, (mem_compactlySupportedForms I).mpr ?_, ?_⟩
  · refine hρc.of_isClosed_subset (_root_.isClosed_tsupport _) <| closure_minimal (fun x hx ↦ ?_)
      (isClosed_tsupport _)
    by_contra hxρ
    -- Near `x` the function `ρ` is identically one, so `x` lies in `U`.
    have hρ1 : ∀ᶠ y in 𝓝 x, ρ y = 1 :=
      (notMem_tsupport_iff_eventuallyEq.mp hxρ).mono fun y hy ↦ (sub_eq_zero.mp hy).symm
    have hxU : (x : M) ∈ U := by
      by_contra hxU
      obtain ⟨y, hy₀, hy₁⟩ := ((hρU x hxU).and hρ1).exists
      exact zero_ne_one (hy₀.symm.trans hy₁)
    obtain ⟨x, rfl⟩ : ∃ x' : U, Opens.inclusion h x' = x := ⟨⟨x, hxU⟩, rfl⟩
    -- On `U` near `x` the cut-off primitive is `θ`, so `dμ` agrees with `dθ = η` at `x`.
    have hμ : ∀ᶠ y in 𝓝 x, (fun y : U ↦ ρ (Opens.inclusion h y) • θ.1 y) y = θ.1 y := by
      filter_upwards [(continuous_inclusion h).continuousAt.eventually hρ1] with y hy
      rw [hy, one_smul]
    have hdμ : mextDeriv μ.1 (Opens.inclusion h x) = mextDeriv θ.1 x := by
      rw [← mpullback_inclusion_apply h (mextDeriv μ.1), mpullback_inclusion_mextDeriv,
        RoughForm.mpullback_inclusion_extendByZero, mextDeriv_congr_of_eventuallyEq hμ]
    have hdθ : mextDeriv θ.1 x = η.1 (Opens.inclusion h x) := by
      rw [← mextDerivₗ_apply, hθ, SmoothForm.coe_mpullback, mpullback_inclusion_apply]
    apply hx
    rw [Submodule.coe_sub, mextDerivₗ_apply, Pi.sub_apply, hdμ, hdθ, sub_self]
    -- The two zeros are the zero of the fibre and the value of the zero form at `x`.
    rfl
  · rw [map_sub, ← LinearMap.comp_apply (mextDerivₗ I (k + 1)), mextDerivₗ_comp_mextDerivₗ,
      LinearMap.zero_apply, sub_zero]

/-- Let `U ≤ W` be open subsets such that the points of `W` outside `U` form a compact set, with
`U` preconnected. If a smooth function `η` on `W` is locally constant on `U`, then its differential
`dη` is the differential of a compactly supported function on `W`. -/
theorem mextDerivₗ_mem_exactCompactlySupportedForms_of_mpullback_mem_closedForms
    [PreconnectedSpace U] (hU : IsCompact {x : W | (x : M) ∉ U}) {η : SmoothForm I W ℝ 0}
    (hη : SmoothForm.mpullback (Opens.inclusion h) (contMDiff_inclusion h) η ∈
      closedForms I U 0) :
    mextDerivₗ I 0 η ∈ exactCompactlySupportedForms I W 1 := by
  obtain ⟨c, hc⟩ := ((mem_closedForms_zero_iff I _).mp hη).exists_eq_const
  -- The constant function `c` on `W`, a closed `0`-form.
  let γ := (closedFormsZeroEquiv I W).symm (LocallyConstant.const W c)
  rw [exactCompactlySupportedForms_succ]
  refine ⟨η - γ.1, (mem_compactlySupportedForms I).mpr ?_, ?_⟩
  · refine hU.of_isClosed_subset (isClosed_tsupport _) <| closure_minimal (fun x hx ↦ ?_)
      (U.isOpen.preimage continuous_subtype_val).isClosed_compl
    intro hxU
    obtain ⟨x, rfl⟩ : ∃ x' : U, Opens.inclusion h x' = x := ⟨⟨x, hxU⟩, rfl⟩
    -- At points of `U`, both `η` and the constant form `γ` take the value `c`.
    have hγ : γ.1.1 = RoughForm.ofFunction I fun _ ↦ c :=
      coe_closedFormsZeroEquiv_symm_apply I (LocallyConstant.const W c)
    have hηx : η.1 (Opens.inclusion h x) 0 = c := by
      have hcx := congrFun hc x
      simp only [SmoothForm.coe_mpullback, mpullback_inclusion_apply, Function.const_apply] at hcx
      exact hcx
    refine hx (ContinuousAlternatingMap.ext fun v ↦ ?_)
    rw [Subsingleton.elim v 0, Submodule.coe_sub, Pi.sub_apply, ContinuousAlternatingMap.sub_apply,
      hγ, RoughForm.ofFunction_apply, hηx, sub_self]
    -- The right-hand side is the zero alternating map evaluated at the empty tuple.
    rfl
  · rw [map_sub, (mem_closedForms_iff_mextDerivₗ_eq_zero I γ.1).mp γ.2, sub_zero]

end ExactNearInfinity

end ClosedForms

/-! ### Extension by zero into the whole manifold

Extension by zero is defined between open subsets of `M`. To extend from an open subset `U` into
`M` itself, extend to the open subset `⊤` and identify `⊤` with `M` through its inclusion
`Diffeomorph.ofTop`. -/

section Top

namespace compactlySupportedDeRhamCohomology

section

variable [IsManifold I 2 M]

/-- Extension by zero from an open subset `U` of a Hausdorff manifold `M` into `M` itself, on
compactly supported cohomology: extension by zero to the open subset `⊤`, identified with `M`
through its inclusion. -/
def extendByZeroTop (U : Opens M) (k : ℕ) :
    compactlySupportedDeRhamCohomology I U k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M k :=
  (equivOfDiffeomorph (Diffeomorph.ofTop ⊤ rfl) k).symm.toLinearMap ∘ₗ extendByZero le_top k

/-- Under the identification of the open subset `⊤` with `M`, extension by zero into `M` is
extension by zero into `⊤`. -/
theorem equivOfDiffeomorph_extendByZeroTop (U : Opens M) (k : ℕ)
    (x : compactlySupportedDeRhamCohomology I U k) :
    equivOfDiffeomorph (Diffeomorph.ofTop ⊤ rfl) k (extendByZeroTop U k x) =
      extendByZero le_top k x := by
  rw [extendByZeroTop, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]

/-- Extension by zero into `M` sends the class of a compactly supported closed form on `U` to the
class of the pullback, along the identification of `M` with the open subset `⊤`, of its extension
by zero to `⊤`. -/
@[simp]
theorem extendByZeroTop_mk (U : Opens M) (k : ℕ) (φ : compactlySupportedClosedForms I U k) :
    extendByZeroTop U k (mk I k φ) =
      mk I k (compactlySupportedClosedForms.mpullback (Diffeomorph.ofTop (⊤ : Opens M) rfl).symm
        (Diffeomorph.ofTop (⊤ : Opens M) rfl).symm.contMDiff
        (Diffeomorph.ofTop (⊤ : Opens M) rfl).symm.toHomeomorph.isProperMap k
        (compactlySupportedClosedForms.extendByZero le_top k φ)) := by
  rw [extendByZeroTop, LinearMap.comp_apply, extendByZero_mk, LinearEquiv.coe_coe,
    equivOfDiffeomorph_symm_apply]
  exact map_mk _ _ _ k _

/-- The class of a compactly supported closed form on `M` supported in an open subset `U` comes from
`H^k_c(U)` by extension by zero. -/
theorem mk_mem_range_extendByZeroTop (U : Opens M) {k : ℕ}
    (φ : compactlySupportedClosedForms I M k)
    (hφ : _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) φ.1.1 ⊆ U) :
    mk I k φ ∈ LinearMap.range (extendByZeroTop U k) := by
  let Φ : (⊤ : Opens M) ≃ₘ⟮I, I⟯ M := Diffeomorph.ofTop ⊤ rfl
  let ψ := compactlySupportedClosedForms.mpullback Φ Φ.contMDiff Φ.toHomeomorph.isProperMap k φ
  have hψ : (ψ : SmoothForm I (⊤ : Opens M) ℝ k).1 = mpullback I I Φ φ.1.1 :=
    compactlySupportedClosedForms.coe_coe_mpullback _ _ _ k φ
  have hψc := compactlySupportedClosedForms_le_compactlySupportedForms I k ψ.2
  -- The pullback of `φ` to `⊤` is supported in `U`, so it is an extension by zero from `U`.
  obtain ⟨χ, hχ⟩ := (compactlySupportedForms.mem_range_extendByZero_iff (le_top : U ≤ ⊤)
    (φ := ⟨ψ.1, hψc⟩)).mpr <| by
    dsimp only
    rw [hψ]
    refine (RoughForm.tsupport_mpullback_subset_preimage Φ.continuous _).trans fun x hx ↦ ?_
    simpa [Φ, Diffeomorph.coe_ofTop] using hφ hx
  -- The form `χ` is closed, since its extension by zero is.
  have hdχ : compactlySupportedForms.mextDerivₗ I U k χ = 0 :=
    compactlySupportedForms.extendByZero_injective (le_top : U ≤ ⊤) (k + 1) <| by
      rw [map_zero, ← compactlySupportedForms.mextDerivₗ_extendByZero, hχ]
      refine Subtype.ext ?_
      rw [compactlySupportedForms.coe_mextDerivₗ, Submodule.coe_zero]
      exact (mem_closedForms_iff_mextDerivₗ_eq_zero I ψ.1).mp
        (compactlySupportedClosedForms_le_closedForms I k ψ.2)
  refine ⟨mk I k ⟨χ.1, (mem_compactlySupportedClosedForms I).mpr
    ⟨χ.2, (mem_closedForms_iff_mextDerivₗ_eq_zero I χ.1).mpr
      (by simpa using congrArg Subtype.val hdχ)⟩⟩, ?_⟩
  rw [← (equivOfDiffeomorph Φ k).injective.eq_iff, equivOfDiffeomorph_extendByZeroTop,
    extendByZero_mk, equivOfDiffeomorph_mk]
  refine congrArg (mk I k) (Subtype.ext (Subtype.ext ?_))
  rw [compactlySupportedClosedForms.coe_extendByZero,
    ← compactlySupportedForms.coe_extendByZero (le_top : U ≤ ⊤), hχ]

end

/-- In the top degree, a submodule of `H^n_c(M)` containing the classes from every member of a
family of open subsets covering `M` is everything: every class is a finite sum of extensions by zero
from members of the family (`exists_sum_extendByZero`). -/
theorem eq_top_of_forall_range_extendByZeroTop_le [IsManifold I ∞ M] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] {n : ℕ} (hn : Module.finrank ℝ E ≤ n)
    {K : Submodule ℝ (compactlySupportedDeRhamCohomology I M n)} (V : M → Opens M)
    (hxV : ∀ x, x ∈ V x) (hK : ∀ x, LinearMap.range (extendByZeroTop (V x) n) ≤ K) : K = ⊤ := by
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨s, d, hd⟩ := exists_sum_extendByZero V (fun _ ↦ le_top)
    (fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxV x⟩) hn
    (equivOfDiffeomorph (Diffeomorph.ofTop ⊤ rfl) n y)
  have hy : y = ∑ i ∈ s, extendByZeroTop (V i) n (d i) :=
    (equivOfDiffeomorph (Diffeomorph.ofTop ⊤ rfl) n).injective <| by
      rw [hd, map_sum]
      simp only [equivOfDiffeomorph_extendByZeroTop]
  exact hy ▸ K.sum_mem fun i _ ↦ hK i ⟨d i, rfl⟩

end compactlySupportedDeRhamCohomology

end Top

end TauCeti
