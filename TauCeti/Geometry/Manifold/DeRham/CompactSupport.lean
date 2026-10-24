/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Map
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.DifferentialForm.Support

/-!
# Compactly supported de Rham cohomology

Smooth real-valued forms with compact topological support form a submodule of all smooth forms.
The exterior derivative does not enlarge supports, so these forms are a subcomplex of the de Rham
complex, the compactly supported de Rham complex; its cohomology is compactly supported de Rham
cohomology `H^•_c`.

A compactly supported closed form has a class in `H^•_c`; every class arises this way, and a class
vanishes exactly when its representative is the exterior derivative of a compactly supported form.
The inclusion of complexes induces the comparison `H^•_c(M) → H^•_dR(M)`, which takes the de Rham
class of the representative; it is an isomorphism on compact manifolds, where every form is
compactly supported.

Pullback along a smooth proper map preserves compact support, so `H^•_c` is contravariant for
smooth proper maps. Pullback along a general smooth map does not preserve compact support: the
constant map `ℝ → pt` pulls the constant function `1` back to a function without compact
support.

## Main definitions

* `TauCeti.compactlySupportedForms I M k`: compactly supported smooth `k`-forms.
* `TauCeti.compactlySupportedClosedForms I M k`: compactly supported closed smooth `k`-forms.
* `TauCeti.compactlySupportedDeRhamComplex I M`: the compactly supported de Rham complex.
* `TauCeti.compactlySupportedDeRhamCohomology I M k`: its cohomology.
* `TauCeti.compactlySupportedDeRhamCohomology.mk`: the class of a compactly supported closed form.
* `TauCeti.compactlySupportedDeRhamCohomology.toDeRhamCohomology`: the comparison with de Rham
  cohomology.
* `TauCeti.compactlySupportedDeRhamComplex.ι`: the inclusion into the de Rham complex.
* `TauCeti.compactlySupportedDeRhamComplex.map`: the cochain map induced by a smooth proper map.
* `TauCeti.compactlySupportedDeRhamCohomology.map`: the induced map on cohomology.

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
  add_mem' := RoughForm.isCompact_tsupport_add
  zero_mem' := RoughForm.isCompact_tsupport_zero
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

/-- The differential of the compactly supported de Rham complex, evaluated on an element. -/
theorem compactlySupportedDeRhamComplex_d_apply (k : ℕ)
    (x : (compactlySupportedDeRhamComplex I M).X k) :
    (compactlySupportedDeRhamComplex I M).d k (k + 1) x =
      (compactlySupportedDeRhamComplexXIso I (k + 1)).inv
        (compactlySupportedForms.mextDerivₗ I M k
          ((compactlySupportedDeRhamComplexXIso I k).hom x)) := by
  rw [(Iso.eq_comp_inv _).mpr (compactlySupportedDeRhamComplex_d I (M := M) k),
    ModuleCat.comp_apply, ModuleCat.comp_apply, ConcreteCategory.hom_ofHom]

/-- A closed compactly supported form, viewed in the compactly supported de Rham complex, is
killed by the differential. -/
theorem compactlySupportedDeRhamComplex_d_eq_zero_of_mem_closedForms (k : ℕ)
    {φ : compactlySupportedForms I M k} (hφ : φ.1 ∈ closedForms I M ℝ k) :
    (compactlySupportedDeRhamComplex I M).d k (k + 1)
      ((compactlySupportedDeRhamComplexXIso I k).inv φ) = 0 := by
  have h : compactlySupportedForms.mextDerivₗ I M k φ = 0 :=
    Subtype.ext ((mem_closedForms_iff_mextDerivₗ_eq_zero I φ.1).mp hφ)
  rw [compactlySupportedDeRhamComplex_d_apply]
  simp [h]

variable (M) in
/-- Compactly supported de Rham cohomology is the categorical homology of the compactly
supported de Rham complex. -/
abbrev compactlySupportedDeRhamCohomology (k : ℕ) : Type _ :=
  (compactlySupportedDeRhamComplex I M).homology k

namespace compactlySupportedDeRhamComplex

variable (M) in
/-- The inclusion of the compactly supported de Rham complex into the de Rham complex. -/
def ι : compactlySupportedDeRhamComplex I M ⟶ deRhamComplex I M ℝ :=
  CochainComplex.ofHom
    (fun k ↦ (compactlySupportedDeRhamComplexXIso I k).hom ≫
      ModuleCat.ofHom (compactlySupportedForms I M k).subtype ≫
        (deRhamComplexXIso (𝕜 := ℝ) I k).inv)
    fun k ↦ by
      rw [← cancel_mono (deRhamComplexXIso (𝕜 := ℝ) I (M := M) (k + 1)).hom]
      simp only [Category.assoc, deRhamComplex_d, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id, compactlySupportedDeRhamComplex_d_assoc]
      ext φ : 2
      simp

/-- Under the canonical identifications of the objects, the inclusion is the inclusion of
compactly supported forms into smooth forms. -/
@[reassoc]
theorem ι_f (k : ℕ) :
    (ι I M).f k ≫ (deRhamComplexXIso (𝕜 := ℝ) I (M := M) k).hom =
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

-- This is a submodule of smooth forms rather than the kernel of
-- `compactlySupportedForms.mextDerivₗ`: instance search for `AddCommGroup` on a submodule of
-- `compactlySupportedForms` exceeds the default synthesis budget.
variable (M) in
/-- The submodule of compactly supported closed smooth forms. -/
def compactlySupportedClosedForms (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k) :=
  compactlySupportedForms I M k ⊓ closedForms I M ℝ k

/-- A smooth form is compactly supported and closed when it is both compactly supported and
closed. -/
@[simp]
theorem mem_compactlySupportedClosedForms {k : ℕ} {φ : SmoothForm I M ℝ k} :
    φ ∈ compactlySupportedClosedForms I M k ↔
      φ ∈ compactlySupportedForms I M k ∧ φ ∈ closedForms I M ℝ k :=
  Iff.rfl

/-- A compactly supported closed form is compactly supported. -/
theorem compactlySupportedClosedForms_le_compactlySupportedForms (k : ℕ) :
    compactlySupportedClosedForms I M k ≤ compactlySupportedForms I M k :=
  inf_le_left

/-- A compactly supported closed form is closed. -/
theorem compactlySupportedClosedForms_le_closedForms (k : ℕ) :
    compactlySupportedClosedForms I M k ≤ closedForms I M ℝ k :=
  inf_le_right

variable (M) in
/-- Compactly supported exact forms are exterior derivatives of compactly supported forms in
positive degree, and zero in degree zero. -/
def exactCompactlySupportedForms : (k : ℕ) → Submodule ℝ (SmoothForm I M ℝ k)
  | 0 => ⊥
  | k + 1 => (compactlySupportedForms I M k).map (mextDerivₗ I (F := ℝ) k)

/-- There are no nonzero compactly supported exact forms in degree zero. -/
@[simp]
theorem exactCompactlySupportedForms_zero : exactCompactlySupportedForms I M 0 = ⊥ := (rfl)

/-- In positive degree, compactly supported exact forms are the image of compactly supported
forms under the exterior derivative. -/
@[simp]
theorem exactCompactlySupportedForms_succ (k : ℕ) :
    exactCompactlySupportedForms I M (k + 1) =
      (compactlySupportedForms I M k).map (mextDerivₗ I (F := ℝ) k) := (rfl)

/-- A compactly supported exact form is exact. -/
theorem exactCompactlySupportedForms_le_exactForms (k : ℕ) :
    exactCompactlySupportedForms I M k ≤ exactForms I M ℝ k := by
  cases k with
  | zero => exact bot_le
  | succ k =>
      rw [exactCompactlySupportedForms_succ, exactForms_succ,
        SmoothForm.mextDerivLinearMap_real]
      exact LinearMap.map_le_range

/-- A compactly supported exact form is compactly supported and closed. -/
theorem exactCompactlySupportedForms_le_compactlySupportedClosedForms (k : ℕ) :
    exactCompactlySupportedForms I M k ≤ compactlySupportedClosedForms I M k := by
  intro φ hφ
  refine (mem_compactlySupportedClosedForms I).mpr
    ⟨?_, exactForms_le_closedForms I k (exactCompactlySupportedForms_le_exactForms I k hφ)⟩
  cases k with
  | zero =>
      rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hφ
      exact hφ ▸ zero_mem _
  | succ k =>
      rw [exactCompactlySupportedForms_succ, Submodule.mem_map] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      have h := (compactlySupportedForms.mextDerivₗ I M k ⟨ψ, hψ⟩).2
      rwa [compactlySupportedForms.coe_mextDerivₗ] at h

namespace compactlySupportedDeRhamCohomology

/-- The compactly supported cohomology class of a compactly supported closed form. -/
def mk (k : ℕ) :
    compactlySupportedClosedForms I M k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M k :=
  (compactlySupportedDeRhamComplex I M).moduleCatHomologyClass
    (Z := compactlySupportedClosedForms I M k) (CochainComplex.next ℕ k)
    ((compactlySupportedDeRhamComplexXIso I k).inv.hom ∘ₗ Submodule.inclusion
      (compactlySupportedClosedForms_le_compactlySupportedForms I k))
    fun φ ↦ by
      rw [LinearMap.comp_apply]
      exact compactlySupportedDeRhamComplex_d_eq_zero_of_mem_closedForms I k
        (compactlySupportedClosedForms_le_closedForms I k φ.2)

/-- The class map is the homology class map of the inclusion of compactly supported closed forms
into the compactly supported de Rham complex. -/
theorem mk_eq_moduleCatHomologyClass (k : ℕ) :
    mk I (M := M) k =
      (compactlySupportedDeRhamComplex I M).moduleCatHomologyClass
        (Z := compactlySupportedClosedForms I M k) (CochainComplex.next ℕ k)
        ((compactlySupportedDeRhamComplexXIso I k).inv.hom ∘ₗ Submodule.inclusion
          (compactlySupportedClosedForms_le_compactlySupportedForms I k))
        fun φ ↦ by
          rw [LinearMap.comp_apply]
          exact compactlySupportedDeRhamComplex_d_eq_zero_of_mem_closedForms I k
            (compactlySupportedClosedForms_le_closedForms I k φ.2) :=
  (rfl)

/-- Every compactly supported cohomology class is represented by a compactly supported closed
form. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (mk I (M := M) k) := by
  rw [mk]
  refine (compactlySupportedDeRhamComplex I M).moduleCatHomologyClass_surjective _ _ _
    fun x hx ↦ ?_
  rw [compactlySupportedDeRhamComplex_d_apply] at hx
  have hφ := (LinearEquiv.map_eq_zero_iff
    (compactlySupportedDeRhamComplexXIso I (M := M) (k + 1)).toLinearEquiv.symm).mp hx
  refine ⟨⟨((compactlySupportedDeRhamComplexXIso I k).hom x).1,
    ((compactlySupportedDeRhamComplexXIso I k).hom x).2,
    (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr (congrArg Subtype.val hφ)⟩, ?_⟩
  exact (compactlySupportedDeRhamComplexXIso I k).hom_inv_id_apply x

/-- A compactly supported closed form represents zero precisely when it is the exterior
derivative of a compactly supported form. -/
@[simp]
theorem mk_eq_zero_iff (k : ℕ) (φ : compactlySupportedClosedForms I M k) :
    mk I k φ = 0 ↔ φ.1 ∈ exactCompactlySupportedForms I M k := by
  cases k with
  | zero =>
    rw [mk, (compactlySupportedDeRhamComplex I M).moduleCatHomologyClass_eq_zero_iff _ _ _
        CochainComplex.prev_nat_zero, exactCompactlySupportedForms_zero, Submodule.mem_bot,
      (compactlySupportedDeRhamComplex I M).shape 0 0 (by simp)]
    exact ⟨fun ⟨_, h⟩ ↦ congrArg Subtype.val h.symm, fun h ↦ ⟨0, Subtype.ext h.symm⟩⟩
  | succ k =>
    rw [mk, (compactlySupportedDeRhamComplex I M).moduleCatHomologyClass_eq_zero_iff _ _ _
        (CochainComplex.prev_nat_succ k), exactCompactlySupportedForms_succ, Submodule.mem_map]
    refine ⟨fun ⟨y, hy⟩ ↦ ⟨_, ((compactlySupportedDeRhamComplexXIso I k).hom y).2, ?_⟩,
      fun ⟨ψ, hψ, hψφ⟩ ↦ ⟨(compactlySupportedDeRhamComplexXIso I k).inv ⟨ψ, hψ⟩, ?_⟩⟩
    · rw [compactlySupportedDeRhamComplex_d_apply] at hy
      exact congrArg Subtype.val (LinearEquiv.injective
        (compactlySupportedDeRhamComplexXIso I (M := M) (k + 1)).toLinearEquiv.symm hy)
    · rw [compactlySupportedDeRhamComplex_d_apply]
      exact congrArg (compactlySupportedDeRhamComplexXIso I (k + 1)).inv.hom (Subtype.ext hψφ)

/-- The kernel of the class map is the submodule of compactly supported exact forms inside
compactly supported closed forms. -/
theorem ker_mk (k : ℕ) :
    LinearMap.ker (mk I (M := M) k) =
      (exactCompactlySupportedForms I M k).comap (compactlySupportedClosedForms I M k).subtype := by
  ext φ
  exact mk_eq_zero_iff I k φ

/-- Two compactly supported closed forms have the same class precisely when they differ by a
compactly supported exact form. -/
theorem mk_eq_mk_iff (k : ℕ) (φ ψ : compactlySupportedClosedForms I M k) :
    mk I k φ = mk I k ψ ↔ φ.1 - ψ.1 ∈ exactCompactlySupportedForms I M k := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff, Submodule.coe_sub]

variable (M) in
/-- The comparison map from compactly supported to ordinary de Rham cohomology, induced on
cohomology by the inclusion of complexes. -/
def toDeRhamCohomology (k : ℕ) :
    compactlySupportedDeRhamCohomology I M k →ₗ[ℝ] deRhamCohomology I M ℝ k :=
  (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.ι I M) k).hom

/-- The comparison map sends the class of a compactly supported closed form to the de Rham class
of the underlying closed form. -/
@[simp]
theorem toDeRhamCohomology_mk (k : ℕ) (φ : compactlySupportedClosedForms I M k) :
    toDeRhamCohomology I M k (mk I k φ) =
      deRhamCohomology.mk I k ⟨φ.1, compactlySupportedClosedForms_le_closedForms I k φ.2⟩ := by
  rw [toDeRhamCohomology, mk, deRhamCohomology.mk_eq_moduleCatHomologyClass]
  refine HomologicalComplex.homologyMap_moduleCatHomologyClass (Z' := closedForms I M ℝ k) _ _ _
    (compactlySupportedDeRhamComplex.ι I M) _ _
    (Submodule.inclusion (compactlySupportedClosedForms_le_closedForms I k)) (fun φ ↦ ?_) φ
  have h := ConcreteCategory.congr_hom
    ((Iso.eq_comp_inv _).mpr (compactlySupportedDeRhamComplex.ι_f I (M := M) k))
    ((compactlySupportedDeRhamComplexXIso I k).inv (Submodule.inclusion
      (compactlySupportedClosedForms_le_compactlySupportedForms I k) φ))
  simpa using h

/-- On a compact manifold compactly supported and ordinary de Rham cohomology agree. -/
theorem toDeRhamCohomology_bijective [CompactSpace M] (k : ℕ) :
    Function.Bijective (toDeRhamCohomology I M k) :=
  ConcreteCategory.bijective_of_isIso
    (HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.ι I M) k)

end compactlySupportedDeRhamCohomology

/-- The map induced on cohomology by the inclusion of complexes is the comparison map. -/
theorem compactlySupportedDeRhamComplex.homologyMap_ι (k : ℕ) :
    HomologicalComplex.homologyMap (compactlySupportedDeRhamComplex.ι I M) k =
      ModuleCat.ofHom (compactlySupportedDeRhamCohomology.toDeRhamCohomology I M k) :=
  (rfl)

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

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [IsManifold I'' 2 M'']

/-- Pullback along a smooth proper map preserves compactly supported exact forms. -/
theorem SmoothForm.mpullback_mem_exactCompactlySupportedForms (f : M → M')
    (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) {k : ℕ} {φ : SmoothForm I' M' ℝ k}
    (hφ : φ ∈ exactCompactlySupportedForms I' M' k) :
    SmoothForm.mpullback f hf φ ∈ exactCompactlySupportedForms I M k := by
  cases k with
  | zero =>
      rw [exactCompactlySupportedForms_zero, Submodule.mem_bot] at hφ ⊢
      rw [hφ, map_zero]
  | succ k =>
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      exact ⟨SmoothForm.mpullback f hf ψ, (compactlySupportedForms.mpullback f hf hp k ⟨ψ, hψ⟩).2,
        SmoothForm.mextDerivₗ_mpullback f hf k ψ⟩

namespace compactlySupportedClosedForms

/-- Pullback of compactly supported closed forms along a smooth proper map. -/
def mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    compactlySupportedClosedForms I' M' k →ₗ[ℝ] compactlySupportedClosedForms I M k :=
  (SmoothForm.mpullback (F := ℝ) (k := k) f hf).restrict fun φ hφ ↦
    ⟨(compactlySupportedForms.mpullback f hf hp k ⟨φ, hφ.1⟩).2,
      closedForms.coe_mpullback f hf k ⟨φ, hφ.2⟩ ▸ (closedForms.mpullback f hf k ⟨φ, hφ.2⟩).2⟩

/-- The pullback of a compactly supported closed form is its pullback as a smooth form. -/
@[simp]
theorem coe_mpullback (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ)
    (φ : compactlySupportedClosedForms I' M' k) :
    (mpullback f hf hp k φ : SmoothForm I M ℝ k) = SmoothForm.mpullback f hf φ :=
  (rfl)

/-- Pullback of compactly supported closed forms by the identity is the identity linear map. -/
@[simp]
theorem mpullback_id (k : ℕ) :
    mpullback (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id isProperMap_id k =
      LinearMap.id := by
  ext φ : 1
  apply Subtype.ext
  rw [coe_mpullback, ← compactlySupportedForms.coe_mpullback id contMDiff_id isProperMap_id k
    ⟨φ.1, compactlySupportedClosedForms_le_compactlySupportedForms I k φ.2⟩,
    compactlySupportedForms.mpullback_id]
  simp only [LinearMap.id_apply]

/-- Pullback of compactly supported closed forms reverses composition. -/
theorem mpullback_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) (hfp : IsProperMap f) (hgp : IsProperMap g) (k : ℕ) :
    mpullback (g ∘ f) (hg.comp hf) (hgp.comp hfp) k =
      (mpullback f hf hfp k).comp (mpullback g hg hgp k) := by
  ext φ : 1
  apply Subtype.ext
  rw [coe_mpullback, ← compactlySupportedForms.coe_mpullback (g ∘ f) (hg.comp hf) (hgp.comp hfp) k
    ⟨φ.1, compactlySupportedClosedForms_le_compactlySupportedForms I'' k φ.2⟩,
    compactlySupportedForms.mpullback_comp f g hf hg hfp hgp]
  simp only [LinearMap.comp_apply, compactlySupportedForms.coe_mpullback, coe_mpullback]

end compactlySupportedClosedForms

namespace compactlySupportedDeRhamCohomology

/-- The map from compactly supported closed forms on the target to compactly supported
cohomology on the source obtained by pulling back and taking the class. -/
private def pullbackClass (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    compactlySupportedClosedForms I' M' k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M k :=
  (mk I k).comp (compactlySupportedClosedForms.mpullback f hf hp k)

/-- Compactly supported exact target forms lie in the kernel of pullback followed by the class
map. -/
private theorem ker_mk_le_ker_pullbackClass (f : M → M') (hf : ContMDiff I I' ∞ f)
    (hp : IsProperMap f) (k : ℕ) :
    LinearMap.ker (mk I' (M := M') k) ≤ LinearMap.ker (pullbackClass f hf hp k) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  rw [LinearMap.mem_ker, pullbackClass, LinearMap.comp_apply, mk_eq_zero_iff,
    compactlySupportedClosedForms.coe_mpullback]
  exact SmoothForm.mpullback_mem_exactCompactlySupportedForms f hf hp hφ

/-- The contravariant map on compactly supported de Rham cohomology induced by a smooth proper
map. -/
def map (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    compactlySupportedDeRhamCohomology I' M' k →ₗ[ℝ] compactlySupportedDeRhamCohomology I M k :=
  LinearMap.liftOfSurjective (R := ℝ) (M := compactlySupportedClosedForms I' M' k)
    (M₂ := compactlySupportedDeRhamCohomology I' M' k)
    (M₃ := compactlySupportedDeRhamCohomology I M k) (f := mk I' k) (mk_surjective I' k)
    ⟨pullbackClass f hf hp k, ker_mk_le_ker_pullbackClass f hf hp k⟩

/-- The induced map sends the class of a compactly supported closed form to the class of its
pullback. -/
@[simp]
theorem map_mk (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ)
    (φ : compactlySupportedClosedForms I' M' k) :
    map f hf hp k (mk I' k φ) = mk I k (compactlySupportedClosedForms.mpullback f hf hp k φ) := by
  rw [map, LinearMap.equivOfSurjective_apply]
  rfl

/-- The map on compactly supported cohomology induced by the identity is the identity. -/
@[simp]
theorem map_id (k : ℕ) :
    map (I := I) (I' := I) (M := M) (M' := M) id contMDiff_id isProperMap_id k =
      LinearMap.id := by
  ext c
  obtain ⟨φ, rfl⟩ := mk_surjective I (M := M) k c
  rw [map_mk, compactlySupportedClosedForms.mpullback_id]
  rfl

/-- Pullback on compactly supported cohomology reverses composition of smooth proper maps. -/
theorem map_comp (f : M → M') (g : M' → M'') (hf : ContMDiff I I' ∞ f)
    (hg : ContMDiff I' I'' ∞ g) (hfp : IsProperMap f) (hgp : IsProperMap g) (k : ℕ) :
    map (g ∘ f) (hg.comp hf) (hgp.comp hfp) k = (map f hf hfp k).comp (map g hg hgp k) := by
  ext c
  obtain ⟨φ, rfl⟩ := mk_surjective I'' (M := M'') k c
  rw [LinearMap.comp_apply, map_mk, map_mk, map_mk,
    compactlySupportedClosedForms.mpullback_comp f g hf hg hfp hgp]
  rfl

/-- The comparison with de Rham cohomology commutes with pullback along smooth proper maps. -/
theorem toDeRhamCohomology_map (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f)
    (k : ℕ) (c : compactlySupportedDeRhamCohomology I' M' k) :
    toDeRhamCohomology I M k (map f hf hp k c) =
      deRhamCohomology.map f hf k (toDeRhamCohomology I' M' k c) := by
  obtain ⟨φ, rfl⟩ := mk_surjective I' k c
  rw [map_mk, toDeRhamCohomology_mk, toDeRhamCohomology_mk, deRhamCohomology.map_mk]
  congr 1
  apply Subtype.ext
  rw [compactlySupportedClosedForms.coe_mpullback, closedForms.coe_mpullback]

end compactlySupportedDeRhamCohomology

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

/-- The map induced on cohomology by the cochain map of a smooth proper map is pullback on
compactly supported cohomology. -/
theorem homologyMap_map (f : M → M') (hf : ContMDiff I I' ∞ f) (hp : IsProperMap f) (k : ℕ) :
    HomologicalComplex.homologyMap (map f hf hp) k =
      ModuleCat.ofHom (compactlySupportedDeRhamCohomology.map f hf hp k) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ ?_)
  obtain ⟨φ, rfl⟩ := compactlySupportedDeRhamCohomology.mk_surjective I' k c
  rw [ModuleCat.hom_ofHom, compactlySupportedDeRhamCohomology.map_mk,
    compactlySupportedDeRhamCohomology.mk, compactlySupportedDeRhamCohomology.mk]
  refine HomologicalComplex.homologyMap_moduleCatHomologyClass
    (Z' := compactlySupportedClosedForms I M k) _ _ _ (map f hf hp) _ _
    (compactlySupportedClosedForms.mpullback f hf hp k) (fun φ ↦ ?_) φ
  have h := ConcreteCategory.congr_hom ((Iso.eq_comp_inv _).mpr (map_f f hf hp k))
    ((compactlySupportedDeRhamComplexXIso I' k).inv (Submodule.inclusion
      (compactlySupportedClosedForms_le_compactlySupportedForms I' k) φ))
  simp only [Category.assoc, ModuleCat.hom_comp, ConcreteCategory.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, Iso.inv_hom_id_apply] at h
  refine h.trans (congrArg (compactlySupportedDeRhamComplexXIso I k).inv.hom (Subtype.ext ?_))
  -- Both sides are the smooth pullback of `φ`; the identification of objects is `Iso.refl`.
  rfl

end compactlySupportedDeRhamComplex

end PullbackComplex

end TauCeti
