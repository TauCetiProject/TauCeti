/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The de Rham complex and its cohomology

The exterior derivative on smooth real-valued forms defines the nonnegative de Rham cochain
complex. Its cohomology is Mathlib's categorical homology, with a concrete linear class map from
closed forms, `HomologicalComplex.moduleCatHomologyClass` of their inclusion. This map is
surjective and its kernel consists exactly of exact forms; exact forms in degree zero are zero.

The construction applies to manifolds of class `C²` with corners and does not require finite
dimensionality, separation, or completeness of the model space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
* Mathlib's `CochainComplex.of` provides the complex.
-/

public section

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

variable (M) in
/-- The nonnegative cochain complex of smooth real-valued differential forms. -/
def deRhamComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun k ↦ ModuleCat.of ℝ (SmoothForm I M ℝ k))
    (fun k ↦ ModuleCat.ofHom (mextDerivₗ I (F := ℝ) k))
    (fun k ↦ ModuleCat.hom_ext (mextDerivₗ_comp_mextDerivₗ I (F := ℝ) k))

/-- The canonical identification of the degree-`k` object with smooth `k`-forms.
This isomorphism makes the form carrier available without unfolding the complex. -/
def deRhamComplexXIso (k : ℕ) :
    (deRhamComplex I M).X k ≅ ModuleCat.of ℝ (SmoothForm I M ℝ k) :=
  by
    unfold deRhamComplex
    exact Iso.refl _

/-- Under the canonical identifications of the objects, the differential is the exterior
 derivative. -/
@[reassoc]
theorem deRhamComplex_d (k : ℕ) :
    (deRhamComplex I M).d k (k + 1) ≫ (deRhamComplexXIso I (M := M) (k + 1)).hom =
      (deRhamComplexXIso I (M := M) k).hom ≫ ModuleCat.ofHom (mextDerivₗ I (F := ℝ) k) := by
  dsimp +instances [deRhamComplexXIso, deRhamComplex]
  simp

/-- The differential of the de Rham complex, evaluated on an element. -/
theorem deRhamComplex_d_apply (k : ℕ) (x : (deRhamComplex I M).X k) :
    (deRhamComplex I M).d k (k + 1) x =
      (deRhamComplexXIso I (k + 1)).inv
        (mextDerivₗ I (F := ℝ) k ((deRhamComplexXIso I k).hom x)) := by
  rw [(Iso.eq_comp_inv _).mpr (deRhamComplex_d I (M := M) k), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ConcreteCategory.hom_ofHom]

variable (M) in
/-- The submodule of smooth forms whose exterior derivative vanishes. -/
def closedForms (k : ℕ) : Submodule ℝ (SmoothForm I M ℝ k) :=
  LinearMap.ker (mextDerivₗ I (F := ℝ) k)

/-- A smooth form is closed precisely when its exterior derivative vanishes. -/
@[simp]
theorem mem_closedForms {k : ℕ} (φ : SmoothForm I M ℝ k) :
    φ ∈ closedForms I M k ↔ mextDeriv φ.1 = 0 := by
  simp only [closedForms, LinearMap.mem_ker, ← Subtype.val_inj, mextDerivₗ_apply,
    Submodule.coe_zero]

/-- A smooth form is closed precisely when its exterior derivative, as a smooth form, vanishes. -/
theorem mem_closedForms_iff_mextDerivₗ_eq_zero {k : ℕ} (φ : SmoothForm I M ℝ k) :
    φ ∈ closedForms I M k ↔ mextDerivₗ I (F := ℝ) k φ = 0 :=
  LinearMap.mem_ker

variable (M) in
/-- Exact forms are exterior derivatives of smooth forms in positive degree, and zero in
 degree zero. -/
def exactForms : (k : ℕ) → Submodule ℝ (SmoothForm I M ℝ k)
  | 0 => ⊥
  | k + 1 => LinearMap.range (mextDerivₗ I (F := ℝ) k)

/-- There are no nonzero exact forms in degree zero. -/
@[simp]
theorem exactForms_zero : exactForms I M 0 = ⊥ := (rfl)

/-- In positive degree, exact forms are the range of the exterior derivative. -/
@[simp]
theorem exactForms_succ (k : ℕ) :
    exactForms I M (k + 1) = LinearMap.range (mextDerivₗ I (F := ℝ) k) := (rfl)

/-- An exact smooth form is closed. -/
theorem exactForms_le_closedForms (k : ℕ) : exactForms I M k ≤ closedForms I M k := by
  cases k with
  | zero => simp
  | succ k =>
    exact LinearMap.range_le_ker_iff.mpr (mextDerivₗ_comp_mextDerivₗ I (F := ℝ) k)

/-- On a manifold of finite dimension at most `k`, every smooth `k`-form is closed. -/
theorem mem_closedForms_of_finrank_le [FiniteDimensional ℝ E] {k : ℕ}
    (h : Module.finrank ℝ E ≤ k) (φ : SmoothForm I M ℝ k) : φ ∈ closedForms I M k :=
  (mem_closedForms I φ).mpr (mextDeriv_eq_zero_of_finrank_le h _)

variable (M) in
/-- De Rham cohomology is the categorical homology of the de Rham complex. -/
abbrev deRhamCohomology (k : ℕ) : Type _ :=
  (deRhamComplex I M).homology k

/-- A closed form, viewed in the de Rham complex, is killed by the differential. -/
theorem deRhamComplex_d_eq_zero_of_mem_closedForms (k : ℕ) {φ : SmoothForm I M ℝ k}
    (hφ : φ ∈ closedForms I M k) :
    (deRhamComplex I M).d k (k + 1) ((deRhamComplexXIso I k).inv φ) = 0 := by
  rw [deRhamComplex_d_apply]
  simp [(mem_closedForms_iff_mextDerivₗ_eq_zero I φ).mp hφ]

namespace deRhamCohomology

/-- The cohomology class of a closed smooth form, the homology class of the corresponding cycle
of the de Rham complex. -/
def mk (k : ℕ) : closedForms I M k →ₗ[ℝ] deRhamCohomology I M k :=
  (deRhamComplex I M).moduleCatHomologyClass (Z := closedForms I M k) (CochainComplex.next ℕ k)
    ((deRhamComplexXIso I k).inv.hom ∘ₗ (closedForms I M k).subtype) fun φ ↦ by
      rw [LinearMap.comp_apply]
      exact deRhamComplex_d_eq_zero_of_mem_closedForms I k φ.2

/-- The class map is the homology class map of the inclusion of closed forms into the de Rham
complex. -/
theorem mk_eq_moduleCatHomologyClass (k : ℕ) :
    mk I (M := M) k =
      (deRhamComplex I M).moduleCatHomologyClass (Z := closedForms I M k)
        (CochainComplex.next ℕ k) ((deRhamComplexXIso I k).inv.hom ∘ₗ (closedForms I M k).subtype)
        fun φ ↦ by
          rw [LinearMap.comp_apply]
          exact deRhamComplex_d_eq_zero_of_mem_closedForms I k φ.2 :=
  (rfl)

/-- Every de Rham cohomology class is represented by a closed smooth form. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (mk I (M := M) k) := by
  rw [mk]
  refine (deRhamComplex I M).moduleCatHomologyClass_surjective _ _ _ fun x hx ↦ ?_
  rw [deRhamComplex_d_apply] at hx
  refine ⟨⟨(deRhamComplexXIso I k).hom x, (mem_closedForms_iff_mextDerivₗ_eq_zero I _).mpr
    ((LinearEquiv.map_eq_zero_iff (deRhamComplexXIso I (M := M) (k + 1)).toLinearEquiv.symm).mp
      hx)⟩, ?_⟩
  simp

/-- A closed form represents zero precisely when it is exact. -/
@[simp]
theorem mk_eq_zero_iff (k : ℕ) (φ : closedForms I M k) :
    mk I k φ = 0 ↔ φ.1 ∈ exactForms I M k := by
  cases k with
  | zero =>
    rw [mk, (deRhamComplex I M).moduleCatHomologyClass_eq_zero_iff _ _ _
        CochainComplex.prev_nat_zero, exactForms_zero, Submodule.mem_bot,
      (deRhamComplex I M).shape 0 0 (by simp)]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const, LinearMap.comp_apply,
      Submodule.subtype_apply]
    exact ⟨fun h ↦ by simpa using congrArg (deRhamComplexXIso I (M := M) 0).hom.hom h.symm,
      fun h ↦ by simp [h]⟩
  | succ k =>
    rw [mk, (deRhamComplex I M).moduleCatHomologyClass_eq_zero_iff _ _ _
        (CochainComplex.prev_nat_succ k), exactForms_succ, LinearMap.mem_range]
    refine ⟨fun ⟨y, hy⟩ ↦ ⟨(deRhamComplexXIso I k).hom y, ?_⟩,
      fun ⟨ψ, hψ⟩ ↦ ⟨(deRhamComplexXIso I k).inv ψ, ?_⟩⟩
    · rw [deRhamComplex_d_apply] at hy
      simpa using congrArg (deRhamComplexXIso I (M := M) (k + 1)).hom.hom hy
    · rw [deRhamComplex_d_apply]
      simp [hψ]

/-- The kernel of the cycle-class map is exactly the submodule of exact forms inside closed
 forms. -/
theorem ker_mk (k : ℕ) :
    LinearMap.ker (mk I (M := M) k) =
      (exactForms I M k).comap (closedForms I M k).subtype := by
  ext φ
  exact mk_eq_zero_iff I k φ

end deRhamCohomology

end TauCeti
