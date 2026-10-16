/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The de Rham complex and its cohomology

The exterior derivative on smooth real-valued forms defines the nonnegative de Rham cochain
complex. Its cohomology is Mathlib's categorical homology, with a concrete linear class map from
closed forms. This map is surjective and its kernel consists exactly of exact forms; exact
forms in degree zero are zero.

The construction applies to manifolds of class `C²` with corners and does not require finite
dimensionality, separation, or completeness of the model space.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 17.
* Mathlib's `CochainComplex.of` and `ShortComplex.moduleCatHomologyIso` provide the complex
  and the concrete presentation of its homology.
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

variable (M) in
/-- De Rham cohomology is the categorical homology of the de Rham complex. -/
abbrev deRhamCohomology (k : ℕ) : Type _ :=
  (deRhamComplex I M).homology k

private def closedFormsEquivKernel (k : ℕ) :
    closedForms I M k ≃ₗ[ℝ]
      ((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData.K := by
  dsimp +instances [ShortComplex.moduleCatLeftHomologyData, deRhamComplex, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor']
  exact LinearEquiv.ofEq _ _ (by simp [closedForms])

private theorem closedFormsEquivKernel_i (k : ℕ) (φ : closedForms I M k) :
    ((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData.i
        (closedFormsEquivKernel I k φ) =
      (deRhamComplexXIso I (M := M) k).inv φ.1 := by
  dsimp +instances [closedFormsEquivKernel, deRhamComplexXIso, deRhamComplex,
    ShortComplex.moduleCatLeftHomologyData, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor']
  rfl

private theorem mem_range_incoming_iff (k : ℕ) (φ : SmoothForm I M ℝ k) :
    (deRhamComplexXIso I (M := M) k).inv φ ∈
        LinearMap.range ((deRhamComplex I M).sc' (k - 1) k (k + 1)).f.hom ↔
      φ ∈ exactForms I M k := by
  cases k with
  | zero =>
    simp only [deRhamComplexXIso, deRhamComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', Nat.zero_sub, CochainComplex.of.d,
      Nat.reduceAdd, Nat.one_ne_zero, ↓reduceDIte, exactForms, Submodule.mem_bot]
    constructor
    · rintro ⟨ψ, hψ⟩
      exact hψ.symm
    · intro hφ
      exact ⟨0, hφ.symm⟩
  | succ k =>
    simp [deRhamComplexXIso, deRhamComplex, HomologicalComplex.sc',
      HomologicalComplex.shortComplexFunctor', exactForms, -LinearMap.mem_range]
    rfl

private theorem mem_range_toCycles_iff (k : ℕ) (φ : closedForms I M k) :
    closedFormsEquivKernel I k φ ∈
        LinearMap.range
          ((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData.f'.hom ↔
      φ.1 ∈ exactForms I M k := by
  let S := (deRhamComplex I M).sc' (k - 1) k (k + 1)
  have hmem : closedFormsEquivKernel I k φ ∈ LinearMap.range S.moduleCatLeftHomologyData.f'.hom ↔
      S.moduleCatLeftHomologyData.i (closedFormsEquivKernel I k φ) ∈ LinearMap.range S.f.hom := by
    -- Evaluate the range equation on the kernel carrier with its own module instances.
    exact Iff.of_eq (congrArg (fun p : Submodule ℝ (LinearMap.ker S.g.hom) ↦
      (show LinearMap.ker S.g.hom from closedFormsEquivKernel I k φ) ∈ p)
        (LinearMap.range_codRestrict _ S.f.hom S.moduleCat_zero_apply))
  rw [closedFormsEquivKernel_i] at hmem
  exact hmem.trans (mem_range_incoming_iff I k φ.1)

private def concreteHomologyIso (k : ℕ) :
    ((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData.H ≅
      (deRhamComplex I M).homology k :=
  ((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatHomologyIso.symm ≪≫
    ((deRhamComplex I M).homologyIsoSc' (k - 1) k (k + 1)
      (by
        cases k with
        | zero => exact (ComplexShape.up ℕ).prev_eq_self' 0 (by simp)
        | succ k => exact (ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk k (k + 1) rfl))
      ((ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk k (k + 1) rfl))).symm

namespace deRhamCohomology

/-- The cohomology class of a closed smooth form, using Mathlib's canonical comparison
 between categorical module homology and the quotient of cycles by boundaries. -/
def mk (k : ℕ) : closedForms I M k →ₗ[ℝ] deRhamCohomology I M k :=
  (concreteHomologyIso I k).hom.hom.comp
    ((((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData.π).hom.comp
      (closedFormsEquivKernel I k).toLinearMap)

/-- Every de Rham cohomology class is represented by a closed smooth form. -/
theorem mk_surjective (k : ℕ) : Function.Surjective (mk I (M := M) k) := by
  exact ((concreteHomologyIso I k).toLinearEquiv.surjective.comp
    (Submodule.mkQ_surjective _)).comp (closedFormsEquivKernel I k).surjective

/-- A closed form represents zero precisely when it is exact. -/
@[simp]
theorem mk_eq_zero_iff (k : ℕ) (φ : closedForms I M k) :
    mk I k φ = 0 ↔ φ.1 ∈ exactForms I M k := by
  simp only [mk, LinearMap.comp_apply]
  rw [← map_zero (concreteHomologyIso I k).hom.hom,
    ((ModuleCat.mono_iff_injective (concreteHomologyIso I k).hom).mp inferInstance).eq_iff]
  let h := ((deRhamComplex I M).sc' (k - 1) k (k + 1)).moduleCatLeftHomologyData
  let T := ShortComplex.mk h.f' h.π h.f'_π
  have ht : T.Exact := T.exact_of_g_is_cokernel h.hπ'
  have hz : h.π.hom (closedFormsEquivKernel I k φ) = 0 ↔
      closedFormsEquivKernel I k φ ∈ LinearMap.range h.f'.hom := by
    rw [ht.moduleCat_range_eq_ker]
    rfl
  exact hz.trans (mem_range_toCycles_iff I k φ)

/-- The kernel of the cycle-class map is exactly the submodule of exact forms inside closed
 forms. -/
theorem ker_mk (k : ℕ) :
    LinearMap.ker (mk I (M := M) k) =
      (exactForms I M k).comap (closedForms I M k).subtype := by
  ext φ
  exact mk_eq_zero_iff I k φ

end deRhamCohomology

end TauCeti
