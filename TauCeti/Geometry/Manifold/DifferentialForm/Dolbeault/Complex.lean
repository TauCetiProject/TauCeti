/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Algebra.Homology.ModuleCat.Basic

/-!
# The Dolbeault complex and its cohomology

For each fixed holomorphic degree `p`, the smooth forms of types `(p,q)` with differential
`∂bar` form a nonnegative cochain complex in `ModuleCat ℂ`. Its cohomology is Mathlib's
categorical homology, with a complex-linear class map from the `∂bar`-closed forms. Every
class has a representative, and a representative has zero class exactly when it is
`∂bar`-exact. In degree zero, exact forms are zero. The quotient of closed forms by exact
forms is identified complex-linearly with this same categorical cohomology.

Type forms are submodules of the generic smooth form carrier, not a new form carrier.
Coefficients may lie in any complex normed space. Neither finite dimensionality nor
compactness of the manifold is needed.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 2.6.
* Mathlib's `CochainComplex.of` and `HomologicalComplex.homology` supply the complex and
  cohomology; the concrete class-map API is `HomologicalComplex.moduleCatHomologyClass`.
-/

public section

noncomputable section

open CategoryTheory
open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

open SmoothAlmostComplexStructure

variable (E M F)

/-- The Dolbeault complex of forms of holomorphic degree `p`, with coefficients in `F`. -/
def dolbeaultComplex (p : ℕ) : CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of
    (fun q ↦ ModuleCat.of ℂ ((ofComplexManifold E M).typeForms (F := F) p q))
    (fun q ↦ ModuleCat.ofHom ((ofComplexManifold E M).delBarType p q))
    (fun q ↦ ModuleCat.hom_ext <| LinearMap.ext fun φ ↦ Subtype.ext <| by simp)

variable {E M F}

/-- The degree-`q` term of the Dolbeault complex is the complex module of type-`(p,q)` forms. -/
def dolbeaultComplexXIso (p q : ℕ) :
    (dolbeaultComplex E M F p).X q ≅
      ModuleCat.of ℂ ((ofComplexManifold E M).typeForms (F := F) p q) := by
  unfold dolbeaultComplex
  exact Iso.refl _

/-- Under the canonical identifications of terms, the differential is `∂bar`. -/
@[reassoc]
theorem dolbeaultComplex_d (p q : ℕ) :
    (dolbeaultComplex E M F p).d q (q + 1) ≫ (dolbeaultComplexXIso p (q + 1)).hom =
      (dolbeaultComplexXIso p q).hom ≫
        ModuleCat.ofHom ((ofComplexManifold E M).delBarType (F := F) p q) := by
  dsimp +instances [dolbeaultComplexXIso, dolbeaultComplex]
  simp

/-- The differential of the Dolbeault complex, evaluated on an element. -/
theorem dolbeaultComplex_d_apply (p q : ℕ) (φ : (dolbeaultComplex E M F p).X q) :
    (dolbeaultComplex E M F p).d q (q + 1) φ =
      (dolbeaultComplexXIso p (q + 1)).inv
        ((ofComplexManifold E M).delBarType p q ((dolbeaultComplexXIso p q).hom φ)) := by
  rw [(Iso.eq_comp_inv _).mpr (dolbeaultComplex_d p q), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ModuleCat.ofHom_apply]

namespace Dolbeault

variable (E M F)

/-- The complex submodule of smooth type-`(p,q)` forms annihilated by `∂bar`. -/
def closedForms (p q : ℕ) : Submodule ℂ (SmoothForm 𝓘(ℝ, E) M F (p + q)) :=
  (ofComplexManifold E M).typeForms p q ⊓ LinearMap.ker (ofComplexManifold E M).delBar

/-- The `∂bar`-exact forms: zero in degree zero, and derivatives of type-`(p,q)` forms in
antiholomorphic degree `q+1`. -/
def exactForms (p : ℕ) : (q : ℕ) → Submodule ℂ (SmoothForm 𝓘(ℝ, E) M F (p + q))
  | 0 => ⊥
  | q + 1 => LinearMap.range
      (((ofComplexManifold E M).typeForms p (q + 1)).subtype.comp
        ((ofComplexManifold E M).delBarType p q))

variable {E M F}

/-- Membership in the closed type forms means having the specified type and vanishing `∂bar`. -/
@[simp]
theorem mem_closedForms (p q : ℕ) (φ : SmoothForm 𝓘(ℝ, E) M F (p + q)) :
    φ ∈ closedForms E M F p q ↔
      φ.IsOfType (ofComplexManifold E M) p q ∧ (ofComplexManifold E M).delBar φ = 0 :=
  and_congr (mem_typeForms _ p q φ) LinearMap.mem_ker

/-- Closed type forms are type forms. -/
theorem closedForms_le_typeForms (p q : ℕ) :
    closedForms E M F p q ≤ (ofComplexManifold E M).typeForms p q := inf_le_left

/-- No nonzero form is exact in antiholomorphic degree zero. -/
@[simp]
theorem exactForms_zero (p : ℕ) : exactForms E M F p 0 = ⊥ := (rfl)

/-- Exact forms in positive antiholomorphic degree are derivatives of type forms. -/
@[simp]
theorem mem_exactForms_succ (p q : ℕ) (φ : SmoothForm 𝓘(ℝ, E) M F (p + (q + 1))) :
    φ ∈ exactForms E M F p (q + 1) ↔
      ∃ ψ : (ofComplexManifold E M).typeForms (F := F) p q,
        (ofComplexManifold E M).delBar ψ.1 = φ := by
  simp only [exactForms, LinearMap.mem_range, LinearMap.comp_apply, Submodule.subtype_apply,
    coe_delBarType]

/-- Every `∂bar`-exact form is `∂bar`-closed. -/
theorem exactForms_le_closedForms (p q : ℕ) :
    exactForms E M F p q ≤ closedForms E M F p q := by
  cases q with
  | zero => simp
  | succ q =>
    intro φ hφ
    obtain ⟨ψ, rfl⟩ := (mem_exactForms_succ p q φ).mp hφ
    exact (mem_closedForms p (q + 1) _).mpr
      ⟨((mem_typeForms _ p q _).mp ψ.2).delBar, by simp⟩

end Dolbeault

variable (E M F)

/-- Dolbeault cohomology is the native categorical cohomology of the Dolbeault complex. -/
abbrev dolbeaultCohomology (p q : ℕ) : Type _ :=
  (dolbeaultComplex E M F p).homology q

namespace dolbeaultCohomology

open Dolbeault

variable {E M F}

private def cycleInclusion (p q : ℕ) :
    closedForms E M F p q →ₗ[ℂ] (dolbeaultComplex E M F p).X q :=
  (dolbeaultComplexXIso p q).inv.hom.comp (Submodule.inclusion (closedForms_le_typeForms p q))

private theorem cycleInclusion_d (p q : ℕ) (φ : closedForms E M F p q) :
    (dolbeaultComplex E M F p).d q (q + 1) (cycleInclusion p q φ) = 0 := by
  rw [dolbeaultComplex_d_apply]
  apply (dolbeaultComplexXIso p (q + 1)).toLinearEquiv.symm.map_eq_zero_iff.mpr
  apply Subtype.ext
  simpa [cycleInclusion] using ((mem_closedForms p q φ.1).mp φ.2).2

/-- The complex-linear cohomology class map on `∂bar`-closed type forms. -/
def mk (p q : ℕ) : closedForms E M F p q →ₗ[ℂ] dolbeaultCohomology E M F p q :=
  (dolbeaultComplex E M F p).moduleCatHomologyClass (CochainComplex.next ℕ q)
    (Z := closedForms E M F p q) (cycleInclusion p q) (cycleInclusion_d p q)

/-- Every Dolbeault cohomology class has a `∂bar`-closed representative. -/
theorem mk_surjective (p q : ℕ) : Function.Surjective (mk (E := E) (M := M) (F := F) p q) := by
  unfold mk
  apply (dolbeaultComplex E M F p).moduleCatHomologyClass_surjective
  intro φ hφ
  let ψ := (dolbeaultComplexXIso p q).hom φ
  have hψ : ψ.1 ∈ closedForms E M F p q := by
    refine (mem_closedForms p q _).mpr ⟨(mem_typeForms _ p q _).mp ψ.2, ?_⟩
    rw [dolbeaultComplex_d_apply] at hφ
    have h := (dolbeaultComplexXIso p (q + 1)).toLinearEquiv.symm.map_eq_zero_iff.mp hφ
    simpa only [coe_delBarType, Submodule.coe_zero] using congrArg Subtype.val h
  exact ⟨⟨ψ.1, hψ⟩, by simp [cycleInclusion, ψ, Submodule.inclusion_apply]⟩

/-- A closed type form represents zero exactly when it is `∂bar`-exact. -/
@[simp]
theorem mk_eq_zero_iff (p q : ℕ) (φ : closedForms E M F p q) :
    mk p q φ = 0 ↔ φ.1 ∈ exactForms E M F p q := by
  cases q with
  | zero =>
    rw [mk, (dolbeaultComplex E M F p).moduleCatHomologyClass_eq_zero_iff
      (CochainComplex.next ℕ 0) (Z := closedForms E M F p 0)
      (cycleInclusion p 0) (cycleInclusion_d p 0)
      CochainComplex.prev_nat_zero, exactForms_zero, Submodule.mem_bot,
      HomologicalComplex.shape _ 0 0 (by simp)]
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply, exists_const]
    constructor
    · intro h
      have h' := congrArg (fun x ↦ ((dolbeaultComplexXIso p 0).hom x).1) h.symm
      simpa [cycleInclusion] using h'
    · intro h
      have hφ : φ = 0 := Subtype.ext h
      simp [hφ]
  | succ q =>
    rw [mk, (dolbeaultComplex E M F p).moduleCatHomologyClass_eq_zero_iff
      (CochainComplex.next ℕ (q + 1)) (Z := closedForms E M F p (q + 1))
      (cycleInclusion p (q + 1)) (cycleInclusion_d p (q + 1))
      (CochainComplex.prev_nat_succ q), mem_exactForms_succ]
    constructor
    · rintro ⟨ψ, hψ⟩
      refine ⟨(dolbeaultComplexXIso p q).hom ψ, ?_⟩
      rw [dolbeaultComplex_d_apply] at hψ
      have h := congrArg (fun x ↦ ((dolbeaultComplexXIso p (q + 1)).hom x).1) hψ
      simpa [cycleInclusion] using h
    · rintro ⟨ψ, hψ⟩
      refine ⟨(dolbeaultComplexXIso p q).inv ψ, ?_⟩
      rw [dolbeaultComplex_d_apply, Iso.inv_hom_id_apply]
      have h : (ofComplexManifold E M).delBarType p q ψ =
          Submodule.inclusion (closedForms_le_typeForms p (q + 1)) φ := by
        apply Subtype.ext
        simpa only [coe_delBarType, Submodule.coe_inclusion] using hψ
      exact congrArg (dolbeaultComplexXIso p (q + 1)).inv h

/-- Two closed type forms represent the same class exactly when their difference is exact. -/
theorem mk_eq_iff (p q : ℕ) (φ ψ : closedForms E M F p q) :
    mk p q φ = mk p q ψ ↔ (φ - ψ).1 ∈ exactForms E M F p q := by
  rw [← sub_eq_zero, ← map_sub, mk_eq_zero_iff]

/-- The kernel of the class map is the submodule of exact forms inside closed forms. -/
theorem ker_mk (p q : ℕ) :
    LinearMap.ker (mk (E := E) (M := M) (F := F) p q) =
      (exactForms E M F p q).comap (closedForms E M F p q).subtype := by
  ext φ
  exact mk_eq_zero_iff p q φ

-- Inferring the coefficient ring through the nested smooth-form submodule exceeds the default
-- typeclass synthesis budget, so specify it before elaborating the quotient comparison.
/-- The native submodule quotient instance, with complex coefficients fixed. -/
local instance closedFormsHasQuotient (p q : ℕ) : HasQuotient ↥(closedForms E M F p q)
    (Submodule ℂ ↥(closedForms E M F p q)) :=
  Submodule.hasQuotient (R := ℂ) (M := ↥(closedForms E M F p q))

/-- The quotient of closed forms by exact forms is complex-linearly equivalent to native
Dolbeault cohomology. -/
def quotientEquiv (p q : ℕ) :
    (closedForms E M F p q ⧸
      (exactForms E M F p q).comap (closedForms E M F p q).subtype) ≃ₗ[ℂ]
        dolbeaultCohomology E M F p q :=
  (Submodule.quotEquivOfEq _ _ (ker_mk (E := E) (M := M) (F := F) p q).symm).trans
    ((mk p q).quotKerEquivOfSurjective (mk_surjective p q))

/-- The quotient comparison sends the quotient of a closed form to its cohomology class. -/
@[simp]
theorem quotientEquiv_mk (p q : ℕ) (φ : closedForms E M F p q) :
    quotientEquiv (E := E) (M := M) (F := F) p q (Submodule.Quotient.mk φ) = mk p q φ := by
  simp [quotientEquiv]

end dolbeaultCohomology

end TauCeti
