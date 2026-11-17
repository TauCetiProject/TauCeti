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
  cohomology; the concrete class-map API is `HomologicalComplex.moduleCatCohomologyClassOfIso`.
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
      ModuleCat.of ℂ ((ofComplexManifold E M).typeForms (F := F) p q) :=
  Iso.refl _

/-- Under the canonical identifications of terms, the differential is `∂bar`. -/
@[reassoc]
theorem dolbeaultComplex_d (p q : ℕ) :
    (dolbeaultComplex E M F p).d q (q + 1) ≫ (dolbeaultComplexXIso p (q + 1)).hom =
      (dolbeaultComplexXIso p q).hom ≫
        ModuleCat.ofHom ((ofComplexManifold E M).delBarType (F := F) p q) := by
  simp [dolbeaultComplex, dolbeaultComplexXIso, CochainComplex.of_d]

/-- The differential of the Dolbeault complex, evaluated on an element. -/
theorem dolbeaultComplex_d_apply (p q : ℕ) (φ : (dolbeaultComplex E M F p).X q) :
    (dolbeaultComplex E M F p).d q (q + 1) φ =
      (dolbeaultComplexXIso p (q + 1)).inv
        ((ofComplexManifold E M).delBarType p q ((dolbeaultComplexXIso p q).hom φ)) := by
  rw [(Iso.eq_comp_inv _).mpr (dolbeaultComplex_d p q), ModuleCat.comp_apply,
    ModuleCat.comp_apply, ModuleCat.ofHom_apply]

-- Fix the scalar ring before searching for the group structure on nested submodules of forms;
-- otherwise synthesis for closed forms and their quotient exceeds the default instance budget,
-- here and in importing modules.
/-- The native additive group of type forms, with complex coefficients fixed. -/
instance typeFormsAddCommGroup (p q : ℕ) :
    AddCommGroup ((ofComplexManifold E M).typeForms (F := F) p q) :=
  Submodule.addCommGroup _

namespace Dolbeault

variable (E M F)

/-- The complex submodule of smooth type-`(p,q)` forms annihilated by `∂bar`. -/
def closedForms (p q : ℕ) :
    Submodule ℂ ((ofComplexManifold E M).typeForms (F := F) p q) :=
  LinearMap.ker ((ofComplexManifold E M).delBarType p q)

/-- The `∂bar`-exact forms: zero in degree zero, and derivatives of type-`(p,q)` forms in
antiholomorphic degree `q+1`. -/
def exactForms (p : ℕ) :
    (q : ℕ) → Submodule ℂ ((ofComplexManifold E M).typeForms (F := F) p q)
  | 0 => ⊥
  | q + 1 => LinearMap.range ((ofComplexManifold E M).delBarType p q)

variable {E M F}

/-- A type form is closed exactly when its underlying smooth form has vanishing `∂bar`. -/
@[simp]
theorem mem_closedForms (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms (F := F) p q) :
    φ ∈ closedForms E M F p q ↔ (ofComplexManifold E M).delBar φ.1 = 0 := by
  simp only [closedForms, LinearMap.mem_ker, Subtype.ext_iff, coe_delBarType,
    Submodule.coe_zero]

/-- No nonzero form is exact in antiholomorphic degree zero. -/
@[simp]
theorem exactForms_zero (p : ℕ) : exactForms E M F p 0 = ⊥ := (rfl)

/-- Exact forms in positive antiholomorphic degree are derivatives of type forms. -/
@[simp]
theorem mem_exactForms_succ (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms (F := F) p (q + 1)) :
    φ ∈ exactForms E M F p (q + 1) ↔
      ∃ ψ : (ofComplexManifold E M).typeForms (F := F) p q,
        (ofComplexManifold E M).delBar ψ.1 = φ.1 := by
  simp only [exactForms, LinearMap.mem_range, Subtype.ext_iff, coe_delBarType]

/-- A type form is exact if, after identifying its antiholomorphic degree with a successor,
it is the Dolbeault differential of a type form in the preceding degree. -/
theorem mem_exactForms_of_eq_delBar {p q n : ℕ} (hq : q = n + 1)
    (φ : (ofComplexManifold E M).typeForms (F := F) p q)
    (α : (ofComplexManifold E M).typeForms (F := F) p n)
    (hφ : LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm 𝓘(ℝ, E) M F k)
      (congrArg (p + ·) hq) φ.1 = (ofComplexManifold E M).delBar α.1) :
    φ ∈ exactForms E M F p q := by
  subst q
  exact (mem_exactForms_succ p n φ).mpr ⟨α, hφ.symm⟩

/-- Every `∂bar`-exact form is `∂bar`-closed. -/
theorem exactForms_le_closedForms (p q : ℕ) :
    exactForms E M F p q ≤ closedForms E M F p q := by
  cases q with
  | zero => simp
  | succ q =>
    rintro _ ⟨ψ, rfl⟩
    exact (mem_closedForms p (q + 1) _).mpr (by simp)

end Dolbeault

variable (E M F)

/-- Dolbeault cohomology is the native categorical cohomology of the Dolbeault complex. -/
abbrev dolbeaultCohomology (p q : ℕ) : Type _ :=
  (dolbeaultComplex E M F p).homology q

namespace dolbeaultCohomology

open Dolbeault

variable {E M F}

private theorem mem_closedForms_iff_complex (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms (F := F) p q) :
    φ ∈ closedForms E M F p q ↔
      (dolbeaultComplex E M F p).d q (q + 1) ((dolbeaultComplexXIso p q).inv φ) = 0 := by
  rw [closedForms, LinearMap.mem_ker, (dolbeaultComplex E M F p).moduleCat_d_inv_eq_zero_iff
    ((ofComplexManifold E M).delBarType p) (dolbeaultComplex_d p)]

private theorem mem_exactForms_iff_complex (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms (F := F) p q) :
    φ ∈ exactForms E M F p q ↔
      ∃ ψ : (dolbeaultComplex E M F p).X ((ComplexShape.up ℕ).prev q),
        (dolbeaultComplex E M F p).d ((ComplexShape.up ℕ).prev q) q ψ =
          (dolbeaultComplexXIso p q).inv φ := by
  exact (dolbeaultComplex E M F p).moduleCat_mem_iff_exists_d_eq_inv (exactForms E M F p)
    ((ofComplexManifold E M).delBarType p) (dolbeaultComplex_d p)
    (exactForms_zero p) (fun _ ↦ rfl) q φ

/-- The complex-linear cohomology class map on `∂bar`-closed type forms. -/
def mk (p q : ℕ) : closedForms E M F p q →ₗ[ℂ] dolbeaultCohomology E M F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q) (closedForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedForms_iff_complex p) q

/-- The class of a closed type form is the native homology class of any corresponding cycle. -/
theorem mk_eq_homologyπ (p q : ℕ) (φ : closedForms E M F p q)
    (z : (dolbeaultComplex E M F p).cycles q)
    (hz : (dolbeaultComplexXIso p q).hom
      ((dolbeaultComplex E M F p).iCycles q z) = φ.1) :
    mk p q φ = (dolbeaultComplex E M F p).homologyπ q z :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q) (closedForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedForms_iff_complex p) φ z hz

/-- Every Dolbeault cohomology class has a `∂bar`-closed representative. -/
theorem mk_surjective (p q : ℕ) : Function.Surjective (mk (E := E) (M := M) (F := F) p q) := by
  exact (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_surjective
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q) (closedForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedForms_iff_complex p) q

/-- A closed type form represents zero exactly when it is `∂bar`-exact. -/
@[simp]
theorem mk_eq_zero_iff (p q : ℕ) (φ : closedForms E M F p q) :
    mk p q φ = 0 ↔ φ.1 ∈ exactForms E M F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q)
    (closedForms E M F p) (exactForms E M F p) (dolbeaultComplexXIso p)
    (mem_closedForms_iff_complex p) (mem_exactForms_iff_complex p) q φ

/-- Two closed type forms represent the same class exactly when their difference is exact. -/
theorem mk_eq_iff (p q : ℕ) (φ ψ : closedForms E M F p q) :
    mk p q φ = mk p q ψ ↔ (φ - ψ).1 ∈ exactForms E M F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_iff
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q)
    (closedForms E M F p) (exactForms E M F p) (dolbeaultComplexXIso p)
    (mem_closedForms_iff_complex p) (mem_exactForms_iff_complex p) q φ ψ

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
