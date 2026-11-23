/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.ComplexManifold
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend

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

A holomorphic map, a smooth map of the underlying real manifolds whose differential is
complex-linear, induces by pullback of type forms a cochain map of Dolbeault complexes
(`TauCeti.dolbeaultComplex.map`), contravariantly functorial in the map. This follows the cochain
map `TauCeti.deRhamComplex.map` of `TauCeti.Geometry.Manifold.DeRham.Map`.

The Dolbeault complex is indexed by `ℕ`. Extended by zero to negative degrees along
`ComplexShape.embeddingUpNat`, its term of degree `q` is identified with the type forms of type
`(p,q)` (`TauCeti.dolbeaultComplex.extendXEquiv`); in these coordinates the differential is `∂bar`
and the extended cochain map of a holomorphic map is pullback.

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
    φ ∈ closedForms E M F p q ↔ (ofComplexManifold E M).delBar φ.val = 0 := by
  simp only [closedForms, LinearMap.mem_ker, Subtype.ext_iff, coe_delBarType,
    Submodule.coe_zero]

/-- A type form is closed exactly when its image under the Dolbeault differential on type forms
vanishes. -/
theorem mem_closedForms_iff_delBarType_eq_zero (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms (F := F) p q) :
    φ ∈ closedForms E M F p q ↔ (ofComplexManifold E M).delBarType p q φ = 0 :=
  LinearMap.mem_ker

/-- No nonzero form is exact in antiholomorphic degree zero. -/
@[simp]
theorem exactForms_zero (p : ℕ) : exactForms E M F p 0 = ⊥ := (rfl)

/-- Exact forms in positive antiholomorphic degree are derivatives of type forms. -/
@[simp]
theorem mem_exactForms_succ (p q : ℕ)
    (φ : (ofComplexManifold E M).typeForms (F := F) p (q + 1)) :
    φ ∈ exactForms E M F p (q + 1) ↔
      ∃ ψ : (ofComplexManifold E M).typeForms (F := F) p q,
        (ofComplexManifold E M).delBar ψ.val = φ.val := by
  simp only [exactForms, LinearMap.mem_range, Subtype.ext_iff, coe_delBarType]

/-- A type form is exact if, after identifying its antiholomorphic degree with a successor,
it is the Dolbeault differential of a type form in the preceding degree. -/
theorem mem_exactForms_of_eq_delBar {p q n : ℕ} (hq : q = n + 1)
    (φ : (ofComplexManifold E M).typeForms (F := F) p q)
    (α : (ofComplexManifold E M).typeForms (F := F) p n)
    (hφ : LinearEquiv.cast (R := ℝ) (M := fun k ↦ SmoothForm 𝓘(ℝ, E) M F k)
      (congrArg (p + ·) hq) φ.val = (ofComplexManifold E M).delBar α.val) :
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
      ((dolbeaultComplex E M F p).iCycles q z) = φ.val) :
    mk p q φ = (dolbeaultComplex E M F p).homologyπ q z :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_homologyπ
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q) (closedForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedForms_iff_complex p) φ z hz

/-- The class map is the homology class map of the closed forms, embedded into the Dolbeault
complex through the canonical identification of its terms. -/
theorem mk_eq_moduleCatHomologyClass (p q : ℕ) :
    mk (E := E) (M := M) (F := F) p q =
      (dolbeaultComplex E M F p).moduleCatHomologyClass (Z := closedForms E M F p q)
        (CochainComplex.next ℕ q)
        ((dolbeaultComplexXIso p q).inv.hom ∘ₗ (closedForms E M F p q).subtype) fun φ ↦ by
          rw [LinearMap.comp_apply, Submodule.subtype_apply, dolbeaultComplex_d_apply,
            Iso.inv_hom_id_apply, (mem_closedForms_iff_delBarType_eq_zero p q φ.val).mp φ.property,
            map_zero] :=
  LinearMap.ext fun φ ↦ by
    rw [mk, HomologicalComplex.moduleCatCohomologyClassOfIso_apply,
      HomologicalComplex.moduleCatHomologyClass_apply]
    rfl

/-- Every Dolbeault cohomology class has a `∂bar`-closed representative. -/
theorem mk_surjective (p q : ℕ) : Function.Surjective (mk (E := E) (M := M) (F := F) p q) := by
  exact (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_surjective
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q) (closedForms E M F p)
    (dolbeaultComplexXIso p) (mem_closedForms_iff_complex p) q

/-- A closed type form represents zero exactly when it is `∂bar`-exact. -/
@[simp]
theorem mk_eq_zero_iff (p q : ℕ) (φ : closedForms E M F p q) :
    mk p q φ = 0 ↔ φ.val ∈ exactForms E M F p q :=
  (dolbeaultComplex E M F p).moduleCatCohomologyClassOfIso_eq_zero_iff
    (fun q ↦ (ofComplexManifold E M).typeForms (F := F) p q)
    (closedForms E M F p) (exactForms E M F p) (dolbeaultComplexXIso p)
    (mem_closedForms_iff_complex p) (mem_exactForms_iff_complex p) q φ

/-- Two closed type forms represent the same class exactly when their difference is exact. -/
theorem mk_eq_iff (p q : ℕ) (φ ψ : closedForms E M F p q) :
    mk p q φ = mk p q ψ ↔ (φ - ψ).val ∈ exactForms E M F p q :=
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

/-! ### The cochain map of a holomorphic map -/

section Map

/-! The induced cochain maps compare complexes in one universe, so the model spaces share a
universe, as do the manifolds. -/

universe u v

variable {E M F}

variable {E₁ E₂ E₃ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]
  {M₁ M₂ M₃ : Type v} [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [IsManifold 𝓘(ℂ, E₁) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [IsManifold 𝓘(ℂ, E₂) ∞ M₂]
  [TopologicalSpace M₃] [ChartedSpace E₃ M₃] [IsManifold 𝓘(ℂ, E₃) ∞ M₃]

namespace dolbeaultComplex

/-- The cochain map of Dolbeault complexes induced by a holomorphic map `f`, given as a smooth
map of the underlying real manifolds whose differential is complex-linear: in each degree it is
pullback of type forms along `f`. -/
def map {f : M₁ → M₂} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f) (p : ℕ) :
    dolbeaultComplex E₂ M₂ F p ⟶ dolbeaultComplex E₁ M₁ F p :=
  CochainComplex.ofHom (fun q ↦ (dolbeaultComplexXIso p q).hom ≫
      ModuleCat.ofHom (mpullbackType hf hJ p q) ≫ (dolbeaultComplexXIso p q).inv)
    fun q ↦ by
      have hcomm : ModuleCat.ofHom (mpullbackType (F := F) hf hJ p q) ≫
          ModuleCat.ofHom ((ofComplexManifold E₁ M₁).delBarType p q) =
            ModuleCat.ofHom ((ofComplexManifold E₂ M₂).delBarType p q) ≫
              ModuleCat.ofHom (mpullbackType hf hJ p (q + 1)) := by
        ext φ : 2
        exact delBarType_mpullbackType _ hf hJ p q φ
      rw [(Iso.eq_comp_inv _).mpr (dolbeaultComplex_d (M := M₁) p q),
        (Iso.eq_comp_inv _).mpr (dolbeaultComplex_d (M := M₂) p q)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hcomm]

/-- Under the canonical identifications of the terms, the induced cochain map is pullback of
type forms. -/
@[reassoc]
theorem map_f {f : M₁ → M₂} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
    (p q : ℕ) :
    (map (F := F) hf hJ p).f q ≫ (dolbeaultComplexXIso p q).hom =
      (dolbeaultComplexXIso p q).hom ≫ ModuleCat.ofHom (mpullbackType hf hJ p q) := by
  simp [map]

/-- The induced cochain map, on a type form read through the canonical identification of the
degree-`q` term, is pullback of that form. -/
theorem map_f_inv_apply {f : M₁ → M₂} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
    (p q : ℕ) (φ : (ofComplexManifold E₂ M₂).typeForms (F := F) p q) :
    (map hf hJ p).f q ((dolbeaultComplexXIso p q).inv φ) =
      (dolbeaultComplexXIso p q).inv (mpullbackType hf hJ p q φ) := by
  rw [(Iso.eq_comp_inv _).mpr (map_f hf hJ p q)]
  simp

/-- The cochain map induced by a holomorphic map depends only on the map. -/
theorem map_congr {f f' : M₁ → M₂} (h : f = f') (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
    (hf' : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f')
    (hJ' : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f') (p : ℕ) :
    map (F := F) hf hJ p = map hf' hJ' p := by
  subst h
  rfl

/-- The identity map induces the identity cochain map. -/
@[simp]
theorem map_id (p : ℕ) :
    map (F := F) (f := (id : M₁ → M₁)) contMDiff_id
      (isPseudoholomorphic_id (ofComplexManifold E₁ M₁)) p = 𝟙 _ := by
  ext q : 2
  simp [map, ModuleCat.ofHom_id]

/-- The induced cochain maps reverse composition of holomorphic maps. -/
theorem map_comp {f : M₁ → M₂} {g : M₂ → M₃} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
    (hg : ContMDiff 𝓘(ℝ, E₂) 𝓘(ℝ, E₃) ∞ g)
    (hJ' : IsPseudoholomorphic (ofComplexManifold E₂ M₂) (ofComplexManifold E₃ M₃) g)
    (p : ℕ) :
    map (F := F) (hg.comp hf) (hJ'.comp hJ) p = map hg hJ' p ≫ map hf hJ p := by
  ext q : 2
  simp only [map, HomologicalComplex.comp_f, Category.assoc, Iso.inv_hom_id_assoc,
    mpullbackType_comp hf hJ hg hJ' p q, ModuleCat.ofHom_comp]

end dolbeaultComplex

end Map

/-! ### The Dolbeault complex extended by zero to `ℤ` -/

namespace dolbeaultComplex

open HomologicalComplex

variable {E M F}

variable (E M F) in
/-- The degree-`n` term of the Dolbeault complex extended by zero, for `n = q`, is the module of
type-`(p,q)` forms. -/
def extendXEquiv (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n) :
    ((dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat).X n ≃ₗ[ℂ]
      (ofComplexManifold E M).typeForms (F := F) p q :=
  ((extendXIso _ _ (i := q) (by simp [← hn])) ≪≫ dolbeaultComplexXIso p q).toLinearEquiv

/-- `extendXEquiv` is the composite of the canonical identifications. -/
theorem extendXEquiv_apply (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n)
    (x : ((dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat).X n) :
    extendXEquiv E M F p q n hn x =
      (dolbeaultComplexXIso p q).hom
        ((extendXIso (dolbeaultComplex E M F p) ComplexShape.embeddingUpNat (i := q)
          (by simp [← hn])).hom x) :=
  (rfl)

/-- The inverse of `extendXEquiv` is the inverse of the canonical identifications. -/
theorem extendXEquiv_symm_apply (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n)
    (α : (ofComplexManifold E M).typeForms (F := F) p q) :
    (extendXEquiv E M F p q n hn).symm α =
      (extendXIso (dolbeaultComplex E M F p) ComplexShape.embeddingUpNat (i := q)
        (by simp [← hn])).inv ((dolbeaultComplexXIso p q).inv α) :=
  (rfl)

/-- In the coordinates `extendXEquiv`, the differential of the extended Dolbeault complex is
`∂bar`. -/
theorem extend_d_extendXEquiv_symm (p q : ℕ) (n m : ℤ) (hn : (q : ℤ) = n) (hm : n + 1 = m)
    (α : (ofComplexManifold E M).typeForms (F := F) p q) :
    ((dolbeaultComplex E M F p).extend ComplexShape.embeddingUpNat).d n m
        ((extendXEquiv E M F p q n hn).symm α) =
      (extendXEquiv E M F p (q + 1) m (by push_cast; omega)).symm
        ((ofComplexManifold E M).delBarType p q α) := by
  subst hn hm
  rw [extend_d_eq _ _ (i := q) (j := q + 1) (by simp) (by simp)]
  simp [extendXEquiv_symm_apply, dolbeaultComplex_d_apply]

section Map

universe u v

variable {E₁ E₂ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  {M₁ M₂ : Type v} [TopologicalSpace M₁] [ChartedSpace E₁ M₁] [IsManifold 𝓘(ℂ, E₁) ∞ M₁]
  [TopologicalSpace M₂] [ChartedSpace E₂ M₂] [IsManifold 𝓘(ℂ, E₂) ∞ M₂]

/-- In the coordinates `extendXEquiv`, the extension of the cochain map of a holomorphic map is
pullback of type forms. -/
theorem extendMap_map_f_extendXEquiv_symm {f : M₁ → M₂} (hf : ContMDiff 𝓘(ℝ, E₁) 𝓘(ℝ, E₂) ∞ f)
    (hJ : IsPseudoholomorphic (ofComplexManifold E₁ M₁) (ofComplexManifold E₂ M₂) f)
    (p q : ℕ) (n : ℤ) (hn : (q : ℤ) = n) (α : (ofComplexManifold E₂ M₂).typeForms (F := F) p q) :
    (extendMap (map (F := F) hf hJ p) ComplexShape.embeddingUpNat).f n
        ((extendXEquiv E₂ M₂ F p q n hn).symm α) =
      (extendXEquiv E₁ M₁ F p q n hn).symm (mpullbackType hf hJ p q α) := by
  subst hn
  rw [extendMap_f _ _ (i := q) (by simp)]
  simp only [extendXEquiv_symm_apply, ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rw [map_f_inv_apply]

end Map

end dolbeaultComplex

end TauCeti
