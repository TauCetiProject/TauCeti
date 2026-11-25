/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.Algebra.Homology.HomologicalComplex.Double
import TauCeti.Algebra.Category.ModuleCat.ExtendScalarsQuotient
import TauCeti.RingTheory.Ideal.Quotient.Operations

/-!
# The two-term resolution of the quotient by a nonzerodivisor

For a commutative ring `A` and a nonzerodivisor `f ∈ A`, multiplication by `f` is injective with
image the ideal `(f)`, so

`0 ⟶ A --f--> A ⟶ A ⧸ (f) ⟶ 0`

is exact, and the two-term complex `A --f--> A` in degrees `1` and `0`, augmented by the quotient
map, is a projective resolution of `A ⧸ (f)`.

## Main definitions

* `TauCeti.regularElementComplex f`: the two-term complex `A --f--> A` in degrees `1` and `0`,
  as Mathlib's `HomologicalComplex.double`.
* `TauCeti.regularElementProjectiveResolution f hf`: for `f ∈ nonZeroDivisors A`, the projective
  resolution of `A ⧸ (f)` with complex `regularElementComplex f` and augmentation the quotient
  map (`TauCeti.regularElementProjectiveResolution_π_f_zero`).

## Main results

* `TauCeti.extendScalars_map_regularElementMul`: multiplication by `f` reduces to zero modulo
  `(f)`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace TauCeti

variable {A : Type u} [CommRing A] (f : A)

/-- Multiplication by `f` on the regular module, as a morphism of `ModuleCat A`. -/
abbrev regularElementMul : ModuleCat.of A A ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (LinearMap.mulLeft A f)

/-- The two-term complex `A --f--> A`, in homological degrees `1` and `0`. -/
abbrev regularElementComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  HomologicalComplex.double (regularElementMul f) (c := ComplexShape.down ℕ) (i₀ := 1)
    (i₁ := 0) rfl

/-- The augmentation of `regularElementComplex f` in degree `0`: the quotient map
`A ⟶ A ⧸ (f)`. -/
abbrev regularElementAugmentation :
    (regularElementComplex f).X 0 ⟶ ModuleCat.of A (A ⧸ Ideal.span {f}) :=
  (HomologicalComplex.doubleXIso₁ (regularElementMul f) (c := ComplexShape.down ℕ) rfl
      one_ne_zero).hom ≫ ModuleCat.ofHom (Ideal.Quotient.mkₐ A (Ideal.span {f})).toLinearMap

/-- The augmentation kills the image of the differential. -/
theorem regularElementComplex_d_comp_augmentation :
    (regularElementComplex f).d 1 0 ≫ regularElementAugmentation f = 0 := by
  rw [HomologicalComplex.double_d _ _ one_ne_zero, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc, ← ModuleCat.ofHom_comp,
    (Ideal.exact_mulLeft_mkₐ_span_singleton (R := A) f).linearMap_comp_eq_zero,
    ModuleCat.ofHom_zero, comp_zero]

/-- Reducing multiplication by `f` modulo `(f)` gives the zero map. -/
theorem extendScalars_map_regularElementMul :
    (ModuleCat.extendScalars (Ideal.Quotient.mk (Ideal.span {f}))).map (regularElementMul f) =
      0 := by
  ext m
  apply (Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).injective
  -- `ext` states the goal on `1 ⊗ₜ m` with `1 : A ⧸ (f)`, whereas the `tmul` lemmas expect `1`
  -- in the restriction of scalars of `A ⧸ (f)`; the two types agree only after unfolding
  -- `ModuleCat.restrictScalars`, so both lemmas need `erw`.
  erw [ModuleCat.ExtendScalars.map_tmul]
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {f}))]
  erw [Ideal.extendScalarsMkEquivQuotSMul_mk_tmul]
  have h0 : (Submodule.Quotient.mk ((1 : A) • (regularElementMul f).hom m) :
      A ⧸ (Ideal.span {f} • ⊤ : Submodule A A)) = 0 := by
    rw [ModuleCat.hom_ofHom, LinearMap.mulLeft_apply, one_smul, Submodule.Quotient.mk_eq_zero,
      Ideal.smul_top_eq_map]
    simpa using Ideal.mul_mem_right m _ (Ideal.mem_span_singleton_self f)
  exact h0.trans ((Ideal.extendScalarsMkEquivQuotSMul (Ideal.span {f}) A).map_zero).symm

/-- **The two-term resolution of `A ⧸ (f)`.** For a nonzerodivisor `f`, the complex
`A --f--> A` in degrees `1` and `0`, augmented by the quotient map, is a projective resolution of
`A ⧸ (f)`. -/
def regularElementProjectiveResolution (hf : f ∈ nonZeroDivisors A) :
    ProjectiveResolution (ModuleCat.of A (A ⧸ Ideal.span {f})) where
  complex := regularElementComplex f
  projective n := by
    rcases n with _ | _ | n
    · exact Projective.of_iso (HomologicalComplex.doubleXIso₁ _ _ one_ne_zero).symm
        (inferInstanceAs (Projective (ModuleCat.of A A)))
    · exact Projective.of_iso (HomologicalComplex.doubleXIso₀ _ _).symm
        (inferInstanceAs (Projective (ModuleCat.of A A)))
    · exact (HomologicalComplex.isZero_double_X _ _ _ (by omega) (by omega)).projective
  π := (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨regularElementAugmentation f, regularElementComplex_d_comp_augmentation f⟩
  quasiIso := ⟨fun n ↦ by
    rcases n with _ | _ | n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        have hex := Ideal.exact_mulLeft_mkₐ_span_singleton (R := A) f
        refine (ShortComplex.exact_and_epi_g_iff_of_iso (S₂ := ModuleCat.shortComplexOfCompEqZero
          _ _ hex.linearMap_comp_eq_zero) ?_).2 ⟨ModuleCat.shortComplex_exact _ hex,
            (ModuleCat.epi_iff_surjective _).2 (Ideal.Quotient.mkₐ_surjective A _)⟩
        exact ShortComplex.isoMk
          (HomologicalComplex.doubleXIso₀ (regularElementMul f) (c := ComplexShape.down ℕ) rfl)
          (HomologicalComplex.doubleXIso₁ (regularElementMul f) (c := ComplexShape.down ℕ) rfl
            one_ne_zero) (Iso.refl _)
          (by simp [HomologicalComplex.double_d _ _ one_ne_zero]) (by simp)
      all_goals first | rfl | exact (regularElementComplex f).shape _ _ (by simp)
    · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      have : Mono (regularElementMul f) := (ModuleCat.mono_iff_injective _).2 fun _ _ h ↦
        (isRegular_iff_mem_nonZeroDivisors.2 hf).left h
      exact (isZero_kernel_of_mono _).of_iso
        (HomologicalComplex.doubleHomologyIso₀ one_ne_zero (limit.isLimit _))
    · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
        HomologicalComplex.exactAt_iff_isZero_homology]
      exact HomologicalComplex.isZero_double_homology _ _ _ (by omega) (by omega)⟩

/-- The complex of `regularElementProjectiveResolution f hf` is `regularElementComplex f`. -/
theorem regularElementProjectiveResolution_complex (hf : f ∈ nonZeroDivisors A) :
    (regularElementProjectiveResolution f hf).complex = regularElementComplex f := by
  rfl

/-- The degree-one term of `regularElementProjectiveResolution f hf` is the regular module. -/
def regularElementProjectiveResolutionXIso₁ (hf : f ∈ nonZeroDivisors A) :
    (regularElementProjectiveResolution f hf).complex.X 1 ≅ ModuleCat.of A A :=
  HomologicalComplex.doubleXIso₀ (regularElementMul f) (c := ComplexShape.down ℕ) rfl

/-- The degree-zero term of `regularElementProjectiveResolution f hf` is the regular module. -/
def regularElementProjectiveResolutionXIso₀ (hf : f ∈ nonZeroDivisors A) :
    (regularElementProjectiveResolution f hf).complex.X 0 ≅ ModuleCat.of A A :=
  HomologicalComplex.doubleXIso₁ (regularElementMul f) (c := ComplexShape.down ℕ) rfl one_ne_zero

/-- The differential of `regularElementProjectiveResolution f hf` is multiplication by `f`. -/
theorem regularElementProjectiveResolution_complex_d (hf : f ∈ nonZeroDivisors A) :
    (regularElementProjectiveResolution f hf).complex.d 1 0 =
      (regularElementProjectiveResolutionXIso₁ f hf).hom ≫ regularElementMul f ≫
        (regularElementProjectiveResolutionXIso₀ f hf).inv :=
  HomologicalComplex.double_d _ _ one_ne_zero

/-- The terms of `regularElementProjectiveResolution f hf` vanish above degree one. -/
theorem isZero_regularElementProjectiveResolution_complex_X (hf : f ∈ nonZeroDivisors A)
    (n : ℕ) (hn : 2 ≤ n) : IsZero ((regularElementProjectiveResolution f hf).complex.X n) :=
  HomologicalComplex.isZero_double_X (regularElementMul f) (c := ComplexShape.down ℕ) rfl n
    (by omega) (by omega)

/-- The augmentation of `regularElementProjectiveResolution f hf` in degree `0` is the quotient
map. -/
theorem regularElementProjectiveResolution_π_f_zero (hf : f ∈ nonZeroDivisors A) :
    (regularElementProjectiveResolution f hf).π.f 0 =
      (regularElementProjectiveResolutionXIso₀ f hf).hom ≫
        ModuleCat.ofHom (Ideal.Quotient.mkₐ A (Ideal.span {f})).toLinearMap ≫
          (HomologicalComplex.singleObjXSelf _ 0 _).inv := by
  simp [regularElementProjectiveResolution, regularElementProjectiveResolutionXIso₀,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero]

end TauCeti
