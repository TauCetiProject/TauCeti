/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Basic
public import TauCeti.CategoryTheory.Graded.WordPathCochain
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hochschild.Complex
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Positive-arity Hochschild cochains of an A-infinity category

The Hochschild cochains of a graded linear quiver are supported on composable strings and take
values in the Hom module between their endpoints. For an A-infinity category, this condition
defines a subcomplex of the positive-arity suspended Hochschild complex of its total morphism
algebra. The differential is `[m, -]`; it preserves path compatibility because braces do.

This file constructs that subcomplex and its injective comparison map, and restricts the brace
to its homogeneous cochains. The degree is the suspended degree: an unsuspended arity-`n`
operation of internal degree `r` has degree `r + n - 1`. Cochains may have arbitrary components
in all positive arities. Arity-zero cochains are not included, so this is not the full
Hochschild complex. No units, finite object set, or characteristic-zero hypothesis are required.

We consume the total-algebra Hochschild differential from
`AInfinityAlgebra.PositiveHochschild`, the word-level path-compatibility calculus and its Koszul
brace. The conventions follow Getzler--Jones, *A-infinity algebras and the cyclic bar complex*,
Sections 1--2, and Keller, *Introduction to A-infinity algebras and modules*, Section 7.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.AInfinityCategory.PositiveHochschild

open GradedLinearQuiver ReducedTensorWords

universe u v w

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]
  (𝒞 : AInfinityCategory R C)

/-- Homogeneous suspended Hochschild cochains supported on composable paths. -/
def cochains (p : ℤ) :
    Submodule R (ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R C) :=
  AInfinityAlgebra.PositiveHochschild.cochains 𝒞.toAInfinityAlgebra p ⊓ wordPathCochains id

@[simp]
theorem mem_cochains {p : ℤ}
    {F : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R C} :
    F ∈ cochains 𝒞 p ↔
      LinearMap.IsHomogeneous F (gradedPiece ((totalGrading R C).shift 1))
        ((totalGrading R C).shift 1).piece p ∧ IsWordPathCompatible id F := by
  simp only [cochains, Submodule.mem_inf, AInfinityAlgebra.PositiveHochschild.mem_cochains,
    mem_wordPathCochains, 𝒞.grading_eq]

/-- The brace preserves homogeneous path cochains. -/
theorem brace_mem_cochains {p q n : ℤ} (h : p + q = n)
    {F G : ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R C}
    (hF : F ∈ cochains 𝒞 p) (hG : G ∈ cochains 𝒞 q) :
    ReducedTensorWords.brace ((totalGrading R C).shift 1) F G q ∈ cochains 𝒞 n := by
  rw [mem_cochains, ← h]
  refine ⟨isHomogeneous_brace ((mem_cochains 𝒞).mp hF).1 ((mem_cochains 𝒞).mp hG).1, ?_⟩
  rw [ReducedTensorWords.brace_def]
  exact ((mem_cochains 𝒞).mp hF).2.comp_gradedCoderiv ((mem_cochains 𝒞).mp hG).2 1 q

/-- The brace of homogeneous path cochains of degrees `p` and `q`, landing in degree `n`
for `h : p + q = n`. -/
def brace {p q n : ℤ} (h : p + q = n) :
    cochains 𝒞 p →ₗ[R] cochains 𝒞 q →ₗ[R] cochains 𝒞 n :=
  let B : cochains 𝒞 p →ₗ[R] cochains 𝒞 q →ₗ[R]
      (ReducedTensorWords R (TotalHom R C) →ₗ[R] TotalHom R C) :=
    ((WordPathCochain.brace (R := R) (C := C) 1 q).compl₁₂
      (Submodule.inclusion (p := cochains 𝒞 p) inf_le_right)
      (Submodule.inclusion (p := cochains 𝒞 q) inf_le_right)).compr₂
        (wordPathCochains id).subtype
  B.codRestrict₂ (cochains 𝒞 n).subtype (Submodule.injective_subtype _) fun F G ↦ by
    rw [Submodule.range_subtype]
    dsimp only [B]
    simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
      WordPathCochain.coe_brace]
    exact brace_mem_cochains 𝒞 h F.property G.property

@[simp]
theorem coe_brace {p q n : ℤ} (h : p + q = n) (F : cochains 𝒞 p) (G : cochains 𝒞 q) :
    (brace 𝒞 h F G).val = ReducedTensorWords.brace ((totalGrading R C).shift 1) F G q := by
  -- Expose the restriction wrapper, then use its evaluation lemma at the subtype injection.
  rw [← Submodule.subtype_apply (brace 𝒞 h F G)]
  unfold brace
  rw [LinearMap.codRestrict₂_apply]
  simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
    WordPathCochain.coe_brace]
  -- Submodule inclusions leave the underlying Taylor maps unchanged.
  rfl

/-- The Hochschild differential restricts to path cochains. Its square-zero law is inherited
from the total morphism algebra, not imposed as additional categorical data. -/
def d (p q : ℤ) (h : p + 1 = q) : cochains 𝒞 p →ₗ[R] cochains 𝒞 q where
  toFun F := ⟨𝒞.toAInfinityAlgebra.hochschildDifferential p F, by
    refine ⟨?_, ?_⟩
    · have hd := (AInfinityAlgebra.PositiveHochschild.d 𝒞.toAInfinityAlgebra p q h
        ⟨F.val, F.property.1⟩).property
      rwa [AInfinityAlgebra.PositiveHochschild.coe_d] at hd
    · rw [AInfinityAlgebra.hochschildDifferential_def, 𝒞.grading_eq]
      exact gerstenhaberBracket_mem_wordPathCochains
        (mem_wordPathCochains.mpr 𝒞.isWordPathCompatible_taylor) F.property.2 1 1 p⟩
  map_add' F G := Subtype.ext (𝒞.toAInfinityAlgebra.hochschildDifferential_add p F G)
  map_smul' r F := Subtype.ext (𝒞.toAInfinityAlgebra.hochschildDifferential_smul p r F)

@[simp]
theorem coe_d (p q : ℤ) (h : p + 1 = q) (F : cochains 𝒞 p) :
    (d 𝒞 p q h F).val = 𝒞.toAInfinityAlgebra.hochschildDifferential p F := (rfl)

/-- The pathwise Hochschild differential squares to zero over any commutative ring. -/
@[simp]
theorem d_d (p q r : ℤ) (hpq : p + 1 = q) (hqr : q + 1 = r) (F : cochains 𝒞 p) :
    d 𝒞 q r hqr (d 𝒞 p q hpq F) = 0 := by
  apply Subtype.ext
  simpa only [coe_d, AInfinityAlgebra.PositiveHochschild.coe_d, ZeroMemClass.coe_zero] using
    congrArg (fun x ↦ x.val)
      (AInfinityAlgebra.PositiveHochschild.d_d 𝒞.toAInfinityAlgebra p q r hpq hqr
        ⟨F.val, F.property.1⟩)

/-- The positive-arity suspended Hochschild complex of an A-infinity category. -/
abbrev complex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.of (fun p ↦ ModuleCat.of R (cochains 𝒞 p))
    (fun p ↦ ModuleCat.ofHom (d 𝒞 p (p + 1) rfl)) (fun p ↦ by
      apply ModuleCat.hom_ext
      exact LinearMap.ext (d_d 𝒞 p (p + 1) (p + 1 + 1) rfl rfl))

/-- The adjacent complex differential is the restricted Hochschild differential. -/
@[simp]
theorem complex_d (p q : ℤ) (h : p + 1 = q) :
    (complex 𝒞).d p q = ModuleCat.ofHom (d 𝒞 p q h) := by
  subst q
  exact CochainComplex.of_d (fun p ↦ ModuleCat.of R (cochains 𝒞 p))
    (fun p ↦ ModuleCat.ofHom (d 𝒞 p (p + 1) rfl)) p

/-- Inclusion into the positive-arity Hochschild complex of the total morphism algebra. -/
def inclusion : complex 𝒞 ⟶ AInfinityAlgebra.PositiveHochschild.complex 𝒞.toAInfinityAlgebra where
  f p := ModuleCat.ofHom (Submodule.inclusion inf_le_left)
  comm' p q hpq := by
    rw [complex_d 𝒞 p q hpq, AInfinityAlgebra.PositiveHochschild.complex_d _ p q hpq]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun (F : cochains 𝒞 p) ↦ Subtype.ext ?_
    exact (AInfinityAlgebra.PositiveHochschild.coe_d 𝒞.toAInfinityAlgebra p q hpq
      (Submodule.inclusion inf_le_left F)).trans (coe_d 𝒞 p q hpq F).symm

@[simp]
theorem inclusion_f_apply (p : ℤ) (F : cochains 𝒞 p) :
    (((inclusion 𝒞).f p).hom F).val = F.val := (rfl)

/-- Pathwise cochains form a genuine subcomplex of the total-algebra cochains. -/
instance : Mono (inclusion 𝒞) :=
  HomologicalComplex.mono_of_mono_f _ fun _ ↦
    (ModuleCat.mono_iff_injective _).mpr (Submodule.inclusion_injective inf_le_left)

end TauCeti.AInfinityCategory.PositiveHochschild
