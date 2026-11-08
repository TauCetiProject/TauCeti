/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
public import TauCeti.RingTheory.SimpleModule.Isotypic

/-!
# Coefficient spaces of simple comodules are isotypic components

Let `C` be a coalgebra over a commutative ring `R` which is projective as an `R`-module, for
instance any coalgebra over a field. Regard `C` and its right comodules as left modules over the
convolution dual `C →ₗ[R] R`, through `TauCeti.Comodule.convolutionModule`; comodule morphisms
and subcomodules are then the module maps and submodules.

For a simple right comodule `M`, the span of the matrix coefficients of `M` is exactly the
`M`-isotypic component of the regular comodule `C`. Indeed each matrix-coefficient map `M → C`
is a morphism out of the simple module `M`, and conversely each copy of `M` inside `C` consists
of matrix coefficients of `M`, each element of `C` being its own coefficient against the counit.

Consequently the coefficient spaces of pairwise non-isomorphic simple comodules are independent,
and so are the coefficient spaces of the simple right coideals of `C`. Over a field, two simple
comodules have the same coefficient space exactly when they are isomorphic. These are the
independence and labelling halves of the algebraic Peter--Weyl decomposition of the coordinate
ring of a linearly reductive group into the coefficient spaces of its irreducible
representations.

## Main statements

* `TauCeti.Comodule.matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars`: the
  coefficient space of a simple comodule `M` is the `M`-isotypic component of `C`.
* `TauCeti.Comodule.iSupIndep_matrixCoefficientSubmodule`: coefficient spaces of pairwise
  non-isomorphic simple comodules are independent.
* `TauCeti.Comodule.sSupIndep_matrixCoefficientSubmodule_image_isAtom`: the coefficient spaces
  of the simple right coideals of `C` form an independent set.
* `TauCeti.Comodule.matrixCoefficientSubmodule_eq_iff`: two simple comodules, projective over
  the ground ring, have the same coefficient space exactly when there is a nonzero morphism
  between them.

## References

* M. Sweedler, *Hopf Algebras* (1969), Chapters II and XIV.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings* (1993), §5.1, the coradical as a
  direct sum of simple subcoalgebras.
-/

public section

namespace TauCeti.Comodule

section Semiring

variable {R C M : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- A nonzero comodule which is projective over the ground ring has a nonzero coefficient space:
the counit recovers every linear functional from its matrix coefficients. -/
theorem matrixCoefficientSubmodule_ne_bot [Module.Projective R M] [Nontrivial M] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) ≠ ⊥ := by
  intro h
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  refine hm ((Module.forall_dual_apply_eq_zero_iff R m).mp fun φ ↦ ?_)
  rw [← counit_matrixCoefficient (R := R) (C := C) φ m,
    (Submodule.eq_bot_iff _).mp h _ (matrixCoefficient_mem_submodule (R := R) (C := C) φ m),
    map_zero]

end Semiring

variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [AddCommGroup N] [Module R N] [Comodule R C N]

attribute [local instance] convolutionModule

/-- Every copy of `M` inside the regular comodule consists of matrix coefficients of `M`: the
`M`-isotypic component of `C`, for the convolution-dual action, lies in the coefficient space of
`M`. No simplicity of `M` is needed. -/
theorem isotypicComponent_restrictScalars_le_matrixCoefficientSubmodule :
    (isotypicComponent (WithConv (C →ₗ[R] R)) C M).restrictScalars R ≤
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  rw [isotypicComponent, Submodule.restrictScalars_sSup]
  refine sSup_le ?_
  rintro _ ⟨T, ⟨e⟩, rfl⟩ c hc
  -- `c` is the value at `e c` of the comodule morphism `M → C` given by `e⁻¹`, and an element of
  -- the regular comodule is its own coefficient against the counit.
  let f := (T.subtype ∘ₗ e.symm.toLinearMap).toComoduleHom
  have hfc : f (e ⟨c, hc⟩) = c := by simp [f]
  rw [← hfc, ← matrixCoefficient_counit_self (R := R) (C := C) (f _), matrixCoefficient_map]
  exact matrixCoefficient_mem_submodule (R := R) (C := C) _ _

/-- The matrix coefficients of a simple comodule `M` lie in the `M`-isotypic component of the
regular comodule, since each matrix-coefficient map is a morphism out of the simple module
`M`. -/
theorem matrixCoefficientSubmodule_le_isotypicComponent_restrictScalars
    [IsSimpleOrder (Subcomodule R C M)] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) ≤
      (isotypicComponent (WithConv (C →ₗ[R] R)) C M).restrictScalars R := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  exact matrixCoefficientSubmodule_le fun φ m ↦ by
    simpa using
      (matrixCoefficientHom (C := C) φ).toConvolutionLinearMap.apply_mem_isotypicComponent m

/-- **The coefficient space of a simple comodule is an isotypic component.** For a simple right
comodule `M`, the span of its matrix coefficients is the `M`-isotypic component of the regular
comodule `C`, viewed as a module over the convolution dual. -/
theorem matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars
    [IsSimpleOrder (Subcomodule R C M)] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) =
      (isotypicComponent (WithConv (C →ₗ[R] R)) C M).restrictScalars R :=
  le_antisymm matrixCoefficientSubmodule_le_isotypicComponent_restrictScalars
    isotypicComponent_restrictScalars_le_matrixCoefficientSubmodule

/-- Simple comodules joined by a nonzero morphism, which is then an isomorphism, have the same
coefficient space. -/
theorem matrixCoefficientSubmodule_eq_of_ne_zero [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] {f : Hom R C M N} (hf : f ≠ 0) :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := N) := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C N)›
  have hf' : f.toConvolutionLinearMap ≠ 0 := fun h ↦ hf <| by
    ext m
    simpa using LinearMap.congr_fun h m
  rw [matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars,
    matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars,
    (LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hf')).isotypicComponent_eq]

/-- If the only comodule morphism from a nonzero comodule `M` to `N` is zero, then `M` and `N`
are not isomorphic as modules over the convolution dual. -/
private theorem not_nonempty_convolutionLinearEquiv [Nontrivial M]
    (h : ∀ f : Hom R C M N, f = 0) : ¬ Nonempty (M ≃ₗ[WithConv (C →ₗ[R] R)] N) := by
  rintro ⟨e⟩
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  refine hm (e.map_eq_zero_iff.mp ?_)
  simpa using congr_arg (fun g : Hom R C M N ↦ g m) (h e.toLinearMap.toComoduleHom)

/-- Coefficient spaces of simple comodules with no nonzero morphism between them are
disjoint. -/
theorem disjoint_matrixCoefficientSubmodule [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)] (h : ∀ f : Hom R C M N, f = 0) :
    Disjoint (matrixCoefficientSubmodule (R := R) (C := C) (M := M))
      (matrixCoefficientSubmodule (R := R) (C := C) (M := N)) := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C N)›
  have := IsSimpleModule.nontrivial (WithConv (C →ₗ[R] R)) M
  rw [matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars,
    matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars,
    Submodule.disjoint_restrictScalars_iff]
  exact disjoint_isotypicComponent _ _ M N (not_nonempty_convolutionLinearEquiv h)

/-- **Coefficient spaces of non-isomorphic simple comodules are independent.** For a family of
simple comodules with no nonzero morphism between distinct members, the coefficient spaces form
an independent family of submodules of `C`. -/
theorem iSupIndep_matrixCoefficientSubmodule {ι : Type*} (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Comodule R C (M i)]
    [∀ i, IsSimpleOrder (Subcomodule R C (M i))]
    (hM : Pairwise fun i j ↦ ∀ f : Hom R C (M i) (M j), f = 0) :
    iSupIndep fun i ↦ matrixCoefficientSubmodule (R := R) (C := C) (M := M i) := by
  have (i : ι) : IsSimpleModule (WithConv (C →ₗ[R] R)) (M i) :=
    isSimpleModule_convolution_iff.mpr inferInstance
  have (i : ι) := IsSimpleModule.nontrivial (WithConv (C →ₗ[R] R)) (M i)
  have hind := iSupIndep_isotypicComponent (WithConv (C →ₗ[R] R)) C M fun i j he ↦
    by_contra fun hij ↦ not_nonempty_convolutionLinearEquiv (hM hij) he
  intro i
  simp_rw [matrixCoefficientSubmodule_eq_isotypicComponent_restrictScalars,
    ← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff]
  exact hind i

/-- **Coefficient spaces of simple right coideals are independent.** The coefficient spaces of
the simple subcomodules of the regular comodule `C` form an independent set of submodules
of `C`. -/
theorem sSupIndep_matrixCoefficientSubmodule_image_isAtom :
    sSupIndep ((fun S : Subcomodule R C C ↦ matrixCoefficientSubmodule (R := R) (C := C) (M := S))
      '' {S | IsAtom S}) := by
  rw [sSupIndep_iff]
  -- Index the set by itself, choosing a simple right coideal with each coefficient space.
  choose S hS hSP using fun P : (fun S : Subcomodule R C C ↦
    matrixCoefficientSubmodule (R := R) (C := C) (M := S)) '' {S | IsAtom S} ↦ P.2
  have : ∀ P, IsSimpleOrder (Subcomodule R C (S P)) :=
    fun P ↦ Subcomodule.isSimpleOrder_iff_isAtom.mpr (hS P)
  have hind := iSupIndep_matrixCoefficientSubmodule (R := R) (C := C) (fun P ↦ S P)
    fun P Q hPQ f ↦ by_contra fun hf ↦
      hPQ (Subtype.ext <| (hSP P).symm.trans <| (matrixCoefficientSubmodule_eq_of_ne_zero hf).trans
        (hSP Q))
  convert hind with P
  exact (hSP P).symm

/-- **Coefficient spaces label simple comodules.** Two simple comodules which are projective
over the ground ring, for instance any two simple comodules over a field, have the same
coefficient space exactly when there is a nonzero morphism between them, that is, exactly when
they are isomorphic. -/
theorem matrixCoefficientSubmodule_eq_iff [Module.Projective R M]
    [IsSimpleOrder (Subcomodule R C M)] [IsSimpleOrder (Subcomodule R C N)] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) =
        matrixCoefficientSubmodule (R := R) (C := C) (M := N) ↔
      ∃ f : Hom R C M N, f ≠ 0 := by
  refine ⟨fun h ↦ ?_, fun ⟨f, hf⟩ ↦ matrixCoefficientSubmodule_eq_of_ne_zero hf⟩
  by_contra! hzero
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  have := IsSimpleModule.nontrivial (WithConv (C →ₗ[R] R)) M
  have hd := disjoint_matrixCoefficientSubmodule hzero
  rw [← h, disjoint_self] at hd
  exact matrixCoefficientSubmodule_ne_bot hd

end TauCeti.Comodule
