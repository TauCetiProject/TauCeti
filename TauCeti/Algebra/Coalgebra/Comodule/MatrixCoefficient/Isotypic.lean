/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Simple coefficient spaces are isotypic components

The coefficient space of a simple right comodule is precisely its isotypic component
in the regular module over the convolution dual. This comparison works over every
field and for infinite-dimensional coalgebras: it uses the full linear dual, not
field-valued points. Consequently distinct simple coefficient spaces are independent,
even without a cosemisimplicity assumption. The independence argument transports
Mathlib's `sSupIndep_isotypicComponents` through restriction of scalars, using
`Subcomodule.convolutionSubmoduleOrderIso` to compare the notions of simplicity.

## Main declarations

* `matrixCoefficientSubmodule_eq_isotypicComponent`: the coefficient/isotypic comparison.
* `sSupIndep_simpleCoefficientSubmodules`: independence of the distinct simple blocks.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), §12, matrix coefficients.
-/

public noncomputable section

namespace TauCeti.Comodule

universe u v w

variable {k : Type u} [Field k]
  {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
  {M : Type w} [AddCommGroup M] [Module k M] [Comodule k C M]

attribute [local instance] convolutionModule

/-- The coefficient space of a simple comodule is its isotypic component in the
regular convolution-dual module, restricted to the ground field. -/
theorem matrixCoefficientSubmodule_eq_isotypicComponent
    [IsSimpleOrder (Subcomodule k C M)] :
    matrixCoefficientSubmodule (R := k) (C := C) (M := M) =
      (isotypicComponent (WithConv (C →ₗ[k] k)) C M).restrictScalars k := by
  let D := WithConv (C →ₗ[k] k)
  have : IsSimpleModule D M := isSimpleModule_convolution_iff.mpr inferInstance
  apply le_antisymm
  · apply matrixCoefficientSubmodule_le
    intro φ m
    let f := (matrixCoefficientHom (C := C) φ).toConvolutionLinearMap
    have : IsSimpleModule D (⊤ : Submodule D M) :=
      IsSimpleModule.congr Submodule.topEquiv
    have hle : LinearMap.range f ≤ isotypicComponent D C M := by
      simpa only [Submodule.map_top,
        Submodule.topEquiv.isotypicComponent_eq (R := D) (M := C)] using
        (⊤ : Submodule D M).map_le_isotypicComponent f
    exact hle ⟨m, by simp [f]⟩
  · rw [isotypicComponent, Submodule.restrictScalars_sSup]
    apply sSup_le
    rintro _ ⟨N, ⟨e⟩, rfl⟩ c hc
    let f := (N.subtype ∘ₗ e.symm.toLinearMap).toComoduleHom
    have h := matrixCoefficient_mem_submodule (R := k) (C := C)
      (Coalgebra.counit ∘ₗ f.toLinearMap) (e ⟨c, hc⟩)
    rw [← matrixCoefficient_map, matrixCoefficient_counit_self] at h
    simpa [f] using h

/-- Every simple comodule occurs in the regular convolution-dual module. In particular
its isotypic component is one of Mathlib's nonzero isotypic components. -/
theorem isotypicComponent_convolution_mem_isotypicComponents
    [IsSimpleOrder (Subcomodule k C M)] :
    isotypicComponent (WithConv (C →ₗ[k] k)) C M ∈
      isotypicComponents (WithConv (C →ₗ[k] k)) C := by
  let D := WithConv (C →ₗ[k] k)
  have : IsSimpleModule D M := isSimpleModule_convolution_iff.mpr inferInstance
  have : Nontrivial M := IsSimpleModule.nontrivial D M
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero k hm
  let f := (matrixCoefficientHom (C := C) φ).toConvolutionLinearMap
  have hf : f ≠ 0 := by
    intro hf
    apply hφ
    have h := congrArg (Coalgebra.counit (R := k) (A := C)) (DFunLike.congr_fun hf m)
    simpa [f] using h
  let e := LinearEquiv.ofInjective f (f.injective_or_eq_zero.resolve_right hf)
  have : IsSimpleModule D (LinearMap.range f) := IsSimpleModule.congr e.symm
  exact ⟨LinearMap.range f, inferInstance, e.isotypicComponent_eq⟩

/-- The distinct coefficient spaces of simple comodules whose carriers have the same
universe as the coalgebra. Indexing by spaces, rather than by all simple objects,
avoids repeating a block for isomorphic comodules. -/
def simpleCoefficientSubmodules (k : Type u) [Field k]
    (C : Type v) [AddCommGroup C] [Module k C] [Coalgebra k C] :
    Set (Submodule k C) :=
  {P | ∃ M : ComoduleCat.{u, v, v} k C,
    IsSimpleOrder (Subcomodule k C M) ∧
      P = matrixCoefficientSubmodule (R := k) (C := C) (M := M)}

/-- Membership in the family of simple coefficient spaces is witnessed by a simple comodule. -/
theorem mem_simpleCoefficientSubmodules {P : Submodule k C} :
    P ∈ simpleCoefficientSubmodules k C ↔
      ∃ M : ComoduleCat.{u, v, v} k C, IsSimpleOrder (Subcomodule k C M) ∧
        P = matrixCoefficientSubmodule (R := k) (C := C) (M := M) := Iff.rfl

/-- The coefficient space of a simple comodule belongs to the family of simple coefficient
spaces. -/
@[simp]
theorem matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules
    {M : Type v} [AddCommGroup M] [Module k M] [Comodule k C M]
    [IsSimpleOrder (Subcomodule k C M)] :
    matrixCoefficientSubmodule (R := k) (C := C) (M := M) ∈
      simpleCoefficientSubmodules k C :=
  ⟨ComoduleCat.of k C M, inferInstance, rfl⟩

/-- A simple comodule has nonzero coefficient space, over any field. -/
theorem matrixCoefficientSubmodule_ne_bot_of_simple
    [IsSimpleOrder (Subcomodule k C M)] :
    matrixCoefficientSubmodule (R := k) (C := C) (M := M) ≠ ⊥ := by
  rw [matrixCoefficientSubmodule_eq_isotypicComponent, ne_eq,
    Submodule.restrictScalars_eq_bot_iff]
  exact (bot_lt_isotypicComponents
    (isotypicComponent_convolution_mem_isotypicComponents (C := C) (M := M))).ne'

/-- Zero is not a simple coefficient space. -/
@[simp]
theorem bot_notMem_simpleCoefficientSubmodules :
    (⊥ : Submodule k C) ∉ simpleCoefficientSubmodules k C := by
  rintro ⟨M, hM, h⟩
  let := hM
  exact matrixCoefficientSubmodule_ne_bot_of_simple (C := C) (M := M) h.symm

/-- Distinct simple coefficient spaces are independent. This holds over arbitrary fields,
and does not require that the coalgebra be linearly reductive. -/
theorem sSupIndep_simpleCoefficientSubmodules :
    sSupIndep (simpleCoefficientSubmodules k C) := by
  let D := WithConv (C →ₗ[k] k)
  have hind : iSupIndep fun P : isotypicComponents D C ↦ P.1.restrictScalars k := by
    intro P
    simpa only [← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff]
      using (sSupIndep_iff _).mp (sSupIndep_isotypicComponents D C) P
  apply hind.sSupIndep_range.mono
  rintro P ⟨M, hM, rfl⟩
  let := hM
  exact ⟨⟨_, isotypicComponent_convolution_mem_isotypicComponents (C := C) (M := M)⟩,
    matrixCoefficientSubmodule_eq_isotypicComponent.symm⟩

end TauCeti.Comodule
