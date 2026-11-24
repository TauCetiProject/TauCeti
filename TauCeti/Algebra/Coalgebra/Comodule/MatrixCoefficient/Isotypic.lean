/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Module
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Morphism
public import TauCeti.Algebra.Coalgebra.Comodule.Preadditive
public import TauCeti.RingTheory.SimpleModule.Isotypic
import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Trivial
import TauCeti.Algebra.Coalgebra.Subcomodule.Finite

/-!
# Simple coefficient spaces are isotypic components

The coefficient space of a simple right comodule is precisely its isotypic component
in the regular module over the convolution dual. This comparison works for every coalgebra
which is projective over its commutative ground ring, in particular over every field and for
infinite-dimensional coalgebras: it uses the full linear dual, not field-valued points.
Indeed each matrix-coefficient map `M → C` is a morphism out of the simple module `M`, and
conversely each copy of `M` inside `C` consists of matrix coefficients of `M`, each element of
`C` being its own coefficient against the counit.

Consequently the coefficient spaces of pairwise non-isomorphic simple comodules are
independent, and distinct simple coefficient spaces are independent, even without a
cosemisimplicity assumption. The independence argument transports Mathlib's
`sSupIndep_isotypicComponents` through restriction of scalars, using
`Subcomodule.convolutionSubmoduleOrderIso` to compare the notions of simplicity.
Two simple comodules which are projective over the ground ring, for instance any two simple
comodules over a field, have the same coefficient space exactly when they are isomorphic, so
coefficient spaces label the isomorphism classes of simple comodules.

## Main declarations

* `matrixCoefficientSubmodule_eq_isotypicComponent`: the coefficient/isotypic comparison.
* `hom_eq_zero_of_matrixCoefficientSubmodule_ne`: simple comodules with distinct coefficient
  spaces admit no nonzero comodule morphism between them.
* `iSupIndep_matrixCoefficientSubmodule`: coefficient spaces of pairwise non-isomorphic simple
  comodules are independent.
* `matrixCoefficientSubmodule_eq_iff`: two simple comodules, projective over the ground ring,
  have the same coefficient space exactly when there is a nonzero morphism between them.
* `finite_of_mem_simpleCoefficientSubmodules`: simple coefficient spaces are finite-dimensional.
* `sSupIndep_simpleCoefficientSubmodules`: independence of the distinct simple blocks.
* `isInternal_of_sSup_simpleCoefficientSubmodules_eq_top`: a coalgebra over a field spanned by its
  distinct simple coefficient spaces is their internal direct sum.
* `span_singleton_one_mem_simpleCoefficientSubmodules`: over a bialgebra over a field, the line
  `k · 1` is a simple coefficient space.

## References

* M. Sweedler, *Hopf Algebras*, Chapters II and XIV.
* J. S. Milne, *Algebraic Groups* (2017), §12, matrix coefficients.
-/

public noncomputable section

namespace TauCeti.Comodule

attribute [local instance] convolutionModule

section Ring

variable {R C M N : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [Coalgebra R C] [Module.Projective R C]
  [AddCommGroup M] [Module R M] [Comodule R C M]
  [AddCommGroup N] [Module R N] [Comodule R C N]

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
theorem matrixCoefficientSubmodule_le_isotypicComponent
    [IsSimpleOrder (Subcomodule R C M)] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) ≤
      (isotypicComponent (WithConv (C →ₗ[R] R)) C M).restrictScalars R := by
  have := isSimpleModule_convolution_iff.mpr ‹IsSimpleOrder (Subcomodule R C M)›
  exact matrixCoefficientSubmodule_le fun φ m ↦ by
    simpa using
      (matrixCoefficientHom (C := C) φ).toConvolutionLinearMap.apply_mem_isotypicComponent m

/-- The coefficient space of a simple comodule is its isotypic component in the
regular convolution-dual module, restricted to the ground ring. -/
theorem matrixCoefficientSubmodule_eq_isotypicComponent
    [IsSimpleOrder (Subcomodule R C M)] :
    matrixCoefficientSubmodule (R := R) (C := C) (M := M) =
      (isotypicComponent (WithConv (C →ₗ[R] R)) C M).restrictScalars R :=
  le_antisymm matrixCoefficientSubmodule_le_isotypicComponent
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
  rw [matrixCoefficientSubmodule_eq_isotypicComponent,
    matrixCoefficientSubmodule_eq_isotypicComponent,
    (LinearEquiv.ofBijective _ (LinearMap.bijective_of_ne_zero hf')).isotypicComponent_eq]

/-- Simple comodules with distinct coefficient spaces have no nonzero comodule morphism between
them. -/
theorem hom_eq_zero_of_matrixCoefficientSubmodule_ne [IsSimpleOrder (Subcomodule R C M)]
    [IsSimpleOrder (Subcomodule R C N)]
    (hne : matrixCoefficientSubmodule (R := R) (C := C) (M := M) ≠
      matrixCoefficientSubmodule (R := R) (C := C) (M := N))
    (f : Hom R C M N) : f = 0 := by
  by_contra hf
  exact hne (matrixCoefficientSubmodule_eq_of_ne_zero hf)

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
  rw [matrixCoefficientSubmodule_eq_isotypicComponent,
    matrixCoefficientSubmodule_eq_isotypicComponent,
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
  simp_rw [matrixCoefficientSubmodule_eq_isotypicComponent,
    ← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff]
  exact hind i

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

end Ring

section Field

universe u v w

variable {k : Type u} [Field k]
  {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
  {M : Type w} [AddCommGroup M] [Module k M] [Comodule k C M]

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

/-- The coefficient space of a simple comodule (in any universe) belongs to the family of simple
coefficient spaces. -/
@[simp]
theorem matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules
    [IsSimpleOrder (Subcomodule k C M)] :
    matrixCoefficientSubmodule (R := k) (C := C) (M := M) ∈ simpleCoefficientSubmodules k C := by
  -- Realize `M : Type w` inside the regular module `C : Type v` as a simple `D`-submodule `T`
  -- with the same `D`-isotypic component, then convert `T` into a simple subcomodule `S` of `C`
  -- in universe `v`. Since `S` and `T` are `D`-linearly equivalent, `M` and `S` share the same
  -- `D`-isotypic component and therefore the same matrix-coefficient space.
  let D := WithConv (C →ₗ[k] k)
  obtain ⟨T, hT, hTeq⟩ :=
    isotypicComponent_convolution_mem_isotypicComponents (k := k) (C := C) (M := M)
  let S : Subcomodule k C C := T.toSubcomodule
  have : IsSimpleModule D S := S.isSimpleModule_convolution_iff_isAtom.mpr <| by
    simpa [S] using ((Subcomodule.convolutionSubmoduleOrderIso (R := k) (C := C)
      (M := C)).symm.isAtom_iff T).mpr (isSimpleModule_iff_isAtom.mp hT)
  have : IsSimpleOrder (Subcomodule k C S) := isSimpleModule_convolution_iff.mp inferInstance
  let g : S →ₗ[D] T := S.subtype.toConvolutionLinearMap.codRestrict T fun x ↦ by
    simpa using (T.mem_toSubcomodule x.val).mp x.property
  have hg : Function.Bijective g :=
    ⟨fun x y h ↦ Subtype.ext (by simpa [g] using congrArg Subtype.val h),
      fun y ↦ ⟨⟨y.val, (T.mem_toSubcomodule y.val).mpr y.property⟩, Subtype.ext (by simp [g])⟩⟩
  rw [matrixCoefficientSubmodule_eq_isotypicComponent (M := M), hTeq,
    ← (LinearEquiv.ofBijective g hg).isotypicComponent_eq,
    ← matrixCoefficientSubmodule_eq_isotypicComponent (M := S)]
  exact ⟨ComoduleCat.of k C S, inferInstance, rfl⟩

/-- A simple coefficient space is finite-dimensional. -/
theorem finite_of_mem_simpleCoefficientSubmodules {P : Submodule k C}
    (hP : P ∈ simpleCoefficientSubmodules k C) : Module.Finite k P := by
  obtain ⟨M, hM, rfl⟩ := mem_simpleCoefficientSubmodules.mp hP
  have := hM
  have : Module.Finite k M := finite_of_isSimpleOrder (C := C)
  infer_instance

/-- Zero is not a simple coefficient space. -/
@[simp]
theorem bot_notMem_simpleCoefficientSubmodules :
    (⊥ : Submodule k C) ∉ simpleCoefficientSubmodules k C := by
  rintro ⟨M, hM, h⟩
  have : IsSimpleModule (WithConv (C →ₗ[k] k)) M := isSimpleModule_convolution_iff.mpr hM
  have := IsSimpleModule.nontrivial (WithConv (C →ₗ[k] k)) M
  exact matrixCoefficientSubmodule_ne_bot (R := k) (C := C) (M := M) h.symm

/-- Distinct simple coefficient spaces are independent. This holds over arbitrary fields,
and does not require that the coalgebra be linearly reductive. -/
theorem sSupIndep_simpleCoefficientSubmodules :
    sSupIndep (simpleCoefficientSubmodules k C) := by
  let D := WithConv (C →ₗ[k] k)
  have hind : iSupIndep fun P : isotypicComponents D C ↦ P.val.restrictScalars k := fun P ↦ by
    simpa only [← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff]
      using (sSupIndep_iff _).mp (sSupIndep_isotypicComponents D C) P
  apply hind.sSupIndep_range.mono
  rintro P ⟨M, hM, rfl⟩
  let := hM
  exact ⟨⟨_, isotypicComponent_convolution_mem_isotypicComponents (C := C) (M := M)⟩,
    matrixCoefficientSubmodule_eq_isotypicComponent.symm⟩

/-- A coalgebra over a field that is spanned by its distinct simple coefficient spaces is their
internal direct sum. -/
theorem isInternal_of_sSup_simpleCoefficientSubmodules_eq_top
    (hspan : sSup (simpleCoefficientSubmodules k C) = ⊤) :
    DirectSum.IsInternal (fun P : simpleCoefficientSubmodules k C ↦ (P.val : Submodule k C)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (sSupIndep_iff _).mp sSupIndep_simpleCoefficientSubmodules
  · rwa [← sSup_eq_iSup']

/-- Over any bialgebra `A` over a field `k`, the line `Submodule.span k {1}` belongs to
`simpleCoefficientSubmodules k A` as the coefficient space of the trivial rank-one comodule. -/
theorem span_singleton_one_mem_simpleCoefficientSubmodules {A : Type v} [Ring A] [Bialgebra k A] :
    Submodule.span k ({1} : Set A) ∈ simpleCoefficientSubmodules k A := by
  let _ : Comodule k A k := Comodule.trivial
  have : Nontrivial (Subcomodule k A k) :=
    ⟨⟨⊥, ⊤, fun h ↦ one_ne_zero (Subcomodule.mem_bot.mp (h.symm ▸ Subcomodule.mem_top (1 : k)))⟩⟩
  have : IsSimpleOrder (Subcomodule k A k) :=
    ⟨fun S ↦ (eq_bot_or_eq_top S.toSubmodule).imp
      Subcomodule.toSubmodule_eq_bot.mp Subcomodule.toSubmodule_eq_top.mp⟩
  rw [← trivial_rankOne_matrixCoefficientSubmodule_eq_span_singleton_one (R := k) (C := A)]
  exact matrixCoefficientSubmodule_mem_simpleCoefficientSubmodules

end Field

end TauCeti.Comodule
