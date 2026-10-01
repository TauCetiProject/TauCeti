/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Split maps between coproducts

## Reindexing a coproduct along an injection is split

Let `X : I → C` be a family of objects of a category with zero morphisms and coproducts, and let
`f : J → I` be injective.  Reindexing along `f` gives a map `∐ (X ∘ f) ⟶ ∐ X`, and this file
shows that it is a split monomorphism: the retraction sends the summand indexed by `f j` back to
the one indexed by `j`, and kills the summands indexed outside the range of `f`.

Mathlib's `CategoryTheory.Limits.MonoCoprod.mono_map'_of_injective` proves the same map is a
monomorphism in a category satisfying `MonoCoprod`; the splitting below needs zero morphisms
instead, and is the stronger statement in the situations where both apply.

Chain complexes built as coproducts over a set of simplices, singular or simplicial, get their
degreewise splittings this way: for a pair of spaces the singular simplices of the subspace form a
subset of those of the ambient space, so the short exact sequence of chains of the pair is split in
each degree, and therefore stays exact after applying a contravariant `Hom(-, M)`.

## The kernel of the codiagonal

Let `R` be an object of a preadditive category with a zero object, and let `ι` be a type with a
distinguished element `i₀`.  The codiagonal `Sigma.desc (fun _ ↦ 𝟙 R) : ∐ (fun _ : ι ↦ R) ⟶ R`,
the identity on every summand, is a split epimorphism with section the inclusion of the summand
`i₀`, and its kernel is the coproduct of the summands indexed by `i ≠ i₀`, embedded through the
differences `ι_i - ι_{i₀}` of coproduct inclusions (`TauCeti.sigmaιSubι`).  The short complex
`∐_{i ≠ i₀} R ⟶ ∐_ι R ⟶ R` is split (`TauCeti.sigmaDescIdSplitting`), which identifies the kernel
of the codiagonal with `∐_{i ≠ i₀} R` (`TauCeti.kernelSigmaDescIdIso`).

Reduced homology in degree zero is the kernel of an augmentation of this form, so this identifies
it with a coproduct indexed by the path components other than that of a chosen basepoint.
-/

public section

open CategoryTheory Limits

universe w

namespace TauCeti

section Reindex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasCoproducts.{w} C]

open scoped Classical in
/-- Reindexing a coproduct along an injective map of index types is a split monomorphism. -/
instance isSplitMono_sigmaMap' {I J : Type w} (X : I → C) (f : J ⟶ I) [Mono f] :
    IsSplitMono (Sigma.map' f fun j ↦ 𝟙 ((X ∘ f) j)) :=
  IsSplitMono.mk'
    { retraction := Sigma.desc fun i ↦
        if h : i ∈ Set.range f then
          eqToHom (congrArg X h.choose_spec).symm ≫ Sigma.ι (X ∘ f) h.choose
        else 0
      id := by
        refine Sigma.hom_ext _ _ fun j ↦ ?_
        have h : f j ∈ Set.range f := ⟨j, rfl⟩
        have hj : h.choose = j := (mono_iff_injective f).1 ‹_› h.choose_spec
        rw [← Category.assoc, Sigma.ι_comp_map', Category.id_comp, Sigma.ι_comp_desc,
          dite_eq_left h, Category.comp_id]
        exact Sigma.eqToHom_comp_ι (X ∘ f) hj }

end Reindex

noncomputable section Codiagonal

variable {C : Type*} [Category* C] [Preadditive C] [HasCoproducts.{w} C] (R : C) {ι : Type w}
  (i₀ : ι)

/-- The morphism `∐_{i ≠ i₀} R ⟶ ∐_ι R` whose component at `i` is the difference `ι_i - ι_{i₀}`
of coproduct inclusions.  It is a kernel of the codiagonal `∐_ι R ⟶ R`
(`TauCeti.isKernelSigmaιSubι`). -/
def sigmaιSubι : (∐ fun _ : {i // i ≠ i₀} ↦ R) ⟶ ∐ fun _ : ι ↦ R :=
  Sigma.desc fun i ↦ Sigma.ι (fun _ : ι ↦ R) i.1 - Sigma.ι (fun _ : ι ↦ R) i₀

@[reassoc (attr := simp)]
lemma ι_sigmaιSubι (i : {i // i ≠ i₀}) :
    Sigma.ι (fun _ : {i // i ≠ i₀} ↦ R) i ≫ sigmaιSubι R i₀ =
      Sigma.ι (fun _ : ι ↦ R) i.1 - Sigma.ι (fun _ : ι ↦ R) i₀ :=
  Sigma.ι_comp_desc _ _

/-- The differences of coproduct inclusions are killed by the codiagonal. -/
@[reassoc (attr := simp)]
lemma sigmaιSubι_desc_id : sigmaιSubι R i₀ ≫ Sigma.desc (fun _ ↦ 𝟙 R) = 0 := by
  ext i
  simp [Preadditive.sub_comp]

open scoped Classical in
/-- The retraction of `TauCeti.sigmaιSubι`: the identity on the summands indexed by `i ≠ i₀` and
zero on the summand indexed by `i₀`. -/
def sigmaιSubιRetraction : (∐ fun _ : ι ↦ R) ⟶ ∐ fun _ : {i // i ≠ i₀} ↦ R :=
  Sigma.desc fun i ↦ if h : i = i₀ then 0 else Sigma.ι (fun _ : {i // i ≠ i₀} ↦ R) ⟨i, h⟩

@[reassoc (attr := simp)]
lemma ι_sigmaιSubιRetraction_of_ne {i : ι} (h : i ≠ i₀) :
    Sigma.ι (fun _ : ι ↦ R) i ≫ sigmaιSubιRetraction R i₀ =
      Sigma.ι (fun _ : {i // i ≠ i₀} ↦ R) ⟨i, h⟩ := by
  simp [sigmaιSubιRetraction, h]

@[reassoc (attr := simp)]
lemma ι_sigmaιSubιRetraction_self :
    Sigma.ι (fun _ : ι ↦ R) i₀ ≫ sigmaιSubιRetraction R i₀ = 0 := by
  simp [sigmaιSubιRetraction]

/-- The short complex `∐_{i ≠ i₀} R ⟶ ∐_ι R ⟶ R` formed by the differences of coproduct
inclusions and the codiagonal. -/
abbrev sigmaDescIdShortComplex : ShortComplex C :=
  ShortComplex.mk (sigmaιSubι R i₀) (Sigma.desc fun _ ↦ 𝟙 R) (sigmaιSubι_desc_id R i₀)

/-- The short complex `∐_{i ≠ i₀} R ⟶ ∐_ι R ⟶ R` is split: the inclusion of the summand `i₀`
sections the codiagonal, and `TauCeti.sigmaιSubιRetraction` retracts the differences. -/
def sigmaDescIdSplitting : (sigmaDescIdShortComplex R i₀).Splitting where
  r := sigmaιSubιRetraction R i₀
  s := Sigma.ι (fun _ : ι ↦ R) i₀
  f_r := by
    ext ⟨i, hi⟩
    simp [Preadditive.sub_comp, hi]
  s_g := by simp
  id := by
    ext i
    by_cases h : i = i₀
    · subst h
      simp
    · simp [Preadditive.comp_add, h]

variable [HasZeroObject C]

/-- The differences of coproduct inclusions form a kernel of the codiagonal. -/
def isKernelSigmaιSubι :
    IsLimit (KernelFork.ofι (sigmaιSubι R i₀) (sigmaιSubι_desc_id R i₀)) :=
  (sigmaDescIdSplitting R i₀).fIsKernel

/-- The kernel of the codiagonal `∐_ι R ⟶ R` is the coproduct of the copies of `R` indexed by
`i ≠ i₀`. -/
def kernelSigmaDescIdIso [HasKernel (Sigma.desc fun _ : ι ↦ 𝟙 R)] :
    kernel (Sigma.desc fun _ : ι ↦ 𝟙 R) ≅ ∐ fun _ : {i // i ≠ i₀} ↦ R :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel _) (isKernelSigmaιSubι R i₀)

@[reassoc (attr := simp)]
lemma kernelSigmaDescIdIso_inv_ι [HasKernel (Sigma.desc fun _ : ι ↦ 𝟙 R)] :
    (kernelSigmaDescIdIso R i₀).inv ≫ kernel.ι (Sigma.desc fun _ : ι ↦ 𝟙 R) =
      sigmaιSubι R i₀ :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

end Codiagonal

end TauCeti
