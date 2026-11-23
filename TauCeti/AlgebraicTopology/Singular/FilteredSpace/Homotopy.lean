/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import TauCeti.Algebra.Homology.Embedding.HomotopyEquiv
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Homotopy
public import TauCeti.AlgebraicTopology.Singular.FilteredSpace.Basic
import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance

/-!
# Homotopies of maps of filtered spaces

Let `X : ℤ → Set Y` and `X' : ℤ → Set Y'` be filtrations of two spaces, and let `H` be a homotopy
between maps `g₀ g₁ : Y ⟶ Y'` which carries `X q` into `X' (q + s)` at every time, for a fixed
integer `s`. The homotopy invariance of singular chains gives a chain homotopy from `g₀` to `g₁`
on singular chains (`TopCat.Homotopy.singularChainComplexFunctorObjMap`), and this chain
homotopy carries the singular chains of each `X q` into those of `X' (q + s)`: reindexed as
cochain complexes, it raises the filtrations of `TauCeti.chainFiltration` by at most `s`
(`TopCat.Homotopy.isFiltered_extend_singularChainComplexFunctorObjMap`). The reason is
naturality: on the chains of `X q` the chain homotopy is that of the restriction of `H` to a
homotopy of maps `X q ⟶ X' (q + s)`.

For `s = 0`, that is, for a homotopy through maps of filtered spaces, this makes `g₀` and `g₁`
induce the same morphism of spectral sequences of filtered spaces on every page
(`TauCeti.filteredSpaceSpectralSequenceMap_eq_of_homotopy`), so a homotopy equivalence of
filtered spaces whose two homotopies preserve the filtrations induces an isomorphism of spectral
sequences (`TauCeti.isIso_filteredSpaceSpectralSequenceMap_of_homotopy`). In particular, for maps
over a base `B` and filtrations by the preimages of a filtration of `B`, such as the skeletal
filtrations giving Serre spectral sequences, every homotopy through maps over `B` preserves the
filtrations (`TauCeti.filteredSpaceSpectralSequenceMap_preimage_eq_of_homotopy`).

Homotopies of cellular maps between CW complexes typically raise skeleta by one, so `s = 1` is
the case that compares the spectral sequences of different cellular models, from the second page
on.

## Main results

* `TopCat.Homotopy.isFiltered_extend_singularChainComplexFunctorObjMap`: the singular chain
  homotopy of a homotopy carrying `X q` into `X' (q + s)` raises the filtrations by `s`.
* `TauCeti.filteredSpaceSpectralSequenceMap_eq_of_homotopy`: maps of filtered spaces that are
  homotopic through a homotopy keeping each `X q` inside `X' q` induce the same morphism of
  spectral sequences.
* `TauCeti.isIso_filteredSpaceSpectralSequenceMap_of_homotopy`: a homotopy equivalence of filtered
  spaces whose two homotopies preserve the filtrations induces an isomorphism of spectral
  sequences.
* `TauCeti.filteredSpaceSpectralSequenceMap_preimage_eq_of_homotopy`: homotopic maps over a base
  induce the same morphism of the spectral sequences of preimage filtrations.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, Theorem 2.10,
  the prism operator and its naturality.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2 and Theorem 5.2, the naturality of the spectral sequence of a filtered space.
-/

public section

noncomputable section

open CategoryTheory Limits HomologicalComplex AlgebraicTopology Set

universe w v u

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCoproducts.{w} A] (R : A)
  {Y Y' : TopCat.{w}} {g₀ g₁ : Y ⟶ Y'}

namespace TopCat.Homotopy

/-- **The singular chain homotopy of a filtration-raising homotopy is filtered.** Let `H` be a
homotopy between maps `g₀ g₁ : Y ⟶ Y'` which carries `X q` into `X' (q + s)` at every time, for
every `q`. Then the chain homotopy from `g₀` to `g₁` that `H` induces on singular chains, reindexed
as cochain complexes, carries the stage `q` of the filtration of the chains of `Y` by the chains of
the `X q` into the stage `q + s` of the filtration of the chains of `Y'` by the chains of the
`X' q`. -/
theorem isFiltered_extend_singularChainComplexFunctorObjMap (H : TopCat.Homotopy g₀ g₁)
    {X : ℤ → Set Y} {X' : ℤ → Set Y'} (s : ℤ)
    (hH : ∀ q τ x, x ∈ X q → H (τ, x) ∈ X' (q + s)) :
    ((H.singularChainComplexFunctorObjMap R).extend ComplexShape.embeddingDownNat).IsFiltered
      (TauCeti.chainFiltration ((singularChainComplexFunctor A).obj R) X)
      (fun q ↦ TauCeti.chainFiltration ((singularChainComplexFunctor A).obj R) X' (q + s)) := by
  refine Homotopy.isFiltered_iff.2 fun q i j ↦ ?_
  let F := (singularChainComplexFunctor A).obj R
  -- The restriction `K` of `H` to a homotopy of maps `X q ⟶ X' (q + s)`, whose singular chain
  -- homotopy is that of `H` on the chains of `X q`, by naturality.
  obtain ⟨g₀', g₁', K, hK⟩ : ∃ (g₀' g₁' : (TopPair.ofSubset (X q)).snd ⟶
      (TopPair.ofSubset (X' (q + s))).snd) (K : TopCat.Homotopy g₀' g₁'), ∀ i j : ℕ,
        (F.map (TopPair.ofSubset (X q)).map).f i ≫ (H.singularChainComplexFunctorObjMap R).hom i j =
          (K.singularChainComplexFunctorObjMap R).hom i j ≫
            (F.map (TopPair.ofSubset (X' (q + s))).map).f j := by
    let K : ContinuousMap.Homotopy
        (⟨fun x : X q ↦ ⟨H (0, x), hH q 0 x x.property⟩, by fun_prop⟩ : C(X q, X' (q + s)))
        ⟨fun x : X q ↦ ⟨H (1, x), hH q 1 x x.property⟩, by fun_prop⟩ :=
      { toFun x := ⟨H (x.1, x.2), hH q x.1 x.2 x.2.property⟩
        continuous_toFun := by fun_prop
        map_zero_left _ := rfl
        map_one_left _ := rfl }
    refine ⟨TopCat.ofHom _, TopCat.ofHom _, K, fun i j ↦
      singularChainComplexFunctorObjMap_hom_comm (f := TopCat.ofHom _) (g := TopCat.ofHom _) K H
        ?_ R i j⟩
    -- Both sides send `(x, t)` to `H (t, x)`, by definition of `K` and of the inclusions.
    ext x
    rfl
  -- On the chains of `X q`, the chain homotopy of `H` is that of its restriction `K`.
  have h : (TauCeti.chainFiltrationι F X q).f i ≫
        ((H.singularChainComplexFunctorObjMap R).extend ComplexShape.embeddingDownNat).hom i j =
      ((K.singularChainComplexFunctorObjMap R).extend ComplexShape.embeddingDownNat).hom i j ≫
        (TauCeti.chainFiltrationι F X' (q + s)).f j := by
    rw [TauCeti.chainFiltrationι_def, TauCeti.chainFiltrationι_def]
    exact Homotopy.extend_hom_comm _ _ _ _ _ hK i j
  refine ⟨(TauCeti.chainFiltrationIso F X q).hom.f i ≫
    ((K.singularChainComplexFunctorObjMap R).extend ComplexShape.embeddingDownNat).hom i j ≫
      (TauCeti.chainFiltrationIso F X' (q + s)).inv.f j, ?_⟩
  simpa [← TauCeti.chainFiltrationIso_hom_comp_chainFiltrationι] using
    congrArg ((TauCeti.chainFiltrationIso F X q).hom.f i ≫ ·) h.symm

end TopCat.Homotopy

namespace TauCeti

variable {X : ℤ → Set Y} {X' : ℤ → Set Y'} (hX : Monotone X) (hX' : Monotone X')

/-- **Maps homotopic through filtration-preserving homotopies induce the same morphism of
spectral sequences.** If `H` is a homotopy between maps `g₀ g₁ : Y ⟶ Y'` which carries each `X q`
into `X' q` at every time, then `g₀` and `g₁` induce the same morphism from the spectral sequence
of the filtration of `Y` by the `X q` to that of the filtration of `Y'` by the `X' q`, on every
page. -/
theorem filteredSpaceSpectralSequenceMap_eq_of_homotopy (H : TopCat.Homotopy g₀ g₁)
    (hH : ∀ q τ x, x ∈ X q → H (τ, x) ∈ X' q) (hg₀ : ∀ q, MapsTo g₀ (X q) (X' q))
    (hg₁ : ∀ q, MapsTo g₁ (X q) (X' q)) :
    filteredSpaceSpectralSequenceMap R hX hX' g₀ hg₀ =
      filteredSpaceSpectralSequenceMap R hX hX' g₁ hg₁ := by
  have hH' := H.isFiltered_extend_singularChainComplexFunctorObjMap R 0
    (by simpa only [add_zero] using hH)
  simp only [add_zero] at hH'
  rw [filteredSpaceSpectralSequenceMap_def, filteredSpaceSpectralSequenceMap_def,
    chainFiltrationMap_def, chainFiltrationMap_def]
  -- The chain maps of `chainFiltrationMap` are the singular chain maps of `g₀` and `g₁`, composed
  -- with the identity natural transformation of singular chains.
  simp only [NatTrans.id_app, Category.comp_id]
  rw [CochainComplex.spectralObjectMap_filtrationFunctorMap_eq_of_homotopy
    ((H.singularChainComplexFunctorObjMap R).extend ComplexShape.embeddingDownNat) hH']

/-- **A homotopy equivalence of filtered spaces through filtration-preserving homotopies induces
an isomorphism of spectral sequences.** If `g : Y ⟶ Y'` carries each `X q` into `X' q`,
`g' : Y' ⟶ Y` carries each `X' q` into `X q`, and the composites `g ≫ g'` and `g' ≫ g` are
homotopic to the identities through homotopies which keep each `X q`, respectively each `X' q`,
inside itself at every time, then `g` induces an isomorphism of spectral sequences of filtered
spaces, on every page. -/
theorem isIso_filteredSpaceSpectralSequenceMap_of_homotopy (g : Y ⟶ Y')
    (hg : ∀ q, MapsTo g (X q) (X' q)) (g' : Y' ⟶ Y) (hg' : ∀ q, MapsTo g' (X' q) (X q))
    (H : TopCat.Homotopy (g ≫ g') (𝟙 Y)) (hH : ∀ q τ x, x ∈ X q → H (τ, x) ∈ X q)
    (H' : TopCat.Homotopy (g' ≫ g) (𝟙 Y')) (hH' : ∀ q τ x, x ∈ X' q → H' (τ, x) ∈ X' q) :
    IsIso (filteredSpaceSpectralSequenceMap R hX hX' g hg) :=
  ⟨filteredSpaceSpectralSequenceMap R hX' hX g' hg', by
    rw [← filteredSpaceSpectralSequenceMap_comp R hX hX' hX g hg g' hg'
        fun q ↦ (hg' q).comp (hg q),
      filteredSpaceSpectralSequenceMap_eq_of_homotopy R hX hX H hH _ fun _ _ hx ↦ hx]
    exact filteredSpaceSpectralSequenceMap_id R hX _, by
    rw [← filteredSpaceSpectralSequenceMap_comp R hX' hX hX' g' hg' g hg
        fun q ↦ (hg q).comp (hg' q),
      filteredSpaceSpectralSequenceMap_eq_of_homotopy R hX' hX' H' hH' _ fun _ _ hx ↦ hx]
    exact filteredSpaceSpectralSequenceMap_id R hX' _⟩

/-- **Homotopic maps over a base induce the same morphism of spectral sequences.** Let
`p : E ⟶ B` and `p' : E' ⟶ B` be maps to a common base, `S : ℤ → Set B` a family of subsets of `B`,
and filter `E` and `E'` by the preimages of the `S q`. A homotopy between maps `f₀ f₁ : E ⟶ E'`
through maps over `B` carries each preimage `p⁻¹(S q)` into `p'⁻¹(S q)`, so `f₀` and `f₁` induce
the same morphism of spectral sequences on every page. For the preimages of the skeleta of a CW
complex in `B` (`TauCeti.preimageSkeleton`) these are the spectral sequences of the skeletal
filtrations, the Serre spectral sequences when `p` and `p'` are Serre fibrations. -/
theorem filteredSpaceSpectralSequenceMap_preimage_eq_of_homotopy {E E' B : TopCat.{w}}
    (p : E ⟶ B) (p' : E' ⟶ B) {S : ℤ → Set B} (hpS : Monotone fun q ↦ p ⁻¹' S q)
    (hpS' : Monotone fun q ↦ p' ⁻¹' S q) {f₀ f₁ : E ⟶ E'} (H : TopCat.Homotopy f₀ f₁)
    (hH : ∀ τ e, p' (H (τ, e)) = p e) (hf₀ : ∀ q, MapsTo f₀ (p ⁻¹' S q) (p' ⁻¹' S q))
    (hf₁ : ∀ q, MapsTo f₁ (p ⁻¹' S q) (p' ⁻¹' S q)) :
    filteredSpaceSpectralSequenceMap R hpS hpS' f₀ hf₀ =
      filteredSpaceSpectralSequenceMap R hpS hpS' f₁ hf₁ :=
  filteredSpaceSpectralSequenceMap_eq_of_homotopy R hpS hpS' H
    (fun q τ e he ↦ by simpa only [mem_preimage, hH] using he) hf₀ hf₁

end TauCeti
