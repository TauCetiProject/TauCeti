/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.IsIso
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
import TauCeti.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Quasi-isomorphisms of filtered complexes

Let `α : F ⟶ G` be a natural transformation of functors `ι ⥤ CochainComplex C ℤ` all of whose
components are quasi-isomorphisms. On `H^n(f)`, the induced morphism of spectral objects is the
map in cohomology of the morphism of mapping cones of `F.map f` and `G.map f`, which is a
quasi-isomorphism (`CochainComplex.mappingCone.quasiIso_map`). So `α` induces an isomorphism of
spectral objects (`CochainComplex.isIso_spectralObjectMap_of_quasiIso`), hence of spectral
sequences.

For a morphism `f : K ⟶ L` of complexes carrying an increasing filtration `F` of `K` into an
increasing filtration `G` of `L`, the components of the induced morphism of filtration functors
at `⊥` and `⊤` are the zero map and, up to isomorphism, `f` itself. So if `f` and its
restrictions `F n ⟶ G n` are quasi-isomorphisms, all components are
(`CochainComplex.quasiIso_filtrationFunctorMap_app`), and so the spectral objects of the two
filtrations are isomorphic. This holds without any boundedness or exhaustiveness assumption on the
filtrations.

## Main results

* `CochainComplex.isIso_spectralObjectMap_of_quasiIso`: natural quasi-isomorphisms induce an
  isomorphism of spectral objects.
* `CochainComplex.quasiIso_filtrationFunctorMap_app`: the components of the morphism of
  filtration functors of a filtered quasi-isomorphism are quasi-isomorphisms.

## References

* J.-L. Verdier, *Des catégories dérivées des catégories abéliennes*, Astérisque 239 (1996), II.4.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 2.2.
-/

public section

open CategoryTheory Limits ComposableArrows

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

section

variable {ι : Type*} [Category* ι] {F G : ι ⥤ CochainComplex C ℤ}

/-- **Natural quasi-isomorphisms induce an isomorphism of spectral objects.** If every component
of `α : F ⟶ G` is a quasi-isomorphism, then `spectralObjectMap α` is an isomorphism. -/
theorem isIso_spectralObjectMap_of_quasiIso (α : F ⟶ G) [∀ i, QuasiIso (α.app i)] :
    IsIso (spectralObjectMap α) := by
  refine Abelian.SpectralObject.isIso_of_isIso_hom_app _ fun n D ↦ ?_
  obtain ⟨i, j, f, rfl⟩ := ComposableArrows.mk₁_surjective D
  rw [(Iso.eq_comp_inv _).2 (spectralObjectMap_hom_app_hIso α f n)]
  infer_instance

end

variable {K L : CochainComplex C ℤ} {F : ℤ → Subobject K} (hF : Monotone F)
  {G : ℤ → Subobject L} (hG : Monotone G)

/-- **The components of the morphism of filtration functors of a filtered quasi-isomorphism are
quasi-isomorphisms.** If `f : K ⟶ L` is a quasi-isomorphism carrying each `F n` into `G n` by a
quasi-isomorphism, then the component of `filtrationFunctorMap hF hG f hf` at every `a : EInt`
is a quasi-isomorphism: at `⊥` both objects are zero, and at `⊤` it is `f`. -/
theorem quasiIso_filtrationFunctorMap_app (f : K ⟶ L) (hf : ∀ n, (G n).Factors ((F n).arrow ≫ f))
    [QuasiIso f] (h : ∀ n : ℤ, QuasiIso ((filtrationFunctorMap hF hG f hf).app n)) (a : EInt) :
    QuasiIso ((filtrationFunctorMap hF hG f hf).app a) := by
  induction a using WithBotTop.rec with
  | bot =>
    have hz {M : CochainComplex C ℤ} {P : ℤ → Subobject M} (hP : Monotone P) :
        IsZero ((filtrationFunctor P hP).obj ⊥) := by
      rw [filtrationFunctor_obj, filtrationEInt_bot]
      exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero
    have : IsIso ((filtrationFunctorMap hF hG f hf).app ⊥) :=
      ⟨0, (hz hF).eq_of_src _ _, (hz hG).eq_of_src _ _⟩
    infer_instance
  | coe n => exact h n
  | top =>
    -- Composed with the isomorphism from `G_⊤` to `L`, the component at `⊤` is the composite of
    -- the isomorphism from `F_⊤` to `K` with `f`.
    have e := filtrationFunctorMap_app_comp (hF := hF) (hG := hG) f hf ⊤
    have : IsIso (filtrationEInt F ⊤).arrow := by rw [filtrationEInt_top]; infer_instance
    have : IsIso (filtrationEInt G ⊤).arrow := by rw [filtrationEInt_top]; infer_instance
    rw [← quasiIso_iff_comp_right _ ((filtrationFunctorObjIso G hG ⊤).hom ≫
      (filtrationEInt G ⊤).arrow), e, ← Category.assoc]
    infer_instance

end CochainComplex
