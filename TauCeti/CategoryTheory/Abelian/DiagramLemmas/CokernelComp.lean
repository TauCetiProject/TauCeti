/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import TauCeti.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Quotients by a composite of monomorphisms

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` in an abelian category with `g` a
monomorphism, the sequence of cokernels

`0 ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`

is short exact.  For submodules `X ⊆ Y ⊆ Z` this is the third isomorphism theorem, and for
singular chain complexes it is what produces the long exact homology sequence of a triple of
topological spaces.

The two short exactness statements below differ only in how the three cokernels are presented:
`TauCeti.shortExact_cokernel_comp` uses the chosen cokernels, while
`TauCeti.shortExact_of_isColimit_cokernelCofork` takes arbitrary colimit cokernel coforks, which
is what a consumer whose quotients are produced by some other colimit construction needs.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] {X Y Z : C}

/-- For composable morphisms `f` and `g` in an abelian category with `g` a monomorphism, the
sequence `coker f ⟶ coker (f ≫ g) ⟶ coker g` is short exact. -/
theorem shortExact_cokernel_comp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (ShortComplex.mk (cokernel.map f (f ≫ g) (𝟙 X) g (by simp))
      (cokernel.map (f ≫ g) g f (𝟙 Z) (by simp))
      ((kernelCokernelCompSequence_exact f g).toIsComplex.zero' 3 4 5)).ShortExact where
  -- The three objects and two maps here are the last three terms of
  -- `CategoryTheory.kernelCokernelCompSequence f g`, so the exactness and the epimorphism
  -- below are read off from that sequence directly.
  exact := (kernelCokernelCompSequence_exact f g).exact' 3 4 5
  mono_f := by
    -- The preceding map in that sequence is the connecting morphism out of `ker g`, which
    -- vanishes because `g` is a monomorphism; exactness there then forces `mono`.
    have hδ : kernelCokernelCompSequence.δ f g = 0 := by
      rw [kernelCokernelCompSequence.δ_fac, kernel.ι_of_mono, zero_comp, neg_zero]
    exact (ShortComplex.exact_iff_mono _ hδ).mp
      ((kernelCokernelCompSequence_exact f g).exact' 2 3 4)
  epi_g := inferInstanceAs (Epi ((kernelCokernelCompSequence f g).map' 4 5))

variable {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} {c₁ : CokernelCofork f} {c₂ : CokernelCofork k}
  {c₃ : CokernelCofork g} {u : c₁.pt ⟶ c₂.pt} {v : c₂.pt ⟶ c₃.pt}

/-- The version of `TauCeti.shortExact_cokernel_comp` for arbitrary colimit cokernel coforks: if
`c₁`, `c₂` and `c₃` exhibit cokernels of `f`, of `f ≫ g` and of `g`, and `u` and `v` are the maps
induced between their points, then `c₁.pt ⟶ c₂.pt ⟶ c₃.pt` is short exact.  The monomorphism
hypothesis on `g` is explicit because the three cokernels typically present `g` in forms that
agree only up to unfolding. -/
theorem shortExact_of_isColimit_cokernelCofork (hk : f ≫ g = k) (hg : Mono g)
    (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (h₃ : IsColimit c₃)
    (hu : Cofork.π c₁ ≫ u = g ≫ Cofork.π c₂) (hv : Cofork.π c₂ ≫ v = Cofork.π c₃) :
    (ShortComplex.mk u v (comp_eq_zero_of_epi (Cofork.IsColimit.epi h₁)
      (CokernelCofork.condition c₃) hu hv)).ShortExact := by
  subst hk
  have := hg
  have h₁' : cokernel.π f ≫ (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) h₁).hom
      = Cofork.π c₁ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _) _ WalkingParallelPair.one
  have h₂' : cokernel.π (f ≫ g) ≫
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (f ≫ g)) h₂).hom = Cofork.π c₂ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _) _ WalkingParallelPair.one
  have h₃' : cokernel.π g ≫ (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel g) h₃).hom
      = Cofork.π c₃ :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _) _ WalkingParallelPair.one
  refine ShortComplex.shortExact_of_iso (ShortComplex.isoMk
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) h₁)
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (f ≫ g)) h₂)
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel g) h₃) ?_ ?_)
    (shortExact_cokernel_comp f g)
  · rw [← cancel_epi (cokernel.π f), ← Category.assoc, h₁', hu]
    simp [← h₂']
  · rw [← cancel_epi (cokernel.π (f ≫ g)), ← Category.assoc, h₂', hv]
    simp [← h₃']

end TauCeti
