/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Detection
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.FinitePresentation
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Finiteness on the pieces of formal glueing

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, where `I` has a finite
generating set `G`. A module is finitely generated (respectively finitely presented) if and only
if its scalar extensions to `S` and to every `R[1/g]`, for `g ∈ G`, have that property.
No Noetherian hypothesis is needed.

This detects finiteness of a reconstructed module in formal glueing, in particular when passing
from an algebra over a completion and an algebra on the complementary open set to a finite
algebra over the original ring. It does not assert the existence of that reconstruction.

## References

* The Stacks Project, Remark 15.91.20 (05EU), preservation of finiteness in formal glueing.
* The Stacks Project, Proposition 15.91.16 (05ER), formal glueing of modules.
-/

public section

open TensorProduct Function

namespace TauCeti

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
  [AddCommGroup M] [Module R M] {G : Finset R}

/-- Finite generation is detected on the formal-glueing pieces. The tensor products with
`Localization.Away g` are the principal localizations of the module. -/
theorem finite_iff_baseChange_and_localized
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.Finite R M ↔ Module.Finite S (S ⊗[R] M) ∧
      ∀ g ∈ G, Module.Finite (Localization.Away g) (Localization.Away g ⊗[R] M) := by
  classical
  refine ⟨fun _ ↦ ⟨inferInstance, fun _ _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  obtain ⟨P, hP, hPS⟩ := Submodule.exists_fg_baseChange_eq_top (R := R) (A := S) (M := M)
  have hfg (g : G) : ∃ Q : Submodule R M, Q.FG ∧ Q.baseChange (Localization.Away g.1) = ⊤ := by
    have := hloc g.1 g.2
    exact Submodule.exists_fg_baseChange_eq_top
  choose Q hQ hQg using hfg
  let N := P ⊔ ⨆ g : G, Q g
  have hN : N.FG := hP.sup (Submodule.fg_iSup _ hQ)
  have hNS : N.baseChange S = ⊤ := top_unique <| hPS ▸ Submodule.baseChange_mono S le_sup_left
  have hNg (g : G) : N.baseChange (Localization.Away g.1) = ⊤ :=
    top_unique <| hQg g ▸ Submodule.baseChange_mono _ ((le_iSup Q g).trans le_sup_right)
  have : Subsingleton (S ⊗[R] (M ⧸ N)) :=
    (Submodule.baseChange_eq_top_iff_subsingleton S N).mp hNS
  have : Subsingleton (M ⧸ N) := subsingleton_of_baseChange_and_localized hG fun g hg ↦ by
    have : Subsingleton (Localization.Away g ⊗[R] (M ⧸ N)) :=
      (Submodule.baseChange_eq_top_iff_subsingleton _ N).mp (hNg ⟨g, hg⟩)
    exact (LocalizedModule.isBaseChange (.powers g) (M ⧸ N)).equiv.symm.subsingleton
  exact ⟨Submodule.Quotient.subsingleton_iff.mp this ▸ hN⟩

/-- Finite presentation is detected on the formal-glueing pieces. Flatness ensures that the
relations of a finite generating family commute with all the scalar extensions in question. -/
theorem finitePresentation_iff_baseChange_and_localized
    (hG : Bijective (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S (S ⊗[R] M) ∧
      ∀ g ∈ G, Module.FinitePresentation (Localization.Away g)
        (Localization.Away g ⊗[R] M) := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun _ _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  have : Module.Finite R M := (finite_iff_baseChange_and_localized hG).mpr
    ⟨inferInstance, fun g hg ↦ by have := hloc g hg; infer_instance⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  -- The kernel of the finite free presentation is finite on every piece.
  have : Module.Finite R (LinearMap.ker f) := (finite_iff_baseChange_and_localized hG).mpr
    ⟨f.finite_tensorProduct_ker (S := S) hf, fun g hg ↦ by
      have := hloc g hg
      exact f.finite_tensorProduct_ker hf⟩
  exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp this)

end TauCeti
