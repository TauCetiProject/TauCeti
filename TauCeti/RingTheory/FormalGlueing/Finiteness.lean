/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGlueing.Detection
public import TauCeti.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.FinitePresentation
import TauCeti.LinearAlgebra.TensorProduct.Kernel

/-!
# Finiteness on the formal-glueing pieces

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, where `I` has a finite
generating set `G`. An `R`-module is finitely generated (respectively finitely presented)
if and only if its base change to `S` and its localizations at the elements of `G` have
that property. Neither Noetherianity nor faithful flatness is required.

This detects finiteness of a reconstructed module in formal glueing, in particular when passing
from an algebra over a completion and an algebra on the complementary open set to a finite
algebra over the original ring. It does not assert the existence of that reconstruction.
The finite-generation proof chooses finitely many generators on each piece and applies joint
detection to the quotient by their span. Finite presentation then follows by applying the
finite-generation criterion to the kernel of a finite free presentation.

## References

* The Stacks Project, Remark 15.91.20 (05EU), preservation of finiteness in formal glueing.
* The Stacks Project, Proposition 15.91.16 (05ER), formal glueing of modules.
-/

public section

open TensorProduct

namespace TauCeti

/-- Finite generation is detected by a flat base change preserving `R/(G)` together with
the principal localizations at the finite set `G`. The localized modules are finite over
the localized rings, not necessarily over `R`. -/
@[stacks 05EU "finite generation on the formal-glueing pieces"]
theorem finite_iff_baseChange_and_localized {R S M : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] (G : Finset R)
    (hG : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    Module.Finite R M ↔ Module.Finite S (S ⊗[R] M) ∧
      ∀ g ∈ G, Module.Finite (Localization.Away g) (LocalizedModule.Away g M) := by
  classical
  refine ⟨fun _ ↦ ⟨inferInstance, fun _ _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  obtain ⟨P, hP, hPS⟩ := exists_fg_baseChange_eq_top R S M
  have hlocal (g : G) : ∃ Q : Submodule R M,
      Q.FG ∧ Q.baseChange (Localization.Away g.1) = ⊤ := by
    have := hloc g.1 g.2
    have : Module.Finite (Localization.Away g.1) (Localization.Away g.1 ⊗[R] M) :=
      Module.Finite.of_surjective (LocalizedModule.equivTensorProduct (.powers g.1) M).toLinearMap
        (LinearEquiv.surjective _)
    exact exists_fg_baseChange_eq_top R (Localization.Away g.1) M
  choose Q hQ hQloc using hlocal
  let N := P ⊔ ⨆ g : G, Q g
  have hN : N.FG := hP.sup (Submodule.fg_iSup Q hQ)
  have hNS : N.baseChange S = ⊤ := by
    apply top_unique
    rw [← hPS]
    exact Submodule.baseChange_mono _ le_sup_left
  have hNloc (g : G) : N.baseChange (Localization.Away g.1) = ⊤ := by
    apply top_unique
    rw [← hQloc g]
    exact Submodule.baseChange_mono _ ((le_iSup Q g).trans le_sup_right)
  have : Subsingleton (S ⊗[R] (M ⧸ N)) :=
    (Submodule.baseChange_eq_top_iff_subsingleton S N).mp hNS
  have : Subsingleton (M ⧸ N) := subsingleton_of_baseChange_and_localized hG fun g hg ↦ by
    have : Subsingleton (Localization.Away g ⊗[R] (M ⧸ N)) :=
      (Submodule.baseChange_eq_top_iff_subsingleton (Localization.Away g) N).mp
        (hNloc ⟨g, hg⟩)
    exact (LocalizedModule.equivTensorProduct (.powers g) (M ⧸ N)).injective.subsingleton
  have htop : N = ⊤ := Submodule.Quotient.subsingleton_iff.mp this
  exact Module.Finite.of_fg_top (htop ▸ hN)

/-- Finite presentation is detected on the formal-glueing pieces. Flatness ensures that the
relations of a finite generating family commute with all the scalar extensions in question. -/
theorem finitePresentation_iff_baseChange_and_localized {R S M : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [AddCommGroup M] [Module R M] (G : Finset R)
    (hG : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (G : Set R)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    Module.FinitePresentation R M ↔ Module.FinitePresentation S (S ⊗[R] M) ∧
      ∀ g ∈ G, Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun _ _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨hS, hloc⟩
  have : Module.Finite R M := (finite_iff_baseChange_and_localized G hG).mpr
    ⟨inferInstance, fun g hg ↦ by have := hloc g hg; infer_instance⟩
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  -- The kernel of the finite free presentation is finite on every piece.
  have : Module.Finite R (LinearMap.ker f) := (finite_iff_baseChange_and_localized G hG).mpr
    ⟨f.finite_tensorProduct_ker (S := S) hf, fun g hg ↦ by
      have := hloc g hg
      have : Module.FinitePresentation (Localization.Away g) (Localization.Away g ⊗[R] M) :=
        Module.FinitePresentation.of_equiv (LocalizedModule.equivTensorProduct (.powers g) M)
      have := f.finite_tensorProduct_ker (S := Localization.Away g) hf
      exact Module.Finite.equiv
        (LocalizedModule.equivTensorProduct (.powers g) (LinearMap.ker f)).symm⟩
  exact Module.finitePresentation_of_surjective f hf (Module.Finite.iff_fg.mp this)

end TauCeti
