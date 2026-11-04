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

/-!
# Finite generation on the formal-glueing pieces

Let `R → S` be flat and induce an isomorphism `R/I → S/IS`, where `I` has a finite
generating set `G`. An `R`-module is finite if and only if its base change to `S` and its
localizations at the elements of `G` are finite. Neither Noetherianity nor faithful
flatness is required.

This is the finite-generation part of finiteness preservation in formal glueing. In
particular, it detects whether a reconstructed algebra defines a finite morphism.
The proof chooses finitely many generators on each piece and applies joint detection
to the quotient by their span.

## References

* The Stacks Project, Remark 15.91.20 (05EU), finite generation in formal glueing.
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
  have htop : N = ⊤ := by
    apply top_unique
    intro m _
    simpa using (Subsingleton.elim (N.mkQ m) 0)
  exact Module.Finite.of_fg_top (htop ▸ hN)

end TauCeti
