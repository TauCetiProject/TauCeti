/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Flasque
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Serre's vanishing theorem on a Noetherian affine scheme

Let `R` be a Noetherian ring. This file proves that a quasi-coherent sheaf of modules on `Spec R`
has no cohomology in positive degrees: `Hⁿ(Spec R, M~) = 0` for every `R`-module `M` and every
`n > 0`. Together with the Mayer–Vietoris sequence this is how the cohomology of a quasi-coherent
sheaf on a Noetherian scheme is computed from an affine open cover.

The proof is by dimension shifting. Embed `M` into an injective `R`-module `I`, with cokernel `Q`.
Since `M ↦ M~` is exact, `0 ⟶ M~ ⟶ I~ ⟶ Q~ ⟶ 0` is a short exact sequence of
`𝒪_{Spec R}`-modules, and `I~` is flasque because `R` is Noetherian. Hence the long exact sequence
gives `H¹(M~) = coker(Γ(I~) ⟶ Γ(Q~)) = coker(I ⟶ Q) = 0` and `Hⁿ⁺²(M~) ≅ Hⁿ⁺¹(Q~)`, and induction
on `n` concludes, since `Q` is again an arbitrary `R`-module.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isQuasicoherent`: a
  quasi-coherent sheaf of modules on the spectrum of a Noetherian ring has vanishing cohomology in
  every positive degree.

## Implementation notes

The Noetherian hypothesis enters only through the flasqueness of `I~`. The vanishing holds on
every affine scheme, but the proof of that generality goes through Čech cohomology rather than
injective modules.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Theorem 3.5 and Proposition 3.4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

open Scheme.Modules

universe u

variable {R : CommRingCat.{u}}

/-- The sequence `0 ⟶ M~ ⟶ I~ ⟶ Q~ ⟶ 0` obtained by applying `M ↦ M~` to the embedding of `M`
into an injective module `I` with cokernel `Q`. -/
private noncomputable def tildeInjectiveShortComplex (M : ModuleCat.{u} R) :
    ShortComplex (Spec R).Modules :=
  (ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M))
    (cokernel.condition _)).map (tilde.functor R)

private lemma shortExact_tildeInjectiveShortComplex (M : ModuleCat.{u} R) :
    (tildeInjectiveShortComplex M).ShortExact :=
  ShortComplex.ShortExact.map_of_exact
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (Injective.ι M))
      mono_f := inferInstanceAs (Mono (Injective.ι M))
      epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι M))) } _

variable [IsNoetherianRing R]

private lemma isFlasque_tildeInjectiveShortComplex (M : ModuleCat.{u} R) :
    (tildeInjectiveShortComplex M).X₂.presheaf.IsFlasque := by
  let I : ModuleCat.{u} R := Injective.under M
  have : Module.Injective R I :=
    Module.injective_module_of_injective_object (inj := inferInstanceAs (Injective I))
  exact isFlasque_tilde_of_injective I

/-- On the spectrum of a Noetherian ring `R`, the sheaf `M~` associated with an `R`-module `M` has
vanishing cohomology in every positive degree. This is the form of Serre's vanishing theorem that
the induction on the degree proves, for all modules at once. -/
private theorem subsingleton_cohomology_tilde_succ (M : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Cohomology (tilde M) (n + 1)) := by
  induction n generalizing M with
  | zero =>
    let S := tildeInjectiveShortComplex M
    have hS : S.ShortExact := shortExact_tildeInjectiveShortComplex M
    have : S.X₂.presheaf.IsFlasque := isFlasque_tildeInjectiveShortComplex M
    have : Epi S.g := hS.epi_g
    -- The terms of `S` are sheaves `N~`, hence quasi-coherent.
    have : S.X₂.IsQuasicoherent := inferInstanceAs (tilde (Injective.under M)).IsQuasicoherent
    have : S.X₃.IsQuasicoherent :=
      inferInstanceAs (tilde (cokernel (Injective.ι M))).IsQuasicoherent
    -- `H⁰(I~) ⟶ H⁰(Q~)` is the surjection `Γ(I~) ⟶ Γ(Q~)` of global sections.
    have hg : Function.Surjective (cohomologyMap S.g 0) := by
      intro z
      obtain ⟨w, hw⟩ : ∃ w : Γ(S.X₂, ⊤), S.g.app ⊤ w = cohomologyZeroEquiv _ z :=
        moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent S.g _
      refine ⟨(cohomologyZeroEquiv _).symm w, (cohomologyZeroEquiv _).injective ?_⟩
      rw [cohomologyZeroEquiv_cohomologyMap, AddEquiv.apply_symm_apply, hw]
    -- Every class in `H¹(M~)` is `δ` of a class in `H⁰(Q~)` coming from `H⁰(I~)`, hence zero.
    have hδ := (cohomologyδ_surjective_of_isFlasque hS 0 1 rfl).comp hg
    have hex := exact_cohomologyMap_cohomologyδ hS 0 1 rfl
    refine ⟨fun x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := hδ x
    obtain ⟨y, rfl⟩ := hδ y
    exact (hex.apply_apply_eq_zero x).trans (hex.apply_apply_eq_zero y).symm
  | succ n ih =>
    -- `Hⁿ⁺²(M~)` is the image of `Hⁿ⁺¹(Q~)`, which vanishes by induction.
    let S := tildeInjectiveShortComplex M
    have : S.X₂.presheaf.IsFlasque := isFlasque_tildeInjectiveShortComplex M
    have : Subsingleton (Cohomology S.X₃ (n + 1)) := ih _
    exact (cohomologyδ_surjective_of_isFlasque (shortExact_tildeInjectiveShortComplex M)
      (n + 1) (n + 2) rfl).subsingleton

/-- **Serre's vanishing theorem** (Hartshorne, *Algebraic Geometry*, Theorem III.3.5): on the
spectrum of a Noetherian ring, a quasi-coherent sheaf of modules has vanishing cohomology in every
positive degree. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.subsingleton_cohomology_succ_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Cohomology M (n + 1)) := by
  -- `M` is isomorphic to the sheaf associated with its module of global sections.
  have : Subsingleton ((cohomologyFunctor _ (n + 1)).obj
      (tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))) :=
    subsingleton_cohomology_tilde_succ _ n
  exact ((cohomologyFunctor _ (n + 1)).mapIso
    (asIso M.fromTildeΓ)).addCommGroupIsoToAddEquiv.symm.toEquiv.subsingleton

end AlgebraicGeometry

end TauCeti
