/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.Algebra.Module.StablyFree.Exact
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.LocalProperties.Projective

/-!
# Stably free localizations of modules with finite projective dimension

A finite module over a Noetherian local ring has a resolution by finite free modules when
its projective dimension is finite. If a localization becomes projective, localizing this
resolution and splitting short exact sequences shows that it is stably free.

## References

* [The Stacks Project, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0), the stable-freeness
  argument used to prove factoriality of regular local rings.
-/


public section

universe u

open CategoryTheory

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A projective localization of a finite module of finite projective dimension over a
Noetherian local ring is stably free. -/
theorem isStablyFree_of_isLocalizedModule_of_hasProjectiveDimensionLE (S : Submonoid R) (n : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      HasProjectiveDimensionLE (ModuleCat.of R M) n →
      ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module (Localization S) N]
        [IsScalarTower R (Localization S) N] (f : M →ₗ[R] N) [IsLocalizedModule S f]
        [Projective (Localization S) N], IsStablyFree (Localization S) N := by
  induction n with
  | zero =>
    intro M _ _ _ hM N _ _ _ _ f _ _
    have : Projective R M := by
      rw [IsProjective.iff_projective, projective_iff_hasProjectiveDimensionLE_zero]
      exact hM
    have : Free R M := free_of_flat_of_isLocalRing
    have : Free (Localization S) N := free_of_isLocalizedModule S f
    infer_instance
  | succ n ih =>
    intro M _ _ _ hM N _ _ _ _ f _ _
    obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hex := LinearMap.exact_subtype_ker_map π
    have hS := ModuleCat.shortComplex_shortExact
      (ModuleCat.shortComplexOfCompEqZero K.subtype π hex.linearMap_comp_eq_zero) hex
      K.injective_subtype hπ
    have : CategoryTheory.Projective (ModuleCat.of R (Fin r → R)) := inferInstance
    have hK : HasProjectiveDimensionLE (ModuleCat.of R K) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n this).mp hM
    let fK := LocalizedModule.mkLinearMap S K
    let fF := LocalizedModule.mkLinearMap S (Fin r → R)
    have : Free (Localization S) (LocalizedModule S (Fin r → R)) := free_of_isLocalizedModule S fF
    have : Module.Finite (Localization S) (LocalizedModule S (Fin r → R)) :=
      .of_isLocalizedModule S fF
    let i := (IsLocalizedModule.map S fK fF K.subtype).extendScalarsOfIsLocalization S
      (Localization S)
    let q := (IsLocalizedModule.map S fF f π).extendScalarsOfIsLocalization S (Localization S)
    have hi : Function.Injective i := IsLocalizedModule.map_injective S fK fF _ K.injective_subtype
    have hq : Function.Surjective q := IsLocalizedModule.map_surjective S fF f _ hπ
    have he : Function.Exact i q := IsLocalizedModule.map_exact S fK fF f _ _ hex
    have : Projective (Localization S) (LocalizedModule S K) := by
      exact Projective.of_exact_of_projective (ring := Localization S)
        (kernel := LocalizedModule S K) (freeModule := LocalizedModule S (Fin r → R))
        (quotientModule := N) (firstMap := i) (secondMap := q) hi hq he
    have := ih K hK (LocalizedModule S K) fK
    exact IsStablyFree.of_exact (ring := Localization S)
      (kernel := LocalizedModule S K) (freeModule := LocalizedModule S (Fin r → R))
      (quotientModule := N) (firstMap := i) (secondMap := q) hi hq he

end Module
