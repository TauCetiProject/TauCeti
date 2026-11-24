/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Module.Injective.Envelope.ModuleCat
public import TauCeti.Algebra.Module.Injective.Envelope.Projective
public import TauCeti.CategoryTheory.Abelian.DominantDimension

/-!
# The dominant dimension of modules

This file specializes the dominant dimension of objects of an abelian category
(`CategoryTheory.dominantDimension`) to modules over a ring.

For a finitely generated module `M` over any ring, `n ≤ dom.dim M` exactly when `M` has a
coresolution `0 → M → I⁰ → ⋯ → Iⁿ⁻¹` by **finitely generated** projective-injective modules
(`ModuleCat.natCast_le_dominantDimension_iff_of_finite`). Indeed the injective envelope of `M` is a
retract of every injective module containing `M`, so it is projective as soon as some
projective-injective module contains `M`, and a projective injective envelope of a finitely
generated module is finitely generated (`TauCeti.IsInjectiveEnvelope.finite_of_projective`).

## Main results

* `ModuleCat.natCast_le_dominantDimension_iff_of_finite`: for a finitely generated module,
  `n ≤ dom.dim` exactly when there is a coresolution with `n` terms by finitely generated
  projective-injective modules.
* `ModuleCat.dominantDimension_pi`: the dominant dimension of a finite product of modules is the
  infimum of those of its factors.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, p. 211.
-/

public section

universe w u v

open CategoryTheory Limits TauCeti

/-- **Finitely generated coresolutions.** For a finitely generated module `M` over any ring,
`n ≤ dom.dim M` exactly when `M` has a coresolution with `n` terms by finitely generated
projective-injective modules. The injective envelope of `M` is a retract of every
projective-injective module containing `M`, hence projective, and a projective injective envelope
of a finitely generated module is finitely generated. -/
theorem ModuleCat.natCast_le_dominantDimension_iff_of_finite {Γ : Type u} [Ring Γ] [Small.{v} Γ]
    (M : ModuleCat.{v} Γ) [Module.Finite Γ M] (n : ℕ) :
    (n : ℕ∞) ≤ CategoryTheory.dominantDimension M ↔
      ObjectProperty.IsSyzygy
        (fun N : ModuleCat.{v} Γ ↦ Module.Finite Γ N ∧ Projective N ∧ Injective N) n M := by
  rw [natCast_le_dominantDimension_iff]
  refine ⟨fun h ↦ ?_, fun h ↦
    hasProjectiveInjectiveCoresolution_iff_isSyzygy.2 (h.mono fun _ h ↦ h.2)⟩
  induction n generalizing M with
  | zero => exact ObjectProperty.isSyzygy_zero _ M
  | succ n ih =>
    obtain ⟨J, j, hj, ⟨hJ, hJ'⟩, h'⟩ := ObjectProperty.isSyzygy_succ_iff_exists_mono.1
      (hasProjectiveInjectiveCoresolution_iff_isSyzygy.1 h)
    -- The injective envelope `ι : M ⟶ E` is a retract of `j`, together with its cokernel.
    obtain ⟨E, ι, hE, hι⟩ := M.exists_injective_and_isEssentialMono
    obtain ⟨⟨r⟩, ⟨r'⟩⟩ := hι.nonempty_retract_and_nonempty_retract_cokernel (Retract.refl M)
      (j := j)
    have : Projective E := r.projective
    have := ((isInjectiveEnvelope_iff_injective_and_isEssentialMono ι).2
      ⟨hE, hι⟩).finite_of_projective
    have : Module.Finite Γ (cokernel ι : ModuleCat.{v} Γ) :=
      Module.Finite.of_surjective (cokernel.π ι).hom
        ((ModuleCat.epi_iff_surjective _).1 inferInstance)
    exact ObjectProperty.isSyzygy_succ_iff_exists_mono.2 ⟨E, ι, hι.mono,
      ⟨inferInstance, inferInstance, hE⟩, ih _
      ((hasProjectiveInjectiveCoresolution_iff_isSyzygy.2 h').of_retract r')⟩

/-- **Finite products.** The dominant dimension of a finite product of modules is the infimum of
those of its factors. -/
theorem ModuleCat.dominantDimension_pi {Γ : Type u} [Ring Γ] {J : Type w} [Finite J]
    (f : J → ModuleCat.{max w v} Γ) :
    CategoryTheory.dominantDimension (ModuleCat.of Γ (∀ j, f j)) =
      ⨅ j, CategoryTheory.dominantDimension (f j) := by
  -- The biproduct and the product cone `ModuleCat.of Γ (∀ j, f j)` are both limits of `f`.
  let e : (⨁ f) ≅ ModuleCat.of Γ (∀ j, f j) :=
    (biproduct.isLimit f).conePointUniqueUpToIso (ModuleCat.HasLimit.productLimitCone f).isLimit
  rw [← dominantDimension_eq_of_iso e, dominantDimension_biproduct]
