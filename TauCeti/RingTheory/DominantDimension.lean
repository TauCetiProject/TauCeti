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
public import TauCeti.Algebra.Module.Injective.Int
public import TauCeti.CategoryTheory.Abelian.DominantDimension

/-!
# The dominant dimension of a ring

The **dominant dimension** `dom.dim Γ` of a ring `Γ` (`TauCeti.dominantDimension`) is the dominant
dimension of the left regular module `Γ` in `ModuleCat Γ` (`CategoryTheory.dominantDimension`): the
supremum of the `n` for which there is an exact sequence `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹`, exact at `Γ` and
at `I⁰, …, Iⁿ⁻²`, by projective and injective modules.

For a finitely generated module `M` over any ring, `n ≤ dom.dim M` exactly when there is such a
coresolution by **finitely generated** projective-injective modules
(`ModuleCat.natCast_le_dominantDimension_iff_of_finite`). Indeed the injective envelope of `M` is a
retract of every injective module containing `M`, so it is projective as soon as some
projective-injective module contains `M`, and a projective injective envelope of a finitely
generated module is finitely generated (`TauCeti.IsInjectiveEnvelope.finite_of_projective`). For an
Artin algebra this is the dominant dimension of [ARS, §VI.5].

For other rings the established notion asks the terms of the minimal injective coresolution to be
flat rather than projective (Hoshino); Xi calls it the *flat-dominant dimension*. The two differ
already for `ℤ`: here `dominantDimension ℤ = 0` (`TauCeti.dominantDimension_int`), because a
projective and injective `ℤ`-module is zero, while in the minimal injective coresolution
`0 → ℤ → ℚ → ℚ/ℤ → 0` the module `ℚ` is flat and `ℚ/ℤ` is not, so the flat version is `1`. The flat
version is not defined here.

## Main definitions

* `TauCeti.dominantDimension Γ`: the dominant dimension of a ring, of left modules.

## Main results

* `ModuleCat.natCast_le_dominantDimension_iff_of_finite` and
  `TauCeti.natCast_le_dominantDimension_iff`: for a finitely generated module, and for the ring
  itself, `n ≤ dom.dim` exactly when there is a coresolution with `n` terms by finitely generated
  projective-injective modules.
* `TauCeti.two_le_dominantDimension_iff`: `dom.dim Γ ≥ 2` exactly when `Γ` has an injective
  copresentation by finitely generated projective-injective modules.
* `ModuleCat.dominantDimension_pi`: the dominant dimension of a finite product of modules is the
  infimum of those of its factors.
* `TauCeti.dominantDimension_eq_top_of_injective`: a left self-injective ring has dominant
  dimension `⊤`.
* `TauCeti.dominantDimension_int`: `dominantDimension ℤ = 0`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, p. 211.
* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280.
* C. Xi, *Frobenius bimodules and flat-dominant dimensions*, arXiv:1903.07921v1, §1.
-/

public section

universe u v

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
@[simp]
theorem ModuleCat.dominantDimension_pi {Γ : Type u} [Ring Γ] {J : Type} [Finite J]
    (f : J → ModuleCat.{v} Γ) :
    CategoryTheory.dominantDimension (ModuleCat.of Γ (∀ j, f j)) =
      ⨅ j, CategoryTheory.dominantDimension (f j) := by
  rw [← dominantDimension_eq_of_iso (ModuleCat.biproductIsoPi f), dominantDimension_biproduct]

namespace TauCeti

/-- The **dominant dimension** `dom.dim Γ` of a ring `Γ`, of left modules: the dominant dimension of
the left regular module (`CategoryTheory.dominantDimension`), the supremum in `ℕ∞` of the `n` for
which `Γ` has a coresolution `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹` by projective and injective modules.

This is the dominant dimension of [ARS, §VI.5] only for Artin algebras
(`TauCeti.natCast_le_dominantDimension_iff`). For other rings the established notion asks the terms
of the minimal injective coresolution to be flat (Hoshino; Xi's *flat-dominant dimension*), and the
two differ already for `ℤ` (`TauCeti.dominantDimension_int`). -/
noncomputable def dominantDimension (Γ : Type u) [Ring Γ] : ℕ∞ :=
  CategoryTheory.dominantDimension (ModuleCat.of Γ Γ)

/-- The dominant dimension of a ring is that of its left regular module. -/
theorem dominantDimension_eq_dominantDimension_of (Γ : Type u) [Ring Γ] :
    dominantDimension Γ = CategoryTheory.dominantDimension (ModuleCat.of Γ Γ) :=
  (rfl)

/-- **The dominant dimension of a ring through finitely generated modules.** `n ≤ dom.dim Γ`
exactly when `Γ` has a coresolution `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹` by finitely generated projective and
injective modules. For an Artin algebra this is the dominant dimension of [ARS, §VI.5]. -/
theorem natCast_le_dominantDimension_iff (Γ : Type u) [Ring Γ] (n : ℕ) :
    (n : ℕ∞) ≤ dominantDimension Γ ↔
      ObjectProperty.IsSyzygy
        (fun M : ModuleCat.{u} Γ ↦ Module.Finite Γ M ∧ Projective M ∧ Injective M) n
        (ModuleCat.of Γ Γ) :=
  ModuleCat.natCast_le_dominantDimension_iff_of_finite (ModuleCat.of Γ Γ) n

/-- **The case `dom.dim Γ ≥ 2` through finitely generated modules.** It holds exactly when `Γ` has
an injective copresentation `0 → Γ → I⁰ → I¹` by finitely generated projective-injective
modules. -/
theorem two_le_dominantDimension_iff (Γ : Type u) [Ring Γ] :
    2 ≤ dominantDimension Γ ↔
      ∃ (I₀ I₁ : ModuleCat.{u} Γ) (f : ModuleCat.of Γ Γ ⟶ I₀) (g : I₀ ⟶ I₁) (w : f ≫ g = 0),
        Mono f ∧ (ShortComplex.mk f g w).Exact ∧
          (Module.Finite Γ I₀ ∧ Projective I₀ ∧ Injective I₀) ∧
            (Module.Finite Γ I₁ ∧ Projective I₁ ∧ Injective I₁) := by
  rw [← Nat.cast_ofNat, TauCeti.natCast_le_dominantDimension_iff, ObjectProperty.isSyzygy_two_iff]

/-- **A left self-injective ring has dominant dimension `⊤`**, through the coresolution
`0 → Γ → Γ → 0 → 0 → ⋯`. -/
@[simp]
theorem dominantDimension_eq_top_of_injective (Γ : Type u) [Ring Γ] [Module.Injective Γ Γ] :
    dominantDimension Γ = ⊤ := by
  have : Projective (ModuleCat.of Γ Γ) := (IsProjective.iff_projective Γ).1 inferInstance
  have : Injective (ModuleCat.of Γ Γ) := Module.injective_object_of_injective_module Γ Γ
  exact CategoryTheory.dominantDimension_eq_top _

/-- The zero ring has dominant dimension `⊤`. -/
@[simp]
theorem dominantDimension_eq_top_of_subsingleton (Γ : Type u) [Ring Γ] [Subsingleton Γ] :
    dominantDimension Γ = ⊤ :=
  (ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ Γ)).dominantDimension_eq_top

/-- **`dominantDimension ℤ = 0`.** A projective and injective `ℤ`-module is zero
(`Module.subsingleton_of_projective_of_injective_int`), so `ℤ` embeds into no projective-injective
module. The flat version of the dominant dimension (Hoshino) is `1` for `ℤ`, so the two notions
differ outside Artin algebras. -/
@[simp]
theorem dominantDimension_int : dominantDimension ℤ = 0 := by
  refine dominantDimension_eq_zero_iff.2 fun ⟨I, ι, hι, hP, hI⟩ ↦ ?_
  have := hP
  have : Module.Injective ℤ I := Module.injective_module_of_injective_object ℤ I
  have := Module.subsingleton_of_projective_of_injective_int I
  exact one_ne_zero ((ModuleCat.mono_iff_injective ι).1 hι (Subsingleton.elim (ι.hom 1) (ι.hom 0)))

end TauCeti
