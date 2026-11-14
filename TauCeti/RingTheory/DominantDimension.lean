/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.Injective.MinimalCoresolution
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
(`ModuleCat.natCast_le_dominantDimension_iff_of_finite`): the minimal injective coresolution is a
termwise retract of every injective coresolution, so its first `n` terms are projective-injective,
and a projective injective envelope of a finitely generated module is finitely generated
(`TauCeti.IsInjectiveEnvelope.finite_of_projective`). For an Artin algebra this is the dominant
dimension of [ARS, §VI.5]. For other rings the established notion asks the terms of the minimal
injective coresolution to be flat rather than projective (Hoshino); Xi calls it the
*flat-dominant dimension*. The two differ already for `ℤ`: here `dominantDimension ℤ = 0`
(`TauCeti.dominantDimension_int`), because a projective and injective `ℤ`-module is zero, while in
the minimal injective coresolution `0 → ℤ → ℚ → ℚ/ℤ → 0` the module `ℚ` is flat and `ℚ/ℤ` is not,
so the flat version is `1`. The flat version is not defined here.

## Main definitions

* `TauCeti.dominantDimension Γ`: the dominant dimension of a ring, of left modules.

## Main results

* `ModuleCat.natCast_le_dominantDimension_iff_of_finite` and
  `TauCeti.natCast_le_dominantDimension_iff_of_finite`: for a finitely generated module, and for
  the ring itself, `n ≤ dom.dim` exactly when there is a coresolution with `n` terms by finitely
  generated projective-injective modules.
* `TauCeti.two_le_dominantDimension_iff_of_finite`: `dom.dim Γ ≥ 2` exactly when `Γ` has an
  injective copresentation by finitely generated projective-injective modules.
* `TauCeti.dominantDimension_eq_top_of_injective`: a left self-injective ring has dominant
  dimension `⊤`.
* `TauCeti.dominantDimension_int`: `dominantDimension ℤ = 0`.
* `ModuleCat.dominantDimension_le_dominantDimension_pi`: `dom.dim M ≤ dom.dim Mⁿ`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, p. 211.
* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280.
* C. Xi, *Frobenius bimodules and flat-dominant dimensions*, arXiv:1903.07921v1, §1.
-/

public section

universe u v

open CategoryTheory Limits ComposableArrows TauCeti

/-- The cosyzygies of a minimal injective coresolution of a finitely generated module by
projective modules are finitely generated, and so are its terms. -/
private theorem ModuleCat.finite_cosyzygy {Γ : Type u} [Ring Γ] [Small.{v} Γ] {n : ℕ}
    {E : ComposableArrows (ModuleCat.{v} Γ) (n + 1)} (hE : E.IsMinimalInjectiveCoresolution)
    [Module.Finite Γ (E.obj' 1)] (hP : ∀ (i : ℕ) (hi : i < n), Projective (E.obj' (i + 2))) :
    ∀ (i : ℕ) (hi : i ≤ n), Module.Finite Γ (E.cosyzygy i)
  | 0, _ => Module.Finite.equiv hE.cosyzygyZeroIso.toLinearEquiv.symm
  | i + 1, hi => by
    have := ModuleCat.finite_cosyzygy hE hP i (by omega)
    have := hE.injective i (by omega)
    have := hP i (by omega)
    have : Module.Projective Γ (E.obj' (i + 2)) :=
      (IsProjective.iff_projective (E.obj' (i + 2))).2 inferInstance
    have := ((isInjectiveEnvelope_iff_injective_and_isEssentialMono _).2
      ⟨inferInstance, hE.isEssentialMono_cosyzygyι i (by omega)⟩).finite_of_projective
    -- The next cosyzygy is a quotient of the term `E.obj' (i + 2)`.
    exact Module.Finite.of_surjective (cokernel.π (E.map' (i + 1) (i + 2))).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- **Finitely generated coresolutions.** For a finitely generated module `M` over any ring,
`n ≤ dom.dim M` exactly when `M` has a coresolution with `n` terms by finitely generated
projective-injective modules. The minimal injective coresolution has projective terms as soon as
`n ≤ dom.dim M`, and a projective injective envelope of a finitely generated module is finitely
generated. -/
theorem ModuleCat.natCast_le_dominantDimension_iff_of_finite {Γ : Type u} [Ring Γ] [Small.{v} Γ]
    (M : ModuleCat.{v} Γ) [Module.Finite Γ M] (n : ℕ) :
    (n : ℕ∞) ≤ CategoryTheory.dominantDimension M ↔
      HasCoresolution (fun N : ModuleCat.{v} Γ ↦ Module.Finite Γ N ∧ Projective N ∧ Injective N)
        M n := by
  constructor
  · intro h
    obtain ⟨E, hE, ⟨e⟩⟩ := ModuleCat.exists_isMinimalInjectiveCoresolution M n
    have hP := (hE.natCast_le_dominantDimension_iff e).1 h
    have : Module.Finite Γ (E.obj' 1) := Module.Finite.equiv e.toLinearEquiv.symm
    have hfin := ModuleCat.finite_cosyzygy hE hP
    refine hasCoresolution_iff.2 ⟨E, hE.toIsCoresolution, ⟨e⟩, fun i hi ↦ ⟨?_, hP i hi,
      hE.injective i hi⟩⟩
    have := hfin i (by omega)
    have := hE.injective i hi
    have := hP i hi
    have : Module.Projective Γ (E.obj' (i + 2)) :=
      (IsProjective.iff_projective (E.obj' (i + 2))).2 inferInstance
    exact ((isInjectiveEnvelope_iff_injective_and_isEssentialMono _).2
      ⟨inferInstance, hE.isEssentialMono_cosyzygyι i hi⟩).finite_of_projective
  · intro h
    obtain ⟨S, hS, e, hP⟩ := hasCoresolution_iff.1 h
    exact natCast_le_dominantDimension_iff.2
      (hasProjectiveInjectiveCoresolution_iff.2 ⟨S, hS, e, fun i hi ↦ (hP i hi).2⟩)

/-- **Finite powers.** The dominant dimension of a finite power `Mⁿ` of a module is at least that
of `M`; for `n = 0` the power is zero, of dominant dimension `⊤`. -/
theorem ModuleCat.dominantDimension_le_dominantDimension_pi {Γ : Type u} [Ring Γ]
    (M : ModuleCat.{v} Γ) (n : ℕ) :
    CategoryTheory.dominantDimension M ≤
      CategoryTheory.dominantDimension (ModuleCat.of Γ (Fin n → M)) := by
  rw [← dominantDimension_eq_of_iso (ModuleCat.biproductIsoPi fun _ : Fin n ↦ M)]
  exact (le_iInf fun _ ↦ le_rfl).trans
    (iInf_dominantDimension_le_dominantDimension_biproduct fun _ : Fin n ↦ M)

namespace TauCeti

/-- The **dominant dimension** `dom.dim Γ` of a ring `Γ`, of left modules: the dominant dimension of
the left regular module (`CategoryTheory.dominantDimension`), the supremum in `ℕ∞` of the `n` for
which `Γ` has a coresolution `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹` by projective and injective modules.

This is the dominant dimension of [ARS, §VI.5] only for Artin algebras
(`TauCeti.natCast_le_dominantDimension_iff_of_finite`). For other rings the established notion asks
the terms of the minimal injective coresolution to be flat (Hoshino; Xi's *flat-dominant
dimension*), and the two differ already for `ℤ` (`TauCeti.dominantDimension_int`). -/
noncomputable def dominantDimension (Γ : Type u) [Ring Γ] : ℕ∞ :=
  CategoryTheory.dominantDimension (ModuleCat.of Γ Γ)

/-- The dominant dimension of a ring is that of its left regular module. -/
theorem dominantDimension_eq_dominantDimension_of (Γ : Type u) [Ring Γ] :
    dominantDimension Γ = CategoryTheory.dominantDimension (ModuleCat.of Γ Γ) :=
  (rfl)

/-- **The dominant dimension of a ring through finitely generated modules.** `n ≤ dom.dim Γ`
exactly when `Γ` has a coresolution `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹` by finitely generated projective and
injective modules. For an Artin algebra this is the dominant dimension of [ARS, §VI.5]. -/
theorem natCast_le_dominantDimension_iff_of_finite (Γ : Type u) [Ring Γ] (n : ℕ) :
    (n : ℕ∞) ≤ dominantDimension Γ ↔
      HasCoresolution (fun M : ModuleCat.{u} Γ ↦ Module.Finite Γ M ∧ Projective M ∧ Injective M)
        (ModuleCat.of Γ Γ) n :=
  ModuleCat.natCast_le_dominantDimension_iff_of_finite (ModuleCat.of Γ Γ) n

/-- **The case `dom.dim Γ ≥ 2` through finitely generated modules.** It holds exactly when `Γ` has
an injective copresentation `0 → Γ → I⁰ → I¹` by finitely generated projective-injective
modules. -/
theorem two_le_dominantDimension_iff_of_finite (Γ : Type u) [Ring Γ] :
    2 ≤ dominantDimension Γ ↔
      ∃ (I₀ I₁ : ModuleCat.{u} Γ) (f : ModuleCat.of Γ Γ ⟶ I₀) (g : I₀ ⟶ I₁) (w : f ≫ g = 0),
        Mono f ∧ (ShortComplex.mk f g w).Exact ∧
          (Module.Finite Γ I₀ ∧ Projective I₀ ∧ Injective I₀) ∧
            (Module.Finite Γ I₁ ∧ Projective I₁ ∧ Injective I₁) := by
  rw [← Nat.cast_ofNat, natCast_le_dominantDimension_iff_of_finite, hasCoresolution_two_iff]

/-- **A left self-injective ring has dominant dimension `⊤`**, through the coresolution
`0 → Γ → Γ → 0 → 0 → ⋯`. -/
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
(`Module.subsingleton_of_projective_of_injective_int`), so `ℤ` has no projective-injective
coresolution with one term. The flat version of the dominant dimension (Hoshino) is `1` for `ℤ`,
so the two notions differ outside Artin algebras. -/
@[simp]
theorem dominantDimension_int : dominantDimension ℤ = 0 := by
  by_contra h
  have h1 : ((1 : ℕ) : ℕ∞) ≤ CategoryTheory.dominantDimension (ModuleCat.of ℤ ℤ) :=
    Order.one_le_iff_ne_zero.2 h
  obtain ⟨I, ι, hι, ⟨hP, hI⟩⟩ := hasCoresolution_one_iff.1
    (hasProjectiveInjectiveCoresolution_iff_hasCoresolution.1
      (natCast_le_dominantDimension_iff.1 h1))
  have : Module.Projective ℤ I := (IsProjective.iff_projective (R := ℤ) I).2 hP
  have : Module.Injective ℤ I := Module.injective_module_of_injective_object ℤ I
  have := Module.subsingleton_of_projective_of_injective_int I
  have hinj := (ModuleCat.mono_iff_injective ι).1 hι
  exact one_ne_zero (hinj (Subsingleton.elim (ι.hom 1) (ι.hom 0)))

end TauCeti
