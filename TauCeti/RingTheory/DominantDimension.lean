/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.Algebra
public import TauCeti.Algebra.Module.Injective.Envelope.ModuleCat
public import TauCeti.CategoryTheory.Abelian.DominantDimension
public import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra

/-!
# The dominant dimension of a ring

The **dominant dimension** `dom.dim Γ` of a ring `Γ` (`TauCeti.dominantDimension`) is the dominant
dimension of the left regular module `Γ` in `ModuleCat Γ` (`CategoryTheory.dominantDimension`): the
supremum of the `n` for which there is an exact sequence `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹`, exact at `Γ` and
at `I⁰, …, Iⁿ⁻²`, by projective and injective modules.

For an Artin algebra this is the dominant dimension of [ARS, §VI.5]: the terms of the minimal
injective coresolution of `Γ` are finitely generated, and `n ≤ dom.dim Γ` exactly when there is
such a coresolution by **finitely generated** projective-injective modules
(`TauCeti.natCast_le_dominantDimension_iff_of_finite`). For other rings the established notion asks
the terms of the minimal injective coresolution to be flat rather than projective (Hoshino); Xi
calls it the *flat-dominant dimension*. The two differ already for `ℤ`: here
`dominantDimension ℤ = 0` (`TauCeti.dominantDimension_int`), because a projective and injective
`ℤ`-module is zero, while in the minimal injective coresolution `0 → ℤ → ℚ → ℚ/ℤ → 0` the module `ℚ`
is flat and `ℚ/ℤ` is not, so the flat version is `1`. The flat version is not defined here.

## Main definitions

* `TauCeti.dominantDimension Γ`: the dominant dimension of a ring, of left modules.

## Main results

* `TauCeti.natCast_le_dominantDimension_iff_of_finite`: for an Artin algebra, `n ≤ dom.dim Γ`
  exactly when `Γ` has a coresolution with `n` terms by finitely generated projective-injective
  modules.
* `TauCeti.dominantDimension_eq_top_of_injective`: a left self-injective ring has dominant
  dimension `⊤`.
* `TauCeti.dominantDimension_int`: `dominantDimension ℤ = 0`.
* `TauCeti.ModuleCat.exists_isMinimalInjectiveCoresolution`: every module has minimal injective
  coresolutions of every length.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, p. 211.
* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280.
* C. Xi, *On the finitistic dimension conjecture III*, J. Algebra 319 (2008), §1.
-/

public section

universe u v

open CategoryTheory Limits ComposableArrows

namespace TauCeti

/-- **Every module has minimal injective coresolutions of every length**, since every module has
an injective envelope. -/
theorem ModuleCat.exists_isMinimalInjectiveCoresolution {R : Type u} [Ring R] [Small.{v} R]
    (M : ModuleCat.{v} R) (n : ℕ) :
    ∃ E : ComposableArrows (ModuleCat.{v} R) (n + 1), E.IsMinimalInjectiveCoresolution ∧
      Nonempty (E.obj' 1 ≅ M) := by
  obtain ⟨E, hE, e, -⟩ := ComposableArrows.exists_isMinimalInjectiveCoresolution
    (Q := fun _ ↦ True)
    (fun X _ ↦ by
      obtain ⟨I, ι, hI, hι⟩ := ModuleCat.exists_isEssentialMono X
      exact ⟨I, ι, hI, hι, trivial, trivial⟩) n trivial (X := M)
  exact ⟨E, hE, e⟩

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

/-- **A left self-injective ring has dominant dimension `⊤`**, through the coresolution
`0 → Γ → Γ → 0 → 0 → ⋯`. -/
theorem dominantDimension_eq_top_of_injective (Γ : Type u) [Ring Γ] [Module.Injective Γ Γ] :
    dominantDimension Γ = ⊤ := by
  have : Projective (ModuleCat.of Γ Γ) := (IsProjective.iff_projective Γ).1 inferInstance
  have : Injective (ModuleCat.of Γ Γ) := Module.injective_object_of_injective_module Γ Γ
  exact CategoryTheory.dominantDimension_eq_top _

/-- The zero ring has dominant dimension `⊤`. -/
theorem dominantDimension_eq_top_of_subsingleton (Γ : Type u) [Ring Γ] [Subsingleton Γ] :
    dominantDimension Γ = ⊤ := by
  have hZ : IsZero (ModuleCat.of Γ Γ) := ModuleCat.isZero_of_subsingleton _
  have := hZ.projective
  have := hZ.injective
  exact CategoryTheory.dominantDimension_eq_top _

/-- A `ℤ`-module that is projective and injective is zero: an element is divisible by every
nonzero integer, by injectivity, and a linear form on a projective module that is nonzero on it
would then take a value divisible by every nonzero integer. -/
private theorem eq_zero_of_projective_of_injective {I : ModuleCat.{0} ℤ} [Projective I]
    [Injective I] (x : I) : x = 0 := by
  by_contra hx
  have : Module.Projective ℤ I := (IsProjective.iff_projective (R := ℤ) I).2 ‹_›
  obtain ⟨s, hs⟩ := Module.projective_def'.1 this
  have hsx : s x ≠ 0 := fun h ↦ hx (by
    have := LinearMap.congr_fun hs x
    rw [LinearMap.comp_apply, h, map_zero, LinearMap.id_apply] at this
    exact this.symm)
  obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hsx
  let φ : I →ₗ[ℤ] ℤ := Finsupp.lapply a ∘ₗ s
  have hφ : φ x ≠ 0 := ha
  -- `x` is divisible by `N = |φ x| + 1`, by injectivity of `I`.
  let N : ℕ := (φ x).natAbs + 1
  let m : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ := ModuleCat.ofHom ((N : ℤ) • LinearMap.id)
  have : Mono m := (ModuleCat.mono_iff_injective m).2 fun a b hab ↦ by
    have : (N : ℤ) * a = N * b := by simpa [m] using hab
    exact mul_left_cancel₀ (by positivity) this
  let g : ModuleCat.of ℤ ℤ ⟶ I := ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ I x)
  let h : ModuleCat.of ℤ ℤ ⟶ I := Injective.factorThru g m
  have hg : m ≫ h = g := Injective.comp_factorThru g m
  have hx' : x = (N : ℤ) • h.hom 1 := by
    have := congrArg (fun f ↦ f.hom 1) hg
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at this
    have hm : m.hom 1 = (N : ℤ) • (1 : ℤ) := rfl
    have hg1 : g.hom 1 = x := LinearMap.toSpanSingleton_apply_one ℤ I x
    rw [hm, map_zsmul, hg1] at this
    exact this.symm
  have hdvd : (N : ℤ) ∣ φ x := by
    rw [hx', map_zsmul, smul_eq_mul]
    exact dvd_mul_right _ _
  have := Int.natAbs_le_of_dvd_ne_zero hdvd hφ
  simp only [N, Int.natAbs_natCast] at this
  omega

/-- **`dominantDimension ℤ = 0`.** A projective and injective `ℤ`-module is zero, so `ℤ` has no
projective-injective coresolution with one term. The flat version of the dominant dimension
(Hoshino) is `1` for `ℤ`, so the two notions differ outside Artin algebras. -/
theorem dominantDimension_int : dominantDimension ℤ = 0 := by
  by_contra h
  have h1 : ((1 : ℕ) : ℕ∞) ≤ CategoryTheory.dominantDimension (ModuleCat.of ℤ ℤ) :=
    Order.one_le_iff_ne_zero.2 h
  obtain ⟨I, ι, hι, ⟨hP, hI⟩, -⟩ := hasCoresolution_succ_iff.1
    (hasProjectiveInjectiveCoresolution_iff_hasCoresolution.1
      (natCast_le_dominantDimension_iff.1 h1))
  have hinj := (ModuleCat.mono_iff_injective ι).1 hι
  have : ι.hom 1 = ι.hom 0 := by rw [map_zero]; exact eq_zero_of_projective_of_injective _
  exact one_ne_zero (hinj this)

section Artin

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type u) [CommRing R] [IsArtinianRing R] (Γ : Type u) [Ring Γ] [Algebra R Γ]
  [Module.Finite R Γ]

include R

/-- Over an Artin algebra, a finitely generated module has an injective envelope by a finitely
generated module, and the cokernel is again finitely generated. -/
private theorem exists_isEssentialMono_finite (X : ModuleCat.{u} Γ) [Module.Finite Γ X] :
    ∃ (I : ModuleCat.{u} Γ) (ι : X ⟶ I), Injective I ∧ IsEssentialMono ι ∧ Module.Finite Γ I ∧
      Module.Finite Γ (cokernel ι : ModuleCat.{u} Γ) := by
  obtain ⟨Q, _, _, _, i, hi⟩ := exists_isInjectiveEnvelope_finite R (A := Γ) X
  let ι : X ⟶ ModuleCat.of Γ Q := ModuleCat.ofHom i
  refine ⟨ModuleCat.of Γ Q, ι, IsInjectiveEnvelope.injective_obj (f := ι) hi,
    IsInjectiveEnvelope.isEssentialMono (f := ι) hi, ‹_›, ?_⟩
  exact Module.Finite.of_surjective (cokernel.π ι).hom
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- **The dominant dimension of an Artin algebra.** For an Artin `R`-algebra `Γ`, `n ≤ dom.dim Γ`
exactly when `Γ` has a coresolution `0 → Γ → I⁰ → ⋯ → Iⁿ⁻¹` by finitely generated projective and
injective modules. The minimal injective coresolution of `Γ` has finitely generated terms, and it is
a termwise retract of every injective coresolution, so it is such a coresolution as soon as
`n ≤ dom.dim Γ`. -/
theorem natCast_le_dominantDimension_iff_of_finite (n : ℕ) :
    (n : ℕ∞) ≤ dominantDimension Γ ↔
      HasCoresolution (fun M : ModuleCat.{u} Γ ↦ Module.Finite Γ M ∧ Projective M ∧ Injective M)
        (ModuleCat.of Γ Γ) n := by
  constructor
  · intro h
    obtain ⟨E, hE, ⟨e⟩, hQ⟩ := exists_isMinimalInjectiveCoresolution
      (Q := fun M : ModuleCat.{u} Γ ↦ Module.Finite Γ M)
      (fun X (_ : Module.Finite Γ X) ↦ exists_isEssentialMono_finite R Γ X) n
      (X := ModuleCat.of Γ Γ) (inferInstanceAs (Module.Finite Γ Γ))
    have hP := (hE.natCast_le_dominantDimension_iff e).1 h
    exact hasCoresolution_iff.2
      ⟨E, hE.toIsCoresolution, ⟨e⟩, fun i hi ↦ ⟨hQ i hi, hP i hi, hE.injective i hi⟩⟩
  · intro h
    obtain ⟨S, hS, e, hP⟩ := hasCoresolution_iff.1 h
    exact natCast_le_dominantDimension_iff.2
      (hasProjectiveInjectiveCoresolution_iff.2 ⟨S, hS, e, fun i hi ↦ (hP i hi).2⟩)

end Artin

end TauCeti
