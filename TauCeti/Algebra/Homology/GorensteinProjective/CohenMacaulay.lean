/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Presentation
public import TauCeti.RingTheory.CohenMacaulay.Ring
import Mathlib.RingTheory.LocalRing.Module

/-!
# Depth and Cohen–Macaulayness of Gorenstein-projective modules

Over a commutative local ring `R`, inducting along projective copresentations
(`TauCeti.IsGorensteinProjective.exists_projectiveCopresentation`) gives `depth R ≤ depth M` for
every Gorenstein-projective `R`-module `M` without Noetherian hypotheses (`depth_self_le_depth`).
Over a Cohen–Macaulay local ring `R`, every Gorenstein-projective `R`-module satisfies
`ringKrullDim R ≤ depth M` (`ringKrullDim_le_depth`), is Cohen–Macaulay (`isCohenMacaulay`), and has
`depth M = ringKrullDim R` when nontrivial (`depth_eq_ringKrullDim`).

## References

* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Lemma 4.2.2.
* E. E. Enochs and O. M. G. Jenda, *Relative Homological Algebra*, Theorem 10.2.14.
* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Section 3.3.
-/

public section

universe v u

open CategoryTheory

namespace TauCeti.IsGorensteinProjective

section LocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- Over a commutative local ring `R`, every Gorenstein-projective module `M` satisfies
`depth R ≤ depth M`. -/
theorem depth_self_le_depth {M : ModuleCat.{v} R} (hM : IsGorensteinProjective R M) :
    IsLocalRing.depth (ModuleCat.of R R) ≤ IsLocalRing.depth M := by
  have bound (k : ℕ) (hk : (k : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of R R)) :
      ∀ {N : ModuleCat.{v} R}, IsGorensteinProjective R N → (k : ℕ∞) ≤ IsLocalRing.depth N := by
    induction k with
    | zero => intro _ _; exact zero_le
    | succ k ih =>
      intro N hN; obtain ⟨T, hT, ⟨e⟩, _, hP, hQ⟩ := hN.exists_projectiveCopresentation
      have hX₂ : IsLocalRing.depth (ModuleCat.of R R) ≤ IsLocalRing.depth T.X₂ := by
        cases subsingleton_or_nontrivial T.X₂
        · rw [IsLocalRing.depth_eq_top_of_subsingleton T.X₂]; exact le_top
        · have : Module.Projective R T.X₂ := (IsProjective.iff_projective T.X₂).2 hP
          have : Module.Free R T.X₂ := Module.free_of_flat_of_isLocalRing
          exact (IsLocalRing.depth_eq_depth_self_of_free T.X₂).ge
      have hX₃ : (k : ℕ∞) + 1 ≤ IsLocalRing.depth T.X₃ + 1 :=
        add_le_add_left (ih ((Nat.cast_le.2 (Nat.le_succ k)).trans hk) hQ) 1
      have hex := IsLocalRing.depth_min_snd_trd_add_one_le_fst_of_exact T.f.hom T.g.hom
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact T).1 hT.exact)
        ((ModuleCat.mono_iff_injective T.f).1 hT.mono_f)
        ((ModuleCat.epi_iff_surjective T.g).1 hT.epi_g)
      rw [← IsLocalRing.depth_eq_of_linearEquiv e.toLinearEquiv]
      exact (le_inf (hk.trans hX₂) (by simpa [Nat.cast_add, Nat.cast_one] using hX₃)).trans hex
  induction hm : IsLocalRing.depth M using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    induction hr : IsLocalRing.depth (ModuleCat.of R R) using ENat.recTopCoe with
    | top =>
      have := bound (m + 1) (by simp [hr]) hM; rw [hm] at this; norm_cast at this; omega
    | coe r => rw [← hm]; exact bound r hr.ge hM

end LocalRing

section CohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.IsCohenMacaulay R] [Small.{v} R]

/-- Over a Cohen–Macaulay local ring `R`, every Gorenstein-projective module `M` satisfies
`ringKrullDim R ≤ depth M`. -/
theorem ringKrullDim_le_depth {M : ModuleCat.{v} R} (hM : IsGorensteinProjective R M) :
    ringKrullDim R ≤ (IsLocalRing.depth M : WithBot ℕ∞) := by
  have hCM : Module.IsCohenMacaulay R R := Ring.isCohenMacaulay_iff_of_isLocalRing.mp inferInstance
  rw [← Module.supportDim_self_eq_ringKrullDim, ← hCM.depth_eq]
  exact WithBot.coe_le_coe.mpr hM.depth_self_le_depth

/-- Over a Cohen–Macaulay local ring `R`, every nontrivial Gorenstein-projective module `M` has
depth equal to `ringKrullDim R`. -/
theorem depth_eq_ringKrullDim {M : ModuleCat.{v} R} (hM : IsGorensteinProjective R M)
    [Nontrivial M] : (IsLocalRing.depth M : WithBot ℕ∞) = ringKrullDim R := by
  have := hM.finite
  exact le_antisymm (IsLocalRing.depth_le_supportDim.trans (Module.supportDim_le_ringKrullDim R M))
    hM.ringKrullDim_le_depth

/-- Over a Cohen–Macaulay local ring `R`, every Gorenstein-projective module is Cohen–Macaulay. -/
theorem isCohenMacaulay {M : ModuleCat.{v} R} (hM : IsGorensteinProjective R M) :
    Module.IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact Module.isCohenMacaulay_of_subsingleton
  have := hM.finite
  exact Module.isCohenMacaulay_iff_supportDim_le_depth.mpr
    ((Module.supportDim_le_ringKrullDim R M).trans hM.ringKrullDim_le_depth)

end CohenMacaulay

end TauCeti.IsGorensteinProjective
