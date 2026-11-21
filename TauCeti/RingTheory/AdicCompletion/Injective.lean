/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import TauCeti.RingTheory.AdicCompletion.Torsion
import TauCeti.RingTheory.AdicCompletion.Algebra
import TauCeti.RingTheory.Ideal.ArtinRees

/-!
# Injective ideal-power-torsion modules over the completion

Let `I` be a finitely generated ideal of a commutative ring `R` whose `I`-adic completion
`R̂ = AdicCompletion I R` is Noetherian. If `E` is an injective `R`-module in which every element
is killed by a power of `I`, equipped with a compatible `R̂`-action (such as
`TauCeti.AdicCompletion.torsionModule`), then `E` remains an injective `R̂`-module
(`TauCeti.AdicCompletion.moduleInjective_of_primaryComponent`).

## Main results

* `TauCeti.AdicCompletion.moduleInjective_of_primaryComponent`: injectivity transfers from `R` to
  `AdicCompletion I R` for `I`-power-torsion modules when `I` is finitely generated and
  `AdicCompletion I R` is Noetherian.

## References

* The Stacks Project, Section 47.7, Remark 47.7.9, Tag 0EGL.
-/

public section

noncomputable section

namespace TauCeti.AdicCompletion

open _root_.AdicCompletion

universe u v

/-- **An `I`-power-torsion injective module remains injective over the `I`-adic completion.**
Let `I` be a finitely generated ideal whose completion `R̂ = AdicCompletion I R` is Noetherian.
If `E` is an injective `R`-module in which every element is killed by a power of `I`, equipped
with a compatible `R̂`-action (such as `torsionModule`), then `E` is an injective `R̂`-module. -/
theorem moduleInjective_of_primaryComponent {R : Type u} [CommRing R] {I : Ideal R}
    {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R] [Module.Injective R E]
    [Module (_root_.AdicCompletion I R) E] [IsScalarTower R (_root_.AdicCompletion I R) E]
    (hI : I.FG) (hE : ∀ x : E, x ∈ I.primaryComponent E)
    [IsNoetherianRing (_root_.AdicCompletion I R)] :
    Module.Injective (_root_.AdicCompletion I R) E := by
  let Rhat := _root_.AdicCompletion I R
  let Ihat : Ideal Rhat := I.map (algebraMap R Rhat)
  refine Module.Baer.injective fun J g ↦ ?_
  -- Extend `g` by zero on some `Î^m`, then to an `R`-linear map `h : R̂ → E` by `R`-injectivity.
  obtain ⟨m, g₁, hg₁J, hg₁I⟩ :=
    Ihat.exists_pow_smul_sup_linearMap_of_mem_primaryComponent (J : Submodule Rhat Rhat) g
      fun _ ↦ (I.mem_primaryComponent_map_iff (S := Rhat)).mpr (hE _)
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R E _ Rhat
    ((J ⊔ Ihat ^ m • (⊤ : Submodule Rhat Rhat) : Submodule Rhat Rhat).restrictScalars R).subtype
    (Submodule.injective_subtype _) (g₁.restrictScalars R)
  have hhJ : ∀ x (hx : x ∈ J), h x = g ⟨x, hx⟩ := fun x hx ↦
    (LinearMap.congr_fun hh ⟨x, Submodule.mem_sup_left hx⟩).trans (hg₁J x hx)
  have hhI : ∀ c ∈ Ihat ^ m, h c = 0 := fun c hc ↦ by
    have hc' : c ∈ Ihat ^ m • (⊤ : Submodule Rhat Rhat) := by rwa [Ideal.smul_eq_mul, Ideal.mul_top]
    exact (LinearMap.congr_fun hh ⟨c, Submodule.mem_sup_right hc'⟩).trans (hg₁I c hc')
  -- Since `h` vanishes on `Î^m`, every value of `h` is killed by `I^m`, so `h` is `R̂`-linear.
  have hsmul : ∀ (a b : Rhat), h (a • b) = a • h b := fun a b ↦ by
    have hb : h b ∈ Submodule.torsionBySet R E ↑(I ^ m) := by
      refine (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨s, hs⟩ ↦ ?_
      dsimp only
      rw [← h.map_smul, Algebra.smul_def]
      exact hhI _ (Ideal.mul_mem_right b _
        (Ideal.map_pow (algebraMap R Rhat) I m ▸ Ideal.mem_map_of_mem _ hs))
    obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_map_pow hI m a
    have hzero : h ((a - algebraMap R Rhat r) * b) = 0 :=
      hhI _ (Ideal.mul_mem_right b _ (Ideal.map_pow (algebraMap R Rhat) I m ▸ hr))
    have hzero' : (a - algebraMap R Rhat r) • h b = 0 :=
      (Submodule.mem_torsionBySet_iff _ _).mp
        ((Submodule.mem_torsionBySet_map_iff (S := Rhat) (I ^ m)).mpr hb) ⟨_, hr⟩
    have hlhs : h (a • b) = r • h b := by
      rw [smul_eq_mul, ← sub_add_cancel a (algebraMap R Rhat r), add_mul, map_add, hzero, zero_add,
        ← Algebra.smul_def, map_smul]
    have hrhs : a • h b = r • h b := by
      rw [← sub_eq_zero, ← algebraMap_smul Rhat r (h b), ← sub_smul]
      exact hzero'
    exact hlhs.trans hrhs.symm
  exact ⟨{ h with map_smul' := hsmul }, hhJ⟩

end TauCeti.AdicCompletion
