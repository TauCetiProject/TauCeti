/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.AdicSystem
public import Mathlib.Algebra.Module.Projective
import TauCeti.Algebra.Module.Projective.Lift
import TauCeti.LinearAlgebra.Quotient.Map
import TauCeti.RingTheory.AdicCompletion.Finite

/-!
# Projectivity of limits of adic systems

An adic system of projective modules over the successive quotient rings, whose bottom module
is finite, has a finite projective limit over an adically complete ring. The finite generation
and reduction properties of that limit are supplied by `ModuleTower.IsAdicSystem.finite_lim`
and `ModuleTower.IsAdicSystem.ker_limπ`.

## References

* The Stacks Project, Lemma 15.13.4, tag 0D4B.
-/

public section

namespace TauCeti.ModuleTower.IsAdicSystem

open Opposite

universe u v w z

variable {R : Type u} [CommRing R] (I : Ideal R)
  {P : Type v} [AddCommGroup P] [Module R P]
  {A : Type w} [AddCommGroup A] [Module R A]
  {B : Type z} [AddCommGroup B] [Module R B]

private theorem ker_stage (n : ℕ)
    [Module (R ⧸ I ^ (n + 2)) B] [IsScalarTower R (R ⧸ I ^ (n + 2)) B]
    [Module.Projective (R ⧸ I ^ (n + 2)) B]
    (f : B →ₗ[R] A) (g : P →ₗ[R] A) (h : P →ₗ[R] B)
    (hg : Function.Surjective g) (hgk : LinearMap.ker g = I ^ (n + 1) • ⊤)
    (hfk : LinearMap.ker f = I ^ (n + 1) • ⊤) (hfg : f.comp h = g) :
    LinearMap.ker h = I ^ (n + 2) • ⊤ := by
  let K : Submodule R P := I ^ (n + 2) • ⊤
  let J := (I ^ (n + 1)).map (Ideal.Quotient.mk (I ^ (n + 2)))
  have hkill : K ≤ LinearMap.ker h := by
    refine Submodule.smul_le.mpr fun r hr x _ ↦ ?_
    rw [LinearMap.mem_ker, h.map_smul,
      ← IsScalarTower.algebraMap_smul (R ⧸ I ^ (n + 2)) r (h x)]
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  let hb := (K.liftQ h hkill).extendScalarsOfSurjective
    (S := R ⧸ I ^ (n + 2)) Ideal.Quotient.mk_surjective
  have hb_mk (p : P) : hb (Submodule.Quotient.mk p) = h p := by
    rw [LinearMap.extendScalarsOfSurjective_apply, Submodule.liftQ_apply]
  have hmem (y : B) : y ∈ J • (⊤ : Submodule (R ⧸ I ^ (n + 2)) B) ↔ f y = 0 := by
    dsimp only [J]
    rw [Submodule.mem_map_quotient_mk_smul_top_iff, ← hfk, LinearMap.mem_ker]
  have hbij : Function.Bijective hb := by
    have hJ : IsNilpotent J := by
      refine ⟨2, ?_⟩
      dsimp only [J]
      rw [← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot]
      exact Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
    apply Ideal.bijective_of_mapQ_bijective J hJ
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_antisymm _ bot_le
      intro x hx
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule _ (P ⧸ K))) x
      obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective K x
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      apply (Submodule.Quotient.mk_mem_map_quotient_mk_smul_top_iff
        (Ideal.pow_le_pow_right (by omega)) p).mpr
      rw [← hgk, LinearMap.mem_ker]
      have hx' : h p ∈ J • (⊤ : Submodule (R ⧸ I ^ (n + 2)) B) := by
        simpa only [LinearMap.mem_ker, Submodule.mapQ_apply, hb_mk,
          Submodule.Quotient.mk_eq_zero] using hx
      exact (LinearMap.congr_fun hfg p).symm.trans ((hmem _).mp hx')
    · intro y
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (J • (⊤ : Submodule _ B)) y
      obtain ⟨p, hp⟩ := hg (f y)
      refine ⟨Submodule.Quotient.mk (Submodule.Quotient.mk p), ?_⟩
      rw [Submodule.mapQ_apply, hb_mk]
      apply (Submodule.Quotient.eq _).mpr
      apply (hmem _).mpr
      simp only [map_sub]
      exact sub_eq_zero.mpr ((LinearMap.congr_fun hfg p).trans hp)
  refine le_antisymm (fun p hp ↦ (Submodule.Quotient.mk_eq_zero K).mp ?_) hkill
  apply hbij.injective
  simpa only [hb_mk, map_zero] using LinearMap.mem_ker.mp hp

variable {I} {F : ModuleTower.{v} R} (hF : F.IsAdicSystem I)
  [Module.Finite R (F.obj (op 0))]

variable [IsAdicComplete I R]

/-- The inverse limit of a finite adic system of projective quotient-ring modules is
projective over the complete base ring, without a Noetherian hypothesis. -/
theorem projective_lim
    (hproj : ∀ n, Module.Projective (R ⧸ I ^ (n + 1)) (hF.levelModule n)) :
    Module.Projective R F.lim := by
  let (n : ℕ) := (hF.isTorsionBySet_obj n).module
  have (n : ℕ) := (hF.isTorsionBySet_obj n).isScalarTower (S := R)
  have (n : ℕ) : Module.Projective (R ⧸ I ^ (n + 1)) (F.obj (op n)) := hproj n
  have : Module.Finite (R ⧸ I ^ (0 + 1)) (F.obj (op 0)) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ I ^ (0 + 1)) _
  have : IsAdicComplete (I ^ (0 + 1)) R := by simpa using (inferInstance : IsAdicComplete I R)
  obtain ⟨P, hAdd, hMod, hfin, hprojective, g0, hg0s, hg0k⟩ :=
    TauCeti.exists_finite_projective_lift (I ^ (0 + 1)) (F.obj (op 0))
  let := hAdd
  let := hMod
  let := hfin
  let := hprojective
  let : IsAdicComplete I P := IsAdicComplete.of_finite_projective I P
  obtain ⟨g, hg⟩ := Module.projective_lifting_property (F.limπ 0) g0
    (F.limπ_surjective hF.transition_surjective 0)
  let gn (n : ℕ) := (F.limπ n).comp g
  have hg0 : gn 0 = g0 := hg
  have hgns (n : ℕ) : Function.Surjective (gn n) :=
    hF.surjective_limπ_comp (hg ▸ hg0s) n
  have hgnk (n : ℕ) : LinearMap.ker (gn n) = I ^ (n + 1) • ⊤ := by
    induction n with
    | zero => exact hg0 ▸ hg0k
    | succ n ih =>
      exact ker_stage I n (F.transition n) (gn n) (gn (n + 1))
        (hgns n) ih (hF.ker_transition n) (by
          dsimp [gn]
          rw [← LinearMap.comp_assoc, F.transition_comp_limπ])
  have hgs : Function.Surjective g :=
    hF.surjective_of_surjective_limπ_zero_comp (hg ▸ hg0s)
  have hgi : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm _ bot_le
    intro p hp
    apply (Submodule.mem_bot R).mpr
    apply (IsHausdorff.eq_iff_smodEq (I := I)).2
    intro n
    apply SModEq.sub_mem.2
    rw [sub_zero]
    apply Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega : n ≤ n + 1))
    rw [← hgnk n, LinearMap.mem_ker]
    simp only [gn, LinearMap.comp_apply, LinearMap.mem_ker.mp hp, map_zero]
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective g ⟨hgi, hgs⟩)

end TauCeti.ModuleTower.IsAdicSystem
