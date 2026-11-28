/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.HodgeTate.Jump

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import TauCeti.NumberTheory.Padics.Complex.FixedPoints

/-!
# Hodge–Tate jumps under twists and cyclotomic powers

This file establishes how the Hodge–Tate jumps PadicComplex.hodgeTateJump and
PadicComplex.HasHodgeTateJumps transform under scalar twists of a representation, and computes
the multiset of jumps for a representation acting through a power of the p-adic cyclotomic
character.

If ρ' is obtained from ρ by multiplying by scalars  g that admit a nonzero period
y ∈ ℂ_p satisfying γ (a g) * y = χ(j g) ^ (-v) · (j g)(y) near 1, then multiplying
semilinear forms by y identifies hodgeTateMaps j ρ γ u with hodgeTateMaps j ρ' γ (u + v),
shifting the jumps by . Specializing to y = 1 and  g = χ(j g) ^ c shifts jumps by -c.
For a finite free representation on which Γ acts purely by χ(j g) ^ c, the coordinate forms of
a basis form a ℂ_p-basis of Hodge–Tate maps of weight -c, provided γ takes algebraic values.

## Main results

* PadicComplex.hodgeTateJump_twist_of_period: twisting by a scalar family with a period of
  weight -v shifts Hodge–Tate jumps by .
* PadicComplex.hodgeTateJump_twist_cyclotomic: twisting by χ ^ c shifts jumps by -c.
* PadicComplex.hasHodgeTateJumps_of_cyclotomic: a finite free representation acting by χ ^ c
  has the single jump -c with multiplicity inrank R T.

## Provenance

Adapted from New.Period.jump_twist_of_period, New.Period.jump_twist_cyclotomicGp, and
New.Period.hasJumps_of_cyclotomicGp_zpow in src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean
of grh-lean (https://github.com/lsernau/grh-lean, commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Topology Filter Module

namespace PadicComplex

variable {p : ℕ} [Fact p.Prime] {Γ R T : Type*} [Monoid Γ]

/-- If ρ' g x = a g • ρ g x and some nonzero y ∈ ℂ_p satisfies
γ (a g) * y = χ(j g) ^ (-v) · (j g)(y) for g near 1, then the multiplicity of the jump
u + v of ρ' at γ equals that of u for ρ. -/
theorem hodgeTateJump_twist_of_period [CommSemiring R] [AddCommMonoid T] [Module R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {ρ ρ' : Representation R Γ T}
    {γ : R →+* ℂ_[p]} {u v : ℤ} (a : Γ → R) {y : ℂ_[p]} (hy : y ≠ 0)
    (h_period : ∀ᶠ g in comap j (𝓝 1),
      γ (a g) * y = twist (-v) (j g).toRingEquiv * j g • y)
    (h_twist : ∀ g x, ρ' g x = a g • ρ g x) :
    hodgeTateJump j ρ' γ (u + v) = hodgeTateJump j ρ γ u := by
  let mulY : (T →ₛₗ[γ] ℂ_[p]) ≃ₗ[PadicAlgCl p] (T →ₛₗ[γ] ℂ_[p]) :=
    (LinearEquiv.smulOfNeZero ℂ_[p] (T →ₛₗ[γ] ℂ_[p]) y hy).restrictScalars (PadicAlgCl p)
  have h_iff (F : T →ₛₗ[γ] ℂ_[p]) :
      y • F ∈ hodgeTateMaps j ρ' γ (u + v) ↔ F ∈ hodgeTateMaps j ρ γ u := by
    simp only [mem_hodgeTateMaps]
    refine forall_congr' fun x ↦ eventually_congr (h_period.mono fun g hg ↦ ?_)
    set c : ℂ_[p] := twist (-v) (j g).toRingEquiv * j g • y
    have hc : c ≠ 0 := mul_ne_zero (twist_ne_zero _ _) ((smul_eq_zero_iff_eq (j g)).not.mpr hy)
    have hlhs : (y • F) (ρ' g x) = c * F (ρ g x) := by
      simp only [LinearMap.smul_apply, smul_eq_mul, h_twist, map_smulₛₗ, c, ← hg]
      ring
    have hrhs : twist (-(u + v)) (j g).toRingEquiv * j g • (y • F) x =
        c * (twist (-u) (j g).toRingEquiv * j g • F x) := by
      rw [neg_add, twist_add]
      simp only [LinearMap.smul_apply, smul_eq_mul, smul_mul', c]
      ring
    rw [hlhs, hrhs, mul_right_inj' hc]
  have h_comap : (hodgeTateMaps j ρ' γ (u + v)).comap mulY.toLinearMap =
      hodgeTateMaps j ρ γ u := Submodule.ext h_iff
  rw [hodgeTateJump_def, hodgeTateJump_def]
  exact LinearEquiv.finrank_eq ((mulY.ofSubmodule' _).symm ≪≫ₗ LinearEquiv.ofEq _ _ h_comap)

/-- Twisting a representation ρ by the c-th power of the p-adic cyclotomic character shifts
the Hodge–Tate jump u to u - c. -/
theorem hodgeTateJump_twist_cyclotomic [CommSemiring R] [Algebra ℤ_[p] R] [AddCommMonoid T]
    [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} {ρ ρ' : Representation R Γ T}
    {γ : R →+* ℂ_[p]}
    (hγ : ∀ z : ℤ_[p], γ (algebraMap ℤ_[p] R z) = algebraMap ℚ_[p] ℂ_[p] (z : ℚ_[p]))
    (u c : ℤ)
    (h_twist : ∀ g x, ρ' g x =
      ((cyclotomicCharacter (PadicAlgCl p) p (j g).toRingEquiv ^ c : ℤ_[p]ˣ) : ℤ_[p]) •
        ρ g x) :
    hodgeTateJump j ρ' γ (u - c) = hodgeTateJump j ρ γ u := by
  rw [sub_eq_add_neg]
  refine hodgeTateJump_twist_of_period
    (fun g ↦ algebraMap ℤ_[p] R
      ((cyclotomicCharacter (PadicAlgCl p) p (j g).toRingEquiv ^ c : ℤ_[p]ˣ) : ℤ_[p]))
    one_ne_zero (.of_forall fun g ↦ ?_) fun g x ↦ by
      rw [algebraMap_smul, h_twist g x]
  simp [hγ, twist_def]

/-- Let the image of j be a neighbourhood of 1, and let T be a finite free R-module on
which Γ acts through the c-th power of the p-adic cyclotomic character. If γ : R →+* ℂ_p
is compatible with ℤ_p → ℂ_p and takes algebraic values, then the only Hodge–Tate jump at γ is
-c, with multiplicity inrank R T. -/
theorem hasHodgeTateJumps_of_cyclotomic [CommRing R] [Algebra ℤ_[p] R] [AddCommGroup T]
    [Module R T] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [Module.Finite R T] [Module.Free R T]
    {j : Γ →* (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)} (hj : Set.range j ∈ 𝓝 1)
    {ρ : Representation R Γ T} (γ : R →+* ℂ_[p])
    (hγ_zp : ∀ z : ℤ_[p], γ (algebraMap ℤ_[p] R z) = algebraMap ℚ_[p] ℂ_[p] (z : ℚ_[p]))
    (hγ_alg : ∀ r : R, γ r ∈ Set.range ((↑) : PadicAlgCl p → ℂ_[p])) (c : ℤ)
    (h : ∀ g x, ρ g x =
      ((cyclotomicCharacter (PadicAlgCl p) p (j g).toRingEquiv ^ c : ℤ_[p]ˣ) : ℤ_[p]) • x) :
    HasHodgeTateJumps j ρ γ (Multiset.replicate (finrank R T) (-c)) := by
  have : Nontrivial R := γ.domain_nontrivial
  let e : Basis (Fin (finrank R T)) R T := finBasis R T
  let eval : (T →ₛₗ[γ] ℂ_[p]) ≃ₗ[ℂ_[p]] Fin (finrank R T) → ℂ_[p] :=
    LinearEquiv.ofBijective (LinearMap.pi fun i ↦ LinearMap.id.flip (e i)) <| by
      refine ⟨fun f g hfg ↦ e.ext (congrFun hfg), fun v ↦ ?_⟩
      let : Algebra R ℂ_[p] := γ.toAlgebra
      exact ⟨⟨(e.constr ℕ v).toAddHom, (e.constr ℕ v).map_smul'⟩, funext (e.constr_basis ℕ v)⟩
  let b : Basis (Fin (finrank R T)) ℂ_[p] (T →ₛₗ[γ] ℂ_[p]) := Basis.ofEquivFun eval
  have hb (i : Fin (finrank R T)) : b i ∈ hodgeTateMaps j ρ γ (-c) := by
    rw [mem_hodgeTateMaps]
    intro x
    have hfix : ∀ᶠ g in comap j (𝓝 1), j g • (b i x) = b i x := by
      have hbi (k : Fin (finrank R T)) : b i (e k) = if k = i then 1 else 0 := by
        change eval (b i) k = if k = i then 1 else 0
        simp [b, Pi.single_apply, eq_comm]
      have hbx : b i x = γ (e.repr x i) := by
        rw [← e.sum_repr x, map_sum]
        simp [map_smulₛₗ, hbi]
      rw [hbx]
      exact (mem_range_coe_iff_eventually_smul_eq.mp (hγ_alg (e.repr x i))).comap j
    filter_upwards [hfix] with g hg
    have hact : ρ g x =
        algebraMap ℤ_[p] R
          ((cyclotomicCharacter (PadicAlgCl p) p (j g).toRingEquiv ^ c : ℤ_[p]ˣ) : ℤ_[p]) • x := by
      rw [algebraMap_smul, h g x]
    rw [hact, map_smulₛₗ, hg, neg_neg, hγ_zp, twist_def]
    rfl
  simpa using hasHodgeTateJumps_of_basis hj b hb

end PadicComplex
