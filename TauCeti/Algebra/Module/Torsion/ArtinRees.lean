/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.Algebra.Module.Torsion.PrimaryComponent

import Mathlib.RingTheory.Filtration
import TauCeti.RingTheory.Ideal.Operations

/-!
# Extending linear maps into primary components via Artin–Rees

Over a Noetherian commutative ring `R`, a linear map from a submodule `N` of a finitely generated
module `P` into the `𝔞`-primary component `Γ_𝔞(M)` of an `R`-module `M` factors through a
quotient by a power of `𝔞`: by Artin–Rees (`Ideal.exists_pow_inf_eq_pow_smul`), it vanishes on
`N ⊓ 𝔞 ^ m • ⊤` for sufficiently large `m`, so it extends by zero on `𝔞 ^ m • ⊤` to a linear
map on `N ⊔ 𝔞 ^ m • ⊤`.

## Main results

* `Ideal.exists_pow_smul_sup_linearMap_of_mem_primaryComponent`: extension by zero on `𝔞 ^ m • ⊤`
  for linear maps from submodules of finite modules into `𝔞`-primary components.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter III, Lemma 3.2.
* The Stacks Project, Section 47.7, Remark 47.7.9, Tag 0EGL.
-/

public section

namespace Ideal

/-- Over a Noetherian commutative ring, any linear map `g : N →ₗ[R] M` from a submodule of a finite
module `P` whose values lie in `𝔞.primaryComponent M` extends to `N ⊔ 𝔞 ^ m • ⊤` (for some `m`)
vanishing on `𝔞 ^ m • ⊤`. -/
theorem exists_pow_smul_sup_linearMap_of_mem_primaryComponent {R P M : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup P] [Module R P] [Module.Finite R P]
    [AddCommGroup M] [Module R M] (𝔞 : Ideal R) (N : Submodule R P) (g : N →ₗ[R] M)
    (hg : ∀ x, g x ∈ 𝔞.primaryComponent M) :
    ∃ (m : ℕ) (g' : ↥(N ⊔ 𝔞 ^ m • (⊤ : Submodule R P)) →ₗ[R] M),
      (∀ x (hx : x ∈ N), g' ⟨x, Submodule.mem_sup_left hx⟩ = g ⟨x, hx⟩) ∧
      (∀ y (hy : y ∈ 𝔞 ^ m • (⊤ : Submodule R P)), g' ⟨y, Submodule.mem_sup_right hy⟩ = 0) := by
  have : Module.Finite R N := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian N)
  obtain ⟨n, hn⟩ := 𝔞.exists_forall_mem_torsionBySet_pow_of_mem_primaryComponent g hg
  have hker : 𝔞 ^ n • (⊤ : Submodule R N) ≤ LinearMap.ker g :=
    Submodule.smul_le.mpr fun r hr x _ ↦ by
      rw [LinearMap.mem_ker, map_smul]
      exact (Submodule.mem_torsionBySet_iff _ _).mp (hn x) ⟨r, hr⟩
  -- By Artin–Rees, `𝔞^(n + k) • ⊤ ⊓ N ≤ 𝔞^n • N`, on which `g` vanishes.
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul 𝔞 N
  have hvanish : ∀ x : N, (x : P) ∈ 𝔞 ^ (n + k) • (⊤ : Submodule R P) → g x = 0 := fun x hx ↦ by
    have hmem : (x : P) ∈ 𝔞 ^ n • N := by
      have h := hk (n + k) (Nat.le_add_left k n)
      rw [Nat.add_sub_cancel] at h
      exact Submodule.smul_mono le_rfl inf_le_right (h.le ⟨hx, x.property⟩)
    exact hker ((Submodule.mem_smul_top_iff (𝔞 ^ n) N x).mpr hmem)
  let φ : P →ₗ.[R] M := ⟨N, g⟩
  let ψ : P →ₗ.[R] M := ⟨𝔞 ^ (n + k) • ⊤, 0⟩
  have hagree : ∀ (x : φ.domain) (y : ψ.domain), (x : P) = y → φ x = ψ y := fun x y hxy ↦
    (hvanish x (hxy ▸ y.property)).trans (LinearMap.zero_apply _).symm
  refine ⟨n + k, (φ.sup ψ hagree).toFun, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · exact (LinearPMap.sup_apply hagree ⟨x, hx⟩ 0 _ (add_zero x)).trans (by simp [φ, ψ])
  · exact (LinearPMap.sup_apply hagree 0 ⟨y, hy⟩ _ (zero_add y)).trans (by simp [φ, ψ])

end Ideal
