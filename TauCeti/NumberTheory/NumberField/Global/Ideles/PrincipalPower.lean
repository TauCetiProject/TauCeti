/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteOpenSubgroup
import Mathlib.GroupTheory.OrderOfElement
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Topology

/-!
# Principal powers of finite ideles modulo an open subgroup

For an open subgroup of the finite ideles, a single positive exponent makes every finite
idele principal modulo the subgroup. Applied to the intersection of a character's kernel
with the integral units, this gives a principal representative with both the prescribed
local valuations and the prescribed character value.
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing
open scoped NumberField

namespace NumberField

/-- Modulo an open subgroup `U` of the finite ideles, every finite idele becomes principal
on raising to a fixed positive power. The exponent may be chosen independently of the idele. -/
theorem exists_pow_div_unitEmbedding_mem_of_isOpen {K : Type*} [Field K] [NumberField K]
    {U : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ}
    (hU : IsOpen (U : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : (FiniteAdeleRing (𝓞 K) K)ˣ,
      ∃ γ : Kˣ, y ^ N / unitEmbedding (𝓞 K) K γ ∈ U := by
  let e := unitEmbedding (𝓞 K) K
  let H := U ⊔ e.range
  have hUH : U ≤ H := le_sup_left
  have heH : e.range ≤ H := le_sup_right
  have hH : H.FiniteIndex :=
    finiteIndex_of_isOpen_of_totallyPositiveUnits_le (Subgroup.isOpen_mono hUH hU)
      (fun γ _ ↦ heH ⟨γ, rfl⟩)
  refine ⟨H.index, hH.index_ne_zero.pos, fun y ↦ ?_⟩
  obtain ⟨u, hu, _, ⟨γ, rfl⟩, h⟩ := Subgroup.mem_sup.mp (H.pow_index_mem y)
  exact ⟨γ, by simpa only [← h, e, mul_div_cancel_right] using hu⟩

end NumberField

namespace MonoidHom

/-- For a homomorphism with open kernel on the finite ideles, one positive exponent makes
all ideles principal modulo the integral units in the kernel. Thus the same global element
matches both the valuations and the homomorphism value of the powered idele. -/
theorem exists_pow_eq_apply_unitEmbedding_of_isOpen_ker {K G : Type*} [Field K] [NumberField K]
    [Monoid G] (θ : (FiniteAdeleRing (𝓞 K) K)ˣ →* G)
    (hθ : IsOpen (θ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ)) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : (FiniteAdeleRing (𝓞 K) K)ˣ,
      ∃ γ : Kˣ, y ^ N / unitEmbedding (𝓞 K) K γ ∈ integralUnits (𝓞 K) K ∧
        θ y ^ N = θ (unitEmbedding (𝓞 K) K γ) := by
  have hopen : IsOpen ((integralUnits (𝓞 K) K ⊓ θ.ker :
      Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ) : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
    rw [Subgroup.coe_inf]
    exact (TauCeti.isOpen_integralUnits _ _).inter hθ
  obtain ⟨N, hN, h⟩ := NumberField.exists_pow_div_unitEmbedding_mem_of_isOpen hopen
  refine ⟨N, hN, fun y ↦ ?_⟩
  obtain ⟨γ, hγ⟩ := h y
  obtain ⟨hval, hker⟩ := Subgroup.mem_inf.mp hγ
  have he := MonoidHom.mem_ker.mp hker
  refine ⟨γ, hval, ?_⟩
  calc
    θ y ^ N = θ ((y ^ N / unitEmbedding (𝓞 K) K γ) * unitEmbedding (𝓞 K) K γ) := by
      rw [div_mul_cancel, map_pow]
    _ = θ (unitEmbedding (𝓞 K) K γ) := by rw [map_mul, he, one_mul]

end MonoidHom
