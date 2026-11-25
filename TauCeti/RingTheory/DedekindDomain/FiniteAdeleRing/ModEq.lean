/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal

/-!
# Congruence of finite adeles

Let `R` be a Dedekind domain with fraction field `K`, write `𝔸_f` for its finite adeles and
`Ô ⊆ 𝔸_f` for the integral finite adeles. For `N ∈ R`, two finite adeles `x` and `y` are
**congruent modulo `N`** (`IsDedekindDomain.FiniteAdeleRing.ModEq N x y`) when `x - y ∈ NÔ`. For
`R = ℤ`, where `Ô = ∏_p ℤ_p` is the ring of profinite integers, this is the congruence modulo `N`
used to define the congruence subgroups of `GL₂(𝔸_f)`.

Congruence modulo `N` is an equivalence relation compatible with addition and with multiplication
by integral finite adeles. For `N ≠ 0` it says that `(x - y) / N` is integral
(`ModEq.iff_mul_inv_mem`); modulo `0` it is equality (`modEq_zero_iff`), since `0Ô = {0}`. The
formula `(x - y) / N` cannot define congruence modulo `0`: there it is `0` for every pair. For
integral `x` and `y`, congruence modulo `N` is membership of `x - y` in the completed ideal
`NÔ` of `(N)` (`modEq_iff_sub_mem_completedIdeal`).

## Main declarations

* `IsDedekindDomain.FiniteAdeleRing.ModEq`: congruence modulo `N`, `x - y ∈ NÔ`.
* `IsDedekindDomain.FiniteAdeleRing.modEq_iff_mul_inv_mem`: for `N ≠ 0`, `(x - y) / N ∈ Ô`.
* `IsDedekindDomain.FiniteAdeleRing.modEq_zero_iff`: congruence modulo `0` is equality.
* `IsDedekindDomain.FiniteAdeleRing.modEq_iff_sub_mem_completedIdeal`: the comparison with
  `completedIdeal`.

## References

* J. S. Milne, *Introduction to Shimura varieties*, §4, definition of congruence subgroups, p. 42.
-/

public section

noncomputable section

namespace IsDedekindDomain.FiniteAdeleRing

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Congruence of finite adeles modulo `N`**: `x - y ∈ NÔ`, that is `x - y = N z` for an
integral finite adele `z`. -/
def ModEq (N : R) (x y : FiniteAdeleRing R K) : Prop :=
  ∃ z ∈ integralAdeles R K, x - y = algebraMap R (FiniteAdeleRing R K) N * z

theorem modEq_iff {N : R} {x y : FiniteAdeleRing R K} :
    ModEq N x y ↔ ∃ z ∈ integralAdeles R K, x - y = algebraMap R (FiniteAdeleRing R K) N * z :=
  Iff.rfl

namespace ModEq

variable {N : R} {x y w : FiniteAdeleRing R K}

@[refl]
protected theorem refl (N : R) (x : FiniteAdeleRing R K) : ModEq N x x :=
  ⟨0, zero_mem _, by simp⟩

protected theorem symm (h : ModEq N x y) : ModEq N y x := by
  obtain ⟨z, hz, h⟩ := h
  exact ⟨-z, neg_mem hz, by rw [mul_neg, ← h, neg_sub]⟩

protected theorem trans (h₁ : ModEq N x y) (h₂ : ModEq N y w) : ModEq N x w := by
  obtain ⟨z₁, hz₁, h₁⟩ := h₁
  obtain ⟨z₂, hz₂, h₂⟩ := h₂
  exact ⟨z₁ + z₂, add_mem hz₁ hz₂, by rw [mul_add, ← h₁, ← h₂, sub_add_sub_cancel]⟩

/-- Congruence modulo `N` is an equivalence relation. -/
protected theorem equivalence (N : R) : Equivalence (ModEq (K := K) N) :=
  ⟨ModEq.refl N, ModEq.symm, ModEq.trans⟩

protected theorem add {x' y' : FiniteAdeleRing R K} (h : ModEq N x y) (h' : ModEq N x' y') :
    ModEq N (x + x') (y + y') := by
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨z', hz', h'⟩ := h'
  exact ⟨z + z', add_mem hz hz', by rw [mul_add, ← h, ← h', add_sub_add_comm]⟩

/-- Congruence modulo `N` is compatible with multiplication by integral finite adeles. -/
protected theorem mul_left {c : FiniteAdeleRing R K} (hc : c ∈ integralAdeles R K)
    (h : ModEq N x y) : ModEq N (c * x) (c * y) := by
  obtain ⟨z, hz, h⟩ := h
  exact ⟨c * z, mul_mem hc hz, by rw [← mul_sub, h, mul_left_comm]⟩

end ModEq

/-- **Congruence modulo zero is equality**, since `0Ô = {0}`. -/
@[simp]
theorem modEq_zero_iff {x y : FiniteAdeleRing R K} : ModEq 0 x y ↔ x = y := by
  refine ⟨fun ⟨z, _, h⟩ ↦ ?_, fun h ↦ h ▸ ModEq.refl 0 x⟩
  rwa [map_zero, zero_mul, sub_eq_zero] at h

/-- **For `N ≠ 0`, congruence modulo `N` says that `(x - y) / N` is integral.** -/
theorem modEq_iff_mul_inv_mem {N : R} (hN : N ≠ 0) {x y : FiniteAdeleRing R K} :
    ModEq N x y ↔
      algebraMap K (FiniteAdeleRing R K) (algebraMap R K N)⁻¹ * (x - y) ∈ integralAdeles R K := by
  have hNK : algebraMap R K N ≠ 0 :=
    (IsFractionRing.injective R K).ne_iff' (map_zero _) |>.mpr hN
  have hunit : algebraMap R (FiniteAdeleRing R K) N *
      algebraMap K (FiniteAdeleRing R K) (algebraMap R K N)⁻¹ = 1 := by
    rw [IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K), ← map_mul,
      mul_inv_cancel₀ hNK, map_one]
  constructor
  · rintro ⟨z, hz, h⟩
    rwa [h, ← mul_assoc, mul_comm _ (algebraMap R _ N), hunit, one_mul]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, hunit, one_mul]

/-- For integral `x` and `y`, congruence modulo `N` is membership of `x - y` in the completion
`NÔ` of the ideal `(N)`. -/
theorem modEq_iff_sub_mem_completedIdeal {N : R} (x y : integralAdeles R K) :
    ModEq N (x : FiniteAdeleRing R K) y ↔ x - y ∈ completedIdeal K (Ideal.span {N}) := by
  rw [completedIdeal_def, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz, h⟩
    refine ⟨⟨z, hz⟩, Subtype.ext ?_⟩
    simp [h, mul_comm]
  · rintro ⟨z, hz⟩
    refine ⟨z, z.property, ?_⟩
    have := congrArg Subtype.val hz
    simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, Subalgebra.coe_sub] at this
    rw [← this, mul_comm]

end IsDedekindDomain.FiniteAdeleRing
