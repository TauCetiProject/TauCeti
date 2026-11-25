/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.CompletedIdeal
import TauCeti.Algebra.Algebra.NatCast

/-!
# Congruence of finite adeles

Let `R` be a Dedekind domain with fraction field `K`, write `𝔸_f` for its finite adeles and
`Ô ⊆ 𝔸_f` for the integral finite adeles. For `N ∈ R`, two finite adeles `x` and `y` are
**congruent modulo `N`** (`IsDedekindDomain.FiniteAdeleRing.ModEq N x y`) when `x - y ∈ NÔ`. For
`R = ℤ`, where `Ô = ∏_p ℤ_p` is the ring of profinite integers, this is the congruence modulo `N`
used to define the congruence subgroups of `GL₂(𝔸_f)`.

Congruence modulo `N` is `SModEq` for the `Ô`-submodule `NÔ` of `𝔸_f`, so it is an equivalence
relation compatible with addition and with multiplication by integral finite adeles, and it
passes to divisors of the modulus (`ModEq.of_dvd`). For `N ≠ 0`
it says that `(x - y) / N` is integral (`modEq_iff_inv_mul_mem`); modulo `0` it is equality
(`modEq_zero_iff`), since `0Ô = {0}`. The formula `(x - y) / N` cannot define congruence modulo
`0`: there it is `0` for every pair. For integral `x` and `y`, congruence modulo `N` is membership
of `x - y` in the completed ideal `NÔ` of `(N)` (`modEq_iff_sub_mem_completedIdeal`).

## Main declarations

* `IsDedekindDomain.FiniteAdeleRing.ModEq`: congruence modulo `N`, `x - y ∈ NÔ`.
* `IsDedekindDomain.FiniteAdeleRing.modEq_iff_inv_mul_mem`: for `N ≠ 0`, `(x - y) / N ∈ Ô`.
* `IsDedekindDomain.FiniteAdeleRing.modEq_zero_iff`: congruence modulo `0` is equality.
* `IsDedekindDomain.FiniteAdeleRing.ModEq.of_dvd`: congruence modulo `M` implies congruence
  modulo every divisor `N` of `M`.
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

/-- **Congruence of finite adeles modulo `N`**: `x - y ∈ NÔ`, congruence modulo the
`Ô`-submodule of `𝔸_f` spanned by `N`. -/
abbrev ModEq (N : R) (x y : FiniteAdeleRing R K) : Prop :=
  x ≡ y [SMOD Submodule.span (integralAdeles R K) {algebraMap R (FiniteAdeleRing R K) N}]

/-- Congruence modulo `N` says that `x - y = N z` for an integral finite adele `z`. -/
theorem modEq_iff {N : R} {x y : FiniteAdeleRing R K} :
    ModEq N x y ↔ ∃ z ∈ integralAdeles R K, x - y = algebraMap R (FiniteAdeleRing R K) N * z := by
  rw [ModEq, SModEq.sub_mem, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, z.property, by rw [← hz, Subalgebra.smul_def, smul_eq_mul, mul_comm]⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨⟨z, hz⟩, by rw [h, Subalgebra.smul_def, smul_eq_mul, mul_comm]⟩

/-- **Congruence modulo zero is equality**, since `0Ô = {0}`. -/
@[simp]
theorem modEq_zero_iff {x y : FiniteAdeleRing R K} : ModEq 0 x y ↔ x = y := by
  rw [ModEq, map_zero, Submodule.span_singleton_eq_bot.mpr rfl, SModEq.bot]

/-- **Congruence passes to divisors of the modulus**: if `N ∣ M`, then congruence modulo `M`
implies congruence modulo `N`, since `MÔ ⊆ NÔ`. -/
theorem ModEq.of_dvd {N M : R} {x y : FiniteAdeleRing R K} (h : N ∣ M) (hxy : ModEq M x y) :
    ModEq N x y := by
  obtain ⟨c, rfl⟩ := h
  refine SModEq.mono ((Submodule.span_singleton_le_iff_mem _ _).mpr
    (Submodule.mem_span_singleton.mpr ⟨⟨_, (integralAdeles R K).algebraMap_mem c⟩, ?_⟩)) hxy
  rw [Subalgebra.smul_def, smul_eq_mul, map_mul, mul_comm]

/-- **For `N ≠ 0`, congruence modulo `N` says that `(x - y) / N` is integral.** -/
theorem modEq_iff_inv_mul_mem {N : R} (hN : N ≠ 0) {x y : FiniteAdeleRing R K} :
    ModEq N x y ↔
      algebraMap K (FiniteAdeleRing R K) (algebraMap R K N)⁻¹ * (x - y) ∈ integralAdeles R K := by
  have hN' := TauCeti.algebraMap_mul_algebraMap_inv (A := FiniteAdeleRing R K)
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hN)
  rw [modEq_iff]
  constructor
  · rintro ⟨z, hz, h⟩
    rwa [h, ← mul_assoc, mul_comm _ (algebraMap R _ N), hN', one_mul]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, hN', one_mul]

/-- For integral `x` and `y`, congruence modulo `N` is membership of `x - y` in the completion
`NÔ` of the ideal `(N)`. -/
theorem modEq_iff_sub_mem_completedIdeal {N : R} (x y : integralAdeles R K) :
    ModEq N (x : FiniteAdeleRing R K) y ↔ x - y ∈ completedIdeal K (Ideal.span {N}) := by
  rw [modEq_iff, completedIdeal_def, Ideal.map_span, Set.image_singleton,
    Ideal.mem_span_singleton']
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
