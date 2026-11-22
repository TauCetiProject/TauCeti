/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Basic facts about algebraic integers

Basic facts about tuples `y : ι → 𝓞 K` of algebraic integers and their images in `K`, and about
the integers inside the ring of integers of a number field: an algebraic integer that is rational
is an integer, so `𝓞 K / ℤ` is torsion-free and `1` extends to a `ℤ`-basis of `𝓞 K`.

## Main results

* `NumberField.RingOfIntegers.coe_tuple_eq_zero_iff`: a tuple of algebraic integers is zero
  exactly when its image in `K` is zero.
* `NumberField.RingOfIntegers.exists_intCast_eq_of_coe_mem_range`: an algebraic integer that is
  rational is an integer.
* `NumberField.RingOfIntegers.exists_basis_inl_eq_one`: `1` extends to a `ℤ`-basis of `𝓞 K`,
  indexed by `Unit ⊕ Fin ([K : ℚ] - 1)`.
-/

public section

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] {ι : Type*}

/-- A tuple of algebraic integers is zero exactly when its image in `K` is zero. -/
@[simp]
theorem coe_tuple_eq_zero_iff {y : ι → 𝓞 K} : (fun i ↦ (y i : K)) = 0 ↔ y = 0 := by
  simp [funext_iff]

variable [NumberField K]

open Module

/-- An algebraic integer that is rational is an integer. -/
theorem exists_intCast_eq_of_coe_mem_range {y : 𝓞 K}
    (hy : (y : K) ∈ Set.range (algebraMap ℚ K)) : ∃ m : ℤ, (m : 𝓞 K) = y := by
  obtain ⟨q, hq⟩ := hy
  have h : IsIntegral ℤ (algebraMap ℚ K q) := hq ▸ isIntegral_coe y
  have hint : IsIntegral ℤ q := isIntegral_algebraMap_iff.mp h
  obtain ⟨m, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨m, ext (by simpa using hq)⟩

variable (K) in
/-- **`1` extends to a `ℤ`-basis of `𝓞 K`.** Since `𝓞 K ∩ ℚ = ℤ`, the quotient `𝓞 K / ℤ` is
torsion-free, hence free of rank `[K : ℚ] - 1`, and lifting a basis of it completes `1` to a basis
of `𝓞 K`. -/
theorem exists_basis_inl_eq_one :
    ∃ e : Basis (Unit ⊕ Fin (finrank ℚ K - 1)) ℤ (𝓞 K), e (Sum.inl ()) = 1 := by
  set N : Submodule ℤ (𝓞 K) := Submodule.span ℤ (Set.range fun _ : Unit ↦ (1 : 𝓞 K))
  have hN : N = ℤ ∙ (1 : 𝓞 K) := by simp [N, Set.range_const]
  have hli : LinearIndependent ℤ (fun _ : Unit ↦ (1 : 𝓞 K)) :=
    linearIndependent_unique_iff.mpr one_ne_zero
  let bN : Basis Unit ℤ N := Basis.span hli
  -- The quotient `𝓞 K / ℤ` is torsion-free: if `r y = k` with `r ≠ 0`, then `y = k / r ∈ ℤ`.
  have : IsTorsionFree ℤ (𝓞 K ⧸ N) := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦ ?_
    induction m using Submodule.Quotient.induction_on with | H y => ?_
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hN,
      Submodule.mem_span_singleton] at h
    rw [Submodule.Quotient.mk_eq_zero, hN, Submodule.mem_span_singleton]
    obtain ⟨k, hk⟩ := h
    by_cases hr : r = 0
    · exact Or.inl hr
    refine Or.inr ?_
    have hk' : (k : K) = r * y := by simpa using congr_arg ((↑) : 𝓞 K → K) hk
    obtain ⟨m, rfl⟩ := exists_intCast_eq_of_coe_mem_range (y := y) ⟨(k : ℚ) / r, by
      rw [map_div₀, map_intCast, map_intCast, hk', mul_div_cancel_left₀ _ (by exact_mod_cast hr)]⟩
    exact ⟨m, by simp⟩
  have hrank : finrank ℤ (𝓞 K ⧸ N) = finrank ℚ K - 1 := by
    have h := N.finrank_quotient_add_finrank
    rw [finrank_eq_card_basis bN, Fintype.card_unit, rank] at h
    omega
  exact ⟨bN.sumQuot (Module.finBasisOfFinrankEq ℤ _ hrank), by
    rw [Basis.sumQuot_inl, Basis.span_apply]⟩

end NumberField.RingOfIntegers
