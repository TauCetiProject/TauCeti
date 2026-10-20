/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries

/-!
# The lattices `U_a` of Laurent series

For a module `V` over a semiring `R`, this file defines the `R`-submodules

`U_a(V) = Xᵃ V⟦X⟧ = {f | f.coeff n = 0 for all n < a}`

of `V`-valued Laurent series `HahnSeries ℤ V`. They decrease in `a`, exhaust all series and meet
in `0`. For `V = R` they are the translates `Xᵃ R⟦X⟧` of the power series, they multiply as
`U_a U_b ⊆ U_{a + b}`, and over a field they are the closed balls of the valuation topology.

## Main definitions

* `TauCeti.LaurentSeries.lattice R V a`: the `R`-submodule `U_a(V)`.

## Main results

* `TauCeti.LaurentSeries.single_mem_lattice_iff`: the monomial `v Xⁿ` lies in `U_a(V)` exactly
  when `v = 0` or `a ≤ n`.
* `TauCeti.LaurentSeries.iSup_lattice`, `TauCeti.LaurentSeries.iInf_lattice`: the lattices
  exhaust all series and meet in `0`.
* `TauCeti.LaurentSeries.mem_lattice_iff_exists`: `U_a(R) = Xᵃ R⟦X⟧`.
* `TauCeti.LaurentSeries.mul_mem_lattice`: `U_a U_b ⊆ U_{a + b}`.
* `TauCeti.LaurentSeries.mem_lattice_iff_valuation_le`: over a field, `U_a` is a closed
  valuation ball.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace TauCeti.LaurentSeries

section Module

variable (R V : Type*) [Semiring R] [AddCommMonoid V] [Module R V]

/-- The lattice `U_a(V) = Xᵃ V⟦X⟧` of `V`-valued Laurent series whose coefficients vanish at
every exponent below `a`, as an `R`-submodule of `HahnSeries ℤ V`. -/
def lattice (a : ℤ) : Submodule R (HahnSeries ℤ V) where
  carrier := {f | ∀ n < a, f.coeff n = 0}
  add_mem' hf hg n hn := by rw [coeff_add, hf n hn, hg n hn, add_zero]
  zero_mem' _ _ := coeff_zero
  smul_mem' r f hf n hn := by rw [coeff_smul, hf n hn, smul_zero]

variable {R V}

/-- Membership in `U_a(V)` is the vanishing of every coefficient below `a`. -/
theorem mem_lattice_iff {a : ℤ} {f : HahnSeries ℤ V} :
    f ∈ lattice R V a ↔ ∀ n < a, f.coeff n = 0 :=
  Iff.rfl

/-- Membership in `U_a(V)` is the order bound `a ≤ ord f`. -/
theorem mem_lattice_iff_le_orderTop {a : ℤ} {f : HahnSeries ℤ V} :
    f ∈ lattice R V a ↔ (a : WithTop ℤ) ≤ f.orderTop := by
  rw [mem_lattice_iff, le_orderTop_iff_forall]
  simp only [WithTop.coe_lt_coe]

/-- A series in `U_a(V)` has zero coefficient at every exponent below `a`. -/
theorem coeff_eq_zero_of_mem_lattice {a n : ℤ} {f : HahnSeries ℤ V} (hf : f ∈ lattice R V a)
    (hn : n < a) : f.coeff n = 0 :=
  hf n hn

/-- The monomial `v Xⁿ` lies in `U_a(V)` once `a ≤ n`. -/
theorem single_mem_lattice {a n : ℤ} (h : a ≤ n) (v : V) : single n v ∈ lattice R V a :=
  fun _ hm ↦ coeff_single_of_ne (by omega)

/-- The monomial `v Xⁿ` lies in `U_a(V)` exactly when `v = 0` or `a ≤ n`. -/
@[simp]
theorem single_mem_lattice_iff {a n : ℤ} {v : V} : single n v ∈ lattice R V a ↔ v = 0 ∨ a ≤ n := by
  refine ⟨fun h ↦ or_iff_not_imp_right.mpr fun hn ↦ ?_, ?_⟩
  · simpa using h n (not_le.mp hn)
  · rintro (rfl | h)
    · rw [single_eq_zero]
      exact zero_mem _
    · exact single_mem_lattice h v

/-- The lattices decrease as the exponent bound increases. -/
theorem lattice_antitone : Antitone (lattice R V) :=
  fun _ _ h _ hf n hn ↦ hf n (hn.trans_le h)

/-- For a nontrivial module `V`, `U_b(V) ⊆ U_a(V)` exactly when `a ≤ b`. -/
theorem lattice_le_lattice_iff [Nontrivial V] {a b : ℤ} :
    lattice R V b ≤ lattice R V a ↔ a ≤ b := by
  refine ⟨fun h ↦ ?_, fun h ↦ lattice_antitone h⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  simpa [hv] using h (single_mem_lattice le_rfl v)

/-- Every `V`-valued Laurent series lies in some lattice `U_a(V)`. -/
theorem iSup_lattice : ⨆ a, lattice R V a = ⊤ :=
  eq_top_iff.mpr fun f _ ↦ Submodule.mem_iSup_of_mem f.order fun _ hn ↦
    coeff_eq_zero_of_lt_order hn

/-- Only `0` lies in every lattice `U_a(V)`. -/
theorem iInf_lattice : ⨅ a, lattice R V a = ⊥ := by
  refine eq_bot_iff.mpr fun f hf ↦ ?_
  rw [Submodule.mem_iInf] at hf
  rw [Submodule.mem_bot]
  ext n
  exact hf (n + 1) n (Int.lt_succ n)

end Module

section Ring

variable {R : Type*} [Semiring R]

/-- The lattices multiply as `U_a U_b ⊆ U_{a + b}`. -/
theorem mul_mem_lattice {a b : ℤ} {f g : R⸨X⸩} (hf : f ∈ lattice R R a)
    (hg : g ∈ lattice R R b) : f * g ∈ lattice R R (a + b) := by
  rw [mem_lattice_iff_le_orderTop] at hf hg ⊢
  exact (WithTop.coe_add a b ▸ add_le_add hf hg).trans orderTop_add_le_mul

/-- A formal power series lies in `U_0`. -/
theorem coe_powerSeries_mem_lattice_zero (p : R⟦X⟧) : (p : R⸨X⸩) ∈ lattice R R 0 :=
  fun n hn ↦ by rw [PowerSeries.coeff_coe, ite_eq_left hn]

/-- The lattice `U_a` is `Xᵃ R⟦X⟧`: its members are the series `Xᵃ p` with `p` a power
series. -/
theorem mem_lattice_iff_exists {a : ℤ} {f : R⸨X⸩} :
    f ∈ lattice R R a ↔ ∃ p : R⟦X⟧, single a 1 * (p : R⸨X⸩) = f := by
  have hmem (p : R⟦X⟧) : single a 1 * (p : R⸨X⸩) ∈ lattice R R a := by
    simpa using mul_mem_lattice (single_mem_lattice (R := R) (le_refl a) (1 : R))
      (coe_powerSeries_mem_lattice_zero p)
  refine ⟨fun hf ↦ ⟨PowerSeries.mk fun n ↦ f.coeff (a + n), ?_⟩, fun ⟨p, hp⟩ ↦ hp ▸ hmem p⟩
  ext n
  obtain hn | hn := lt_or_ge n a
  · rw [hf n hn, coeff_eq_zero_of_mem_lattice (hmem _) hn]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + a := ⟨(n - a).toNat, by omega⟩
    rw [coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
    simp [add_comm]

/-- The lattice `U_0` consists of the formal power series. -/
theorem mem_lattice_zero_iff {f : R⸨X⸩} : f ∈ lattice R R 0 ↔ ∃ p : R⟦X⟧, (p : R⸨X⸩) = f := by
  simp only [mem_lattice_iff_exists, single_zero_one, one_mul]

/-- Over a field, `U_a` is the closed valuation ball `{f | v f ≤ exp (-a)}`. -/
theorem mem_lattice_iff_valuation_le {K : Type*} [Field K] {a : ℤ} {f : K⸨X⸩} :
    f ∈ lattice K K a ↔ Valued.v f ≤ WithZero.exp (-a) :=
  (_root_.LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).symm

end Ring

end TauCeti.LaurentSeries
