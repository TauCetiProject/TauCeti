/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Period pairs and removable singularities along a period lattice

Every full lattice in `ℂ` is the lattice of a period pair
(`Submodule.exists_periodPair_lattice_eq_of_isZLattice`).

Elementary analytic facts about functions that are only controlled off the lattice `L.lattice` of
a period pair `L`:

* `PeriodPair.countable_lattice`, `PeriodPair.eventually_notMem_lattice`: the lattice is countable
  and avoided by a punctured neighbourhood of every point;
* `PeriodPair.differentiable_of_periodic`: a lattice-periodic function that is differentiable at
  `0` and off the lattice is entire.

The lattice is stable under integer multiples (`PeriodPair.intCast_mul_mem_lattice`), and the
coordinates of `m ω₁ + n ω₂` in `PeriodPair.latticeBasis` are `m` and `n`
(`PeriodPair.latticeBasis_repr_eq`).

At positive level `N`, the division point `(m ω₁ + n ω₂) / N` lies in the lattice exactly when
`m` and `n` vanish modulo `N` (`PeriodPair.div_mem_lattice_iff_intCast_eq_zero`); for a residue
pair `a : (ℤ/Nℤ)²` this says that its division point is a period only for `a = 0`
(`PeriodPair.val_mul_ω₁_add_val_mul_ω₂_div_mem_lattice_iff`).
-/

public section

open Filter
open scoped Topology

namespace Submodule

/-- Every full lattice in `ℂ` is the lattice of a period pair: a `ℤ`-basis of the lattice is an
`ℝ`-basis of `ℂ`. -/
theorem exists_periodPair_lattice_eq_of_isZLattice (Λ : Submodule ℤ ℂ) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] : ∃ L : PeriodPair, L.lattice = Λ := by
  let b := Module.finBasisOfFinrankEq ℤ Λ
    (by rw [ZLattice.rank ℝ Λ, Complex.finrank_real_complex] : Module.finrank ℤ Λ = 2)
  let b' := b.ofZLatticeBasis ℝ Λ
  refine ⟨⟨b' 0, b' 1, ?_⟩, ?_⟩
  · convert b'.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  · rw [PeriodPair.lattice, ← b.ofZLatticeBasis_span ℝ]
    congr 1
    ext z
    simp [b', Fin.exists_fin_two, eq_comm]

end Submodule

namespace PeriodPair

variable (L : PeriodPair)

/-- The lattice of a period pair is countable. -/
lemma countable_lattice : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

/-- Every point has a punctured neighbourhood avoiding the lattice. -/
lemma eventually_notMem_lattice (l₀ : ℂ) : ∀ᶠ u in 𝓝[≠] l₀, u ∉ L.lattice := by
  filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l₀),
    self_mem_nhdsWithin] with u hu hne using fun h ↦ hu ⟨h, hne⟩

/-- A function that is periodic under every lattice vector, differentiable at `0` and
differentiable off the lattice is differentiable everywhere. -/
lemma differentiable_of_periodic {H : ℂ → ℂ} (hper : ∀ w ∈ L.lattice, Function.Periodic H w)
    (h₀ : DifferentiableAt ℂ H 0) (hoff : ∀ x ∉ L.lattice, DifferentiableAt ℂ H x) :
    Differentiable ℂ H := by
  intro x
  by_cases hx : x ∈ L.lattice
  · have hcomp : H = fun y ↦ H (y - x) := funext fun y ↦ by
      rw [← hper x hx (y - x), sub_add_cancel]
    rw [hcomp]
    exact differentiableAt_comp_sub_const.mpr (by simpa using h₀)
  · exact hoff x hx

/-- The lattice is stable under multiplication by integers. -/
lemma intCast_mul_mem_lattice (n : ℤ) {z : ℂ} (hz : z ∈ L.lattice) : (n : ℂ) * z ∈ L.lattice := by
  simpa [zsmul_eq_mul] using zsmul_mem hz n

/-- The coordinates of `m ω₁ + n ω₂` in the basis `ω₁, ω₂` of the lattice are `m` and `n`. -/
lemma latticeBasis_repr_eq {L : PeriodPair} {m n : ℤ} {x : L.lattice}
    (hx : (m : ℂ) * L.ω₁ + n * L.ω₂ = x) :
    L.latticeBasis.repr x 0 = m ∧ L.latticeBasis.repr x 1 = n := by
  have : x = m • L.latticeBasis 0 + n • L.latticeBasis 1 := by
    ext
    simp [← hx, zsmul_eq_mul]
  subst this
  simp

/-- If both integer coordinates vanish modulo `N`, their division point lies in the period
lattice. At `N = 0` the quotient is zero by Lean's division-by-zero convention. -/
theorem div_mem_lattice_of_intCast_eq_zero {N : ℕ} {m n : ℤ}
    (hm : (m : ZMod N) = 0) (hn : (n : ZMod N) = 0) :
    (m * L.ω₁ + n * L.ω₂) / N ∈ L.lattice := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hm
  obtain ⟨l, hl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hn
  rcases eq_or_ne (N : ℂ) 0 with hN | hN
  · rw [hN, div_zero]
    exact zero_mem _
  convert add_mem (zsmul_mem L.ω₁_mem_lattice k) (zsmul_mem L.ω₂_mem_lattice l) using 1
  rw [hk, hl, div_eq_iff hN]
  push_cast
  simp only [zsmul_eq_mul]
  ring

/-- At positive level, a division point `(m ω₁ + n ω₂) / N` lies in the period lattice exactly
when both integer coordinates vanish modulo `N`. -/
@[simp]
theorem div_mem_lattice_iff_intCast_eq_zero {N : ℕ} [NeZero N] {m n : ℤ} :
    (m * L.ω₁ + n * L.ω₂) / N ∈ L.lattice ↔ (m : ZMod N) = 0 ∧ (n : ZMod N) = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ L.div_mem_lattice_of_intCast_eq_zero h.1 h.2⟩
  have hN : (N : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (NeZero.ne N)
  have h' : ((m / (N : ℤ) : ℚ) : ℂ) * L.ω₁ + ((n / (N : ℤ) : ℚ) : ℂ) * L.ω₂ ∈ L.lattice := by
    convert h using 1
    push_cast
    ring
  obtain ⟨hm, hn⟩ := mul_ω₁_add_mul_ω₂_mem_lattice.mp h'
  rw [Rat.den_div_intCast_eq_one_iff _ _ hN] at hm hn
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨hm, hn⟩

/-- At positive level, the division point `(a₀.val ω₁ + a₁.val ω₂) / N` of a residue pair
`a : (ℤ/Nℤ)²` lies in the period lattice exactly when `a = 0`. -/
theorem val_mul_ω₁_add_val_mul_ω₂_div_mem_lattice_iff {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) :
    ((a 0).val * L.ω₁ + (a 1).val * L.ω₂) / N ∈ L.lattice ↔ a = 0 := by
  have h := L.div_mem_lattice_iff_intCast_eq_zero (N := N) (m := (a 0).val) (n := (a 1).val)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h
  rw [h, funext_iff, Fin.forall_fin_two, Pi.zero_apply, Pi.zero_apply]

end PeriodPair
