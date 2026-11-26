/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# The generalized Riemann hypothesis for Dirichlet L-functions

For a Dirichlet character `χ` modulo `N ≥ 1`, `TauCeti.DirichletGRH χ` states that every zero `s`
of the meromorphically continued function `χ.LFunction` in the open right half-plane `0 < Re s`
(excluding the totalized value at the pole `s = 1` when `χ = 1`) lies on the critical line
`Re s = 1 / 2`. `TauCeti.GRH` states `DirichletGRH χ` for all positive moduli `N` and all
Dirichlet characters `χ` modulo `N`. Both are propositions intended to appear as explicit
hypotheses of conditional theorems.

The condition `0 < Re s` excludes both the archimedean trivial zeros on `Re s ≤ 0` and the
purely imaginary zeros `Re s = 0` introduced by deleted Euler factors of imprimitive characters,
while nonvanishing on `1 ≤ Re s` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`) reduces
`DirichletGRH χ` to zeros in the open critical strip `0 < Re s < 1`. Consequently:

* `DirichletCharacter.dirichletGRH_iff_mem_Ioo`: `DirichletGRH χ` is equivalent to every zero of
  `χ.LFunction` with `0 < Re s < 1` having `Re s = 1 / 2`.
* `DirichletCharacter.dirichletGRH_changeLevel_iff` and
  `DirichletCharacter.dirichletGRH_primitiveCharacter_iff`: `DirichletGRH` is invariant under
  raising the level and passing to the inducing primitive character, so `GRH` is equivalent to its
  restriction to primitive characters (`TauCeti.grh_iff_isPrimitive`).
* `TauCeti.dirichletGRH_one_iff` and `DirichletCharacter.dirichletGRH_modOne_iff`: for a principal
  character modulo any `N ≥ 1`, `DirichletGRH` is equivalent to Mathlib's `RiemannHypothesis`; in
  particular `GRH` implies `RiemannHypothesis` (`TauCeti.GRH.riemannHypothesis`).
* `DirichletCharacter.dirichletGRH_inv_iff`: `DirichletGRH` is invariant under character inversion.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §7.3 and §10.3.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12 and §14.
-/

public section

open Complex ComplexConjugate Set

namespace TauCeti

/-- **The generalized Riemann hypothesis for a single Dirichlet character.** Every zero `s` of
`χ.LFunction` in `0 < Re s` (away from `s = 1` when `χ = 1`) has `Re s = 1 / 2`. -/
def DirichletGRH {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s = 0 → s.re = 1 / 2

/-- Zero-location projection from `DirichletGRH χ`. -/
theorem DirichletGRH.re_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (h : DirichletGRH χ)
    {s : ℂ} (hs : 0 < s.re) (h1 : χ ≠ 1 ∨ s ≠ 1) (h0 : χ.LFunction s = 0) :
    s.re = 1 / 2 :=
  h s hs h1 h0

end TauCeti

namespace DirichletCharacter

open TauCeti

theorem dirichletGRH_def {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletGRH χ =
      ∀ s : ℂ, 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) → χ.LFunction s = 0 → s.re = 1 / 2 :=
  (rfl)

/-- Because `χ.LFunction` has no zeros on `1 ≤ Re s` (away from the principal pole at `1`),
`DirichletGRH χ` is equivalent to every zero in the open critical strip `0 < Re s < 1` lying on
`Re s = 1 / 2`. -/
theorem dirichletGRH_iff_mem_Ioo {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletGRH χ ↔ ∀ s : ℂ, χ.LFunction s = 0 → s.re ∈ Ioo 0 1 → s.re = 1 / 2 := by
  refine ⟨fun h s h0 hre ↦ h s hre.1 (.inr fun hs1 ↦ by simp [hs1] at hre) h0,
    fun h s hs h1 h0 ↦ h s h0 ⟨hs, ?_⟩⟩
  exact lt_of_not_ge fun hge ↦ χ.LFunction_ne_zero_of_one_le_re h1 hge h0

/-- At modulus `1`, `DirichletGRH` is equivalent to `RiemannHypothesis`. -/
@[simp]
theorem dirichletGRH_modOne_iff (χ : DirichletCharacter ℂ 1) :
    DirichletGRH χ ↔ RiemannHypothesis := by
  rw [χ.dirichletGRH_iff_mem_Ioo, riemannHypothesis_iff_mem_Ioo]
  simp_rw [LFunction_modOne_eq]

/-- Complex conjugation relates the zeros of `χ.LFunction` and `χ⁻¹.LFunction`, so `DirichletGRH`
is invariant under character inversion. -/
@[simp]
theorem dirichletGRH_inv_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletGRH χ⁻¹ ↔ DirichletGRH χ := by
  suffices ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N),
      DirichletGRH ψ → DirichletGRH ψ⁻¹ from
    ⟨fun h ↦ inv_inv χ ▸ this χ⁻¹ h, this χ⟩
  intro N _ ψ h
  rw [dirichletGRH_iff_mem_Ioo] at h ⊢
  intro s h0 hre
  rw [← conj_conj s, LFunction_inv_conj_eq_zero_iff] at h0
  simpa using h (conj s) h0 (by simpa using hre)

/-- Raising the level of a Dirichlet character deletes Euler factors whose zeros lie on `Re s = 0`,
leaving `DirichletGRH` unchanged. -/
@[simp]
theorem dirichletGRH_changeLevel_iff {M N : ℕ} [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M)
    (hMN : M ∣ N) : DirichletGRH (changeLevel hMN χ) ↔ DirichletGRH χ := by
  rw [dirichletGRH_iff_mem_Ioo, dirichletGRH_iff_mem_Ioo]
  refine forall_congr' fun s ↦ ⟨fun h h0 hre ↦ h ?_ hre, fun h h0 hre ↦ h ?_ hre⟩
  · exact (LFunction_changeLevel_eq_zero_iff χ hMN hre.1.ne'
      (.inr fun hs1 ↦ by simp [hs1] at hre)).2 h0
  · exact (LFunction_changeLevel_eq_zero_iff χ hMN hre.1.ne'
      (.inr fun hs1 ↦ by simp [hs1] at hre)).1 h0

/-- `DirichletGRH` holds for a character if and only if it holds for its inducing primitive
character. -/
@[simp]
theorem dirichletGRH_primitiveCharacter_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletGRH χ.primitiveCharacter ↔ DirichletGRH χ := by
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
  exact (χ.primitiveCharacter.dirichletGRH_changeLevel_iff χ.conductor_dvd_level).symm

end DirichletCharacter

namespace TauCeti

/-- For the principal character modulo any `N ≥ 1`, `DirichletGRH` is equivalent to
`RiemannHypothesis`. -/
@[simp]
theorem dirichletGRH_one_iff {N : ℕ} [NeZero N] :
    DirichletGRH (1 : DirichletCharacter ℂ N) ↔ RiemannHypothesis := by
  rw [← DirichletCharacter.changeLevel_one N.one_dvd,
    DirichletCharacter.dirichletGRH_changeLevel_iff, DirichletCharacter.dirichletGRH_modOne_iff]

/-- **The generalized Riemann hypothesis for all Dirichlet L-functions.** -/
def GRH : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), DirichletGRH χ

theorem grh_def : GRH = ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), DirichletGRH χ :=
  (rfl)

/-- Specialize `GRH` to a single Dirichlet character. -/
theorem GRH.dirichletGRH (h : GRH) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    DirichletGRH χ :=
  h N χ

/-- `GRH` implies `RiemannHypothesis` via the principal character modulo `1`. -/
theorem GRH.riemannHypothesis (h : GRH) : RiemannHypothesis :=
  (dirichletGRH_one_iff (N := 1)).mp (h 1 1)

/-- `GRH` holds for all Dirichlet characters if and only if it holds for all primitive Dirichlet
characters. -/
theorem grh_iff_isPrimitive :
    GRH ↔ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → DirichletGRH χ :=
  ⟨fun h N _ χ _ ↦ h N χ, fun h _ _ χ ↦
    χ.dirichletGRH_primitiveCharacter_iff.mp
      (h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive)⟩

end TauCeti
