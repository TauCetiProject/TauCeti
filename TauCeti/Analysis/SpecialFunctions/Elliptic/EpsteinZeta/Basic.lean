/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import TauCeti.Analysis.Complex.UpperHalfPlane.PeriodPair
import Mathlib.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.SpecialFunctions.Elliptic.Period.Covolume

/-!
# The real Epstein zeta function of a lattice

For a lattice `Λ ⊂ ℂ` of area `A = covolume Λ`, the real Epstein zeta function is

`E(Λ, s) = ∑_{0 ≠ l ∈ Λ} (A / |l|²) ^ s`.

It only depends on the homothety class of `Λ`, and the series converges for `s > 1`. Its
expansion at the pole `s = 1`, Kronecker's first limit formula, is
`PeriodPair.tendsto_epsteinZeta_sub`.

## Main definitions and results

* `PeriodPair.epsteinZeta`: the real Epstein zeta function `E(Λ, s)` of the lattice of a period
  pair, normalised by its covolume.
* `PeriodPair.epsteinZeta_eq_of_lattice_eq`, `PeriodPair.epsteinZeta_smul`: `E(Λ, s)` depends only
  on the lattice, and only on its homothety class.
* `PeriodPair.hasSum_epsteinZeta`: the series `E(Λ, s)` converges for `s > 1`.
-/

public section

noncomputable section

namespace PeriodPair

variable (L : PeriodPair)

/-- The **real Epstein zeta function** of the lattice `Λ` of a period pair, normalised by the
covolume `A` of `Λ`: `E(Λ, s) = ∑_{l ∈ Λ} (A / |l|²) ^ s` for real `s`. The series converges for
`s > 1` (`PeriodPair.hasSum_epsteinZeta`); the term at `l = 0` is `0 ^ s = 0` for `s ≠ 0`. -/
def epsteinZeta (s : ℝ) : ℝ :=
  ∑' l : L.lattice, (ZLattice.covolume L.lattice / ‖(l : ℂ)‖ ^ 2) ^ s

/-- The defining series of `PeriodPair.epsteinZeta`. -/
theorem epsteinZeta_def (s : ℝ) :
    L.epsteinZeta s = ∑' l : L.lattice, (ZLattice.covolume L.lattice / ‖(l : ℂ)‖ ^ 2) ^ s :=
  (rfl)

/-- The real Epstein zeta function depends only on the lattice, not on the chosen basis. -/
theorem epsteinZeta_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.epsteinZeta = L'.epsteinZeta := by
  ext s
  -- The instance arguments of `ZLattice.covolume` are propositions, so `congr` reduces to `h`.
  have hA : ZLattice.covolume L.lattice = ZLattice.covolume L'.lattice := by
    congr 1
  rw [epsteinZeta, epsteinZeta, hA]
  exact (Equiv.subtypeEquivRight (p := (· ∈ L.lattice)) (q := (· ∈ L'.lattice))
    fun x ↦ by rw [h]).tsum_eq
      fun l : L'.lattice ↦ (ZLattice.covolume L'.lattice / ‖(l : ℂ)‖ ^ 2) ^ s

/-- The real Epstein zeta function is invariant under homotheties of the lattice. -/
@[simp]
theorem epsteinZeta_smul (c : ℂˣ) : (c • L).epsteinZeta = L.epsteinZeta := by
  ext s
  have hc : 0 < ‖(c : ℂ)‖ := norm_pos_iff.2 c.ne_zero
  rw [epsteinZeta, epsteinZeta, ← (L.latticeSMulEquiv c).toEquiv.tsum_eq]
  congr 1 with l
  rw [LinearEquiv.coe_toEquiv, coe_latticeSMulEquiv, norm_mul, mul_pow, covolume_lattice_smul,
    mul_div_mul_left _ _ (by positivity)]

/-- The series defining `PeriodPair.epsteinZeta L s` converges for `s > 1`. -/
theorem hasSum_epsteinZeta {s : ℝ} (hs : 1 < s) :
    HasSum (fun l : L.lattice ↦ (ZLattice.covolume L.lattice / ‖(l : ℂ)‖ ^ 2) ^ s)
      (L.epsteinZeta s) := by
  refine Summable.hasSum ?_
  have h := (ZLattice.summable_norm_rpow L.lattice (-2 * s) (by simp; linarith)).mul_left
    (ZLattice.covolume L.lattice ^ s)
  have hA := ZLattice.covolume_pos L.lattice
  refine h.congr fun l ↦ ?_
  rw [Real.div_rpow hA.le (sq_nonneg _), ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _),
    div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _), Submodule.norm_coe]
  norm_num

end PeriodPair
