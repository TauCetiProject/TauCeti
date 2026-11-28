/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AffineGrassmannian.Lattice.Cartan
public import TauCeti.RingTheory.PowerSeries.Jet
public import Mathlib.RingTheory.LaurentSeries
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Lift
import Mathlib.Algebra.Group.Action.End

/-!
# Finite-jet actions on bounded lattices

The integral general linear group preserves every interval between two constant diagonal
lattices. A matrix congruent to the identity modulo `ξ ^ m` acts trivially on the interval
`ξ ^ b Bⁿ ⊆ L ⊆ ξ ^ a Bⁿ` when `b ≤ a + m`. Indeed its displacement sends `L` into
`ξ ^ (a + m) Bⁿ`, and the same applies to its inverse.

For power series this gives an action of `GLₙ(R[X]/(X ^ m))` on the interval, compatible with
the arc-group action, for every commutative ring `R` and positive `m ≥ b - a`.
Laurent series use Mathlib's localization algebra structure over power series.

## References

* X. Zhu, *An introduction to affine Grassmannians and the geometric Satake equivalence*,
  §1.1 and §2.1.
-/

public section

open Matrix
open scoped Polynomial PowerSeries LaurentSeries

namespace TauCeti.ProjectiveLattice

section PowerSeries

variable (R n : Type*) [CommRing R] [Fintype n] [DecidableEq n]

local instance : FaithfulSMul R⟦X⟧ R⸨X⸩ :=
  (faithfulSMul_iff_algebraMap_injective R⟦X⟧ R⸨X⸩).2 (by
    rw [LaurentSeries.coe_algebraMap]
    exact HahnSeries.ofPowerSeries_injective)

/-- The lattices between `X ^ b R⟦X⟧ⁿ` and `X ^ a R⟦X⟧ⁿ`, with the localization algebra
structure on Laurent series. The bounds may coincide, and the coefficient ring may be nonreduced. -/
noncomputable abbrev powerSeriesInterval (a b : ℤ) :=
  Set.Icc (diagonal (fun _ : n ↦ b)
    (IsLocalization.Away.algebraMap_isUnit (S := R⸨X⸩) (PowerSeries.X : R⟦X⟧)))
    (diagonal (fun _ : n ↦ a)
      (IsLocalization.Away.algebraMap_isUnit (S := R⸨X⸩) (PowerSeries.X : R⟦X⟧)))

variable {R n}

/-- The reduction kernel at level `m` fixes every lattice in an interval of width at most `m`.
No positivity hypothesis is needed for this kernel assertion. -/
theorem map_smul_eq_of_jet_eq_one {a b : ℤ} {m : ℕ} (hm : b ≤ a + m)
    {g : GL n R⟦X⟧} (hg : GeneralLinearGroup.map
      (↑(PowerSeries.jet R m) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ m : R[X])) g = 1)
    (L : powerSeriesInterval R n a b) :
    GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val = L.val := by
  apply map_smul_eq_of_congruent _ hm ?_ L.property
  have hk := (GeneralLinearGroup.mem_ker_map_iff
    (↑(PowerSeries.jet R m) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ m : R[X]))).1
      (MonoidHom.mem_ker.mpr hg)
  simpa only [RingHom.ker_coe_toRingHom, PowerSeries.ker_jet, Ideal.mem_span_singleton] using hk

variable (R n)

/-- The action of the finite jet group on an interval of lattices whose width is at most `m`.
It is uniquely determined by compatibility with the arc-group action. -/
noncomputable def jetAction (a b : ℤ) (m : ℕ) [NeZero m] (hm : b ≤ a + m) :
    GL n (AdjoinRoot (Polynomial.X ^ m : R[X])) →*
      Equiv.Perm (powerSeriesInterval R n a b) :=
  (GeneralLinearGroup.map (↑(PowerSeries.jet R m))).liftOfSurjective
    (GeneralLinearGroup.map_surjective _ PowerSeries.jet_surjective)
    ⟨diagonalIntervalAction (IsLocalization.Away.algebraMap_isUnit
        (PowerSeries.X : R⟦X⟧)) a b, fun g hg ↦ by
      apply MonoidHom.mem_ker.mpr
      ext L : 2
      simpa only [val_diagonalIntervalAction_apply, Equiv.Perm.one_apply] using
        map_smul_eq_of_jet_eq_one hm hg L⟩

/-- The finite-jet action as a `MulAction`, for use as a local instance after choosing the
jet level and its width bound. -/
noncomputable abbrev jetMulAction (a b : ℤ) (m : ℕ) [NeZero m] (hm : b ≤ a + m) :
    MulAction (GL n (AdjoinRoot (Polynomial.X ^ m : R[X]))) (powerSeriesInterval R n a b) :=
  MulAction.compHom _ (jetAction R n a b m hm)

variable {R n}

/-- Reducing an arc to its jet and applying the jet action gives the original lattice action. -/
@[simp]
theorem val_jetAction_map {a b : ℤ} {m : ℕ} [NeZero m] (hm : b ≤ a + m)
    (g : GL n R⟦X⟧) (L : powerSeriesInterval R n a b) :
    (jetAction R n a b m hm (GeneralLinearGroup.map (↑(PowerSeries.jet R m)) g) L).val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val := by
  dsimp only [jetAction, MonoidHom.liftOfSurjective]
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  exact val_diagonalIntervalAction_apply _ a b g L

/-- The jet action is the unique action homomorphism extending the arc action on the interval. -/
theorem jetAction_unique {a b : ℤ} {m : ℕ} [NeZero m] (hm : b ≤ a + m)
    (ρ : GL n (AdjoinRoot (Polynomial.X ^ m : R[X])) →*
      Equiv.Perm (powerSeriesInterval R n a b))
    (hρ : ∀ (g : GL n R⟦X⟧) (L : powerSeriesInterval R n a b),
      (ρ (GeneralLinearGroup.map (↑(PowerSeries.jet R m)) g) L).val =
        GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val) :
    ρ = jetAction R n a b m hm := by
  apply (MonoidHom.cancel_right (GeneralLinearGroup.map_surjective
    (↑(PowerSeries.jet R m) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ m : R[X]))
    PowerSeries.jet_surjective)).1
  ext g L : 3
  exact (hρ g L).trans (val_jetAction_map hm g L).symm

/-- Once the smaller jet level bounds the interval width, reducing from a larger jet level
does not change the lattice action. -/
theorem jetAction_comp_algHomOfDvd {a b : ℤ} {m M : ℕ} [NeZero m] [NeZero M]
    (hm : b ≤ a + m) (h : m ≤ M) :
    (jetAction R n a b m hm).comp
      (GeneralLinearGroup.map (AdjoinRoot.algHomOfDvd R (Polynomial.X ^ M : R[X])
        (Polynomial.X ^ m) (pow_dvd_pow Polynomial.X h)).toRingHom) =
      jetAction R n a b M (by omega) := by
  apply jetAction_unique
  intro g L
  have hmap : GeneralLinearGroup.map
      (AdjoinRoot.algHomOfDvd R (Polynomial.X ^ M : R[X]) (Polynomial.X ^ m)
        (pow_dvd_pow Polynomial.X h)).toRingHom
      (GeneralLinearGroup.map (↑(PowerSeries.jet R M)) g) =
        GeneralLinearGroup.map (↑(PowerSeries.jet R m)) g := by
    ext i j
    exact PowerSeries.algHomOfDvd_jet h _
  simpa only [MonoidHom.comp_apply, hmap] using val_jetAction_map hm g L

/-- Every jet fixes every lattice in the interval with equal exponent bounds `a, a`. -/
@[simp]
theorem jetAction_self (a : ℤ) (m : ℕ) [NeZero m]
    (q : GL n (AdjoinRoot (Polynomial.X ^ m : R[X])))
    (L : powerSeriesInterval R n a a) :
    jetAction R n a a m (by omega) q L = L := by
  apply Subtype.ext
  exact (Set.subsingleton_Icc_of_ge le_rfl)
    (jetAction R n a a m (by omega) q L).property L.property

/-- On any lattice interval of width at most one, an arc acts in the same way as its constant
matrix. In particular this identifies the first-jet action on `XL₀ ⊆ L ⊆ L₀`. -/
theorem map_smul_eq_constantCoeff_smul {a b : ℤ} (hab : b ≤ a + 1)
    (L : powerSeriesInterval R n a b) (g : GL n R⟦X⟧) :
    GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩) g • L.val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩)
        (GeneralLinearGroup.map (PowerSeries.C : R →+* R⟦X⟧)
          (GeneralLinearGroup.map (PowerSeries.constantCoeff : R⟦X⟧ →+* R) g)) • L.val := by
  have hj : GeneralLinearGroup.map
      (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X])) g =
      GeneralLinearGroup.map
        (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X]))
        (GeneralLinearGroup.map (PowerSeries.C : R →+* R⟦X⟧)
          (GeneralLinearGroup.map (PowerSeries.constantCoeff : R⟦X⟧ →+* R) g)) := by
    simpa only [GeneralLinearGroup.map_comp, MonoidHom.comp_apply] using
      (congrArg (fun f : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X]) ↦
        GeneralLinearGroup.map f g) PowerSeries.jet_one_comp_C_constantCoeff).symm
  rw [← val_jetAction_map (m := 1) hab g L, ← val_jetAction_map (m := 1) hab _ L, hj]

/-- The first-jet action on an interval of width at most one is the action of its matrix
evaluated at zero. -/
@[simp]
theorem val_jetAction_one {a b : ℤ} (hab : b ≤ a + 1)
    (q : GL n (AdjoinRoot (Polynomial.X ^ 1 : R[X]))) (L : powerSeriesInterval R n a b) :
    (jetAction R n a b 1 hab q L).val =
      GeneralLinearGroup.map (algebraMap R⟦X⟧ R⸨X⸩)
        (GeneralLinearGroup.map (PowerSeries.C : R →+* R⟦X⟧)
          (GeneralLinearGroup.map (AdjoinRoot.lift (RingHom.id R) 0 (by simp)) q)) • L.val := by
  obtain ⟨g, rfl⟩ := GeneralLinearGroup.map_surjective
    (↑(PowerSeries.jet R 1) : R⟦X⟧ →+* AdjoinRoot (Polynomial.X ^ 1 : R[X]))
    PowerSeries.jet_surjective q
  rw [val_jetAction_map, map_smul_eq_constantCoeff_smul hab L g]
  congr 2
  ext i j
  simp [PowerSeries.jet_apply, PowerSeries.coeff_zero_eq_constantCoeff]

end PowerSeries

end TauCeti.ProjectiveLattice
