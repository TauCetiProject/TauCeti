/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Pi

/-!
# Finite-coordinate presentations of restricted coefficient modules

Restricted series with coefficients in a finite product of seminormed modules are tuples of
restricted series. The equivalence `IsRestrictedFamily.piLinearEquiv` separates the coordinates
at every polyradius, including when the variable set is infinite. For ultrametric coefficient
modules it is linear for the convolution action of restricted scalar series as well
(`IsRestrictedFamily.piSeriesLinearEquiv`).

In particular, `IsRestrictedFamily.piRingLinearEquiv` identifies restricted families with
coefficients in the finite free module `ι → R` with `ι` copies of the restricted-series ring.
This is the finite free case of transporting a coefficient-module presentation to restricted
series. The coefficient formulas describe both directions without unfolding the equivalences.
No completeness or positivity hypothesis on the polyradius is needed for these algebraic
comparisons. No topology on restricted families is asserted here.

The construction extends the finite-coordinate comparison for topological restricted series in
`TauCeti.RingTheory.Huber.Restricted.PowerSeries` to the weighted norm-decay condition.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily

open _root_.MvPowerSeries

variable {σ ι R : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)]

section Coefficients

variable [SeminormedRing R] [∀ i, Module R (E i)] [∀ i, IsBoundedSMul R (E i)]

variable (R) in
/-- Separating the coordinates of a finite product commutes with forming restricted families,
at every polyradius. The coefficient modules carry the maximum seminorm. -/
def piLinearEquiv (c : σ → ℝ) :
    IsRestrictedFamily.addSubgroup (∀ i, E i) c ≃ₗ[R]
      ∀ i, IsRestrictedFamily.addSubgroup (E i) c where
  toFun a i := ⟨fun t ↦ (a : (σ →₀ ℕ) → ∀ i, E i) t i,
    mem_addSubgroup.mpr (isRestrictedFamily_pi_iff.mp (mem_addSubgroup.mp a.2) i)⟩
  invFun a := ⟨fun t i ↦ (a i : (σ →₀ ℕ) → E i) t,
    mem_addSubgroup.mpr (isRestrictedFamily_pi_iff.mpr fun i ↦ mem_addSubgroup.mp (a i).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    ext i t
    simp

variable {c : σ → ℝ}

/-- The coordinate comparison takes the indicated coordinate of every coefficient. -/
@[simp]
theorem piLinearEquiv_apply (a : IsRestrictedFamily.addSubgroup (∀ i, E i) c)
    (i : ι) (t : σ →₀ ℕ) :
    (piLinearEquiv R c a i : (σ →₀ ℕ) → E i) t = (a : (σ →₀ ℕ) → ∀ i, E i) t i :=
  (rfl)

/-- The inverse coordinate comparison assembles the coefficient vectors coordinatewise. -/
@[simp]
theorem piLinearEquiv_symm_apply (a : ∀ i, IsRestrictedFamily.addSubgroup (E i) c)
    (t : σ →₀ ℕ) (i : ι) :
    ((piLinearEquiv R c).symm a : (σ →₀ ℕ) → ∀ i, E i) t i =
      (a i : (σ →₀ ℕ) → E i) t :=
  (rfl)

/-- The coordinate comparison commutes with finite-support inclusion. -/
@[simp]
theorem piLinearEquiv_ofFinsupp (a : (σ →₀ ℕ) →₀ ∀ i, E i) (i : ι) :
    piLinearEquiv R c (ofFinsupp R c a) i =
      ofFinsupp R c (Finsupp.mapRange.linearMap (LinearMap.proj (R := R) i) a) := by
  ext t
  simp

end Coefficients

section Convolution

variable [NormedRing R] [IsUltrametricDist R] [∀ i, IsUltrametricDist (E i)]
  [∀ i, Module R (E i)] [∀ i, IsBoundedSMul R (E i)] {c : σ → ℝ}

/-- Separating coefficient coordinates commutes with convolution by a scalar restricted series. -/
theorem piLinearEquiv_isRestrictedSubring_smul
    (f : IsRestricted.subring (R := R) c)
    (a : IsRestrictedFamily.addSubgroup (∀ i, E i) c) :
    piLinearEquiv R c (f • a) = f • piLinearEquiv R c a := by
  ext i t
  exact (congrFun (convSMul_comp (LinearMap.proj i) (f : MvPowerSeries σ R)
    (a : (σ →₀ ℕ) → ∀ i, E i)) t).symm

variable (R c) in
/-- The finite-coordinate comparison is linear over the restricted-series ring acting by
convolution, without a completeness assumption. -/
def piSeriesLinearEquiv :
    IsRestrictedFamily.addSubgroup (∀ i, E i) c ≃ₗ[IsRestricted.subring (R := R) c]
      ∀ i, IsRestrictedFamily.addSubgroup (E i) c :=
  { (piLinearEquiv (E := E) R c).toAddEquiv with
    map_smul' := fun f a ↦ piLinearEquiv_isRestrictedSubring_smul f a }

/-- The restricted-series linear comparison is the coefficient-module linear comparison. -/
@[simp]
theorem coe_piSeriesLinearEquiv :
    ⇑(piSeriesLinearEquiv (E := E) R c) = piLinearEquiv R c :=
  (rfl)

/-- The inverse restricted-series linear comparison assembles the same coefficient vectors. -/
@[simp]
theorem coe_piSeriesLinearEquiv_symm :
    ⇑(piSeriesLinearEquiv (E := E) R c).symm = (piLinearEquiv R c).symm :=
  (rfl)

end Convolution

section FiniteFree

variable [NormedRing R] [IsUltrametricDist R]

variable (R) in
/-- Restricted families with coefficients in a finite free module are a finite free module over
the restricted-series ring, with the same coordinates. -/
noncomputable def piRingLinearEquiv (c : σ → ℝ) :
    IsRestrictedFamily.addSubgroup (ι → R) c ≃ₗ[IsRestricted.subring (R := R) c]
      ι → IsRestricted.subring (R := R) c :=
  (piSeriesLinearEquiv R c).trans (LinearEquiv.piCongrRight fun _ ↦ subringLinearEquiv.symm)

variable {c : σ → ℝ}

/-- Each coordinate series has the corresponding coordinate of the original coefficients. -/
@[simp]
theorem coeff_piRingLinearEquiv (a : IsRestrictedFamily.addSubgroup (ι → R) c)
    (i : ι) (t : σ →₀ ℕ) :
    _root_.MvPowerSeries.coeff t (piRingLinearEquiv R c a i : MvPowerSeries σ R) =
      (a : (σ →₀ ℕ) → ι → R) t i := by
  simp [piRingLinearEquiv]

/-- The inverse finite-free comparison assembles a tuple of series coefficientwise. -/
@[simp]
theorem piRingLinearEquiv_symm_apply (a : ι → IsRestricted.subring (R := R) c)
    (t : σ →₀ ℕ) (i : ι) :
    ((piRingLinearEquiv R c).symm a : (σ →₀ ℕ) → ι → R) t i =
      _root_.MvPowerSeries.coeff t (a i : MvPowerSeries σ R) := by
  simp [piRingLinearEquiv, LinearEquiv.piCongrRight_symm]

end FiniteFree

end TauCeti.MvPowerSeries.IsRestrictedFamily
