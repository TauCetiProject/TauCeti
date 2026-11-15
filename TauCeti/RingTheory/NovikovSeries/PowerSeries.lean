/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RingTheory.NovikovSeries.Functoriality

/-!
# Power series in a monomial of positive period

For the exponent monoid `ℕ` with the period map `n ↦ n` (`Nat.castAddMonoidHom ℝ`), every
coefficient function has only finitely many nonzero coefficients below each cutoff, so the
Novikov series are the formal power series `R⟦X⟧` of Mathlib, with the same coefficients. This
file constructs that comparison as a ring isomorphism `TauCeti.NovikovSeries.toPowerSeries`,
sending the monomial `r e^n` to `r Xⁿ`.

Let `γ` be an exponent of positive period, `N γ > 0`. The exponent homomorphism `n ↦ n • γ`
rescales periods by `N γ`, so the pushforward `TauCeti.NovikovSeries.mapRingHom` along it applies.
Composing with the comparison gives the ring homomorphism

`TauCeti.NovikovSeries.ofPowerSeries γ hγ : R⟦X⟧ →+* Nov(R, H, N)`,

which sends `X` to `e^γ`: a power series `∑ aₙ Xⁿ` goes to `∑ aₙ e^(n • γ)`. It is compatible with
supports: the coefficient at `n • γ` is `aₙ`, every other coefficient vanishes, and a series
divisible by `Xⁿ` goes to the period neighbourhood `U_(n N γ)`. In particular its image lies in the
nonnegative subring. No injectivity of the period map `N` is needed, and `H` may have torsion:
the multiples of `γ` are pairwise distinct because their periods are. Being a pushforward of
coefficients, the map needs no topology on `R`, unlike Mathlib's evaluation `PowerSeries.aeval` at
topologically nilpotent elements.

Such maps turn local generating series in one variable, such as the multiplicity series of a
periodic orbit or of a pseudoholomorphic torus, into series indexed by the homology class of the
orbit, where products over all orbits converge in the period topology.

## Main definitions

* `TauCeti.NovikovSeries.toPowerSeries`: the coefficient-preserving ring isomorphism between
  Novikov series on `ℕ` for the period map `n ↦ n` and power series.
* `TauCeti.NovikovSeries.ofPowerSeries`: for `N γ > 0`, the ring homomorphism `R⟦X⟧ → Nov(R, H, N)`
  sending `X` to `e^γ`.

## Main results

* `TauCeti.NovikovSeries.ofPowerSeries_monomial`, `TauCeti.NovikovSeries.ofPowerSeries_X`: the
  monomial `r Xⁿ` goes to `r e^(n • γ)`.
* `TauCeti.NovikovSeries.coeff_ofPowerSeries_nsmul`,
  `TauCeti.NovikovSeries.coeff_ofPowerSeries_of_forall_nsmul_ne`: the coefficients of the image.
* `TauCeti.NovikovSeries.ofPowerSeries_mem_periodFiltration`: a series divisible by `Xⁿ` goes to
  the period neighbourhood `U_(N γ * n)`.
* `TauCeti.NovikovSeries.ofPowerSeries_mem_nonnegSubring`: the image lies in the nonnegative
  subring.

## References

* A. Pajitnov, *Circle-valued Morse Theory*, de Gruyter 2006, Chapter 3.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

open PowerSeries (C X monomial)

open scoped PowerSeries

namespace TauCeti

namespace NovikovSeries

variable {R : Type*}

section Comparison

variable [Semiring R]

/-- Novikov series on `ℕ` for the period map `n ↦ n` are the power series: the ring isomorphism
which keeps every coefficient. -/
def toPowerSeries : NovikovSeries R ℕ (Nat.castAddMonoidHom ℝ) ≃+* R⟦X⟧ where
  toFun a := PowerSeries.mk a.coeff
  invFun f := ⟨fun n => PowerSeries.coeff n f, fun C => (Set.finite_lt_nat ⌈C⌉₊).subset fun n hn =>
    Nat.lt_ceil.2 (by simpa using hn.2)⟩
  left_inv a := by
    ext n
    simp
  right_inv f := by
    ext n
    simp
  map_add' a b := by
    ext n
    simp
  map_mul' a b := by
    ext n
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk]
    simp only [PowerSeries.coeff_mk]
    exact coeff_mul_eq_sum (fun p hp => Finset.mem_antidiagonal.1 hp)
      fun u v huv _ _ => Finset.mem_antidiagonal.2 huv

@[simp]
theorem coeff_toPowerSeries (a : NovikovSeries R ℕ (Nat.castAddMonoidHom ℝ)) (n : ℕ) :
    PowerSeries.coeff n (toPowerSeries a) = a.coeff n :=
  PowerSeries.coeff_mk _ _

@[simp]
theorem coeff_toPowerSeries_symm (f : R⟦X⟧) (n : ℕ) :
    (toPowerSeries.symm f : NovikovSeries R ℕ (Nat.castAddMonoidHom ℝ)).coeff n =
      PowerSeries.coeff n f :=
  (rfl)

/-- The comparison sends the monomial `r e^n` to the power series monomial `r Xⁿ`. -/
@[simp]
theorem toPowerSeries_single (n : ℕ) (r : R) :
    toPowerSeries (single n r : NovikovSeries R ℕ (Nat.castAddMonoidHom ℝ)) = monomial n r := by
  ext k
  rw [coeff_toPowerSeries, PowerSeries.coeff_monomial]
  split_ifs with hk
  · rw [hk, coeff_single_same]
  · exact coeff_single_of_ne hk r

/-- The inverse comparison sends the power series monomial `r Xⁿ` to the monomial `r e^n`. -/
@[simp]
theorem toPowerSeries_symm_monomial (n : ℕ) (r : R) :
    (toPowerSeries.symm (monomial n r) : NovikovSeries R ℕ (Nat.castAddMonoidHom ℝ)) =
      single n r :=
  toPowerSeries.symm_apply_eq.2 (toPowerSeries_single n r).symm

end Comparison

section OfPowerSeries

variable {H : Type*} [AddMonoid H] {N : H →+ ℝ} {γ : H}

/-- The multiples of an exponent `γ` have periods `N (n • γ) = N γ * n`. -/
theorem period_multiplesHom (γ : H) (n : ℕ) :
    N (multiplesHom H γ n) = N γ * Nat.castAddMonoidHom ℝ n := by
  simp [mul_comm]

variable [Semiring R]

variable (γ) in
/-- For an exponent `γ` of positive period, the ring homomorphism `R⟦X⟧ → Nov(R, H, N)` sending
`X` to `e^γ`: the power series `∑ aₙ Xⁿ` goes to `∑ aₙ e^(n • γ)`. It is the pushforward along the
exponent homomorphism `n ↦ n • γ`, which rescales periods by `N γ`. -/
def ofPowerSeries (hγ : 0 < N γ) : R⟦X⟧ →+* NovikovSeries R H N :=
  (mapRingHom (RingHom.id R) (multiplesHom H γ) ⟨N γ, hγ, period_multiplesHom γ⟩).comp
    toPowerSeries.symm.toRingHom

variable (hγ : 0 < N γ)

/-- The series map is the pushforward along `n ↦ n • γ` of the series on `ℕ` with the same
coefficients. -/
theorem ofPowerSeries_apply (f : R⟦X⟧) :
    ofPowerSeries γ hγ f = map (RingHom.id R : R →+ R) (multiplesHom H γ)
      ⟨N γ, hγ, period_multiplesHom γ⟩ (toPowerSeries.symm f) := by
  rw [ofPowerSeries, RingHom.comp_apply, mapRingHom_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom]

/-- The monomial `r Xⁿ` goes to the monomial `r e^(n • γ)`. -/
@[simp]
theorem ofPowerSeries_monomial (n : ℕ) (r : R) :
    ofPowerSeries γ hγ (monomial n r) = single (n • γ) r := by
  simp [ofPowerSeries_apply]

/-- The constant series `r` goes to the constant Novikov series `r e^0`. -/
@[simp]
theorem ofPowerSeries_C (r : R) : ofPowerSeries γ hγ (C r) = single 0 r := by
  rw [← PowerSeries.monomial_zero_eq_C_apply, ofPowerSeries_monomial, zero_smul]

/-- The variable `X` goes to the monomial `e^γ`. -/
@[simp]
theorem ofPowerSeries_X : ofPowerSeries γ hγ (X : R⟦X⟧) = single γ (1 : R) := by
  rw [PowerSeries.X_eq, ofPowerSeries_monomial, one_smul]

/-- The coefficient of the image at `n • γ` is the `n`-th coefficient. -/
@[simp]
theorem coeff_ofPowerSeries_nsmul (f : R⟦X⟧) (n : ℕ) :
    (ofPowerSeries γ hγ f).coeff (n • γ) = PowerSeries.coeff n f := by
  -- The multiples of `γ` are pairwise distinct, because their periods `n • N γ` are.
  have hinj : Function.Injective (multiplesHom H γ) :=
    .of_comp (f := N) <| by simpa [Function.comp_def] using (nsmul_left_strictMono hγ).injective
  rw [ofPowerSeries_apply, ← multiplesHom_apply, coeff_map_of_injective _ _ _ hinj]
  simp

/-- The image has zero coefficient off the multiples of `γ`. -/
theorem coeff_ofPowerSeries_of_forall_nsmul_ne {h : H} (hh : ∀ n : ℕ, n • γ ≠ h) (f : R⟦X⟧) :
    (ofPowerSeries γ hγ f).coeff h = 0 := by
  rw [ofPowerSeries_apply]
  exact coeff_map_eq_zero_of_notMem_range _ _ _ _ fun ⟨n, hn⟩ => hh n hn

end OfPowerSeries

section Filtration

variable [Ring R]

/-- A power series lies in the period neighbourhood `U_n` of the Novikov series on `ℕ` exactly
when it is divisible by `Xⁿ`. -/
theorem toPowerSeries_symm_mem_periodFiltration_iff {f : R⟦X⟧} {n : ℕ} :
    (toPowerSeries.symm f : NovikovSeries R ℕ (Nat.castAddMonoidHom ℝ)) ∈
        periodFiltration R (Nat.castAddMonoidHom ℝ) n ↔ X ^ n ∣ f := by
  simp [mem_periodFiltration, PowerSeries.X_pow_dvd_iff]

variable {H : Type*} [AddMonoid H] {N : H →+ ℝ} {γ : H} (hγ : 0 < N γ)

/-- **Support compatibility.** A power series divisible by `Xⁿ` goes to the period neighbourhood
`U_(N γ * n)`. -/
theorem ofPowerSeries_mem_periodFiltration {f : R⟦X⟧} {n : ℕ} (hf : X ^ n ∣ f) :
    ofPowerSeries γ hγ f ∈ periodFiltration R N (N γ * n) := by
  rw [ofPowerSeries_apply]
  exact map_mem_periodFiltration _ _ _ hγ.le (period_multiplesHom γ)
    (toPowerSeries_symm_mem_periodFiltration_iff.2 hf)

/-- The image of a power series lies in the nonnegative subring. -/
theorem ofPowerSeries_mem_nonnegSubring (f : R⟦X⟧) :
    ofPowerSeries γ hγ f ∈ nonnegSubring R N := by
  simpa using ofPowerSeries_mem_periodFiltration hγ (n := 0) (f := f) (by simp)

end Filtration

end NovikovSeries

end TauCeti
