/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
public import TauCeti.RingTheory.PowerSeries.HasseDeriv.GaussNorm
public import TauCeti.RingTheory.PowerSeries.Restricted

/-!
# Entire power series

A power series `f = ∑ aₙ Xⁿ` over a normed ring is *entire* when it is restricted at every real
radius, that is, `‖aₙ‖ rⁿ → 0` for every `r`. Over a complete ultrametric ring the sum
`∑ aₙ bⁿ` of such a series then converges at every `b`, not only on a closed disc of some fixed
radius. Entire series are the natural home of Fredholm determinants of compact operators and of
their factorisations by polynomials.

Restrictedness at a radius `r` implies restrictedness at every radius `s` with `|s| ≤ |r|`, so
it suffices to test positive radii (`PowerSeries.isEntire_iff_forall_pos`), or the radii along
any sequence tending to infinity (`PowerSeries.isEntire_iff_of_tendsto`). Over any normed ring,
the entire series form the subring `PowerSeries.IsEntire.subring`. Entire series are stable
under Hasse derivatives, rescaling `f(X) ↦ f(aX)` and coefficientwise application of bounded ring
homomorphisms.

Over a normed ring with `‖a‖ < 1`, the series `∑ a^(n²) Xⁿ` is entire
(`PowerSeries.isEntire_mk_pow_sq`), while for `a ≠ 0` and a multiplicative norm the series
`∑ aⁿ Xⁿ` is not, failing to be restricted at the radius `‖a‖⁻¹`
(`PowerSeries.not_isEntire_mk_pow`), although it is restricted at every radius `r` with
`|r| < ‖a‖⁻¹`. These are the standard examples separating entire series from series
restricted at a fixed radius.

## Main definitions

* `PowerSeries.IsEntire`: `f` is restricted at every real radius.
* `PowerSeries.IsEntire.subring`: the subring of entire series.

## Main results

* `PowerSeries.isEntire_iff`: the defining condition, for use outside this file.
* `PowerSeries.isEntire_iff_forall_pos` and `PowerSeries.isEntire_iff_of_tendsto`: entireness
  can be tested at positive radii, or along radii tending to infinity.
* `PowerSeries.IsEntire.add`, `PowerSeries.IsEntire.mul`, `PowerSeries.isEntire_coe` and their
  companions: entire series form a subring containing the polynomials.
* `PowerSeries.IsEntire.hasseDeriv`, `PowerSeries.IsEntire.derivative`,
  `PowerSeries.IsEntire.rescale` and `PowerSeries.IsEntire.map`: entireness is preserved by Hasse
  derivatives, rescaling and bounded coefficient maps.
* `PowerSeries.IsEntire.summable_norm_coeff_mul_pow`: `∑ ‖aₙ‖ tⁿ` converges for every real `t`.
* `PowerSeries.IsEntire.mk_coeff_succ`: dropping the constant term and dividing by `X` keeps a
  series entire.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. 127 (1997),
  417–479, Appendix A.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

section NormedRing

variable {R : Type*} [NormedRing R] {f g : R⟦X⟧}

/-- A power series `∑ aₙ Xⁿ` is *entire* when it is restricted at every real radius `r`, that is,
`‖aₙ‖ rⁿ → 0`. -/
def IsEntire (f : R⟦X⟧) : Prop :=
  ∀ r : ℝ, f.IsRestricted r

/-- A series is entire exactly when it is restricted at every real radius. -/
theorem isEntire_iff : f.IsEntire ↔ ∀ r : ℝ, f.IsRestricted r :=
  Iff.rfl

/-- An entire series is restricted at every radius. -/
theorem IsEntire.isRestricted (hf : f.IsEntire) (r : ℝ) : f.IsRestricted r :=
  hf r

/-- Entireness only needs to be checked at positive radii. -/
theorem isEntire_iff_forall_pos : f.IsEntire ↔ ∀ r : ℝ, 0 < r → f.IsRestricted r := by
  refine ⟨fun hf r _ ↦ hf r, fun hf r ↦ ?_⟩
  refine TauCeti.PowerSeries.isRestricted_of_abs_le (hf (|r| + 1) (by positivity)) ?_
  rw [abs_of_pos (by positivity : 0 < |r| + 1)]
  exact le_add_of_nonneg_right zero_le_one

/-- Entireness only needs to be checked along a family of radii tending to infinity, for
instance at the radii `n : ℕ`. -/
theorem isEntire_iff_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {ρ : ι → ℝ}
    (hρ : Tendsto ρ l atTop) : f.IsEntire ↔ ∀ i, f.IsRestricted (ρ i) := by
  refine ⟨fun hf i ↦ hf (ρ i), fun hf r ↦ ?_⟩
  obtain ⟨i, hi⟩ := (hρ.eventually_ge_atTop |r|).exists
  exact TauCeti.PowerSeries.isRestricted_of_abs_le (hf i) (hi.trans (le_abs_self _))

/-- The zero series is entire. -/
@[simp]
theorem isEntire_zero : (0 : R⟦X⟧).IsEntire :=
  fun r ↦ isRestricted_zero r

/-- The constant series `1` is entire. -/
@[simp]
theorem isEntire_one : (1 : R⟦X⟧).IsEntire :=
  fun r ↦ isRestricted_one r

/-- Constant series are entire. -/
@[simp]
theorem isEntire_C (a : R) : (C a).IsEntire :=
  fun r ↦ isRestricted_C r a

/-- Monomials are entire. -/
@[simp]
theorem isEntire_monomial (n : ℕ) (a : R) : (monomial n a).IsEntire :=
  fun r ↦ isRestricted_monomial r n a

/-- The variable `X` is entire. -/
@[simp]
theorem isEntire_X : (X : R⟦X⟧).IsEntire :=
  fun _ ↦ MvPowerSeries.isRestricted_X _ ()

/-- Every polynomial is entire. -/
@[simp]
theorem isEntire_coe (p : Polynomial R) : (p : R⟦X⟧).IsEntire :=
  fun _ ↦ TauCeti.PowerSeries.isRestricted_polynomial p

/-- A sum of entire series is entire. -/
theorem IsEntire.add (hf : f.IsEntire) (hg : g.IsEntire) : (f + g).IsEntire :=
  fun r ↦ (hf r).add (hg r)

/-- The negative of an entire series is entire. -/
theorem IsEntire.neg (hf : f.IsEntire) : (-f).IsEntire :=
  fun r ↦ (hf r).neg

/-- A difference of entire series is entire. -/
theorem IsEntire.sub (hf : f.IsEntire) (hg : g.IsEntire) : (f - g).IsEntire :=
  fun r ↦ (hf r).sub (hg r)

/-- A scalar multiple `a • f` of an entire series is entire. -/
theorem IsEntire.smul (a : R) (hf : f.IsEntire) : (a • f).IsEntire :=
  fun r ↦ (hf r).smul a

/-- A finite sum of entire series is entire. -/
theorem IsEntire.sum {ι : Type*} {s : Finset ι} {f : ι → R⟦X⟧} (hf : ∀ i ∈ s, (f i).IsEntire) :
    (∑ i ∈ s, f i).IsEntire :=
  fun r ↦ MvPowerSeries.IsRestricted.sum fun i hi ↦ hf i hi r

/-- A bounded ring homomorphism `φ`, `‖φ x‖ ≤ C ‖x‖`, maps entire series to entire series
coefficientwise. -/
theorem IsEntire.map {S : Type*} [NormedRing S] (hf : f.IsEntire) (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) : (map φ f).IsEntire :=
  -- `PowerSeries.map φ` is `MvPowerSeries.map φ` in the single variable `Unit`.
  fun r ↦ (hf r).map φ hφ

/-- Over a normed ring, if `‖a‖ < 1` then `∑ a^(n²) Xⁿ` is entire: at the radius `r`, its
weighted coefficient norms are bounded by `(‖a‖ⁿ r)ⁿ`. -/
theorem isEntire_mk_pow_sq {a : R} (ha : ‖a‖ < 1) : (mk fun n ↦ a ^ (n ^ 2)).IsEntire := by
  intro r
  rw [← isRestricted_abs_iff, isRestricted_iff']
  have hsmall : ∀ᶠ n in atTop, ‖a‖ ^ n * |r| ≤ 1 / 2 := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg a) ha).mul_const |r|
    rw [zero_mul] at h
    exact h.eventually (Iic_mem_nhds (by norm_num))
  refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  calc ‖coeff n (mk fun n ↦ a ^ (n ^ 2))‖ * |r| ^ n ≤ ‖a‖ ^ (n ^ 2) * |r| ^ n := by
        rw [coeff_mk]
        gcongr
        exact norm_pow_le' a (by positivity)
    _ = (‖a‖ ^ n * |r|) ^ n := by rw [mul_pow, ← pow_mul, sq]
    _ ≤ (1 / 2) ^ n := by gcongr

/-- Over a ring with multiplicative norm, if `a ≠ 0` then `∑ aⁿ Xⁿ` is not entire: its weighted
coefficient norms at the radius `‖a‖⁻¹` are all `1`. -/
theorem not_isEntire_mk_pow [NormMulClass R] {a : R} (ha : a ≠ 0) :
    ¬(mk fun n ↦ a ^ n).IsEntire :=
  fun hf ↦ TauCeti.PowerSeries.not_isRestricted_mk_pow ha (hf ‖a‖⁻¹)

/-- A product of entire series is entire. -/
theorem IsEntire.mul (hf : f.IsEntire) (hg : g.IsEntire) : (f * g).IsEntire :=
  fun r ↦ (hf (|r| + 1)).mul_of_abs_lt (hg (|r| + 1)) (lt_abs.mpr (.inl (lt_add_one _)))

/-- A power of an entire series is entire. -/
theorem IsEntire.pow (hf : f.IsEntire) (n : ℕ) : (f ^ n).IsEntire := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

/-- Hasse derivatives of entire series are entire. The polynomial growth of the binomial
coefficient is absorbed by testing the original series at a larger radius. -/
theorem IsEntire.hasseDeriv (hf : f.IsEntire) (k : ℕ) :
    (PowerSeries.hasseDeriv k f).IsEntire :=
  fun r ↦ (hf (|r| + 1)).hasseDeriv_of_abs_lt (lt_abs.mpr (.inl (lt_add_one _))) k

/-- For an entire series `f = ∑ aₙ Xⁿ`, the series `∑ ‖aₙ‖ tⁿ` converges for every real `t`. -/
theorem IsEntire.summable_norm_coeff_mul_pow (hf : f.IsEntire) (t : ℝ) :
    Summable fun n ↦ ‖coeff n f‖ * t ^ n := by
  -- restrictedness at the radius `2 |t|` bounds the terms by a multiple of `2⁻ⁿ`
  obtain ⟨B, hB⟩ := ((isRestricted_iff' (2 * |t|) f).mp (hf.isRestricted _)).bddAbove_range
  refine Summable.of_norm_bounded (summable_geometric_two.mul_left B) fun n ↦ ?_
  have hn : ‖coeff n f‖ * (2 * |t|) ^ n ≤ B := hB ⟨n, rfl⟩
  calc ‖‖coeff n f‖ * t ^ n‖ = ‖coeff n f‖ * (2 * |t|) ^ n * (1 / 2) ^ n := by
        simp [mul_pow]
        field_simp
    _ ≤ B * (1 / 2) ^ n := by gcongr

/-- The series `∑ aₙ₊₁ Xⁿ` obtained from an entire series by dropping the constant term and
dividing by `X` is entire. -/
theorem IsEntire.mk_coeff_succ (hf : f.IsEntire) : (mk fun n ↦ coeff (n + 1) f).IsEntire := by
  refine isEntire_iff_forall_pos.mpr fun r hr ↦ (isRestricted_iff' r _).mpr ?_
  have h := ((tendsto_add_atTop_iff_nat 1).mpr
    ((isRestricted_iff' r f).mp (hf.isRestricted r))).mul_const r⁻¹
  rw [zero_mul] at h
  refine h.congr fun n ↦ ?_
  rw [coeff_mk, pow_succ]
  field_simp

variable (R) in
/-- The entire power series form a subring. -/
protected noncomputable def IsEntire.subring : Subring R⟦X⟧ where
  carrier := {f | f.IsEntire}
  zero_mem' := isEntire_zero
  one_mem' := isEntire_one
  add_mem' := fun hf hg ↦ hf.add hg
  mul_mem' := fun hf hg ↦ hf.mul hg
  neg_mem' := fun hf ↦ hf.neg

/-- Membership in the subring of entire series is entireness. -/
@[simp]
theorem IsEntire.mem_subring : f ∈ IsEntire.subring R ↔ f.IsEntire :=
  Iff.rfl

/-- Over an ultrametric ring, every entire series is restricted at each radius `r`, so the
subring of entire series lies in the restricted subring at `r`. -/
theorem IsEntire.subring_le_isRestrictedSubring [IsUltrametricDist R] (r : ℝ) :
    IsEntire.subring R ≤ IsRestricted.subring r :=
  fun _ hf ↦ hf.isRestricted r

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] {f : R⟦X⟧}

/-- If `f(X)` is entire, so is `f(aX)` for every `a`. -/
theorem IsEntire.rescale (hf : f.IsEntire) (a : R) : (rescale a f).IsEntire :=
  fun _ ↦ (hf _).rescale

/-- The derivative of an entire series is entire. -/
theorem IsEntire.derivative (hf : f.IsEntire) : (d⁄dX f).IsEntire := by
  rw [← hasseDeriv_one_apply]
  exact hf.hasseDeriv 1

end NormedCommRing

end PowerSeries
