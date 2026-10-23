/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Entire.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm

/-!
# Power series on an open disc

A power series `f = ∑ aₙ Xⁿ` over a normed ring lies *on the open disc* of radius `R₀` when it is
restricted at every radius `0 < r < R₀`, that is, `‖aₙ‖ rⁿ → 0` for each such `r`. No condition
is imposed on the boundary circle `‖x‖ = R₀`: over a complete ultrametric ring such a series can
be summed at every `x` with `‖x‖ < R₀`, being restricted at a radius strictly between `‖x‖`
and `R₀`. These series form the coefficient algebra of analytic functions on an open disc. They
sit between the series restricted at the radius `R₀` and the entire series: a series restricted
at `R₀` lies on the open disc of radius `R₀` (`PowerSeries.IsRestricted.onOpenDisc`), and a
series is entire exactly when it lies on every open disc
(`PowerSeries.isEntire_iff_forall_onOpenDisc`). Mathlib's `FormalMultilinearSeries.radius`
measures the same growth for series of multilinear maps over a nontrivially normed field; here the
coefficients lie in an arbitrary normed ring, which may have nilpotents, and the series are native
power series carrying the restricted-series API.

The condition can equivalently be tested along any family of radii below `R₀` tending to `R₀`
(`PowerSeries.onOpenDisc_iff_of_tendsto`), for instance along a sequence, and it amounts to
bounded weighted coefficient norms at every smaller radius
(`PowerSeries.onOpenDisc_iff_forall_hasGaussNorm`). In particular, a series with bounded
coefficients lies on the open unit disc (`PowerSeries.onOpenDisc_of_bddAbove_norm_coeff`); this is
the inclusion of bounded-coefficient series into the open unit-disc algebra used in Iwasawa theory.

No ultrametric hypothesis is needed for the algebraic structure: products and Hasse derivatives
only lose an arbitrarily small amount of radius, which the open condition absorbs. Thus over any
normed ring the series on the open disc of radius `R₀` form a subring
`PowerSeries.OnOpenDisc.subring R R₀`, stable under Hasse derivatives and bounded coefficient
maps.

The geometric series `∑ aⁿ Xⁿ` lies on the open disc of radius `‖a‖⁻¹`
(`PowerSeries.onOpenDisc_mk_pow`), but for `a ≠ 0` and a multiplicative norm it is not
restricted at that radius (`TauCeti.PowerSeries.not_isRestricted_mk_pow`). Similarly,
over a nontrivial normed ring, `∑ Xⁿ` lies on the open unit disc without being restricted at the
radius `1`
(`PowerSeries.onOpenDisc_mk_one`, `TauCeti.PowerSeries.not_isRestricted_mk_one`).

## Main definitions

* `PowerSeries.OnOpenDisc`: `f` is restricted at every radius `0 < r < R₀`.
* `PowerSeries.OnOpenDisc.subring`: the subring of series on the open disc of radius `R₀`.

## Main results

* `PowerSeries.OnOpenDisc.isRestricted`: a series on the open disc of radius `R₀` is restricted
  at every radius `r` with `|r| < R₀`.
* `PowerSeries.onOpenDisc_iff_of_tendsto`: the condition can be tested along radii tending
  to `R₀` from below.
* `PowerSeries.onOpenDisc_iff_forall_hasGaussNorm`: the condition amounts to bounded weighted
  coefficient norms at every smaller radius.
* `PowerSeries.HasGaussNorm.onOpenDisc`: bounded weighted coefficients at `R₀` give a series on
  the open disc of radius `R₀`; `PowerSeries.onOpenDisc_of_bddAbove_norm_coeff` is the case
  `R₀ = 1`.
* `PowerSeries.IsRestricted.onOpenDisc` and `PowerSeries.isEntire_iff_forall_onOpenDisc`: the
  comparisons with restricted and entire series.
* `PowerSeries.OnOpenDisc.add`, `PowerSeries.OnOpenDisc.mul`, `PowerSeries.onOpenDisc_coe` and
  their companions: these series form a subring containing the polynomials.
* `PowerSeries.OnOpenDisc.hasseDeriv`, `PowerSeries.OnOpenDisc.derivative` and
  `PowerSeries.OnOpenDisc.map`: the condition is preserved by Hasse derivatives and bounded
  coefficient maps.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), 13–59.
-/

public section

namespace PowerSeries

open Filter
open scoped Topology

section NormedRing

variable {R : Type*} [NormedRing R] {R₀ R₁ : ℝ} {f g : R⟦X⟧}

/-- A power series `f = ∑ aₙ Xⁿ` lies *on the open disc* of radius `R₀` when it is restricted at
every radius `0 < r < R₀`, that is, `‖aₙ‖ rⁿ → 0` for each such `r`. -/
def OnOpenDisc (R₀ : ℝ) (f : R⟦X⟧) : Prop :=
  ∀ r : ℝ, 0 < r → r < R₀ → f.IsRestricted r

/-- A series lies on the open disc of radius `R₀` exactly when it is restricted at every radius
`0 < r < R₀`. -/
theorem onOpenDisc_iff : f.OnOpenDisc R₀ ↔ ∀ r : ℝ, 0 < r → r < R₀ → f.IsRestricted r :=
  Iff.rfl

/-- A series on the open disc of radius `R₀` is restricted at every radius `r` with `|r| < R₀`. -/
theorem OnOpenDisc.isRestricted (hf : f.OnOpenDisc R₀) {r : ℝ} (hr : |r| < R₀) :
    f.IsRestricted r := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hr
  have hs : 0 < s := (abs_nonneg r).trans_lt hrs
  exact TauCeti.PowerSeries.isRestricted_of_abs_le (hf s hs hsR)
    (hrs.le.trans_eq (abs_of_pos hs).symm)

/-- For a nonpositive radius `R₀` the open disc is empty, and every series lies on it. -/
theorem onOpenDisc_of_nonpos (h : R₀ ≤ 0) (f : R⟦X⟧) : f.OnOpenDisc R₀ :=
  fun _ hr hrR ↦ absurd (hr.trans hrR) h.not_gt

/-- A series on an open disc lies on every smaller open disc. -/
theorem OnOpenDisc.mono (hf : f.OnOpenDisc R₀) (h : R₁ ≤ R₀) : f.OnOpenDisc R₁ :=
  fun r hr hrR ↦ hf r hr (hrR.trans_le h)

/-- The condition of lying on the open disc of radius `R₀` can be tested along any family of
radii `ρ i` with `|ρ i| < R₀` tending to `R₀`, for instance along a sequence. In particular it
does not depend on the choice of such a family. -/
theorem onOpenDisc_iff_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot] {ρ : ι → ℝ}
    (hρ : ∀ i, |ρ i| < R₀) (hlim : Tendsto ρ l (𝓝 R₀)) :
    f.OnOpenDisc R₀ ↔ ∀ i, f.IsRestricted (ρ i) := by
  refine ⟨fun hf i ↦ hf.isRestricted (hρ i), fun hf r hr hrR ↦ ?_⟩
  obtain ⟨i, hi⟩ := (hlim.eventually (lt_mem_nhds hrR)).exists
  exact TauCeti.PowerSeries.isRestricted_of_abs_le (hf i)
    ((abs_of_pos hr).trans_le (hi.le.trans (le_abs_self _)))

/-- A series restricted at the radius `R₀` lies on the open disc of radius `R₀`. -/
theorem IsRestricted.onOpenDisc (hf : f.IsRestricted R₀) : f.OnOpenDisc R₀ :=
  fun r hr hrR ↦ TauCeti.PowerSeries.isRestricted_of_abs_le hf
    (by rw [abs_of_pos hr, abs_of_pos (hr.trans hrR)]; exact hrR.le)

/-- A series whose weighted coefficient norms `‖aₙ‖ R₀ⁿ` are bounded lies on the open disc of
radius `R₀`. -/
theorem HasGaussNorm.onOpenDisc (hf : f.HasGaussNorm norm R₀) : f.OnOpenDisc R₀ :=
  fun _ hr hrR ↦ hf.isRestricted_of_abs_lt ((abs_of_pos hr).trans_lt hrR)

/-- A series lies on the open disc of radius `R₀` exactly when its weighted coefficient norms are
bounded at every radius `0 < r < R₀`. -/
theorem onOpenDisc_iff_forall_hasGaussNorm :
    f.OnOpenDisc R₀ ↔ ∀ r : ℝ, 0 < r → r < R₀ → f.HasGaussNorm norm r := by
  refine ⟨fun hf r hr hrR ↦ TauCeti.PowerSeries.hasGaussNorm_of_isRestricted (hf r hr hrR),
    fun hf r hr hrR ↦ ?_⟩
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  exact (hf s (hr.trans hrs) hsR).isRestricted_of_abs_lt ((abs_of_pos hr).trans_lt hrs)

/-- A series with bounded coefficients lies on the open unit disc. -/
theorem onOpenDisc_of_bddAbove_norm_coeff (hf : BddAbove (Set.range fun n ↦ ‖coeff n f‖)) :
    f.OnOpenDisc 1 :=
  HasGaussNorm.onOpenDisc (by simpa only [HasGaussNorm, one_pow, mul_one] using hf)

/-- An entire series lies on every open disc. -/
theorem IsEntire.onOpenDisc (hf : f.IsEntire) (R₀ : ℝ) : f.OnOpenDisc R₀ :=
  fun r _ _ ↦ hf.isRestricted r

/-- A series is entire exactly when it lies on every open disc. -/
theorem isEntire_iff_forall_onOpenDisc : f.IsEntire ↔ ∀ R₀ : ℝ, f.OnOpenDisc R₀ := by
  refine ⟨fun hf R₀ ↦ hf.onOpenDisc R₀, fun hf ↦ isEntire_iff_forall_pos.mpr fun r hr ↦ ?_⟩
  exact hf (r + 1) r hr (lt_add_one r)

/-- The zero series lies on every open disc. -/
@[simp]
theorem onOpenDisc_zero : (0 : R⟦X⟧).OnOpenDisc R₀ :=
  isEntire_zero.onOpenDisc R₀

/-- The constant series `1` lies on every open disc. -/
@[simp]
theorem onOpenDisc_one : (1 : R⟦X⟧).OnOpenDisc R₀ :=
  isEntire_one.onOpenDisc R₀

/-- Constant series lie on every open disc. -/
@[simp]
theorem onOpenDisc_C (a : R) : (C a).OnOpenDisc R₀ :=
  (isEntire_C a).onOpenDisc R₀

/-- Monomials lie on every open disc. -/
@[simp]
theorem onOpenDisc_monomial (n : ℕ) (a : R) : (monomial n a).OnOpenDisc R₀ :=
  (isEntire_monomial n a).onOpenDisc R₀

/-- The variable `X` lies on every open disc. -/
@[simp]
theorem onOpenDisc_X : (X : R⟦X⟧).OnOpenDisc R₀ :=
  isEntire_X.onOpenDisc R₀

/-- Every polynomial lies on every open disc. -/
@[simp]
theorem onOpenDisc_coe (p : Polynomial R) : (p : R⟦X⟧).OnOpenDisc R₀ :=
  (isEntire_coe p).onOpenDisc R₀

/-- A sum of series on an open disc lies on that disc. -/
theorem OnOpenDisc.add (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) : (f + g).OnOpenDisc R₀ :=
  fun r hr hrR ↦ (hf r hr hrR).add (hg r hr hrR)

/-- The negative of a series on an open disc lies on that disc. -/
theorem OnOpenDisc.neg (hf : f.OnOpenDisc R₀) : (-f).OnOpenDisc R₀ :=
  fun r hr hrR ↦ (hf r hr hrR).neg

/-- A difference of series on an open disc lies on that disc. -/
theorem OnOpenDisc.sub (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) : (f - g).OnOpenDisc R₀ :=
  fun r hr hrR ↦ (hf r hr hrR).sub (hg r hr hrR)

/-- A scalar multiple `a • f` of a series on an open disc lies on that disc. -/
theorem OnOpenDisc.smul (a : R) (hf : f.OnOpenDisc R₀) : (a • f).OnOpenDisc R₀ :=
  fun r hr hrR ↦ (hf r hr hrR).smul a

/-- A finite sum of series on an open disc lies on that disc. -/
theorem OnOpenDisc.sum {ι : Type*} {s : Finset ι} {f : ι → R⟦X⟧}
    (hf : ∀ i ∈ s, (f i).OnOpenDisc R₀) : (∑ i ∈ s, f i).OnOpenDisc R₀ :=
  fun r hr hrR ↦ MvPowerSeries.IsRestricted.sum fun i hi ↦ hf i hi r hr hrR

/-- A product of series on an open disc lies on that disc. Over a general normed ring, the
product of two series restricted at a radius `s` is only restricted at the radii below `s`; the
open condition provides such an `s` between `r` and `R₀`. -/
theorem OnOpenDisc.mul (hf : f.OnOpenDisc R₀) (hg : g.OnOpenDisc R₀) : (f * g).OnOpenDisc R₀ := by
  intro r hr hrR
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs : 0 < s := hr.trans hrs
  exact (hf s hs hsR).mul_of_abs_lt (hg s hs hsR) (by rwa [abs_of_pos hr, abs_of_pos hs])

/-- A power of a series on an open disc lies on that disc. -/
theorem OnOpenDisc.pow (hf : f.OnOpenDisc R₀) (n : ℕ) : (f ^ n).OnOpenDisc R₀ := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

/-- Hasse derivatives of a series on an open disc lie on that disc. -/
theorem OnOpenDisc.hasseDeriv (hf : f.OnOpenDisc R₀) (k : ℕ) :
    (PowerSeries.hasseDeriv k f).OnOpenDisc R₀ := by
  intro r hr hrR
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs : 0 < s := hr.trans hrs
  exact (hf s hs hsR).hasseDeriv_of_abs_lt (by rwa [abs_of_pos hr, abs_of_pos hs]) k

/-- A bounded ring homomorphism `φ`, `‖φ x‖ ≤ C ‖x‖`, maps series on an open disc to series on
that disc coefficientwise. -/
theorem OnOpenDisc.map {S : Type*} [NormedRing S] (hf : f.OnOpenDisc R₀) (φ : R →+* S) {C : ℝ}
    (hφ : ∀ x, ‖φ x‖ ≤ C * ‖x‖) : (map φ f).OnOpenDisc R₀ :=
  -- `PowerSeries.map φ` is `MvPowerSeries.map φ` in the single variable `Unit`.
  fun r hr hrR ↦ (hf r hr hrR).map φ hφ

/-- The geometric series `∑ aⁿ Xⁿ` lies on the open disc of radius `‖a‖⁻¹`: at a radius
`r < ‖a‖⁻¹`, its weighted coefficient norms are bounded by `(‖a‖ r)ⁿ` from `n = 1` on. -/
theorem onOpenDisc_mk_pow (a : R) : (mk fun n ↦ a ^ n).OnOpenDisc ‖a‖⁻¹ := by
  intro r hr hra
  have ha : 0 < ‖a‖ := inv_pos.mp (hr.trans hra)
  have har : ‖a‖ * r < 1 :=
    calc ‖a‖ * r < ‖a‖ * ‖a‖⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ ha.ne'
  rw [isRestricted_iff']
  refine squeeze_zero' (.of_forall fun n ↦ by positivity) ?_
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) har)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [coeff_mk, mul_pow]
  exact mul_le_mul_of_nonneg_right (norm_pow_le' a hn) (by positivity)

/-- The series `∑ Xⁿ` lies on the open unit disc, its coefficients being bounded. -/
theorem onOpenDisc_mk_one : (mk 1 : R⟦X⟧).OnOpenDisc 1 :=
  onOpenDisc_of_bddAbove_norm_coeff ⟨‖(1 : R)‖, by simp [upperBounds]⟩

variable (R) in
/-- The power series on the open disc of radius `R₀` form a subring. -/
protected noncomputable def OnOpenDisc.subring (R₀ : ℝ) : Subring R⟦X⟧ where
  carrier := {f | f.OnOpenDisc R₀}
  zero_mem' := onOpenDisc_zero
  one_mem' := onOpenDisc_one
  add_mem' := fun hf hg ↦ hf.add hg
  mul_mem' := fun hf hg ↦ hf.mul hg
  neg_mem' := fun hf ↦ hf.neg

/-- Membership in the subring of series on the open disc of radius `R₀` is lying on that disc. -/
@[simp]
theorem OnOpenDisc.mem_subring : f ∈ OnOpenDisc.subring R R₀ ↔ f.OnOpenDisc R₀ :=
  Iff.rfl

variable (R) in
/-- The subring of series on the open disc of radius `R₀` shrinks as `R₀` grows. -/
theorem OnOpenDisc.subring_antitone : Antitone (OnOpenDisc.subring R) :=
  fun _ _ h _ hf ↦ OnOpenDisc.mono hf h

/-- Entire series lie in the subring of series on every open disc. -/
theorem IsEntire.subring_le_onOpenDiscSubring (R₀ : ℝ) :
    IsEntire.subring R ≤ OnOpenDisc.subring R R₀ :=
  fun _ hf ↦ (IsEntire.mem_subring.mp hf).onOpenDisc R₀

/-- Over an ultrametric ring, the subring of series restricted at `R₀` lies in the subring of
series on the open disc of radius `R₀`. -/
theorem IsRestricted.subring_le_onOpenDiscSubring [IsUltrametricDist R] (R₀ : ℝ) :
    IsRestricted.subring R₀ ≤ OnOpenDisc.subring R R₀ :=
  fun _ hf ↦ IsRestricted.onOpenDisc hf

end NormedRing

section NormedCommRing

variable {R : Type*} [NormedCommRing R] {R₀ : ℝ} {f : R⟦X⟧}

/-- The derivative of a series on an open disc lies on that disc. -/
theorem OnOpenDisc.derivative (hf : f.OnOpenDisc R₀) : (d⁄dX f).OnOpenDisc R₀ := by
  rw [← hasseDeriv_one_apply]
  exact hf.hasseDeriv 1

end NormedCommRing

end PowerSeries
