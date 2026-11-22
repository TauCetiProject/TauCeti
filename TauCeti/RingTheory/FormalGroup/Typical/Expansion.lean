/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Araki
public import TauCeti.RingTheory.FormalGroup.Curve.Expansion

/-!
# `p`-typical curves and isomorphisms through formal-group expansions

Let `F` be a commutative `p`-typical formal group law over a commutative ring `R` in which every
prime `q ≠ p` is invertible, and write a curve as its formal-group expansion
`γ(T) = ∑^F_{n ≥ 1} cₙ Tⁿ` (`FormalGroup.Curve.expansionCoeff`). Then `γ` is `p`-typical exactly
when `cₙ = 0` for every `n` that is not a power of `p`
(`FormalGroup.Curve.isPTypical_iff_forall_expansionCoeff_eq_zero`), that is, exactly when
`γ(T) = ∑^F_{i ≥ 0} tᵢ T^(pⁱ)` for some `tᵢ ∈ R`
(`FormalGroup.Curve.isPTypical_iff_exists_coeff_eq_sum_pow`); the `tᵢ` are unique, equal to
`c_(pⁱ)`. Applied to the inverse of an isomorphism this is Ravenel's Lemma A2.1.26: an isomorphism
`f : F → G` out of a `p`-typical law has `p`-typical target exactly when
`f⁻¹(T) = ∑^F_{i ≥ 0} tᵢ T^(pⁱ)`
(`TauCeti.FormalGroupIso.isPTypical_iff_exists_coeff_invHom_eq_sum_pow`); here `t₀` is the linear
coefficient of `f⁻¹`, a unit. These parameters `tᵢ` describe the isomorphisms between `p`-typical
laws.

As infinite formal-group sums are stated coefficientwise, `γ(T) = ∑^F_{i ≥ 0} tᵢ T^(pⁱ)` means that
`γ` agrees with `∑^F_{i < N} tᵢ T^(pⁱ)` below degree `p^N` for every `N`. For the `p`-series the
expansion coefficients in degrees `pⁱ` are the Araki coefficients
(`FormalGroup.arakiCoeff_eq_expansionCoeff`).

The hypothesis that `F` is `p`-typical cannot be dropped in either direction, and the invertibility
of the primes `q ≠ p` is needed to show that a `p`-typical curve has no expansion terms outside the
degrees `pⁱ`: over `𝔽₂` the curve `T²` on the additive law is `3`-typical.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2, Lemma A2.1.26 and its proof.
-/

public section

open Finset
open PowerSeries (coeff)

namespace FormalGroup

variable {R : Type*} [CommRing R] {F : FormalGroup R} [F.IsComm] {p : ℕ}

namespace Curve

/-- A finite formal-group sum of monomial curves on a `p`-typical law is `p`-typical when its
terms outside the degrees `pⁱ` vanish. -/
private theorem isPTypical_sum_monomialCurve (hF : F.IsPTypical p) (hp : p.Prime) (c : ℕ → R)
    (N : ℕ) (hc : ∀ j < N, (∀ k, j + 1 ≠ p ^ k) → c (j + 1) = 0) :
    (∑ j ∈ range N, F.monomialCurve (j + 1) j.succ_ne_zero (c (j + 1))).IsPTypical p := by
  refine (F.mem_pTypicalCurveSubgroup p _).1 (sum_mem fun j hj ↦ ?_)
  by_cases hpow : ∃ k, j + 1 = p ^ k
  · obtain ⟨k, hk⟩ := hpow
    have h : F.monomialCurve (j + 1) j.succ_ne_zero (c (j + 1)) =
        F.monomialCurve (p ^ k) (pow_ne_zero k hp.ne_zero) (c (j + 1)) :=
      Curve.ext (by simp [hk])
    rw [h]
    exact (F.mem_pTypicalCurveSubgroup p _).2 (hF.monomialCurve_pow hp k _)
  · rw [hc j (mem_range.mp hj) fun k hk ↦ hpow ⟨k, hk⟩, monomialCurve_zero]
    exact zero_mem _

/-- On a `p`-typical law, a curve whose formal-group expansion has no terms outside the degrees
`pⁱ` is `p`-typical. -/
theorem isPTypical_of_forall_expansionCoeff_eq_zero (hF : F.IsPTypical p) (hp : p.Prime)
    {γ : F.Curve} (h : ∀ n, (∀ k, n ≠ p ^ k) → γ.expansionCoeff n = 0) : γ.IsPTypical p :=
  isPTypical_of_forall_exists_coeff_eq fun N ↦
    ⟨_, isPTypical_sum_monomialCurve hF hp _ N fun j _ ↦ h (j + 1),
      fun _ hk ↦ γ.coeff_sum_expansionCoeff hk⟩

/-- On a `p`-typical law over a ring in which every prime `q ≠ p` is invertible, the formal-group
expansion of a `p`-typical curve has no terms outside the degrees `pⁱ`. -/
theorem IsPTypical.expansionCoeff_eq_zero (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p)
    {n : ℕ} (hn : ∀ k, n ≠ p ^ k) : γ.expansionCoeff n = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · exact γ.expansionCoeff_zero
    have hs := isPTypical_sum_monomialCurve hF hp γ.expansionCoeff n
      fun j hj hpow ↦ ih (j + 1) (by omega) hpow
    rw [expansionCoeff_succ]
    refine (hγ.sub hs).coeff_eq_zero_of_forall_lt hunit hn fun i hi ↦ ?_
    rw [Curve.coeff_sub_congr (fun j hj ↦
        (γ.coeff_sum_expansionCoeff (hj.trans (Nat.lt_succ_iff.mp hi))).symm) (fun _ _ ↦ rfl),
      sub_self, toPowerSeries_zero, map_zero]

/-- **`p`-typical curves through their expansion.** On a `p`-typical law over a ring in which every
prime `q ≠ p` is invertible, a curve is `p`-typical if and only if its formal-group expansion has
no terms outside the degrees `pⁱ`. -/
theorem isPTypical_iff_forall_expansionCoeff_eq_zero (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    γ.IsPTypical p ↔ ∀ n, (∀ k, n ≠ p ^ k) → γ.expansionCoeff n = 0 :=
  ⟨fun hγ _ ↦ hγ.expansionCoeff_eq_zero hF hp hunit,
    isPTypical_of_forall_expansionCoeff_eq_zero hF hp⟩

/-- Below degree `p ^ N`, a finite formal-group sum of monomial curves whose terms outside the
degrees `pⁱ` vanish is the formal-group sum of its terms in the degrees `pⁱ`, `i < N`. -/
private theorem sum_range_monomialCurve_eq_sum_pow (hp : p.Prime) (c : ℕ → R)
    (hc : ∀ n, (∀ k, n ≠ p ^ k) → c n = 0) (N : ℕ) :
    ∑ j ∈ range (p ^ N - 1), F.monomialCurve (j + 1) j.succ_ne_zero (c (j + 1)) =
      ∑ i ∈ range N, F.monomialCurve (p ^ i) (pow_ne_zero i hp.ne_zero) (c (p ^ i)) := by
  classical
  let g : ℕ → F.Curve := fun d ↦ if hd : d = 0 then 0 else F.monomialCurve d hd (c d)
  obtain ⟨M, hM⟩ : ∃ M, p ^ N = M + 1 :=
    Nat.exists_eq_add_one_of_ne_zero (pow_ne_zero N hp.ne_zero)
  have h₁ : ∑ j ∈ range (p ^ N - 1), F.monomialCurve (j + 1) j.succ_ne_zero (c (j + 1)) =
      ∑ d ∈ range (p ^ N), g d := by
    rw [hM, Nat.add_sub_cancel, sum_range_succ']
    simp [g]
  have h₂ : ∑ i ∈ range N, F.monomialCurve (p ^ i) (pow_ne_zero i hp.ne_zero) (c (p ^ i)) =
      ∑ d ∈ (range N).image (p ^ ·), g d := by
    rw [sum_image fun i _ j _ h ↦ Nat.pow_right_injective hp.two_le h]
    exact sum_congr rfl fun i _ ↦ by simp [g, hp.ne_zero]
  rw [h₁, h₂]
  refine (sum_subset (fun d hd ↦ ?_) fun d hd hd' ↦ ?_).symm
  · obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
    exact mem_range.mpr (Nat.pow_lt_pow_right hp.one_lt (mem_range.mp hi))
  · have hpow (k : ℕ) : d ≠ p ^ k := by
      rintro rfl
      exact hd' (mem_image_of_mem _ (mem_range.mpr
        ((Nat.pow_lt_pow_iff_right hp.one_lt).mp (mem_range.mp hd))))
    simp [g, hc d hpow]

/-- A `p`-typical curve `γ` on a `p`-typical law, over a ring in which every prime `q ≠ p` is
invertible, is the formal-group sum `∑^F_{i ≥ 0} c_(pⁱ) T^(pⁱ)` of its expansion terms in the
degrees `pⁱ`: it agrees with `∑^F_{i < N} c_(pⁱ) T^(pⁱ)` below degree `p ^ N`. -/
theorem IsPTypical.coeff_eq_coeff_sum_expansionCoeff_pow (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p)
    {N k : ℕ} (hk : k < p ^ N) :
    coeff k γ.toPowerSeries = coeff k (∑ i ∈ range N, F.monomialCurve (p ^ i)
      (pow_ne_zero i hp.ne_zero) (γ.expansionCoeff (p ^ i))).toPowerSeries := by
  rw [← γ.coeff_sum_expansionCoeff (N := p ^ N - 1) (by omega),
    sum_range_monomialCurve_eq_sum_pow hp _ fun _ ↦ hγ.expansionCoeff_eq_zero hF hp hunit]

/-- The coefficients `tᵢ` of a formal-group sum `∑^F_{i ≥ 0} tᵢ T^(pⁱ)` are unique: two families
whose partial sums `∑^F_{i < N} tᵢ T^(pⁱ)` both agree with `γ` below degree `p ^ N`, for every `N`,
are equal. -/
theorem eq_of_forall_coeff_eq_sum_pow (hp : 1 < p) {γ : F.Curve} {t t' : ℕ → R}
    (ht : ∀ N, ∀ k < p ^ N, coeff k γ.toPowerSeries = coeff k (∑ i ∈ range N,
      F.monomialCurve (p ^ i) (pow_ne_zero i (Nat.ne_zero_of_lt hp)) (t i)).toPowerSeries)
    (ht' : ∀ N, ∀ k < p ^ N, coeff k γ.toPowerSeries = coeff k (∑ i ∈ range N,
      F.monomialCurve (p ^ i) (pow_ne_zero i (Nat.ne_zero_of_lt hp)) (t' i)).toPowerSeries) :
    t = t' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hlt : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp n.lt_succ_self
    have hsum :
        ∑ i ∈ range n, F.monomialCurve (p ^ i) (pow_ne_zero i (Nat.ne_zero_of_lt hp)) (t i) =
          ∑ i ∈ range n, F.monomialCurve (p ^ i) (pow_ne_zero i (Nat.ne_zero_of_lt hp)) (t' i) :=
      sum_congr rfl fun i hi ↦ by rw [ih i (mem_range.mp hi)]
    have h := (ht (n + 1) (p ^ n) hlt).symm.trans (ht' (n + 1) (p ^ n) hlt)
    rw [sum_range_succ, sum_range_succ, hsum, Curve.coeff_add_monomialCurve_self,
      Curve.coeff_add_monomialCurve_self] at h
    exact add_left_cancel h

/-- **`p`-typical curves as formal-group sums in the degrees `pⁱ`.** On a `p`-typical law over a
ring in which every prime `q ≠ p` is invertible, a curve `γ` is `p`-typical if and only if
`γ(T) = ∑^F_{i ≥ 0} tᵢ T^(pⁱ)` for some `tᵢ ∈ R`, that is, `γ` agrees with
`∑^F_{i < N} tᵢ T^(pⁱ)` below degree `p ^ N` for every `N`. -/
theorem isPTypical_iff_exists_coeff_eq_sum_pow (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    γ.IsPTypical p ↔ ∃ t : ℕ → R, ∀ N, ∀ k < p ^ N, coeff k γ.toPowerSeries =
      coeff k (∑ i ∈ range N,
        F.monomialCurve (p ^ i) (pow_ne_zero i hp.ne_zero) (t i)).toPowerSeries := by
  refine ⟨fun hγ ↦ ⟨fun i ↦ γ.expansionCoeff (p ^ i),
    fun _ _ hk ↦ hγ.coeff_eq_coeff_sum_expansionCoeff_pow hF hp hunit hk⟩, fun ⟨t, ht⟩ ↦ ?_⟩
  refine isPTypical_of_forall_exists_coeff_eq fun N ↦
    ⟨∑ i ∈ range N, F.monomialCurve (p ^ i) (pow_ne_zero i hp.ne_zero) (t i),
      (F.mem_pTypicalCurveSubgroup p _).1
        (sum_mem fun i _ ↦ (F.mem_pTypicalCurveSubgroup p _).2 (hF.monomialCurve_pow hp i (t i))),
      fun k hk ↦ (ht N k (hk.trans_lt (Nat.lt_pow_self hp.one_lt))).symm⟩

/-- If `γ(T) = ∑^F_{i ≥ 0} tᵢ T^(pⁱ)` on a `p`-typical law over a ring in which every prime
`q ≠ p` is invertible, then each `tᵢ` is the expansion coefficient of `γ` in degree `pⁱ`. -/
theorem expansionCoeff_pow_eq_of_forall_coeff_eq_sum_pow (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} {t : ℕ → R}
    (ht : ∀ N, ∀ k < p ^ N, coeff k γ.toPowerSeries = coeff k (∑ i ∈ range N,
      F.monomialCurve (p ^ i) (pow_ne_zero i hp.ne_zero) (t i)).toPowerSeries) (i : ℕ) :
    γ.expansionCoeff (p ^ i) = t i := by
  have hγ := (isPTypical_iff_exists_coeff_eq_sum_pow hF hp hunit γ).2 ⟨t, ht⟩
  exact congrFun (eq_of_forall_coeff_eq_sum_pow hp.one_lt
    (fun _ _ hk ↦ hγ.coeff_eq_coeff_sum_expansionCoeff_pow hF hp hunit hk) ht) i

end Curve

/-- The Araki coefficients of a `p`-typical law over a ring in which every prime `q ≠ p` is
invertible are the expansion coefficients of its `p`-series in the degrees `pⁱ`. -/
theorem arakiCoeff_eq_expansionCoeff (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ) :
    F.arakiCoeff hp n = (p • F.tautologicalCurve).expansionCoeff (p ^ n) := by
  refine (Curve.expansionCoeff_pow_eq_of_forall_coeff_eq_sum_pow hF hp hunit
    (fun N k hk ↦ ?_) n).symm
  rw [Curve.toPowerSeries_nsmul, toPowerSeries_tautologicalCurve, PowerSeries.X_subst]
  exact F.coeff_nsmulSeries_eq_sum_arakiCoeff hp hF hunit hk

end FormalGroup

namespace TauCeti.FormalGroupIso

open FormalGroup

variable {R : Type*} [CommRing R] {F G : FormalGroup R} [F.IsComm] [G.IsComm] {p : ℕ}

/-- An isomorphism `f : F → G` out of a `p`-typical law, over a ring in which every prime `q ≠ p`
is invertible, has `p`-typical target if and only if the formal-group expansion
`f⁻¹(T) = ∑^F_{n ≥ 1} cₙ Tⁿ` of its inverse on `F` has no terms outside the degrees `pⁱ`. -/
theorem isPTypical_iff_forall_expansionCoeff_eq_zero (e : FormalGroupIso F G)
    (hF : F.IsPTypical p) (hp : p.Prime) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    G.IsPTypical p ↔ ∀ n, (∀ k, n ≠ p ^ k) →
      (e.invHom.mapCurve G.tautologicalCurve).expansionCoeff n = 0 := by
  rw [isPTypical_def, ← Curve.isPTypical_invHom_mapCurve_iff e p,
    Curve.isPTypical_iff_forall_expansionCoeff_eq_zero hF hp hunit]

/-- **Ravenel's Lemma A2.1.26.** An isomorphism `f : F → G` out of a `p`-typical law, over a ring
in which every prime `q ≠ p` is invertible, has `p`-typical target if and only if
`f⁻¹(T) = ∑^F_{i ≥ 0} tᵢ T^(pⁱ)` for some `tᵢ ∈ R`, the sum taken in `F`: `f⁻¹` agrees with
`∑^F_{i < N} tᵢ T^(pⁱ)` below degree `p ^ N` for every `N`. -/
theorem isPTypical_iff_exists_coeff_invHom_eq_sum_pow (e : FormalGroupIso F G)
    (hF : F.IsPTypical p) (hp : p.Prime) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    G.IsPTypical p ↔ ∃ t : ℕ → R, ∀ N, ∀ k < p ^ N, coeff k e.invHom.toPowerSeries =
      coeff k (∑ i ∈ range N,
        F.monomialCurve (p ^ i) (pow_ne_zero i hp.ne_zero) (t i)).toPowerSeries := by
  rw [isPTypical_def, ← Curve.isPTypical_invHom_mapCurve_iff e p,
    Curve.isPTypical_iff_exists_coeff_eq_sum_pow hF hp hunit,
    FormalGroupHom.mapCurve_tautologicalCurve]

end TauCeti.FormalGroupIso
