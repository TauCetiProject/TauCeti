/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Typical

/-!
# Expansions of curves in the degrees `p ^ i`

Let `F` be a formal group law over a commutative ring `R` and `p ≠ 0`. Every curve `γ` on `F`
has **`p`-typical expansion coefficients** `t_i = γ.pTypicalCoeff hp i`
(`FormalGroup.Curve.pTypicalCoeff`): `t_i` is the coefficient of `X ^ (p ^ i)` in the residual
`γ -_F ∑^F_{j < i} t_j X ^ (p ^ j)`, the differences and sums being taken in `F` (the finite sums
need `F` commutative). For the `p`-series `[p]_F(X)` these are the Araki coefficients
`FormalGroup.arakiCoeff`.

For `p` prime, `F` `p`-typical and every prime `q ≠ p` invertible in `R`, a curve `γ` on `F` is
`p`-typical exactly when it is the formal-group sum `γ = ∑^F_{i ≥ 0} t_i X ^ (p ^ i)` for some
family `t`, and then `t` is its family of `p`-typical expansion coefficients. The infinite sum is
stated coefficientwise: `γ` agrees with `∑^F_{i < n} t_i X ^ (p ^ i)` below degree `p ^ n` for
every `n`. Applied to the inverse series of an isomorphism `f : F ≅ G` out of a `p`-typical law,
this is Ravenel's Lemma A2.1.26: `G` is `p`-typical exactly when
`f⁻¹(X) = ∑^F_{i ≥ 0} t_i X ^ (p ^ i)` with `t_0` a unit, and `t_0 = 1` when the isomorphism is
strict. Ravenel uses these expansions to parametrize strict isomorphisms of `p`-typical laws.

## Main definitions

* `FormalGroup.Curve.pTypicalCoeff`: the `p`-typical expansion coefficients of a curve.

## Main results

* `FormalGroup.Curve.pTypicalCoeff_eq_coeff_sub_sum`: the defining recursion.
* `FormalGroup.Curve.eq_pTypicalCoeff_of_coeff_eq_coeff_sum`: uniqueness of `p`-typical
  expansions.
* `FormalGroup.Curve.IsPTypical.coeff_eq_coeff_sum_pTypicalCoeff`,
  `FormalGroup.Curve.isPTypical_of_coeff_eq_coeff_sum` and
  `FormalGroup.Curve.isPTypical_iff_exists_coeff_eq_coeff_sum`: a curve on a `p`-typical law is
  `p`-typical exactly when it has a `p`-typical expansion.
* `TauCeti.FormalGroupIso.isPTypical_iff_exists_coeff_invHom_eq_coeff_sum` and
  `TauCeti.FormalGroupIso.isPTypical_iff_exists_coeff_invHom_eq_coeff_sum_of_isStrict`:
  Ravenel's Lemma A2.1.26 for isomorphisms out of a `p`-typical law.

## References

* P. Cartier, *Modules associés à un groupe formel commutatif. Courbes typiques*, C. R. Acad. Sci.
  Paris Sér. A-B 265 (1967), A129–A132.
* [M. Hazewinkel, *Formal Groups and Applications*][hazewinkel1978], Chapter III, §16.
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2, Lemma A2.1.26 and its proof.
-/

public section

open Finset
open PowerSeries (coeff)

namespace FormalGroup

variable {R S : Type*} [CommRing R] [CommRing S]

namespace Curve

variable {F : FormalGroup R} {p : ℕ}

private noncomputable def pTypicalPartialSum (γ : F.Curve) (hp : p ≠ 0) : ℕ → F.Curve
  | 0 => 0
  | n + 1 =>
      let s := pTypicalPartialSum γ hp n
      s + F.monomialCurve (p ^ n) (pow_ne_zero n hp) (coeff (p ^ n) (γ - s).toPowerSeries)

/-- The `p`-typical expansion coefficients of a curve `γ` on `F`: `γ.pTypicalCoeff hp n` is the
coefficient of `X ^ (p ^ n)` in `γ -_F ∑^F_{j < n} t_j X ^ (p ^ j)`, where `t_j` are the previous
coefficients. On a `p`-typical law with every prime `q ≠ p` invertible, a `p`-typical curve is the
formal-group sum `∑^F_{j ≥ 0} t_j X ^ (p ^ j)`
(`FormalGroup.Curve.IsPTypical.coeff_eq_coeff_sum_pTypicalCoeff`). -/
noncomputable def pTypicalCoeff (γ : F.Curve) (hp : p ≠ 0) (n : ℕ) : R :=
  coeff (p ^ n) (γ - pTypicalPartialSum γ hp n).toPowerSeries

private theorem pTypicalPartialSum_succ (γ : F.Curve) (hp : p ≠ 0) (n : ℕ) :
    γ.pTypicalPartialSum hp (n + 1) = γ.pTypicalPartialSum hp n +
      F.monomialCurve (p ^ n) (pow_ne_zero n hp) (γ.pTypicalCoeff hp n) := by
  rw [pTypicalPartialSum, pTypicalCoeff]

/-- The first `p`-typical expansion coefficient of a curve is its linear coefficient. -/
@[simp]
theorem pTypicalCoeff_zero (γ : F.Curve) (hp : p ≠ 0) :
    γ.pTypicalCoeff hp 0 = coeff 1 γ.toPowerSeries := by
  simp [pTypicalCoeff, pTypicalPartialSum]

private theorem map_pTypicalPartialSum (γ : F.Curve) (hp : p ≠ 0) (φ : R →+* S) (n : ℕ) :
    Curve.map φ (γ.pTypicalPartialSum hp n) = (Curve.map φ γ).pTypicalPartialSum hp n := by
  induction n with
  | zero => simp [pTypicalPartialSum]
  | succ n ih =>
    simp only [pTypicalPartialSum_succ, map_add, ih, map_monomialCurve, pTypicalCoeff,
      ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_sub]

/-- The `p`-typical expansion coefficients of a curve commute with base change. -/
@[simp]
theorem map_pTypicalCoeff (γ : F.Curve) (hp : p ≠ 0) (φ : R →+* S) (n : ℕ) :
    φ (γ.pTypicalCoeff hp n) = (Curve.map φ γ).pTypicalCoeff hp n := by
  simp only [pTypicalCoeff, ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_sub,
    map_pTypicalPartialSum]

variable [F.IsComm]

private theorem pTypicalPartialSum_eq_sum (γ : F.Curve) (hp : p ≠ 0) (n : ℕ) :
    γ.pTypicalPartialSum hp n =
      ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp) (γ.pTypicalCoeff hp j) := by
  induction n with
  | zero => simp [pTypicalPartialSum]
  | succ n ih => rw [pTypicalPartialSum_succ, sum_range_succ, ih]

/-- The defining recursion of the `p`-typical expansion coefficients: `t_n` is the coefficient of
`X ^ (p ^ n)` in `γ -_F ∑^F_{j < n} t_j X ^ (p ^ j)`. -/
theorem pTypicalCoeff_eq_coeff_sub_sum (γ : F.Curve) (hp : p ≠ 0) (n : ℕ) :
    γ.pTypicalCoeff hp n = coeff (p ^ n)
      (γ - ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp)
        (γ.pTypicalCoeff hp j)).toPowerSeries := by
  rw [pTypicalCoeff, pTypicalPartialSum_eq_sum]

/-- **Uniqueness of `p`-typical expansions.** If `γ` agrees with `∑^F_{j < n} t_j X ^ (p ^ j)`
below degree `p ^ n` for every `n`, then `t` is the family of `p`-typical expansion coefficients
of `γ`. -/
theorem eq_pTypicalCoeff_of_coeff_eq_coeff_sum (γ : F.Curve) (hp : 1 < p) {t : ℕ → R}
    (h : ∀ n k, k < p ^ n → coeff k γ.toPowerSeries = coeff k
      (∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j (Nat.ne_zero_of_lt hp))
        (t j)).toPowerSeries) :
    t = γ.pTypicalCoeff (Nat.ne_zero_of_lt hp) := by
  have hp0 : p ≠ 0 := Nat.ne_zero_of_lt hp
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    let m (c : R) := F.monomialCurve (p ^ n) (pow_ne_zero n hp0) c
    let s := ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp0) (t j)
    have hs : s = ∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp0)
        (γ.pTypicalCoeff hp0 j) :=
      sum_congr rfl fun j hj ↦ by rw [ih j (mem_range.mp hj)]
    have hγ (i : ℕ) (hi : i ≤ p ^ n) :
        coeff i γ.toPowerSeries = coeff i (s + m (t n)).toPowerSeries := by
      rw [h (n + 1) i (hi.trans_lt (Nat.pow_lt_pow_right hp (Nat.lt_succ_self n))),
        sum_range_succ]
    rw [pTypicalCoeff_eq_coeff_sub_sum, ← hs, coeff_sub_congr hγ fun _ _ ↦ rfl,
      add_sub_cancel_left]
    simp [m]

private theorem coeff_sub_pTypicalPartialSum_succ_of_le (γ : F.Curve) (hp : p ≠ 0) (n : ℕ)
    (h : ∀ k < p ^ n, coeff k (γ - γ.pTypicalPartialSum hp n).toPowerSeries = 0)
    {k : ℕ} (hk : k ≤ p ^ n) :
    coeff k (γ - γ.pTypicalPartialSum hp (n + 1)).toPowerSeries = 0 := by
  rw [pTypicalPartialSum_succ, ← sub_sub]
  let t := F.monomialCurve (p ^ n) (pow_ne_zero n hp) (γ.pTypicalCoeff hp n)
  have ht (i : ℕ) (hi : i ≤ k) :
      coeff i (γ - γ.pTypicalPartialSum hp n).toPowerSeries = coeff i t.toPowerSeries := by
    rcases (hi.trans hk).lt_or_eq with hil | rfl
    · simp [t, h i hil, PowerSeries.coeff_X_pow, hil.ne]
    · simp [t, pTypicalCoeff]
  rw [coeff_sub_congr ht (fun _ _ ↦ rfl), sub_self, toPowerSeries_zero, map_zero]

private theorem isPTypical_pTypicalPartialSum (hF : F.IsPTypical p) (hp : p.Prime) (γ : F.Curve)
    (n : ℕ) : (γ.pTypicalPartialSum hp.ne_zero n).IsPTypical p := by
  rw [pTypicalPartialSum_eq_sum]
  exact hF.sum_monomialCurve_pow hp _ _

private theorem coeff_sub_pTypicalPartialSum_eq_zero (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p)
    (n : ℕ) : ∀ k < p ^ n, coeff k (γ - γ.pTypicalPartialSum hp.ne_zero n).toPowerSeries = 0 := by
  induction n with
  | zero =>
    intro k hk
    simp only [pow_zero, Nat.lt_one_iff] at hk
    subst k
    exact coeff_zero_toPowerSeries _
  | succ n ih =>
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ihk =>
      intro hk
      by_cases hle : k ≤ p ^ n
      · exact coeff_sub_pTypicalPartialSum_succ_of_le γ hp.ne_zero n ih hle
      have hpower (j : ℕ) : k ≠ p ^ j := by
        intro he
        rcases le_or_gt j n with hj | hj
        · exact hle (he.le.trans (Nat.pow_le_pow_right hp.pos hj))
        · exact (not_le_of_gt hk)
            ((Nat.pow_le_pow_right hp.pos (Nat.succ_le_of_lt hj)).trans he.ge)
      exact (hγ.sub (isPTypical_pTypicalPartialSum hF hp γ (n + 1))).coeff_eq_zero_of_forall_lt
        hunit hpower fun i hi ↦ ihk i hi (hi.trans hk)

/-- **`p`-typical curves are sums of `p`-power monomials.** On a `p`-typical law over a ring in
which every prime `q ≠ p` is invertible, a `p`-typical curve `γ` agrees below degree `p ^ n` with
`∑^F_{j < n} t_j X ^ (p ^ j)`, where `t` are its `p`-typical expansion coefficients. -/
theorem IsPTypical.coeff_eq_coeff_sum_pTypicalCoeff (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) {γ : F.Curve} (hγ : γ.IsPTypical p)
    {n k : ℕ} (hk : k < p ^ n) :
    coeff k γ.toPowerSeries = coeff k
      (∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
        (γ.pTypicalCoeff hp.ne_zero j)).toPowerSeries := by
  rw [← pTypicalPartialSum_eq_sum]
  let s := γ.pTypicalPartialSum hp.ne_zero n
  have h := coeff_add_eq_left_of_forall_lt_coeff_eq_zero s (γ - s) hk
    (coeff_sub_pTypicalPartialSum_eq_zero hF hp hunit hγ n)
  rwa [add_sub_cancel] at h

/-- **Sums of `p`-power monomials are `p`-typical.** On a `p`-typical law, a curve that agrees
below degree `p ^ n` with `∑^F_{j < n} t_j X ^ (p ^ j)` for every `n` is `p`-typical. -/
theorem isPTypical_of_coeff_eq_coeff_sum (hF : F.IsPTypical p) (hp : p.Prime) {γ : F.Curve}
    (t : ℕ → R)
    (h : ∀ n k, k < p ^ n → coeff k γ.toPowerSeries = coeff k
      (∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero) (t j)).toPowerSeries) :
    γ.IsPTypical p := by
  refine (isPTypical_def p γ).mpr fun q hq hqp ↦ ?_
  ext k
  rw [F.coeff_frobeniusCurve_congr hq.ne_zero
      fun i hi ↦ h (k * q) i (hi.trans_lt (Nat.lt_pow_self hp.one_lt)),
    (hF.sum_monomialCurve_pow hp (range (k * q)) t).frobeniusCurve_eq_zero hq hqp]

/-- **Ravenel's Lemma A2.1.26, curve form.** On a `p`-typical law over a ring in which every
prime `q ≠ p` is invertible, a curve `γ` is `p`-typical if and only if it is a formal-group sum
`∑^F_{j ≥ 0} t_j X ^ (p ^ j)`, that is, it agrees with `∑^F_{j < n} t_j X ^ (p ^ j)` below degree
`p ^ n` for every `n`. The family `t` is then unique (`eq_pTypicalCoeff_of_coeff_eq_coeff_sum`). -/
theorem isPTypical_iff_exists_coeff_eq_coeff_sum (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (γ : F.Curve) :
    γ.IsPTypical p ↔ ∃ t : ℕ → R, ∀ n k, k < p ^ n → coeff k γ.toPowerSeries = coeff k
      (∑ j ∈ range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero) (t j)).toPowerSeries :=
  ⟨fun hγ ↦ ⟨γ.pTypicalCoeff hp.ne_zero, fun _ _ hk ↦
      hγ.coeff_eq_coeff_sum_pTypicalCoeff hF hp hunit hk⟩,
    fun ⟨t, h⟩ ↦ isPTypical_of_coeff_eq_coeff_sum hF hp t h⟩

end Curve

end FormalGroup

namespace TauCeti.FormalGroupIso

open FormalGroup

variable {R : Type*} [CommRing R] {F G : FormalGroup R} [F.IsComm] [G.IsComm] {p : ℕ}

/-- **Ravenel's Lemma A2.1.26.** Let `e : F ≅ G` be an isomorphism out of a `p`-typical law `F`
over a ring in which every prime `q ≠ p` is invertible. Then `G` is `p`-typical if and only if
the inverse series is a formal-group sum `e⁻¹(X) = ∑^F_{j ≥ 0} t_j X ^ (p ^ j)` with `t_0` a
unit, that is, `e⁻¹(X)` agrees with `∑^F_{j < n} t_j X ^ (p ^ j)` below degree `p ^ n` for
every `n`. -/
theorem isPTypical_iff_exists_coeff_invHom_eq_coeff_sum (e : FormalGroupIso F G)
    (hF : F.IsPTypical p) (hp : p.Prime) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    G.IsPTypical p ↔ ∃ t : ℕ → R, IsUnit (t 0) ∧ ∀ n k, k < p ^ n →
      PowerSeries.coeff k e.invHom.toPowerSeries = PowerSeries.coeff k
        (∑ j ∈ Finset.range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
          (t j)).toPowerSeries := by
  rw [isPTypical_def, ← Curve.isPTypical_invHom_mapCurve_iff e,
    Curve.isPTypical_iff_exists_coeff_eq_coeff_sum hF hp hunit,
    FormalGroupHom.mapCurve_tautologicalCurve]
  refine ⟨fun ⟨t, h⟩ ↦ ⟨t, ?_, h⟩, fun ⟨t, _, h⟩ ↦ ⟨t, h⟩⟩
  rw [Curve.eq_pTypicalCoeff_of_coeff_eq_coeff_sum _ hp.one_lt h, Curve.pTypicalCoeff_zero]
  simpa using e.symm.isUnit_coeff_one

/-- **Ravenel's Lemma A2.1.26, strict form.** Let `e : F ≅ G` be a strict isomorphism out of a
`p`-typical law `F` over a ring in which every prime `q ≠ p` is invertible. Then `G` is
`p`-typical if and only if `e⁻¹(X) = ∑^F_{j ≥ 0} t_j X ^ (p ^ j)` with `t_0 = 1`. -/
theorem isPTypical_iff_exists_coeff_invHom_eq_coeff_sum_of_isStrict (e : FormalGroupIso F G)
    [e.IsStrict] (hF : F.IsPTypical p) (hp : p.Prime)
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    G.IsPTypical p ↔ ∃ t : ℕ → R, t 0 = 1 ∧ ∀ n k, k < p ^ n →
      PowerSeries.coeff k e.invHom.toPowerSeries = PowerSeries.coeff k
        (∑ j ∈ Finset.range n, F.monomialCurve (p ^ j) (pow_ne_zero j hp.ne_zero)
          (t j)).toPowerSeries := by
  rw [e.isPTypical_iff_exists_coeff_invHom_eq_coeff_sum hF hp hunit]
  refine ⟨fun ⟨t, _, h⟩ ↦ ⟨t, ?_, h⟩, fun ⟨t, ht, h⟩ ↦ ⟨t, ht ▸ isUnit_one, h⟩⟩
  let γ : F.Curve := ⟨e.invHom.toPowerSeries, e.invHom.zero_constantCoeff⟩
  rw [γ.eq_pTypicalCoeff_of_coeff_eq_coeff_sum hp.one_lt h, Curve.pTypicalCoeff_zero]
  simpa [γ] using IsStrict.coeff_one (f := e.symm)

end TauCeti.FormalGroupIso
