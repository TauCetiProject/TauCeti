/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Order
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.Ideal.Radical
import TauCeti.RingTheory.PowerSeries.Order

/-!
# Height-ideal bounds and Landweber unit conditions for Weierstrass families

Let `W` be a Weierstrass curve over an arbitrary commutative ring `R`. This file determines when
the height ideals `I_n(Ê)` of the formal group `Ê` of `W` equal the unit ideal, with no
characteristic, Noetherian, or reducedness assumptions on `R` (including rings with nilpotents and
the zero ring):

* For every `p > 1` and `n ≥ 3`, `I_n(Ê) = R` if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`).
* For every `p ≠ 0`, the coefficient of `T ^ (p ^ 2)` in `[p]_Ê(T)` (Landweber's `v₂` when `p`
  is prime) is a unit modulo `I₂(Ê)` if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`); for `p > 1`, this is
  equivalent to `I_n(Ê) = R` for `n ≥ 3`.
* In particular, for any smooth-or-nodal Weierstrass family (`(c₄, Δ) = R`) — and hence for every
  elliptic Weierstrass curve (`IsUnit Δ`) — every height ideal `I_n(Ê)` with `n ≥ 3` is the unit
  ideal for all `p > 1`, and the `T ^ (p ^ 2)` coefficient of `[p]_Ê` is a unit modulo `I₂(Ê)`
  for all `p ≠ 0` (so Landweber's `v₂` is a unit modulo `(p, v₁)` at every prime `p`).
* For any Weierstrass family whose discriminant is nilpotent modulo `p`
  (`W.Δ ∈ (Ideal.span {(p : R)}).radical`, including singular families `Δ = 0`, nilpotent
  thickenings `IsNilpotent Δ`, and families singular over all primes dividing `p`), every `p > 1`,
  and every `n ≥ 2`, `I_n(Ê) = R` if and only if `(p, c₄) = R`
  (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff_of_Δ_mem_radical`). When `p` is prime,
  equivalently the Hasse invariant `coeff (p - 1) ω` is a unit modulo `p` if and only if `c₄` is a
  unit modulo `p`
  (`WeierstrassCurve.isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_mem_radical`). In
  particular, on any family singular modulo `p` with `c₄` a unit modulo `p`, the Hasse invariant
  is a unit modulo `p`.

The proofs test properness on maximal-ideal quotients `R ⧸ m`, combining the order bound
`WeierstrassCurve.order_nsmulSeries_formalGroup_le_sq` (and the sharper nodal bound
`WeierstrassCurve.order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero`) with cuspidal
vanishing `WeierstrassCurve.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero`. This
supplies the height-two unit condition and the nodal Hasse-invariant unit condition for Landweber
exactness at every prime; it does not assert the separate regularity of `p` and `v₁` for an
arbitrary family.

## Main results

* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`: for `1 < p` and `n ≥ 3`, `I_n(Ê) = ⊤`
  iff `(p, c₄, Δ) = ⊤`.
* `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`: for `p ≠ 0`, the `T ^ (p ^ 2)`
  coefficient of `[p]_Ê` is a unit modulo `I₂(Ê)` iff `(p, c₄, Δ) = ⊤`.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top` and
  `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top`: the height-two
  bound (`1 < p`, `n ≥ 3`) and unit condition (`p ≠ 0`) for smooth-or-nodal Weierstrass families
  (`(c₄, Δ) = ⊤`).
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top` and
  `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup`: the height-two bound (`1 < p`,
  `n ≥ 3`) and unit condition (`p ≠ 0`) for elliptic Weierstrass curves.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff_of_Δ_mem_radical`: for
  `W.Δ ∈ (Ideal.span {(p : R)}).radical`, `1 < p`, and `n ≥ 2`, `I_n(Ê) = ⊤` iff `(p, c₄) = ⊤`.
* `WeierstrassCurve.isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_mem_radical`: for
  `W.Δ ∈ (Ideal.span {(p : R)}).radical` and prime `p`, the Hasse invariant is a unit modulo `p`
  iff `c₄` is a unit modulo `p`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.7 and V.3.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p n : ℕ}

private theorem nat_le_order_nsmulSeries_formalGroup_iff {K : Type*} [Field K]
    (W : WeierstrassCurve K) {p N : ℕ} (hp : p ≠ 0) (h1 : 1 < N)
    (hN : (p : K) = 0 → p ^ 2 < N ∨ W.Δ = 0 ∧ p < N) :
    ((N : ℕ) : ℕ∞) ≤ ((formalGroup W).nsmulSeries p).order ↔
      (p : K) = 0 ∧ W.c₄ = 0 ∧ W.Δ = 0 := by
  constructor
  · intro hord
    have hpK : (p : K) = 0 := by
      simpa [FormalGroup.coeff_one_nsmulSeries] using
        PowerSeries.coeff_of_lt_order 1 (lt_of_lt_of_le (by exact_mod_cast h1) hord)
    have hzero : W.c₄ = 0 ∧ W.Δ = 0 := by
      by_contra hne
      rw [not_and_or] at hne
      rcases hN hpK with hN | ⟨hΔ, hN⟩
      · exact not_lt_of_ge (hord.trans (W.order_nsmulSeries_formalGroup_le_sq hp hne))
          (by exact_mod_cast hN)
      · exact not_lt_of_ge
          (hord.trans (W.order_nsmulSeries_formalGroup_le_of_Δ_eq_zero_of_c₄_ne_zero hp hΔ
            (hne.resolve_right (not_not.mpr hΔ))))
          (by exact_mod_cast hN)
    exact ⟨hpK, hzero⟩
  · rintro ⟨hpK, hc₄, hΔ⟩
    rw [W.nsmulSeries_formalGroup_eq_zero_of_Δ_eq_zero_of_c₄_eq_zero hΔ hc₄ hpK,
      PowerSeries.order_zero]
    exact le_top

/-- The coefficients of `[p]_Ê` in degrees below `N` (with `p ≠ 0`, and either `p² < N` or
`W.Δ ∈ (Ideal.span {(p : R)}).radical ∧ p < N`) generate the unit ideal exactly when `p`, `c₄`,
and `Δ` do. -/
private theorem span_coeff_nsmulSeries_eq_top_iff {N : ℕ} (hp : p ≠ 0)
    (hN : p ^ 2 < N ∨ W.Δ ∈ (Ideal.span {(p : R)}).radical ∧ p < N) :
    Ideal.span ((fun k ↦ PowerSeries.coeff k ((formalGroup W).nsmulSeries p)) '' Set.Iio N) = ⊤ ↔
      Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  have h1 : 1 < N := hN.elim
    (lt_of_le_of_lt (Nat.one_le_pow 2 p (Nat.pos_of_ne_zero hp)))
    (fun h ↦ lt_of_le_of_lt (Nat.pos_of_ne_zero hp) h.2)
  have hmax (m : Ideal R) [hm : m.IsMaximal] :
      Ideal.span ((fun k ↦ PowerSeries.coeff k ((formalGroup W).nsmulSeries p)) '' Set.Iio N) ≤ m ↔
        Ideal.span {(p : R), W.c₄, W.Δ} ≤ m := by
    let _ := Ideal.Quotient.field m
    let π := Ideal.Quotient.mk m
    have hcoeff :
        Ideal.span ((fun k ↦ PowerSeries.coeff k ((formalGroup W).nsmulSeries p)) '' Set.Iio N) ≤
            m ↔
          ((N : ℕ) : ℕ∞) ≤ ((formalGroup (W.map π)).nsmulSeries p).order := by
      nth_rw 1 [← Ideal.mk_ker (I := m)]
      rw [PowerSeries.span_coeff_le_ker_iff, map_nsmulSeries_formalGroup]
    have hgen :
        Ideal.span {(p : R), W.c₄, W.Δ} ≤ m ↔
          (p : R ⧸ m) = 0 ∧ (W.map π).c₄ = 0 ∧ (W.map π).Δ = 0 := by
      simp [π, Ideal.span_le, Set.subset_def, ← Ideal.Quotient.eq_zero_iff_mem, map_c₄, map_Δ]
    have hNm : ((p : R ⧸ m) = 0) → p ^ 2 < N ∨ (W.map π).Δ = 0 ∧ p < N :=
      fun hp0 ↦ hN.imp_right fun ⟨hΔ, hlt⟩ ↦ ⟨by
        rw [map_Δ, Ideal.Quotient.eq_zero_iff_mem]
        exact hm.isPrime.radical_le_iff.mpr ((Ideal.span_singleton_le_iff_mem m).mpr
          (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [π] using hp0))) hΔ, hlt⟩
    exact hcoeff.trans <|
      (nat_le_order_nsmulSeries_formalGroup_iff (W.map π) hp h1 hNm).trans hgen.symm
  rw [← not_iff_not]
  simp_rw [← ne_eq, Ideal.ne_top_iff_exists_maximal]
  exact exists_congr fun m ↦ and_congr_right fun hm ↦ hmax m

/-- **Exact characterization of `I_n(Ê) = ⊤` for `n ≥ 3`.** Over an arbitrary commutative ring `R`
and for any `p > 1`, every height ideal `I_n` (`n ≥ 3`) of the formal group of a Weierstrass curve
`W` is the unit ideal if and only if `(p, c₄, Δ) = R` (equivalently, `W` has no cuspidal fiber in
residue characteristics dividing `p`). -/
theorem heightIdeal_formalGroup_eq_top_iff (hp : 1 < p) (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  rw [FormalGroup.heightIdeal_def]
  exact W.span_coeff_nsmulSeries_eq_top_iff (by omega)
    (Or.inl (Nat.pow_lt_pow_right hp (by omega : 2 < n)))

/-- **Exact characterization of the height-two unit condition.** For any `p ≠ 0`, the
`T ^ (p ^ 2)` coefficient of `[p]_Ê` (Landweber's `v₂` when `p` is prime) is a unit modulo
`I₂(Ê)` if and only if `(p, c₄, Δ) = R`. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_iff (hp : p ≠ 0) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) ↔
      Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  have h := W.span_coeff_nsmulSeries_eq_top_iff hp (Or.inl (Nat.lt_add_one (p ^ 2)))
  rw [Ideal.span_image_Iio_succ] at h
  simpa [Ideal.Quotient.isUnit_mk_iff, FormalGroup.heightIdeal_def] using h

/-- **Height-two bound for smooth-or-nodal Weierstrass families.** If `(c₄, Δ) = R`, then for
every `p > 1` every height ideal from `I₃` onward of the formal group of `W` is the unit ideal. -/
theorem heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top (h : Ideal.span {W.c₄, W.Δ} = ⊤)
    (hp : 1 < p) (hn : 3 ≤ n) : (formalGroup W).heightIdeal p n = ⊤ := by
  refine (W.heightIdeal_formalGroup_eq_top_iff hp hn).mpr (top_unique ?_)
  rw [← h]
  exact Ideal.span_mono (Set.subset_insert _ _)

/-- **Landweber's `v₂`-unit condition for smooth-or-nodal Weierstrass families.** If
`(c₄, Δ) = R`, then for every `p ≠ 0` the `T ^ (p ^ 2)` coefficient of `[p]_Ê` (Landweber's `v₂`
when `p` is prime) is a unit modulo `I₂(Ê)`, with no regularity assumption on the coefficient ring.
-/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top
    (h : Ideal.span {W.c₄, W.Δ} = ⊤) (hp : p ≠ 0) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) := by
  refine (W.isUnit_mk_coeff_nsmulSeries_formalGroup_iff hp).mpr (top_unique ?_)
  rw [← h]
  exact Ideal.span_mono (Set.subset_insert _ _)

/-- **Height-two bound for elliptic Weierstrass curves.** For every `p > 1`, every height ideal
from `I₃` onward of the formal group of an elliptic Weierstrass curve is the unit ideal. This holds
over arbitrary commutative coefficient rings. -/
theorem heightIdeal_formalGroup_eq_top [W.IsElliptic] (hp : 1 < p) (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ :=
  W.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) W.isUnit_Δ) hp hn

/-- **Landweber's height-two unit condition for elliptic Weierstrass curves.** For every `p ≠ 0`
(in particular, every prime `p`), the `T ^ (p ^ 2)` coefficient of `[p]_Ê` on an elliptic
Weierstrass curve is a unit modulo `I₂(Ê)`, with no regularity assumption on the coefficient ring.
-/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup [W.IsElliptic] (hp : p ≠ 0) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) :=
  W.isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) W.isUnit_Δ) hp

/-- **Exact characterization of `I_n(Ê) = ⊤` (`n ≥ 2`) for families singular over primes dividing
`p`.** When `W.Δ ∈ (Ideal.span {(p : R)}).radical` (in particular, when `IsNilpotent W.Δ` or
`W.Δ = 0`), for every `p > 1` and every `n ≥ 2`, `I_n(Ê) = ⊤` if and only if `(p, c₄) = R`. -/
theorem heightIdeal_formalGroup_eq_top_iff_of_Δ_mem_radical
    (hΔ : W.Δ ∈ (Ideal.span {(p : R)}).radical) (hp : 1 < p) (hn : 2 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄} = ⊤ := by
  have hpn : p < p ^ n := lt_of_lt_of_le (lt_self_pow₀ hp (by omega : 1 < 2))
    (Nat.pow_le_pow_right (zero_lt_one.trans hp) hn)
  have hΔ' : W.Δ ∈ (Ideal.span {(p : R), W.c₄}).radical :=
    Ideal.radical_mono (Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) hΔ
  rw [FormalGroup.heightIdeal_def,
    W.span_coeff_nsmulSeries_eq_top_iff (by omega) (Or.inr ⟨hΔ, hpn⟩),
    Ideal.span_insert, Ideal.span_insert, ← sup_assoc, ← Ideal.span_insert,
    Ideal.sup_span_singleton_eq_top_iff_of_mem_radical hΔ']

/-- **The Hasse invariant on families singular over primes dividing `p`.** When
`W.Δ ∈ (Ideal.span {(p : R)}).radical` (in particular, when `IsNilpotent W.Δ` or `W.Δ = 0`), for
every prime `p` the Hasse invariant `coeff (p - 1) ω` of the formal group of `W` is a unit modulo
`p` if and only if `c₄` is a unit modulo `p`. -/
theorem isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_mem_radical
    (hΔ : W.Δ ∈ (Ideal.span {(p : R)}).radical) (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(p : R)})
      (PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential)) ↔
      IsUnit (Ideal.Quotient.mk (Ideal.span {(p : R)}) W.c₄) := by
  rw [← W.heightIdeal_formalGroup_two_eq_top_iff hp,
    W.heightIdeal_formalGroup_eq_top_iff_of_Δ_mem_radical hΔ hp.one_lt le_rfl,
    Ideal.Quotient.isUnit_mk_iff, Ideal.span_insert, sup_comm]

end WeierstrassCurve
