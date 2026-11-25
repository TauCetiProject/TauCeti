/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Classification
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Ideal
import TauCeti.RingTheory.Ideal.Quotient.Coprime

/-!
# Height-ideal strata, bounds, and Landweber unit conditions for Weierstrass families

Let `W` be a Weierstrass curve over an arbitrary commutative ring `R`, and let `p` be any prime
(including `2` and `3`). Combining `FormalGroup.heightIdeal_le_prime_iff` with the field-level
height classification of Weierstrass curves
(`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Classification`) determines the prime
ideals containing the higher height ideals `I_n(Ê)` of `Ê = formalGroup W`, their radicals, and
when they equal the unit ideal, with no characteristic, Noetherian, or reducedness assumptions on
`R` (including rings with nilpotents and the zero ring):

* For every `n ≥ 3` (and for `⨆ n, I_n(Ê)`), a prime ideal `P` contains `I_n(Ê)` if and only if it
  contains `(p, c₄, Δ)` (`WeierstrassCurve.heightIdeal_formalGroup_le_prime_iff`,
  `WeierstrassCurve.iSup_heightIdeal_formalGroup_le_prime_iff`), so `√I_n(Ê) = √(p, c₄, Δ)`
  (`WeierstrassCurve.radical_heightIdeal_formalGroup`,
  `WeierstrassCurve.radical_iSup_heightIdeal_formalGroup`) and `I_n(Ê) = R` (as well as
  `⨆ n, I_n(Ê) = R`) if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`,
  `WeierstrassCurve.iSup_heightIdeal_formalGroup_eq_top_iff`). Equivalently,
  Landweber's `v₂` is a unit modulo `I₂(Ê) = (p, v₁)` if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`).
* In particular, for any smooth-or-nodal Weierstrass family (`(c₄, Δ) = R`) — and hence for every
  elliptic Weierstrass curve (`IsUnit Δ`) — every height ideal `I_n(Ê)` with `n ≥ 3` is the unit
  ideal and `v₂` is a unit modulo `(p, v₁)`. All subsequent height quotients therefore vanish.
* For a singular Weierstrass family (`Δ = 0`) and every `n ≥ 2`, a prime ideal `P` contains `I_n(Ê)`
  if and only if it contains `(p, c₄)`
  (`WeierstrassCurve.heightIdeal_formalGroup_le_prime_iff_of_Δ_eq_zero`), so `√I_n(Ê) = √(p, c₄)`
  (`WeierstrassCurve.radical_heightIdeal_formalGroup_of_Δ_eq_zero`) and `I_n(Ê) = R` if and only if
  `(p, c₄) = R` (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero`). Equivalently,
  the Hasse invariant `coeff (p - 1) ω` is a unit modulo `p` if and only if `c₄` is a unit modulo
  `p` (`WeierstrassCurve.isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_eq_zero`). In
  particular, on any nodal family (`Δ = 0` and `IsUnit c₄`), split or non-split, the Hasse
  invariant is a unit modulo `p`.

This supplies the scheme-theoretic support of the higher height ideals, the height-two unit
condition, and the nodal Hasse-invariant unit condition for Landweber exactness at every prime; it
does not assert the separate regularity of `p` and `v₁` for an arbitrary family.

## Main results

* `WeierstrassCurve.heightIdeal_formalGroup_le_prime_iff` and
  `WeierstrassCurve.radical_heightIdeal_formalGroup`: for `n ≥ 3`, `I_n(Ê) ≤ P ↔ (p, c₄, Δ) ≤ P`
  for every prime ideal `P`, and `√I_n(Ê) = √(p, c₄, Δ)` (with supremum counterparts
  `WeierstrassCurve.iSup_heightIdeal_formalGroup_le_prime_iff`,
  `WeierstrassCurve.radical_iSup_heightIdeal_formalGroup`, and
  `WeierstrassCurve.iSup_heightIdeal_formalGroup_eq_top_iff`).
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`: for `n ≥ 3`, `I_n(Ê) = ⊤` iff
  `(p, c₄, Δ) = ⊤`.
* `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`: `v₂` is a unit modulo
  `I₂(Ê)` iff `(p, c₄, Δ) = ⊤`.
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top` and
  `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top`: the height-two
  bound and `v₂`-unit condition for smooth-or-nodal Weierstrass families (`(c₄, Δ) = ⊤`).
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top` and
  `WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup`: the height-two bound and `v₂`-unit
  condition for elliptic Weierstrass curves.
* `WeierstrassCurve.heightIdeal_formalGroup_le_prime_iff_of_Δ_eq_zero`,
  `WeierstrassCurve.radical_heightIdeal_formalGroup_of_Δ_eq_zero`, and
  `WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero`: for `Δ = 0` and `n ≥ 2`,
  `I_n(Ê) ≤ P ↔ (p, c₄) ≤ P`, `√I_n(Ê) = √(p, c₄)`, and `I_n(Ê) = ⊤ ↔ (p, c₄) = ⊤`.
* `WeierstrassCurve.isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_eq_zero`: for
  `Δ = 0`, the Hasse invariant is a unit modulo `p` iff `c₄` is a unit modulo `p`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.7 and V.3.
* P. S. Landweber, *Homological properties of comodules over `MU_*(MU)` and `BP_*(BP)`*,
  Amer. J. Math. 98 (1976), 591–610.
* P. G. Goerss, *Topological modular forms [after Hopkins, Miller and Lurie]*, Séminaire
  Bourbaki 1005 (2009), §3.2.
-/

public section

namespace WeierstrassCurve

private theorem algebraMap_fractionRing_quotient_eq_zero {R : Type*} [CommRing R] {P : Ideal R}
    {x : R} :
    algebraMap R (FractionRing (R ⧸ P)) x = 0 ↔ x ∈ P := by
  rw [IsScalarTower.algebraMap_apply R (R ⧸ P) (FractionRing (R ⧸ P)),
    map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))),
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p n : ℕ}

/-- **Prime ideals containing `I_n(Ê)` for `n ≥ 3`.** Over an arbitrary commutative ring `R`, at
any prime `p` and for every `n ≥ 3`, a prime ideal `P` of `R` contains
`(formalGroup W).heightIdeal p n` if and only if `P` contains `(p, c₄, Δ)`. -/
theorem heightIdeal_formalGroup_le_prime_iff (hp : p.Prime) (hn : 3 ≤ n) {P : Ideal R}
    [P.IsPrime] :
    (formalGroup W).heightIdeal p n ≤ P ↔ Ideal.span {(p : R), W.c₄, W.Δ} ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  let K := FractionRing (R ⧸ P)
  let φ : R →+* K := algebraMap R K
  rw [(formalGroup W).heightIdeal_le_prime_iff hp, ← map_formalGroup]
  simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  by_cases hpP : (p : R) ∈ P
  · have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr
      (by rw [← map_natCast φ]; exact algebraMap_fractionRing_quotient_eq_zero.mpr hpP)
    refine ⟨fun hnh ↦ ⟨hpP, ?_⟩, fun ⟨_, hc₄P, hΔP⟩ ↦ ?_⟩
    · have hnotle : ¬ (formalGroup (W.map φ)).height p ≤ 2 := fun h2 ↦
        absurd (le_trans (by exact_mod_cast hn) (hnh.trans h2) : (3 : ℕ∞) ≤ 2) (by decide)
      have hcΔ : (W.map φ).c₄ = 0 ∧ (W.map φ).Δ = 0 := by
        simpa only [not_or, not_ne_iff] using
          mt (W.map φ).height_formalGroup_le_two_iff.mpr hnotle
      exact ⟨algebraMap_fractionRing_quotient_eq_zero.mp (by simpa [φ] using hcΔ.1),
        algebraMap_fractionRing_quotient_eq_zero.mp (by simpa [φ] using hcΔ.2)⟩
    · rw [(W.map φ).height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero
        (by simpa [φ] using algebraMap_fractionRing_quotient_eq_zero.mpr hΔP)
        (by simpa [φ] using algebraMap_fractionRing_quotient_eq_zero.mpr hc₄P)]
      exact le_top
  · have hpK : (p : K) ≠ 0 := by
      rw [← map_natCast φ]; exact mt algebraMap_fractionRing_quotient_eq_zero.mp hpP
    rw [(formalGroup (W.map φ)).height_eq_zero_of_natCast_ne_zero hpK]
    exact iff_of_false (by simpa using (by omega : n ≠ 0)) (fun h ↦ hpP h.1)

/-- **The radical of `I_n(Ê)` for `n ≥ 3` is `√(p, c₄, Δ)`.** -/
theorem radical_heightIdeal_formalGroup (hp : p.Prime) (hn : 3 ≤ n) :
    ((formalGroup W).heightIdeal p n).radical = (Ideal.span {(p : R), W.c₄, W.Δ}).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext P
  exact and_congr_left fun hP ↦ W.heightIdeal_formalGroup_le_prime_iff hp hn (P := P)

/-- **Prime ideals containing `⨆ n, I_n(Ê)`.** At any prime `p`, a prime ideal `P` of `R` contains
`⨆ n, (formalGroup W).heightIdeal p n` if and only if `P` contains `(p, c₄, Δ)`. -/
theorem iSup_heightIdeal_formalGroup_le_prime_iff (hp : p.Prime) {P : Ideal R} [P.IsPrime] :
    ⨆ n, (formalGroup W).heightIdeal p n ≤ P ↔ Ideal.span {(p : R), W.c₄, W.Δ} ≤ P := by
  rw [iSup_le_iff]
  refine ⟨fun h ↦ (W.heightIdeal_formalGroup_le_prime_iff hp le_rfl).mp (h 3), fun h n ↦ ?_⟩
  exact le_trans ((formalGroup W).heightIdeal_mono (le_max_left n 3))
    ((W.heightIdeal_formalGroup_le_prime_iff hp (le_max_right n 3)).mpr h)

/-- **The radical of `⨆ n, I_n(Ê)` is `√(p, c₄, Δ)`.** -/
theorem radical_iSup_heightIdeal_formalGroup (hp : p.Prime) :
    (⨆ n, (formalGroup W).heightIdeal p n).radical =
      (Ideal.span {(p : R), W.c₄, W.Δ}).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext P
  exact and_congr_left fun hP ↦ W.iSup_heightIdeal_formalGroup_le_prime_iff hp (P := P)

/-- **Exact characterization of `⨆ n, I_n(Ê) = ⊤`.** At any prime `p`, the supremum of the height
ideals of the formal group of `W` is the unit ideal if and only if `(p, c₄, Δ) = R`. -/
theorem iSup_heightIdeal_formalGroup_eq_top_iff (hp : p.Prime) :
    ⨆ n, (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  rw [← Ideal.radical_eq_top, W.radical_iSup_heightIdeal_formalGroup hp, Ideal.radical_eq_top]

/-- **Exact characterization of `I_n(Ê) = ⊤` for `n ≥ 3`.** Over an arbitrary commutative ring `R`
and at any prime `p`, every height ideal `I_n` (`n ≥ 3`) of the formal group of a Weierstrass curve
`W` is the unit ideal if and only if `(p, c₄, Δ) = R` (equivalently, `W` has no cuspidal fiber in
characteristic `p`). -/
theorem heightIdeal_formalGroup_eq_top_iff (hp : p.Prime) (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  rw [← Ideal.radical_eq_top, W.radical_heightIdeal_formalGroup hp hn, Ideal.radical_eq_top]

/-- **Exact characterization of the `v₂`-unit condition.** At any prime `p`, Landweber's `v₂` of
the formal group of a Weierstrass curve `W` is a unit modulo `I₂(Ê) = (p, v₁)` if and only if
`(p, c₄, Δ) = R`. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_iff (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) ↔
      Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  rw [(formalGroup W).isUnit_mk_coeff_nsmulSeries_iff hp 2,
    W.heightIdeal_formalGroup_eq_top_iff hp le_rfl]

/-- **Height-two bound for smooth-or-nodal Weierstrass families.** If `(c₄, Δ) = R`, then at every
prime `p` every height ideal from `I₃` onward of the formal group of `W` is the unit ideal. -/
theorem heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top (h : Ideal.span {W.c₄, W.Δ} = ⊤)
    (hp : p.Prime) (hn : 3 ≤ n) : (formalGroup W).heightIdeal p n = ⊤ := by
  refine (W.heightIdeal_formalGroup_eq_top_iff hp hn).mpr (top_unique ?_)
  rw [← h]
  exact Ideal.span_mono (Set.subset_insert _ _)

/-- **Landweber's `v₂`-unit condition for smooth-or-nodal Weierstrass families.** If
`(c₄, Δ) = R`, then at every prime `p` Landweber's `v₂` of the formal group of `W` is a unit
modulo `(p, v₁)`, with no regularity assumption on the coefficient ring. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup_of_span_c₄_Δ_eq_top
    (h : Ideal.span {W.c₄, W.Δ} = ⊤) (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) :=
  ((formalGroup W).isUnit_mk_coeff_nsmulSeries_iff hp 2).mpr
    (W.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top h hp le_rfl)

/-- **Height-two bound for elliptic Weierstrass curves.** At every prime `p`, every height ideal
from `I₃` onward of the formal group of an elliptic Weierstrass curve is the unit ideal. This holds
over arbitrary commutative coefficient rings. -/
theorem heightIdeal_formalGroup_eq_top [W.IsElliptic] (hp : p.Prime) (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ :=
  W.heightIdeal_formalGroup_eq_top_of_span_c₄_Δ_eq_top
    (Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) W.isUnit_Δ) hp hn

/-- **Landweber's `v₂`-unit condition for elliptic Weierstrass curves.** At every prime `p`,
Landweber's `v₂` of the formal group of an elliptic Weierstrass curve is a unit modulo `(p, v₁)`.
This is the height-two unit condition, with no regularity assumption on the coefficient ring. -/
theorem isUnit_mk_coeff_nsmulSeries_formalGroup [W.IsElliptic] (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk ((formalGroup W).heightIdeal p 2)
      (PowerSeries.coeff (p ^ 2) ((formalGroup W).nsmulSeries p))) :=
  ((formalGroup W).isUnit_mk_coeff_nsmulSeries_iff hp 2).mpr
    (W.heightIdeal_formalGroup_eq_top hp le_rfl)

/-- **Prime ideals containing `I_n(Ê)` (`n ≥ 2`) on singular Weierstrass families.** When `Δ = 0`,
at any prime `p` and for every `n ≥ 2`, a prime ideal `P` of `R` contains
`(formalGroup W).heightIdeal p n` if and only if `P` contains `(p, c₄)`. -/
theorem heightIdeal_formalGroup_le_prime_iff_of_Δ_eq_zero (hΔ : W.Δ = 0) (hp : p.Prime)
    (hn : 2 ≤ n) {P : Ideal R} [P.IsPrime] :
    (formalGroup W).heightIdeal p n ≤ P ↔ Ideal.span {(p : R), W.c₄} ≤ P := by
  have : Fact p.Prime := ⟨hp⟩
  let K := FractionRing (R ⧸ P)
  let φ : R →+* K := algebraMap R K
  have hΔφ : (W.map φ).Δ = 0 := by rw [map_Δ, hΔ, map_zero]
  rw [(formalGroup W).heightIdeal_le_prime_iff hp, ← map_formalGroup]
  simp only [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
  by_cases hpP : (p : R) ∈ P
  · have : CharP K p := (CharP.charP_iff_prime_eq_zero hp).mpr
      (by rw [← map_natCast φ]; exact algebraMap_fractionRing_quotient_eq_zero.mpr hpP)
    refine ⟨fun hnh ↦ ⟨hpP, ?_⟩, fun ⟨_, hc₄P⟩ ↦ ?_⟩
    · by_contra hc₄P
      have hc₄φ : (W.map φ).c₄ ≠ 0 := by
        rw [map_c₄]; exact mt algebraMap_fractionRing_quotient_eq_zero.mp hc₄P
      rw [(W.map φ).height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔφ hc₄φ] at hnh
      exact absurd (le_trans (by exact_mod_cast hn) hnh : (2 : ℕ∞) ≤ 1) (by decide)
    · rw [(W.map φ).height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero hΔφ
        (by simpa [φ] using algebraMap_fractionRing_quotient_eq_zero.mpr hc₄P)]
      exact le_top
  · have hpK : (p : K) ≠ 0 := by
      rw [← map_natCast φ]; exact mt algebraMap_fractionRing_quotient_eq_zero.mp hpP
    rw [(formalGroup (W.map φ)).height_eq_zero_of_natCast_ne_zero hpK]
    exact iff_of_false (by simpa using (by omega : n ≠ 0)) (fun h ↦ hpP h.1)

/-- **The radical of `I_n(Ê)` (`n ≥ 2`) when `Δ = 0` is `√(p, c₄)`.** -/
theorem radical_heightIdeal_formalGroup_of_Δ_eq_zero (hΔ : W.Δ = 0) (hp : p.Prime)
    (hn : 2 ≤ n) :
    ((formalGroup W).heightIdeal p n).radical = (Ideal.span {(p : R), W.c₄}).radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext P
  exact and_congr_left fun hP ↦
    W.heightIdeal_formalGroup_le_prime_iff_of_Δ_eq_zero hΔ hp hn (P := P)

/-- **Exact characterization of `I_n(Ê) = ⊤` (`n ≥ 2`) for singular Weierstrass families.** When
`Δ = 0`, every height ideal from `I₂` onward is the unit ideal if and only if `(p, c₄) = R`. -/
theorem heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero (hΔ : W.Δ = 0) (hp : p.Prime)
    (hn : 2 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄} = ⊤ := by
  rw [← Ideal.radical_eq_top, W.radical_heightIdeal_formalGroup_of_Δ_eq_zero hΔ hp hn,
    Ideal.radical_eq_top]

/-- **The Hasse invariant on singular Weierstrass families.** When `Δ = 0`, for every prime `p`
the Hasse invariant `coeff (p - 1) ω` of the formal group of `W` is a unit modulo `p` if and only
if `c₄` is a unit modulo `p`. In particular, on every nodal family (`Δ = 0` and `IsUnit c₄`), the
Hasse invariant is a unit modulo `p`. -/
theorem isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_eq_zero (hΔ : W.Δ = 0)
    (hp : p.Prime) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(p : R)})
      (PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential)) ↔
      IsUnit (Ideal.Quotient.mk (Ideal.span {(p : R)}) W.c₄) := by
  rw [← W.heightIdeal_formalGroup_two_eq_top_iff hp,
    W.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero hΔ hp le_rfl,
    Ideal.Quotient.isUnit_mk_iff, Ideal.span_insert, sup_comm]

end WeierstrassCurve
