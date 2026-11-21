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
# Height-ideal bounds and Landweber unit conditions for Weierstrass families

Let `W` be a Weierstrass curve over an arbitrary commutative ring `R`, and let `p` be any prime
(including `2` and `3`). This file determines when the height ideals `I_n(Ê)` of the formal group
`Ê` of `W` equal the unit ideal, with no characteristic, Noetherian, or reducedness assumptions on
`R` (including rings with nilpotents and the zero ring):

* For every `n ≥ 3`, `I_n(Ê) = R` if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff`). Equivalently, Landweber's `v₂` is a unit
  modulo `I₂(Ê) = (p, v₁)` if and only if `(p, c₄, Δ) = R`
  (`WeierstrassCurve.isUnit_mk_coeff_nsmulSeries_formalGroup_iff`).
* In particular, for any smooth-or-nodal Weierstrass family (`(c₄, Δ) = R`) — and hence for every
  elliptic Weierstrass curve (`IsUnit Δ`) — every height ideal `I_n(Ê)` with `n ≥ 3` is the unit
  ideal and `v₂` is a unit modulo `(p, v₁)`. All subsequent height quotients therefore vanish.
* For a singular Weierstrass family (`Δ = 0`) and every `n ≥ 2`, `I_n(Ê) = R` if and only if
  `(p, c₄) = R` (`WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero`). Equivalently,
  the Hasse invariant `coeff (p - 1) ω` is a unit modulo `p` if and only if `c₄` is a unit modulo
  `p` (`WeierstrassCurve.isUnit_mk_coeff_invariantDifferential_formalGroup_iff_of_Δ_eq_zero`). In
  particular, on any nodal family (`Δ = 0` and `IsUnit c₄`), split or non-split, the Hasse
  invariant is a unit modulo `p`.

The proofs combine the field-level height classification of Weierstrass curves
(`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Classification`) with detection of a
proper height ideal on maximal-ideal quotients
(`FormalGroup.heightIdeal_eq_top_iff_forall_height_lt`). This supplies the height-two unit
condition and the nodal Hasse-invariant unit condition for Landweber exactness at every prime; it
does not assert the separate regularity of `p` and `v₁` for an arbitrary family.

## Main results

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
* `WeierstrassCurve.heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero`: for `Δ = 0` and `n ≥ 2`,
  `I_n(Ê) = ⊤` iff `(p, c₄) = ⊤`.
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

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {p n : ℕ}

/-- **Exact characterization of `I_n(Ê) = ⊤` for `n ≥ 3`.** Over an arbitrary commutative ring `R`
and at any prime `p`, every height ideal `I_n` (`n ≥ 3`) of the formal group of a Weierstrass curve
`W` is the unit ideal if and only if `(p, c₄, Δ) = R` (equivalently, `W` has no cuspidal fiber in
characteristic `p`). -/
theorem heightIdeal_formalGroup_eq_top_iff (hp : p.Prime) (hn : 3 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄, W.Δ} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [(formalGroup W).heightIdeal_eq_top_iff_forall_height_lt hp (by omega)]
  constructor
  · intro h
    by_contra hI
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : R), W.c₄, W.Δ}) hI
    let _ : m.IsMaximal := hm
    let _ := Ideal.Quotient.field m
    have hp_mem : (p : R) ∈ m := hle (Ideal.subset_span (by simp))
    have hc₄_mem : W.c₄ ∈ m := hle (Ideal.subset_span (by simp))
    have hΔ_mem : W.Δ ∈ m := hle (Ideal.subset_span (by simp))
    let _ : CharP (R ⧸ m) p := (CharP.charP_iff_prime_eq_zero hp).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
      exact hp_mem)
    have hlt := h (R ⧸ m) (Ideal.Quotient.mk m)
    rw [← map_formalGroup] at hlt
    have htop := (W.map (Ideal.Quotient.mk m)).height_formalGroup_eq_top_of_Δ_eq_zero_of_c₄_eq_zero
      (by rw [map_Δ, Ideal.Quotient.eq_zero_iff_mem]; exact hΔ_mem)
      (by rw [map_c₄, Ideal.Quotient.eq_zero_iff_mem]; exact hc₄_mem)
    rw [htop] at hlt
    exact not_top_lt hlt
  · intro h K _ _ f
    rw [← map_formalGroup]
    have hmap : Ideal.span {(0 : K), (W.map f).c₄, (W.map f).Δ} = ⊤ := by
      have hm := congrArg (Ideal.map f) h
      rw [Ideal.map_top, Ideal.map_span] at hm
      simpa [Set.image_insert_eq, Set.image_singleton, map_natCast, CharP.cast_eq_zero K p,
        map_c₄, map_Δ] using hm
    have hne : (W.map f).c₄ ≠ 0 ∨ (W.map f).Δ ≠ 0 := by
      by_contra hzero
      push Not at hzero
      rw [hzero.1, hzero.2] at hmap
      simp at hmap
    have hle : (formalGroup (W.map f)).height p ≤ 2 :=
      (W.map f).height_formalGroup_le_two_iff.mpr hne
    exact lt_of_le_of_lt hle (by exact_mod_cast (by omega : 2 < n))

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

/-- **Exact characterization of `I_n(Ê) = ⊤` (`n ≥ 2`) for singular Weierstrass families.** When
`Δ = 0`, every height ideal from `I₂` onward is the unit ideal if and only if `(p, c₄) = R`. -/
theorem heightIdeal_formalGroup_eq_top_iff_of_Δ_eq_zero (hΔ : W.Δ = 0) (hp : p.Prime)
    (hn : 2 ≤ n) :
    (formalGroup W).heightIdeal p n = ⊤ ↔ Ideal.span {(p : R), W.c₄} = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro h
    have hmax : (formalGroup W).heightIdeal p (max n 3) = ⊤ :=
      top_unique (h ▸ (formalGroup W).heightIdeal_mono (le_max_left n 3))
    have hspan := (W.heightIdeal_formalGroup_eq_top_iff hp (le_max_right n 3)).mp hmax
    rw [hΔ, Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_zero, sup_bot_eq,
      ← Ideal.span_insert] at hspan
    exact hspan
  · intro h
    refine ((formalGroup W).heightIdeal_eq_top_iff_forall_height_lt hp (by omega)).mpr ?_
    intro K _ _ f
    rw [← map_formalGroup]
    have hmap : Ideal.span {(0 : K), (W.map f).c₄} = ⊤ := by
      have hm := congrArg (Ideal.map f) h
      rw [Ideal.map_top, Ideal.map_span] at hm
      simpa [Set.image_insert_eq, Set.image_singleton, map_natCast, CharP.cast_eq_zero K p,
        map_c₄] using hm
    have hc₄ : (W.map f).c₄ ≠ 0 := by
      intro hzero
      rw [hzero] at hmap
      simp at hmap
    have hΔf : (W.map f).Δ = 0 := by rw [map_Δ, hΔ, map_zero]
    rw [(W.map f).height_formalGroup_eq_one_of_Δ_eq_zero_of_c₄_ne_zero hΔf hc₄]
    exact_mod_cast (by omega : 1 < n)

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
