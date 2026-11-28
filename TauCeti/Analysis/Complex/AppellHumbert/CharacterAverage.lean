/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import TauCeti.Analysis.Complex.AppellHumbert.Translation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Character-weighted averages of normalised theta translations

Let `D = (B, χ)` be an Appell–Humbert datum for a subgroup `L ⊆ V`, let `b : V →L[ℂ] V` satisfy
`E (b u, w) + E (u, b w) = E (u, w)` with `E (b l, m) ∈ ℤ` on `L`, and let `F : V →+ V` be an
additive map. For `H = {x : V | F x ∈ L}` with finite quotient `Q = H ⧸ (L.comap H.subtype)` and
a function `f : V → ℂ` invariant under `N_{F l}` for `l ∈ L`, the character-weighted sum
`∑ k : Q, ξ (-k) • N_{F k.out} f` transforms by `ξ` under `N_{F y}` for every `y ∈ H`.

## Main results

* `TauCeti.AppellHumbertData.normalizedTranslate_add_of_mem`: for `u, w ∈ L`, the normalised
  translations compose strictly: `N_u (N_w f) = N_{u + w} f`.
* `TauCeti.AppellHumbertData.normalizedTranslate_quotOut_eq`: if `N_{F l} f = f` for `l ∈ L`,
  then `N_{F (q.out)} f` depends only on the coset `q` in `H ⧸ K`.
* `TauCeti.AppellHumbertData.normalizedTranslate_charAverage`: for any character `ξ : AddChar Q ℂ`,
  `N_{F y} (∑ k : Q, ξ (-k) • N_{F k.out} f) = ξ y • ∑ k : Q, ξ (-k) • N_{F k.out} f`.

## Provenance

Adapted from `New.ThetaTori.IsHermitianAction.normShift_normShift_of_mem`,
`New.ThetaTori.IsHermitianAction.normShift_map_out`, and
`New.ThetaTori.IsHermitianAction.normShift_sum_eq_char_smul` in
`src/Lib/Shimura/GoodReduction/GaussSums.lean` of `grh-lean`
(https://github.com/lsernau/grh-lean, commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), built directly on
`TauCeti.AppellHumbertData.normalizedTranslate` and generalized to any additive map `F : V →+ V`.
-/

public section

open Complex

namespace TauCeti.AppellHumbertData

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {L : Submodule ℤ V}
  (D : AppellHumbertData L) {b : V →L[ℂ] V}

/-- On elements `u, w ∈ L`, if `E (b u, w) + E (u, b w) = E (u, w)` and `E (b L, L) ⊆ ℤ`, the
normalised translations compose without a phase factor: `N_u (N_w f) = N_{u + w} f`. -/
theorem normalizedTranslate_add_of_mem
    (hadj : ∀ u w, D.riemannForm (b u) w + D.riemannForm u (b w) = D.riemannForm u w)
    (hint : ∀ l m : L, ∃ k : ℤ, D.riemannForm m (b l) = k)
    {u w : V} (hu : u ∈ L) (hw : w ∈ L) (f : V → ℂ) :
    D.normalizedTranslate b u (D.normalizedTranslate b w f) =
      D.normalizedTranslate b (u + w) f := by
  rw [D.normalizedTranslate_normalizedTranslate hadj u w f]
  obtain ⟨k, hk⟩ := hint ⟨u, hu⟩ ⟨w, hw⟩
  have h1 : (Circle.exp (2 * Real.pi * D.riemannForm w (b u)) : ℂ) = 1 := by
    rw [hk, Circle.coe_exp]
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    push_cast
    ring
  rw [h1, one_smul]

/-- If `f` is fixed by `N_{F l}` for all `l ∈ L`, then for `K ≤ H` with `F '' K ⊆ F '' L` and
`F '' H ⊆ L`, the normalised translate `N_{F x} f` depends only on the coset of `x` in `H ⧸ K`. -/
theorem normalizedTranslate_quotOut_eq
    (hadj : ∀ u w, D.riemannForm (b u) w + D.riemannForm u (b w) = D.riemannForm u w)
    (hint : ∀ l m : L, ∃ k : ℤ, D.riemannForm m (b l) = k)
    (F : V →+ V) {H : AddSubgroup V} (hH : ∀ x ∈ H, F x ∈ L)
    (K : AddSubgroup H) (hK : ∀ x ∈ K, ∃ l ∈ L, F x.val = F l)
    {f : V → ℂ} (hf : ∀ l ∈ L, D.normalizedTranslate b (F l) f = f) (x : H) :
    D.normalizedTranslate b (F (QuotientAddGroup.mk (s := K) x).out.val) f =
      D.normalizedTranslate b (F x.val) f := by
  obtain ⟨k, hk⟩ := QuotientAddGroup.mk_out_eq_add K x
  obtain ⟨l, hl, hFl⟩ := hK k.val k.property
  rw [hk, AddSubgroup.coe_add, map_add, hFl,
    ← D.normalizedTranslate_add_of_mem hadj hint (hH x.val x.property)
      (hFl ▸ hH k.val.val k.val.property), hf l hl]

/-- Character-weighted average of normalised translates: for a finite quotient `Q = H ⧸ K` and an
additive character `ξ : AddChar Q ℂ`, the sum `s = ∑ k : Q, ξ (-k) • N_{F k.out} f` is an
eigenfunction of `N_{F y}` with eigenvalue `ξ y` for every `y : H`. -/
theorem normalizedTranslate_charAverage
    (hadj : ∀ u w, D.riemannForm (b u) w + D.riemannForm u (b w) = D.riemannForm u w)
    (hint : ∀ l m : L, ∃ k : ℤ, D.riemannForm m (b l) = k)
    (F : V →+ V) {H : AddSubgroup V} (hH : ∀ x ∈ H, F x ∈ L)
    (K : AddSubgroup H) [Fintype (H ⧸ K)] (hK : ∀ x ∈ K, ∃ l ∈ L, F x.val = F l)
    {f : V → ℂ} (hf : ∀ l ∈ L, D.normalizedTranslate b (F l) f = f)
    (ξ : AddChar (H ⧸ K) ℂ) (y : H) :
    D.normalizedTranslate b (F y.val)
        (∑ k : H ⧸ K, ξ (-k) • D.normalizedTranslate b (F k.out.val) f) =
      ξ (QuotientAddGroup.mk y) •
        (∑ k : H ⧸ K, ξ (-k) • D.normalizedTranslate b (F k.out.val) f) := by
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (s := K) y)) _ _ fun k ↦ ?_
  have hclass : (QuotientAddGroup.mk (s := K) (y + k.out)) =
      QuotientAddGroup.mk (s := K) y + k := by
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  have hterm : D.normalizedTranslate b (F (QuotientAddGroup.mk (s := K) y + k).out.val) f =
      D.normalizedTranslate b (F y.val) (D.normalizedTranslate b (F k.out.val) f) := by
    rw [← hclass, D.normalizedTranslate_quotOut_eq hadj hint F hH K hK hf (y + k.out),
      AddSubgroup.coe_add, map_add,
      D.normalizedTranslate_add_of_mem hadj hint (hH y.val y.property)
        (hH k.out.val k.out.property)]
  change D.normalizedTranslate b (F y.val) (ξ (-k) • D.normalizedTranslate b (F k.out.val) f) =
    ξ (QuotientAddGroup.mk y) •
      (ξ (-(QuotientAddGroup.mk y + k)) •
        D.normalizedTranslate b (F (QuotientAddGroup.mk (s := K) y + k).out.val) f)
  rw [hterm, map_smul, smul_smul, ← ξ.map_add_eq_mul, neg_add, add_neg_cancel_left]

end TauCeti.AppellHumbertData
