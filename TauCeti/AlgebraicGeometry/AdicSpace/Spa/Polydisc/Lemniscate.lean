/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Subdisc
public import TauCeti.Analysis.Normed.Field.Basic

import TauCeti.Algebra.Polynomial.Splits

/-!
# The domains `{|p| ≤ |c|}` and `{|c| ≤ |p|}` of one polynomial in the closed unit disc

Let `K` be a nonarchimedean normed field, `X = Spa (K⟨T⟩, K⟨T⟩°)` the closed unit disc, and `p` a
polynomial of positive degree that splits over `K`, with leading coefficient `u` and multiset of
roots `S`. For `c ∈ K` this file describes the two subsets of `X`

```text
X(p/c) = {x : x(p) ≤ x(c)},        X(c/p) = {x : x(c) ≤ x(p)},
```

the Weierstrass and the Laurent domain of `X` defined by `p` and the constant `c`. For each root
`b` choose a radius `d b ∈ K` with

```text
‖u‖ · ∏_{α ∈ S} max ‖d b‖ ‖b - α‖ = ‖c‖,
```

which over an algebraically closed field is always possible
(`NormedField.exists_prod_map_max_norm_eq_of_isAlgClosed`). Then, for `c ≠ 0`,

```text
X(p/c) = ⋃_{b ∈ S} D(b, |d b|),        X(c/p) = ⋂_{b ∈ S} {x : x(d b) ≤ x(T - b)},
```

so `X(p/c)` is a finite union of closed discs about the roots of `p`, and `X(c/p)` is the closed
unit disc with the open discs of radius `‖d b‖` about the roots removed. Classically these are
the lemniscates `{y : |p(y)| ≤ |c|}` and their complements; here the statements hold for all
points of the adic disc, including those of rank two.

## Main results

* `TauCeti.ValuationSpectrum.setOf_eval₂RingHom_vle_weightedC_eq_iUnion_closedSubdisc`: the
  Weierstrass domain `X(p/c)` is the union of the closed discs `D(b, |d b|)` about the roots `b`
  of `p`.
* `TauCeti.ValuationSpectrum.setOf_weightedC_vle_eval₂RingHom_eq_iInter`: the Laurent domain
  `X(c/p)` is the intersection of the sets `{x : x(d b) ≤ x(T - b)}`.
* `TauCeti.ValuationSpectrum.exists_setOf_vle_eq_iUnion_closedSubdisc_and_setOf_vle_eq_iInter`:
  over an algebraically closed field, radii `d b ≠ 0` with both descriptions exist.

## Implementation notes

No classification of the points of `X` is used. For a point `x` and a centre `b`, the ultrametric
inequality `x(T - α) ≤ max (x(T - b)) (x(b - α))` bounds `x(p)` above by
`x(u) ∏_α max (x(T - b)) (x(b - α))`, and this is an equality when `b` is a root minimising
`α ↦ x(T - α)` over the finitely many roots. The bound is strictly increasing in `x(T - b)` when
`b` is a root, and equals `x(c)` when `x(T - b)` is replaced by `x(d b)`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* J. Fresnel, M. van der Put, *Rigid Analytic Geometry and Its Applications*, Chapter 2, for
  the rational subdomains of the closed disc.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NormedField K]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight

/-! ### Values of constants and of split polynomials -/

/-- If `‖u‖ ∏_{α ∈ S} max ‖e‖ ‖b - α‖ = ‖c‖` with `b ∈ S` and `c ≠ 0`, then `e ≠ 0`: the factor at
`α = b` is `‖e‖`. -/
private theorem ne_zero_of_norm_mul_prod_map_max_eq {S : Multiset K} {u b c e : K} (hb : b ∈ S)
    (hd : ‖u‖ * (S.map fun α ↦ max ‖e‖ ‖b - α‖).prod = ‖c‖) (hc : c ≠ 0) : e ≠ 0 := by
  rintro rfl
  obtain ⟨S, rfl⟩ := Multiset.exists_cons_of_mem hb
  rw [Multiset.map_cons, Multiset.prod_cons, sub_self, norm_zero, max_self, zero_mul, mul_zero,
    eq_comm, norm_eq_zero] at hd
  exact hc hd

variable [NonarchimedeanRing K]

/-- The value of a split polynomial is the value of its leading coefficient times the values of
its linear factors. -/
private theorem valuation_eval₂RingHom_eq (x : closedPolydisc 1 K) {p : Polynomial K}
    (hroots : Multiset.card p.roots = p.natDegree) :
    x.1.valuation (Polynomial.eval₂RingHom C T p) =
      x.1.valuation (C p.leadingCoeff) * (p.roots.map fun α ↦ x.1.valuation (T - C α)).prod := by
  rw [Polynomial.coe_eval₂RingHom,
    Polynomial.Splits.eval₂_eq_prod_roots (Polynomial.splits_iff_card_roots.mpr hroots), map_mul,
    map_multiset_prod, Multiset.map_map, Function.comp_def]

/-- **The bound at a centre `b`**: since `x(T - α) ≤ max (x(T - b)) (x(b - α))`, the value of a
split polynomial is at most `x(u) ∏_α max (x(T - b)) (x(b - α))`. -/
private theorem valuation_eval₂RingHom_le (x : closedPolydisc 1 K) {p : Polynomial K}
    (hroots : Multiset.card p.roots = p.natDegree) (b : K) :
    x.1.valuation (Polynomial.eval₂RingHom C T p) ≤ x.1.valuation (C p.leadingCoeff) *
      (p.roots.map fun α ↦ max (x.1.valuation (T - C b)) (x.1.valuation (C (b - α)))).prod := by
  rw [valuation_eval₂RingHom_eq x hroots]
  refine mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ fun α _ ↦ ?_) _
  rw [show T - C α = (T - C b) + C (b - α) by rw [map_sub]; ring]
  exact Valuation.map_add _ _ _

/-- **The bound is attained at a minimising root**: if `x(T - b) ≤ x(T - α)` for every root `α`,
then `x(T - α) = max (x(T - b)) (x(b - α))` for every root, and the bound at `b` is the value of
the polynomial. -/
private theorem valuation_eval₂RingHom_eq_of_forall_le (x : closedPolydisc 1 K) {p : Polynomial K}
    (hroots : Multiset.card p.roots = p.natDegree) {b : K}
    (hb : ∀ α ∈ p.roots, x.1.valuation (T - C b) ≤ x.1.valuation (T - C α)) :
    x.1.valuation (Polynomial.eval₂RingHom C T p) = x.1.valuation (C p.leadingCoeff) *
      (p.roots.map fun α ↦ max (x.1.valuation (T - C b)) (x.1.valuation (C (b - α)))).prod := by
  refine (valuation_eval₂RingHom_le x hroots b).antisymm ?_
  rw [valuation_eval₂RingHom_eq x hroots]
  refine mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ fun α hα ↦ max_le (hb α hα) ?_) _
  -- `b - α = (T - α) - (T - b)`, and `x(T - b) ≤ x(T - α)`
  rw [show C (b - α) = (T - C α) - (T - C b) by rw [map_sub]; ring]
  exact (Valuation.map_sub _ _ _).trans (max_le le_rfl (hb α hα))

/-- **Some root attains the bound**: a root `b` minimising `α ↦ x(T - α)` over the finitely many
roots satisfies the hypothesis of `valuation_eval₂RingHom_eq_of_forall_le`. -/
private theorem exists_mem_roots_valuation_eval₂RingHom_eq (x : closedPolydisc 1 K)
    {p : Polynomial K} (hroots : Multiset.card p.roots = p.natDegree) (hp : 0 < p.natDegree) :
    ∃ b ∈ p.roots, x.1.valuation (Polynomial.eval₂RingHom C T p) =
      x.1.valuation (C p.leadingCoeff) *
        (p.roots.map fun α ↦ max (x.1.valuation (T - C b)) (x.1.valuation (C (b - α)))).prod := by
  classical
  obtain ⟨b, hb, hmin⟩ := p.roots.toFinset.exists_min_image (fun α ↦ x.1.valuation (T - C α))
    (Multiset.toFinset_nonempty.mpr (Multiset.card_pos.mp (hroots ▸ hp)))
  exact ⟨b, Multiset.mem_toFinset.mp hb, valuation_eval₂RingHom_eq_of_forall_le x hroots
    fun α hα ↦ hmin α (Multiset.mem_toFinset.mpr hα)⟩

variable [IsUltrametricDist K]

/-- **The bound is strictly increasing at a root**: if `b` is one of the `α ∈ S` and `u ≠ 0`, then
replacing `x(f)` by a larger `x(g)` strictly increases `x(u) ∏_{α ∈ S} max (x(f)) (x(b - α))`,
since the factor at `α = b` is `x(f)` itself. -/
private theorem valuation_mul_prod_map_max_lt (x : closedPolydisc 1 K) {S : Multiset K} {u b : K}
    (hu : u ≠ 0) (hb : b ∈ S) {f g : 𝒯} (h : x.1.valuation f < x.1.valuation g) :
    x.1.valuation (C u) * (S.map fun α ↦ max (x.1.valuation f) (x.1.valuation (C (b - α)))).prod <
      x.1.valuation (C u) *
        (S.map fun α ↦ max (x.1.valuation g) (x.1.valuation (C (b - α)))).prod := by
  refine mul_lt_mul_of_pos_left ?_
    (zero_lt_iff.mpr fun h0 ↦ hu ((closedPolydisc_valuation_weightedC_eq_zero_iff x u).mp h0))
  obtain ⟨S, rfl⟩ := Multiset.exists_cons_of_mem hb
  simp only [Multiset.map_cons, Multiset.prod_cons, sub_self, map_zero, max_eq_left zero_le]
  have hpos : 0 < (S.map fun α ↦ max (x.1.valuation g) (x.1.valuation (C (b - α)))).prod := by
    refine zero_lt_iff.mpr (Multiset.prod_ne_zero fun h0 ↦ ?_)
    obtain ⟨α, -, hα⟩ := Multiset.mem_map.mp h0
    exact (zero_le.trans_lt h).ne' (le_zero_iff.mp (hα ▸ le_max_left _ _))
  calc x.1.valuation f * (S.map fun α ↦ max (x.1.valuation f) (x.1.valuation (C (b - α)))).prod
      ≤ x.1.valuation f * (S.map fun α ↦ max (x.1.valuation g) (x.1.valuation (C (b - α)))).prod :=
        mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ fun _ _ ↦ max_le_max_right _ h.le) _
    _ < x.1.valuation g * (S.map fun α ↦ max (x.1.valuation g) (x.1.valuation (C (b - α)))).prod :=
        mul_lt_mul_of_pos_right h hpos

/-- **The bound at the radius**: if `‖u‖ ∏_{α ∈ S} max ‖d‖ ‖b - α‖ = ‖c‖`, then
`x(u) ∏_{α ∈ S} max (x(d)) (x(b - α)) = x(c)`. -/
private theorem valuation_mul_prod_map_max_eq (x : closedPolydisc 1 K) {S : Multiset K}
    {u b c d : K} (hd : ‖u‖ * (S.map fun α ↦ max ‖d‖ ‖b - α‖).prod = ‖c‖) :
    x.1.valuation (C u) *
        (S.map fun α ↦ max (x.1.valuation (C d)) (x.1.valuation (C (b - α)))).prod =
      x.1.valuation (C c) := by
  set e : K → K := fun α ↦ if ‖d‖ ≤ ‖b - α‖ then b - α else d
  have he (α : K) : ‖e α‖ = max ‖d‖ ‖b - α‖ := by
    simp only [e]
    split_ifs with h
    exacts [(max_eq_right h).symm, (max_eq_left (le_of_not_ge h)).symm]
  have hprod : x.1.valuation (C u) * (S.map fun α ↦ x.1.valuation (C (e α))).prod =
      x.1.valuation (C (u * (S.map e).prod)) := by
    rw [map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def]
  simp only [closedPolydisc_max_valuation_weightedC]
  refine hprod.trans (closedPolydisc_valuation_weightedC_eq_of_norm_eq x ?_)
  rw [norm_mul, Multiset.norm_prod, Multiset.map_map, ← hd]
  simp only [Function.comp_def, he]

/-! ### The two domains -/

variable {p : Polynomial K} {c : K} {d : K → K}

/-- **The Weierstrass domain `{x : x(p) ≤ x(c)}` of one polynomial is a finite union of closed
discs.** Let `p` be a polynomial of positive degree whose roots account for its degree, `c ≠ 0`,
and for each root `b` let `d b` satisfy `‖u‖ ∏_α max ‖d b‖ ‖b - α‖ = ‖c‖`, where `u` is the leading
coefficient and `α` runs over the roots with multiplicity. Then a point of the closed unit disc
satisfies `x(p) ≤ x(c)` exactly when it lies in one of the discs `D(b, |d b|)`. -/
theorem setOf_eval₂RingHom_vle_weightedC_eq_iUnion_closedSubdisc
    (hroots : Multiset.card p.roots = p.natDegree) (hp : 0 < p.natDegree) (hc : c ≠ 0)
    (hd : ∀ b ∈ p.roots,
      ‖p.leadingCoeff‖ * (p.roots.map fun α ↦ max ‖d b‖ ‖b - α‖).prod = ‖c‖) :
    {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T p) (C c)} =
      ⋃ b ∈ p.roots, closedSubdisc b (d b) := by
  have hu := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hp)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_closedSubdisc, exists_prop]
  constructor
  · intro h
    obtain ⟨b, hb, hval⟩ := exists_mem_roots_valuation_eval₂RingHom_eq x hroots hp
    refine ⟨b, hb, ?_, fun h0 ↦ ?_⟩
    · rw [← valuation_le_iff]
      by_contra! hlt
      have key := valuation_mul_prod_map_max_lt x hu hb hlt
      rw [valuation_mul_prod_map_max_eq x (hd b hb), ← hval] at key
      exact key.not_ge ((valuation_le_iff _ _ _).mpr h)
    · rw [← map_zero C, ← valuation_le_iff, map_zero C, map_zero, le_zero_iff,
        closedPolydisc_valuation_weightedC_eq_zero_iff] at h0
      exact ne_zero_of_norm_mul_prod_map_max_eq hb (hd b hb) hc h0
  · rintro ⟨b, hb, h, -⟩
    rw [← valuation_le_iff] at h ⊢
    refine (valuation_eval₂RingHom_le x hroots b).trans ?_
    rw [← valuation_mul_prod_map_max_eq x (hd b hb)]
    exact mul_le_mul_right (Multiset.prod_map_le_prod_map _ _ fun _ _ ↦ max_le_max_right _ h) _

/-- **The Laurent domain `{x : x(c) ≤ x(p)}` of one polynomial is the closed unit disc with
finitely many open discs removed.** Let `p` be a polynomial of positive degree whose roots account
for its degree, and for each root `b` let `d b` satisfy `‖u‖ ∏_α max ‖d b‖ ‖b - α‖ = ‖c‖`, where
`u` is the leading coefficient and `α` runs over the roots with multiplicity. Then a point of the
closed unit disc satisfies `x(c) ≤ x(p)` exactly when `x(d b) ≤ x(T - b)` for every root `b`. -/
theorem setOf_weightedC_vle_eval₂RingHom_eq_iInter
    (hroots : Multiset.card p.roots = p.natDegree) (hp : 0 < p.natDegree)
    (hd : ∀ b ∈ p.roots,
      ‖p.leadingCoeff‖ * (p.roots.map fun α ↦ max ‖d b‖ ‖b - α‖).prod = ‖c‖) :
    {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (C c) (Polynomial.eval₂RingHom C T p)} =
      ⋂ b ∈ p.roots, {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (C (d b)) (T - C b)} := by
  have hu := Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hp)
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, ← valuation_le_iff]
  constructor
  · intro h b hb
    by_contra! hlt
    have key := valuation_mul_prod_map_max_lt x hu hb hlt
    rw [valuation_mul_prod_map_max_eq x (hd b hb)] at key
    exact ((valuation_eval₂RingHom_le x hroots b).trans_lt key).not_ge h
  · intro h
    obtain ⟨b, hb, hval⟩ := exists_mem_roots_valuation_eval₂RingHom_eq x hroots hp
    rw [hval, ← valuation_mul_prod_map_max_eq x (hd b hb)]
    exact mul_le_mul_right
      (Multiset.prod_map_le_prod_map _ _ fun _ _ ↦ max_le_max_right _ (h b hb)) _

/-- **The domains of one polynomial over an algebraically closed field.** For a polynomial `p` of
positive degree and `c ≠ 0` there are nonzero radii `d b`, one for each root `b` of `p`, such that
`{x : x(p) ≤ x(c)}` is the union of the closed discs `D(b, |d b|)` and `{x : x(c) ≤ x(p)}` is the
set of points with `x(d b) ≤ x(T - b)` for every root `b`. -/
theorem exists_setOf_vle_eq_iUnion_closedSubdisc_and_setOf_vle_eq_iInter [IsAlgClosed K]
    (hp : 0 < p.natDegree) (hc : c ≠ 0) :
    ∃ d : K → K, (∀ b ∈ p.roots, d b ≠ 0) ∧
      {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T p) (C c)} =
        ⋃ b ∈ p.roots, closedSubdisc b (d b) ∧
      {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (C c) (Polynomial.eval₂RingHom C T p)} =
        ⋂ b ∈ p.roots, {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (C (d b)) (T - C b)} := by
  have hroots := IsAlgClosed.card_roots_eq_natDegree (p := p)
  have hu : p.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hp)
  have key (b : K) : ∃ e : K, b ∈ p.roots →
      ‖p.leadingCoeff‖ * (p.roots.map fun α ↦ max ‖e‖ ‖b - α‖).prod = ‖c‖ := by
    by_cases hb : b ∈ p.roots
    · obtain ⟨e, he⟩ := NormedField.exists_prod_map_max_norm_eq_of_isAlgClosed
        (Multiset.mem_map.mpr ⟨b, hb, sub_self b⟩) (c / p.leadingCoeff)
      refine ⟨e, fun _ ↦ ?_⟩
      rw [Multiset.map_map, Function.comp_def, norm_div] at he
      rw [he, mul_div_cancel₀ _ (norm_ne_zero_iff.mpr hu)]
    · exact ⟨0, fun h ↦ (hb h).elim⟩
  choose d hd using key
  exact ⟨d, fun b hb ↦ ne_zero_of_norm_mul_prod_map_max_eq hb (hd b hb) hc,
    setOf_eval₂RingHom_vle_weightedC_eq_iUnion_closedSubdisc hroots hp hc fun b hb ↦ hd b hb,
    setOf_weightedC_vle_eval₂RingHom_eq_iInter hroots hp fun b hb ↦ hd b hb⟩

end TauCeti.ValuationSpectrum
