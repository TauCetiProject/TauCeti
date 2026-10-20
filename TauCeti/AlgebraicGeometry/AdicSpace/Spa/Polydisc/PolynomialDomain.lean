/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.HoledDisc
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Lemniscate
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.RationalSubset
import TauCeti.RingTheory.Huber.Normed
import TauCeti.Topology.Homeomorph.SetCongr

/-!
# The domains `{|f| ≤ |g|}` and the rational subsets of the closed unit disc

Let `K` be an algebraically closed nonarchimedean normed field and `X = Spa (K⟨T⟩, K⟨T⟩°)` the
closed unit disc. For coprime polynomials `f` and `g` this file shows that

```text
X(f/g) = {x : x(f) ≤ x(g)}
```

is a finite union of *holed discs* `TauCeti.ValuationSpectrum.holedDisc`, closed discs with
finitely many open discs removed:

```text
X(f/g) = ⋃_{(a, c, H) ∈ P} D(a, |c|) ∖ ⋃_{(b, d) ∈ H} D⁻(b, |d|)
```

for a finite set `P` of triples. Classically these are the rational lemniscates
`{y : |f(y)| ≤ |g(y)|}`; here the statement holds for all points of the adic disc, including those
of rank two. It generalises the one-polynomial case `g = c` of `Lemniscate.lean`.

When `K` is moreover a Tate ring, for instance when its norm is nontrivial, it follows that every
rational subset of `X` is a finite union of holed discs, which describes the rational subdomains of
the closed disc. A rational subset has a presentation `R(f₁, …, fₙ / g)` by polynomials with a
nonzero constant among the `fᵢ`
(`TauCeti.ValuationSpectrum.mem_spaRationalFamily_iff_exists_polynomial`). The constant forces
`x(g) ≠ 0`, so the subset is the intersection of the domains `X(fᵢ/g)`, and in each of them the
common factor `gcd(fᵢ, g)` can be cancelled. Finite intersections of finite unions of holed discs
are again finite unions of holed discs (`TauCeti.ValuationSpectrum.IsHoledDiscUnion.inter`), since
two closed discs meet in a closed disc or not at all.

Conversely every finite union of holed discs is rational
(`TauCeti.ValuationSpectrum.IsHoledDiscUnion.mem_spaRationalFamily`), so over an algebraically
closed nontrivially normed field the rational subsets of `X` are exactly the finite unions of
holed discs.

Coprimality cannot be dropped: for `f = T` and `g = c T` with `0 < ‖c‖ < 1`, the domain `X(f/g)`
is the zero locus of `T`, while every nonempty holed disc contains a Gauss point, at which `T` does
not vanish.

## Main results

* `TauCeti.ValuationSpectrum.exists_finset_setOf_vle_eq_iUnion_holedDisc`: for
  coprime `f` and `g`, the domain `X(f/g)` is a finite union of holed discs.
* `TauCeti.ValuationSpectrum.exists_finset_eq_iUnion_holedDisc_of_mem_spaRationalFamily`: every
  rational subset of `X` is a finite union of holed discs `TauCeti.ValuationSpectrum.holedDisc`.
* `TauCeti.ValuationSpectrum.mem_spaRationalFamily_iff_isHoledDiscUnion`: a subset of `X` is
  rational if and only if it is a finite union of holed discs.

## Implementation notes

No classification of the points of `X` is used. Let `Z` be the finite set of roots of `f` and `g`,
together with `0`. A point `x` is sorted by a centre `γ ∈ Z` minimising `α ↦ x(T - α)`, and by the
largest distance `‖γ - δ‖`, `δ ∈ Z`, below `x(T - γ)`. On the set of points with given `γ` and `δ`
(a holed disc), each factor `max (x(T - γ)) (x(γ - α))` of
`TauCeti.ValuationSpectrum.valuation_eval₂RingHom_eq_of_forall_le` is either `x(T - γ)` or the
constant `x(γ - α)`, so `x(f) = x(T - γ)ᵐ x(c)` and `x(g) = x(T - γ)ⁿ x(e)` for constants `c`, `e`.
If `m = n`, or if `n < m` and `c = 0`, the inequality `x(f) ≤ x(g)` holds on the whole cell or on
none of it (here `e ≠ 0` as `g ≠ 0`). Otherwise it compares `x(T - γ)` with `x(ρ)` for an element
`ρ ∈ K` with `ρ ^ (m - n) = e / c` if `n < m`, or `ρ ^ (n - m) = c / e` if `m < n`, which exists
because `K` is algebraically closed; so it becomes one more disc or hole about `γ`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Example 7.57.
* J. Fresnel, M. van der Put, *Rigid Analytic Geometry and Its Applications*, Chapter 2, for
  the rational subdomains of the closed disc.
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §7.2, for rational subdomains of
  affinoid spaces.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [NonarchimedeanRing K]

local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set K)) isWeightFamily_one_weight
local notation "𝒯" K => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set K))
  isWeightFamily_one_weight

/-! ### Cells of the closed disc relative to a finite set of centres -/

/-- The points `x` such that `x(γ - α) ≤ x(T - α)` for every `α ∈ Z` (equivalently, `γ`
minimises `α ↦ x(T - α)` over `Z`), `x(γ - δ) ≤ x(T - γ)`, and `x(T - γ) ≤ x(γ - α)` for every
`α ∈ Z` farther from `γ` than `δ`. -/
private noncomputable def cell (Z : Finset K) (γ δ : K) : Set (closedPolydisc 1 K) :=
  (⋂ α ∈ Z, {x | x.1.toValuativeRel.vle (C (γ - α)) (T - C α)}) ∩
    {x | x.1.toValuativeRel.vle (C (γ - δ)) (T - C γ)} ∩
    ⋂ α ∈ Z.filter fun α ↦ ‖γ - δ‖ < ‖γ - α‖, closedSubdisc γ (γ - α)

private theorem mem_cell {Z : Finset K} {γ δ : K} {x : closedPolydisc 1 K} :
    x ∈ cell Z γ δ ↔ (∀ α ∈ Z, x.1.valuation (C (γ - α)) ≤ x.1.valuation (T - C α)) ∧
      x.1.valuation (C (γ - δ)) ≤ x.1.valuation (T - C γ) ∧
      ∀ α ∈ Z, ‖γ - δ‖ < ‖γ - α‖ → x.1.valuation (T - C γ) ≤ x.1.valuation (C (γ - α)) := by
  simp only [cell, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, Finset.mem_filter,
    mem_closedSubdisc, ← valuation_le_iff, and_imp, and_assoc]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ forall₂_congr fun α _ ↦
    imp_congr_right fun h ↦ and_iff_left ?_
  rw [← map_zero C, closedPolydisc_valuation_weightedC_le_iff, norm_zero, not_le]
  exact (norm_nonneg _).trans_lt h

private theorem isHoledDiscUnion_cell (Z : Finset K) (γ δ : K) :
    IsHoledDiscUnion (cell Z γ δ) := by
  rw [cell, ← Set.univ_inter (⋂ α ∈ Z, _)]
  exact ((isHoledDiscUnion_univ.inter_biInter_setOf_vle Z (fun α ↦ α)
    (fun α ↦ γ - α)).inter_setOf_vle
    γ (γ - δ)).inter_biInter_closedSubdisc _ (fun _ ↦ γ) (fun α ↦ γ - α)

/-- **The cells cover the closed disc**: take `γ ∈ Z` minimising `α ↦ x(T - α)`, then `δ ∈ Z`
maximising `‖γ - δ‖` subject to `x(γ - δ) ≤ x(T - γ)`. -/
private theorem exists_mem_cell {Z : Finset K} (hZ : Z.Nonempty) (x : closedPolydisc 1 K) :
    ∃ γ ∈ Z, ∃ δ ∈ Z, x ∈ cell Z γ δ := by
  classical
  obtain ⟨γ, hγ, hmin⟩ := Z.exists_min_image (fun α ↦ x.1.valuation (T - C α)) hZ
  obtain ⟨δ, hδ, hmax⟩ :=
    (Z.filter fun α ↦ x.1.valuation (C (γ - α)) ≤ x.1.valuation (T - C γ)).exists_max_image
      (fun α ↦ ‖γ - α‖) ⟨γ, Finset.mem_filter.mpr ⟨hγ, by simp⟩⟩
  rw [Finset.mem_filter] at hδ
  refine ⟨γ, hγ, δ, hδ.1, mem_cell.mpr ⟨fun α hα ↦ ?_, hδ.2, fun α hα hlt ↦ ?_⟩⟩
  · -- `γ - α = (T - α) - (T - γ)`, and `x(T - γ) ≤ x(T - α)`
    rw [show C (γ - α) = (T - C α) - (T - C γ) by rw [map_sub]; ring]
    exact (Valuation.map_sub _ _ _).trans (max_le le_rfl (hmin α hα))
  · by_contra! h
    exact hlt.not_ge (hmax α (Finset.mem_filter.mpr ⟨hα, h.le⟩))

/-- On a cell, `γ` minimises `α ↦ x(T - α)` over `Z`. -/
private theorem valuation_le_of_mem_cell {Z : Finset K} {γ δ α : K} {x : closedPolydisc 1 K}
    (hx : x ∈ cell Z γ δ) (hα : α ∈ Z) :
    x.1.valuation (T - C γ) ≤ x.1.valuation (T - C α) := by
  -- `T - γ = (T - α) - (γ - α)`, and `x(γ - α) ≤ x(T - α)`
  rw [show T - C γ = (T - C α) - C (γ - α) by rw [map_sub]; ring]
  exact (Valuation.map_sub _ _ _).trans (max_le le_rfl ((mem_cell.mp hx).1 α hα))

/-- On a cell, `max (x(T - γ)) (x(γ - α))` is `x(T - γ)` for the centres `α` at distance at most
`‖γ - δ‖` from `γ`, and the constant `x(γ - α)` for the others. -/
private theorem max_valuation_eq_ite_of_mem_cell {Z : Finset K} {γ δ α : K}
    {x : closedPolydisc 1 K} (hx : x ∈ cell Z γ δ) (hα : α ∈ Z) :
    max (x.1.valuation (T - C γ)) (x.1.valuation (C (γ - α))) =
      if ‖γ - α‖ ≤ ‖γ - δ‖ then x.1.valuation (T - C γ) else x.1.valuation (C (γ - α)) := by
  obtain ⟨-, hlow, hup⟩ := mem_cell.mp hx
  split_ifs with h
  · exact max_eq_left (((closedPolydisc_valuation_weightedC_le_iff x _ _).mpr h).trans hlow)
  · exact max_eq_right (hup α hα (not_le.mp h))

/-- **The value of a split polynomial on a cell**: if the roots of `p` lie in `Z`, then on the
cell of `(γ, δ)`, `x(p) = x(T - γ)ᵐ x(c)`, where `m` counts the roots at distance at most
`‖γ - δ‖` from `γ` and `c` is the leading coefficient times the product of `γ - α` over the
other roots. -/
private theorem valuation_eval₂RingHom_eq_pow_mul_of_mem_cell {Z : Finset K} {γ δ : K}
    {x : closedPolydisc 1 K} (hx : x ∈ cell Z γ δ) {p : Polynomial K}
    (hroots : Multiset.card p.roots = p.natDegree) (hZ : ∀ α ∈ p.roots, α ∈ Z) :
    x.1.valuation (Polynomial.eval₂RingHom C T p) =
      x.1.valuation (T - C γ) ^ Multiset.card (p.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) *
        x.1.valuation (C (p.leadingCoeff *
          ((p.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map (γ - ·)).prod)) := by
  rw [valuation_eval₂RingHom_eq_of_forall_le x hroots fun α hα ↦
      valuation_le_of_mem_cell hx (hZ α hα),
    Multiset.map_congr rfl fun α hα ↦ max_valuation_eq_ite_of_mem_cell hx (hZ α hα)]
  have h₁ : ((p.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖).map fun α ↦
      if ‖γ - α‖ ≤ ‖γ - δ‖ then x.1.valuation (T - C γ) else x.1.valuation (C (γ - α))) =
      (p.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖).map fun _ ↦ x.1.valuation (T - C γ) :=
    Multiset.map_congr rfl fun α hα ↦ ite_eq_left (Multiset.of_mem_filter hα)
  have h₂ : ((p.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map fun α ↦
      if ‖γ - α‖ ≤ ‖γ - δ‖ then x.1.valuation (T - C γ) else x.1.valuation (C (γ - α))) =
      (p.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map fun α ↦ x.1.valuation (C (γ - α)) :=
    Multiset.map_congr rfl fun α hα ↦ ite_eq_right (Multiset.mem_filter.mp hα).2
  conv_lhs => rw [← Multiset.filter_add_not (fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) p.roots]
  rw [Multiset.map_add, Multiset.prod_add, h₁, h₂]
  simp [map_multiset_prod, mul_left_comm (x.1.valuation (C p.leadingCoeff))]

/-- **At a point of the cell with `x(T - γ) = 0`**, `δ = γ` and `γ` is not a root of both of two
coprime polynomials, so one of the two root counts of
`valuation_eval₂RingHom_eq_pow_mul_of_mem_cell` vanishes. -/
private theorem card_filter_eq_zero_or_of_mem_cell {Z : Finset K} {γ δ : K}
    {x : closedPolydisc 1 K} (hx : x ∈ cell Z γ δ) (h0 : x.1.valuation (T - C γ) = 0)
    {f g : Polynomial K} (hfg : IsCoprime f g) :
    Multiset.card (f.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) = 0 ∨
      Multiset.card (g.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) = 0 := by
  have hδ : ‖γ - δ‖ = 0 := by
    have hlow := (mem_cell.mp hx).2.1
    rwa [h0, le_zero_iff, closedPolydisc_valuation_weightedC_eq_zero_iff, ← norm_eq_zero] at hlow
  have hroot {p : Polynomial K}
      (hp : Multiset.card (p.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) ≠ 0) :
      Polynomial.X - Polynomial.C γ ∣ p := by
    obtain ⟨α, hα⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero hp)
    have hαγ : α = γ := by
      have := Multiset.of_mem_filter hα
      rw [hδ, norm_le_zero_iff, sub_eq_zero] at this
      exact this.symm
    rw [Polynomial.dvd_iff_isRoot, ← hαγ]
    exact (Polynomial.mem_roots'.mp (Multiset.mem_of_mem_filter hα)).2
  by_contra! h
  exact Polynomial.not_isUnit_X_sub_C γ (hfg.isUnit_of_dvd' (hroot h.1) (hroot h.2))

/-! ### The domain of two polynomials -/

/-- On a cell, the inequality `x(f) ≤ x(g)` is the inequality
`x(T - γ)ᵐ x(c) ≤ x(T - γ)ⁿ x(e)` of `valuation_eval₂RingHom_eq_pow_mul_of_mem_cell`. -/
private theorem vle_iff_of_mem_cell [IsAlgClosed K] {Z : Finset K} {γ δ : K}
    {x : closedPolydisc 1 K} (hx : x ∈ cell Z γ δ) {f g : Polynomial K}
    (hZf : ∀ α ∈ f.roots, α ∈ Z) (hZg : ∀ α ∈ g.roots, α ∈ Z) :
    x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T f) (Polynomial.eval₂RingHom C T g) ↔
      x.1.valuation (T - C γ) ^ Multiset.card (f.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) *
          x.1.valuation (C (f.leadingCoeff *
            ((f.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map (γ - ·)).prod)) ≤
        x.1.valuation (T - C γ) ^ Multiset.card (g.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖) *
          x.1.valuation (C (g.leadingCoeff *
            ((g.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map (γ - ·)).prod)) := by
  rw [← valuation_le_iff,
    valuation_eval₂RingHom_eq_pow_mul_of_mem_cell hx IsAlgClosed.card_roots_eq_natDegree hZf,
    valuation_eval₂RingHom_eq_pow_mul_of_mem_cell hx IsAlgClosed.card_roots_eq_natDegree hZg]

/-- **Comparing `x(T - γ)ʲ x(a)` with `x(T - γ)ᵏ x(b)`** for `j < k` and `ρ ^ (k - j) = a / b`
is comparing `x(ρ)` with `x(T - γ)`, at a point with `x(T - γ) ≠ 0`: write `x(a) = x(ρ)ᵏ⁻ʲ x(b)`,
then cancel `x(T - γ)ʲ` and `x(b)` and compare `(k - j)`-th powers. -/
private theorem valuation_pow_mul_le_iff {x : closedPolydisc 1 K} {γ ρ a b : K} {j k : ℕ}
    (hjk : j < k) (hb : b ≠ 0) (hρ : ρ ^ (k - j) = a / b)
    (h0 : x.1.valuation (T - C γ) ≠ 0) :
    (x.1.valuation (T - C γ) ^ j * x.1.valuation (C a) ≤
        x.1.valuation (T - C γ) ^ k * x.1.valuation (C b) ↔
      x.1.valuation (C ρ) ≤ x.1.valuation (T - C γ)) ∧
    (x.1.valuation (T - C γ) ^ k * x.1.valuation (C b) ≤
        x.1.valuation (T - C γ) ^ j * x.1.valuation (C a) ↔
      x.1.valuation (T - C γ) ≤ x.1.valuation (C ρ)) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hjk.le
  rw [Nat.add_sub_cancel_left] at hρ
  have ha : x.1.valuation (C a) = x.1.valuation (C ρ) ^ l * x.1.valuation (C b) := by
    rw [← map_pow, ← map_pow, ← map_mul, ← map_mul, hρ, div_mul_cancel₀ _ hb]
  have hb' : 0 < x.1.valuation (C b) :=
    zero_lt_iff.mpr ((closedPolydisc_valuation_weightedC_eq_zero_iff x b).not.mpr hb)
  rw [ha, pow_add, mul_assoc]
  constructor <;>
  rw [mul_le_mul_iff_right₀ (pow_pos (zero_lt_iff.mpr h0) _), mul_le_mul_iff_left₀ hb',
    pow_le_pow_iff_left₀ zero_le zero_le (by omega)]

/-- **On each cell, `X(f/g)` is a finite union of holed discs.** On the cell of `(γ, δ)`, the
inequality `x(T - γ)ᵐ x(c) ≤ x(T - γ)ⁿ x(e)` of
`valuation_eval₂RingHom_eq_pow_mul_of_mem_cell` holds everywhere or nowhere if `m = n`, and
otherwise says `x(T - γ) ≤ x(ρ)` (if `n < m`) or `x(ρ) ≤ x(T - γ)` (if `m < n`) for a root `ρ` of
`ρ^|m - n| = e / c` or `c / e`. -/
private theorem isHoledDiscUnion_cell_inter [IsAlgClosed K] {Z : Finset K} {f g : Polynomial K}
    (hfg : IsCoprime f g) (hg : g ≠ 0) (hZf : ∀ α ∈ f.roots, α ∈ Z) (hZg : ∀ α ∈ g.roots, α ∈ Z)
    (γ δ : K) :
    IsHoledDiscUnion (cell Z γ δ ∩ {x | x.1.toValuativeRel.vle
      (Polynomial.eval₂RingHom C T f) (Polynomial.eval₂RingHom C T g)}) := by
  set m := Multiset.card (f.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖)
  set n := Multiset.card (g.roots.filter fun α ↦ ‖γ - α‖ ≤ ‖γ - δ‖)
  set c := f.leadingCoeff * ((f.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map (γ - ·)).prod
  set e := g.leadingCoeff * ((g.roots.filter fun α ↦ ¬ ‖γ - α‖ ≤ ‖γ - δ‖).map (γ - ·)).prod
  have he : e ≠ 0 := by
    refine mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg) (Multiset.prod_ne_zero fun h ↦ ?_)
    obtain ⟨α, hα, h0⟩ := Multiset.mem_map.mp h
    exact Multiset.of_mem_filter hα (by rw [h0, norm_zero]; exact norm_nonneg _)
  -- it suffices to describe the inequality `x(T - γ)ᵐ x(c) ≤ x(T - γ)ⁿ x(e)` on the cell
  have key (H : Set (closedPolydisc 1 K)) (hH : IsHoledDiscUnion (cell Z γ δ ∩ H))
      (hiff : ∀ x ∈ cell Z γ δ, x.1.valuation (T - C γ) ^ m * x.1.valuation (C c) ≤
        x.1.valuation (T - C γ) ^ n * x.1.valuation (C e) ↔ x ∈ H) :
      IsHoledDiscUnion (cell Z γ δ ∩ {x | x.1.toValuativeRel.vle
        (Polynomial.eval₂RingHom C T f) (Polynomial.eval₂RingHom C T g)}) := by
    convert hH using 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact and_congr_right fun hx ↦ (vle_iff_of_mem_cell hx hZf hZg).trans (hiff x hx)
  have hcell := isHoledDiscUnion_cell Z γ δ
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · -- `m < n`: the inequality says `x(ρ) ≤ x(T - γ)` for `ρ ^ (n - m) = c / e`
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (c / e) (Nat.sub_pos_of_lt hmn)
    refine key _ (hcell.inter_setOf_vle γ ρ) fun x hx ↦ ?_
    rw [Set.mem_ofPred_eq, ← valuation_le_iff]
    by_cases h0 : x.1.valuation (T - C γ) = 0
    · -- here `m = 0` by coprimality, and `x(c) = 0 ↔ x(ρ) = 0`
      have hm : m = 0 := (card_filter_eq_zero_or_of_mem_cell hx h0 hfg).resolve_right
        (by omega)
      rw [hm, Nat.sub_zero] at hρ
      have hρc : ρ = 0 ↔ c = 0 := by
        rw [← pow_eq_zero_iff (by omega : n ≠ 0), hρ, div_eq_zero_iff, or_iff_left he]
      simp [h0, hm, zero_pow (by omega : n ≠ 0),
        closedPolydisc_valuation_weightedC_eq_zero_iff, hρc]
    · exact (valuation_pow_mul_le_iff hmn he hρ h0).1
  · -- `m = n`: the inequality says `‖c‖ ≤ ‖e‖`, independently of the point
    have hiff (x) (hx : x ∈ cell Z γ δ) : x.1.valuation (T - C γ) ^ m * x.1.valuation (C c) ≤
        x.1.valuation (T - C γ) ^ n * x.1.valuation (C e) ↔ ‖c‖ ≤ ‖e‖ := by
      rw [← hmn, ← closedPolydisc_valuation_weightedC_le_iff x]
      by_cases h0 : x.1.valuation (T - C γ) = 0
      · have hm : m = 0 := by
          rcases card_filter_eq_zero_or_of_mem_cell hx h0 hfg with h | h
          exacts [h, hmn.trans h]
        rw [hm, pow_zero, one_mul, one_mul]
      · exact mul_le_mul_iff_right₀ (pow_pos (zero_lt_iff.mpr h0) _)
    by_cases hce : ‖c‖ ≤ ‖e‖
    · exact key Set.univ (by rwa [Set.inter_univ]) fun x hx ↦ by simpa [hce] using hiff x hx
    · exact key ∅ (by rw [Set.inter_empty]; exact isHoledDiscUnion_empty)
        fun x hx ↦ by simpa [hce] using hiff x hx
  · -- `n < m`: the inequality says `x(T - γ) ≤ x(ρ)` for `ρ ^ (m - n) = e / c`
    by_cases hc : c = 0
    · refine key Set.univ (by rwa [Set.inter_univ]) fun x _ ↦ ?_
      simp [hc]
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (e / c) (Nat.sub_pos_of_lt hmn)
    refine key _ (hcell.inter_closedSubdisc γ ρ) fun x hx ↦ ?_
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega), eq_comm, div_eq_zero_iff] at hρ
      exact hρ.elim he hc
    rw [mem_closedSubdisc, ← valuation_le_iff, and_iff_left (by
      rwa [← map_zero C, closedPolydisc_vle_weightedC_iff, norm_zero, not_le, norm_pos_iff])]
    by_cases h0 : x.1.valuation (T - C γ) = 0
    · simp only [h0, zero_le, zero_pow (by omega : m ≠ 0), zero_mul]
    · exact (valuation_pow_mul_le_iff hmn hc hρ h0).2

/-- **The domain `{x : x(f) ≤ x(g)}` of two coprime polynomials is a finite union of holed
discs.** Let `K` be algebraically closed and `f`, `g` coprime polynomials over `K`. Then there is
a finite set `P` of triples `(a, c, H)`, with `H` a finite set of pairs `(b, d)`, such that a point
of the closed unit disc satisfies `x(f) ≤ x(g)` exactly when, for some `(a, c, H) ∈ P`, it lies in
the holed disc `D(a, |c|) ∖ ⋃_{(b, d) ∈ H} D⁻(b, |d|)`. -/
theorem exists_finset_setOf_vle_eq_iUnion_holedDisc [IsAlgClosed K]
    {f g : Polynomial K} (hfg : IsCoprime f g) :
    ∃ P : Finset (K × K × Finset (K × K)),
      {x : closedPolydisc 1 K | x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T f)
        (Polynomial.eval₂RingHom C T g)} =
        ⋃ p ∈ P, holedDisc p.1 p.2.1 (fun q : p.2.2 ↦ q.1.1) (fun q ↦ q.1.2) := by
  classical
  suffices h : IsHoledDiscUnion {x : closedPolydisc 1 K | x.1.toValuativeRel.vle
      (Polynomial.eval₂RingHom C T f) (Polynomial.eval₂RingHom C T g)} from
    isHoledDiscUnion_iff.mp h
  rcases eq_or_ne g 0 with rfl | hg
  · -- `f` is a unit, hence a nonzero constant, and no point has `x(f) ≤ 0`
    obtain ⟨u, hu, rfl⟩ := Polynomial.isUnit_iff.mp (isCoprime_zero_right.mp hfg)
    convert isHoledDiscUnion_empty using 1
    refine Set.eq_empty_of_forall_notMem fun x hx ↦ hu.ne_zero ?_
    rw [Set.mem_ofPred_eq, map_zero, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      ← map_zero C, closedPolydisc_vle_weightedC_iff, norm_zero, norm_le_zero_iff] at hx
    exact hx
  set Z : Finset K := insert 0 (f.roots.toFinset ∪ g.roots.toFinset)
  have hZf : ∀ α ∈ f.roots, α ∈ Z := fun α hα ↦ by simp [Z, hα]
  have hZg : ∀ α ∈ g.roots, α ∈ Z := fun α hα ↦ by simp [Z, hα]
  have hcover : {x : closedPolydisc 1 K | x.1.toValuativeRel.vle
      (Polynomial.eval₂RingHom C T f) (Polynomial.eval₂RingHom C T g)} =
      ⋃ γ ∈ Z, ⋃ δ ∈ Z, cell Z γ δ ∩ {x | x.1.toValuativeRel.vle
        (Polynomial.eval₂RingHom C T f) (Polynomial.eval₂RingHom C T g)} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨γ, hγ, δ, hδ, h⟩ := exists_mem_cell (Finset.insert_nonempty _ _) x
      exact ⟨γ, hγ, δ, hδ, h, hx⟩
    · rintro ⟨-, -, -, -, -, hx⟩
      exact hx
  rw [hcover]
  exact isHoledDiscUnion_biUnion _ fun γ _ ↦ isHoledDiscUnion_biUnion _ fun δ _ ↦
    isHoledDiscUnion_cell_inter hfg hg hZf hZg γ δ

/-! ### Rational subsets of the closed disc -/

omit [IsUltrametricDist K] in
/-- Cancelling `gcd(g, p)` does not change the inequality `x(g) ≤ x(p)` at a point where
`x(gcd(g, p)) ≠ 0`. -/
private theorem vle_iff_vle_div_gcd [DecidableEq K] {x : closedPolydisc 1 K} {g p : Polynomial K}
    (hp : p ≠ 0) (hx : x.1.valuation (Polynomial.eval₂RingHom C T (gcd g p)) ≠ 0) :
    x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T g) (Polynomial.eval₂RingHom C T p) ↔
      x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T (g / gcd g p))
        (Polynomial.eval₂RingHom C T (p / gcd g p)) := by
  have hh : gcd g p ≠ 0 := fun h0 ↦ hp ((gcd_eq_zero_iff g p).mp h0).2
  have key : x.1.valuation (Polynomial.eval₂RingHom C T (gcd g p * (g / gcd g p))) ≤
        x.1.valuation (Polynomial.eval₂RingHom C T (gcd g p * (p / gcd g p))) ↔
      x.1.valuation (Polynomial.eval₂RingHom C T (g / gcd g p)) ≤
        x.1.valuation (Polynomial.eval₂RingHom C T (p / gcd g p)) := by
    simp only [map_mul]
    exact mul_le_mul_iff_right₀ (zero_lt_iff.mpr hx)
  rwa [EuclideanDomain.mul_div_cancel' hh (gcd_dvd_left g p),
    EuclideanDomain.mul_div_cancel' hh (gcd_dvd_right g p), valuation_le_iff,
    valuation_le_iff] at key

/-- Let `G` be a finite set of polynomials containing a nonzero constant `c`, and `p ≠ 0`. The
points with `x(g) ≤ x(p)` for all `g ∈ G` and `x(p) ≠ 0` are those with `x(g') ≤ x(p')` for all
`g ∈ G`, where `g' = g / gcd(g, p)` and `p' = p / gcd(g, p)` are coprime. The constant `c` forces
`x(p) ≠ 0` on both sides, and there the common factor `gcd(g, p)` cancels. -/
private theorem setOf_forall_vle_eq_iInter_div_gcd [DecidableEq K] {G : Finset (Polynomial K)}
    {p : Polynomial K} {c : K} (hc : c ≠ 0) (hcG : Polynomial.C c ∈ G) (hp : p ≠ 0) :
    {x : closedPolydisc 1 K | (∀ g ∈ G, x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T g)
        (Polynomial.eval₂RingHom C T p)) ∧
      ¬ x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T p) 0} =
      ⋂ g ∈ G, {x : closedPolydisc 1 K | x.1.toValuativeRel.vle
        (Polynomial.eval₂RingHom C T (g / gcd g p))
        (Polynomial.eval₂RingHom C T (p / gcd g p))} := by
  ext x
  have hp0 : ¬ x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T p) 0 ↔
      x.1.valuation (Polynomial.eval₂RingHom C T p) ≠ 0 := by
    rw [Ne, ← le_zero_iff, ← map_zero x.1.valuation, valuation_le_iff]
  -- a divisor of a polynomial with nonzero value has nonzero value
  have hdvd {f h : Polynomial K} (hhf : h ∣ f)
      (hf : x.1.valuation (Polynomial.eval₂RingHom C T f) ≠ 0) :
      x.1.valuation (Polynomial.eval₂RingHom C T h) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hf (map_dvd _ (map_dvd _ hhf))
  rw [Set.mem_ofPred_eq, Set.mem_iInter₂, hp0]
  refine ⟨fun ⟨hG, hx⟩ g hg ↦
    (vle_iff_vle_div_gcd hp (hdvd (gcd_dvd_right g p) hx)).mp (hG g hg), fun hG ↦ ?_⟩
  -- the constant `c` has nonzero value, and `x(c) ≤ x(p)` then gives `x(p) ≠ 0`
  have hcx : x.1.valuation (Polynomial.eval₂RingHom C T (Polynomial.C c)) ≠ 0 := by
    rwa [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Ne,
      closedPolydisc_valuation_weightedC_eq_zero_iff]
  have hcp := (vle_iff_vle_div_gcd hp (hdvd (gcd_dvd_left _ p) hcx)).mpr (hG _ hcG)
  have hx : x.1.valuation (Polynomial.eval₂RingHom C T p) ≠ 0 :=
    fun h0 ↦ hcx (le_zero_iff.mp (h0 ▸ (valuation_le_iff _ _ _).mpr hcp))
  exact ⟨fun g hg ↦ (vle_iff_vle_div_gcd hp (hdvd (gcd_dvd_right g p) hx)).mpr (hG g hg), hx⟩

/-- **Every rational subset of the closed unit disc is a finite union of holed discs.** Let `K`
be algebraically closed and a Tate ring, as is every algebraically closed field with a nontrivial
ultrametric norm. Then for every rational subset `U` of the closed unit disc
`Spa (K⟨T⟩, K⟨T⟩°)` there is a finite set `P` of triples `(a, c, H)`, with `H` a finite set of
pairs `(b, d)`, such that `U` is the union over `P` of the holed discs `holedDisc a c b d`: the
closed disc `D(a, |c|)` with the open disc of radius `‖d‖` about `b` removed for every
`(b, d) ∈ H`. -/
theorem exists_finset_eq_iUnion_holedDisc_of_mem_spaRationalFamily
    [IsTateRing K] [IsAlgClosed K] {U : Set (closedPolydisc 1 K)}
    (hU : (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹' U ∈
      spaRationalFamily (powerBoundedSubring (𝒯 K))) :
    ∃ P : Finset (K × K × Finset (K × K)),
      U = ⋃ p ∈ P, holedDisc p.1 p.2.1 (fun q : p.2.2 ↦ q.1.1) (fun q : p.2.2 ↦ q.1.2) := by
  classical
  suffices h : IsHoledDiscUnion U from isHoledDiscUnion_iff.mp h
  -- present `U` by polynomials, with a unit constant `c` among the numerators
  obtain ⟨G, p, c, hc, hcG, hV⟩ := (mem_spaRationalFamily_iff_exists_polynomial _).mp hU
  have hU' : U = {x : closedPolydisc 1 K | (∀ g ∈ G, x.1.toValuativeRel.vle
      (Polynomial.eval₂RingHom C T g) (Polynomial.eval₂RingHom C T p)) ∧
      ¬ x.1.toValuativeRel.vle (Polynomial.eval₂RingHom C T p) 0} := by
    ext x
    have hx := Set.ext_iff.mp hV (Homeomorph.setCongr (closedPolydisc_def 1 K) x)
    simp only [Set.mem_preimage, Homeomorph.setCongr_apply, TauCeti.Homeomorph.setCongr_symm_apply,
      mem_rationalSubset_iff, Finset.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hx
    have hv : x.1 ∈ spa (powerBoundedSubring (𝒯 K)) := closedPolydisc_def 1 K ▸ x.2
    exact hx.trans (and_iff_right hv)
  rcases eq_or_ne p 0 with rfl | hp
  · -- no point has `x(0) ≠ 0`
    convert isHoledDiscUnion_empty using 1
    rw [hU', map_zero]
    exact Set.eq_empty_of_forall_notMem fun x hx ↦ hx.2 (x.1.toValuativeRel.vle_refl 0)
  -- after cancelling common factors, each inequality is between coprime polynomials
  rw [hU', setOf_forall_vle_eq_iInter_div_gcd hc.ne_zero hcG hp]
  exact isHoledDiscUnion_biInter G fun g _ ↦ isHoledDiscUnion_iff.mpr
    (exists_finset_setOf_vle_eq_iUnion_holedDisc (isCoprime_div_gcd_div_gcd hp))

/-- **The rational subsets of the closed unit disc are exactly the finite unions of holed discs**,
over an algebraically closed nontrivially normed ultrametric field. The forward direction is
`exists_finset_eq_iUnion_holedDisc_of_mem_spaRationalFamily` and the converse is
`IsHoledDiscUnion.mem_spaRationalFamily`. -/
theorem mem_spaRationalFamily_iff_isHoledDiscUnion {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] [NonarchimedeanRing K] [IsAlgClosed K] {U : Set (closedPolydisc 1 K)} :
    (Homeomorph.setCongr (closedPolydisc_def 1 K)).symm ⁻¹' U ∈
      spaRationalFamily (powerBoundedSubring (𝒯 K)) ↔ IsHoledDiscUnion U :=
  ⟨fun hU ↦ isHoledDiscUnion_iff.mpr
      (exists_finset_eq_iUnion_holedDisc_of_mem_spaRationalFamily hU),
    IsHoledDiscUnion.mem_spaRationalFamily⟩

end TauCeti.ValuationSpectrum
