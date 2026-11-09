/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.NumberTheory.NewtonPolygon.Mul
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
import TauCeti.RingTheory.PowerSeries.RootBound

/-!
# Newton slopes, root valuations, and root norms

Let `v` be a real additive valuation for which only zero has infinite valuation. If a polynomial
`f` splits into linear factors, its finite slope multiset `Polynomial.newtonSlopes f v` is the
image of its multiset of nonzero roots under `α ↦ -v α`. This is the identification of the
slopes of the Newton polygon with the negatives of the root valuations. The root zero, with
multiplicity the order of vanishing of `f` at zero, contributes no slope.

The proof reads the slopes off the factorisation `f = c * ∏ (X - α)`: the slopes of a product
are the slopes of the factors together, and `X - α` has the single slope `-v α` when `α ≠ 0`
and no slope when `α = 0`. No completeness of the valuation is used. Applied after an extension
of coefficients compatible with the valuations, this gives the slopes of a polynomial in terms
of its roots in any valued extension in which it splits.

When `v` comes from an absolute value with `‖x‖ = b ^ (-v x)` for a base `1 < b`, the root `α`
has norm `b ^ m` exactly when `-v α = m`. Hence the endpoints of the finite face of slope `σ`
count the roots, with multiplicity and including the root zero, in the open and closed balls of
radius `b ^ σ`, and the width of the face counts those on the sphere of that radius. Moreover,
over an ultrametric normed field, every root of a nonzero pure polynomial of slope `m` in any
normed field extension has norm at most `b ^ m`, and every nonzero root has norm `b ^ m`, without
assuming that the polynomial splits.

## Main results

* `Polynomial.newtonSlopes_multiset_prod_X_sub_C`: the finite slopes of `∏ (X - α)` are the
  negated valuations of the nonzero `α`.
* `Polynomial.newtonSlopes_eq_map_roots`: the finite slopes of a split polynomial are the
  negated valuations of its nonzero roots.
* `Polynomial.newtonSlopes_eq_map_roots_map`: the same in a valued extension in which the
  polynomial splits.
* `Polynomial.newtonSlopes_eq_replicate`: if all nonzero roots have the same valuation `-m`,
  every finite slope equals `m`.
* `Polynomial.neg_untop₀_mem_newtonSlopes_of_isRoot`: the negated valuation of any nonzero root is
  a finite slope, without assuming that the polynomial splits.
* `Polynomial.addValuation_eq_neg_of_forall_mem_newtonSlopes_eq`: if every finite slope equals
  `q`, every nonzero root in a valued extension has valuation `-q`.
* `Polynomial.card_filter_roots_lt_addValuation`,
  `Polynomial.card_filter_roots_le_addValuation` and
  `Polynomial.card_filter_roots_addValuation_eq`: the left endpoint, the right endpoint and
  the width of the finite face of slope `σ` count the roots `α` with `-σ < v α`, with
  `-σ ≤ v α` and with `v α = -σ`.
* `Polynomial.norm_le_rpow_of_forall_mem_newtonSlopes_eq` and
  `Polynomial.norm_eq_rpow_of_forall_mem_newtonSlopes_eq`: over an ultrametric normed field,
  every root of a nonzero pure polynomial of slope `m` in any normed field extension has norm at
  most `b ^ m`, and every nonzero root has norm `b ^ m`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3, Lemma 4.
* K. S. Kedlaya, [*Newton polygons*](https://kskedlaya.org/18.787/newton-poly.pdf),
  MIT 18.787, fall 2007, §1. Kedlaya plots coefficient points at negative indices; our
  convention uses positive indices, so the slopes have the opposite sign.
-/

public section

open scoped PowerSeries
open TauCeti

namespace Polynomial

section AddValuation

variable {R : Type*} [CommRing R] {v : AddValuation R (WithTop ℝ)}

/-- If only zero has infinite valuation, the finite slopes of `∏ (X - α)`, over a multiset of
elements `α`, are the negated valuations `-v α` of the nonzero `α`, with multiplicity. -/
theorem newtonSlopes_multiset_prod_X_sub_C [DecidableEq R] (hv : ∀ x, v x = ⊤ → x = 0)
    (s : Multiset R) :
    (s.map (X - C ·)).prod.newtonSlopes v =
      (s.filter (· ≠ 0)).map fun α => -(v α).untop₀ := by
  induction s using Multiset.induction_on with
  | empty => simpa using newtonSlopes_C v (1 : R)
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons,
      newtonSlopes_mul _ _ v ((monic_X_sub_C a).newtonPolygon_ne_top v)
        ((monic_multiset_prod_of_monic _ _ fun α _ => monic_X_sub_C α).newtonPolygon_ne_top v),
      ih]
    by_cases ha : a = 0
    · simp [ha, ← monomial_one_one_eq_X]
    · simp [newtonSlopes_X_sub_C v (mt (hv a) ha), ha, Multiset.singleton_add]

/-- If only zero has infinite valuation, the negated valuation `-v α` of a nonzero root `α` of a
nonzero polynomial is one of its finite slopes. The polynomial need not split. -/
theorem neg_untop₀_mem_newtonSlopes_of_isRoot (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]} (hf : f ≠ 0)
    {α : R} (hα : α ≠ 0) (hroot : f.IsRoot α) : -(v α).untop₀ ∈ f.newtonSlopes v := by
  have hle :=
    newtonSlopes_le_of_dvd (newtonPolygon_ne_top_of_ne_zero hv hf) (dvd_iff_isRoot.mpr hroot)
  rw [newtonSlopes_X_sub_C v (mt (hv α) hα)] at hle
  exact Multiset.singleton_le.mp hle

/-- If every finite slope of `f` equals `q`, then every nonzero root `α` of `f` in a valued
extension `L` whose valuation `w` restricts to `v` has valuation `w α = -q`. Only zero may have
infinite valuation in `L`, and `f` need not split there. -/
theorem addValuation_eq_neg_of_forall_mem_newtonSlopes_eq {K L : Type*} [Ring K] [CommRing L]
    {v : AddValuation K (WithTop ℝ)} {w : AddValuation L (WithTop ℝ)}
    (hw : ∀ x, w x = ⊤ → x = 0) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x) {f : K[X]}
    (hf : f.map φ ≠ 0) {q : ℝ} (hq : ∀ m ∈ f.newtonSlopes v, m = q) {α : L} (hα : α ≠ 0)
    (hroot : (f.map φ).IsRoot α) : w α = ((-q : ℝ) : WithTop ℝ) := by
  have hmem := neg_untop₀_mem_newtonSlopes_of_isRoot hw hf hα hroot
  rw [newtonSlopes_map f v φ hφ] at hmem
  rw [← WithTop.coe_untop₀_of_ne_top (mt (hw α) hα), ← hq _ hmem, neg_neg]

variable [IsDomain R]

/-- If only zero has infinite valuation, the finite slopes of a split polynomial are the negated
valuations `-v α` of its nonzero roots `α`, with multiplicity. The root zero contributes no
slope. -/
theorem newtonSlopes_eq_map_roots [DecidableEq R] (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]}
    (hf : f.Splits) :
    f.newtonSlopes v = (f.roots.filter (· ≠ 0)).map fun α => -(v α).untop₀ := by
  rcases eq_or_ne f 0 with rfl | hf₀
  · simp
  conv_lhs => rw [hf.eq_prod_roots]
  rw [newtonSlopes_C_mul _ v (mt (hv _) (leadingCoeff_ne_zero.mpr hf₀)),
    newtonSlopes_multiset_prod_X_sub_C hv]

/-- If `f` splits over a valued extension `L` whose valuation `w` restricts to `v`, and only
zero has infinite valuation in `L`, the finite slopes of `f` are the negated valuations `-w α`
of its nonzero roots `α` in `L`, with multiplicity. -/
theorem newtonSlopes_eq_map_roots_map {K L : Type*} [Ring K] [CommRing L] [IsDomain L]
    [DecidableEq L] {v : AddValuation K (WithTop ℝ)} {w : AddValuation L (WithTop ℝ)}
    (hw : ∀ x, w x = ⊤ → x = 0) (φ : K →+* L) (hφ : ∀ x, w (φ x) = v x) {f : K[X]}
    (hf : (f.map φ).Splits) :
    f.newtonSlopes v = ((f.map φ).roots.filter (· ≠ 0)).map fun α => -(w α).untop₀ := by
  rw [← newtonSlopes_map f v φ hφ, newtonSlopes_eq_map_roots hw hf]

/-- If only zero has infinite valuation and all nonzero roots of a split polynomial have the
same valuation `-m`, then every finite slope equals `m`: a polynomial of degree `d` and order of
vanishing `a` at zero has the slope `m` with multiplicity `d - a`. -/
theorem newtonSlopes_eq_replicate (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]} (hf : f.Splits)
    {m : ℝ} (hm : ∀ α ∈ f.roots, α ≠ 0 → v α = ((-m : ℝ) : WithTop ℝ)) :
    f.newtonSlopes v = Multiset.replicate (f.natDegree - f.natTrailingDegree) m := by
  classical
  rw [← card_newtonSlopes f v hv, Multiset.eq_replicate_card, newtonSlopes_eq_map_roots hv hf]
  intro b hb
  obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.mp hb
  rw [Multiset.mem_filter] at hα
  rw [hm α hα.1 hα.2, WithTop.untop₀_coe, neg_neg]

/-- Counting finite slopes in terms of roots: a predicate holds for a number of finite slopes
equal to the number of nonzero roots `α` for which it holds at `-v α`. -/
theorem card_filter_newtonSlopes_eq [DecidableEq R] (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]}
    (hf : f.Splits) (p : ℝ → Prop) [DecidablePred p] :
    ((f.newtonSlopes v).filter p).card =
      (f.roots.filter fun α => α ≠ 0 ∧ p (-(v α).untop₀)).card := by
  rw [newtonSlopes_eq_map_roots hv hf, Multiset.filter_map, Multiset.card_map,
    Multiset.filter_filter]
  exact congrArg _ (Multiset.filter_congr fun _ _ => and_comm)

/-- If only zero has infinite valuation and `f` splits, the left endpoint of the finite face of
slope `σ` of the Newton polygon is the number of roots `α` with `-σ < v α`, counted with
multiplicity and including the root zero. For a valuation `‖x‖ = b ^ (-v x)` with `1 < b`, these
are the roots in the open ball of radius `b ^ σ`. -/
theorem card_filter_roots_lt_addValuation (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]}
    (hf : f.Splits) {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    (f.roots.filter fun α => ((-σ : ℝ) : WithTop ℝ) < v α).card = l := by
  classical
  rw [left_eq_natTrailingDegree_add_card_filter_newtonSlopes_lt hv hface,
    card_filter_newtonSlopes_eq hv hf, card_filter_roots_eq_natTrailingDegree_add f
      (by rw [v.map_zero]; exact WithTop.coe_lt_top _)]
  refine congrArg _ (congrArg _ (Multiset.filter_congr fun α _ => and_congr_right fun hα => ?_))
  rw [← WithTop.coe_untop₀_of_ne_top (mt (hv α) hα), WithTop.coe_lt_coe]
  exact neg_lt

/-- If only zero has infinite valuation and `f` splits, the right endpoint of the finite face of
slope `σ` of the Newton polygon is the number of roots `α` with `-σ ≤ v α`, counted with
multiplicity and including the root zero. For a valuation `‖x‖ = b ^ (-v x)` with `1 < b`, these
are the roots in the closed ball of radius `b ^ σ`. -/
theorem card_filter_roots_le_addValuation (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]}
    (hf : f.Splits) {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    (f.roots.filter fun α => ((-σ : ℝ) : WithTop ℝ) ≤ v α).card = u := by
  classical
  rw [right_eq_natTrailingDegree_add_card_filter_newtonSlopes_le hv hface,
    card_filter_newtonSlopes_eq hv hf, card_filter_roots_eq_natTrailingDegree_add f
      (by rw [v.map_zero]; exact le_top)]
  refine congrArg _ (congrArg _ (Multiset.filter_congr fun α _ => and_congr_right fun hα => ?_))
  rw [← WithTop.coe_untop₀_of_ne_top (mt (hv α) hα), WithTop.coe_le_coe]
  exact neg_le

/-- If only zero has infinite valuation and `f` splits, the width `u - l` of the finite face of
slope `σ` of the Newton polygon is the number of roots `α` with `v α = -σ`, counted with
multiplicity. For a valuation `‖x‖ = b ^ (-v x)` with `1 < b`, these are the roots on the sphere
of radius `b ^ σ`. -/
theorem card_filter_roots_addValuation_eq (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]}
    (hf : f.Splits) {σ : ℝ} {l u : ℕ} (hface : IsFiniteFace (f.newtonPolygon v) σ l u) :
    (f.roots.filter fun α => v α = ((-σ : ℝ) : WithTop ℝ)).card = u - l := by
  classical
  rw [← count_newtonSlopes_of_isFiniteFace hface, Multiset.count_eq_card_filter_eq,
    card_filter_newtonSlopes_eq hv hf]
  refine congrArg _ (Multiset.filter_congr fun α _ => ⟨fun h => ?_, ?_⟩)
  · have hα : α ≠ 0 := by
      rintro rfl
      rw [v.map_zero] at h
      exact WithTop.top_ne_coe h
    refine ⟨hα, ?_⟩
    rw [h, WithTop.untop₀_coe, neg_neg]
  · rintro ⟨hα, h⟩
    rw [← WithTop.coe_untop₀_of_ne_top (mt (hv α) hα), h, neg_neg]

end AddValuation

section RootNorm

variable {K L : Type*} [NormedField K] [IsUltrametricDist K]
  [NormedField L] [NormedAlgebra K L]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀))

include hb hv

/-- Every root `x` of a nonzero polynomial pure of slope `m`, in any normed field extension `L` of
`K`, satisfies `‖x‖ ≤ b ^ m`. -/
theorem norm_le_rpow_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {m : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m) {x : L} (hx : aeval x f = 0) : ‖x‖ ≤ b ^ m := by
  have : IsUltrametricDist L := .of_normedAlgebra K
  have hc : 0 < b ^ m := Real.rpow_pos_of_pos (zero_lt_one.trans hb) m
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  set P : K[X] := C f.leadingCoeff⁻¹ * f
  have hmonic : P.Monic := by
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  have hPd : TauCeti.PowerSeries.IsDistinguished (b ^ m) P.natDegree (P : K⟦X⟧) := by
    rw [hmonic.isDistinguished_iff_forall_mem_newtonSlopes_le v hb hv]
    intro s hs
    rw [newtonSlopes_C_mul f v (v.ne_top_iff.mpr (inv_ne_zero hlc))] at hs
    exact (hm s hs).le
  have hPdL : TauCeti.PowerSeries.IsDistinguished (b ^ m) P.natDegree
      (P.map (algebraMap K L) : L⟦X⟧) := by
    rw [polynomial_map_coe]
    exact hPd.map (algebraMap K L) (norm_algebraMap' L)
  have hroot : (P.map (algebraMap K L)).eval x = 0 := by
    rw [eval_map_algebraMap, map_mul, aeval_C, hx, mul_zero]
  exact hPdL.norm_le_of_eval_eq_zero hc
    ⟨hmonic.natDegree_map (algebraMap K L), hmonic.map (algebraMap K L)⟩ hroot

/-- Every nonzero root `x` of a nonzero polynomial pure of slope `m`, in any normed field extension
`L` of `K`, has norm `‖x‖ = b ^ m`. -/
theorem norm_eq_rpow_of_forall_mem_newtonSlopes_eq {f : K[X]} (hf : f ≠ 0) {m : ℝ}
    (hm : ∀ s ∈ f.newtonSlopes v, s = m) {x : L} (hx0 : x ≠ 0) (hx : aeval x f = 0) :
    ‖x‖ = b ^ m := by
  refine le_antisymm (norm_le_rpow_of_forall_mem_newtonSlopes_eq v hb hv hf hm hx) ?_
  have hrev0 : f.reverse ≠ 0 := reverse_eq_zero.not.mpr hf
  have hrev_slopes : ∀ s ∈ f.reverse.newtonSlopes v, s = -m := by
    intro s hs
    rw [newtonSlopes_reverse, Multiset.mem_map] at hs
    obtain ⟨t, ht, rfl⟩ := hs
    rw [hm t ht]
  have hrev_root : aeval x⁻¹ f.reverse = 0 := by
    rw [aeval_def, f.eval₂_inv_reverse_eq_zero_iff (algebraMap K L) hx0, ← aeval_def]
    exact hx
  have hinv := norm_le_rpow_of_forall_mem_newtonSlopes_eq v hb hv hrev0 hrev_slopes hrev_root
  rw [norm_inv, Real.rpow_neg (zero_lt_one.trans hb).le] at hinv
  exact (inv_le_inv₀ (norm_pos_iff.mpr hx0)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hb) m)).mp hinv

end RootNorm

end Polynomial
