/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Module.StrictGenerators
import TauCeti.Analysis.Normed.Ring.Approximation
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Finsupp.WellFounded

/-!
# Restricted power series over a Euclidean normed ring are noetherian

Let `R` be a complete ring whose norm is multiplicative and ultrametric, and let
`deg : R → ℕ` be a *Euclidean degree compatible with the norm*:

* `deg y = deg x` whenever `‖x - y‖ < ‖x‖`, so the degree only sees the leading part of an
  element;
* for `x ≠ 0`, every `y` can be written `y = z * x + w` with `‖w‖ ≤ ‖y‖` and either `w = 0` or
  `deg w < deg x`.

Then for every finite set of variables `σ` and all positive radii `c : σ → ℝ`, the ring
`R{T/c}` of restricted power series with the Gauss norm at the radii `c` is left noetherian
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`). This is Kedlaya's
analogue of the Hilbert basis theorem, stated for an abstract Euclidean normed ring. Kedlaya
proves it for the completion `A^r` of `W(𝒪_L)[[x] : x ∈ L]` for the Gauss norm `λ_r`, which is
Euclidean in this sense for the degree read off from its Newton polygon (his Remark 2.7 and
Proposition 2.9), and deduces that the rings `B^I` of the Fargues–Fontaine curve are strongly
noetherian. A complete nonarchimedean division ring satisfies the
hypotheses with `deg = 0`, so its Tate algebras at arbitrary radii are left noetherian
(`TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`).

The argument gives more than finite generation. Every left ideal `H` has finitely many nonzero
elements `x` such that each `y ∈ H` is a combination `∑ a x * x` with `‖a x‖ * ‖x‖ ≤ ‖y‖`
(`TauCeti.MvPowerSeries.exists_finset_eq_sum_mul_isRestricted_subring_of_division`): no
cancellation between the terms is needed to represent `y`. For Tate algebras at unit polyradius
the generators can be normalised to Gauss norm one, and the coefficients are then bounded by
`‖y‖` (`Ideal.exists_finset_norm_eq_one_isRestricted_subring`). In particular, the map
`(a x)ₓ ↦ ∑ a x * x` from the finite free module with the maximum norm onto `H` induces on `H`
its subspace topology, making `H` complete and hence closed
(`TauCeti.MvPowerSeries.isClosed_ideal_isRestricted_subring_of_division`).

Running the same Gröbner reduction on an arbitrary series `y` whenever `y` is strictly farther from
`0` than from `H` — using an element of `H` strictly closer to `y` than `‖y‖` to supply the divisor
at the leading index of `y` — shows that every left ideal is *strictly closed*: for every `y`, the
coset `y + H` has an element of minimal Gauss norm
(`TauCeti.MvPowerSeries.exists_norm_sub_le_isRestricted_subring_of_division`,
`Ideal.exists_norm_sub_le_isRestricted_subring`), even when the coefficient ring is not spherically
complete.

## Proof

The argument is a Gröbner-basis argument. Fix a monomial order on the exponents. The *leading
index* of a nonzero restricted series is the largest exponent, for the monomial order, at which
its weighted coefficient norm attains the Gauss norm. For an ideal `H`, the pairs (leading
index, degree of the leading coefficient) of the nonzero elements of `H` lie in the
well-quasi-ordered set `(σ →₀ ℕ) × ℕ` (Dickson's lemma). So finitely many elements of `H`
realise all the minimal pairs, and every nonzero element of `H` has a pair above one of theirs.

Fix `ε < 1` bounding, relative to the norm, the weighted coefficients of these finitely many
elements beyond their leading indices. Let `y` have `‖y‖ ≤ M` and `‖y‖ > θ ≥ ε M`, and suppose some
`h ∈ H` satisfies `‖y - h‖ < ‖y‖` (for instance `h = y` when `y ∈ H`). Then `h` shares the leading
index and leading-coefficient degree of `y`. A reduction step divides the leading coefficient of `y`
by the leading coefficient of a chosen `x`, shifted to the leading index of `y`. This replaces that
coefficient by a remainder of smaller degree or of weighted norm at most `θ`. It changes
coefficients at larger indices only by at most `ε M ≤ θ`, which by the compatibility of `deg` with
the norm keeps the degrees of the large ones. Recording, at each index, one more than the degree of
each coefficient of weighted norm above `θ`, reduction strictly decreases in the colexicographic
order. That order is well founded:

* for `y ∈ H` and `θ = ε ‖y‖`, after finitely many steps `y` is within `ε ‖y‖` of a combination
  `∑ b x * x` of the chosen elements with `‖b x‖ * ‖x‖ ≤ ‖y‖`; iterating gives a convergent
  expansion of `y` whose ultrametric coefficient bound survives
  (`TauCeti.exists_eq_sum_mul_of_approx`);
* for arbitrary `y` at positive distance `d` from `H` and `θ = max d (ε ‖y‖)`, finitely many steps
  produce `g ∈ H` with `‖y - g‖ ≤ max d (ε ‖y‖)`, and iterating until `εⁿ ‖y‖ ≤ d` attains `d`.

This follows Kedlaya's proof, with two reorganisations: Dickson's lemma is applied directly to
the pairs above instead of to Kedlaya's minimal leading degrees `d_I`, and his argument by
contradiction on an infinite reduction sequence is replaced by the well-founded potential.

## Main results

* `TauCeti.MvPowerSeries.exists_finset_eq_sum_mul_isRestricted_subring_of_division`: every left
  ideal of restricted power series over a complete ring with a multiplicative ultrametric norm
  and a compatible Euclidean degree has a finite strict generating system.
* `TauCeti.MvPowerSeries.isClosed_ideal_isRestricted_subring_of_division` and
  `TauCeti.MvPowerSeries.exists_norm_sub_le_isRestricted_subring_of_division`: every left ideal is
  closed and every coset contains an element of minimal Gauss norm.
* `Ideal.exists_finset_eq_sum_mul_isRestricted_subring`,
  `Ideal.exists_finset_norm_eq_one_isRestricted_subring`, and
  `Ideal.exists_norm_sub_le_isRestricted_subring`: the same for Tate algebras over a complete
  nonarchimedean division ring, with generators of Gauss norm one at unit polyradius.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`: restricted power
  series at arbitrary positive radii in finitely many variables over a complete ring with a
  multiplicative ultrametric norm and a compatible Euclidean degree form a left noetherian ring.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`: Tate algebras in finitely many
  variables at arbitrary positive radii over a complete nonarchimedean division ring are
  left noetherian.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Remark 2.7, Proposition 2.9, Theorem 3.2 and Lemmas 3.8–3.9.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, Theorem 1, and §5.2.7,
  Proposition 2.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter Topology

variable {σ R : Type*} [NormedRing R] [IsUltrametricDist R] {c : σ → ℝ}
  [∀ i, Fact (0 < c i)]

/-- `J` is the *leading index* of `f` for the monomial order `m`: the weighted coefficient norm
of `f` attains the Gauss norm at `J`, and at no exponent above `J`. -/
private def IsLeadingIndex (m : MonomialOrder σ) (f : IsRestricted.subring (R := R) c)
    (J : σ →₀ ℕ) : Prop :=
  ‖coeff J (f : MvPowerSeries σ R)‖ * J.prod (c · ^ ·) = ‖f‖ ∧
    ∀ J', m.toSyn J < m.toSyn J' → ‖coeff J' (f : MvPowerSeries σ R)‖ * J'.prod (c · ^ ·) < ‖f‖

/-- A nonzero restricted series has a leading index. -/
private theorem exists_isLeadingIndex (m : MonomialOrder σ)
    {f : IsRestricted.subring (R := R) c} (hf : f ≠ 0) : ∃ J, IsLeadingIndex m f J :=
  f.2.exists_achievesGaussNorm_max m fun h ↦ hf (Subtype.ext h)

/-- Perturbing `y` by strictly less than `‖y‖` preserves its norm, its leading index, and the
degree of its leading coefficient. -/
private theorem isLeadingIndex_of_norm_sub_lt (m : MonomialOrder σ) (deg : R → ℕ)
    (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    {y h : IsRestricted.subring (R := R) c} {J : σ →₀ ℕ} (hJ : IsLeadingIndex m y J)
    (hyh : ‖y - h‖ < ‖y‖) :
    h ≠ 0 ∧ IsLeadingIndex m h J ∧
      deg (coeff J (h : MvPowerSeries σ R)) = deg (coeff J (y : MvPowerSeries σ R)) := by
  have hnorm : ‖y‖ = ‖h‖ := IsUltrametricDist.norm_eq_of_norm_sub_lt_left hyh
  have hh0 : h ≠ 0 := norm_pos_iff.mp ((norm_nonneg (y - h)).trans_lt (hnorm ▸ hyh))
  have hdiff (t : σ →₀ ℕ) :
      ‖coeff t (y : MvPowerSeries σ R) - coeff t (h : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤
        ‖y - h‖ := by
    simpa [AddSubgroupClass.coe_sub, map_sub] using norm_coeff_mul_prod_le (y - h) t
  have hwJ := prod_pow_pos (c := c) J
  have hcJ : ‖coeff J (y : MvPowerSeries σ R) - coeff J (h : MvPowerSeries σ R)‖ <
      ‖coeff J (y : MvPowerSeries σ R)‖ :=
    lt_of_mul_lt_mul_right ((hdiff J).trans_lt (hyh.trans_eq hJ.1.symm)) hwJ.le
  refine ⟨hh0, ⟨?_, fun J' hJJ' ↦ ?_⟩, hdeg _ _ hcJ⟩
  · rw [← IsUltrametricDist.norm_eq_of_norm_sub_lt_left hcJ, hJ.1, hnorm]
  · have hwJ' := (prod_pow_pos (c := c) J').le
    have hsub := IsUltrametricDist.norm_sub_le_max (coeff J' (y : MvPowerSeries σ R))
      (coeff J' (y : MvPowerSeries σ R) - coeff J' (h : MvPowerSeries σ R))
    rw [sub_sub_cancel] at hsub
    calc ‖coeff J' (h : MvPowerSeries σ R)‖ * J'.prod (c · ^ ·)
        ≤ max (‖coeff J' (y : MvPowerSeries σ R)‖ * J'.prod (c · ^ ·))
            (‖coeff J' (y : MvPowerSeries σ R) - coeff J' (h : MvPowerSeries σ R)‖ *
              J'.prod (c · ^ ·)) := by
          rw [← max_mul_of_nonneg _ _ hwJ']
          exact mul_le_mul_of_nonneg_right hsub hwJ'
      _ < ‖h‖ := by
          rw [← hnorm]
          exact max_lt (hJ.2 J' hJJ') ((hdiff J').trans_lt hyh)

/-- **Finite Gröbner data.** Every ideal `H` contains finitely many nonzero elements such that
each nonzero `y ∈ H` with leading index `J` has one of them with leading index `I ≤ J` and leading
coefficient of degree at most that of `y`. -/
private theorem exists_finset_isLeadingIndex [Finite σ] (m : MonomialOrder σ) (deg : R → ℕ)
    (H : Ideal (IsRestricted.subring (R := R) c)) :
    ∃ F : Finset (IsRestricted.subring (R := R) c), (∀ x ∈ F, x ∈ H ∧ x ≠ 0) ∧
      ∀ y ∈ H, y ≠ 0 → ∀ J, IsLeadingIndex m y J → ∃ x ∈ F, ∃ I, IsLeadingIndex m x I ∧
        I ≤ J ∧ deg (coeff I (x : MvPowerSeries σ R)) ≤ deg (coeff J (y : MvPowerSeries σ R)) := by
  classical
  let P : Set ((σ →₀ ℕ) × ℕ) := {p | ∃ f ∈ H, f ≠ 0 ∧ IsLeadingIndex m f p.1 ∧
    deg (coeff p.1 (f : MvPowerSeries σ R)) = p.2}
  have hpwo : P.IsPWO := Set.isPWO_of_wellQuasiOrderedLE P
  have hfin : {p | Minimal (· ∈ P) p}.Finite :=
    (setOfPred_minimal_antichain _).finite_of_partiallyWellOrderedOn
      (hpwo.mono (setOfPred_minimal_subset _))
  choose! g hg using fun p (hp : p ∈ P) ↦ hp
  refine ⟨hfin.toFinset.image g, ?_, fun y hy hy0 J hJ ↦ ?_⟩
  · simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hg p hp.1).1, (hg p hp.1).2.1⟩
  · obtain ⟨p, hp, hpmin⟩ :=
      hpwo.exists_le_minimal (a := (J, deg (coeff J (y : MvPowerSeries σ R))))
        ⟨y, hy, hy0, hJ, rfl⟩
    obtain ⟨-, -, hpI, hpdeg⟩ := hg p hpmin.1
    exact ⟨g p, Finset.mem_image_of_mem _ (hfin.mem_toFinset.mpr hpmin), p.1, hpI, hp.1,
      hpdeg ▸ hp.2⟩

/-- **A uniform gap.** For finitely many restricted series there is `ε < 1` such that each of
their weighted coefficient norms smaller than the Gauss norm is at most `ε` times it. -/
private theorem exists_gap (F : Finset (IsRestricted.subring (R := R) c)) :
    ∃ ε, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ F, ∀ t,
      ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < ‖x‖ →
        ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε * ‖x‖ := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
  | insert x F _ ih =>
    obtain ⟨ε, hε0, hε1, hε⟩ := ih
    rcases eq_or_ne x 0 with rfl | hx
    · refine ⟨ε, hε0, hε1, fun y hy t ht ↦ ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact absurd ht (by simp)
      · exact hε y hy t ht
    obtain ⟨δ, hδ0, hδx, hδ⟩ := exists_norm_coeff_mul_prod_gap x hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    refine ⟨max ε (δ / ‖x‖), hε0.trans_le (le_max_left _ _),
      max_lt hε1 ((div_lt_one hxpos).mpr hδx), fun y hy t ht ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · calc _ ≤ δ := hδ t ht
        _ = δ / ‖y‖ * ‖y‖ := (div_mul_cancel₀ δ hxpos.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hxpos.le
    · exact (hε y hy t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- The reduction potential at threshold `θ > 0`: at each index (transported to the monomial
order), one more than the degree of the coefficient if its weighted norm exceeds `θ`, and `0`
otherwise. It has finite support because the series is restricted. -/
private noncomputable def potential (m : MonomialOrder σ) (deg : R → ℕ) {θ : ℝ} (hθ : 0 < θ)
    (y : IsRestricted.subring (R := R) c) : m.syn →₀ ℕ :=
  Finsupp.ofSupportFinite
    (fun s ↦ if θ < ‖coeff (m.toSyn.symm s) (y : MvPowerSeries σ R)‖ *
      (m.toSyn.symm s).prod (c · ^ ·) then deg (coeff (m.toSyn.symm s) (y : MvPowerSeries σ R)) + 1
      else 0) (by
    have hfin : {t | ¬ ‖coeff t (y : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < θ}.Finite :=
      y.2.eventually (gt_mem_nhds hθ)
    refine (hfin.image m.toSyn).subset fun s hs ↦ ⟨m.toSyn.symm s, fun h ↦ hs ?_, by simp⟩
    exact ite_eq_right h.not_gt)

omit [∀ i, Fact (0 < c i)] in
private theorem potential_apply (m : MonomialOrder σ) (deg : R → ℕ) {θ : ℝ} (hθ : 0 < θ)
    (y : IsRestricted.subring (R := R) c) (t : σ →₀ ℕ) :
    potential m deg hθ y (m.toSyn t) =
      if θ < ‖coeff t (y : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) then
        deg (coeff t (y : MvPowerSeries σ R)) + 1 else 0 := by
  rw [potential, Finsupp.ofSupportFinite_coe, AddEquiv.symm_apply_apply]

/-- A change of weighted norm at most `θ` in the coefficient at `t` leaves the potential entry at
`t` unchanged: by the ultrametric inequality, a coefficient above the threshold keeps its norm,
hence its degree, and one below the threshold stays below. -/
private theorem potential_apply_eq_of_le (m : MonomialOrder σ) (deg : R → ℕ)
    (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x) {θ : ℝ} (hθ : 0 < θ)
    {y y' : IsRestricted.subring (R := R) c} {t : σ →₀ ℕ}
    (h : ‖coeff t (y : MvPowerSeries σ R) - coeff t (y' : MvPowerSeries σ R)‖ *
      t.prod (c · ^ ·) ≤ θ) :
    potential m deg hθ y' (m.toSyn t) = potential m deg hθ y (m.toSyn t) := by
  have hw := (prod_pow_pos (c := c) t).le
  rw [potential_apply, potential_apply]
  set u := coeff t (y : MvPowerSeries σ R)
  set v := coeff t (y' : MvPowerSeries σ R)
  by_cases hu : θ < ‖u‖ * t.prod (c · ^ ·)
  · have huv : ‖u - v‖ < ‖u‖ := lt_of_mul_lt_mul_right (h.trans_lt hu) hw
    have hv : ‖u‖ ≤ ‖v‖ := (IsUltrametricDist.norm_eq_of_norm_sub_lt_left huv).le
    rw [ite_eq_left (hu.trans_le (mul_le_mul_of_nonneg_right hv hw)), ite_eq_left hu,
      hdeg u v huv]
  · have hv : ‖v‖ * t.prod (c · ^ ·) ≤ θ := by
      have := IsUltrametricDist.norm_sub_le_max u (u - v)
      rw [sub_sub_cancel] at this
      refine (mul_le_mul_of_nonneg_right this hw).trans ?_
      rw [max_mul_of_nonneg _ _ hw]
      exact max_le (not_lt.mp hu) h
    rw [ite_eq_right hv.not_gt, ite_eq_right hu]

variable [NormMulClass R]

/-- Above `K + I`, where `I` is a leading index of `x`, the monomial multiple `z X^K * x` has
weighted coefficient norms at most `ε` times its norm `‖z‖ ∏ i, c i ^ K i * ‖x‖`, provided the
weighted coefficient norms of `x` smaller than `‖x‖` are at most `ε ‖x‖`. -/
private theorem norm_coeff_monomial_mul_le (m : MonomialOrder σ)
    {x : IsRestricted.subring (R := R) c} {I : σ →₀ ℕ} (hI : IsLeadingIndex m x I) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ∀ t, ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < ‖x‖ →
      ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε * ‖x‖)
    (z : R) (K : σ →₀ ℕ) {t : σ →₀ ℕ} (ht : m.toSyn (K + I) < m.toSyn t) :
    ‖if K ≤ t then z * coeff (t - K) (x : MvPowerSeries σ R) else 0‖ * t.prod (c · ^ ·) ≤
      ε * (‖z‖ * K.prod (c · ^ ·) * ‖x‖) := by
  have hzK := mul_nonneg (norm_nonneg z) (prod_pow_pos (c := c) K).le
  split_ifs with hKt
  · have hlt : m.toSyn I < m.toSyn (t - K) := by
      by_contra! h
      have := add_le_add_right h (m.toSyn K)
      rw [← map_add, ← map_add, add_tsub_cancel_of_le hKt] at this
      exact ht.not_ge this
    calc ‖z * coeff (t - K) (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·)
        = ‖z‖ * K.prod (c · ^ ·) * (‖coeff (t - K) (x : MvPowerSeries σ R)‖ *
            (t - K).prod (c · ^ ·)) := by
          rw [norm_mul, ← tsub_add_cancel_of_le hKt, add_tsub_cancel_right, add_comm,
            prod_pow_add]
          ring
      _ ≤ ‖z‖ * K.prod (c · ^ ·) * (ε * ‖x‖) :=
          mul_le_mul_of_nonneg_left (hε _ (hI.2 _ hlt)) hzK
      _ = _ := by ring
  · simpa using mul_nonneg hε0 (mul_nonneg hzK (norm_nonneg x))

/-- **One reduction step**, from the proof of Kedlaya's Lemma 3.8. If `y` has `θ < ‖y‖ ≤ M` for a
threshold `θ ≥ ε M` and some `h ∈ H` satisfies `‖y - h‖ < ‖y‖`, subtracting a monomial multiple
`a * x` of a suitable `x ∈ F` keeps the norm at most `M`, with `‖a‖ * ‖x‖ ≤ M`, and strictly lowers
the reduction potential at threshold `θ`. -/
private theorem exists_reduction_step (m : MonomialOrder σ) (deg : R → ℕ)
    (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {H : Ideal (IsRestricted.subring (R := R) c)} {F : Finset (IsRestricted.subring (R := R) c)}
    (hF0 : ∀ x ∈ F, x ≠ 0)
    (hF : ∀ y ∈ H, y ≠ 0 → ∀ J, IsLeadingIndex m y J → ∃ x ∈ F, ∃ I, IsLeadingIndex m x I ∧
      I ≤ J ∧ deg (coeff I (x : MvPowerSeries σ R)) ≤ deg (coeff J (y : MvPowerSeries σ R)))
    {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ x ∈ F, ∀ t, ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < ‖x‖ →
      ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε * ‖x‖)
    {M θ : ℝ} (hθ : 0 < θ) (hεM : ε * M ≤ θ) {y : IsRestricted.subring (R := R) c}
    (hy : ∃ h ∈ H, ‖y - h‖ < ‖y‖) (hyM : ‖y‖ ≤ M) (hyθ : θ < ‖y‖) :
    ∃ x ∈ F, ∃ a, ‖a‖ * ‖x‖ ≤ M ∧ ‖y - a * x‖ ≤ M ∧
      toColex (potential m deg hθ (y - a * x)) < toColex (potential m deg hθ y) := by
  have hy0 : y ≠ 0 := norm_pos_iff.1 (hθ.trans hyθ)
  obtain ⟨J, hJ⟩ := exists_isLeadingIndex m hy0
  obtain ⟨h, hhH, hyh⟩ := hy
  obtain ⟨hh0, hJh, hdegh⟩ := isLeadingIndex_of_norm_sub_lt m deg hdeg hJ hyh
  obtain ⟨x, hxF, I, hI, hIJ, hdegI⟩ := hF h hhH hh0 J hJh
  rw [hdegh] at hdegI
  have hI₁ := hI.1
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr (hF0 x hxF)
  set cx := coeff I (x : MvPowerSeries σ R)
  have hc0 : cx ≠ 0 := fun h => hxpos.ne (by rw [← hI₁, h, norm_zero, zero_mul])
  obtain ⟨z, w, hzw, hwle, hwdeg⟩ := hdiv cx (coeff J (y : MvPowerSeries σ R)) hc0
  set K := J - I
  have hKI : K + I = J := tsub_add_cancel_of_le hIJ
  have hKJ : K ≤ J := tsub_le_self
  have hJK : J - K = I := tsub_tsub_cancel_of_le hIJ
  set a : IsRestricted.subring (R := R) c := ⟨monomial K z, isRestricted_monomial c K z⟩
    with ha_def
  have hna : ‖a‖ = ‖z‖ * K.prod (c · ^ ·) := norm_monomial K z
  have hcoeff (t : σ →₀ ℕ) : coeff t ((y - a * x : IsRestricted.subring (R := R) c) :
      MvPowerSeries σ R) = coeff t (y : MvPowerSeries σ R) -
        if K ≤ t then z * coeff (t - K) (x : MvPowerSeries σ R) else 0 := by
    rw [ha_def, AddSubgroupClass.coe_sub, map_sub, Subring.coe_mul, coeff_monomial_mul]
  -- The size `‖z * cx‖ wJ = ‖a‖ ‖x‖` of the subtracted multiple.
  have hax : ‖a‖ * ‖x‖ = ‖z * cx‖ * J.prod (c · ^ ·) := by
    rw [hna, ← hI₁, norm_mul, ← hKI, prod_pow_add]
    ring
  have hzc : ‖z * cx‖ ≤ ‖coeff J (y : MvPowerSeries σ R)‖ := by
    rw [eq_sub_of_add_eq hzw.symm]
    exact (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le le_rfl hwle)
  have haxM : ‖a‖ * ‖x‖ ≤ M := by
    rw [hax]
    exact (mul_le_mul_of_nonneg_right hzc (prod_pow_pos J).le).trans (hJ.1.le.trans hyM)
  refine ⟨x, hxF, a, haxM, ?_, ?_⟩
  · rw [← norm_mul] at haxM
    exact (IsUltrametricDist.norm_sub_le_max _ _).trans (max_le hyM haxM)
  rw [Finsupp.Colex.lt_iff]
  refine ⟨m.toSyn J, fun s hs ↦ ?_, ?_⟩
  · -- Above `J` the potential is unchanged: the subtracted coefficients have weighted norm
    -- at most `ε M ≤ θ`.
    obtain ⟨t, rfl⟩ := m.toSyn.surjective s
    simp only [ofColex_toColex]
    refine potential_apply_eq_of_le m deg hdeg hθ ?_
    rw [hcoeff, sub_sub_cancel]
    refine (norm_coeff_monomial_mul_le m hI hε0.le (hε x hxF) z K (by rwa [hKI])).trans ?_
    rw [← hna]
    exact (mul_le_mul_of_nonneg_left haxM hε0.le).trans hεM
  · -- At `J` it drops: the leading coefficient of `y` is replaced by the remainder `w`.
    have hwJ : coeff J ((y - a * x : IsRestricted.subring (R := R) c) : MvPowerSeries σ R) = w := by
      rw [hcoeff, ite_eq_left hKJ, hJK, hzw, add_sub_cancel_left]
    simp only [ofColex_toColex, potential_apply]
    rw [hwJ, ite_eq_left (hyθ.trans_eq hJ.1.symm)]
    split_ifs with hθw
    · rcases hwdeg with rfl | hwdeg
      · rw [norm_zero, zero_mul] at hθw
        exact absurd hθw hθ.le.not_gt
      · omega
    · omega

/-- **Approximation by the Gröbner data** (Kedlaya, Lemma 3.8). Every `y ∈ H` with `‖y‖ ≤ M` is
within `ε M` of a combination `∑ x ∈ F, b x * x` with `‖b x‖ * ‖x‖ ≤ M`. -/
private theorem exists_approx (m : MonomialOrder σ) (deg : R → ℕ)
    (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {H : Ideal (IsRestricted.subring (R := R) c)} {F : Finset (IsRestricted.subring (R := R) c)}
    (hFH : ∀ x ∈ F, x ∈ H ∧ x ≠ 0)
    (hF : ∀ y ∈ H, y ≠ 0 → ∀ J, IsLeadingIndex m y J → ∃ x ∈ F, ∃ I, IsLeadingIndex m x I ∧
      I ≤ J ∧ deg (coeff I (x : MvPowerSeries σ R)) ≤ deg (coeff J (y : MvPowerSeries σ R)))
    {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ x ∈ F, ∀ t, ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < ‖x‖ →
      ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε * ‖x‖)
    {M : ℝ} (hθ : 0 < ε * M) (y : IsRestricted.subring (R := R) c) :
    y ∈ H → ‖y‖ ≤ M → ∃ b : IsRestricted.subring (R := R) c → IsRestricted.subring (R := R) c,
      (∀ x ∈ F, ‖b x‖ * ‖x‖ ≤ M) ∧ ‖y - ∑ x ∈ F, b x * x‖ ≤ ε * M := by
  classical
  have hM : 0 ≤ M := (pos_of_mul_pos_right hθ hε0.le).le
  induction y using (InvImage.wf (fun y ↦ toColex (potential m deg hθ y)) wellFounded_lt).induction
    with
  | h y ih =>
    intro hy hyM
    by_cases hyθ : ‖y‖ ≤ ε * M
    · exact ⟨0, fun x _ ↦ by simpa using hM, by simpa using hyθ⟩
    have hypos : 0 < ‖y‖ := hθ.trans (not_le.mp hyθ)
    obtain ⟨x₀, hx₀, a, hax, hyaM, hlt⟩ := exists_reduction_step m deg hdeg hdiv
      (fun x hx ↦ (hFH x hx).2) hF hε0 hε hθ le_rfl ⟨y, hy, by simpa using hypos⟩ hyM
      (not_le.mp hyθ)
    obtain ⟨b, hb, hbε⟩ := ih (y - a * x₀) hlt (H.sub_mem hy (H.mul_mem_left a (hFH x₀ hx₀).1)) hyaM
    refine ⟨fun x ↦ b x + if x = x₀ then a else 0, fun x hx ↦ ?_, ?_⟩
    · refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _)
        (norm_nonneg x)).trans ?_
      rw [max_mul_of_nonneg _ _ (norm_nonneg x)]
      refine max_le (hb x hx) ?_
      split_ifs with h
      · exact h ▸ hax
      · simpa using hM
    · have : ∑ x ∈ F, (b x + if x = x₀ then a else 0) * x = ∑ x ∈ F, b x * x + a * x₀ := by
        simp [add_mul, Finset.sum_add_distrib, ite_mul, hx₀]
      rwa [this, ← sub_sub, sub_right_comm]

/-- **Coset reduction step.** If `y` has distance at most `d > 0` to `H`, well-founded reduction at
threshold `max d (ε ‖y‖)` brings `y` within `max d (ε ‖y‖)` of `H`. -/
private theorem exists_coset_step (m : MonomialOrder σ) (deg : R → ℕ)
    (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    {H : Ideal (IsRestricted.subring (R := R) c)} {F : Finset (IsRestricted.subring (R := R) c)}
    (hFH : ∀ x ∈ F, x ∈ H ∧ x ≠ 0)
    (hF : ∀ y ∈ H, y ≠ 0 → ∀ J, IsLeadingIndex m y J → ∃ x ∈ F, ∃ I, IsLeadingIndex m x I ∧
      I ≤ J ∧ deg (coeff I (x : MvPowerSeries σ R)) ≤ deg (coeff J (y : MvPowerSeries σ R)))
    {ε : ℝ} (hε0 : 0 < ε)
    (hε : ∀ x ∈ F, ∀ t, ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) < ‖x‖ →
      ‖coeff t (x : MvPowerSeries σ R)‖ * t.prod (c · ^ ·) ≤ ε * ‖x‖)
    {d : ℝ} (hd : 0 < d) (y : IsRestricted.subring (R := R) c)
    (hy : ∀ δ > d, ∃ h ∈ H, ‖y - h‖ < δ) :
    ∃ g ∈ H, ‖y - g‖ ≤ max d (ε * ‖y‖) := by
  set M := ‖y‖
  set θ := max d (ε * M)
  have hθ : 0 < θ := hd.trans_le (le_max_left _ _)
  suffices ∀ y' : IsRestricted.subring (R := R) c,
      (∀ δ > d, ∃ h ∈ H, ‖y' - h‖ < δ) → ‖y'‖ ≤ M → ∃ g ∈ H, ‖y' - g‖ ≤ θ from
    this y hy le_rfl
  intro y'
  induction y' using
    (InvImage.wf (fun y' ↦ toColex (potential m deg hθ y')) wellFounded_lt).induction with
  | h y' ih =>
    intro hy' hy'M
    by_cases hy'θ : ‖y'‖ ≤ θ
    · exact ⟨0, H.zero_mem, by simpa using hy'θ⟩
    have hy'lt : θ < ‖y'‖ := not_le.mp hy'θ
    obtain ⟨h₀, hh₀, hy'h₀⟩ := hy' ‖y'‖ ((le_max_left _ _).trans_lt hy'lt)
    obtain ⟨x₀, hx₀, a, -, hyaM, hlt⟩ := exists_reduction_step m deg hdeg hdiv
      (fun x hx ↦ (hFH x hx).2) hF hε0 hε hθ (le_max_right _ _) ⟨h₀, hh₀, hy'h₀⟩ hy'M hy'lt
    obtain ⟨g, hg, hgθ⟩ := ih (y' - a * x₀) hlt (fun δ hδ ↦ by
      obtain ⟨h, hh, hhδ⟩ := hy' δ hδ
      exact ⟨h - a * x₀, H.sub_mem hh (H.mul_mem_left a (hFH x₀ hx₀).1), by
        rwa [sub_sub_sub_cancel_right]⟩) hyaM
    refine ⟨g + a * x₀, H.add_mem hg (H.mul_mem_left a (hFH x₀ hx₀).1), ?_⟩
    rwa [add_comm, ← sub_sub]

/-- **Strict generators of ideals of restricted power series**, from the argument of Kedlaya's
Theorem 3.2 for an abstract Euclidean normed ring.
Let `R` be a complete ring with a multiplicative ultrametric norm, and `deg : R → ℕ`
a degree such that `deg y = deg x` whenever `‖x - y‖ < ‖x‖`, and such that for `x ≠ 0` every `y`
can be divided as `y = z * x + w` with `‖w‖ ≤ ‖y‖` and either `w = 0` or `deg w < deg x`. Then
for finitely many variables and all positive radii `c`, every left ideal `H` of the ring of
restricted power series has a finite set `F` of nonzero elements such that every `y ∈ H` is a
combination `∑ x ∈ F, a x * x` with `‖a x‖ * ‖x‖ ≤ ‖y‖`. In particular `F` generates `H`, and
`F` is empty when `H = ⊥`. -/
theorem exists_finset_eq_sum_mul_isRestricted_subring_of_division [CompleteSpace R]
    [Finite σ] (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    (H : Ideal (IsRestricted.subring (R := R) c)) :
    ∃ F : Finset (IsRestricted.subring (R := R) c), (∀ x ∈ F, x ∈ H ∧ x ≠ 0) ∧
      ∀ y ∈ H, ∃ a : IsRestricted.subring (R := R) c → IsRestricted.subring (R := R) c,
        y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ * ‖x‖ ≤ ‖y‖ := by
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  let m : MonomialOrder σ := MonomialOrder.lex
  obtain ⟨F, hFH, hF⟩ := exists_finset_isLeadingIndex m deg H
  obtain ⟨ε, hε0, hε1, hε⟩ := exists_gap F
  refine ⟨F, hFH, fun y hy ↦ TauCeti.exists_eq_sum_mul_of_approx (S := H) hε1 (fun y hy ↦ ?_) hy⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, fun x _ ↦ by simp, by simp, by simp⟩
  obtain ⟨b, hb, hbε⟩ :=
    exists_approx m deg hdeg hdiv hFH hF hε0 hε (mul_pos hε0 (norm_pos_iff.mpr hy0)) y hy le_rfl
  exact ⟨b, hb, H.sub_mem hy (H.sum_mem fun x hx ↦ H.mul_mem_left _ (hFH x hx).1), hbε⟩

/-- **Left ideals of restricted power series over a Euclidean normed ring are closed.** Under the
hypotheses of `exists_finset_eq_sum_mul_isRestricted_subring_of_division`, every left ideal `H` of
`IsRestricted.subring c` has a finite strict generating system and is therefore complete and closed
for the Gauss norm. -/
theorem isClosed_ideal_isRestricted_subring_of_division [CompleteSpace R] [Finite σ]
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    (H : Ideal (IsRestricted.subring (R := R) c)) :
    IsClosed (H : Set (IsRestricted.subring (R := R) c)) :=
  H.isClosed_of_exists_finset_eq_sum_smul (by
    simpa only [smul_eq_mul] using
      exists_finset_eq_sum_mul_isRestricted_subring_of_division deg hdeg hdiv H)

/-- **Least-norm coset representatives for ideals of restricted power series.** Under the
hypotheses of `exists_finset_eq_sum_mul_isRestricted_subring_of_division`, every left ideal `H` is
strictly closed: for every restricted series `y`, there is `h ∈ H` minimising `‖y - h‖` over `H`. -/
theorem exists_norm_sub_le_isRestricted_subring_of_division [CompleteSpace R] [Finite σ]
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x))
    (H : Ideal (IsRestricted.subring (R := R) c)) (y : IsRestricted.subring (R := R) c) :
    ∃ h ∈ H, ∀ h' ∈ H, ‖y - h‖ ≤ ‖y - h'‖ := by
  let S : Set ℝ := (fun h' ↦ ‖y - h'‖) '' (H : Set (IsRestricted.subring (R := R) c))
  have hSne : S.Nonempty := ⟨‖y - 0‖, 0, H.zero_mem, rfl⟩
  have hSbdd : BddBelow S := ⟨0, by rintro _ ⟨_, -, rfl⟩; exact norm_nonneg _⟩
  set d := sInf S
  have hd_le (h' : IsRestricted.subring (R := R) c) (hh' : h' ∈ H) : d ≤ ‖y - h'‖ :=
    csInf_le hSbdd ⟨h', hh', rfl⟩
  have hd_lt {δ : ℝ} (hδ : d < δ) : ∃ h' ∈ H, ‖y - h'‖ < δ := by
    obtain ⟨_, ⟨h', hh', rfl⟩, hh'δ⟩ := (csInf_lt_iff hSbdd hSne).mp hδ
    exact ⟨h', hh', hh'δ⟩
  have hd0 : 0 ≤ d := le_csInf hSne (by rintro _ ⟨_, -, rfl⟩; exact norm_nonneg _)
  rcases hd0.eq_or_lt with hd_eq | hd_pos
  · have hyH : y ∈ H := by
      refine (isClosed_ideal_isRestricted_subring_of_division deg hdeg hdiv H).closure_subset ?_
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨h', hh', hh'δ⟩ := hd_lt (hd_eq.symm.trans_lt hδ)
      exact ⟨h', hh', by rwa [dist_eq_norm]⟩
    exact ⟨y, hyH, fun _ _ ↦ by simp⟩
  · let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
    let m : MonomialOrder σ := MonomialOrder.lex
    obtain ⟨F, hFH, hF⟩ := exists_finset_isLeadingIndex m deg H
    obtain ⟨ε, hε0, hε1, hε⟩ := exists_gap F
    have hiter (n : ℕ) : ∃ g ∈ H, ‖y - g‖ ≤ max d (ε ^ n * ‖y‖) := by
      induction n with
      | zero => exact ⟨0, H.zero_mem, by simp⟩
      | succ n ih =>
        obtain ⟨g, hg, hgn⟩ := ih
        obtain ⟨g₁, hg₁, hg₁ε⟩ := exists_coset_step m deg hdeg hdiv hFH hF hε0 hε hd_pos (y - g)
          fun δ hδ ↦ by
            obtain ⟨h', hh', hh'δ⟩ := hd_lt hδ
            exact ⟨h' - g, H.sub_mem hh' hg, by rwa [sub_sub_sub_cancel_right]⟩
        refine ⟨g + g₁, H.add_mem hg hg₁, ?_⟩
        rw [← sub_sub]
        refine hg₁ε.trans (max_le (le_max_left _ _) ?_)
        calc ε * ‖y - g‖ ≤ ε * max d (ε ^ n * ‖y‖) := mul_le_mul_of_nonneg_left hgn hε0.le
          _ = max (ε * d) (ε * (ε ^ n * ‖y‖)) := mul_max_of_nonneg _ _ hε0.le
          _ ≤ max d (ε ^ (n + 1) * ‖y‖) := max_le
              ((mul_le_of_le_one_left hd_pos.le hε1.le).trans (le_max_left _ _))
              (by rw [pow_succ', mul_assoc]; exact le_max_right _ _)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hd_pos (by positivity : 0 < ‖y‖ + 1)) hε1
    obtain ⟨h, hh, hhn⟩ := hiter n
    have hεy : ε ^ n * ‖y‖ ≤ d := by
      calc ε ^ n * ‖y‖ ≤ ε ^ n * (‖y‖ + 1) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (pow_nonneg hε0.le n)
        _ ≤ d := ((lt_div_iff₀ (by positivity : 0 < ‖y‖ + 1)).mp hn).le
    exact ⟨h, hh, fun h' hh' ↦ (hhn.trans (max_le le_rfl hεy)).trans (hd_le h' hh')⟩

/-- **Kedlaya's Hilbert basis theorem for restricted power series**, the argument of Kedlaya's
Theorem 3.2 for an abstract Euclidean normed ring.
Let `R` be a complete ring with a multiplicative ultrametric norm, and `deg : R → ℕ`
a degree such that `deg y = deg x` whenever `‖x - y‖ < ‖x‖`, and such that for `x ≠ 0` every `y`
can be divided as `y = z * x + w` with `‖w‖ ≤ ‖y‖` and either `w = 0` or `deg w < deg x`. Then
for finitely many variables and all positive radii `c`, the ring of restricted power series
with its Gauss norm at the radii `c` is left noetherian. -/
theorem isNoetherianRing_isRestricted_subring_of_division [CompleteSpace R] [Finite σ]
    (deg : R → ℕ) (hdeg : ∀ x y : R, ‖x - y‖ < ‖x‖ → deg y = deg x)
    (hdiv : ∀ x y : R, x ≠ 0 → ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x)) :
    IsNoetherianRing (IsRestricted.subring (R := R) c) := by
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun H ↦ ?_
  obtain ⟨F, hFH, hF⟩ :=
    exists_finset_eq_sum_mul_isRestricted_subring_of_division deg hdeg hdiv H
  refine ⟨F, le_antisymm (Ideal.span_le.mpr fun x hx ↦ (hFH x hx).1) fun y hy ↦ ?_⟩
  obtain ⟨a, rfl, -⟩ := hF y hy
  exact _root_.sum_mem fun x hx ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span hx)

section DivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A division ring is Euclidean for every degree: division leaves no remainder. -/
private theorem exists_eq_mul_add_of_divisionRing {deg : K → ℕ} (x y : K) (hx : x ≠ 0) :
    ∃ z w, y = z * x + w ∧ ‖w‖ ≤ ‖y‖ ∧ (w = 0 ∨ deg w < deg x) :=
  ⟨y * x⁻¹, 0, by rw [add_zero, inv_mul_cancel_right₀ hx], by simp, Or.inl rfl⟩

/-- **Tate algebras are left noetherian.** Over a complete nonarchimedean division ring `K`,
the ring of restricted power series in finitely many variables at arbitrary positive radii `c` is
left noetherian: `K` satisfies the hypotheses of
`isNoetherianRing_isRestricted_subring_of_division` with the zero degree. -/
theorem isNoetherianRing_isRestricted_subring :
    IsNoetherianRing (IsRestricted.subring (R := K) c) :=
  isNoetherianRing_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing

/-- **Strict generators of ideals of Tate algebras.** Over a complete nonarchimedean division ring
`K`, in finitely many variables and at arbitrary positive radii `c`, every left ideal `H` of the
Tate algebra has a finite set `F` of nonzero elements such that every `y ∈ H` is a combination
`∑ x ∈ F, a x * x` with `‖a x‖ * ‖x‖ ≤ ‖y‖`. -/
theorem _root_.Ideal.exists_finset_eq_sum_mul_isRestricted_subring
    (H : Ideal (IsRestricted.subring (R := K) c)) :
    ∃ F : Finset (IsRestricted.subring (R := K) c), (∀ x ∈ F, x ∈ H ∧ x ≠ 0) ∧
      ∀ y ∈ H, ∃ a : IsRestricted.subring (R := K) c → IsRestricted.subring (R := K) c,
        y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ * ‖x‖ ≤ ‖y‖ :=
  exists_finset_eq_sum_mul_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing H

/-- **Strict generators of norm one.** Over a complete nonarchimedean division ring `K`, every
left ideal `H` of the Tate algebra `K⟨X⟩` at unit polyradius in finitely many variables has a
finite set `F` of generators of Gauss norm one such that every `y ∈ H` is a combination
`∑ x ∈ F, a x * x` with `‖a x‖ ≤ ‖y‖`. The set `F` is empty when `H = ⊥`. -/
theorem _root_.Ideal.exists_finset_norm_eq_one_isRestricted_subring
    (H : Ideal (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) :
    ∃ F : Finset (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)), (∀ x ∈ F, x ∈ H ∧ ‖x‖ = 1) ∧
      ∀ y ∈ H, ∃ a : IsRestricted.subring (R := K) (fun _ : σ ↦ 1) →
          IsRestricted.subring (R := K) (fun _ : σ ↦ 1),
        y = ∑ x ∈ F, a x * x ∧ ∀ x ∈ F, ‖a x‖ ≤ ‖y‖ := by
  simpa only [smul_eq_mul] using H.exists_finset_norm_eq_one_of_exists_finset_eq_sum_smul
    (fun _ _ hx ↦ exists_isUnit_and_norm_eq hx)
    (by simpa only [smul_eq_mul] using H.exists_finset_eq_sum_mul_isRestricted_subring)

/-- **Strict closedness of ideals of Tate algebras** ([Bosch, Güntzer, Remmert, *Non-Archimedean
Analysis*][bosch-guntzer-remmert], §5.2.7, Proposition 2). Over a complete nonarchimedean division
ring `K`, in finitely many variables and at arbitrary positive radii `c`, every left ideal `H` is
strictly closed: for every `y`, there is `h ∈ H` minimising `‖y - h‖` over `H`. -/
theorem _root_.Ideal.exists_norm_sub_le_isRestricted_subring
    (H : Ideal (IsRestricted.subring (R := K) c)) (y : IsRestricted.subring (R := K) c) :
    ∃ h ∈ H, ∀ h' ∈ H, ‖y - h‖ ≤ ‖y - h'‖ :=
  exists_norm_sub_le_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    exists_eq_mul_add_of_divisionRing H y

end DivisionRing

end TauCeti.MvPowerSeries
