/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Basic
import TauCeti.Analysis.Normed.Group.Ultra
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

## Proof

The argument is a Gröbner-basis argument. Fix a monomial order on the exponents. The *leading
index* of a nonzero restricted series is the largest exponent, for the monomial order, at which
its weighted coefficient norm attains the Gauss norm. For an ideal `H`, the pairs (leading
index, degree of the leading coefficient) of the nonzero elements of `H` lie in the
well-quasi-ordered set `(σ →₀ ℕ) × ℕ` (Dickson's lemma). So finitely many elements of `H`
realise all the minimal pairs, and every nonzero element of `H` has a pair above one of theirs.

Fix `ε < 1` bounding, relative to the norm, the weighted coefficients of these finitely many
elements beyond their leading indices. Let `y ∈ H` with `‖y‖ ≤ M` and `‖y‖ > ε M`. A reduction
step divides the leading coefficient of `y` by the leading coefficient of a chosen `x`, shifted
to the leading index of `y`. This replaces that coefficient by a remainder of smaller degree or
of weighted norm at most `ε M`. It changes coefficients at larger indices only by at most `ε M`,
which by the compatibility of `deg` with the norm keeps the degrees of the large ones.
Recording, at each index, one more than the degree of each coefficient of weighted norm above
`ε M`, reduction strictly decreases in the colexicographic order. That order is well founded,
so after finitely many steps `y` is within `ε ‖y‖` of a combination of the chosen elements with
coefficients bounded by `‖y‖`. Iterating gives a convergent expansion of `y`
(`Ideal.le_span_of_approx`).

This follows Kedlaya's proof, with two reorganisations: Dickson's lemma is applied directly to
the pairs above instead of to Kedlaya's minimal leading degrees `d_I`, and his argument by
contradiction on an infinite reduction sequence is replaced by the well-founded potential.

## Main results

* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring_of_division`: restricted power
  series at arbitrary positive radii in finitely many variables over a complete ring with a
  multiplicative ultrametric norm and a compatible Euclidean degree form a left noetherian ring.
* `TauCeti.MvPowerSeries.isNoetherianRing_isRestricted_subring`: Tate algebras in finitely many
  variables at arbitrary positive radii over a complete nonarchimedean division ring are
  left noetherian.

## References

* K. S. Kedlaya, *Noetherian properties of Fargues–Fontaine curves*, IMRN 2016, no. 8,
  2544–2567; arXiv:1410.5160v3, Remark 2.7, Proposition 2.9, Theorem 3.2 and Lemmas 3.8–3.9.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.6, Theorem 1.
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

/-- **One reduction step**, from the proof of Kedlaya's Lemma 3.8. If `y ∈ H` has
`ε M < ‖y‖ ≤ M`, subtracting a monomial multiple `a * x` of a suitable `x ∈ F` keeps the norm at
most `M`, with `‖a‖ * ‖x‖ ≤ M`, and strictly lowers the reduction potential at threshold `ε M`. -/
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
    {M : ℝ} (hθ : 0 < ε * M) {y : IsRestricted.subring (R := R) c} (hy : y ∈ H)
    (hyM : ‖y‖ ≤ M) (hyθ : ε * M < ‖y‖) :
    ∃ x ∈ F, ∃ a, ‖a‖ * ‖x‖ ≤ M ∧ ‖y - a * x‖ ≤ M ∧
      toColex (potential m deg hθ (y - a * x)) < toColex (potential m deg hθ y) := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact (hθ.trans (by simpa using hyθ)).false
  obtain ⟨J, hJ⟩ := exists_isLeadingIndex m hy0
  obtain ⟨x, hxF, I, hI, hIJ, hdegI⟩ := hF y hy hy0 J hJ
  have hI₁ := hI.1
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr (hF0 x hxF)
  set cx := coeff I (x : MvPowerSeries σ R)
  have hc0 : cx ≠ 0 := by
    rintro h
    rw [h, norm_zero, zero_mul] at hI₁
    exact hxpos.ne hI₁
  obtain ⟨z, w, hzw, hwle, hwdeg⟩ := hdiv cx (coeff J (y : MvPowerSeries σ R)) hc0
  set K := J - I
  have hKI : K + I = J := tsub_add_cancel_of_le hIJ
  have hKJ : K ≤ J := tsub_le_self
  have hJK : J - K = I := tsub_tsub_cancel_of_le hIJ
  obtain ⟨a, ha⟩ : ∃ a : IsRestricted.subring (R := R) c, (a : MvPowerSeries σ R) = monomial K z :=
    ⟨⟨_, isRestricted_monomial c K z⟩, rfl⟩
  have hna : ‖a‖ = ‖z‖ * K.prod (c · ^ ·) := by
    rw [← norm_monomial K z (c := c)]
    exact congrArg norm (Subtype.ext ha)
  -- The coefficients of the reduced series.
  have hcoeff (t : σ →₀ ℕ) : coeff t ((y - a * x : IsRestricted.subring (R := R) c) :
      MvPowerSeries σ R) = coeff t (y : MvPowerSeries σ R) -
        if K ≤ t then z * coeff (t - K) (x : MvPowerSeries σ R) else 0 := by
    rw [AddSubgroupClass.coe_sub, Subring.coe_mul, ha, map_sub, coeff_monomial_mul]
  -- The size `‖z * cx‖ wJ = ‖a‖ ‖x‖` of the subtracted multiple.
  have hax : ‖a‖ * ‖x‖ = ‖z * cx‖ * J.prod (c · ^ ·) := by
    rw [hna, ← hI₁, norm_mul, ← hKI, prod_pow_add]
    ring
  have hzc : ‖z * cx‖ ≤ ‖coeff J (y : MvPowerSeries σ R)‖ := by
    have : z * cx = coeff J (y : MvPowerSeries σ R) - w := by rw [hzw, add_sub_cancel_right]
    rw [this]
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
    -- at most `ε M`.
    obtain ⟨t, rfl⟩ := m.toSyn.surjective s
    simp only [ofColex_toColex]
    refine potential_apply_eq_of_le m deg hdeg hθ ?_
    rw [hcoeff, sub_sub_cancel]
    refine (norm_coeff_monomial_mul_le m hI hε0.le (hε x hxF) z K (by rwa [hKI])).trans ?_
    rw [← hna]
    exact mul_le_mul_of_nonneg_left haxM hε0.le
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
    obtain ⟨x₀, hx₀, a, hax, hyaM, hlt⟩ := exists_reduction_step m deg hdeg hdiv
      (fun x hx ↦ (hFH x hx).2) hF hε0 hε hθ hy hyM (not_le.mp hyθ)
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
  let _ : LinearOrder σ := LinearOrder.lift' (Finite.equivFin σ) (Finite.equivFin σ).injective
  let m : MonomialOrder σ := MonomialOrder.lex
  refine (isNoetherianRing_iff_ideal_fg _).mpr fun H ↦ ?_
  obtain ⟨F, hFH, hF⟩ := exists_finset_isLeadingIndex m deg H
  obtain ⟨ε, hε0, hε1, hε⟩ := exists_gap F
  refine ⟨F, le_antisymm (Ideal.span_le.mpr fun x hx ↦ (hFH x hx).1)
    (Ideal.le_span_of_approx (fun x hx ↦ (hFH x hx).1) hε0.le hε1 fun y hy ↦ ?_)⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact ⟨0, fun x _ ↦ by simp, by simp⟩
  exact exists_approx m deg hdeg hdiv hFH hF hε0 hε (mul_pos hε0 (norm_pos_iff.mpr hy0)) y hy le_rfl

/-- **Tate algebras are left noetherian.** Over a complete nonarchimedean division ring `K`,
the ring of restricted power series in finitely many variables at arbitrary positive radii `c` is
left noetherian: `K` satisfies the hypotheses of
`isNoetherianRing_isRestricted_subring_of_division` with the zero degree. -/
theorem isNoetherianRing_isRestricted_subring {K : Type*} [NormedDivisionRing K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ] :
    IsNoetherianRing (IsRestricted.subring (R := K) c) :=
  isNoetherianRing_isRestricted_subring_of_division (fun _ ↦ 0) (fun _ _ _ ↦ rfl)
    fun x y hx ↦ ⟨y * x⁻¹, 0, by rw [add_zero, inv_mul_cancel_right₀ hx], by simp, Or.inl rfl⟩

end TauCeti.MvPowerSeries
