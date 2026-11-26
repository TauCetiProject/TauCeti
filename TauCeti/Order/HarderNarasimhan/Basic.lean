/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.RelSeries
public import TauCeti.Order.Lattice.Submodular
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Linarith

/-!
# Harder–Narasimhan filtrations in a lattice with a rank and a degree

Let `L` be a lattice carrying a strictly monotone *rank* `rank : L → ℕ` that is modular,
`rank (a ⊔ b) + rank (a ⊓ b) = rank a + rank b`, and a *degree* `degree : L → 𝕜` with values in a
linearly ordered field that is supermodular,
`degree a + degree b ≤ degree (a ⊔ b) + degree (a ⊓ b)`. The basic example is the lattice of
saturated subbundles of a vector bundle `E` on a smooth projective curve: the join of two saturated
subbundles is the saturation of their sum, which can only raise the degree, and the rank is the
dimension of the generic fibre. The slope of an interval `[a, b]` with `a < b` is
`(degree b - degree a) / (rank b - rank a)`; the interval is semistable when no `c ∈ (a, b]` has
slope over `a` larger than the slope of `[a, b]`.

The Harder–Narasimhan theorem in this setting says that, provided the degree attains its maximum
on each rank level of every interval, every interval `[a, b]` has a unique chain
`a = a₀ < a₁ < ⋯ < a_k = b` whose successive intervals are semistable with strictly decreasing
slopes. The step `a₁` is the *maximal destabilizing* element of `[a, b]`: the greatest element of
`(a, b]` of maximal slope over `a`.

For vector bundles on a curve this is the classical Harder–Narasimhan filtration. Applied to the
degree shifted by the partial sums of a dominant tuple `T` (see
`TauCeti.RankDegree.shift`), it gives the canonical `T`-Harder–Narasimhan filtration used in the
truncation of automorphic forms and stacks of shtukas.

## Main definitions

* `TauCeti.RankDegree`: a modular strictly monotone rank and a supermodular degree on a lattice.
* `TauCeti.RankDegree.slope`: the slope of an interval.
* `TauCeti.RankDegree.Semistable`: semistability of an interval.
* `TauCeti.RankDegree.IsMaxDestabilizing`: the maximal destabilizing element of an interval.
* `TauCeti.RankDegree.IsHNSeries`: a series with semistable steps of strictly decreasing slopes.
* `TauCeti.RankDegree.DegreeMaxAttained`: the degree attains its maximum on each rank level of
  each interval.
* `TauCeti.RankDegree.DegreeMaxAttained.maxDestabilizing`: the maximal destabilizing element of an
  interval, when the degree attains its maximum on each rank level.
* `TauCeti.RankDegree.DegreeMaxAttained.hnSeries`: the Harder–Narasimhan series of an interval,
  when the degree attains its maximum on each rank level.
* `TauCeti.RankDegree.ofLinearOrder`: a strictly monotone rank and an arbitrary degree on a linear
  order.

## Main results

* `TauCeti.RankDegree.IsHNSeries.isMaxDestabilizing`: each step of a Harder–Narasimhan series is
  the maximal destabilizing element of the interval from the previous step to the end.
* `TauCeti.RankDegree.IsHNSeries.eq`: a Harder–Narasimhan series is determined by its endpoints.
* `TauCeti.RankDegree.DegreeMaxAttained.existsUnique_isHNSeries`: existence and uniqueness of the
  Harder–Narasimhan series of an interval.
* `TauCeti.RankDegree.IsHNSeries.eq_hnSeries`: every Harder–Narasimhan series is the one chosen by
  `TauCeti.RankDegree.DegreeMaxAttained.hnSeries`.
* `TauCeti.RankDegree.DegreeMaxAttained.hnSeries_one`: the first step of the Harder–Narasimhan
  series is the maximal destabilizing element.
* `TauCeti.RankDegree.IsHNSeries.length_eq_one_iff`: the series is trivial exactly when the
  interval is semistable.

## References

* G. Harder, M. S. Narasimhan, *On the cohomology groups of moduli spaces of vector bundles on
  curves*, Math. Ann. 212 (1975), 215–248.
* S. S. Shatz, *The decomposition and specialization of algebraic families of vector bundles*,
  Compositio Math. 35 (1977), §§1–3.
* Y. André, *Slope filtrations*, Confluentes Math. 1 (2009), §1.
-/

public section

namespace TauCeti

/-- A rank and a degree on a lattice: a strictly monotone modular rank function with values in
`ℕ` and a supermodular degree function with values in `𝕜`. Supermodularity of the degree is
recorded as submodularity of its negative. -/
@[ext]
structure RankDegree (L 𝕜 : Type*) [Lattice L] [Neg 𝕜] [Add 𝕜] [LE 𝕜] where
  /-- The rank. -/
  rank : L → ℕ
  /-- The degree. -/
  degree : L → 𝕜
  /-- The rank is strictly monotone. -/
  rank_strictMono : StrictMono rank
  /-- The rank is modular. -/
  rank_sup_add_rank_inf (a b : L) : rank (a ⊔ b) + rank (a ⊓ b) = rank a + rank b
  /-- The degree is supermodular. -/
  isSubmodular_neg_degree : IsSubmodular fun a ↦ -degree a

namespace RankDegree

variable {L 𝕜 : Type*} [Lattice L] [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable (D : RankDegree L 𝕜) {a b c d e x y z : L}

/-! ### Rank and degree -/

omit [IsStrictOrderedRing 𝕜] in
theorem rank_lt_rank (h : a < b) : D.rank a < D.rank b :=
  D.rank_strictMono h

omit [IsStrictOrderedRing 𝕜] in
theorem rank_le_rank (h : a ≤ b) : D.rank a ≤ D.rank b :=
  D.rank_strictMono.monotone h

omit [IsStrictOrderedRing 𝕜] in
/-- An element below another of at most its rank is equal to it. -/
theorem eq_of_le_of_rank_le (h : a ≤ b) (hr : D.rank b ≤ D.rank a) : a = b :=
  h.eq_of_not_lt fun hlt ↦ (D.rank_lt_rank hlt).not_ge hr

/-- The supermodular inequality for the degree. -/
theorem degree_add_degree_le (a b : L) :
    D.degree a + D.degree b ≤ D.degree (a ⊔ b) + D.degree (a ⊓ b) := by
  have := D.isSubmodular_neg_degree.apply a b
  linarith

theorem cast_rank_sup_add_cast_rank_inf (a b : L) :
    (D.rank (a ⊔ b) : 𝕜) + D.rank (a ⊓ b) = D.rank a + D.rank b := by
  exact_mod_cast D.rank_sup_add_rank_inf a b

theorem cast_rank_sub_cast_rank_pos (h : a < b) : (0 : 𝕜) < D.rank b - D.rank a :=
  sub_pos.2 (Nat.cast_lt.2 (D.rank_lt_rank h))

theorem cast_rank_sub_cast_rank_nonneg (h : a ≤ b) : (0 : 𝕜) ≤ D.rank b - D.rank a :=
  sub_nonneg.2 (Nat.cast_le.2 (D.rank_le_rank h))

/-! ### Slopes -/

/-- The slope of the interval `[a, b]`: the degree difference divided by the rank difference. It
is meaningful for `a < b`; for `a = b` it is `0`. -/
def slope (a b : L) : 𝕜 :=
  (D.degree b - D.degree a) / (D.rank b - D.rank a)

omit [IsStrictOrderedRing 𝕜] in
theorem slope_def (a b : L) :
    D.slope a b = (D.degree b - D.degree a) / (D.rank b - D.rank a) :=
  (rfl)

omit [IsStrictOrderedRing 𝕜] in
@[simp]
theorem slope_self (a : L) : D.slope a a = 0 := by
  simp [slope_def]

/-- Over an interval `a ≤ b`, the degree difference is the slope times the rank difference. -/
theorem degree_sub_degree_eq_slope_mul (h : a ≤ b) :
    D.degree b - D.degree a = D.slope a b * (D.rank b - D.rank a) := by
  rcases h.lt_or_eq with h | rfl
  · rw [slope_def, div_mul_cancel₀ _ (D.cast_rank_sub_cast_rank_pos h).ne']
  · simp

theorem slope_le_iff (h : a < b) {μ : 𝕜} :
    D.slope a b ≤ μ ↔ D.degree b - D.degree a ≤ μ * (D.rank b - D.rank a) := by
  rw [slope_def, div_le_iff₀ (D.cast_rank_sub_cast_rank_pos h)]

theorem le_slope_iff (h : a < b) {μ : 𝕜} :
    μ ≤ D.slope a b ↔ μ * (D.rank b - D.rank a) ≤ D.degree b - D.degree a := by
  rw [slope_def, le_div_iff₀ (D.cast_rank_sub_cast_rank_pos h)]

/-- Of two elements of the same rank above `a`, the one of larger degree has the larger slope. -/
theorem slope_le_slope_of_rank_eq (hae : a < e) (hr : D.rank e = D.rank c)
    (hd : D.degree e ≤ D.degree c) : D.slope a e ≤ D.slope a c := by
  rw [slope_def, slope_def, ← hr]
  exact div_le_div_of_nonneg_right (by linarith) (D.cast_rank_sub_cast_rank_pos hae).le

/-! ### Semistability -/

/-- The interval `[a, b]` is semistable if no `c ∈ (a, b]` has slope over `a` larger than the
slope of `[a, b]`. -/
def Semistable (a b : L) : Prop :=
  ∀ c, a < c → c ≤ b → D.slope a c ≤ D.slope a b

omit [IsStrictOrderedRing 𝕜] in
theorem semistable_iff :
    D.Semistable a b ↔ ∀ c, a < c → c ≤ b → D.slope a c ≤ D.slope a b :=
  Iff.rfl

/-- In a semistable interval `[a, b]`, every `c ∈ [a, b]` has degree over `a` at most the slope of
`[a, b]` times its rank over `a`. -/
theorem Semistable.degree_sub_le {D : RankDegree L 𝕜} (h : D.Semistable a b) (hac : a ≤ c)
    (hcb : c ≤ b) : D.degree c - D.degree a ≤ D.slope a b * (D.rank c - D.rank a) := by
  rcases hac.lt_or_eq with hac | rfl
  · exact (D.slope_le_iff hac).1 (h c hac hcb)
  · simp

/-! ### Maximal destabilizing elements -/

/-- `c` is the maximal destabilizing element of the interval `[a, b]`: it lies in `(a, b]`, has
maximal slope over `a` among the elements of `(a, b]`, and lies above every element of `(a, b]`
of that slope. -/
structure IsMaxDestabilizing (a b c : L) : Prop where
  /-- The element `c` lies strictly above `a`. -/
  left_lt : a < c
  /-- The element `c` lies below `b`. -/
  le_right : c ≤ b
  /-- The slope of `[a, c]` is maximal among the elements of `(a, b]`. -/
  slope_le (e : L) : a < e → e ≤ b → D.slope a e ≤ D.slope a c
  /-- Every element of `(a, b]` of the maximal slope lies below `c`. -/
  le_of_slope_eq (e : L) : a < e → e ≤ b → D.slope a e = D.slope a c → e ≤ c

namespace IsMaxDestabilizing

variable {D}

omit [IsStrictOrderedRing 𝕜] in
/-- The maximal destabilizing element of an interval is unique. -/
theorem unique {c' : L} (h : D.IsMaxDestabilizing a b c) (h' : D.IsMaxDestabilizing a b c') :
    c = c' :=
  have hs := le_antisymm (h'.slope_le c h.left_lt h.le_right) (h.slope_le c' h'.left_lt h'.le_right)
  le_antisymm (h'.le_of_slope_eq c h.left_lt h.le_right hs)
    (h.le_of_slope_eq c' h'.left_lt h'.le_right hs.symm)

omit [IsStrictOrderedRing 𝕜] in
/-- The interval up to the maximal destabilizing element is semistable. -/
theorem semistable (h : D.IsMaxDestabilizing a b c) : D.Semistable a c :=
  fun e hae hec ↦ h.slope_le e hae (hec.trans h.le_right)

/-- Above the maximal destabilizing element `c` of `[a, b]`, every element of `(c, b]` has slope
over `c` strictly less than the slope of `[a, c]`. -/
theorem slope_lt (h : D.IsMaxDestabilizing a b c) (hcd : c < d) (hdb : d ≤ b) :
    D.slope c d < D.slope a c := by
  by_contra! hle
  have had : a < d := h.left_lt.trans hcd
  have h1 := D.degree_sub_degree_eq_slope_mul h.left_lt.le
  have h2 := (D.le_slope_iff hcd).1 hle
  have h3 : D.slope a c ≤ D.slope a d := (D.le_slope_iff had).2 (by linarith)
  exact (h.le_of_slope_eq d had hdb (le_antisymm (h.slope_le d had hdb) h3)).not_gt hcd

end IsMaxDestabilizing

omit [IsStrictOrderedRing 𝕜] in
/-- An interval `[a, b]` with `a < b` is semistable exactly when `b` is its maximal destabilizing
element. -/
theorem semistable_iff_isMaxDestabilizing (hab : a < b) :
    D.Semistable a b ↔ D.IsMaxDestabilizing a b b :=
  ⟨fun h ↦ ⟨hab, le_rfl, h, fun _ _ heb _ ↦ heb⟩, IsMaxDestabilizing.semistable⟩

/-- The elements of `(a, b]` of maximal slope over `a` are closed under joins. -/
theorem slope_sup_eq (hac : a < c) (hcb : c ≤ b) (hae : a < e) (heb : e ≤ b)
    (hmax : ∀ x, a < x → x ≤ b → D.slope a x ≤ D.slope a c) (he : D.slope a e = D.slope a c) :
    D.slope a (c ⊔ e) = D.slope a c := by
  set μ := D.slope a c
  have hace : a < c ⊔ e := hac.trans_le le_sup_left
  have hinf : D.degree (c ⊓ e) - D.degree a ≤ μ * (D.rank (c ⊓ e) - D.rank a) := by
    rcases (le_inf hac.le hae.le).lt_or_eq with hlt | heq
    · exact (D.slope_le_iff hlt).1 (hmax _ hlt (inf_le_left.trans hcb))
    · simp [← heq]
  have hc := D.degree_sub_degree_eq_slope_mul hac.le
  have he' := D.degree_sub_degree_eq_slope_mul hae.le
  rw [he] at he'
  have hsup := D.degree_add_degree_le c e
  have hrk : μ * D.rank (c ⊔ e) + μ * D.rank (c ⊓ e) = μ * D.rank c + μ * D.rank e := by
    rw [← mul_add, ← mul_add, D.cast_rank_sup_add_cast_rank_inf]
  refine le_antisymm (hmax _ hace (sup_le hcb heb)) ((D.le_slope_iff hace).2 ?_)
  linarith

/-! ### Attainment of the maximal degree -/

/-- The degree attains its maximum on each rank level of each interval: whenever `(a, b]` has an
element of rank `r`, some element of `(a, b]` of rank `r` has the largest degree among them. For
the lattice of saturated subbundles of a vector bundle on a curve this holds because degrees are
integers bounded above, see `TauCeti.RankDegree.degreeMaxAttained_of_bddAbove`. -/
def DegreeMaxAttained : Prop :=
  ∀ a b e : L, a < e → e ≤ b → ∃ c, a < c ∧ c ≤ b ∧ D.rank c = D.rank e ∧
    ∀ e', a < e' → e' ≤ b → D.rank e' = D.rank e → D.degree e' ≤ D.degree c

omit [IsStrictOrderedRing 𝕜] in
theorem degreeMaxAttained_iff : D.DegreeMaxAttained ↔
    ∀ a b e : L, a < e → e ≤ b → ∃ c, a < c ∧ c ≤ b ∧ D.rank c = D.rank e ∧
      ∀ e', a < e' → e' ≤ b → D.rank e' = D.rank e → D.degree e' ≤ D.degree c :=
  Iff.rfl

omit [IsStrictOrderedRing 𝕜] in
/-- On a finite lattice the degree attains its maximum on each rank level of each interval. -/
theorem degreeMaxAttained_of_finite [Finite L] : D.DegreeMaxAttained := by
  intro a b e hae heb
  obtain ⟨c, ⟨hac, hcb, hrc⟩, hmax⟩ := Set.exists_max_image
    {x | a < x ∧ x ≤ b ∧ D.rank x = D.rank e} D.degree (Set.toFinite _) ⟨e, hae, heb, rfl⟩
  exact ⟨c, hac, hcb, hrc, fun e' hae' he'b hr ↦ hmax e' ⟨hae', he'b, hr⟩⟩

/-- An integer-valued degree that is bounded above on each lower interval attains its maximum on
each rank level of each interval. -/
theorem degreeMaxAttained_of_bddAbove (deg : L → ℤ) (hdeg : ∀ a, D.degree a = deg a)
    (hbdd : ∀ b, BddAbove (deg '' Set.Iic b)) : D.DegreeMaxAttained := by
  intro a b e hae heb
  let P : ℤ → Prop := fun z ↦ ∃ x, a < x ∧ x ≤ b ∧ D.rank x = D.rank e ∧ deg x = z
  obtain ⟨B, hB⟩ := hbdd b
  obtain ⟨z, ⟨c, hac, hcb, hrc, rfl⟩, hz⟩ := Int.exists_greatest_of_bdd (P := P)
    ⟨B, fun _ ⟨x, _, hxb, _, hx⟩ ↦ hx ▸ hB ⟨x, hxb, rfl⟩⟩ ⟨_, e, hae, heb, rfl, rfl⟩
  refine ⟨c, hac, hcb, hrc, fun e' hae' he'b hr ↦ ?_⟩
  rw [hdeg, hdeg]
  exact_mod_cast hz _ ⟨e', hae', he'b, hr, rfl⟩

namespace DegreeMaxAttained

variable {D}

/-- If the degree attains its maximum on each rank level, then the slope over `a` attains its
maximum on `(a, b]`. -/
theorem exists_slope_max (h : D.DegreeMaxAttained) (hab : a < b) :
    ∃ c, a < c ∧ c ≤ b ∧ ∀ e, a < e → e ≤ b → D.slope a e ≤ D.slope a c := by
  -- Induct on a bound `k` for the ranks of the competitors.
  suffices H : ∀ k : ℕ, ∃ c, a < c ∧ c ≤ b ∧
      ∀ e, a < e → e ≤ b → D.rank e ≤ k → D.slope a e ≤ D.slope a c by
    obtain ⟨c, hac, hcb, hc⟩ := H (D.rank b)
    exact ⟨c, hac, hcb, fun e hae heb ↦ hc e hae heb (D.rank_le_rank heb)⟩
  intro k
  induction k with
  | zero =>
    refine ⟨b, hab, le_rfl, fun e hae _ hk ↦ ?_⟩
    have := D.rank_lt_rank hae
    omega
  | succ k ih =>
    obtain ⟨c, hac, hcb, hc⟩ := ih
    by_cases hk : ∃ e, a < e ∧ e ≤ b ∧ D.rank e = k + 1
    · obtain ⟨e₀, hae₀, he₀b, hr₀⟩ := hk
      obtain ⟨c', hac', hc'b, hrc', hc'⟩ := h a b e₀ hae₀ he₀b
      have key : ∀ e, a < e → e ≤ b → D.rank e ≤ k + 1 →
          D.slope a e ≤ max (D.slope a c) (D.slope a c') := by
        intro e hae heb hk
        rcases hk.lt_or_eq with hk | hk
        · exact le_max_of_le_left (hc e hae heb (by omega))
        · refine le_max_of_le_right (D.slope_le_slope_of_rank_eq hae (by omega) ?_)
          exact hc' e hae heb (by omega)
      rcases le_total (D.slope a c) (D.slope a c') with hle | hle
      · exact ⟨c', hac', hc'b, fun e hae heb hk ↦ (key e hae heb hk).trans_eq (max_eq_right hle)⟩
      · exact ⟨c, hac, hcb, fun e hae heb hk ↦ (key e hae heb hk).trans_eq (max_eq_left hle)⟩
    · refine ⟨c, hac, hcb, fun e hae heb hke ↦ hc e hae heb ?_⟩
      have : D.rank e ≠ k + 1 := fun hr ↦ hk ⟨e, hae, heb, hr⟩
      omega

/-- If the degree attains its maximum on each rank level, then every interval `[a, b]` with
`a < b` has a maximal destabilizing element. -/
theorem exists_isMaxDestabilizing (h : D.DegreeMaxAttained) (hab : a < b) :
    ∃ c, D.IsMaxDestabilizing a b c := by
  classical
  obtain ⟨c₀, hac₀, hc₀b, hmax⟩ := h.exists_slope_max hab
  -- Among the elements of maximal slope, take one of greatest rank.
  let P : ℕ → Prop := fun n ↦ ∃ c, a < c ∧ c ≤ b ∧ D.slope a c = D.slope a c₀ ∧ D.rank c = n
  have hP₀ : P (D.rank c₀) := ⟨c₀, hac₀, hc₀b, rfl, rfl⟩
  obtain ⟨c, hac, hcb, hμ, hrc⟩ := Nat.findGreatest_spec (D.rank_le_rank hc₀b) hP₀
  have hmax' : ∀ x, a < x → x ≤ b → D.slope a x ≤ D.slope a c := hμ ▸ hmax
  refine ⟨c, hac, hcb, hmax', fun e hae heb he ↦ ?_⟩
  have hce : c ≤ c ⊔ e := le_sup_left
  have hsup := D.slope_sup_eq hac hcb hae heb hmax' he
  have hrk : D.rank (c ⊔ e) ≤ D.rank c := hrc ▸ Nat.le_findGreatest
    (D.rank_le_rank (sup_le hcb heb)) ⟨c ⊔ e, hac.trans_le hce, sup_le hcb heb, hsup.trans hμ, rfl⟩
  exact le_sup_right.trans (D.eq_of_le_of_rank_le hce hrk).ge

/-- The maximal destabilizing element of an interval `[a, b]` with `a < b`, when the degree
attains its maximum on each rank level. -/
noncomputable def maxDestabilizing (h : D.DegreeMaxAttained) (hab : a < b) : L :=
  (h.exists_isMaxDestabilizing hab).choose

theorem isMaxDestabilizing_maxDestabilizing (h : D.DegreeMaxAttained) (hab : a < b) :
    D.IsMaxDestabilizing a b (h.maxDestabilizing hab) :=
  (h.exists_isMaxDestabilizing hab).choose_spec

end DegreeMaxAttained

/-- A maximal destabilizing element is the chosen one. -/
theorem IsMaxDestabilizing.eq_maxDestabilizing {D : RankDegree L 𝕜}
    (hc : D.IsMaxDestabilizing a b c) (h : D.DegreeMaxAttained) :
    c = h.maxDestabilizing (hc.left_lt.trans_le hc.le_right) :=
  hc.unique (h.isMaxDestabilizing_maxDestabilizing _)

/-! ### Harder–Narasimhan series -/

/-- A Harder–Narasimhan series: a strictly increasing series `a₀ < a₁ < ⋯ < a_k` whose
successive intervals `[aᵢ, aᵢ₊₁]` are semistable, with strictly decreasing slopes. -/
structure IsHNSeries (p : LTSeries L) : Prop where
  /-- Each step of the series is semistable. -/
  semistable (i : Fin p.length) : D.Semistable (p i.castSucc) (p i.succ)
  /-- The slopes of the steps strictly decrease. -/
  strictAnti_slope : StrictAnti fun i : Fin p.length ↦ D.slope (p i.castSucc) (p i.succ)

/-- The basic estimate behind the Harder–Narasimhan theorem. Let `[x, y]` be semistable of slope
`μ`, and suppose that above `y`, up to `z`, the degree over `y` is at most `μ` times the rank over
`y`, with equality only at `y`. Then on `[x, z]` the degree over `x` is at most `μ` times the rank
over `x`, with equality only below `y`. -/
private theorem degree_sub_le_of_semistable (hxy : x < y) (hs : D.Semistable x y) (hyz : y ≤ z)
    (hrest : ∀ c, y ≤ c → c ≤ z →
      D.degree c - D.degree y ≤ D.slope x y * (D.rank c - D.rank y) ∧
      (D.degree c - D.degree y = D.slope x y * (D.rank c - D.rank y) → c = y))
    (hxc : x ≤ c) (hcz : c ≤ z) :
    D.degree c - D.degree x ≤ D.slope x y * (D.rank c - D.rank x) ∧
      (D.degree c - D.degree x = D.slope x y * (D.rank c - D.rank x) → c ≤ y) := by
  set μ := D.slope x y
  -- Split `c` along `y`: the part `c ⊓ y` lies in `[x, y]`, the part `c ⊔ y` in `[y, z]`.
  have h1 := D.degree_add_degree_le c y
  have h2 : μ * D.rank (c ⊔ y) + μ * D.rank (c ⊓ y) = μ * D.rank c + μ * D.rank y := by
    rw [← mul_add, ← mul_add, D.cast_rank_sup_add_cast_rank_inf]
  obtain ⟨h3, h3eq⟩ := hrest (c ⊔ y) le_sup_right (sup_le hcz hyz)
  have h4 := hs.degree_sub_le (le_inf hxc hxy.le) inf_le_right
  refine ⟨by linarith, fun heq ↦ le_sup_left.trans (h3eq ?_).le⟩
  linarith

/-- Degree bound along a Harder–Narasimhan series: from the `i`-th term on, the degree over `p i`
is at most `μ` times the rank over `p i` for any `μ` above all later slopes, with equality only
at `p i`. -/
private theorem IsHNSeries.degree_sub_le_aux {D : RankDegree L 𝕜} {p : LTSeries L}
    (hp : D.IsHNSeries p) (i : Fin (p.length + 1)) (μ : 𝕜)
    (hμ : ∀ j : Fin p.length, i ≤ j.castSucc → D.slope (p j.castSucc) (p j.succ) < μ)
    (c : L) (hic : p i ≤ c) (hc : c ≤ p.last) :
    D.degree c - D.degree (p i) ≤ μ * (D.rank c - D.rank (p i)) ∧
      (D.degree c - D.degree (p i) = μ * (D.rank c - D.rank (p i)) → c = p i) := by
  induction i using Fin.reverseInduction generalizing μ c with
  | last =>
    obtain rfl : c = p (Fin.last _) := le_antisymm hc hic
    simp
  | cast i ih =>
    have hxy : p i.castSucc < p i.succ := p.strictMono Fin.castSucc_lt_succ
    have hν := hμ i le_rfl
    obtain ⟨hb, -⟩ := degree_sub_le_of_semistable D hxy (hp.semistable i)
      (p.monotone (Fin.le_last _))
      (ih _ (fun j hj ↦ hp.strictAnti_slope (Fin.succ_le_castSucc_iff.1 hj))) hic hc
    have hr := D.cast_rank_sub_cast_rank_nonneg hic
    refine ⟨hb.trans (mul_le_mul_of_nonneg_right hν.le hr), fun he ↦ ?_⟩
    -- Equality with `μ` larger than the first slope forces the rank difference to vanish.
    have hzero : (D.rank c : 𝕜) - D.rank (p i.castSucc) = 0 := by
      by_contra hne
      have := mul_lt_mul_of_pos_right hν (lt_of_le_of_ne hr (Ne.symm hne))
      linarith
    rw [sub_eq_zero, Nat.cast_inj] at hzero
    exact (D.eq_of_le_of_rank_le hic hzero.le).symm

namespace IsHNSeries

variable {D} {p q : LTSeries L}

/-- Each step of a Harder–Narasimhan series is the maximal destabilizing element of the interval
from the previous step to the end of the series. -/
theorem isMaxDestabilizing (hp : D.IsHNSeries p) (i : Fin p.length) :
    D.IsMaxDestabilizing (p i.castSucc) p.last (p i.succ) := by
  have hxy : p i.castSucc < p i.succ := p.strictMono Fin.castSucc_lt_succ
  have key (c : L) (hxc : p i.castSucc ≤ c) (hc : c ≤ p.last) :=
    degree_sub_le_of_semistable D hxy (hp.semistable i) (p.monotone (Fin.le_last _))
      (hp.degree_sub_le_aux i.succ _ fun j hj ↦ hp.strictAnti_slope (Fin.succ_le_castSucc_iff.1 hj))
      hxc hc
  refine ⟨hxy, p.monotone (Fin.le_last _), fun e hxe he ↦ ?_, fun e hxe he hse ↦ ?_⟩
  · exact (D.slope_le_iff hxe).2 (key e hxe.le he).1
  · refine (key e hxe.le he).2 ?_
    rw [D.degree_sub_degree_eq_slope_mul hxe.le, hse]

/-- The first step of a Harder–Narasimhan series of positive length is the maximal destabilizing
element of the whole interval. -/
theorem isMaxDestabilizing_head (hp : D.IsHNSeries p) (h : p.length ≠ 0) :
    D.IsMaxDestabilizing p.head p.last (p 1) := by
  have : NeZero p.length := ⟨h⟩
  have := hp.isMaxDestabilizing 0
  rwa [Fin.succ_zero_eq_one'] at this

/-- The terms of two Harder–Narasimhan series with the same endpoints agree at every index both
series reach. -/
private theorem apply_eq_apply (hp : D.IsHNSeries p) (hq : D.IsHNSeries q)
    (hhead : p.head = q.head) (hlast : p.last = q.last) :
    ∀ (k : ℕ) (hkp : k < p.length + 1) (hkq : k < q.length + 1), p ⟨k, hkp⟩ = q ⟨k, hkq⟩ := by
  intro k
  induction k with
  | zero => exact fun _ _ ↦ hhead
  | succ k ih =>
    intro hkp hkq
    have hk := ih (by omega) (by omega)
    have hp' := hp.isMaxDestabilizing ⟨k, by omega⟩
    have hq' := hq.isMaxDestabilizing ⟨k, by omega⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at hp' hq'
    rw [hk, hlast] at hp'
    exact hp'.unique hq'

/-- A Harder–Narasimhan series is determined by its endpoints. -/
theorem eq (hp : D.IsHNSeries p) (hq : D.IsHNSeries q) (hhead : p.head = q.head)
    (hlast : p.last = q.last) : p = q := by
  have hpq := apply_eq_apply hp hq hhead hlast
  -- A shorter series would reach the common endpoint at an index where the longer one is
  -- still strictly below it.
  have hlen : ∀ {p q : LTSeries L}, (∀ (k : ℕ) (hkp : k < p.length + 1)
      (hkq : k < q.length + 1), p ⟨k, hkp⟩ = q ⟨k, hkq⟩) → p.last = q.last →
      ¬ p.length < q.length := by
    intro p q hpq hlast hlt
    have h1 := hpq p.length (by omega) (by omega)
    have h2 : q ⟨p.length, by omega⟩ < q.last :=
      q.strictMono (Fin.lt_def.2 hlt)
    exact h2.ne (h1.symm.trans hlast)
  have hlen_eq : p.length = q.length := le_antisymm
    (not_lt.1 (hlen (fun k h h' ↦ (hpq k h' h).symm) hlast.symm)) (not_lt.1 (hlen hpq hlast))
  refine RelSeries.ext hlen_eq (funext fun i ↦ ?_)
  exact hpq i i.isLt (hlen_eq ▸ i.isLt)

/-- A Harder–Narasimhan series with distinct endpoints consists of a single step exactly when
the interval between its endpoints is semistable. -/
theorem length_eq_one_iff (hp : D.IsHNSeries p) (h : p.head < p.last) :
    p.length = 1 ↔ D.Semistable p.head p.last := by
  have hne : p.length ≠ 0 := by
    intro h0
    have h0' : (0 : Fin (p.length + 1)) = Fin.last _ := by
      ext
      simp [h0]
    exact h.ne (congrArg p h0')
  have hmd := hp.isMaxDestabilizing_head hne
  have : NeZero p.length := ⟨hne⟩
  -- The index `1` is the successor of `0`, so its value is `1`.
  have hval : ((1 : Fin (p.length + 1)) : ℕ) = 1 := by
    rw [← Fin.succ_zero_eq_one', Fin.val_succ, Fin.val_zero]
  constructor
  · intro h1
    have h1' : p 1 = p.last := congrArg p (Fin.ext (by rw [hval, Fin.val_last, h1]))
    exact h1' ▸ hmd.semistable
  · intro hs
    have hlast := hmd.unique ((D.semistable_iff_isMaxDestabilizing h).1 hs)
    have := congrArg Fin.val (p.strictMono.injective hlast)
    rw [hval, Fin.val_last] at this
    exact this.symm

end IsHNSeries

omit [IsStrictOrderedRing 𝕜] in
/-- The trivial series at a single point is a Harder–Narasimhan series. -/
theorem isHNSeries_singleton (a : L) :
    D.IsHNSeries (RelSeries.singleton {(a, b) : L × L | a < b} a) :=
  ⟨fun i ↦ i.elim0, fun i ↦ i.elim0⟩

namespace DegreeMaxAttained

variable {D}

/-- Existence of Harder–Narasimhan series: if the degree attains its maximum on each rank level,
every interval `[a, b]` with `a ≤ b` has a Harder–Narasimhan series from `a` to `b`. -/
theorem exists_isHNSeries (h : D.DegreeMaxAttained) (hab : a ≤ b) :
    ∃ p : LTSeries L, p.head = a ∧ p.last = b ∧ D.IsHNSeries p := by
  classical
  choose f hf using fun x (hx : x < b) ↦ h.exists_isMaxDestabilizing hx
  -- Iterate the passage to the maximal destabilizing element of `[x, b]`, starting from `a`.
  let next : L → L := fun x ↦ if hx : x < b then f x hx else b
  let g : ℕ → L := fun k ↦ next^[k] a
  have g_succ (k : ℕ) : g (k + 1) = next (g k) := Function.iterate_succ_apply' next k a
  have next_of_lt (x : L) (hx : x < b) : next x = f x hx := by simp [next, hx]
  have next_le (x : L) : next x ≤ b := by
    by_cases hx : x < b
    · exact (next_of_lt _ hx ▸ hf _ hx).le_right
    · simp [next, hx]
  have g_le (k : ℕ) : g k ≤ b := by
    cases k with
    | zero => exact hab
    | succ k => exact g_succ k ▸ next_le _
  have g_md (k : ℕ) (hk : g k < b) : D.IsMaxDestabilizing (g k) b (g (k + 1)) := by
    rw [g_succ, next_of_lt _ hk]
    exact hf _ hk
  -- The ranks increase strictly until `b` is reached, so `b` is reached.
  have hex : ∃ n, g n = b := by
    by_contra! hne
    have hrk (k : ℕ) : D.rank a + k ≤ D.rank (g k) := by
      induction k with
      | zero => simp [g]
      | succ k ih =>
        have := D.rank_lt_rank (g_md k ((g_le k).lt_of_ne (hne k))).left_lt
        omega
    have := hrk (D.rank b + 1)
    have := D.rank_le_rank (g_le (D.rank b + 1))
    omega
  let n := Nat.find hex
  have g_lt (k : ℕ) (hk : k < n) : g k < b := (g_le k).lt_of_ne (Nat.find_min hex hk)
  have hslope (m : ℕ) (hm : m < n - 1) :
      D.slope (g (m + 1)) (g (m + 1 + 1)) < D.slope (g m) (g (m + 1)) :=
    (g_md m (g_lt m (by omega))).slope_lt (g_md (m + 1) (g_lt (m + 1) (by omega))).left_lt
      (g_le _)
  have hanti : StrictAntiOn (fun m ↦ D.slope (g m) (g (m + 1))) (Set.Iic (n - 1)) :=
    strictAntiOn_Iic_of_succ_lt fun m hm ↦ by simpa [Nat.succ_eq_succ] using hslope m hm
  refine ⟨LTSeries.mk n (fun i ↦ g i) ?_, rfl, Nat.find_spec hex, ?_, ?_⟩
  · exact Fin.strictMono_iff_lt_succ.2 fun i ↦ (g_md i (g_lt i i.isLt)).left_lt
  · intro i
    exact (g_md i (g_lt i i.isLt)).semistable
  · intro i j hij
    exact hanti (Nat.le_sub_one_of_lt (i.isLt : (i : ℕ) < n))
      (Nat.le_sub_one_of_lt (j.isLt : (j : ℕ) < n)) hij

/-- The Harder–Narasimhan theorem: if the degree attains its maximum on each rank level, every
interval `[a, b]` with `a ≤ b` has a unique Harder–Narasimhan series from `a` to `b`. -/
theorem existsUnique_isHNSeries (h : D.DegreeMaxAttained) (hab : a ≤ b) :
    ∃! p : LTSeries L, p.head = a ∧ p.last = b ∧ D.IsHNSeries p := by
  obtain ⟨p, hpa, hpb, hp⟩ := h.exists_isHNSeries hab
  exact ⟨p, ⟨hpa, hpb, hp⟩, fun q ⟨hqa, hqb, hq⟩ ↦ hq.eq hp (hqa.trans hpa.symm)
    (hqb.trans hpb.symm)⟩

/-- The Harder–Narasimhan series of an interval `[a, b]` with `a ≤ b`, when the degree attains
its maximum on each rank level. -/
noncomputable def hnSeries (h : D.DegreeMaxAttained) (hab : a ≤ b) : LTSeries L :=
  (h.exists_isHNSeries hab).choose

@[simp]
theorem head_hnSeries (h : D.DegreeMaxAttained) (hab : a ≤ b) : (h.hnSeries hab).head = a :=
  (h.exists_isHNSeries hab).choose_spec.1

@[simp]
theorem last_hnSeries (h : D.DegreeMaxAttained) (hab : a ≤ b) : (h.hnSeries hab).last = b :=
  (h.exists_isHNSeries hab).choose_spec.2.1

theorem isHNSeries_hnSeries (h : D.DegreeMaxAttained) (hab : a ≤ b) :
    D.IsHNSeries (h.hnSeries hab) :=
  (h.exists_isHNSeries hab).choose_spec.2.2

/-- The Harder–Narasimhan series of an interval `[a, b]` with `a < b` has positive length. -/
theorem length_hnSeries_ne_zero (h : D.DegreeMaxAttained) (hab : a < b) :
    (h.hnSeries hab.le).length ≠ 0 :=
  RelSeries.length_ne_zero_of_nontrivial
    ⟨_, RelSeries.head_mem _, _, RelSeries.last_mem _, by simpa using hab.ne⟩

/-- The first step of the Harder–Narasimhan series of an interval `[a, b]` with `a < b` is its
maximal destabilizing element. -/
theorem hnSeries_one (h : D.DegreeMaxAttained) (hab : a < b) :
    h.hnSeries hab.le 1 = h.maxDestabilizing hab := by
  have hmd := (h.isHNSeries_hnSeries hab.le).isMaxDestabilizing_head (h.length_hnSeries_ne_zero hab)
  rw [head_hnSeries, last_hnSeries] at hmd
  exact hmd.eq_maxDestabilizing h

end DegreeMaxAttained

/-- A Harder–Narasimhan series is the Harder–Narasimhan series of the interval between its
endpoints. -/
theorem IsHNSeries.eq_hnSeries {D : RankDegree L 𝕜} {p : LTSeries L} (hp : D.IsHNSeries p)
    (h : D.DegreeMaxAttained) : p = h.hnSeries p.head_le_last :=
  hp.eq (h.isHNSeries_hnSeries _) (h.head_hnSeries _).symm (h.last_hnSeries _).symm

section LinearOrder

variable {L 𝕜 : Type*} [LinearOrder L] [AddCommGroup 𝕜] [PartialOrder 𝕜]

/-- On a linearly ordered set every degree is supermodular, since the join and meet of two
elements are the two elements themselves; so a strictly monotone rank and an arbitrary degree form
a rank and degree. On `Fin (n + 1)` with the rank `Fin.val`, this encodes a finite sequence of
points `(k, degree k)` in the plane. -/
def ofLinearOrder (rank : L → ℕ) (hrank : StrictMono rank) (degree : L → 𝕜) :
    RankDegree L 𝕜 where
  rank := rank
  degree := degree
  rank_strictMono := hrank
  rank_sup_add_rank_inf a b := by
    rcases le_total a b with h | h <;> simp [h, add_comm]
  isSubmodular_neg_degree := (isSubmodular_def _).2 fun a b ↦ by
    rcases le_total a b with h | h <;> simp [h, add_comm]

@[simp]
theorem rank_ofLinearOrder (rank : L → ℕ) (hrank : StrictMono rank) (degree : L → 𝕜) :
    (ofLinearOrder rank hrank degree).rank = rank :=
  (rfl)

@[simp]
theorem degree_ofLinearOrder (rank : L → ℕ) (hrank : StrictMono rank) (degree : L → 𝕜) :
    (ofLinearOrder rank hrank degree).degree = degree :=
  (rfl)

end LinearOrder

end RankDegree

end TauCeti
