/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Analysis.Real.Sqrt
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Topology.Algebra.Polynomial.Root.Isolated

/-!
# Exact algebraic values with isolating rational regions

An algebraic number used in a certified computation is never identified with a numerical
approximation. It is an element `z` of a field `K` over `ℚ` (for instance an algebraic closure of
`ℚ` or a number field) together with a fixed embedding `σ : K →+* ℂ`, and it is pinned down by a
*root isolation*: a nonzero squarefree polynomial `f ∈ ℚ[X]` with `f(z) = 0` and a rational
region of the complex plane (a real interval, a closed disc with centre in `ℚ(i)`, or a rectangle
with rational sides) that contains `σ z` and no other complex root of `f`. The proof that the
region contains exactly one root is part of the datum; a numerical root is never asserted to be
exact.

Such data exist for every algebraic `z` and can be taken inside any prescribed neighbourhood of
`σ z`, with `σ z` in the interior of the region when it is a disc or a rectangle and strictly
between the endpoints when it is an interval, so no root of `f` lies on the boundary circle, the
sides or the endpoints of the region; data of finitely many distinct values can be taken pairwise
disjoint. Equality of two isolated values is decided exactly: `z = z'` if and only if the gcd of
the two polynomials has a complex root in the intersection of the two regions. Overlapping regions
alone prove nothing: `[1, 2]` isolates both `√2` (as a root of `X² - 2`) and `√3` (as a root of
`X² - 3`).

## Main definitions

* `TauCeti.RationalRegion`: a real interval, a closed disc or a rectangle in `ℂ` described by
  rational numbers, with `TauCeti.RationalRegion.toSet` the subset of `ℂ` it describes.
* `TauCeti.RootIsolation σ z`: a nonzero squarefree rational polynomial vanishing at `z`, with a
  rational region containing `σ z` and no other complex root of the polynomial.
* `TauCeti.RootIsolation.ofRat`: the isolation of a rational number `q` by `X - q` and `[q, q]`.
* `TauCeti.RootIsolation.ofSubset`: the isolation given by a squarefree annihilator and a region
  containing `σ z` and no other root; `TauCeti.RootIsolation.restrict` shrinks the region of an
  isolation.

## Main results

* `TauCeti.RationalRegion.isCompact_toSet`: every rational region is compact, hence bounded and
  closed.
* `TauCeti.RootIsolation.eq_of_aeval_eq_zero`: an element of `K` that is a root of the polynomial
  and is sent by `σ` into the region equals `z`.
* `TauCeti.RootIsolation.exists_disc`, `TauCeti.RootIsolation.exists_box`,
  `TauCeti.RootIsolation.exists_interval`: for every squarefree annihilator `f` of `z` and every
  neighbourhood `V` of `σ z`, there is an isolation by `f` whose region is a disc, a rectangle or
  (when `σ z` is real) an interval contained in `V`, with `σ z` in the interior of the disc or
  rectangle and strictly between the endpoints of the interval.
* `TauCeti.RootIsolation.nonempty_iff_isAlgebraic`: an element of `K` has a root isolation
  exactly when it is algebraic over `ℚ`.
* `TauCeti.RootIsolation.exists_diam_lt`: every algebraic value has isolations of arbitrarily
  small diameter.
* `TauCeti.RootIsolation.exists_subset_of_isAlgebraic`: every algebraic value has an isolation
  inside every prescribed neighbourhood. With `TauCeti.RootIsolation.isAlgebraic` and Mathlib's
  `IsAlgebraic.add`, `IsAlgebraic.mul` and `IsAlgebraic.inv`, this isolates the sum, the product
  and the inverse of isolated values.
* `TauCeti.RootIsolation.exists_pairwise_disjoint`: finitely many algebraic values have isolations
  with pairwise disjoint regions.
* `TauCeti.RootIsolation.eq_iff_exists_aeval_gcd_eq_zero`: the exact equality test by the gcd of
  the two polynomials.

## References

* B. M. M. de Weger, *Algorithms for Diophantine equations*, CWI Tract 65, 1989, §2.5, printed
  pp. 32–34 (numerical approximation of roots in Diophantine computations).
-/

public section

open Polynomial Complex Metric Topology Filter Function

namespace TauCeti

/-- A closed region of the complex plane described by rational numbers: a real interval, a closed
disc with centre in `ℚ(i)`, or a rectangle with rational sides. -/
inductive RationalRegion where
  /-- The real interval `[l, u]`, as a subset of `ℂ`. -/
  | interval (J : NonemptyInterval ℚ)
  /-- The closed disc `{w : |w - (a + b i)| ≤ r}`. -/
  | disc (a b r : ℚ)
  /-- The rectangle `{w : Re w ∈ R, Im w ∈ J}`. -/
  | box (R J : NonemptyInterval ℚ)

namespace RationalRegion

/-- The subset of `ℂ` described by a rational region. -/
noncomputable def toSet : RationalRegion → Set ℂ
  | interval J => ((↑) : ℝ → ℂ) '' Set.Icc (J.fst : ℝ) J.snd
  | disc a b r => closedBall (a + b * I) r
  | box R J => Set.Icc (R.fst : ℝ) R.snd ×ℂ Set.Icc (J.fst : ℝ) J.snd

theorem toSet_interval (J : NonemptyInterval ℚ) :
    (interval J).toSet = ((↑) : ℝ → ℂ) '' Set.Icc (J.fst : ℝ) J.snd :=
  (rfl)

theorem toSet_disc (a b r : ℚ) : (disc a b r).toSet = closedBall (a + b * I) r :=
  (rfl)

theorem toSet_box (R J : NonemptyInterval ℚ) :
    (box R J).toSet = Set.Icc (R.fst : ℝ) R.snd ×ℂ Set.Icc (J.fst : ℝ) J.snd :=
  (rfl)

@[simp]
theorem mem_toSet_interval {J : NonemptyInterval ℚ} {w : ℂ} :
    w ∈ (interval J).toSet ↔ w.im = 0 ∧ w.re ∈ Set.Icc (J.fst : ℝ) J.snd := by
  rw [toSet_interval]
  constructor
  · rintro ⟨t, ht, rfl⟩
    simpa using ht
  · rintro ⟨him, hre⟩
    exact ⟨w.re, hre, Complex.ext (by simp) (by simp [him])⟩

@[simp]
theorem mem_toSet_disc {a b r : ℚ} {w : ℂ} :
    w ∈ (disc a b r).toSet ↔ dist w (a + b * I) ≤ r :=
  Iff.rfl

@[simp]
theorem mem_toSet_box {R J : NonemptyInterval ℚ} {w : ℂ} :
    w ∈ (box R J).toSet ↔
      w.re ∈ Set.Icc (R.fst : ℝ) R.snd ∧ w.im ∈ Set.Icc (J.fst : ℝ) J.snd :=
  mem_reProdIm

/-- The diameter of a real interval, viewed in `ℂ`, is its width. -/
theorem diam_toSet_interval (J : NonemptyInterval ℚ) : diam (interval J).toSet = J.length := by
  rw [toSet_interval, isometry_ofReal.diam_image,
    Real.diam_Icc (by exact_mod_cast J.fst_le_snd), NonemptyInterval.length, Rat.cast_sub]

/-- The subset of `ℂ` described by a rational region is compact. -/
theorem isCompact_toSet : ∀ R : RationalRegion, IsCompact R.toSet
  | interval _ => isCompact_Icc.image continuous_ofReal
  | disc _ _ _ => isCompact_closedBall _ _
  | box _ _ => isCompact_Icc.reProdIm isCompact_Icc

/-- The subset of `ℂ` described by a rational region is bounded. -/
theorem isBounded_toSet (R : RationalRegion) : Bornology.IsBounded R.toSet :=
  R.isCompact_toSet.isBounded

/-- The subset of `ℂ` described by a rational region is closed. -/
theorem isClosed_toSet (R : RationalRegion) : IsClosed R.toSet :=
  R.isCompact_toSet.isClosed

/-- Rational approximations of the real and imaginary parts of `x` to within `s`, with
`4 s < ε`. -/
private theorem exists_rat_approx (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b s : ℚ, 0 < s ∧ 4 * (s : ℝ) < ε ∧ |x.re - a| < s ∧ |x.im - b| < s := by
  obtain ⟨s, hs0, hs⟩ := exists_rat_btwn (div_pos hε four_pos)
  obtain ⟨a, ha⟩ := exists_rat_near x.re hs0
  obtain ⟨b, hb⟩ := exists_rat_near x.im hs0
  exact ⟨a, b, s, by exact_mod_cast hs0, by linarith, ha, hb⟩

/-- Every neighbourhood of `x` contains a closed disc with centre in `ℚ(i)` and rational radius
containing `x` in its interior. -/
theorem exists_disc_subset {x : ℂ} {V : Set ℂ} (hV : V ∈ 𝓝 x) :
    ∃ a b r : ℚ, dist x (a + b * I) < r ∧ (disc a b r).toSet ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨a, b, s, -, hsε, ha, hb⟩ := exists_rat_approx x hε
  have hc : dist x (a + b * I) < 2 * s := by
    have : ‖x - (a + b * I)‖ ≤ |x.re - a| + |x.im - b| := by
      simpa using norm_le_abs_re_add_abs_im (x - (a + b * I))
    rw [Complex.dist_eq]
    linarith
  refine ⟨a, b, 2 * s, by exact_mod_cast hc, fun w hw => hεV ?_⟩
  rw [mem_toSet_disc] at hw
  rw [mem_ball]
  have := dist_triangle w (a + b * I) x
  rw [dist_comm (a + b * I : ℂ) x] at this
  push_cast at hw
  linarith

/-- The rational interval `[a - s, a + s]`. -/
private def symmInterval (a s : ℚ) (hs : 0 < s) : NonemptyInterval ℚ :=
  ⟨(a - s, a + s), by dsimp only; linarith⟩

private theorem mem_Icc_symmInterval_iff {a s : ℚ} (hs : 0 < s) {t : ℝ} :
    t ∈ Set.Icc ((symmInterval a s hs).fst : ℝ) (symmInterval a s hs).snd ↔ |t - a| ≤ s := by
  simp only [symmInterval, Set.mem_Icc, abs_sub_le_iff]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

private theorem mem_Ioo_symmInterval_iff {a s : ℚ} (hs : 0 < s) {t : ℝ} :
    t ∈ Set.Ioo ((symmInterval a s hs).fst : ℝ) (symmInterval a s hs).snd ↔ |t - a| < s := by
  simp only [symmInterval, Set.mem_Ioo, abs_sub_lt_iff]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Every neighbourhood of `x` contains a rectangle with rational sides containing `x` in its
interior. -/
theorem exists_box_subset {x : ℂ} {V : Set ℂ} (hV : V ∈ 𝓝 x) :
    ∃ R J : NonemptyInterval ℚ, x.re ∈ Set.Ioo (R.fst : ℝ) R.snd ∧
      x.im ∈ Set.Ioo (J.fst : ℝ) J.snd ∧ (box R J).toSet ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨a, b, s, hs, hsε, ha, hb⟩ := exists_rat_approx x hε
  refine ⟨symmInterval a s hs, symmInterval b s hs, (mem_Ioo_symmInterval_iff hs).2 ha,
    (mem_Ioo_symmInterval_iff hs).2 hb, fun w hw => hεV ?_⟩
  rw [mem_toSet_box, mem_Icc_symmInterval_iff, mem_Icc_symmInterval_iff] at hw
  rw [mem_ball, Complex.dist_eq]
  have := norm_le_abs_re_add_abs_im (w - x)
  rw [sub_re, sub_im] at this
  have h1 := abs_sub_le w.re a x.re
  have h2 := abs_sub_le w.im b x.im
  rw [abs_sub_comm (a : ℝ)] at h1
  rw [abs_sub_comm (b : ℝ)] at h2
  linarith [hw.1, hw.2]

/-- Every neighbourhood of a real number `x` of `ℂ` contains a real interval with rational
endpoints, with `x.re` strictly between its endpoints. -/
theorem exists_interval_subset {x : ℂ} (hx : x.im = 0) {V : Set ℂ} (hV : V ∈ 𝓝 x) :
    ∃ J : NonemptyInterval ℚ, x.re ∈ Set.Ioo (J.fst : ℝ) J.snd ∧ (interval J).toSet ⊆ V := by
  obtain ⟨R, J, hR, hJ, hsub⟩ := exists_box_subset hV
  refine ⟨R, hR, fun w hw => hsub ?_⟩
  rw [mem_toSet_interval] at hw
  rw [mem_toSet_box, hw.1, ← hx]
  exact ⟨hw.2, Set.Ioo_subset_Icc_self hJ⟩

end RationalRegion

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- A *root isolation* of an element `z` of a field `K` over `ℚ`, with respect to an embedding
`σ : K →+* ℂ`: a squarefree (hence nonzero) polynomial `f ∈ ℚ[X]` with `f(z) = 0`, and a rational
region of `ℂ` containing `σ z` in which `σ z` is the only complex root of `f`. -/
@[ext]
structure RootIsolation (σ : K →+* ℂ) (z : K) where
  /-- The isolating polynomial. -/
  poly : ℚ[X]
  /-- The isolating polynomial is squarefree. -/
  squarefree_poly : Squarefree poly
  /-- The isolating polynomial vanishes at `z`. -/
  aeval_poly : aeval z poly = 0
  /-- The isolating rational region. -/
  region : RationalRegion
  /-- The region contains `σ z`. -/
  mem_region : σ z ∈ region.toSet
  /-- Every complex root of the polynomial in the region is `σ z`. -/
  eq_of_mem_region : ∀ w ∈ region.toSet, aeval w poly = 0 → w = σ z

namespace RootIsolation

attribute [simp] aeval_poly

variable {σ : K →+* ℂ} {z z' : K}

/-- The isolating polynomial is nonzero. -/
theorem poly_ne_zero (D : RootIsolation σ z) : D.poly ≠ 0 :=
  D.squarefree_poly.ne_zero

/-- The isolating polynomial vanishes at the embedded value `σ z`. -/
@[simp]
theorem aeval_apply_poly (D : RootIsolation σ z) : aeval (σ z) D.poly = 0 := by
  simpa [D.aeval_poly] using aeval_algHom_apply σ.toRatAlgHom z D.poly

/-- An isolated value is algebraic over `ℚ`. -/
theorem isAlgebraic (D : RootIsolation σ z) : IsAlgebraic ℚ z :=
  ⟨D.poly, D.poly_ne_zero, D.aeval_poly⟩

/-- Every root `y ∈ K` of the isolating polynomial with `σ y` in the region is `z`. -/
theorem eq_of_aeval_eq_zero (D : RootIsolation σ z) {y : K} (hy : σ y ∈ D.region.toSet)
    (h : aeval y D.poly = 0) : y = z :=
  σ.injective <| D.eq_of_mem_region _ hy <| by
    simpa [h] using aeval_algHom_apply σ.toRatAlgHom y D.poly

/-- The isolation of a rational number `q` by the polynomial `X - q` and the singleton interval
`[q, q]`. -/
noncomputable def ofRat (q : ℚ) : RootIsolation σ (q : K) where
  poly := X - C q
  squarefree_poly := (irreducible_X_sub_C q).squarefree
  aeval_poly := by simp
  region := .interval (NonemptyInterval.pure q)
  mem_region := by simp
  eq_of_mem_region w hw _ := by
    rw [RationalRegion.mem_toSet_interval] at hw
    simp only [NonemptyInterval.pure, Set.Icc_self, Set.mem_singleton_iff] at hw
    rw [map_ratCast]
    exact Complex.ext (by simp [hw.2]) (by simp [hw.1])

@[simp]
theorem ofRat_poly (q : ℚ) : (ofRat (σ := σ) q).poly = X - C q :=
  (rfl)

@[simp]
theorem ofRat_region (q : ℚ) :
    (ofRat (σ := σ) q).region = .interval (NonemptyInterval.pure q) :=
  (rfl)

/-- The isolation of `z` by a squarefree annihilator `f` and a rational region containing `σ z`
in which `σ z` is the only complex root of `f`. -/
def ofSubset {f : ℚ[X]} (hf : Squarefree f) (hz : aeval z f = 0) (R : RationalRegion)
    (hmem : σ z ∈ R.toSet) (hR : R.toSet ⊆ {w | aeval w f = 0 → w = σ z}) :
    RootIsolation σ z :=
  ⟨f, hf, hz, R, hmem, hR⟩

@[simp]
theorem ofSubset_poly {f : ℚ[X]} (hf : Squarefree f) (hz : aeval z f = 0) (R : RationalRegion)
    (hmem : σ z ∈ R.toSet) (hR : R.toSet ⊆ {w | aeval w f = 0 → w = σ z}) :
    (ofSubset hf hz R hmem hR).poly = f :=
  (rfl)

@[simp]
theorem ofSubset_region {f : ℚ[X]} (hf : Squarefree f) (hz : aeval z f = 0) (R : RationalRegion)
    (hmem : σ z ∈ R.toSet) (hR : R.toSet ⊆ {w | aeval w f = 0 → w = σ z}) :
    (ofSubset hf hz R hmem hR).region = R :=
  (rfl)

/-- Shrinking the region of an isolation to a rational region that still contains `σ z` gives an
isolation by the same polynomial. -/
def restrict (D : RootIsolation σ z) (R : RationalRegion) (hmem : σ z ∈ R.toSet)
    (hR : R.toSet ⊆ D.region.toSet) : RootIsolation σ z :=
  ofSubset D.squarefree_poly D.aeval_poly R hmem fun w hw => D.eq_of_mem_region w (hR hw)

@[simp]
theorem restrict_poly (D : RootIsolation σ z) (R : RationalRegion) (hmem : σ z ∈ R.toSet)
    (hR : R.toSet ⊆ D.region.toSet) : (D.restrict R hmem hR).poly = D.poly :=
  (rfl)

@[simp]
theorem restrict_region (D : RootIsolation σ z) (R : RationalRegion) (hmem : σ z ∈ R.toSet)
    (hR : R.toSet ⊆ D.region.toSet) : (D.restrict R hmem hR).region = R :=
  (rfl)

/-- For every squarefree annihilator `f` of `z` and every neighbourhood `V` of `σ z`, there is an
isolation of `z` by `f` whose region is a closed disc `|w - (a + b i)| ≤ r` contained in `V`, with
`σ z` in its interior. -/
theorem exists_disc {f : ℚ[X]} (hf : Squarefree f) (hz : aeval z f = 0) {V : Set ℂ}
    (hV : V ∈ 𝓝 (σ z)) :
    ∃ (a b r : ℚ) (D : RootIsolation σ z), D.poly = f ∧ D.region = .disc a b r ∧
      dist (σ z) (a + b * I) < r ∧ D.region.toSet ⊆ V := by
  obtain ⟨a, b, r, hr, hsub⟩ := RationalRegion.exists_disc_subset
    (inter_mem hV (eventually_aeval_eq_zero_imp_eq hf.ne_zero (σ z)))
  rw [Set.subset_inter_iff] at hsub
  exact ⟨a, b, r, ofSubset hf hz _ (RationalRegion.mem_toSet_disc.mpr hr.le) hsub.2, rfl, rfl,
    hr, hsub.1⟩

/-- For every squarefree annihilator `f` of `z` and every neighbourhood `V` of `σ z`, there is an
isolation of `z` by `f` whose region is a rectangle `R × J` with rational sides contained in `V`,
with `σ z` in its interior. -/
theorem exists_box {f : ℚ[X]} (hf : Squarefree f) (hz : aeval z f = 0) {V : Set ℂ}
    (hV : V ∈ 𝓝 (σ z)) :
    ∃ (R J : NonemptyInterval ℚ) (D : RootIsolation σ z), D.poly = f ∧ D.region = .box R J ∧
      (σ z).re ∈ Set.Ioo (R.fst : ℝ) R.snd ∧ (σ z).im ∈ Set.Ioo (J.fst : ℝ) J.snd ∧
      D.region.toSet ⊆ V := by
  obtain ⟨R, J, hR, hJ, hsub⟩ := RationalRegion.exists_box_subset
    (inter_mem hV (eventually_aeval_eq_zero_imp_eq hf.ne_zero (σ z)))
  rw [Set.subset_inter_iff] at hsub
  exact ⟨R, J, ofSubset hf hz _ (RationalRegion.mem_toSet_box.mpr
    ⟨Set.Ioo_subset_Icc_self hR, Set.Ioo_subset_Icc_self hJ⟩) hsub.2, rfl, rfl, hR, hJ, hsub.1⟩

/-- For every squarefree annihilator `f` of `z` such that `σ z` is real, and every neighbourhood
`V` of `σ z`, there is an isolation of `z` by `f` whose region is a real interval with rational
endpoints contained in `V`, with `(σ z).re` strictly between its endpoints. -/
theorem exists_interval {f : ℚ[X]} (hf : Squarefree f) (hz : aeval z f = 0)
    (hreal : (σ z).im = 0) {V : Set ℂ} (hV : V ∈ 𝓝 (σ z)) :
    ∃ (J : NonemptyInterval ℚ) (D : RootIsolation σ z), D.poly = f ∧ D.region = .interval J ∧
      (σ z).re ∈ Set.Ioo (J.fst : ℝ) J.snd ∧ D.region.toSet ⊆ V := by
  obtain ⟨J, hJ, hsub⟩ := RationalRegion.exists_interval_subset hreal
    (inter_mem hV (eventually_aeval_eq_zero_imp_eq hf.ne_zero (σ z)))
  rw [Set.subset_inter_iff] at hsub
  exact ⟨J, ofSubset hf hz _ (RationalRegion.mem_toSet_interval.mpr
    ⟨hreal, Set.Ioo_subset_Icc_self hJ⟩) hsub.2, rfl, rfl, hJ, hsub.1⟩

variable (σ) in
/-- Every algebraic value has an isolation whose region lies in a prescribed neighbourhood of
`σ z`. -/
theorem exists_subset_of_isAlgebraic (hz : IsAlgebraic ℚ z) {V : Set ℂ} (hV : V ∈ 𝓝 (σ z)) :
    ∃ D : RootIsolation σ z, D.region.toSet ⊆ V := by
  have hint := hz.isIntegral
  obtain ⟨-, -, -, D, -, -, -, hD⟩ :=
    exists_disc (minpoly.irreducible hint).squarefree (minpoly.aeval ℚ z) hV
  exact ⟨D, hD⟩

variable (σ) in
/-- An element of `K` has a root isolation exactly when it is algebraic over `ℚ`. -/
theorem nonempty_iff_isAlgebraic : Nonempty (RootIsolation σ z) ↔ IsAlgebraic ℚ z :=
  ⟨fun ⟨D⟩ => D.isAlgebraic, fun hz =>
    ⟨(exists_subset_of_isAlgebraic σ hz Filter.univ_mem).choose⟩⟩

variable (σ) in
/-- Every algebraic value has isolations of arbitrarily small diameter. -/
theorem exists_diam_lt (hz : IsAlgebraic ℚ z) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : RootIsolation σ z, diam D.region.toSet < ε := by
  obtain ⟨D, hD⟩ := exists_subset_of_isAlgebraic σ hz (ball_mem_nhds (σ z) (by positivity :
    0 < ε / 3))
  refine ⟨D, (diam_mono hD isBounded_ball).trans_lt ?_⟩
  linarith [diam_ball (x := σ z) (by positivity : 0 ≤ ε / 3)]

variable (σ) in
/-- Finitely many algebraic values have isolations whose regions are pairwise disjoint. -/
theorem exists_pairwise_disjoint (s : Finset K) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    ∃ D : (z : s) → RootIsolation σ z, Pairwise (Disjoint on fun z => (D z).region.toSet) := by
  obtain ⟨U, hU, hdisj⟩ := ((s : Set K).image σ).toFinite.t2_separation
  choose D hD using fun z : s => exists_subset_of_isAlgebraic σ (hs z z.property)
    ((hU _).2.mem_nhds (hU _).1)
  exact ⟨D, fun z z' hne => (hdisj (Set.mem_image_of_mem σ z.property)
    (Set.mem_image_of_mem σ z'.property) (σ.injective.ne (Subtype.coe_ne_coe.mpr hne))).mono
    (hD z) (hD z')⟩

/-- Exact equality test: two isolated values are equal if and only if the gcd of their isolating
polynomials has a complex root in the intersection of their regions. -/
theorem eq_iff_exists_aeval_gcd_eq_zero (D : RootIsolation σ z) (D' : RootIsolation σ z') :
    z = z' ↔ ∃ w ∈ D.region.toSet ∩ D'.region.toSet,
      aeval w (EuclideanDomain.gcd D.poly D'.poly) = 0 := by
  constructor
  · rintro rfl
    refine ⟨σ z, ⟨D.mem_region, D'.mem_region⟩, ?_⟩
    rw [EuclideanDomain.gcd_eq_gcd_ab]
    simp
  · rintro ⟨w, ⟨hw, hw'⟩, h0⟩
    apply σ.injective
    rw [← D.eq_of_mem_region w hw (aeval_eq_zero_of_dvd_aeval_eq_zero
      (EuclideanDomain.gcd_dvd_left _ _) h0), D'.eq_of_mem_region w hw'
      (aeval_eq_zero_of_dvd_aeval_eq_zero (EuclideanDomain.gcd_dvd_right _ _) h0)]

end RootIsolation

/-! ### Examples

The following checks illustrate the conventions. The interval `[1, 3/2]` isolates `√2` as a root
of `X² - 2` and excludes the other root `-√2`; the discs of radius `1/2` about `i` and `-i` isolate
`i` and `-i` as roots of `X² + 1`; `X - 3` with `[3, 3]` isolates `3` with diameter `0`; the
interval `[1, 2]` isolates both `√2` and `√3`, so overlapping regions do not prove equality; and
`1/√2` is isolated as a root of `2X² - 1` by the positive interval `[1/2, 1]`. -/

namespace RootIsolation

/-- An isolation of a positive real `t` with `t² = a` by any polynomial whose complex roots are
the square roots of `a`, and a rational interval of positive numbers containing `t`. -/
private noncomputable def ofSq (g : ℚ[X]) (hg : Squarefree g) (a : ℚ)
    (hroot : ∀ w : ℂ, aeval w g = 0 ↔ w ^ 2 = a) {t : ℝ} (ht : 0 < t) (hta : t ^ 2 = a)
    (J : NonemptyInterval ℚ) (hJ : 0 < J.fst) (hl : (J.fst : ℝ) ≤ t) (hu : t ≤ J.snd) :
    RootIsolation (RingHom.id ℂ) (t : ℂ) where
  poly := g
  squarefree_poly := hg
  aeval_poly := (hroot _).2 (by exact_mod_cast hta)
  region := .interval J
  mem_region := RationalRegion.mem_toSet_interval.mpr ⟨by simp, by simp [hl, hu]⟩
  eq_of_mem_region w hw h0 := by
    rw [RationalRegion.mem_toSet_interval] at hw
    have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hw.1])
    have h2 : w.re ^ 2 = t ^ 2 := by
      rw [hw'] at h0
      rw [hta]
      exact_mod_cast (hroot _).1 h0
    have hpos : 0 ≤ w.re := le_trans (by exact_mod_cast hJ.le) hw.2.1
    rw [RingHom.id_apply, hw', (pow_left_inj₀ hpos ht.le two_ne_zero).1 h2]

private theorem aeval_X_sq_sub_C_eq_zero_iff (a : ℚ) (w : ℂ) :
    aeval w (X ^ 2 - C a) = 0 ↔ w ^ 2 = a := by
  simp [sub_eq_zero]

private theorem squarefree_X_sq_sub_C {a : ℚ} (ha : a ≠ 0) : Squarefree (X ^ 2 - C a) :=
  (separable_X_pow_sub_C a (by norm_num) ha).squarefree

/-- `[1, 3/2]` isolates `√2` as a root of `X² - 2`. -/
private noncomputable def sqrtTwo : RootIsolation (RingHom.id ℂ) (√2 : ℝ) :=
  ofSq _ (squarefree_X_sq_sub_C two_ne_zero) 2 (aeval_X_sq_sub_C_eq_zero_iff 2)
    (by positivity) (by simp) ⟨(1, 3 / 2), by norm_num⟩ (by norm_num)
    (by simp) ((Real.sqrt_le_left (by norm_num)).2 (by norm_num))

example : sqrtTwo.poly = X ^ 2 - C 2 ∧ aeval (-(√2 : ℝ) : ℂ) sqrtTwo.poly = 0 ∧
    (-(√2 : ℝ) : ℂ) ∉ sqrtTwo.region.toSet := by
  refine ⟨rfl, ?_, ?_⟩
  · refine (aeval_X_sq_sub_C_eq_zero_iff 2 _).2 ?_
    rw [neg_sq, ← ofReal_pow, Real.sq_sqrt zero_le_two]
    norm_num
  · simp only [sqrtTwo, ofSq, RationalRegion.mem_toSet_interval, Set.mem_Icc, not_and]
    intro _ h
    have : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg 2
    simp only [neg_re, ofReal_re] at h
    norm_num at h
    linarith

/-- The disc of radius `1/2` about `b i` isolates `z = b i` as a root of `X² + 1`, for
`b = ± 1`. -/
private noncomputable def ofI (b : ℚ) (hb : b ^ 2 = 1) (z : ℂ) (hz : (b : ℂ) * I = z) :
    RootIsolation (RingHom.id ℂ) z :=
  have hb' : (b : ℂ) ^ 2 = 1 := by exact_mod_cast hb
  { poly := X ^ 2 + 1
    squarefree_poly := by
      simpa using squarefree_X_sq_sub_C (a := -1) (by norm_num)
    aeval_poly := by simp [← hz, mul_pow, hb']
    region := .disc 0 b (1 / 2)
    mem_region := by simp [← hz]
    eq_of_mem_region w hw h0 := by
      simp only [map_add, map_pow, aeval_X, map_one] at h0
      have hprod : (w - b * I) * (w + b * I) = 0 := by
        linear_combination h0 - I ^ 2 * hb' - Complex.I_sq
      rcases mul_eq_zero.mp hprod with h | h
      · rw [RingHom.id_apply, ← hz, sub_eq_zero.mp h]
      · have hb1 : |(b : ℝ)| = 1 := by
          simpa using (sq_eq_sq_iff_abs_eq_abs (b : ℝ) 1).1 (by exact_mod_cast hb)
        have hdist : ‖-((b : ℂ) * I) - (((0 : ℚ) : ℂ) + b * I)‖ = 2 := by
          rw [show -((b : ℂ) * I) - (((0 : ℚ) : ℂ) + b * I) = -(2 * ((b : ℝ) : ℂ) * I) by
            push_cast; ring]
          simp [hb1]
        rw [eq_neg_of_add_eq_zero_left h, RationalRegion.mem_toSet_disc, Complex.dist_eq,
          hdist] at hw
        norm_num at hw }

/-- The discs of radius `1/2` about `i` and `-i` isolate `i` and `-i` as roots of `X² + 1`. -/
example : ∃ (D : RootIsolation (RingHom.id ℂ) I) (D' : RootIsolation (RingHom.id ℂ) (-I)),
    D.poly = X ^ 2 + 1 ∧ D.region = .disc 0 1 (1 / 2) ∧
      D'.poly = X ^ 2 + 1 ∧ D'.region = .disc 0 (-1) (1 / 2) :=
  ⟨ofI 1 (by norm_num) I (by simp), ofI (-1) (by norm_num) (-I) (by simp), rfl, rfl, rfl, rfl⟩

/-- `X - 3` with the singleton interval `[3, 3]` isolates `3`, with diameter `0`. -/
example : (ofRat (σ := RingHom.id ℂ) 3).poly = X - C 3 ∧
    diam (ofRat (σ := RingHom.id ℂ) 3).region.toSet = 0 := by
  simp [RationalRegion.diam_toSet_interval]

/-- The interval `[1, 2]` isolates both `√2` (as a root of `X² - 2`) and `√3` (as a root of
`X² - 3`): overlapping, even identical, regions do not prove equality. -/
example : ∃ (D : RootIsolation (RingHom.id ℂ) (√2 : ℝ))
    (D' : RootIsolation (RingHom.id ℂ) (√3 : ℝ)),
    D.region = D'.region ∧ ((√2 : ℝ) : ℂ) ≠ (√3 : ℝ) := by
  refine ⟨ofSq _ (squarefree_X_sq_sub_C two_ne_zero) 2 (aeval_X_sq_sub_C_eq_zero_iff 2)
    (by positivity) (by simp) ⟨(1, 2), by norm_num⟩ (by norm_num) (by simp)
    ((Real.sqrt_le_left (by norm_num)).2 (by norm_num)),
    ofSq _ (squarefree_X_sq_sub_C three_ne_zero) 3 (aeval_X_sq_sub_C_eq_zero_iff 3)
    (by positivity) (by simp) ⟨(1, 2), by norm_num⟩ (by norm_num) (by simp)
    ((Real.sqrt_le_left (by norm_num)).2 (by norm_num)), rfl, ?_⟩
  rw [Ne, ofReal_inj, Real.sqrt_inj (by norm_num) (by norm_num)]
  norm_num

/-- The positive interval `[1/2, 1]` isolates `1/√2` as a root of `2X² - 1`. -/
example : ∃ D : RootIsolation (RingHom.id ℂ) ((√2)⁻¹ : ℝ),
    D.poly = C 2 * X ^ 2 - 1 ∧ D.region = .interval ⟨(1 / 2, 1), by norm_num⟩ := by
  have hpoly : (C 2 * X ^ 2 - 1 : ℚ[X]) = C 2 * (X ^ 2 - C (1 / 2)) := by
    rw [mul_sub, ← C_mul]
    norm_num
  have hsq : Squarefree (C 2 * X ^ 2 - 1 : ℚ[X]) := by
    rw [hpoly]
    exact (Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr two_ne_zero))
      (separable_X_pow_sub_C (n := 2) (1 / 2 : ℚ) (by norm_num) (by norm_num))).squarefree
  have hroot (w : ℂ) : aeval w (C 2 * X ^ 2 - 1 : ℚ[X]) = 0 ↔ w ^ 2 = ((1 / 2 : ℚ) : ℂ) := by
    simp only [map_sub, map_mul, map_pow, aeval_X, map_one, map_ofNat]
    push_cast
    constructor <;> intro h
    · linear_combination h / 2
    · linear_combination 2 * h
  refine ⟨ofSq _ hsq (1 / 2) hroot (by positivity) ?_ _ (by norm_num) ?_ ?_, rfl, rfl⟩
  · rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  · have h2 : √2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
    simpa using inv_anti₀ (by positivity) h2
  · have h1 : 1 ≤ √2 := by simp
    simpa using inv_le_one_of_one_le₀ h1

/-- The sum, the product and the inverse of isolated values are isolated, inside any prescribed
neighbourhood of their images. -/
example {K : Type*} [Field K] [Algebra ℚ K] {σ : K →+* ℂ} {z z' : K} (D : RootIsolation σ z)
    (D' : RootIsolation σ z') {V : Set ℂ} (hV : V ∈ 𝓝 (σ (z + z')))
    (hV' : V ∈ 𝓝 (σ (z * z'))) (hV'' : V ∈ 𝓝 (σ z⁻¹)) :
    (∃ E : RootIsolation σ (z + z'), E.region.toSet ⊆ V) ∧
      (∃ E : RootIsolation σ (z * z'), E.region.toSet ⊆ V) ∧
      ∃ E : RootIsolation σ z⁻¹, E.region.toSet ⊆ V :=
  ⟨exists_subset_of_isAlgebraic σ (D.isAlgebraic.add D'.isAlgebraic) hV,
    exists_subset_of_isAlgebraic σ (D.isAlgebraic.mul D'.isAlgebraic) hV',
    exists_subset_of_isAlgebraic σ D.isAlgebraic.inv hV''⟩

end RootIsolation

end TauCeti
