/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.MultipleRoots.Submanifold
public import TauCeti.Geometry.RealAlgebraic.SignInvariant
public import TauCeti.Geometry.RealAlgebraic.Stack.Basic
public import TauCeti.RingTheory.MvPolynomial.Lazard.Lift
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Lazard delineations

Let `F k`, for `k` in an index type `ι`, be real polynomials in the variables `X₀, …, Xₙ`, with
the last variable `Xₙ` distinguished, and let `S ⊆ ℝⁿ` be a set of base points. Moving `Xₙ`
into the coefficients turns `F k` into a polynomial in `X₀, …, Xₙ₋₁` with coefficients in `ℝ[Xₙ]`,
whose Lazard evaluation over `α ∈ S` is a univariate polynomial; for `F k ≠ 0` it is nonzero,
even where the ordinary fibre `F k (α, Xₙ)` vanishes identically. A *Lazard delineation* of the
family over a nonempty `S` is a common stack of the real roots of these Lazard evaluations:
continuous functions `θ₀ < ⋯ < θₘ₋₁` on `S` such that

* the vector of base exponents removed by Lazard evaluation of each member is the same at every
  point of `S`;
* the roots of the Lazard evaluation of every nonzero member are among the values `θᵢ α`, every
  `θᵢ` is a root of some member, and the multiplicity of `θᵢ α` as a root of the Lazard evaluation
  of each member does not depend on `α`.

Unlike an ordinary delineation (`TauCeti.Delineation`), nothing is asked of the ordinary fibres:
members may be nullified at some points of `S`, and the degrees of the Lazard evaluations may
change along `S`.

By `MvPolynomial.lazardValuation_snoc`, the Lazard valuation of a nonzero member at a point
`(α, β)` is the removed base exponent vector over `α` followed by the multiplicity of `β` as a
root of the Lazard evaluation over `α`. Over a Lazard delineation it is therefore constant on
every section, where it ends with the multiplicity of the section, and on every sector, where it
ends with `0`. Since a polynomial vanishes exactly where its Lazard valuation is positive, each
member is then sign-invariant on every section and sector over a preconnected base.

Where the removed exponents are constant, the coefficients of the Lazard evaluations are
polynomial functions of the base point. So over an analytic submanifold of `ℝⁿ` the root
functions of a Lazard delineation are analytic: their multiplicities are constant and positive.
In other words, every Lazard delineation over an analytic submanifold is an analytic one.

## Main declarations

* `TauCeti.LazardDelineation`: a common stack of the roots of the Lazard evaluations of a family.
* `TauCeti.LazardDelineation.lazardValuation_snoc_of_mem_sectionSet`,
  `TauCeti.LazardDelineation.lazardValuation_snoc_of_mem_sectorSet`: the Lazard valuations of a
  nonzero member on a section and on a sector.
* `TauCeti.LazardDelineation.lazardValuation_snoc_eq_of_mem_sectionSet`,
  `TauCeti.LazardDelineation.lazardValuation_snoc_eq_of_mem_sectorSet`: every member is Lazard
  valuation-invariant on each section and each sector.
* `TauCeti.LazardDelineation.signInvariant_sectionSet`,
  `TauCeti.LazardDelineation.signInvariant_sectorSet`: over a preconnected base, every member is
  sign-invariant on each section and each sector.
* `TauCeti.LazardDelineation.analyticOnSubmanifold_root`: over an analytic submanifold, the root
  functions are analytic.

## References

* D. Lazard, *An improved projection for cylindrical algebraic decomposition*, in *Algebraic
  Geometry and its Applications*, Springer (1994), 467–476.
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 2 (Lazard
  delineability and valuation-invariance in sections and sectors).
-/

public section

open MvPolynomial Set Filter Topology

namespace TauCeti

variable {ι : Type*} {n : ℕ}

/-- A *Lazard delineation* of a family `F k` of real polynomials in `n + 1` variables over a
nonempty set `S ⊆ ℝⁿ` of base points. Move the last variable into the coefficients and
Lazard-evaluate the base variables at `α ∈ S`. A Lazard delineation is a common stack of the
roots of the resulting univariate polynomials: continuous functions
`root 0 < ⋯ < root (count - 1)` on `S` such that the removed base exponents of each member are a
constant `exponent k`, the roots of each nonzero member are among the `root i α`, each `root i` is
a root of some member, and the multiplicity of `root i α` as a root of the Lazard evaluation of
`F k` is a constant `multiplicity k i`. -/
structure LazardDelineation (F : ι → MvPolynomial (Fin (n + 1)) ℝ) (S : Set (Fin n → ℝ)) where
  /-- The base is nonempty, so that `exponent` and `multiplicity` are determined by the roots. -/
  nonempty : S.Nonempty
  /-- The number of sections of the stack. -/
  count : ℕ
  /-- The root functions, listed in increasing order. -/
  root : Fin count → S → ℝ
  /-- Each root function is continuous. -/
  continuous_root (i : Fin count) : Continuous (root i)
  /-- At each point the root functions are strictly increasing in their index. -/
  strictMono_root (x : S) : StrictMono fun i ↦ root i x
  /-- The vector of base exponents removed by Lazard evaluation of the `k`-th member. -/
  exponent : ι → Fin n →₀ ℕ
  /-- The base exponents removed by Lazard evaluation of `F k` over `x` are `exponent k` at
  every `x`. -/
  lazardExponent_eq (k : ι) (x : S) :
    (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardExponent
      (Polynomial.C ∘ x.1) = exponent k
  /-- The multiplicity of the `i`-th root function as a root of the Lazard evaluation of the
  `k`-th member. -/
  multiplicity : ι → Fin count → ℕ
  /-- The multiplicity of `root i x` as a root of the Lazard evaluation of `F k` over `x` is
  `multiplicity k i` at every `x`. -/
  rootMultiplicity_root (k : ι) (i : Fin count) (x : S) :
    ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ x.1)).rootMultiplicity (root i x) = multiplicity k i
  /-- Every root of the Lazard evaluation of a nonzero member is the value of a root function. -/
  exists_root_eq (k : ι) (x : S) : F k ≠ 0 → ∀ t,
    ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ x.1)).IsRoot t → ∃ i, root i x = t
  /-- Every root function is a root of some member. -/
  exists_multiplicity_pos (i : Fin count) : ∃ k, 0 < multiplicity k i

namespace LazardDelineation

variable {F : ι → MvPolynomial (Fin (n + 1)) ℝ} {S : Set (Fin n → ℝ)} (D : LazardDelineation F S)

/-- A Lazard delineation is determined by its root functions: the removed base exponents and the
multiplicities can be read off at any point of the nonempty base. -/
@[ext (iff := false)]
theorem ext {D₁ D₂ : LazardDelineation F S} (hcount : D₁.count = D₂.count)
    (hroot : ∀ i x, D₁.root i x = D₂.root (Fin.cast hcount i) x) : D₁ = D₂ := by
  cases D₁ with | mk hS c r _ _ e he m hm _ _ =>
  cases D₂ with | mk _ c' r' _ _ e' he' m' hm' _ _ =>
  obtain ⟨x, hx⟩ := hS
  dsimp only at hcount hroot
  subst hcount
  obtain rfl : r = r' := funext₂ hroot
  obtain rfl : e = e' := funext fun k ↦ (he k ⟨x, hx⟩).symm.trans (he' k ⟨x, hx⟩)
  obtain rfl : m = m' := funext₂ fun k i ↦ (hm k i ⟨x, hx⟩).symm.trans (hm' k i ⟨x, hx⟩)
  rfl

/-- On a sector of a Lazard delineation, the fibre coordinate is not a root of the Lazard
evaluation of any member over the base point. -/
theorem rootMultiplicity_eq_zero_of_mem_sectorSet (k : ι) {j : Fin (D.count + 1)} {z : S × ℝ}
    (hz : z ∈ sectorSet D.root j) :
    ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
      (Polynomial.C ∘ z.1.1)).rootMultiplicity z.2 = 0 := by
  by_cases hk : F k = 0
  · simp [hk]
  refine Polynomial.rootMultiplicity_eq_zero fun ht ↦ ?_
  obtain ⟨i, hi⟩ := D.exists_root_eq k z.1 hk z.2 ht
  exact disjoint_left.1 (disjoint_sectionSet_sectorSet D.root i j) (mem_sectionSet.2 hi) hz

/-- **Lazard valuations on a section.** At every point of the `i`-th section of a Lazard
delineation, the Lazard valuation of a nonzero member `F k` is its removed base exponent vector
followed by the multiplicity of the section as a root of its Lazard evaluation. -/
theorem lazardValuation_snoc_of_mem_sectionSet {k : ι} (hk : F k ≠ 0) {i : Fin D.count}
    {z : S × ℝ} (hz : z ∈ sectionSet D.root i) :
    (F k).lazardValuation (Fin.snoc z.1.1 z.2) =
      toLex (Finsupp.snoc (D.exponent k) (D.multiplicity k i)) := by
  rw [lazardValuation_snoc hk, D.lazardExponent_eq, ← mem_sectionSet.1 hz,
    D.rootMultiplicity_root]

/-- **Lazard valuations on a sector.** At every point of a sector of a Lazard delineation, the
Lazard valuation of a nonzero member `F k` is its removed base exponent vector followed by `0`. -/
theorem lazardValuation_snoc_of_mem_sectorSet {k : ι} (hk : F k ≠ 0) {j : Fin (D.count + 1)}
    {z : S × ℝ} (hz : z ∈ sectorSet D.root j) :
    (F k).lazardValuation (Fin.snoc z.1.1 z.2) = toLex (Finsupp.snoc (D.exponent k) 0) := by
  rw [lazardValuation_snoc hk, D.lazardExponent_eq,
    D.rootMultiplicity_eq_zero_of_mem_sectorSet k hz]

/-- Every member of a family is Lazard valuation-invariant on each section of a Lazard
delineation. -/
theorem lazardValuation_snoc_eq_of_mem_sectionSet (k : ι) {i : Fin D.count} {z z' : S × ℝ}
    (hz : z ∈ sectionSet D.root i) (hz' : z' ∈ sectionSet D.root i) :
    (F k).lazardValuation (Fin.snoc z.1.1 z.2) = (F k).lazardValuation (Fin.snoc z'.1.1 z'.2) := by
  obtain hk | hk := eq_or_ne (F k) 0
  · simp [hk]
  · rw [D.lazardValuation_snoc_of_mem_sectionSet hk hz,
      D.lazardValuation_snoc_of_mem_sectionSet hk hz']

/-- Every member of a family is Lazard valuation-invariant on each sector of a Lazard
delineation. -/
theorem lazardValuation_snoc_eq_of_mem_sectorSet (k : ι) {j : Fin (D.count + 1)} {z z' : S × ℝ}
    (hz : z ∈ sectorSet D.root j) (hz' : z' ∈ sectorSet D.root j) :
    (F k).lazardValuation (Fin.snoc z.1.1 z.2) = (F k).lazardValuation (Fin.snoc z'.1.1 z'.2) := by
  obtain hk | hk := eq_or_ne (F k) 0
  · simp [hk]
  · rw [D.lazardValuation_snoc_of_mem_sectorSet hk hz,
      D.lazardValuation_snoc_of_mem_sectorSet hk hz']

/-- Over a preconnected base, every member of a family is sign-invariant on each section of a
Lazard delineation. -/
theorem signInvariant_sectionSet (hS : IsPreconnected S) (k : ι) (i : Fin D.count) :
    SignInvariant (fun z : S × ℝ ↦ eval (Fin.snoc z.1.1 z.2) (F k)) (sectionSet D.root i) := by
  have := isPreconnected_iff_preconnectedSpace.1 hS
  refine (isPreconnected_sectionSet (D.continuous_root i)).signInvariant_of_eq_zero_iff
    ((continuous_eval (F k)).comp ((continuous_subtype_val.comp continuous_fst).finSnoc
      (A := fun _ ↦ ℝ) continuous_snd)).continuousOn fun z hz z' hz' ↦ ?_
  rw [← lazardValuation_pos_iff, ← lazardValuation_pos_iff,
    D.lazardValuation_snoc_eq_of_mem_sectionSet k hz hz']

/-- Over a preconnected base, every member of a family is sign-invariant on each sector of a
Lazard delineation. -/
theorem signInvariant_sectorSet (hS : IsPreconnected S) (k : ι) (j : Fin (D.count + 1)) :
    SignInvariant (fun z : S × ℝ ↦ eval (Fin.snoc z.1.1 z.2) (F k)) (sectorSet D.root j) := by
  have := isPreconnected_iff_preconnectedSpace.1 hS
  refine (isPreconnected_sectorSet D.continuous_root D.strictMono_root j
    ).signInvariant_of_eq_zero_iff
    ((continuous_eval (F k)).comp ((continuous_subtype_val.comp continuous_fst).finSnoc
      (A := fun _ ↦ ℝ) continuous_snd)).continuousOn fun z hz z' hz' ↦ ?_
  rw [← lazardValuation_pos_iff, ← lazardValuation_pos_iff,
    D.lazardValuation_snoc_eq_of_mem_sectorSet k hz hz']

/-- **Lazard delineations over analytic submanifolds are analytic.** Over an analytic
submanifold `S`, the root functions of a Lazard delineation are analytic on `S`. Any ambient
function agreeing with a root function on `S` gives the same conclusion. -/
theorem analyticOnSubmanifold_root {d : ℕ} (hS : IsAnalyticSubmanifold d S) (i : Fin D.count)
    {r : (Fin n → ℝ) → ℝ} (hr : ∀ x : S, r x = D.root i x) : AnalyticOnSubmanifold d r S := by
  obtain ⟨k, hk⟩ := D.exists_multiplicity_pos i
  -- Over `S` the coefficients of the Lazard evaluations of `F k` are fixed Taylor coefficients,
  -- polynomial in the base point.
  let c (j : ℕ) : MvPolynomial (Fin (n + 1)) ℝ :=
    (taylor (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℝ) (map C (F k))).coeff
      (Finsupp.snoc (D.exponent k) j)
  have hcoeff (x : S) (j : ℕ) :
      ((optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval
        (Polynomial.C ∘ x.1)).coeff j = eval (Fin.snoc x.1 0) (c j) := by
    rw [coeff_lazardEval_optionEquivRight_rename_finSuccEquivLast, D.lazardExponent_eq,
      eval_coeff_taylor_map_C]
  refine hS.analyticOnSubmanifold_of_rootMultiplicity_eq (F := fun x ↦
      (optionEquivRight ℝ (Fin n) (rename finSuccEquivLast (F k))).lazardEval (Polynomial.C ∘ x))
    (fun j ↦ ?_) (fun x _ ↦ ?_) ?_
    fun x _ ↦ ⟨D.multiplicity k i, hk, eventually_nhdsWithin_of_forall fun y hy ↦ ?_⟩
  · have hsnoc (l : Fin (n + 1)) :
        AnalyticOnNhd ℝ (fun x : Fin n → ℝ ↦ Fin.snoc (α := fun _ ↦ ℝ) x 0 l) univ := by
      cases l using Fin.lastCases with
      | last => simpa using analyticOnNhd_const
      | cast l =>
        simp only [Fin.snoc_castSucc]
        exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) l).analyticOnNhd univ
    refine ((AnalyticOnNhd.aeval_mvPolynomial hsnoc (c j)).mono (subset_univ S)
      |>.analyticOnSubmanifold hS).congr fun x hx ↦ ?_
    simp only [hcoeff ⟨x, hx⟩ j, aeval_eq_eval]
  · -- the degree in the last variable bounds the degrees of all Lazard evaluations
    refine ⟨(F k).degreeOf (Fin.last n), eventually_nhdsWithin_of_forall fun y _ ↦ ?_⟩
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun j hj ↦ ?_
    rw [coeff_lazardEval_optionEquivRight_rename_finSuccEquivLast, ← notMem_support_iff]
    refine notMem_support_of_degreeOf_lt (Fin.last n) ?_
    rwa [degreeOf_taylor, Finsupp.snoc_last]
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (D.continuous_root i).congr fun x ↦ (hr x).symm
  · rw [hr ⟨y, hy⟩]
    exact D.rootMultiplicity_root k i ⟨y, hy⟩

end LazardDelineation

end TauCeti
