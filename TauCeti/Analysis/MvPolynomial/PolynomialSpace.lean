/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.RingTheory.MvPolynomial.RestrictTotalDegree
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.FieldTheory.Finite.Polynomial
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Analysis.MvPolynomial.Jacobian

/-!
# Bounded-degree polynomial functions on Euclidean space

`TauCeti.polynomialsDegLE ι m` is the subspace of real functions on `EuclideanSpace ℝ ι`
represented by multivariate polynomials of total degree at most `m`. Evaluation is injective,
so this space is linearly equivalent to the corresponding formal polynomial space and has
dimension `(m + Fintype.card ι).choose (Fintype.card ι)`.

These are functions on the whole Euclidean space, before restriction to a domain or passage
to almost-everywhere classes. In particular, degree zero means exactly the constant functions,
also when the coordinate type is empty.

Evaluating a real multilinear map on the diagonal gives a polynomial function of degree at most
the number of its arguments (`MultilinearMap.apply_const_mem_polynomialsDegLE`), and hence every
partial sum of a real formal multilinear series belongs to `polynomialsDegLE ι (N - 1)`
(`FormalMultilinearSeries.partialSum_mem_polynomialsDegLE`). Polynomial functions of bounded degree
are closed under pointwise products (`TauCeti.mul_mem_polynomialsDegLE`,
`TauCeti.finset_prod_mem_polynomialsDegLE`, `TauCeti.prod_coord_mem_polynomialsDegLE`).

The file also develops the foundational calculus of these polynomial functions on
`EuclideanSpace ℝ ι`:

* Every function in `polynomialsDegLE ι m` is real-analytic on `EuclideanSpace ℝ ι`, hence `C^n`
  for every `n` (`MvPolynomial.analyticOnNhd_polynomialEvalₗ`,
  `MvPolynomial.contDiff_polynomialEvalₗ`, `TauCeti.analyticOnNhd_of_mem_polynomialsDegLE`,
  `TauCeti.contDiff_of_mem_polynomialsDegLE`).
* Two polynomial functions agreeing on a nonempty open set, or almost everywhere there with respect
  to an open-positive measure, agree everywhere on `EuclideanSpace ℝ ι`
  (`TauCeti.polynomialEvalₗ_eq_of_eqOn_isOpen`,
  `TauCeti.eq_of_mem_polynomialsDegLE_of_eqOn_isOpen`,
  `TauCeti.eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen`).
* Coordinate and directional Fréchet derivatives and gradients of `polynomialEvalₗ ι p` agree with
  the evaluated formal partial derivatives (`MvPolynomial.fderiv_polynomialEvalₗ_single`,
  `MvPolynomial.fderiv_polynomialEvalₗ_apply`, `MvPolynomial.gradient_polynomialEvalₗ`);
  directional differentiation lowers the degree bound by at most one
  (`TauCeti.fderiv_apply_mem_polynomialsDegLE`), and every iterated Fréchet derivative of order
  strictly exceeding `m` vanishes identically
  (`TauCeti.iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE`).

The construction uses Mathlib's `MvPolynomial.evalₗ`, `MvPolynomial.funext`, and
`AnalyticOnNhd.eval_continuousLinearMap`, together with `TauCeti.finrank_restrictTotalDegree`,
`MvPolynomial.totalDegree_pderiv_le`, and the Euclidean polynomial derivative formulas from
`TauCeti.Analysis.MvPolynomial.Jacobian`.
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial

section Basic

variable (ι : Type*)

/-- Evaluate a real multivariate polynomial on Euclidean coordinates, linearly in the
polynomial. -/
def polynomialEvalₗ : MvPolynomial ι ℝ →ₗ[ℝ] (EuclideanSpace ℝ ι → ℝ) :=
  (LinearMap.funLeft ℝ ℝ (EuclideanSpace.equiv ι ℝ)).comp (MvPolynomial.evalₗ ℝ ι)

@[simp]
theorem polynomialEvalₗ_apply (p : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    polynomialEvalₗ ι p x = eval (fun i ↦ x i) p :=
  (rfl)

/-- Evaluation on the whole Euclidean space determines a formal polynomial uniquely. -/
theorem polynomialEvalₗ_injective : Function.Injective (polynomialEvalₗ ι) := by
  intro p q h
  apply MvPolynomial.funext
  intro x
  have hx := congrFun h ((EuclideanSpace.equiv ι ℝ).symm x)
  simpa only [polynomialEvalₗ_apply, PiLp.continuousLinearEquiv_symm_apply,
    PiLp.toLp_apply] using hx

/-- The subspace of real polynomial functions of total degree at most `m`. -/
def polynomialsDegLE (m : ℕ) : Submodule ℝ (EuclideanSpace ℝ ι → ℝ) :=
  (restrictTotalDegree ι ℝ m).map (polynomialEvalₗ ι)

/-- The polynomial function space is the image of formal bounded-degree polynomials. -/
theorem polynomialsDegLE_def (m : ℕ) :
    polynomialsDegLE ι m = (restrictTotalDegree ι ℝ m).map (polynomialEvalₗ ι) :=
  (rfl)

/-- Membership is precisely representability by a polynomial of bounded total degree. -/
theorem mem_polynomialsDegLE_iff {m : ℕ} {f : EuclideanSpace ℝ ι → ℝ} :
    f ∈ polynomialsDegLE ι m ↔
      ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ m ∧ polynomialEvalₗ ι p = f := by
  simp only [polynomialsDegLE_def, Submodule.mem_map, mem_restrictTotalDegree]

/-- Evaluating a formal polynomial belongs to the function space exactly at its degree
and above. -/
@[simp]
theorem polynomialEvalₗ_mem_polynomialsDegLE_iff (m : ℕ) (p : MvPolynomial ι ℝ) :
    polynomialEvalₗ ι p ∈ polynomialsDegLE ι m ↔ p.totalDegree ≤ m := by
  rw [mem_polynomialsDegLE_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    exact polynomialEvalₗ_injective ι h ▸ hq
  · exact fun hp ↦ ⟨p, hp, rfl⟩

/-- Increasing the total-degree bound enlarges the polynomial function space. -/
theorem polynomialsDegLE_mono : Monotone (polynomialsDegLE ι) :=
  fun _ _ h ↦ Submodule.map_mono (restrictTotalDegree_mono ι ℝ h)

/-- Formal bounded-degree polynomials and the functions they represent are linearly
equivalent. -/
def restrictTotalDegreeEquivPolynomialsDegLE (m : ℕ) :
    restrictTotalDegree ι ℝ m ≃ₗ[ℝ] polynomialsDegLE ι m :=
  Submodule.equivMapOfInjective (polynomialEvalₗ ι) (polynomialEvalₗ_injective ι) _

@[simp]
theorem coe_restrictTotalDegreeEquivPolynomialsDegLE (m : ℕ) (p : restrictTotalDegree ι ℝ m) :
    (restrictTotalDegreeEquivPolynomialsDegLE ι m p : EuclideanSpace ℝ ι → ℝ) =
      polynomialEvalₗ ι p :=
  (rfl)

@[simp]
theorem polynomialEvalₗ_restrictTotalDegreeEquivPolynomialsDegLE_symm (m : ℕ)
    (f : polynomialsDegLE ι m) :
    polynomialEvalₗ ι ((restrictTotalDegreeEquivPolynomialsDegLE ι m).symm f) = f :=
  Submodule.map_equivMapOfInjective_symm_apply _ _ _ _

@[simp]
theorem polynomialEvalₗ_C (c : ℝ) :
    polynomialEvalₗ ι (C c) = fun _ ↦ c := by
  ext x
  simp

@[simp]
theorem polynomialEvalₗ_X (i : ι) :
    polynomialEvalₗ ι (X i) = fun x ↦ x i := by
  ext x
  simp

/-- Every constant function belongs to every nonnegative degree bound. -/
@[simp]
theorem const_mem_polynomialsDegLE (m : ℕ) (c : ℝ) :
    (fun _ : EuclideanSpace ℝ ι ↦ c) ∈ polynomialsDegLE ι m := by
  rw [← polynomialEvalₗ_C ι c, polynomialEvalₗ_mem_polynomialsDegLE_iff]
  simp

/-- A coordinate function belongs exactly when the degree bound is positive. -/
@[simp]
theorem coordinate_mem_polynomialsDegLE_iff (m : ℕ) (i : ι) :
    (fun x : EuclideanSpace ℝ ι ↦ x i) ∈ polynomialsDegLE ι m ↔ 1 ≤ m := by
  rw [← polynomialEvalₗ_X ι i, polynomialEvalₗ_mem_polynomialsDegLE_iff, totalDegree_X]

/-- Degree-zero polynomial functions are exactly the constant functions. -/
theorem mem_polynomialsDegLE_zero_iff {f : EuclideanSpace ℝ ι → ℝ} :
    f ∈ polynomialsDegLE ι 0 ↔ ∃ c : ℝ, f = fun _ ↦ c := by
  constructor
  · rintro hf
    obtain ⟨p, hp, rfl⟩ := (mem_polynomialsDegLE_iff ι).1 hf
    have hpC := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hp)
    refine ⟨p.coeff 0, ?_⟩
    rw [hpC]
    ext x
    simp
  · rintro ⟨c, rfl⟩
    exact const_mem_polynomialsDegLE ι 0 c

/-- Evaluating a real multilinear map on the diagonal gives a polynomial function whose degree is
at most the number of arguments. -/
theorem _root_.MultilinearMap.apply_const_mem_polynomialsDegLE [Finite ι] {κ : Type*}
    [Fintype κ] (m : (Π _ : κ, EuclideanSpace ℝ ι) →ₘₗ[ℝ] ℝ) :
    (fun x ↦ m fun _ ↦ x) ∈ polynomialsDegLE ι (Fintype.card κ) := by
  classical
  have := Fintype.ofFinite ι
  set b := EuclideanSpace.basisFun ι ℝ
  refine (mem_polynomialsDegLE_iff ι).2
    ⟨∑ σ : κ → ι, C (m fun j ↦ b (σ j)) * ∏ j, X (σ j), ?_, ?_⟩
  · refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ ↦ ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    refine (totalDegree_finsetProd _ _).trans ?_
    simp [totalDegree_X]
  · ext x
    -- Expand `x = ∑ᵢ xᵢ eᵢ` in every argument by multilinearity.
    conv_rhs => rw [← b.sum_repr x, m.map_sum]
    simp [m.map_smul_univ, b, mul_comm]

/-- Every partial sum `p.partialSum N` of a real formal multilinear series on Euclidean space is a
polynomial function of degree at most `N - 1`. -/
theorem _root_.FormalMultilinearSeries.partialSum_mem_polynomialsDegLE {ι : Type*} [Finite ι]
    [ContinuousAdd (EuclideanSpace ℝ ι)] [ContinuousConstSMul ℝ (EuclideanSpace ℝ ι)]
    (p : FormalMultilinearSeries ℝ (EuclideanSpace ℝ ι) ℝ) (N : ℕ) :
    p.partialSum N ∈ polynomialsDegLE ι (N - 1) := by
  have hsum : p.partialSum N = ∑ k ∈ Finset.range N, fun y ↦ p k fun _ ↦ y := by
    ext y
    simp [FormalMultilinearSeries.partialSum]
  rw [hsum]
  refine Submodule.sum_mem _ fun k hk ↦
    polynomialsDegLE_mono ι (Nat.le_sub_one_of_lt (Finset.mem_range.1 hk)) ?_
  simpa using (p k).toMultilinearMap.apply_const_mem_polynomialsDegLE

section Operations

variable {ι}

/-- The product of two polynomial functions has degree at most the sum of their degree bounds. -/
theorem mul_mem_polynomialsDegLE {m k : ℕ} {f g : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ polynomialsDegLE ι m) (hg : g ∈ polynomialsDegLE ι k) :
    f * g ∈ polynomialsDegLE ι (m + k) := by
  obtain ⟨p, hp, rfl⟩ := (mem_polynomialsDegLE_iff ι).1 hf
  obtain ⟨q, hq, rfl⟩ := (mem_polynomialsDegLE_iff ι).1 hg
  exact (mem_polynomialsDegLE_iff ι).2
    ⟨p * q, (totalDegree_mul p q).trans (add_le_add hp hq), by
      ext x; simp only [Pi.mul_apply, polynomialEvalₗ_apply, MvPolynomial.eval_mul]⟩

/-- A finite product of polynomial functions has degree at most the sum of their degree bounds. -/
theorem finset_prod_mem_polynomialsDegLE {α : Type*} (s : Finset α)
    {d : α → ℕ} {f : α → EuclideanSpace ℝ ι → ℝ}
    (hf : ∀ a ∈ s, f a ∈ polynomialsDegLE ι (d a)) :
    (∏ a ∈ s, f a) ∈ polynomialsDegLE ι (∑ a ∈ s, d a) := by
  classical
  have hrep : ∀ a, ∃ p : MvPolynomial ι ℝ,
      a ∈ s → p.totalDegree ≤ d a ∧ polynomialEvalₗ ι p = f a := fun a ↦ by
    by_cases ha : a ∈ s
    · obtain ⟨p, hp, hpe⟩ := (mem_polynomialsDegLE_iff ι).1 (hf a ha)
      exact ⟨p, fun _ ↦ ⟨hp, hpe⟩⟩
    · exact ⟨1, fun h ↦ absurd h ha⟩
  choose p hp using hrep
  refine (mem_polynomialsDegLE_iff ι).2 ⟨∏ a ∈ s, p a,
    (MvPolynomial.totalDegree_finsetProd s p).trans
      (Finset.sum_le_sum fun a ha ↦ (hp a ha).1), ?_⟩
  ext x
  simp only [Finset.prod_apply, polynomialEvalₗ_apply, MvPolynomial.eval_prod]
  exact Finset.prod_congr rfl fun a ha ↦ by
    simpa [polynomialEvalₗ_apply] using congrFun (hp a ha).2 x

/-- A finite product of coordinate projections indexed by `S : Finset α` has total degree at most
`S.card`. -/
theorem prod_coord_mem_polynomialsDegLE {α : Type*} (S : Finset α) (I : α → ι) :
    (fun x : EuclideanSpace ℝ ι ↦ ∏ l ∈ S, x (I l)) ∈ polynomialsDegLE ι S.card := by
  convert finset_prod_mem_polynomialsDegLE S fun l _ ↦
    (coordinate_mem_polynomialsDegLE_iff ι 1 (I l)).2 le_rfl using 1
  · simp
  · ext x; simp

end Operations

/-- Bounded-degree polynomial functions form a finite-dimensional space. -/
instance [Finite ι] (m : ℕ) : FiniteDimensional ℝ (polynomialsDegLE ι m) :=
  inferInstanceAs (Module.Finite ℝ ((restrictTotalDegree ι ℝ m).map (polynomialEvalₗ ι)))

/-- The dimension of polynomial functions of total degree at most `m` is the number of
monomials of that degree or less. -/
@[simp]
theorem finrank_polynomialsDegLE [Fintype ι] (m : ℕ) :
    Module.finrank ℝ (polynomialsDegLE ι m) =
      (m + Fintype.card ι).choose (Fintype.card ι) := by
  rw [← (restrictTotalDegreeEquivPolynomialsDegLE ι m).finrank_eq,
    finrank_restrictTotalDegree]

end Basic

section Calculus

open MeasureTheory
open scoped ContDiff Gradient InnerProductSpace Topology

private theorem polynomialEvalₗ_eq_fun {ι : Type*} (p : MvPolynomial ι ℝ) :
    (polynomialEvalₗ ι p : EuclideanSpace ℝ ι → ℝ) = fun x : EuclideanSpace ℝ ι ↦ eval x p :=
  _root_.funext fun x ↦ polynomialEvalₗ_apply ι p x

/-! ### Analyticity and smoothness -/

section Analytic

variable {ι : Type*} [Fintype ι]

/-- Evaluating a real multivariate polynomial on `EuclideanSpace ℝ ι` is real-analytic on the whole
space. -/
theorem _root_.MvPolynomial.analyticOnNhd_polynomialEvalₗ (p : MvPolynomial ι ℝ) :
    AnalyticOnNhd ℝ (polynomialEvalₗ ι p) Set.univ := by
  rw [polynomialEvalₗ_eq_fun]
  exact AnalyticOnNhd.eval_continuousLinearMap
    (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap p

/-- Evaluating a real multivariate polynomial on `EuclideanSpace ℝ ι` is `C^n` for every `n`. -/
theorem _root_.MvPolynomial.contDiff_polynomialEvalₗ {n : WithTop ℕ∞} (p : MvPolynomial ι ℝ) :
    ContDiff ℝ n (polynomialEvalₗ ι p) :=
  p.analyticOnNhd_polynomialEvalₗ.contDiff.of_le le_top

/-- Every polynomial function in `polynomialsDegLE ι m` is real-analytic on `EuclideanSpace ℝ ι`. -/
theorem analyticOnNhd_of_mem_polynomialsDegLE {m : ℕ} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ polynomialsDegLE ι m) :
    AnalyticOnNhd ℝ f Set.univ := by
  obtain ⟨p, -, rfl⟩ := (mem_polynomialsDegLE_iff ι).mp hf
  exact p.analyticOnNhd_polynomialEvalₗ

/-- Every polynomial function in `polynomialsDegLE ι m` is `C^n` for every `n`. -/
theorem contDiff_of_mem_polynomialsDegLE {m : ℕ} {n : WithTop ℕ∞} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ polynomialsDegLE ι m) :
    ContDiff ℝ n f :=
  (analyticOnNhd_of_mem_polynomialsDegLE hf).contDiff.of_le le_top

end Analytic

/-! ### Open-set rigidity -/

section Rigidity

variable {ι : Type*} [Finite ι]

/-- Two formal polynomials whose evaluations agree on a nonempty open subset of
`EuclideanSpace ℝ ι` are equal. -/
theorem polynomialEvalₗ_eq_of_eqOn_isOpen {p q : MvPolynomial ι ℝ}
    {s : Set (EuclideanSpace ℝ ι)} (hs : IsOpen s) (hs_ne : s.Nonempty)
    (heq : Set.EqOn (polynomialEvalₗ ι p) (polynomialEvalₗ ι q) s) :
    p = q := by
  let := Fintype.ofFinite ι
  obtain ⟨z₀, hz₀⟩ := hs_ne
  apply polynomialEvalₗ_injective ι
  exact p.analyticOnNhd_polynomialEvalₗ.eq_of_eventuallyEq
    q.analyticOnNhd_polynomialEvalₗ (heq.eventuallyEq_of_mem (hs.mem_nhds hz₀))

/-- Two polynomial functions agreeing on a nonempty open subset of `EuclideanSpace ℝ ι` are equal
everywhere. -/
theorem eq_of_mem_polynomialsDegLE_of_eqOn_isOpen {m₁ m₂ : ℕ} {f g : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ polynomialsDegLE ι m₁) (hg : g ∈ polynomialsDegLE ι m₂)
    {s : Set (EuclideanSpace ℝ ι)} (hs : IsOpen s) (hs_ne : s.Nonempty) (heq : Set.EqOn f g s) :
    f = g := by
  let := Fintype.ofFinite ι
  obtain ⟨z₀, hz₀⟩ := hs_ne
  exact (analyticOnNhd_of_mem_polynomialsDegLE hf).eq_of_eventuallyEq
    (analyticOnNhd_of_mem_polynomialsDegLE hg) (heq.eventuallyEq_of_mem (hs.mem_nhds hz₀))

/-- Two polynomial functions agreeing almost everywhere on a nonempty open subset of
`EuclideanSpace ℝ ι` with respect to an open-positive measure are equal everywhere. -/
theorem eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen {m₁ m₂ : ℕ}
    [MeasurableSpace (EuclideanSpace ℝ ι)] {mu : Measure (EuclideanSpace ℝ ι)}
    [mu.IsOpenPosMeasure] {f g : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ polynomialsDegLE ι m₁) (hg : g ∈ polynomialsDegLE ι m₂)
    {s : Set (EuclideanSpace ℝ ι)} (hs : IsOpen s) (hs_ne : s.Nonempty)
    (hae : f =ᵐ[mu.restrict s] g) :
    f = g := by
  let := Fintype.ofFinite ι
  exact eq_of_mem_polynomialsDegLE_of_eqOn_isOpen hf hg hs hs_ne <|
    Measure.eqOn_open_of_ae_eq hae hs
      (contDiff_of_mem_polynomialsDegLE (n := 0) hf).continuous.continuousOn
      (contDiff_of_mem_polynomialsDegLE (n := 0) hg).continuous.continuousOn

end Rigidity

/-! ### Derivatives and degree lowering -/

section Derivatives

/-- Differentiating `polynomialEvalₗ ι p` in the `i`-th standard coordinate direction evaluates
`pderiv i p`. -/
@[simp]
theorem _root_.MvPolynomial.fderiv_polynomialEvalₗ_single {ι : Type*} [Finite ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    fderiv ℝ (polynomialEvalₗ ι p) x (EuclideanSpace.single i 1) =
      polynomialEvalₗ ι (pderiv i p) x := by
  rw [polynomialEvalₗ_eq_fun, polynomialEvalₗ_apply]
  exact p.fderiv_eval_euclidean_single x i

/-- The directional Fréchet derivative of `polynomialEvalₗ ι p` at `x` along `v` is the inner
product of the evaluated formal gradient with `v`. -/
theorem _root_.MvPolynomial.fderiv_polynomialEvalₗ_apply {ι : Type*} [Fintype ι]
    (p : MvPolynomial ι ℝ) (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (polynomialEvalₗ ι p) x v = ∑ i, polynomialEvalₗ ι (pderiv i p) x * v i := by
  rw [polynomialEvalₗ_eq_fun]
  simpa only [polynomialEvalₗ_apply] using p.fderiv_eval_euclidean_apply x v

/-- The Euclidean gradient of `polynomialEvalₗ ι p` at `x` expands in the standard basis with
coefficients `polynomialEvalₗ ι (pderiv i p) x`. -/
theorem _root_.MvPolynomial.gradient_polynomialEvalₗ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    ∇ (polynomialEvalₗ ι p) x =
      ∑ i, polynomialEvalₗ ι (pderiv i p) x • EuclideanSpace.single i 1 := by
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).injective
  ext v
  simp [p.fderiv_polynomialEvalₗ_apply, EuclideanSpace.inner_single_left, mul_comm]

/-- Differentiating a polynomial function of degree at most `m` in a fixed direction produces a
polynomial function of degree at most `m - 1`. -/
theorem fderiv_apply_mem_polynomialsDegLE {ι : Type*} [Finite ι] {m : ℕ}
    {f : EuclideanSpace ℝ ι → ℝ} (hf : f ∈ polynomialsDegLE ι m) (v : EuclideanSpace ℝ ι) :
    (fun x ↦ fderiv ℝ f x v) ∈ polynomialsDegLE ι (m - 1) := by
  let := Fintype.ofFinite ι
  obtain ⟨p, hp, rfl⟩ := (mem_polynomialsDegLE_iff ι).mp hf
  have heq : (fun x ↦ fderiv ℝ (polynomialEvalₗ ι p) x v) =
      ∑ i, v i • polynomialEvalₗ ι (pderiv i p) := by
    ext x
    simp [p.fderiv_polynomialEvalₗ_apply, mul_comm]
  rw [heq]
  refine Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ (v i) ?_
  rw [polynomialEvalₗ_mem_polynomialsDegLE_iff]
  exact (p.totalDegree_pderiv_le i).trans (Nat.sub_le_sub_right hp 1)

/-- Every iterated Fréchet derivative of order strictly above `m` vanishes on
`polynomialsDegLE ι m`. -/
theorem iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE {ι : Type*} [Fintype ι] {m k : ℕ}
    (hmk : m < k) {f : EuclideanSpace ℝ ι → ℝ} (hf : f ∈ polynomialsDegLE ι m) :
    iteratedFDeriv ℝ k f = 0 := by
  induction m generalizing k f with
  | zero =>
      obtain ⟨c, rfl⟩ := (mem_polynomialsDegLE_zero_iff ι).mp hf
      exact iteratedFDeriv_const_of_ne hmk.ne' c
  | succ m ih =>
      obtain _ | k := k
      · omega
      ext x v
      rw [Pi.zero_apply, zero_apply, iteratedFDeriv_succ_apply_right]
      set g : (EuclideanSpace ℝ ι →L[ℝ] ℝ) →L[ℝ] ℝ :=
        ContinuousLinearMap.apply ℝ ℝ (v (Fin.last k))
      have hdf : ContDiff ℝ k (fun y ↦ fderiv ℝ f y) :=
        (contDiff_of_mem_polynomialsDegLE (n := k + 1) hf).fderiv_right (m := k) le_rfl
      have hcomp := congrArg (fun M ↦ M (Fin.init v))
        (g.iteratedFDeriv_comp_left (hdf.contDiffAt (x := x)) (i := k) le_rfl)
      simpa only [Function.comp_def, g, ContinuousLinearMap.compContinuousMultilinearMap_coe,
        ContinuousLinearMap.apply_apply, Pi.zero_apply, zero_apply] using
          hcomp.symm.trans <| congrArg (fun M ↦ M x (Fin.init v)) <|
            ih (Nat.lt_of_succ_lt_succ hmk) (fderiv_apply_mem_polynomialsDegLE hf (v (Fin.last k)))

end Derivatives

end Calculus

end TauCeti
