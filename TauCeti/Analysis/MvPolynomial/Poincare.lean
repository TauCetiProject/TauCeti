/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos
public import TauCeti.Analysis.MvPolynomial.PolynomialSpace
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Algebra.MvPolynomial.PDeriv
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.RingTheory.MvPolynomial.Poincare

/-!
# Analytic calculus and the Poincaré lemma on Euclidean polynomial spaces

`TauCeti.polynomialsDegLE ι m` is the space of real functions on `EuclideanSpace ℝ ι` represented
by formal polynomials of total degree at most `m`. This file records the analytic calculus of
these functions on `EuclideanSpace ℝ ι` and transports the formal polynomial Poincaré lemma
(`MvPolynomial.exists_mem_restrictTotalDegree_pderiv_eq`) to functions in `polynomialsDegLE`:

* Every function in `polynomialsDegLE ι m` is real-analytic on `EuclideanSpace ℝ ι`, hence smooth;
  two such functions agreeing on a nonempty open set, or almost everywhere there with respect to an
  open-positive measure, agree everywhere on `EuclideanSpace ℝ ι`.
* Directional differentiation lowers the degree bound by at most one, and every iterated Fréchet
  derivative of order strictly exceeding `m` vanishes identically.
* A finite family `p : ι → EuclideanSpace ℝ ι → ℝ` in `polynomialsDegLE ι m` whose coordinate
  derivatives satisfy `fderiv ℝ (p i) x (single j 1) = fderiv ℝ (p j) x (single i 1)` is the
  coordinate gradient of a polynomial function `q ∈ polynomialsDegLE ι (m + 1)`, uniquely
  determined after prescribing `q 0`.

## Main results

* `TauCeti.analyticOnNhd_of_mem_polynomialsDegLE`, `TauCeti.contDiff_of_mem_polynomialsDegLE`:
  analyticity and smoothness of bounded-degree polynomial functions.
* `TauCeti.eq_of_mem_polynomialsDegLE_of_eqOn_isOpen`,
  `TauCeti.eq_of_mem_polynomialsDegLE_of_ae_eq_isOpen`: rigidity of polynomial functions from a
  nonempty open set.
* `TauCeti.fderiv_apply_mem_polynomialsDegLE`: directional derivatives map `polynomialsDegLE ι m`
  into `polynomialsDegLE ι (m - 1)`.
* `TauCeti.iteratedFDeriv_eq_zero_of_mem_polynomialsDegLE`: `iteratedFDeriv ℝ k f = 0` when
  `f ∈ polynomialsDegLE ι m` and `m < k`.
* `TauCeti.exists_mem_polynomialsDegLE_fderiv_single_eq`,
  `TauCeti.existsUnique_mem_polynomialsDegLE_fderiv_single_eq`,
  `TauCeti.exists_mem_polynomialsDegLE_gradient_eq`: the Euclidean polynomial Poincaré lemma with
  degree control.

## References

* S. C. Brenner, L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer (2008), §4.3.
-/

public section

noncomputable section

namespace TauCeti

open MvPolynomial MeasureTheory
open scoped ContDiff Gradient InnerProductSpace Topology

private theorem polynomialEvalₗ_eq_fun {ι : Type*} (p : MvPolynomial ι ℝ) :
    (polynomialEvalₗ ι p : EuclideanSpace ℝ ι → ℝ) = fun x : EuclideanSpace ℝ ι ↦ eval x p :=
  _root_.funext fun x ↦ polynomialEvalₗ_apply ι p x

/-! ### Analyticity and smoothness -/

section Analytic

variable {ι : Type*} [Fintype ι]

/-- Evaluating a real multivariate polynomial on `EuclideanSpace ℝ ι` is real-analytic on the whole
space. -/
theorem analyticOnNhd_polynomialEvalₗ (p : MvPolynomial ι ℝ) :
    AnalyticOnNhd ℝ (polynomialEvalₗ ι p) Set.univ := by
  rw [polynomialEvalₗ_eq_fun]
  exact AnalyticOnNhd.eval_continuousLinearMap
    (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap p

/-- Evaluating a real multivariate polynomial on `EuclideanSpace ℝ ι` is `C^n` for every `n`. -/
theorem contDiff_polynomialEvalₗ {n : WithTop ℕ∞} (p : MvPolynomial ι ℝ) :
    ContDiff ℝ n (polynomialEvalₗ ι p) :=
  (analyticOnNhd_polynomialEvalₗ p).contDiff.of_le le_top

/-- Every polynomial function in `polynomialsDegLE ι m` is real-analytic on `EuclideanSpace ℝ ι`. -/
theorem analyticOnNhd_of_mem_polynomialsDegLE {m : ℕ} {f : EuclideanSpace ℝ ι → ℝ}
    (hf : f ∈ polynomialsDegLE ι m) :
    AnalyticOnNhd ℝ f Set.univ := by
  obtain ⟨p, -, rfl⟩ := (mem_polynomialsDegLE_iff ι).mp hf
  exact analyticOnNhd_polynomialEvalₗ p

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
  exact (analyticOnNhd_polynomialEvalₗ p).eq_of_eventuallyEq
    (analyticOnNhd_polynomialEvalₗ q) (heq.eventuallyEq_of_mem (hs.mem_nhds hz₀))

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
theorem fderiv_polynomialEvalₗ_single {ι : Type*} [Finite ι] [DecidableEq ι]
    (p : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    fderiv ℝ (polynomialEvalₗ ι p) x (EuclideanSpace.single i 1) =
      polynomialEvalₗ ι (pderiv i p) x := by
  rw [polynomialEvalₗ_eq_fun, polynomialEvalₗ_apply]
  exact p.fderiv_eval_euclidean_single x i

/-- The directional Fréchet derivative of `polynomialEvalₗ ι p` at `x` along `v` is the inner
product of the evaluated formal gradient with `v`. -/
theorem fderiv_polynomialEvalₗ_apply {ι : Type*} [Fintype ι] (p : MvPolynomial ι ℝ)
    (x v : EuclideanSpace ℝ ι) :
    fderiv ℝ (polynomialEvalₗ ι p) x v = ∑ i, polynomialEvalₗ ι (pderiv i p) x * v i := by
  rw [polynomialEvalₗ_eq_fun]
  simpa only [polynomialEvalₗ_apply] using p.fderiv_eval_euclidean_apply x v

/-- The Euclidean gradient of `polynomialEvalₗ ι p` at `x` expands in the standard basis with
coefficients `polynomialEvalₗ ι (pderiv i p) x`. -/
theorem gradient_polynomialEvalₗ {ι : Type*} [Fintype ι] [DecidableEq ι] (p : MvPolynomial ι ℝ)
    (x : EuclideanSpace ℝ ι) :
    ∇ (polynomialEvalₗ ι p) x =
      ∑ i, polynomialEvalₗ ι (pderiv i p) x • EuclideanSpace.single i 1 := by
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).injective
  ext v
  simp [fderiv_polynomialEvalₗ_apply, EuclideanSpace.inner_single_left, mul_comm]

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
    simp [fderiv_polynomialEvalₗ_apply, mul_comm]
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

/-! ### The polynomial Poincaré lemma on Euclidean space -/

section Poincare

/-- **Polynomial Poincaré lemma on `EuclideanSpace ℝ ι`.** If `p : ι → EuclideanSpace ℝ ι → ℝ` is
a family of polynomial functions of total degree at most `m` whose coordinate partial derivatives
commute, then there exists `q ∈ polynomialsDegLE ι (m + 1)` whose coordinate partial derivatives
are the `p i`. -/
theorem exists_mem_polynomialsDegLE_fderiv_single_eq {ι : Type*} [Finite ι] [DecidableEq ι]
    {m : ℕ} {p : ι → EuclideanSpace ℝ ι → ℝ} (hp : ∀ i, p i ∈ polynomialsDegLE ι m)
    (hclosed : ∀ i j x, fderiv ℝ (p i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (p j) x (EuclideanSpace.single i 1)) :
    ∃ q ∈ polynomialsDegLE ι (m + 1),
      ∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x := by
  choose P hPdeg hPeval using fun i ↦ (mem_polynomialsDegLE_iff ι).mp (hp i)
  have hPmem : ∀ i, P i ∈ restrictTotalDegree ι ℝ m := fun i ↦
    (mem_restrictTotalDegree ι m (P i)).mpr (hPdeg i)
  have hPclosed : ∀ i j, pderiv j (P i) = pderiv i (P j) := by
    intro i j
    apply polynomialEvalₗ_injective ι
    ext x
    simpa only [← fderiv_polynomialEvalₗ_single, hPeval] using hclosed i j x
  obtain ⟨Q, hQdeg, hQp⟩ := exists_mem_restrictTotalDegree_pderiv_eq hPmem hPclosed
  refine ⟨polynomialEvalₗ ι Q, ?_, fun i x ↦ ?_⟩
  · rw [polynomialEvalₗ_mem_polynomialsDegLE_iff]
    exact (mem_restrictTotalDegree ι (m + 1) Q).mp hQdeg
  · rw [fderiv_polynomialEvalₗ_single, hQp i, hPeval i]

/-- A closed family in `polynomialsDegLE ι m` admits a unique potential in
`polynomialsDegLE ι (m + 1)` with any prescribed value at `0`. -/
theorem existsUnique_mem_polynomialsDegLE_fderiv_single_eq {ι : Type*} [Finite ι] [DecidableEq ι]
    {m : ℕ} {p : ι → EuclideanSpace ℝ ι → ℝ} (hp : ∀ i, p i ∈ polynomialsDegLE ι m)
    (hclosed : ∀ i j x, fderiv ℝ (p i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (p j) x (EuclideanSpace.single i 1)) (c : ℝ) :
    ∃! q : EuclideanSpace ℝ ι → ℝ,
      q ∈ polynomialsDegLE ι (m + 1) ∧
        (∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x) ∧ q 0 = c := by
  let := Fintype.ofFinite ι
  obtain ⟨q₀, hq₀deg, hq₀f⟩ := exists_mem_polynomialsDegLE_fderiv_single_eq hp hclosed
  set q : EuclideanSpace ℝ ι → ℝ := fun x ↦ q₀ x + (c - q₀ 0)
  have hqdeg : q ∈ polynomialsDegLE ι (m + 1) :=
    Submodule.add_mem _ hq₀deg (const_mem_polynomialsDegLE ι (m + 1) (c - q₀ 0))
  have hqf : ∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x := fun i x ↦ by
    simp [q, fderiv_add_const, hq₀f i x]
  have hq0 : q 0 = c := by simp [q]
  refine ⟨q, ⟨hqdeg, hqf, hq0⟩, ?_⟩
  rintro q' ⟨hq'deg, hq'f, hq'0⟩
  obtain ⟨Q, -, hQ⟩ := (mem_polynomialsDegLE_iff ι).mp hqdeg
  obtain ⟨Q', -, hQ'⟩ := (mem_polynomialsDegLE_iff ι).mp hq'deg
  rw [← hQ', ← hQ]
  congr 1
  apply pderiv.ext
  · intro i
    apply polynomialEvalₗ_injective ι
    ext x
    simpa only [← fderiv_polynomialEvalₗ_single, hQ, hQ', hqf i x] using hq'f i x
  · have h0 : polynomialEvalₗ ι Q' 0 = polynomialEvalₗ ι Q 0 := by rw [hQ', hQ, hq'0, hq0]
    simpa only [polynomialEvalₗ_apply, PiLp.zero_apply, ← Pi.zero_def, eval_zero] using h0

/-- Full Euclidean form of `exists_mem_polynomialsDegLE_fderiv_single_eq`, recording both the
directional Fréchet derivative and the gradient expansion of the potential `q`. -/
theorem exists_mem_polynomialsDegLE_gradient_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    {p : ι → EuclideanSpace ℝ ι → ℝ} (hp : ∀ i, p i ∈ polynomialsDegLE ι m)
    (hclosed : ∀ i j x, fderiv ℝ (p i) x (EuclideanSpace.single j 1) =
      fderiv ℝ (p j) x (EuclideanSpace.single i 1)) :
    ∃ q ∈ polynomialsDegLE ι (m + 1),
      (∀ i x, fderiv ℝ q x (EuclideanSpace.single i 1) = p i x) ∧
      (∀ x v, fderiv ℝ q x v = ∑ i, p i x * v i) ∧
      (∀ x, ∇ q x = ∑ i, p i x • EuclideanSpace.single i 1) := by
  obtain ⟨q, hqdeg, hqf⟩ := exists_mem_polynomialsDegLE_fderiv_single_eq hp hclosed
  obtain ⟨Q, -, rfl⟩ := (mem_polynomialsDegLE_iff ι).mp hqdeg
  have hQp : ∀ i x, polynomialEvalₗ ι (pderiv i Q) x = p i x := fun i x ↦ by
    rw [← fderiv_polynomialEvalₗ_single, hqf i x]
  refine ⟨polynomialEvalₗ ι Q, hqdeg, hqf, fun x v ↦ ?_, fun x ↦ ?_⟩
  · simp_rw [fderiv_polynomialEvalₗ_apply, hQp]
  · simp_rw [gradient_polynomialEvalₗ, hQp]

end Poincare

end TauCeti
