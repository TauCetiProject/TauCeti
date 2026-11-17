/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IteratedFDeriv
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# Realization of finite symmetric jets

Over a nontrivially normed field of characteristic zero, a finite family of symmetric
continuous multilinear maps is the derivative tuple of a smooth polynomial at any prescribed
point. The construction is the finite Taylor polynomial, with the derivative of order `k`
divided by `k!`. No finite-dimensionality or completeness assumption is needed for this
polynomial realization. The polynomial and its smoothness are available without characteristic
zero or symmetry assumptions.

`finiteJetSeries` is the factorial-normalized coefficient series, and `finiteJetPolynomial`
is its finite Taylor sum about the chosen center. The main results are:

* `iteratedFDeriv_finiteJetPolynomial_self`: realization of each prescribed symmetric derivative;
* `taylorMonomial`, `iteratedFDeriv_taylorMonomial_self`: the one-term case
  `y ↦ A (y - x, …, y - x) / k!`, whose only nonzero derivative at `x` is `A`;
* `exists_contDiff_iteratedFDeriv_eq_eventually_mem`: realization with the graph in any
  neighborhood of the center-value pair `(x, A 0 0)`;
* `exists_contDiff_hasCompactSupport_iteratedFDeriv_eq`: on a finite-dimensional real base,
  realization with compact support in any prescribed neighborhood of the center.

The order-zero datum `A 0` is a zero-linear map, whose value `A 0 0` is the value of the
realizing function at the center. In local bundle charts, the graph-neighborhood result lets a
prescribed jet be realized by a local section staying in the chart domain near that pair.

## References

* Ian M. Anderson, *The Variational Bicomplex*, Chapter 1, §A.
* Ivan Kolář, Peter W. Michor and Jan Slovák, *Natural Operations in Differential Geometry*,
  Chapter 12.
-/

public section

open scoped ContDiff Topology
open Set

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The formal multilinear series with coefficient `A i / i!` in each prescribed order
`i ≤ r`, and zero coefficients in all higher orders. -/
noncomputable def finiteJetSeries (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) : FormalMultilinearSeries 𝕜 E F :=
  fun n ↦ if h : n < r + 1 then (n.factorial : 𝕜)⁻¹ • A ⟨n, h⟩ else 0

/-- The coefficient of the finite jet series in a prescribed order. -/
@[simp]
theorem finiteJetSeries_apply (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (i : Fin (r + 1)) :
    finiteJetSeries r A i.val = (i.val.factorial : 𝕜)⁻¹ • A i := by
  simp [finiteJetSeries, i.isLt]

/-- The order-zero coefficient is the prescribed zero-linear map. -/
@[simp]
theorem finiteJetSeries_zero (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) :
    finiteJetSeries r A 0 = A 0 := by
  have hcoeff := finiteJetSeries_apply r A (0 : Fin (r + 1))
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one] at hcoeff
  exact hcoeff.trans (one_smul 𝕜 (A 0))

/-- The coefficients above the prescribed jet order vanish. -/
@[simp]
theorem finiteJetSeries_eq_zero_of_le (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (n : ℕ) (hn : r + 1 ≤ n) :
    finiteJetSeries r A n = 0 := by
  simp [finiteJetSeries, not_lt.mpr hn]

/-- The factorial-normalized finite Taylor sum associated with a tuple `A`, centered at `x`.
The tuple contains precisely the orders from zero through `r`. In characteristic zero,
`iteratedFDeriv_finiteJetPolynomial_self` realizes every symmetric tuple as its derivatives. -/
noncomputable def finiteJetPolynomial (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x y : E) : F :=
  (finiteJetSeries r A).partialSum (r + 1) (y - x)

/-- Evaluation of the finite jet polynomial as its finite Taylor sum. -/
theorem finiteJetPolynomial_apply (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x y : E) :
    finiteJetPolynomial r A x y =
      ∑ i : Fin (r + 1), (i.val.factorial : 𝕜)⁻¹ • A i (fun _ ↦ y - x) := by
  rw [finiteJetPolynomial, FormalMultilinearSeries.partialSum, ← Fin.sum_univ_eq_sum_range]
  simp only [finiteJetSeries_apply, smul_apply]

/-- The finite Taylor polynomial has its prescribed factorial-normalized finite power series
on the whole space, expressed as a ball of infinite radius about its center. -/
theorem finiteJetPolynomial_hasFiniteFPowerSeriesOnBall (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) :
    HasFiniteFPowerSeriesOnBall (finiteJetPolynomial r A x) (finiteJetSeries r A) x
      (r + 1) ⊤ := by
  have hp := ((finiteJetSeries r A).hasFiniteFPowerSeriesOnBall_of_finite
    (finiteJetSeries_eq_zero_of_le r A)).comp_sub x
  simp only [zero_add] at hp
  convert hp using 1
  ext y
  rw [finiteJetPolynomial, FormalMultilinearSeries.sum_of_finite _
    (finiteJetSeries_eq_zero_of_le r A)]

/-- The value of the finite Taylor polynomial at its center is its order-zero datum. -/
@[simp]
theorem finiteJetPolynomial_self (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) :
    finiteJetPolynomial r A x x = A 0 0 := by
  rw [← (finiteJetPolynomial_hasFiniteFPowerSeriesOnBall r A x).toHasFPowerSeriesOnBall.coeff_zero
    (0 : Fin 0 → E)]
  rw [finiteJetSeries_zero]
  -- Both presentations of the empty input tuple are definitionally equal.
  rfl

/-- The finite Taylor polynomial is smooth (and in fact analytic). -/
theorem contDiff_finiteJetPolynomial (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) {n : ℕ∞ω} :
    ContDiff 𝕜 n (finiteJetPolynomial r A x) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  exact ((finiteJetPolynomial_hasFiniteFPowerSeriesOnBall r A x).cpolynomialAt_of_mem
    (by simp)).contDiffAt

/-- All derivatives above the prescribed jet order vanish everywhere, without any symmetry
or characteristic-zero assumption on the prescribed coefficients. -/
@[simp]
theorem iteratedFDeriv_finiteJetPolynomial_eq_zero_of_le (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) (n : ℕ)
    (hn : r + 1 ≤ n) :
    iteratedFDeriv 𝕜 n (finiteJetPolynomial r A x) = 0 := by
  funext y
  have hp := (finiteJetPolynomial_hasFiniteFPowerSeriesOnBall r A x).changeOrigin
    (y := y - x) (by simp)
  rw [add_sub_cancel] at hp
  rw [← iteratedFDerivWithin_univ]
  have hp' := hp.toHasFPowerSeriesOnBall
  rw [← hasFPowerSeriesWithinOnBall_univ] at hp'
  exact hp'.iteratedFDerivWithin_eq_zero
    (contDiff_finiteJetPolynomial r A x (n := ω)).contDiffOn.analyticOn
    uniqueDiffOn_univ (mem_univ y) (hp.finite n hn)

/-- Every prescribed symmetric derivative of the finite Taylor polynomial has the
specified value at its center. Symmetry is invariance under permutations of the slots. -/
theorem iteratedFDeriv_finiteJetPolynomial_self (r : ℕ)
    [CharZero 𝕜]
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F) (x : E) (i : Fin (r + 1))
    (hA : ∀ (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v) :
    iteratedFDeriv 𝕜 i.val (finiteJetPolynomial r A x) x = A i := by
  -- Mathlib's HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum accounts for permutation
  -- multiplicities in every order, including order zero.
  have hp := finiteJetPolynomial_hasFiniteFPowerSeriesOnBall r A x
  ext v
  rw [hp.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum
    ((contDiff_finiteJetPolynomial r A x (n := ω)).contDiffOn.analyticOn)]
  simp only [finiteJetSeries_apply, smul_apply]
  have hsym (σ : Equiv.Perm (Fin i.val)) :
      A i (fun j ↦ v (σ j)) = A i v := hA v σ
  simp_rw [hsym]
  simp [Fintype.card_perm, nsmul_eq_mul, ← smul_assoc,
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i.val)]

/-- The normalized Taylor monomial `y ↦ A (y - x, …, y - x) / k!` of a continuous `k`-multilinear
map `A`, centered at `x`. It is the finite jet polynomial whose only nonzero datum is `A`, in order
`k` (`taylorMonomial_eq_finiteJetPolynomial`), so for symmetric `A` its only nonzero derivative at
`x` is `A`, in order `k` (`iteratedFDeriv_taylorMonomial_self`,
`iteratedFDeriv_taylorMonomial_of_ne`). -/
noncomputable def taylorMonomial (k : ℕ) (A : E [×k]→L[𝕜] F) (x y : E) : F :=
  (k.factorial : 𝕜)⁻¹ • A fun _ ↦ y - x

/-- Evaluation of the Taylor monomial. -/
theorem taylorMonomial_apply (k : ℕ) (A : E [×k]→L[𝕜] F) (x y : E) :
    taylorMonomial k A x y = (k.factorial : 𝕜)⁻¹ • A fun _ ↦ y - x := by
  rw [taylorMonomial]

/-- The Taylor monomial of `A` is the finite jet polynomial with datum `A` in order `k` and zero
in lower orders. -/
theorem taylorMonomial_eq_finiteJetPolynomial (k : ℕ) (A : E [×k]→L[𝕜] F) (x : E) :
    taylorMonomial k A x = finiteJetPolynomial k (Fin.lastCases A fun _ ↦ 0) x := by
  ext y
  simp [taylorMonomial_apply, finiteJetPolynomial_apply, Fin.sum_univ_castSucc]

/-- The Taylor monomial is smooth (and in fact a polynomial). -/
theorem contDiff_taylorMonomial (k : ℕ) (A : E [×k]→L[𝕜] F) (x : E) {n : ℕ∞ω} :
    ContDiff 𝕜 n (taylorMonomial k A x) := by
  rw [taylorMonomial_eq_finiteJetPolynomial]
  exact contDiff_finiteJetPolynomial ..

/-- The derivative of order `k` at the center of the Taylor monomial of a symmetric `A` is `A`. -/
theorem iteratedFDeriv_taylorMonomial_self [CharZero 𝕜] (k : ℕ) (A : E [×k]→L[𝕜] F) (x : E)
    (hA : ∀ (v : Fin k → E) (σ : Equiv.Perm (Fin k)), A (v ∘ σ) = A v) :
    iteratedFDeriv 𝕜 k (taylorMonomial k A x) x = A := by
  rw [taylorMonomial_eq_finiteJetPolynomial]
  simpa using iteratedFDeriv_finiteJetPolynomial_self k (Fin.lastCases A fun _ ↦ 0) x
    (Fin.last k) (by simpa using hA)

/-- The derivatives of orders other than `k` at the center of a Taylor monomial vanish. -/
theorem iteratedFDeriv_taylorMonomial_of_ne [CharZero 𝕜] (k : ℕ) (A : E [×k]→L[𝕜] F) (x : E)
    {j : ℕ} (hj : j ≠ k) :
    iteratedFDeriv 𝕜 j (taylorMonomial k A x) x = 0 := by
  rw [taylorMonomial_eq_finiteJetPolynomial]
  rcases lt_or_gt_of_ne hj with hj | hj
  · have h := iteratedFDeriv_finiteJetPolynomial_self k (Fin.lastCases A fun _ ↦ 0) x
      (Fin.castSucc ⟨j, hj⟩) fun v σ ↦ by simp only [Fin.lastCases_castSucc, zero_apply]
    simp only [Fin.lastCases_castSucc, Fin.val_castSucc] at h
    exact h
  · exact congrFun (iteratedFDeriv_finiteJetPolynomial_eq_zero_of_le k _ x j hj) x

/-- A finite symmetric jet is realized by an analytic smooth function whose graph stays
in any prescribed neighborhood of the center-value pair `(x, A 0 0)` near the center. -/
theorem exists_contDiff_iteratedFDeriv_eq_eventually_mem (r : ℕ) [CharZero 𝕜]
    (A : (i : Fin (r + 1)) → E [×i.val]→L[𝕜] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v)
    (x : E) {u : Set (E × F)} (hu : u ∈ 𝓝 (x, A 0 0)) :
    ∃ f : E → F, ContDiff 𝕜 ω f ∧
      (∀ i : Fin (r + 1), iteratedFDeriv 𝕜 i.val f x = A i) ∧
      ∀ᶠ y in 𝓝 x, (y, f y) ∈ u := by
  refine ⟨finiteJetPolynomial r A x, contDiff_finiteJetPolynomial r A x,
    (fun i ↦ iteratedFDeriv_finiteJetPolynomial_self r A x i (hA i)), ?_⟩
  have hmem : u ∈ 𝓝 (x, finiteJetPolynomial r A x x) := by simpa using hu
  exact (continuousAt_id.prodMk
    (contDiff_finiteJetPolynomial r A x (n := ω)).continuous.continuousAt).eventually hmem

/-- On a finite-dimensional real base, any finite symmetric jet is realized by a
smooth function with compact support in an arbitrarily prescribed neighborhood. -/
theorem exists_contDiff_hasCompactSupport_iteratedFDeriv_eq
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (r : ℕ)
    (A : (i : Fin (r + 1)) → E [×i.val]→L[ℝ] F)
    (hA : ∀ i (v : Fin i.val → E) (σ : Equiv.Perm (Fin i.val)), A i (v ∘ σ) = A i v)
    (x : E) {s : Set E} (hs : s ∈ 𝓝 x) :
    ∃ f : E → F, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ s ∧
      ∀ i : Fin (r + 1), iteratedFDeriv ℝ i.val f x = A i := by
  obtain ⟨χ, hχ, -, hχone, hχc, hχs⟩ :=
    (isCompact_singleton (x := x)).exists_contDiff_cutoff_eventuallyEq_one
      isOpen_interior (singleton_subset_iff.mpr (mem_interior_iff_mem_nhds.mpr hs))
  let p := finiteJetPolynomial r A x
  have heq : (fun y ↦ χ y • p y) =ᶠ[𝓝 x] p :=
    (hχone x (mem_singleton x)).mono fun y hy ↦ by simp [hy]
  refine ⟨fun y ↦ χ y • p y, hχ.smul (contDiff_finiteJetPolynomial r A x),
    hχc.smul_right, (tsupport_smul_subset_left _ _).trans (hχs.trans interior_subset), ?_⟩
  intro i
  exact ((heq.iteratedFDeriv ℝ i.val).eq_of_nhds).trans
    (iteratedFDeriv_finiteJetPolynomial_self r A x i (hA i))

end TauCeti
