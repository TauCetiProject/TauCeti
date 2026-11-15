/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Order truncation and homogeneous seminorms on higher-order Sobolev spaces

Because `TauCeti.Wkp` constructs `W^{k,p}(Ω)` inductively as iterated weak-derivative graphs, the
weak derivative field of positive order `j + 1 ≤ k` of `u ∈ W^{k,p}(Ω)` is obtained in two steps:
first truncate `u` from order `k` down to order `j + 1` along `TauCeti.Wkp.toOrderL` (the iterate
of `TauCeti.Wkp.lowerOrderL`), and then take its highest weak derivative
`TauCeti.Wkp.iteratedGradient j (toOrderL h u)` in `Lᵖ(Ω; TauCeti.IteratedGradient E j)`.

Taking the `Lᵖ(Ω)` norm of the value at order `0` and of `iteratedGradient j (toOrderL h u)` at
order `j + 1 ≤ k` yields the homogeneous Sobolev seminorms `|·|_{j,p}`, bundled here as Mathlib
`Seminorm`s `TauCeti.Wkp.seminorm k j hj : Seminorm ℝ (Wkp mu Omega p k)`. Subadditivity,
homogeneity, and nonnegativity are inherited directly from `SeminormClass`.

Above first order, each `TauCeti.WeakDerivStep` uses an `ℓ²` product norm
(`‖u‖² = ‖lowerOrder u‖² + ‖D^{k} u‖²`), whereas at first order `TauCeti.W1p` takes the `Lᵖ` norm
of the pointwise Euclidean norm of `(u, ∇u)`. Writing
`S(u) = √(∑_{j=0}^k |u|_{j,p}²)` for the Euclidean combination of the homogeneous seminorms, one
therefore has exact equality `‖u‖ = S(u)` when `p = 2` (`TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`),
and for every `1 ≤ p ≤ ∞` and every order `k` the dimension- and order-independent equivalence
`S(u) ≤ √2 ‖u‖` and `‖u‖ ≤ √2 S(u)` (`TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm` and
`TauCeti.Wkp.norm_le_sqrt_two_mul`). The factor `√2` in the lower comparison is attained by `sin`
in `W^{1,∞}(0, 2π)`.

## Main definitions

* `TauCeti.Wkp.toOrderL`: the continuous linear truncation `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for
  `j ≤ k`.
* `TauCeti.Wkp.seminorm`: the order-`j` homogeneous Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)`
  (`j ≤ k`), bundled as a `Seminorm ℝ (Wkp mu Omega p k)`.

## Main results

* `TauCeti.Wkp.toOrderL_self`, `TauCeti.Wkp.toOrderL_comp_toOrderL`,
  `TauCeti.Wkp.value_toOrderL`, `TauCeti.Wkp.toOrderL_injective`: functoriality, value
  preservation, and injectivity of order truncation.
* `TauCeti.Wkp.norm_le_sqrt_two_mul`, `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`: two-sided comparison
  between the iterated graph norm on `W^{k,p}(Ω)` and `√(∑_{j ≤ k} |u|_{j,p}²)` within `√2`.
* `TauCeti.Wkp.norm_sq_eq_sum_seminorm_sq`, `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`: exact
  equality `‖u‖ = √(∑_{j ≤ k} |u|_{j,2}²)` at exponent `2`.
* `TauCeti.Wkp.restrictL_toOrderL`, `TauCeti.Wkp.seminorm_restrictL_le`: compatibility of
  truncation and seminorms with restriction to an open subdomain.
* `TauCeti.Wkp.ofExponentLEL_toOrderL`, `TauCeti.Wkp.seminorm_ofExponentLEL_le`: compatibility of
  truncation and seminorms with lowering the integrability exponent on finite-measure domains.
* `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn`: agreement of truncated weak
  derivatives and Sobolev seminorms with classical Fréchet and one-dimensional derivatives on `Cʲ`
  representatives.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003, Chapter 3.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §4.1.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society, 2010,
  §5.2.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

section General

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Order truncation -/

/-- Forget the weak derivatives above order `j`: the continuous linear projection
`W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` obtained by iterating `TauCeti.Wkp.lowerOrderL`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j :=
  Nat.leRec (motive := fun k _ => Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun k _ ih => ih.comp (lowerOrderL k)) h

/-- Truncating a Sobolev space to its own order is the identity continuous linear map. -/
@[simp]
theorem toOrderL_self {k : ℕ} (h : k ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = ContinuousLinearMap.id ℝ _ :=
  Nat.leRec_self _ _

/-- Truncating from order `k + 1` to order `j ≤ k` factors through `TauCeti.Wkp.lowerOrderL k`. -/
theorem toOrderL_succ {j k : ℕ} (h : j ≤ k) (h' : j ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h' = (toOrderL h).comp (lowerOrderL k) :=
  Nat.leRec_succ _ _ h

/-- Pointwise form of `TauCeti.Wkp.toOrderL_succ`: truncating from `k + 1` to `j ≤ k` first drops
to `lowerOrder k u` and then truncates from `k` to `j`. -/
theorem toOrderL_succ_apply {j k : ℕ} (h : j ≤ k) (h' : j ≤ k + 1)
    (u : Wkp mu Omega p (k + 1)) :
    toOrderL h' u = toOrderL h (lowerOrder k u) := by
  rw [toOrderL_succ h, ContinuousLinearMap.comp_apply, lowerOrderL_apply]

/-- Truncating by a single order from `k + 1` to `k` is `TauCeti.Wkp.lowerOrderL k`. -/
theorem toOrderL_le_succ {k : ℕ} (h : k ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = lowerOrderL k := by
  rw [toOrderL_succ le_rfl, toOrderL_self, ContinuousLinearMap.id_comp]

/-- Order truncation preserves the `Lᵖ` value component. -/
@[simp]
theorem value_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    value j (toOrderL h u) = value k u := by
  induction h using Nat.leRec with
  | refl => simp
  | le_succ_of_le h ih => rw [toOrderL_succ_apply h, ih, ← value_succ]

/-- Composing the bundled value projection with order truncation recovers the value projection at
the source order. -/
@[simp]
theorem valueL_comp_toOrderL {j k : ℕ} (h : j ≤ k) :
    (valueL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h) = valueL k :=
  ContinuousLinearMap.ext fun u => by simp

/-- An order-`j` Sobolev function `v` is the truncation of `u ∈ W^{k,p}(Ω)` if and only if their
`Lᵖ` values coincide. -/
theorem toOrderL_eq_iff {j k : ℕ} (h : j ≤ k) {u : Wkp mu Omega p k} {v : Wkp mu Omega p j} :
    toOrderL h u = v ↔ value k u = value j v :=
  ⟨fun huv => huv ▸ (value_toOrderL h u).symm, fun hval => ext j ((value_toOrderL h u).trans hval)⟩

/-- Order truncation is injective: the `Lᵖ` value determines every recorded weak derivative. -/
theorem toOrderL_injective {j k : ℕ} (h : j ≤ k) :
    Function.Injective (toOrderL (mu := mu) (Omega := Omega) (p := p) h) :=
  fun _ _ huv => ext k (by rw [← value_toOrderL h, huv, value_toOrderL])

/-- Two Sobolev functions have equal order-`j` truncations if and only if they are equal. -/
@[simp]
theorem toOrderL_inj {j k : ℕ} (h : j ≤ k) {u v : Wkp mu Omega p k} :
    toOrderL h u = toOrderL h v ↔ u = v :=
  (toOrderL_injective h).eq_iff

/-- Order truncations compose transitively as continuous linear maps. -/
@[simp]
theorem toOrderL_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) hij).comp (toOrderL hjk) =
      toOrderL (hij.trans hjk) :=
  ContinuousLinearMap.ext fun u => ext i (by simp)

/-- Applying two successive order truncations agrees with truncating directly to the lowest
order. -/
@[simp]
theorem toOrderL_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL hij (toOrderL hjk u) = toOrderL (hij.trans hjk) u :=
  ext i (by simp)

/-- Forgetting one further derivative after truncating to `j + 1` agrees with truncating directly
to `j`. Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    lowerOrder j (toOrderL h u) = toOrderL (Nat.le_of_succ_le h) u := by
  apply ext j
  rw [← value_succ, value_toOrderL, value_toOrderL]

/-- Bundled form of `TauCeti.Wkp.lowerOrder_toOrderL`. -/
theorem lowerOrderL_comp_toOrderL {j k : ℕ} (h : j + 1 ≤ k) :
    (lowerOrderL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h) =
      toOrderL (Nat.le_of_succ_le h) :=
  ContinuousLinearMap.ext fun u => by
    rw [ContinuousLinearMap.comp_apply, lowerOrderL_apply, lowerOrder_toOrderL]

/-- Truncating to order `0` is the `Lᵖ` value projection `TauCeti.Wkp.valueL k`. -/
theorem toOrderL_zero {k : ℕ} (h : 0 ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = valueL k :=
  ContinuousLinearMap.ext fun u => by
    rw [valueL_apply, ← value_toOrderL h, value_zero]

/-- Taking the first-order part after truncating to a positive order `j + 1` recovers the
first-order part of the original function. -/
theorem firstOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    firstOrder j (toOrderL h u) = firstOrder k u :=
  W1p.ext_value (by rw [value_firstOrder, value_toOrderL, value_firstOrder])

/-- Truncating from positive order `k + 1` to order `1` is `TauCeti.Wkp.firstOrderL k`. -/
theorem toOrderL_one {k : ℕ} (h : 1 ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = firstOrderL k :=
  ContinuousLinearMap.ext fun u =>
    (firstOrder_zero (toOrderL h u)).symm.trans
      ((firstOrder_toOrderL h u).trans (firstOrderL_apply k u).symm)

/-- Truncating to a lower order does not increase the Sobolev norm. -/
theorem norm_toOrderL_apply_le {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ := by
  induction h using Nat.leRec with
  | refl => simp
  | le_succ_of_le h ih =>
      rw [toOrderL_succ_apply h]
      exact (ih _).trans (norm_lowerOrder_le _ u)

/-- The operator norm of `TauCeti.Wkp.toOrderL` is at most `1`. -/
theorem opNorm_toOrderL_le {j k : ℕ} (h : j ≤ k) :
    ‖toOrderL (mu := mu) (Omega := Omega) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_apply_le h u

/-- For `1 ≤ k`, the weak gradient `iteratedGradient 0 (toOrderL h u)` is the weak Fréchet
derivative of `value k u`, identified with a functional through the real inner product. -/
theorem hasWeakFDerivOn_value_toOrderL {k : ℕ} (h : 1 ≤ k) (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (value k u)
      (fun x => innerSL ℝ (iteratedGradient 0 (toOrderL h u) x)) := by
  rw [← value_toOrderL h]
  exact hasWeakFDerivOn_value (toOrderL h u)

/-- Adjacent truncated weak derivatives satisfy the weak Fréchet derivative identity: for
`j + 2 ≤ k`, `iteratedGradient (j + 1) (toOrderL h u)` is the weak Fréchet derivative on `Ω` of
`iteratedGradient j (toOrderL _ u)`. -/
theorem hasWeakFDerivOn_iteratedGradient_toOrderL {j k : ℕ} (h : j + 2 ≤ k)
    (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (iteratedGradient j (toOrderL (Nat.le_of_succ_le h) u))
      (iteratedGradient (j + 1) (toOrderL h u)) := by
  rw [← lowerOrder_toOrderL h]
  exact hasWeakFDerivOn_iteratedGradient j (toOrderL h u)

/-! ### Homogeneous Sobolev seminorms -/

/-- The order-`j` homogeneous Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` (`j ≤ k`), bundled as a
Mathlib `Seminorm`. At order `0` it is the `Lᵖ(Ω)` norm of the value; at order `j + 1` it is the
`Lᵖ(Ω)` norm of the weak derivative `iteratedGradient j (toOrderL h u)`. Subadditivity,
homogeneity, and nonnegativity follow from `SeminormClass` (`map_add_le_add`, `map_smul_eq_mul`,
`apply_nonneg`, `map_zero`). -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ =>
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, h =>
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap

/-- Bundled formula for the order-`0` Sobolev seminorm. -/
theorem seminorm_zero {k : ℕ} (h : 0 ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k 0 h =
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap :=
  (rfl)

/-- Bundled formula for the order-`j + 1` Sobolev seminorm. -/
theorem seminorm_succ {k j : ℕ} (h : j + 1 ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k (j + 1) h =
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap :=
  (rfl)

/-- The order-`0` seminorm of `u ∈ W^{k,p}(Ω)` is the `Lᵖ(Ω)` norm of its value. -/
theorem seminorm_zero_apply {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  rw [seminorm_zero, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, coe_normSeminorm,
    valueL_apply]

/-- On `W^{0,p}(Ω) = Lᵖ(Ω)`, the order-`0` seminorm is the `Lᵖ(Ω)` norm itself. -/
theorem seminorm_zero_zero_apply (h : 0 ≤ 0) (u : Wkp mu Omega p 0) :
    seminorm 0 0 h u = ‖u‖ := by
  rw [seminorm_zero_apply, value_zero]

/-- The order-`j + 1` seminorm of `u ∈ W^{k,p}(Ω)` is the `Lᵖ(Ω)` norm of its `(j + 1)`-st weak
derivative `iteratedGradient j (toOrderL h u)`. -/
theorem seminorm_succ_apply {k j : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  rw [seminorm_succ, Seminorm.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, coe_normSeminorm, iteratedGradientL_apply]

/-- The top seminorm `|u|_{k+1,p}` on `W^{k+1,p}(Ω)` is the `Lᵖ(Ω)` norm of `iteratedGradient k u`.
-/
theorem seminorm_self_succ_apply {k : ℕ} (h : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Pulling back the `i`-th seminorm on `W^{j,p}(Ω)` along `toOrderL hjk` yields the `i`-th
seminorm on `W^{k,p}(Ω)`. -/
@[simp]
theorem seminorm_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) j i hij).comp (toOrderL hjk).toLinearMap =
      seminorm k i (hij.trans hjk) := by
  cases i with
  | zero =>
      ext u
      simp [seminorm_zero_apply]
  | succ i =>
      ext u
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_succ_apply]
      rw [toOrderL_toOrderL]

/-- Order truncation preserves every Sobolev seminorm up to the truncated order. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i hij (toOrderL hjk u) = seminorm k i (hij.trans hjk) u :=
  DFunLike.congr_fun (seminorm_comp_toOrderL hij hjk) u

/-- The order-`j` seminorm of `lowerOrder k u` agrees with the order-`j` seminorm of `u`.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side at `k = 0`.
-/
theorem seminorm_lowerOrder {j k : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j hj (lowerOrder k u) = seminorm (k + 1) j (Nat.le_succ_of_le hj) u := by
  rw [← lowerOrderL_apply, ← toOrderL_le_succ (Nat.le_succ k), seminorm_toOrderL]

/-- The order-`0` seminorm vanishes if and only if the Sobolev function is zero. -/
@[simp]
theorem seminorm_zero_eq_zero_iff {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = 0 ↔ u = 0 := by
  rw [seminorm_zero_apply, norm_eq_zero]
  refine ⟨fun hu => ext k ?_, fun hu => by rw [hu, ← valueL_apply, map_zero]⟩
  rw [hu, ← valueL_apply, map_zero]

/-- Every Sobolev seminorm is bounded above by the full Sobolev graph norm. -/
theorem seminorm_le_norm {k j : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j hj u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      exact norm_value_le k u
  | succ j =>
      rw [seminorm_succ_apply]
      exact (norm_iteratedGradient_le j (toOrderL hj u)).trans (norm_toOrderL_apply_le hj u)

/-- As a `Seminorm`, `seminorm k j hj` is bounded by `normSeminorm`. -/
theorem seminorm_le_normSeminorm {k j : ℕ} (hj : j ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k j hj ≤ normSeminorm ℝ (Wkp mu Omega p k) :=
  seminorm_le_norm hj

/-- Every Sobolev seminorm is continuous for the Sobolev norm topology. -/
theorem continuous_seminorm {k j : ℕ} (hj : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j hj) :=
  Seminorm.continuous_of_le continuous_norm (seminorm_le_normSeminorm hj)

/-! ### Comparison between the graph norm and the seminorms -/

private theorem seminorm_fin_castSucc {k : ℕ} (j : Fin (k + 1)) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (Fin.castSucc j) (Fin.castSucc j).is_le u =
      seminorm k j j.is_le (lowerOrder k u) := by
  simp only [Fin.val_castSucc]
  rw [← seminorm_lowerOrder]

private theorem seminorm_fin_last (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (Fin.last (k + 1)) (Fin.last (k + 1)).is_le u =
      ‖iteratedGradient k u‖ := by
  simp only [Fin.val_last]
  rw [seminorm_self_succ_apply]

/-- At order `0`, the sum of the squared seminorms is the squared `Lᵖ(Ω)` norm. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    (∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2) = ‖u‖ ^ 2 := by
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero]
  rw [seminorm_zero_zero_apply]

/-- Splitting off the top derivative from the sum of squared seminorms on `W^{k+1,p}(Ω)`. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    (∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2) =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2) +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc, seminorm_fin_last]
  congr 1
  exact Finset.sum_congr rfl fun j _ => congrArg (· ^ 2) (seminorm_fin_castSucc j u)

/-- The Sobolev graph norm is bounded above by the `ℓ¹` sum of the homogeneous seminorms. -/
theorem norm_le_sum_seminorm :
    ∀ {k : ℕ} (u : Wkp mu Omega p k), ‖u‖ ≤ ∑ j : Fin (k + 1), seminorm k j j.is_le u
  | 0, u => by
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero]
      rw [seminorm_zero_zero_apply]
  | k + 1, u => by
      rw [Fin.sum_univ_castSucc, seminorm_fin_last]
      have hsum : (∑ j : Fin (k + 1), seminorm (k + 1) (Fin.castSucc j) (Fin.castSucc j).is_le u) =
          ∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) :=
        Finset.sum_congr rfl fun j _ => seminorm_fin_castSucc j u
      linarith [hsum, norm_le_sum_seminorm (lowerOrder k u),
        norm_le_norm_lowerOrder_add_norm_iteratedGradient k u]

/-- Squared form of `TauCeti.Wkp.norm_le_sqrt_two_mul`: the squared Sobolev norm is at most twice
the sum of the squared homogeneous seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      nlinarith [norm_nonneg u, sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have ih := norm_sq_le_two_mul_sum_seminorm_sq (lowerOrder (k + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Upper comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`1 ≤ p ≤ ∞`, the iterated graph norm on `W^{k,p}(Ω)` is at most `√2` times the Euclidean sum of
the homogeneous seminorms. At `k = 0` the sum equals `‖u‖ ^ 2`; for `k ≥ 1` the factor `√2`
accounts for the `W^{1,p}` norm at order one. -/
theorem norm_le_sqrt_two_mul {k : ℕ} (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.sqrt_sq (norm_nonneg u)]
  exact Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq u)

/-- Squared form of `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`: the sum of the squared homogeneous
seminorms is at most twice the squared Sobolev norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hv := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u)).2 (norm_lowerOrder_le 0 u)
      have hg := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg u)).2 (norm_iteratedGradient_le 0 u)
      linarith
  | k + 2, u => by
      rw [sum_seminorm_sq_succ (k + 1) u,
        norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u]
      have ih := sum_seminorm_sq_le_two_mul_norm_sq (lowerOrder (k + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Lower comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`1 ≤ p ≤ ∞`, the Euclidean sum of the homogeneous seminorms is at most `√2` times the iterated
graph norm on `W^{k,p}(Ω)`. -/
theorem sqrt_le_sqrt_two_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq u)

/-- At exponent `2`, the squared Sobolev norm equals the sum of the squared homogeneous seminorms
at every order. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k u,
        sum_seminorm_sq_succ k u, norm_sq_eq_sum_seminorm_sq (lowerOrder k u)]

/-- At exponent `2`, the Sobolev norm equals the Euclidean sum of the homogeneous seminorms at
every order. -/
theorem norm_eq_sqrt_sum_seminorm_sq {k : ℕ} (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg u), norm_sq_eq_sum_seminorm_sq]

/-! ### Classical derivatives of smooth representatives -/

/-- If `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a function `f` that is
`C^{j+1}` on `Ω` (`j + 1 ≤ k`), then its `(j + 1)`-st weak derivative field agrees almost
everywhere on `Ω` with `TauCeti.iteratedGradientChain f j`. -/
theorem iteratedGradient_toOrderL_ae_eq_of_contDiffOn {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f j :=
  iteratedGradient_ae_eq_of_contDiffOn j (toOrderL h u) hf (by rwa [value_toOrderL])

/-- The order-`0` seminorm of `u ∈ W^{k,p}(Ω)` equals the `Lᵖ(Ω)` norm of any almost-everywhere
representative of its value. -/
theorem seminorm_zero_eq_lpNorm_of_ae_eq {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) {f : E → ℝ}
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k 0 h u = lpNorm f p (mu.restrict Omega) := by
  rw [seminorm_zero_apply]
  exact Lp.norm_eq_lpNorm_of_ae_eq hu

/-- If `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a function `f` that is `Cʲ` on
`Ω` (`j ≤ k`), then `seminorm k j hj u` agrees with the `Lᵖ(Ω)` norm of the classical `j`-th
Fréchet derivative `iteratedFDeriv ℝ j f`. -/
theorem seminorm_eq_lpNorm_of_contDiffOn {k j : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j hj u = lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, Lp.norm_def, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen (by simp)).aestronglyMeasurable
          Omega.isOpen.measurableSet) ?_
      filter_upwards [hu] with x hx
      rw [hx, norm_iteratedFDeriv_zero]
  | succ j =>
      rw [seminorm_succ_apply]
      exact norm_iteratedGradient_eq_lpNorm_of_contDiffOn j (toOrderL hj u) hf
        (by rwa [value_toOrderL])

end General

section Restriction

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Compatibility with open restriction -/

/-- Restriction to an open subdomain commutes with order truncation. -/
theorem restrictL_toOrderL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    restrictL hU j (toOrderL h u) = toOrderL h (restrictL hU k u) := by
  apply ext j
  rw [value_toOrderL, value_restrictL, value_restrictL, value_toOrderL]

/-- Bundled form of `TauCeti.Wkp.restrictL_toOrderL`. -/
theorem restrictL_comp_toOrderL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) :
    (restrictL (mu := mu) (p := p) hU j).comp (toOrderL h) =
      (toOrderL h).comp (restrictL hU k) :=
  ContinuousLinearMap.ext fun u => restrictL_toOrderL hU h u

/-- Truncated weak derivatives commute with restriction to an open subdomain. -/
theorem iteratedGradient_toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) :
    iteratedGradient j (toOrderL h (restrictL hU k u)) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
        (iteratedGradient j (toOrderL h u)) := by
  rw [← restrictL_toOrderL, iteratedGradient_restrictL]

/-- Restricting to an open subdomain preserves every truncated weak derivative almost everywhere
there. -/
theorem iteratedGradient_toOrderL_restrictL_ae (hU : U ≤ Omega) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) :
    iteratedGradient j (toOrderL h (restrictL hU k u)) =ᵐ[mu.restrict U]
      iteratedGradient j (toOrderL h u) := by
  rw [← restrictL_toOrderL]
  exact iteratedGradient_restrictL_ae hU j (toOrderL h u)

/-- Restriction to an open subdomain does not increase any homogeneous Sobolev seminorm. -/
theorem seminorm_restrictL_le (hU : U ≤ Omega) {k j : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j hj (restrictL hU k u) ≤ seminorm k j hj u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply,
        ← value_toOrderL (Nat.zero_le k) (restrictL hU k u), ← restrictL_toOrderL,
        ← value_toOrderL (Nat.zero_le k) u, value_zero, value_zero]
      exact norm_restrictL_le hU 0 (toOrderL (Nat.zero_le k) u)
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, iteratedGradient_toOrderL_restrictL]
      let r : Lp (IteratedGradient E j) p (mu.restrict Omega) →L[ℝ]
          Lp (IteratedGradient E j) p (mu.restrict U) :=
        Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
          simpa only [one_smul] using
            Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
      have hop : ‖r‖ ≤ 1 := by
        simpa only [ENNReal.toReal_one, Real.one_rpow] using
          Lp.norm_LpToLpOfMeasureLeSMul_le (E := IteratedGradient E j) (p := p) (c := 1) (by simp)
            (by simpa only [one_smul] using
              Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
      simpa only [one_mul] using r.le_of_opNorm_le hop (iteratedGradient j (toOrderL hj u))

end Restriction

section Exponent

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-! ### Compatibility with lowering the integrability exponent -/

/-- Lowering the integrability exponent on a finite-measure domain commutes with order truncation.
-/
theorem ofExponentLEL_toOrderL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    ofExponentLEL hpq j (toOrderL h u) = toOrderL h (ofExponentLEL hpq k u) :=
  ext j (by simp only [value_ofExponentLEL, value_toOrderL])

/-- Bundled form of `TauCeti.Wkp.ofExponentLEL_toOrderL`. -/
theorem ofExponentLEL_comp_toOrderL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) :
    (ofExponentLEL (mu := mu) (Omega := Omega) hpq j).comp (toOrderL h) =
      (toOrderL h).comp (ofExponentLEL hpq k) :=
  ContinuousLinearMap.ext fun u => ofExponentLEL_toOrderL hpq h u

/-- Lowering the exponent maps every truncated weak derivative to its `Lᵖ` copy. -/
theorem iteratedGradient_toOrderL_ofExponentLEL (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega q k) :
    iteratedGradient j (toOrderL h (ofExponentLEL hpq k u)) =
      Lp.ofExponentLEL ℝ _ hpq (iteratedGradient j (toOrderL h u)) := by
  rw [← ofExponentLEL_toOrderL, iteratedGradient_ofExponentLEL]

/-- Lowering the exponent does not change any truncated weak derivative almost everywhere. -/
theorem iteratedGradient_toOrderL_ofExponentLEL_ae (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega q k) :
    ⇑(iteratedGradient j (toOrderL h (ofExponentLEL hpq k u))) =ᵐ[mu.restrict Omega]
      iteratedGradient j (toOrderL h u) := by
  rw [← ofExponentLEL_toOrderL]
  exact iteratedGradient_ofExponentLEL_ae hpq j (toOrderL h u)

/-- On a domain of finite measure, lowering the exponent from `q` to `p ≤ q` multiplies every
homogeneous Sobolev seminorm by at most `μ(Ω) ^ (1 / p - 1 / q)`. -/
theorem seminorm_ofExponentLEL_le (hpq : p ≤ q) {k j : ℕ} (hj : j ≤ k) (u : Wkp mu Omega q k) :
    seminorm k j hj (ofExponentLEL hpq k u) ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * seminorm k j hj u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, value_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq (value k u)
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, iteratedGradient_toOrderL_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq (iteratedGradient j (toOrderL hj u))

end Exponent

section Real

variable {mu : Measure ℝ} [mu.IsAddHaarMeasure] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On an open subset of `ℝ`, the order-`j` Sobolev seminorm of a representative `f` that is `Cʲ`
on `Ω` equals the `Lᵖ(Ω)` norm of its one-dimensional `j`-th derivative `iteratedDeriv j f`. -/
theorem seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn {k j : ℕ} (hj : j ≤ k)
    (u : Wkp mu Omega p k) {f : ℝ → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : ℝ → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j hj u = lpNorm (iteratedDeriv j f) p (mu.restrict Omega) := by
  rw [seminorm_eq_lpNorm_of_contDiffOn hj u hf hu, lpNorm, lpNorm]
  congr 1
  have hc : AEStronglyMeasurable (iteratedFDeriv ℝ j f) (mu.restrict Omega) :=
    (ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen le_rfl).aestronglyMeasurable
      Omega.isOpen.measurableSet
  refine eLpNorm_congr_norm_ae hc ?_ (.of_forall fun _ => norm_iteratedFDeriv_eq_norm_iteratedDeriv)
  rw [iteratedDeriv_eq_equiv_comp]
  exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable hc

end Real

/-! ### Concrete checks -/

section Examples

open intervalIntegral

private theorem lpNorm_two_Ioo_eq_sqrt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : Continuous f) :
    lpNorm f 2 (volume.restrict (Set.Ioo a b)) = √(∫ x in a..b, (f x) ^ 2) := by
  have hmem : MemLp f 2 (volume.restrict (Set.Ioo a b)) :=
    hf.continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc isOpen_Ioo.measurableSet
      Set.Ioo_subset_Icc_self 2
  rw [← Lp.norm_eq_lpNorm_of_ae_eq hmem.coeFn_toLp, ← Real.sqrt_sq (norm_nonneg _),
    hmem.norm_toLp_sq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab]
  simp only [Real.norm_eq_abs, sq_abs]

private theorem norm_top_ge_of_ae_eq_of_mem {Omega : Opens ℝ}
    {f : Lp ℝ ∞ (volume.restrict (Omega : Set ℝ))} {g : ℝ → ℝ}
    (hfg : (f : ℝ → ℝ) =ᵐ[volume.restrict (Omega : Set ℝ)] g) (hg : Continuous g)
    {x : ℝ} (hx : x ∈ (Omega : Set ℝ)) : ‖g x‖ ≤ ‖f‖ := by
  by_contra! h
  have hae : ∀ᵐ y ∂volume.restrict (Omega : Set ℝ), ¬‖f‖ < ‖g y‖ := by
    filter_upwards [hfg, Lp.ae_norm_le_norm_top f] with y hy hle using not_lt_of_ge (hy ▸ hle)
  have hzero : volume ({y | ‖f‖ < ‖g y‖} ∩ (Omega : Set ℝ)) = 0 := by
    rw [← Measure.restrict_apply' Omega.isOpen.measurableSet]
    exact measure_eq_zero_iff_ae_notMem.2 hae
  exact (volume.measure_pos_of_mem_nhds (Filter.inter_mem
    (hg.continuousAt.norm.eventually (lt_mem_nhds h)) (Omega.isOpen.mem_nhds hx))).ne' hzero

-- On `Ω = (0, 1)`, `u(x) = x` in `W^{1,2}(0, 1)` satisfies `toOrderL le_rfl u = u`,
-- `|u|_{1,2} = 1`, and `‖u‖ = √(|u|_{0,2}² + |u|_{1,2}²) = 2 / √3`.
example :
    let Ω : Opens ℝ := ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩
    ∃ u : Wkp volume Ω 2 1,
      toOrderL (mu := volume) (Omega := Ω) (p := 2) (le_rfl : 1 ≤ 1) u = u ∧
      seminorm 1 1 le_rfl u = 1 ∧
      ‖u‖ = 2 / √3 := by
  let Ω : Opens ℝ := ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := 2) 1 isOpen_univ (f := id) contDiff_id.contDiffOn isCompact_Icc
    Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hd1 : iteratedDeriv 1 (id : ℝ → ℝ) = fun _ => (1 : ℝ) := by
    ext x
    simp
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = √(1 / 3 : ℝ) := by
    rw [seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn (Nat.zero_le 1) u
      contDiff_id.contDiffOn hu, iteratedDeriv_zero]
    dsimp only [Ω]
    rw [Opens.coe_mk, lpNorm_two_Ioo_eq_sqrt zero_le_one continuous_id]
    simp only [id_eq, integral_pow]
    norm_num
  have h1 : seminorm 1 1 le_rfl u = 1 := by
    rw [seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn le_rfl u contDiff_id.contDiffOn hu, hd1]
    dsimp only [Ω]
    rw [Opens.coe_mk, lpNorm_two_Ioo_eq_sqrt zero_le_one continuous_const]
    norm_num
  refine ⟨u, by simp, h1, ?_⟩
  rw [norm_eq_sqrt_sum_seminorm_sq, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  rw [h0, h1, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / √3)]
  congr 1
  rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by positivity)]
  norm_num

-- On `Ω = (0, 1)`, `u(x) = x²` in `W^{2,2}(0, 1)` has seminorms `1 / √5`, `2 / √3`, and `2`.
example :
    ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2,
      seminorm 2 0 (Nat.zero_le 2) u = 1 / √5 ∧
      seminorm 2 1 (by decide) u = 2 / √3 ∧
      seminorm 2 2 le_rfl u = 2 := by
  let Ω : Opens ℝ := ⟨Set.Ioo 0 1, isOpen_Ioo⟩
  have hf2 : ContDiff ℝ 2 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  have hf1 : ContDiff ℝ 1 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  have hf0 : ContDiff ℝ 0 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := 2) 2 isOpen_univ hf2.contDiffOn isCompact_Icc
    Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have hd1 : iteratedDeriv 1 (fun x : ℝ => x ^ 2) = fun x => 2 * x := by
    ext x
    simp
  have hd2 : iteratedDeriv 2 (fun x : ℝ => x ^ 2) = fun _ => 2 := by
    ext x
    rw [iteratedDeriv_succ, hd1]
    simp
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn (Nat.zero_le 2) u hf0.contDiffOn hu,
      iteratedDeriv_zero]
    dsimp only [Ω]
    rw [Opens.coe_mk, lpNorm_two_Ioo_eq_sqrt zero_le_one (continuous_pow 2)]
    have hpow : (fun x : ℝ => (x ^ 2) ^ 2) = fun x => x ^ 4 := by ext x; ring
    rw [hpow, integral_pow, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 / √5)]
    congr 1
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  · rw [seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn (by decide) u hf1.contDiffOn hu, hd1]
    dsimp only [Ω]
    rw [Opens.coe_mk, lpNorm_two_Ioo_eq_sqrt (f := fun x : ℝ => 2 * x) zero_le_one
      (continuous_const.mul continuous_id')]
    have hpow : (fun x : ℝ => (2 * x) ^ 2) = fun x => 4 * x ^ 2 := by ext x; ring
    rw [hpow, intervalIntegral.integral_const_mul, integral_pow,
      ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 / √3)]
    congr 1
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  · rw [seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn le_rfl u hf2.contDiffOn hu, hd2]
    dsimp only [Ω]
    rw [Opens.coe_mk, lpNorm_two_Ioo_eq_sqrt zero_le_one continuous_const]
    have hval : ∫ _ : ℝ in (0 : ℝ)..1, (2 : ℝ) ^ 2 = (2 : ℝ) ^ 2 := by simp
    rw [hval, Real.sqrt_sq (by positivity)]

-- Sharpness of `sqrt_le_sqrt_two_mul_norm`: on `Ω = (0, 2π)`, `u(x) = sin x` in `W^{1,∞}(0, 2π)`
-- has `‖u‖ = 1` (since `sin² x + cos² x = 1` everywhere) while `|u|_{0,∞} = |u|_{1,∞} = 1`, so
-- `√(|u|_{0,∞}² + |u|_{1,∞}²) = √2 = √2 * ‖u‖`.
example :
    ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) (2 * Real.pi), isOpen_Ioo⟩ ∞ 1,
      ‖u‖ = 1 ∧ √(∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) = √2 := by
  let Ω : Opens ℝ := ⟨Set.Ioo 0 (2 * Real.pi), isOpen_Ioo⟩
  have hsin1 : ContDiff ℝ 1 Real.sin := Real.contDiff_sin
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := ∞) 1 isOpen_univ hsin1.contDiffOn isCompact_Icc
    Set.Ioo_subset_Icc_self (Set.subset_univ _)
  let u₁ : W1p volume Ω ∞ := u
  have hu_val : (W1p.value u₁ : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] Real.sin := by
    simpa only [value_one] using hu
  have hgrad : (W1p.gradient u₁ : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] Real.cos := by
    have hchain := iteratedGradient_ae_eq_of_contDiffOn 0 u hsin1.contDiffOn hu
    rw [iteratedGradient_zero] at hchain
    refine hchain.trans (.of_forall fun x => ?_)
    rw [iteratedGradientChain_zero]
    have hfg := inner_gradient_left (𝕜 := ℝ) (f := Real.sin) (x := x) (y := 1)
    rw [(Real.hasDerivAt_sin x).hasFDerivAt.fderiv] at hfg
    simpa [RCLike.inner_apply] using hfg
  have hjet_norm : ∀ᵐ x ∂volume.restrict (Ω : Set ℝ),
      ‖(u₁ : Sobolev1JetLp volume Ω ∞) x‖ = 1 := by
    filter_upwards [W1p.value_apply_ae u₁, W1p.gradient_apply_ae u₁, hu_val, hgrad]
      with x hv hg hsin hcos
    have hsq := WithLp.prod_norm_sq_eq_of_L2 ((u₁ : Sobolev1JetLp volume Ω ∞) x)
    rw [← hv, ← hg, hsin, hcos, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
      Real.sin_sq_add_cos_sq] at hsq
    nlinarith [norm_nonneg ((u₁ : Sobolev1JetLp volume Ω ∞) x)]
  have hs0 : seminorm 1 0 (Nat.zero_le 1) u = 1 := by
    rw [seminorm_zero_apply, value_one]
    apply le_antisymm
    · exact Lp.norm_top_le_of_ae_bound zero_le_one (hu_val.mono fun x hx => by
        rw [hx, Real.norm_eq_abs]
        exact Real.abs_sin_le_one x)
    · have hmem : Real.pi / 2 ∈ (Ω : Set ℝ) := ⟨by positivity, by linarith [Real.pi_pos]⟩
      simpa [Real.sin_pi_div_two] using
        norm_top_ge_of_ae_eq_of_mem hu_val Real.continuous_sin hmem
  have hs1 : seminorm 1 1 le_rfl u = 1 := by
    rw [seminorm_self_succ_apply, iteratedGradient_zero]
    apply le_antisymm
    · exact Lp.norm_top_le_of_ae_bound zero_le_one (hgrad.mono fun x hx => by
        rw [hx, Real.norm_eq_abs]
        exact Real.abs_cos_le_one x)
    · have hmem : Real.pi ∈ (Ω : Set ℝ) := ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
      simpa [Real.cos_pi] using
        norm_top_ge_of_ae_eq_of_mem hgrad Real.continuous_cos hmem
  refine ⟨u, ?_, ?_⟩
  · have hnorm_le : ‖u‖ ≤ 1 :=
      Lp.norm_top_le_of_ae_bound zero_le_one (hjet_norm.mono fun _ hx => hx.le)
    have hs_le := seminorm_le_norm (Nat.zero_le 1) u
    linarith
  · simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, hs0, hs1]
    norm_num

private instance (a b : ℝ) :
    IsFiniteMeasure (volume.restrict ((⟨Set.Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
  Real.isFiniteMeasure_restrict_Ioo a b

-- On `Ω = (0, 2)` of measure `2`, the constant `1` in `W^{1,2}(0, 2)` has `|u|_{0,2} = √2`, and
-- lowering the exponent to `p = 1` gives `|ofExponentLEL _ 1 u|_{0,1} = 2 ≤ √2 * √2`.
example :
    ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ 2 1,
      seminorm 1 0 (Nat.zero_le 1) u = √2 ∧
      seminorm 1 0 (Nat.zero_le 1) (ofExponentLEL (p := 1) (by norm_num) 1 u) = 2 ∧
      seminorm 1 0 (Nat.zero_le 1) (ofExponentLEL (p := 1) (by norm_num) 1 u) ≤
        (volume (Set.Ioo (0 : ℝ) 2) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal *
          seminorm 1 0 (Nat.zero_le 1) u := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ
    (f := fun _ : ℝ => (1 : ℝ)) contDiff_const.contDiffOn isCompact_Icc
    Set.Ioo_subset_Icc_self (Set.subset_univ _)
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [seminorm_eq_lpNorm_iteratedDeriv_of_contDiffOn (Nat.zero_le 1) u
      contDiff_const.contDiffOn hu, iteratedDeriv_zero, Opens.coe_mk,
      lpNorm_two_Ioo_eq_sqrt (by norm_num) continuous_const]
    norm_num
  · have hu1 : (value 1 (ofExponentLEL (p := 1) (by norm_num) 1 u) : ℝ → ℝ) =ᵐ[
        volume.restrict ((⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)]
        fun _ => (1 : ℝ) := (value_ofExponentLEL_ae (by norm_num) 1 u).trans hu
    rw [seminorm_zero_eq_lpNorm_of_ae_eq (Nat.zero_le 1) _ hu1, lpNorm,
      eLpNorm_const' (1 : ℝ) one_ne_zero ENNReal.one_ne_top]
    simp [Real.volume_Ioo]
  · simpa only [Opens.coe_mk] using seminorm_ofExponentLEL_le (by norm_num) (Nat.zero_le 1) u

end Examples

end TauCeti.Wkp
