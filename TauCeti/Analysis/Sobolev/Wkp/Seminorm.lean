/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.Wkp.LinearIsometry
public import TauCeti.Analysis.Sobolev.Wkp.Translation

/-!
# Order truncation and seminorms on higher-order Sobolev spaces

An element of `W^{k,p}(Ω)` (`TauCeti.Wkp`) is built recursively by adjoining one weak derivative
at a time: order `0` is `Lᵖ(Ω)`, order `1` is `TauCeti.W1p`, and each stage `k + 2` adjoins the
weak Fréchet derivative of the highest recorded derivative at stage `k + 1` via
`TauCeti.WeakDerivStep`. Accessing an intermediate weak derivative of order `j + 1 ≤ k`, or the
corresponding homogeneous Sobolev seminorm `|u|_{j+1,p}`, therefore goes through truncating `u`
from order `k` down to order `j + 1` and applying `TauCeti.Wkp.iteratedGradient`.

This file defines the continuous linear truncation `TauCeti.Wkp.toOrderL` for `j ≤ k` as the
iterate of `TauCeti.Wkp.lowerOrderL`, its zero-boundary counterpart `TauCeti.Wkp0.toOrderL`, and
the family of Sobolev seminorms `TauCeti.Wkp.seminorm k j h : Seminorm ℝ (Wkp mu Omega p k)` for
`j ≤ k`. At `j = 0` the seminorm is `‖value k u‖`; at `j + 1` it is
`‖iteratedGradient j (toOrderL h u)‖`.

## Norm comparisons

Let `S(u) = √(∑_{j=0}^k |u|_{j,p}²)`. Above first order, each `WeakDerivStep` uses the Euclidean
product norm, so `‖u‖² = ‖lowerOrder (k + 1) u‖² + ‖iteratedGradient (k + 1) u‖²` holds for every
exponent `p` (`TauCeti.Wkp.norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ`). All
departure between the iterated graph norm `‖u‖` and `S(u)` therefore originates at first order,
where `TauCeti.W1p` takes the `Lᵖ` norm of the pointwise Euclidean norm `√(|u|² + ‖∇u‖²)`:

* For `p = 2`, Fubini's theorem makes the first-order norm satisfy `‖u‖² = |u|_{0,2}² + |u|_{1,2}²`
  as well, so `‖u‖ = S(u)` at every order `k` (`TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`).
* For general `1 ≤ p ≤ ∞` and every order `k`, the component bounds `|u|_{0,p} ≤ ‖u‖` and
  `|u|_{1,p} ≤ ‖u‖` together with the triangle inequality `‖u‖ ≤ |u|_{0,p} + |u|_{1,p}` at order `1`
  propagate up the Euclidean graph stages without accumulating extra factors, giving the uniform
  two-sided equivalence
  `S(u) ≤ √2 ‖u‖` (`TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`) and
  `‖u‖ ≤ √2 S(u)` (`TauCeti.Wkp.norm_le_sqrt_two_mul`).
  The factor `√2` in the lower comparison is sharp: for `u(x) = sin x` in `W^{1,∞}(0, 2π)`, the
  pointwise Euclidean jet norm `√(sin² x + cos² x)` is identically `1` while `|u|_{0,∞} = 1` and
  `|u|_{1,∞} = 1`, so `‖u‖ = 1` and `S(u) = √2`.

## Main definitions

* `TauCeti.Wkp.toOrderL`: the continuous linear projection `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for
  `j ≤ k`, forgetting weak derivatives above order `j`.
* `TauCeti.Wkp0.toOrderL`: the corresponding projection `W^{k,p}_0(Ω) →L[ℝ] W^{j,p}_0(Ω)` on
  zero-boundary Sobolev spaces.
* `TauCeti.Wkp.seminorm`: the `j`th Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`,
  bundled as a `Seminorm ℝ`.

## Main results

* `TauCeti.Wkp.toOrderL_comp_toOrderL`, `TauCeti.Wkp.value_toOrderL`,
  `TauCeti.Wkp.toOrderL_injective`, `TauCeti.Wkp.opNorm_toOrderL_le`: functoriality, value
  preservation, injectivity, and contractivity of order truncation.
* `TauCeti.Wkp.toOrderL_restrictL`, `TauCeti.Wkp.toOrderL_ofExponentLEL`,
  `TauCeti.Wkp.toOrderL_compLinearIsometryEquiv`, `TauCeti.Wkp.toOrderL_translate`,
  `TauCeti.Wkp.toOrderL_lineDerivL`: compatibility of order truncation with subdomain restriction,
  exponent lowering, linear isometries, translations, and weak directional differentiation.
* `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn`: identification of intermediate
  weak derivatives and Sobolev seminorms with classical derivatives for `C^{j+1}` and `C^j`
  representatives.
* `TauCeti.Wkp.seminorm_ofExponentLEL_le`: on a domain of finite measure and for `p ≤ q`,
  `|u|_{j,p} ≤ μ(Ω) ^ (1/p - 1/q) |u|_{j,q}` for every `j ≤ k`.
* `TauCeti.Wkp.norm_le_sqrt_two_mul`, `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`,
  `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`: equivalence between the Sobolev graph norm and the
  Euclidean combination of the seminorms, with equality at `p = 2`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003, Chapter 3.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, Chapter 4.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., American Mathematical Society, 2010,
  §5.2.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal

section TruncationAndSeminorms

variable {E E' : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  [MeasurableSpace E'] [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
  [FiniteDimensional ℝ E'] [BorelSpace E'] {nu : Measure E'} [nu.IsAddHaarMeasure]
  {Omega U : Opens E} {W' : Opens E'} {e : E ≃ₗᵢ[ℝ] E'}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

namespace Wkp

/-! ### Order truncation -/

/-- Forget the weak derivatives above order `j`: the iterate of `TauCeti.Wkp.lowerOrderL` as a
continuous linear map `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)`, equal to the identity when `j = k`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j :=
  Nat.leRec (motive := fun k _ => Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun k _ ih => ih.comp (lowerOrderL k)) h

/-- Truncating from order `k` to order `k` is the identity continuous linear map. -/
@[simp]
theorem toOrderL_self {k : ℕ} (h : k ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = ContinuousLinearMap.id ℝ _ :=
  Nat.leRec_self _ _

/-- Applying `toOrderL` at equal orders returns the same Sobolev function. -/
theorem toOrderL_self_apply {k : ℕ} (h : k ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h u = u := by
  rw [toOrderL_self]
  rfl

/-- Truncating from order `k + 1` to order `j ≤ k` factors through `lowerOrderL k`. -/
theorem toOrderL_succ_right {j k : ℕ} (h : j ≤ k) (h' : j ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h' = (toOrderL h).comp (lowerOrderL k) :=
  Nat.leRec_succ _ _ h

/-- Truncating from order `k + 1` to order `j ≤ k` forgets the highest derivative first and then
truncates from `k` to `j`. -/
theorem toOrderL_succ_right_apply {j k : ℕ} (h : j ≤ k) (h' : j ≤ k + 1)
    (u : Wkp mu Omega p (k + 1)) :
    toOrderL h' u = toOrderL h (lowerOrder k u) := by
  rw [toOrderL_succ_right h h', ContinuousLinearMap.comp_apply, lowerOrderL_apply]

/-- Truncating by a single order is `lowerOrderL`. -/
theorem toOrderL_succ_self (k : ℕ) (h : k ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = lowerOrderL k := by
  rw [toOrderL_succ_right le_rfl h, toOrderL_self, ContinuousLinearMap.id_comp]

/-- Applying `toOrderL` across a single order step agrees with `lowerOrder`. -/
theorem toOrderL_succ_self_apply (k : ℕ) (h : k ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    toOrderL h u = lowerOrder k u := by
  rw [toOrderL_succ_self, lowerOrderL_apply]

/-- Successive order truncations compose to a single truncation. -/
@[simp]
theorem toOrderL_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) hij).comp (toOrderL hjk) =
      toOrderL (hij.trans hjk) := by
  induction k, hjk using Nat.le_induction with
  | base => rw [toOrderL_self, ContinuousLinearMap.comp_id]
  | succ k hjk ih =>
      rw [toOrderL_succ_right hjk, ← ContinuousLinearMap.comp_assoc, ih,
        ← toOrderL_succ_right (hij.trans hjk)]

/-- Truncating from `k` to `j` and then from `j` to `i` equals truncating directly from `k` to
`i`. -/
@[simp]
theorem toOrderL_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL hij (toOrderL hjk u) = toOrderL (hij.trans hjk) u := by
  rw [← ContinuousLinearMap.comp_apply, toOrderL_comp_toOrderL]

/-- Composing `lowerOrderL` on the left of `toOrderL` lowers the target order by one. -/
theorem lowerOrderL_comp_toOrderL {j k : ℕ} (h : j + 1 ≤ k) (h' : j ≤ k) :
    (lowerOrderL (mu := mu) (Omega := Omega) (p := p) j).comp (toOrderL h) = toOrderL h' := by
  rw [← toOrderL_succ_self j j.le_succ, toOrderL_comp_toOrderL]

/-- Taking `lowerOrder` after `toOrderL` truncates to one lower order. -/
theorem lowerOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k) (h' : j ≤ k) (u : Wkp mu Omega p k) :
    lowerOrder j (toOrderL h u) = toOrderL h' u := by
  rw [← lowerOrderL_apply, ← ContinuousLinearMap.comp_apply, lowerOrderL_comp_toOrderL h h']

/-- Truncating to order zero is the bundled `Lᵖ` value projection `valueL`. -/
theorem toOrderL_zero : ∀ (k : ℕ) (h : 0 ≤ k),
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = valueL k
  | 0, h => ContinuousLinearMap.ext fun u => by
      rw [toOrderL_self_apply, valueL_apply, value_zero]
  | k + 1, h => ContinuousLinearMap.ext fun u => by
      rw [toOrderL_succ_right_apply (Nat.zero_le k) h,
        DFunLike.congr_fun (toOrderL_zero k (Nat.zero_le k)) (lowerOrder k u),
        valueL_apply, valueL_apply, value_succ]

/-- Applying `toOrderL` to order zero extracts the `Lᵖ` value component. -/
theorem toOrderL_zero_apply (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h u = value k u := by
  rw [toOrderL_zero, valueL_apply]

/-- Composing `valueL` with `toOrderL` gives `valueL` at the higher order. -/
@[simp]
theorem valueL_comp_toOrderL {j k : ℕ} (h : j ≤ k) :
    (valueL (mu := mu) (Omega := Omega) (p := p) j).comp (toOrderL h) = valueL k := by
  rw [← toOrderL_zero j (Nat.zero_le j), toOrderL_comp_toOrderL, toOrderL_zero]

/-- Order truncation preserves the `Lᵖ` value component. -/
@[simp]
theorem value_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    value j (toOrderL h u) = value k u := by
  rw [← valueL_apply, ← ContinuousLinearMap.comp_apply, valueL_comp_toOrderL, valueL_apply]

/-- Truncating from order `k + 1` to order `1` is `firstOrderL k`. -/
theorem toOrderL_one : ∀ (k : ℕ) (h : 1 ≤ k + 1),
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = firstOrderL k
  | 0, h => ContinuousLinearMap.ext fun u =>
      (toOrderL_self_apply h u).trans ((firstOrder_zero u).symm.trans (firstOrderL_apply 0 u).symm)
  | k + 1, h => ContinuousLinearMap.ext fun u =>
      (toOrderL_succ_right_apply (Nat.succ_le_succ (Nat.zero_le k)) h u).trans
        ((DFunLike.congr_fun (toOrderL_one k (Nat.succ_le_succ (Nat.zero_le k)))
          (lowerOrder (k + 1) u)).trans
          ((firstOrderL_apply k (lowerOrder (k + 1) u)).trans
            ((firstOrder_succ k u).symm.trans (firstOrderL_apply (k + 1) u).symm)))

/-- Taking the first-order part commutes with truncating to any positive order. -/
theorem firstOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    firstOrder j (toOrderL h u) = firstOrder k u := by
  have hjk : j ≤ k := Nat.le_of_succ_le_succ h
  induction k, hjk using Nat.le_induction with
  | base => rw [toOrderL_self_apply]
  | succ k hjk ih =>
      rw [toOrderL_succ_right_apply (Nat.succ_le_succ hjk) h, firstOrder_succ,
        ih (Nat.succ_le_succ hjk) (lowerOrder (k + 1) u)]

/-- Truncating `mk k u D hD` to any order `j ≤ k + 1` forgets the adjoined derivative `D` and
truncates `u`. -/
theorem toOrderL_mk {j k : ℕ} (h : j ≤ k + 1) (h' : j ≤ k + 2)
    (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    toOrderL h' (mk k u D hD) = toOrderL h u := by
  rw [toOrderL_succ_right_apply h h', lowerOrder_mk]

/-- Order truncation is injective: the `Lᵖ` value determines all higher weak derivatives. -/
theorem toOrderL_injective {j k : ℕ} (h : j ≤ k) :
    Function.Injective (toOrderL (mu := mu) (Omega := Omega) (p := p) h) := fun _ _ huv =>
  ext k (by rw [← value_toOrderL h, huv, value_toOrderL])

/-- Two Sobolev functions have the same order-`j` truncation if and only if they are equal. -/
@[simp]
theorem toOrderL_inj {j k : ℕ} (h : j ≤ k) {u v : Wkp mu Omega p k} :
    toOrderL h u = toOrderL h v ↔ u = v :=
  (toOrderL_injective h).eq_iff

/-- An order truncation of `u` vanishes if and only if `u` vanishes. -/
@[simp]
theorem toOrderL_eq_zero_iff {j k : ℕ} (h : j ≤ k) {u : Wkp mu Omega p k} :
    toOrderL h u = 0 ↔ u = 0 :=
  (toOrderL h).map_eq_zero_iff (toOrderL_injective h)

/-- Order truncation does not increase the Sobolev graph norm. -/
theorem norm_toOrderL_apply_le {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ := by
  induction k, h using Nat.le_induction with
  | base => rw [toOrderL_self_apply]
  | succ k hjk ih =>
      rw [toOrderL_succ_right_apply hjk]
      exact (ih (lowerOrder k u)).trans (norm_lowerOrder_le k u)

/-- The operator norm of `toOrderL` is at most `1`. -/
theorem opNorm_toOrderL_le {j k : ℕ} (h : j ≤ k) :
    ‖toOrderL (mu := mu) (Omega := Omega) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_apply_le h u

/-- Order truncation commutes with restriction to an open subdomain. -/
theorem toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h (restrictL hU k u) = restrictL hU j (toOrderL h u) :=
  ext j (by rw [value_toOrderL, value_restrictL, value_restrictL, value_toOrderL])

/-- Bundled form of `TauCeti.Wkp.toOrderL_restrictL`: order truncation and subdomain restriction
commute as continuous linear maps. -/
theorem toOrderL_comp_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (p := p) h).comp (restrictL hU k) =
      (restrictL hU j).comp (toOrderL h) :=
  ContinuousLinearMap.ext (toOrderL_restrictL hU h)

/-- On a domain of finite measure, order truncation commutes with lowering the integrability
exponent. -/
theorem toOrderL_ofExponentLEL [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    toOrderL h (ofExponentLEL hpq k u) = ofExponentLEL hpq j (toOrderL h u) :=
  ext j (by rw [value_toOrderL, value_ofExponentLEL, value_ofExponentLEL, value_toOrderL])

/-- Bundled form of `TauCeti.Wkp.toOrderL_ofExponentLEL`: order truncation and exponent lowering
commute as continuous linear maps. -/
theorem toOrderL_comp_ofExponentLEL [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) h).comp (ofExponentLEL hpq k) =
      (ofExponentLEL hpq j).comp (toOrderL h) :=
  ContinuousLinearMap.ext (toOrderL_ofExponentLEL hpq h)

/-- Order truncation commutes with transport along a measure-preserving linear isometry. -/
theorem toOrderL_compLinearIsometryEquiv (he : MeasurePreserving e mu nu)
    (hUW' : (U : Set E) = e ⁻¹' W') {j k : ℕ} (h : j ≤ k) (u : Wkp nu W' p k) :
    toOrderL h (compLinearIsometryEquiv he hUW' k u) =
      compLinearIsometryEquiv he hUW' j (toOrderL h u) := by
  induction k, h using Nat.le_induction with
  | base => simp only [toOrderL_self_apply]
  | succ k hjk ih =>
      rw [toOrderL_succ_right_apply hjk, lowerOrder_compLinearIsometryEquiv, ih,
        ← toOrderL_succ_right_apply hjk]

/-- Order truncation commutes with whole-space translation. -/
theorem toOrderL_translate (v : E) {j k : ℕ} (h : j ≤ k) (u : Wkp mu ⊤ p k) :
    toOrderL h (translate v k u) = translate v j (toOrderL h u) :=
  ext j (by rw [value_toOrderL, value_translate, value_translate, value_toOrderL])

/-- Order truncation commutes with weak directional differentiation. -/
theorem toOrderL_lineDerivL (v : E) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    toOrderL h (lineDerivL v k u) = lineDerivL v j (toOrderL (Nat.succ_le_succ h) u) := by
  refine (lineDerivL_eq_of_hasWeakLineDerivOn ?_).symm
  rw [value_toOrderL, value_toOrderL]
  exact hasWeakLineDerivOn_lineDerivL v k u

/-- Bundled form of `TauCeti.Wkp.toOrderL_lineDerivL`: order truncation and weak directional
differentiation commute as continuous linear maps. -/
theorem toOrderL_comp_lineDerivL (v : E) {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) h).comp (lineDerivL v k) =
      (lineDerivL v j).comp (toOrderL (Nat.succ_le_succ h)) :=
  ContinuousLinearMap.ext (toOrderL_lineDerivL v h)

/-- Truncating an embedded test function from order `k` to order `j` yields its embedding at order
`j`. -/
theorem toOrderL_ofTestFunctionₗ {j k : ℕ} (h : j ≤ k) (phi : 𝓓(Omega, ℝ)) :
    toOrderL (mu := mu) (p := p) h (ofTestFunctionₗ k phi) = ofTestFunctionₗ j phi :=
  ext j (by rw [value_toOrderL, value_ofTestFunctionₗ, value_ofTestFunctionₗ])

/-- Order truncation preserves the zero-boundary subspace `W^{k,p}_0(Ω)`. -/
theorem toOrderL_mem_wkp0Submodule {j k : ℕ} (h : j ≤ k) {u : Wkp mu Omega p k}
    (hu : u ∈ wkp0Submodule mu Omega p k) :
    toOrderL h u ∈ wkp0Submodule mu Omega p j := by
  refine wkp0Submodule_subset_of_isClosed k
    ((wkp0Submodule mu Omega p j).isClosed.preimage (toOrderL h).continuous)
    (fun phi => ?_) hu
  rw [mem_preimage, toOrderL_ofTestFunctionₗ h]
  exact ofTestFunctionₗ_mem_wkp0Submodule j phi

end Wkp

namespace Wkp0

/-- Continuous linear order truncation `W^{k,p}_0(Ω) →L[ℝ] W^{j,p}_0(Ω)` on zero-boundary Sobolev
spaces, obtained by restricting `TauCeti.Wkp.toOrderL`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp0 mu Omega p k →L[ℝ] Wkp0 mu Omega p j :=
  ((Wkp.toOrderL h).comp (wkp0Submodule mu Omega p k).toSubmodule.subtypeL).codRestrict
    (wkp0Submodule mu Omega p j).toSubmodule
    fun u => Wkp.toOrderL_mem_wkp0Submodule h u.2

/-- Coercing `TauCeti.Wkp0.toOrderL` to the ambient Sobolev space gives `TauCeti.Wkp.toOrderL`. -/
@[simp]
theorem coe_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp0 mu Omega p k) :
    (toOrderL h u : Wkp mu Omega p j) = Wkp.toOrderL h (u : Wkp mu Omega p k) :=
  (rfl)

/-- Truncating from order `k` to order `k` on `W^{k,p}_0(Ω)` is the identity. -/
@[simp]
theorem toOrderL_self {k : ℕ} (h : k ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext fun u => Subtype.ext (Wkp.toOrderL_self_apply h (u : Wkp mu Omega p k))

/-- Truncating by a single order on `W^{k,p}_0(Ω)` is `TauCeti.Wkp0.lowerOrderL`. -/
theorem toOrderL_succ_self (k : ℕ) (h : k ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = lowerOrderL k :=
  ContinuousLinearMap.ext fun u => Subtype.ext <| by
    rw [coe_toOrderL, Wkp.toOrderL_succ_self_apply, coe_lowerOrderL]

/-- Successive truncations on zero-boundary Sobolev spaces compose to a single truncation. -/
@[simp]
theorem toOrderL_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) hij).comp (toOrderL hjk) =
      toOrderL (hij.trans hjk) :=
  ContinuousLinearMap.ext fun u => Subtype.ext (by simp only [ContinuousLinearMap.comp_apply,
    coe_toOrderL, Wkp.toOrderL_toOrderL])

/-- Applying successive truncations on `W^{k,p}_0(Ω)` equals truncating in one step. -/
@[simp]
theorem toOrderL_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp0 mu Omega p k) :
    toOrderL hij (toOrderL hjk u) = toOrderL (hij.trans hjk) u := by
  rw [← ContinuousLinearMap.comp_apply, toOrderL_comp_toOrderL]

/-- Order truncation on `W^{k,p}_0(Ω)` is injective. -/
theorem toOrderL_injective {j k : ℕ} (h : j ≤ k) :
    Function.Injective (toOrderL (mu := mu) (Omega := Omega) (p := p) h) := fun _ _ huv =>
  Subtype.ext (Wkp.toOrderL_injective h (congrArg Subtype.val huv))

/-- Two elements of `W^{k,p}_0(Ω)` have equal order-`j` truncations if and only if they are
equal. -/
@[simp]
theorem toOrderL_inj {j k : ℕ} (h : j ≤ k) {u v : Wkp0 mu Omega p k} :
    toOrderL h u = toOrderL h v ↔ u = v :=
  (toOrderL_injective h).eq_iff

/-- An order truncation on `W^{k,p}_0(Ω)` vanishes if and only if the element vanishes. -/
@[simp]
theorem toOrderL_eq_zero_iff {j k : ℕ} (h : j ≤ k) {u : Wkp0 mu Omega p k} :
    toOrderL h u = 0 ↔ u = 0 :=
  (toOrderL h).map_eq_zero_iff (toOrderL_injective h)

/-- Order truncation on `W^{k,p}_0(Ω)` does not increase the Sobolev graph norm. -/
theorem norm_toOrderL_apply_le {j k : ℕ} (h : j ≤ k) (u : Wkp0 mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ :=
  Wkp.norm_toOrderL_apply_le h (u : Wkp mu Omega p k)

/-- The operator norm of `TauCeti.Wkp0.toOrderL` is at most `1`. -/
theorem opNorm_toOrderL_le {j k : ℕ} (h : j ≤ k) :
    ‖toOrderL (mu := mu) (Omega := Omega) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_apply_le h u

/-- Truncating a test function in `W^{k,p}_0(Ω)` gives its embedding in `W^{j,p}_0(Ω)`. -/
theorem toOrderL_ofTestFunctionₗ {j k : ℕ} (h : j ≤ k) (phi : 𝓓(Omega, ℝ)) :
    toOrderL (mu := mu) (p := p) h (ofTestFunctionₗ k phi) = ofTestFunctionₗ j phi :=
  Subtype.ext (by rw [coe_toOrderL, coe_ofTestFunctionₗ, coe_ofTestFunctionₗ,
    Wkp.toOrderL_ofTestFunctionₗ])

end Wkp0

namespace Wkp

/-! ### Intermediate weak derivative fields -/

/-- For `1 ≤ k`, the first-order weak derivative field `iteratedGradient 0 (toOrderL h u)` is the
weak gradient of `value k u`. -/
theorem hasWeakFDerivOn_value_toOrderL {k : ℕ} (h : 1 ≤ k) (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (value k u)
      (fun x => innerSL ℝ (iteratedGradient 0 (toOrderL h u) x)) := by
  rw [← value_toOrderL h u]
  exact hasWeakFDerivOn_value (toOrderL h u)

/-- Adjacent intermediate weak derivative fields of `u ∈ W^{k,p}(Ω)` satisfy the weak Fréchet
derivative identity: for `j + 2 ≤ k`, `iteratedGradient (j + 1) (toOrderL h₂ u)` is the weak
Fréchet derivative of `iteratedGradient j (toOrderL h₁ u)` on `Ω`. -/
theorem hasWeakFDerivOn_iteratedGradient_toOrderL {j k : ℕ} (h₁ : j + 1 ≤ k) (h₂ : j + 2 ≤ k)
    (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (iteratedGradient j (toOrderL h₁ u))
      (iteratedGradient (j + 1) (toOrderL h₂ u)) := by
  rw [← lowerOrder_toOrderL h₂ h₁ u]
  exact hasWeakFDerivOn_iteratedGradient j (toOrderL h₂ u)

/-- Restricting `u ∈ W^{k,p}(Ω)` to an open subdomain `U ≤ Ω` restricts each intermediate weak
derivative field via `Lp.LpToLpOfMeasureLeSMul`. -/
theorem iteratedGradient_toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) :
    iteratedGradient j (toOrderL h (restrictL hU k u)) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
        (iteratedGradient j (toOrderL h u)) := by
  rw [toOrderL_restrictL, iteratedGradient_restrictL]

/-- Restricting to an open subdomain keeps every intermediate weak derivative field unchanged
almost everywhere on the subdomain. -/
theorem iteratedGradient_toOrderL_restrictL_ae (hU : U ≤ Omega) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) :
    iteratedGradient j (toOrderL h (restrictL hU k u)) =ᵐ[mu.restrict U]
      iteratedGradient j (toOrderL h u) := by
  rw [toOrderL_restrictL]
  exact iteratedGradient_restrictL_ae hU j (toOrderL h u)

/-- Lowering the exponent on a finite-measure domain sends each intermediate weak derivative field
to its `Lᵖ` copy via `Lp.ofExponentLEL`. -/
theorem iteratedGradient_toOrderL_ofExponentLEL [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega q k) :
    iteratedGradient j (toOrderL h (ofExponentLEL hpq k u)) =
      Lp.ofExponentLEL ℝ _ hpq (iteratedGradient j (toOrderL h u)) := by
  rw [toOrderL_ofExponentLEL, iteratedGradient_ofExponentLEL]

/-- Lowering the exponent does not change any intermediate weak derivative field almost
everywhere. -/
theorem iteratedGradient_toOrderL_ofExponentLEL_ae [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega q k) :
    ⇑(iteratedGradient j (toOrderL h (ofExponentLEL hpq k u))) =ᵐ[mu.restrict Omega]
      iteratedGradient j (toOrderL h u) := by
  rw [toOrderL_ofExponentLEL]
  exact iteratedGradient_ofExponentLEL_ae hpq j (toOrderL h u)

/-- Transporting `u ∈ W^{k,p}(W')` along a measure-preserving linear isometry `e` pulls back every
intermediate weak derivative field by `(e.iteratedGradientCongr j).symm` almost everywhere. -/
theorem iteratedGradient_toOrderL_compLinearIsometryEquiv_ae (he : MeasurePreserving e mu nu)
    (hUW' : (U : Set E) = e ⁻¹' W') {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp nu W' p k) :
    iteratedGradient j (toOrderL h (compLinearIsometryEquiv he hUW' k u)) =ᵐ[mu.restrict U]
      fun x => (e.iteratedGradientCongr j).symm (iteratedGradient j (toOrderL h u) (e x)) := by
  rw [toOrderL_compLinearIsometryEquiv]
  exact iteratedGradient_compLinearIsometryEquiv_ae he hUW' j (toOrderL h u)

/-- Whole-space translation translates every intermediate weak derivative field in `Lᵖ`. -/
theorem iteratedGradient_toOrderL_translate (v : E) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu ⊤ p k) :
    iteratedGradient j (toOrderL h (translate v k u)) =
      (mu.restrict ((⊤ : Opens E) : Set E)).translateLp p v
        (iteratedGradient j (toOrderL h u)) := by
  rw [toOrderL_translate, iteratedGradient_translate]

/-- **Intermediate weak derivatives of smooth representatives.** If `u ∈ W^{k,p}(Ω)` has a
representative `f` that is `C^{j+1}` on `Ω` (`j + 1 ≤ k`), then its weak derivative of order
`j + 1` agrees almost everywhere on `Ω` with the classical field `iteratedGradientChain f j`.
Only `C^{j+1}` regularity is required, even when `j + 1 < k`. -/
theorem iteratedGradient_toOrderL_ae_eq_of_contDiffOn {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f j := by
  refine iteratedGradient_ae_eq_of_contDiffOn j (toOrderL h u) hf ?_
  rw [value_toOrderL]
  exact hu

/-! ### Sobolev seminorms -/

/-- The `j`th Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` (`j ≤ k`), bundled as an `ℝ`-seminorm.
At order `0` it is the `Lᵖ(Ω)` norm of `value k u`; at order `j + 1` it is the `Lᵖ(Ω)` norm of the
weak derivative `iteratedGradient j (toOrderL h u)`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ =>
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, h =>
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap

/-- At derivative order `0`, the Sobolev seminorm is the `Lᵖ` norm of the value component. -/
@[simp]
theorem seminorm_zero_apply {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  simp only [seminorm, Seminorm.comp_apply, ContinuousLinearMap.coe_coe, coe_normSeminorm,
    valueL_apply]

/-- At derivative order `j + 1`, the Sobolev seminorm is the `Lᵖ` norm of the weak derivative
`iteratedGradient j (toOrderL h u)`. -/
@[simp]
theorem seminorm_succ_apply {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  simp only [seminorm, Seminorm.comp_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, coe_normSeminorm]
  rw [iteratedGradientL_apply]

/-- At ambient order `0`, the unique Sobolev seminorm is the `Lᵖ` norm itself. -/
theorem seminorm_zero_zero (h : 0 ≤ 0) (u : Wkp mu Omega p 0) :
    seminorm 0 0 h u = ‖u‖ := by
  rw [seminorm_zero_apply, value_zero]

/-- On `W^{1,p}(Ω)`, the `0`th seminorm is the `Lᵖ` norm of `W1p.value`. -/
theorem seminorm_one_zero (h : 0 ≤ 1) (u : Wkp mu Omega p 1) :
    seminorm 1 0 h u = ‖W1p.value u‖ := by
  rw [seminorm_zero_apply, value_one]

/-- On `W^{1,p}(Ω)`, the `1`st seminorm is the `Lᵖ` norm of `W1p.gradient`. -/
theorem seminorm_one_one (h : 1 ≤ 1) (u : Wkp mu Omega p 1) :
    seminorm 1 1 h u = ‖W1p.gradient u‖ := by
  rw [seminorm_succ_apply, toOrderL_self_apply, iteratedGradient_zero]

/-- At positive order `k + 1`, the top seminorm `|u|_{k+1,p}` is `‖iteratedGradient k u‖`. -/
theorem seminorm_top_succ (k : ℕ) (h : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self_apply]

/-- Pulling back the `i`th seminorm on `W^{j,p}(Ω)` along `toOrderL` gives the `i`th seminorm on
`W^{k,p}(Ω)`. -/
theorem seminorm_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) j i hij).comp (toOrderL hjk).toLinearMap =
      seminorm k i (hij.trans hjk) := by
  ext u
  cases i with
  | zero =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_zero_apply,
        value_toOrderL]
  | succ i =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_succ_apply]
      rw [toOrderL_toOrderL]

/-- Order truncation preserves every Sobolev seminorm up to the truncated order. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i hij (toOrderL hjk u) = seminorm k i (hij.trans hjk) u :=
  DFunLike.congr_fun (seminorm_comp_toOrderL hij hjk) u

/-- The `j`th seminorm of `lowerOrder k u` (`j ≤ k`) equals the `j`th seminorm of `u` at order
`k + 1`. -/
theorem seminorm_lowerOrder {j k : ℕ} (h : j ≤ k) (h' : j ≤ k + 1)
    (u : Wkp mu Omega p (k + 1)) :
    seminorm k j h (lowerOrder k u) = seminorm (k + 1) j h' u := by
  rw [← toOrderL_succ_self_apply k k.le_succ u, seminorm_toOrderL]

/-- For `j ≤ k + 1`, the `j`th seminorm of `mk k u D hD` is the `j`th seminorm of `u`. -/
theorem seminorm_mk_of_le {j k : ℕ} (h : j ≤ k + 1) (h' : j ≤ k + 2)
    (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) j h' (mk k u D hD) = seminorm (k + 1) j h u := by
  rw [← seminorm_lowerOrder h h', lowerOrder_mk]

/-- The top seminorm of `mk k u D hD` is the `Lᵖ` norm of the adjoined weak derivative `D`. -/
theorem seminorm_mk_top (k : ℕ) (h : k + 2 ≤ k + 2) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) (k + 2) h (mk k u D hD) = ‖D‖ := by
  rw [seminorm_top_succ, iteratedGradient_mk]

/-- Every Sobolev seminorm is bounded by the full Sobolev graph norm. -/
theorem seminorm_le_norm {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      exact norm_value_le k u
  | succ j =>
      rw [seminorm_succ_apply]
      exact (norm_iteratedGradient_le j (toOrderL h u)).trans (norm_toOrderL_apply_le h u)

/-- As bundled seminorms, each `seminorm k j h` is bounded by `normSeminorm`. -/
theorem seminorm_le_normSeminorm {j k : ℕ} (h : j ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k j h ≤
      normSeminorm ℝ (Wkp mu Omega p k) :=
  seminorm_le_norm h

/-- Every Sobolev seminorm is `1`-Lipschitz with respect to the Sobolev graph norm. -/
theorem lipschitzWith_seminorm {j k : ℕ} (h : j ≤ k) :
    LipschitzWith 1 (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  LipschitzWith.of_dist_le_mul fun u v => by
    rw [NNReal.coe_one, one_mul, Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
    exact ((seminorm k j h).norm_sub_map_le_sub u v).trans (seminorm_le_norm h (u - v))

/-- Every Sobolev seminorm is continuous with respect to the Sobolev graph topology. -/
theorem continuous_seminorm {j k : ℕ} (h : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  (lipschitzWith_seminorm h).continuous

/-- The `0`th Sobolev seminorm vanishes if and only if the Sobolev function itself vanishes. -/
theorem seminorm_zero_eq_zero_iff {k : ℕ} (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = 0 ↔ u = 0 := by
  have hv0 : value (mu := mu) (Omega := Omega) (p := p) k 0 = 0 := by
    rw [← valueL_apply, map_zero]
  rw [seminorm_zero_apply, norm_eq_zero]
  exact ⟨fun hu => ext k (hu.trans hv0.symm), fun hu => hu ▸ hv0⟩

/-- For `j + 1 ≤ k`, the `(j + 1)`st Sobolev seminorm vanishes if and only if the weak derivative
field `iteratedGradient j (toOrderL h u)` vanishes in `Lᵖ(Ω)`. -/
theorem seminorm_succ_eq_zero_iff {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = 0 ↔ iteratedGradient j (toOrderL h u) = 0 := by
  rw [seminorm_succ_apply, norm_eq_zero]

/-- At positive order `k + 1`, the top seminorm vanishes if and only if `iteratedGradient k u`
vanishes in `Lᵖ(Ω)`. -/
theorem seminorm_top_succ_eq_zero_iff (k : ℕ) (h : k + 1 ≤ k + 1)
    (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = 0 ↔ iteratedGradient k u = 0 := by
  rw [seminorm_top_succ, norm_eq_zero]

/-- **Classical identification of Sobolev seminorms.** If `u ∈ W^{k,p}(Ω)` is represented almost
everywhere on `Ω` by a function `f` that is `C^j` on `Ω` (`j ≤ k`), then `|u|_{j,p}` equals the
classical `Lᵖ(Ω)` derivative seminorm `lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`. Only
`C^j` regularity is needed. -/
theorem seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn {j k : ℕ} (h : j ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u = lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, Lp.norm_def, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen
          le_rfl).aestronglyMeasurable Omega.isOpen.measurableSet) ?_
      filter_upwards [hu] with x hx
      rw [hx, norm_iteratedFDeriv_zero]
  | succ j =>
      rw [seminorm_succ_apply]
      refine norm_iteratedGradient_eq_lpNorm_of_contDiffOn j (toOrderL h u) hf ?_
      rw [value_toOrderL]
      exact hu

/-- For an embedded test function `φ ∈ 𝓓(Ω, ℝ)`, the `j`th Sobolev seminorm equals the ambient
`Lᵖ` norm of its `j`th classical derivative `iteratedFDeriv ℝ j φ`. -/
theorem seminorm_ofTestFunctionₗ {j k : ℕ} (h : j ≤ k) (phi : 𝓓(Omega, ℝ)) :
    seminorm k j h (ofTestFunctionₗ (mu := mu) (p := p) k phi) =
      lpNorm (iteratedFDeriv ℝ j (phi : E → ℝ)) p mu := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, Lp.norm_def, ← Lp.eNorm_def, enorm_value_ofTestFunctionₗ, lpNorm]
      congr 2
      exact (eLpNorm_congr_norm_ae
        ((phi.contDiff.continuous_iteratedFDeriv (by simp)).aestronglyMeasurable)
        phi.continuous.aestronglyMeasurable
        (.of_forall fun x => norm_iteratedFDeriv_zero)).symm
  | succ j =>
      rw [seminorm_succ_apply, toOrderL_ofTestFunctionₗ, Lp.norm_def, ← Lp.eNorm_def,
        enorm_iteratedGradient_ofTestFunctionₗ, lpNorm]

/-- Restricting to an open subdomain `U ≤ Ω` does not increase any Sobolev seminorm. -/
theorem seminorm_restrictL_le (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h (restrictL hU k u) ≤ seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, ← toOrderL_zero_apply k h,
        ← toOrderL_zero_apply k h u, toOrderL_restrictL]
      exact norm_restrictL_le hU 0 (toOrderL h u)
  | succ j =>
      let hmeas : mu.restrict U ≤ (1 : ℝ≥0∞) • mu.restrict Omega := by
        simpa only [one_smul] using Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
      rw [seminorm_succ_apply, seminorm_succ_apply, iteratedGradient_toOrderL_restrictL]
      have hop : ‖Lp.LpToLpOfMeasureLeSMul (E := IteratedGradient E j) (p := p) (c := 1)
          (by simp) hmeas‖ ≤ 1 := by
        simpa only [ENNReal.toReal_one, Real.one_rpow] using
          Lp.norm_LpToLpOfMeasureLeSMul_le (E := IteratedGradient E j) (p := p) (c := 1)
            (by simp) hmeas
      simpa only [one_mul] using
        (Lp.LpToLpOfMeasureLeSMul (E := IteratedGradient E j) (p := p) (c := 1) (by simp)
          hmeas).le_of_opNorm_le hop (iteratedGradient j (toOrderL h u))

/-- **Change of exponent for Sobolev seminorms.** On a domain of finite measure and for `p ≤ q`,
every Sobolev seminorm satisfies `|u|_{j,p} ≤ μ(Ω) ^ (1/p - 1/q) |u|_{j,q}`. -/
theorem seminorm_ofExponentLEL_le [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    seminorm k j h (ofExponentLEL hpq k u) ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, value_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (value k u)
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, iteratedGradient_toOrderL_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (iteratedGradient j (toOrderL h u))

/-- Transport along a measure-preserving linear isometry preserves every Sobolev seminorm. -/
@[simp]
theorem seminorm_compLinearIsometryEquiv (he : MeasurePreserving e mu nu)
    (hUW' : (U : Set E) = e ⁻¹' W') {j k : ℕ} (h : j ≤ k) (u : Wkp nu W' p k) :
    seminorm k j h (compLinearIsometryEquiv he hUW' k u) = seminorm k j h u := by
  have hr : MeasurePreserving e (mu.restrict U) (nu.restrict W') :=
    hUW' ▸ he.restrict_preimage W'.isOpen.measurableSet
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, ← toOrderL_zero_apply k h,
        ← toOrderL_zero_apply k h u, toOrderL_compLinearIsometryEquiv]
      exact (compLinearIsometryEquiv he hUW' 0).norm_map _
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply]
      set v := toOrderL h u
      let g := Lp.compMeasurePreserving e hr (iteratedGradient j v)
      have hgnorm : ‖g‖ = ‖iteratedGradient j v‖ :=
        Lp.norm_compMeasurePreserving (iteratedGradient j v) hr
      rw [← hgnorm, Lp.norm_def, Lp.norm_def]
      congr 1
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) ?_
      filter_upwards [iteratedGradient_toOrderL_compLinearIsometryEquiv_ae he hUW' h u,
        Lp.coeFn_compMeasurePreserving (iteratedGradient j v) hr] with x hx hgx
      rw [hx, LinearIsometryEquiv.norm_map, hgx, Function.comp_apply]

/-- Whole-space translation preserves every Sobolev seminorm. -/
@[simp]
theorem seminorm_translate (v : E) {j k : ℕ} (h : j ≤ k) (u : Wkp mu ⊤ p k) :
    seminorm k j h (translate v k u) = seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, value_translate]
      exact ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p v).norm_map _
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, iteratedGradient_toOrderL_translate]
      exact ((mu.restrict ((⊤ : Opens E) : Set E)).translateLp p v).norm_map _

/-! ### Equivalence of the Sobolev norm and the seminorms -/

/-- At order `0`, the sum of squared seminorms is `‖u‖²`. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    (∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2) = ‖u‖ ^ 2 := by
  rw [Fin.sum_univ_one]
  exact congrArg (· ^ 2) (seminorm_zero_zero _ u)

/-- Splitting off the top seminorm at order `k + 1` expresses the sum of squared seminorms in
terms of `lowerOrder k u` and `iteratedGradient k u`. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    (∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2) =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2) +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (· ^ 2) (seminorm_lowerOrder j.is_le (j.castSucc).is_le u).symm
  · exact congrArg (· ^ 2) (seminorm_top_succ k (Fin.last (k + 1)).is_le u)

/-- For every order `k` and exponent `1 ≤ p ≤ ∞`, the squared Sobolev norm is at most twice the
sum of squared seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      linarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      nlinarith [norm_nonneg u, sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have hlow := norm_sq_le_two_mul_sum_seminorm_sq (lowerOrder (k + 1) u)
      linarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- For every order `k` and exponent `1 ≤ p ≤ ∞`, the sum of squared seminorms is at most twice
the squared Sobolev norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      linarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have h₀ : ‖lowerOrder 0 u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_lowerOrder_le 0 u) 2
      have h₁ : ‖iteratedGradient 0 u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_iteratedGradient_le 0 u) 2
      linarith
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have hlow := sum_seminorm_sq_le_two_mul_norm_sq (lowerOrder (k + 1) u)
      linarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Upper comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`1 ≤ p ≤ ∞`, `‖u‖ ≤ √2 √(∑_{j=0}^k |u|_{j,p}²)`. -/
theorem norm_le_sqrt_two_mul {k : ℕ} (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
  calc ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ √(2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
        Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq u)
    _ = √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
        Real.sqrt_mul zero_le_two _

/-- **Lower comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`1 ≤ p ≤ ∞`, `√(∑_{j=0}^k |u|_{j,p}²) ≤ √2 ‖u‖`. -/
theorem sqrt_le_sqrt_two_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ :=
  calc √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2)
      ≤ √(2 * ‖u‖ ^ 2) := Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq u)
    _ = √2 * ‖u‖ := by rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq (norm_nonneg u)]

/-- At exponent `p = 2`, the squared Sobolev norm equals the sum of squared seminorms at every
order `k`. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k u,
        norm_sq_eq_sum_seminorm_sq (lowerOrder k u), sum_seminorm_sq_succ k u]

/-- At exponent `p = 2`, the Sobolev norm equals `√(∑_{j=0}^k |u|_{j,2}²)` at every order `k`. -/
theorem norm_eq_sqrt_sum_seminorm_sq {k : ℕ} (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq u, Real.sqrt_sq (norm_nonneg u)]

/-- The Sobolev norm is bounded by the `ℓ¹` sum of the Sobolev seminorms. -/
theorem norm_le_sum_seminorm :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ≤ ∑ j : Fin (k + 1), seminorm k j j.is_le u
  | 0, u => by
      rw [Fin.sum_univ_one]
      exact (seminorm_zero_zero _ u).ge
  | k + 1, u => by
      rw [Fin.sum_univ_castSucc]
      have hlow := norm_le_sum_seminorm (lowerOrder k u)
      have hsum : (∑ j : Fin (k + 1), seminorm (k + 1) (j.castSucc) (j.castSucc).is_le u) =
          ∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) :=
        Finset.sum_congr rfl fun j _ => (seminorm_lowerOrder j.is_le (j.castSucc).is_le u).symm
      rw [hsum, show seminorm (k + 1) (Fin.last (k + 1)) (Fin.last (k + 1)).is_le u =
          ‖iteratedGradient k u‖ from seminorm_top_succ k _ u]
      linarith [norm_le_norm_lowerOrder_add_norm_iteratedGradient k u]

/-- The `ℓ¹` sum of the Sobolev seminorms is at most `(k + 1) ‖u‖`. -/
theorem sum_seminorm_le_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    (∑ j : Fin (k + 1), seminorm k j j.is_le u) ≤ (k + 1 : ℝ) * ‖u‖ := by
  calc (∑ j : Fin (k + 1), seminorm k j j.is_le u)
      ≤ ∑ _ : Fin (k + 1), ‖u‖ := Finset.sum_le_sum fun j _ => seminorm_le_norm j.is_le u
    _ = (k + 1 : ℝ) * ‖u‖ := by simp [nsmul_eq_mul]

/-- The sum of squared Sobolev seminorms vanishes if and only if `u = 0`. -/
@[simp]
theorem sum_seminorm_sq_eq_zero_iff {k : ℕ} (u : Wkp mu Omega p k) :
    (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) = 0 ↔ u = 0 := by
  refine ⟨fun h => ?_, fun h => by subst h; simp⟩
  have h0 : ‖u‖ ^ 2 ≤ 0 := by
    simpa only [h, mul_zero] using norm_sq_le_two_mul_sum_seminorm_sq u
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h0 (sq_nonneg ‖u‖)))

end Wkp

end TruncationAndSeminorms

end TauCeti
