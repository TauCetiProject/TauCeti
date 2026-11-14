/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Exponent
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Order truncation and derivative seminorms on `W^{k,p}`

An element of `TauCeti.Wkp mu Omega p k` is built recursively by adjoining one weak derivative at
each stage above `W^{1,p}(Ω)`, with `TauCeti.Wkp.lowerOrderL` forgetting the highest derivative by
one step. Iterating `lowerOrderL` gives the continuous linear truncation
`TauCeti.Wkp.toOrderL : W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for every `j ≤ k`, and composing it
with `TauCeti.Wkp.iteratedGradientL` accesses the intermediate weak derivative field of order
`j + 1` inside `W^{k,p}(Ω)`.

From these intermediate derivative projections we package the homogeneous derivative seminorms
`|u|_{j,p}` (`0 ≤ j ≤ k`) as bundled Mathlib `Seminorm`s `TauCeti.Wkp.seminorm k j hj`. On `C^j`
representatives each seminorm agrees with the classical `Lᵖ` norm of `iteratedFDeriv ℝ j f`; it
is monotone under domain restriction and obeys Hölder's bound `μ(Ω) ^ (1/p - 1/q)` under lowering
the integrability exponent on domains of finite measure.

Finally, we compare the iterated weak-derivative graph norm `‖u‖` of `W^{k,p}(Ω)` with the
Euclidean combination `S(u) = (∑_{j ≤ k} |u|_{j,p}²)^{1/2}`. Above first order each
`WeakDerivStep` uses an `ℓ²` product norm, while at first order `W^{1,p}` takes the `Lᵖ` norm of
the pointwise Euclidean value-gradient jet. Consequently `‖u‖ = S(u)` holds with equality at
`p = 2` for every order `k`, and for arbitrary `1 ≤ p ≤ ∞` the two quantities are equivalent
within a universal factor of `√2` independent of the dimension, domain, exponent, and Sobolev
order: `S(u) ≤ √2 ‖u‖` and `‖u‖ ≤ √2 S(u)`.

## Main definitions

* `TauCeti.Wkp.toOrderL`: continuous linear truncation `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` (`j ≤ k`).
* `TauCeti.Wkp.seminorm`: the homogeneous order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)`,
  bundled as `Seminorm ℝ (Wkp mu Omega p k)`.

## Main results

* `TauCeti.Wkp.toOrderL_self`, `TauCeti.Wkp.toOrderL_comp_toOrderL`, `TauCeti.Wkp.value_toOrderL`:
  functoriality of order truncation and compatibility with the `Lᵖ` value projection.
* `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_of_contDiffOn`: identification of intermediate weak derivatives
  and Sobolev seminorms with classical derivatives of `C^j` representatives.
* `TauCeti.Wkp.toOrderL_restrictL`, `TauCeti.Wkp.seminorm_restrictL_le`: compatibility of order
  truncation and seminorms with restriction to an open subdomain.
* `TauCeti.Wkp.toOrderL_ofExponentLEL`, `TauCeti.Wkp.seminorm_ofExponentLEL_le`: compatibility with
  exponent inclusion `W^{k,q}(Ω) →L[ℝ] W^{k,p}(Ω)` and the bound
  `|u|_{j,p} ≤ μ(Ω) ^ (1/p - 1/q) |u|_{j,q}`.
* `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`, `TauCeti.Wkp.norm_le_sqrt_two_mul`,
  `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`: exact Euclidean seminorm formula at `p = 2` and
  two-sided `√2` comparison for general `1 ≤ p ≤ ∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.2.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Chapter 3.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  §4.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

section Ambient

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

section TruncationAndSeminorm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Order truncation -/

/-- Continuous linear truncation `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for `j ≤ k`, forgetting the
weak derivatives of order strictly above `j`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j :=
  Nat.leRec (motive := fun k _ => Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun ⦃m⦄ _ ih => ih.comp (lowerOrderL m)) h

/-- Truncating `W^{k,p}(Ω)` to the same order `k` is the identity continuous linear map. -/
@[simp]
theorem toOrderL_self {k : ℕ} (h : k ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = ContinuousLinearMap.id ℝ _ := by
  rw [toOrderL]
  exact Nat.leRec_self _ _

/-- Truncating from `k + 1` to `j` factors through `lowerOrderL k`. -/
theorem toOrderL_comp_lowerOrderL {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) h).comp (lowerOrderL k) =
      toOrderL (Nat.le_succ_of_le h) := by
  rw [toOrderL, toOrderL]
  exact (Nat.leRec_succ (motive := fun m _ => Wkp mu Omega p m →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun ⦃m⦄ _ ih => ih.comp (lowerOrderL m)) h).symm

/-- Applying `toOrderL` after `lowerOrder` agrees with truncating directly from `k + 1`. -/
theorem toOrderL_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    toOrderL h (lowerOrder k u) = toOrderL (Nat.le_succ_of_le h) u := by
  rw [← lowerOrderL_apply, ← ContinuousLinearMap.comp_apply, toOrderL_comp_lowerOrderL]

/-- Order truncation preserves the `Lᵖ` value component. -/
@[simp]
theorem value_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    value j (toOrderL h u) = value k u := by
  induction h with
  | refl => rw [toOrderL_self, ContinuousLinearMap.id_apply]
  | @step m hjm ih => rw [← toOrderL_lowerOrder hjm, ih, value_succ]

/-- Composing the value projection with `toOrderL` recovers the higher-order value projection. -/
@[simp]
theorem valueL_comp_toOrderL {j k : ℕ} (h : j ≤ k) :
    (valueL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h) = valueL k :=
  ContinuousLinearMap.ext fun u => by simp

/-- Order truncation is injective because weak derivatives are uniquely determined by the `Lᵖ`
value component. -/
theorem toOrderL_injective {j k : ℕ} (h : j ≤ k) :
    Function.Injective (toOrderL (mu := mu) (Omega := Omega) (p := p) h) := fun _ _ huv =>
  ext k (by simpa only [value_toOrderL] using congrArg (value j) huv)

/-- Truncating to order zero is the `Lᵖ` value projection `valueL`. -/
@[simp]
theorem toOrderL_zero {k : ℕ} (h : 0 ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = valueL k :=
  ContinuousLinearMap.ext fun u => by simpa only [value_zero, valueL_apply] using value_toOrderL h u

/-- Truncating by one order from `k + 1` to `k` is `lowerOrderL k`. -/
theorem toOrderL_succ_self (k : ℕ) (h : k ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = lowerOrderL k :=
  ContinuousLinearMap.ext fun u => ext k (by rw [value_toOrderL, lowerOrderL_apply, ← value_succ])

/-- Truncating a positive-order Sobolev space to order one agrees with `firstOrderL`. -/
theorem toOrderL_eq_firstOrderL (k : ℕ) (h : 1 ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = firstOrderL k :=
  -- `firstOrderL k` has codomain `W1p`, so `DFunLike.coe` at codomain `Wkp … 1` only unifies with
  -- `firstOrderL_apply` at default transparency rather than under `rw`.
  ContinuousLinearMap.ext fun u => ext 1 <|
    (value_toOrderL h u).trans ((value_firstOrder k u).symm.trans
      ((value_one (firstOrder k u)).symm.trans (congrArg (value 1) (firstOrderL_apply k u).symm)))

/-- Successive order truncations compose to a single truncation. -/
@[simp]
theorem toOrderL_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL hij (toOrderL hjk u) = toOrderL (hij.trans hjk) u :=
  ext i (by rw [value_toOrderL, value_toOrderL, value_toOrderL])

/-- Continuous linear order truncations compose transitively. -/
@[simp]
theorem toOrderL_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) hij).comp (toOrderL hjk) =
      toOrderL (hij.trans hjk) :=
  ContinuousLinearMap.ext (toOrderL_toOrderL hij hjk)

/-- Forgetting one further derivative after truncating to `j + 1` truncates to `j`. -/
theorem lowerOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    lowerOrder j (toOrderL h u) = toOrderL (Nat.le_of_succ_le h) u :=
  ext j (by rw [← value_succ, value_toOrderL, value_toOrderL])

/-- Composing `lowerOrderL j` on the left with `toOrderL` lowers the target order by one. -/
theorem lowerOrderL_comp_toOrderL {j k : ℕ} (h : j + 1 ≤ k) :
    (lowerOrderL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h) =
      toOrderL (Nat.le_of_succ_le h) :=
  ContinuousLinearMap.ext fun u => by
    rw [ContinuousLinearMap.comp_apply, lowerOrderL_apply, lowerOrder_toOrderL]

/-- Truncating `mk k u D hD` to any order `j ≤ k + 1` drops the adjoined top derivative and
truncates `u`. -/
theorem toOrderL_mk {j k : ℕ} (h : j ≤ k + 2) (hj : j ≤ k + 1) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    toOrderL h (mk k u D hD) = toOrderL hj u :=
  ext j (by rw [value_toOrderL, value_mk, value_toOrderL])

/-- Order truncation is norm-nonincreasing. -/
theorem norm_toOrderL_apply_le {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ := by
  induction h with
  | refl => rw [toOrderL_self, ContinuousLinearMap.id_apply]
  | @step m hjm ih =>
      rw [← toOrderL_lowerOrder hjm]
      exact (ih (lowerOrder m u)).trans (norm_lowerOrder_le m u)

/-- The operator norm of `toOrderL` is at most `1`. -/
theorem opNorm_toOrderL_le {j k : ℕ} (h : j ≤ k) :
    ‖toOrderL (mu := mu) (Omega := Omega) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_apply_le h u

/-! ### Intermediate weak derivatives -/

/-- For `1 ≤ k`, the first-order weak derivative `iteratedGradient 0 (toOrderL h u)` is the weak
gradient of `value k u`. -/
theorem hasWeakFDerivOn_value_toOrderL {k : ℕ} (h : 1 ≤ k) (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (value k u)
      (fun x => innerSL ℝ (iteratedGradient 0 (toOrderL h u) x)) := by
  rw [← value_toOrderL h u]
  exact hasWeakFDerivOn_value (toOrderL h u)

/-- Any two adjacent intermediate weak derivatives inside `W^{k,p}(Ω)` satisfy the weak Fréchet
derivative relation. -/
theorem hasWeakFDerivOn_iteratedGradient_toOrderL {j k : ℕ} (h' : j + 1 ≤ k) (h : j + 2 ≤ k)
    (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (iteratedGradient j (toOrderL h' u))
      (iteratedGradient (j + 1) (toOrderL h u)) := by
  rw [← lowerOrder_toOrderL h u]
  exact hasWeakFDerivOn_iteratedGradient j (toOrderL h u)

/-- If `u ∈ W^{k,p}(Ω)` has a `C^{j+1}` representative `f` on `Ω` (`j + 1 ≤ k`), its order
`j + 1` weak derivative agrees almost everywhere on `Ω` with the classical field
`iteratedGradientChain f j`. -/
theorem iteratedGradient_toOrderL_ae_eq_of_contDiffOn {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f j :=
  iteratedGradient_ae_eq_of_contDiffOn j (toOrderL h u) hf (by rwa [value_toOrderL])

/-! ### Derivative seminorms -/

/-- The order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` (`j ≤ k`), bundled as a Mathlib
`Seminorm`: at `j = 0` it is the `Lᵖ` norm of `value k u`, and at `j + 1` it is the `Lᵖ` norm of
the order-`(j + 1)` weak derivative `iteratedGradient j (toOrderL h u)`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ =>
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, h =>
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap

/-- At order zero, `seminorm k 0 h u` is the `Lᵖ` norm of the value component `value k u`. -/
@[simp]
theorem seminorm_zero_apply (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  rw [seminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe, valueL_apply]

/-- At positive derivative order `j + 1 ≤ k`, `seminorm k (j + 1) h u` is the `Lᵖ` norm of the
intermediate weak derivative `iteratedGradient j (toOrderL h u)`. -/
@[simp]
theorem seminorm_succ_apply {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  rw [seminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, iteratedGradientL_apply]

/-- The top seminorm at order `k + 1` is the `Lᵖ` norm of `iteratedGradient k u`. -/
theorem seminorm_succ_self (k : ℕ) (h : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Evaluating the order-`i` seminorm on a truncated Sobolev function recovers the order-`i`
seminorm on the original space. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i hij (toOrderL hjk u) = seminorm k i (hij.trans hjk) u := by
  cases i with
  | zero => rw [seminorm_zero_apply, seminorm_zero_apply, value_toOrderL]
  | succ m => rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_toOrderL]

/-- Pulling `seminorm j i hij` back along `toOrderL hjk` yields `seminorm k i (hij.trans hjk)`. -/
@[simp]
theorem seminorm_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) j i hij).comp (toOrderL hjk).toLinearMap =
      seminorm k i (hij.trans hjk) :=
  Seminorm.ext (seminorm_toOrderL hij hjk)

/-- Taking `lowerOrder k` preserves all seminorms of order `j ≤ k`. -/
theorem seminorm_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j h (lowerOrder k u) = seminorm (k + 1) j (Nat.le_succ_of_le h) u := by
  rw [← lowerOrderL_apply, ← toOrderL_succ_self k (Nat.le_succ k), seminorm_toOrderL]

/-- On `mk k u D hD`, every seminorm of order `j ≤ k + 1` agrees with that of `u`. -/
theorem seminorm_mk_of_le {j k : ℕ} (h : j ≤ k + 2) (hj : j ≤ k + 1)
    (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) j h (mk k u D hD) = seminorm (k + 1) j hj u := by
  rw [← seminorm_toOrderL le_rfl h, toOrderL_mk h hj, seminorm_toOrderL]

/-- On `mk k u D hD`, the top seminorm at order `k + 2` is `‖D‖`. -/
theorem seminorm_mk_self (k : ℕ) (h : k + 2 ≤ k + 2)
    (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hD : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) (k + 2) h (mk k u D hD) = ‖D‖ := by
  rw [seminorm_succ_self, iteratedGradient_mk]

/-- Every derivative seminorm is bounded by the Sobolev graph norm. -/
theorem seminorm_le_norm {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      exact norm_value_le k u
  | succ m =>
      rw [seminorm_succ_apply]
      exact (norm_iteratedGradient_le m (toOrderL h u)).trans (norm_toOrderL_apply_le h u)

/-- Every Sobolev derivative seminorm is continuous with respect to the graph norm. -/
theorem continuous_seminorm {j k : ℕ} (h : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  Seminorm.continuous_of_le (q := normSeminorm ℝ _) continuous_norm
    (Seminorm.le_def.2 (seminorm_le_norm h))

/-- The zeroth seminorm of `u` equals `lpNorm f p (mu.restrict Omega)` for any almost-everywhere
representative `f` of `value k u`. -/
theorem seminorm_zero_eq_lpNorm_of_ae_eq (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k 0 h u = lpNorm f p (mu.restrict Omega) := by
  rw [seminorm_zero_apply]
  exact Lp.norm_eq_lpNorm_of_ae_eq hu

/-- If `u ∈ W^{k,p}(Ω)` has a `C^j` representative `f` on `Ω` (`j ≤ k`), then `|u|_{j,p}`
equals the classical derivative seminorm `lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`. -/
theorem seminorm_eq_lpNorm_of_contDiffOn {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k)
    {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u = lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, Lp.norm_def, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen le_rfl).aestronglyMeasurable
          Omega.isOpen.measurableSet) ?_
      filter_upwards [hu] with x hx
      rw [hx, norm_iteratedFDeriv_zero]
  | succ m =>
      rw [seminorm_succ_apply]
      exact norm_iteratedGradient_eq_lpNorm_of_contDiffOn m (toOrderL h u) hf
        (by rwa [value_toOrderL])

/-! ### Restriction to an open subdomain -/

section Restriction

variable {U : Opens E}

/-- Order truncation commutes with restriction to an open subdomain. -/
theorem toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h (restrictL hU k u) = restrictL hU j (toOrderL h u) :=
  ext j (by rw [value_toOrderL, value_restrictL, value_restrictL, value_toOrderL])

/-- As continuous linear maps, `toOrderL` and `restrictL` commute. -/
theorem toOrderL_comp_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := U) (p := p) h).comp (restrictL hU k) =
      (restrictL hU j).comp (toOrderL h) :=
  ContinuousLinearMap.ext (toOrderL_restrictL hU h)

/-- Restricting to an open subdomain restricts each intermediate weak derivative in `Lᵖ`. -/
theorem iteratedGradient_toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) :
    iteratedGradient j (toOrderL h (restrictL hU k u)) =
      Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
        simpa only [one_smul] using
          Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU))
        (iteratedGradient j (toOrderL h u)) := by
  rw [toOrderL_restrictL, iteratedGradient_restrictL]

/-- Restricting to an open subdomain preserves each intermediate weak derivative almost everywhere
on the subdomain. -/
theorem iteratedGradient_toOrderL_restrictL_ae (hU : U ≤ Omega) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) :
    iteratedGradient j (toOrderL h (restrictL hU k u)) =ᵐ[mu.restrict U]
      iteratedGradient j (toOrderL h u) := by
  rw [toOrderL_restrictL]
  exact iteratedGradient_restrictL_ae hU j (toOrderL h u)

/-- Restricting to an open subdomain does not increase any derivative seminorm. -/
theorem seminorm_restrictL_le (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h (restrictL hU k u) ≤ seminorm k j h u := by
  have hle : mu.restrict (U : Set E) ≤ mu.restrict (Omega : Set E) :=
    Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hU)
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply,
        Lp.norm_eq_lpNorm_of_ae_eq (value_restrictL_ae hU k u)]
      exact lpNorm_le_norm_of_ae_eq_of_le hle .rfl
  | succ m =>
      rw [seminorm_succ_apply, seminorm_succ_apply,
        Lp.norm_eq_lpNorm_of_ae_eq (iteratedGradient_toOrderL_restrictL_ae hU h u)]
      exact lpNorm_le_norm_of_ae_eq_of_le hle .rfl

end Restriction

/-! ### Change of integrability exponent -/

section Exponent

variable {q : ℝ≥0∞} [Fact (1 ≤ q)] [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- Order truncation commutes with lowering the integrability exponent on a finite-measure
domain. -/
theorem toOrderL_ofExponentLEL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    toOrderL h (ofExponentLEL hpq k u) = ofExponentLEL hpq j (toOrderL h u) :=
  ext j (by rw [value_toOrderL, value_ofExponentLEL, value_ofExponentLEL, value_toOrderL])

/-- As continuous linear maps, `toOrderL` and `ofExponentLEL` commute. -/
theorem toOrderL_comp_ofExponentLEL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) h).comp (ofExponentLEL hpq k) =
      (ofExponentLEL hpq j).comp (toOrderL h) :=
  ContinuousLinearMap.ext (toOrderL_ofExponentLEL hpq h)

/-- Lowering the integrability exponent sends each intermediate weak derivative to its `Lᵖ`
copy. -/
theorem iteratedGradient_toOrderL_ofExponentLEL (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega q k) :
    iteratedGradient j (toOrderL h (ofExponentLEL hpq k u)) =
      Lp.ofExponentLEL ℝ _ hpq (iteratedGradient j (toOrderL h u)) := by
  rw [toOrderL_ofExponentLEL, iteratedGradient_ofExponentLEL]

/-- Lowering the integrability exponent preserves each intermediate weak derivative almost
everywhere. -/
theorem iteratedGradient_toOrderL_ofExponentLEL_ae (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega q k) :
    ⇑(iteratedGradient j (toOrderL h (ofExponentLEL hpq k u))) =ᵐ[mu.restrict Omega]
      iteratedGradient j (toOrderL h u) := by
  rw [toOrderL_ofExponentLEL]
  exact iteratedGradient_ofExponentLEL_ae hpq j (toOrderL h u)

/-- **Hölder bound on Sobolev seminorms under change of exponent.** On a domain `Ω` of finite
measure and for `1 ≤ p ≤ q ≤ ∞`, every order-`j` seminorm (`j ≤ k`) obeys
`|u|_{j,p} ≤ μ(Ω) ^ (1/p - 1/q) · |u|_{j,q}`. -/
theorem seminorm_ofExponentLEL_le (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    seminorm k j h (ofExponentLEL hpq k u) ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, value_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq (value k u)
  | succ m =>
      rw [seminorm_succ_apply, seminorm_succ_apply, iteratedGradient_toOrderL_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq (iteratedGradient m (toOrderL h u))

end Exponent

/-! ### Comparison between the graph norm and the derivative seminorms -/

/-- At order zero, the sum of squared seminorms reduces to the squared `Lᵖ` norm. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    (∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2) = ‖u‖ ^ 2 := by
  rw [Fin.sum_univ_one]
  simp only [Fin.val_zero]
  rw [seminorm_zero_apply, value_zero]

/-- Splitting off the top term expresses the sum of squared seminorms at order `m + 1` in terms of
`lowerOrder m u` and `iteratedGradient m u`. -/
theorem sum_seminorm_sq_succ (m : ℕ) (u : Wkp mu Omega p (m + 1)) :
    (∑ j : Fin (m + 2), seminorm (m + 1) j j.is_le u ^ 2) =
      (∑ j : Fin (m + 1), seminorm m j j.is_le (lowerOrder m u) ^ 2) +
        ‖iteratedGradient m u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_castSucc, seminorm_lowerOrder]
  · simp only [Fin.val_last]
    rw [seminorm_succ_self]

/-- **Upper squared comparison of the Sobolev graph norm with the derivative seminorms.** -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hle := norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u
      nlinarith [sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖), norm_nonneg u]
  | m + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ m u,
        sum_seminorm_sq_succ (m + 1) u]
      have ih := norm_sq_le_two_mul_sum_seminorm_sq (lowerOrder (m + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (m + 1) u‖]

/-- **Lower squared comparison of the Sobolev graph norm with the derivative seminorms.** -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have h0 := norm_lowerOrder_le 0 u
      have h1 := norm_iteratedGradient_le 0 u
      nlinarith [norm_nonneg (lowerOrder 0 u), norm_nonneg (iteratedGradient 0 u), norm_nonneg u]
  | m + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ m u,
        sum_seminorm_sq_succ (m + 1) u]
      have ih := sum_seminorm_sq_le_two_mul_norm_sq (lowerOrder (m + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (m + 1) u‖]

/-- **Upper comparison of the Sobolev graph norm with the derivative seminorms.** For every order
`k` and exponent `1 ≤ p ≤ ∞`, `‖u‖ ≤ √2 · (∑_{j ≤ k} |u|_{j,p}²)^{1/2}`. -/
theorem norm_le_sqrt_two_mul {k : ℕ} (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq u)

/-- **Lower comparison of the Sobolev graph norm with the derivative seminorms.** For every order
`k` and exponent `1 ≤ p ≤ ∞`, `(∑_{j ≤ k} |u|_{j,p}²)^{1/2} ≤ √2 · ‖u‖`. -/
theorem sqrt_le_sqrt_two_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq u)

end TruncationAndSeminorm

/-! ### Exact seminorm decomposition at `p = 2` -/

/-- At exponent `p = 2`, the squared Sobolev graph norm equals the sum of squared derivative
seminorms at every order `k`. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | m + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq m u, sum_seminorm_sq_succ,
        norm_sq_eq_sum_seminorm_sq (lowerOrder m u)]

/-- At exponent `p = 2`, the Sobolev graph norm equals the Euclidean combination of the derivative
seminorms at every order `k`. -/
theorem norm_eq_sqrt_sum_seminorm_sq {k : ℕ} (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq u, Real.sqrt_sq (norm_nonneg u)]

end Ambient

/-! ### Concrete numerical checks on `(0, 1)` and `(0, 2)` -/

section Examples

private local instance (a b : ℝ) :
    IsFiniteMeasure (volume.restrict ((⟨Set.Ioo a b, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
  inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo a b)))

private theorem lpNorm_two_Ioo_pow (b : ℝ) (n : ℕ) :
    lpNorm (fun x : ℝ => x ^ n) 2 (volume.restrict (Set.Ioo 0 b)) =
      √(b ^ (2 * n + 1) / (2 * n + 1 : ℝ)) := by
  rcases le_or_gt 0 b with hb | hb
  · have hmem : MemLp (fun x : ℝ => x ^ n) 2 (volume.restrict (Set.Ioo 0 b)) :=
      ((continuous_pow n).continuousOn (s := Set.Icc 0 b)).memLp_restrict_of_subset_isCompact
        isCompact_Icc measurableSet_Ioo Set.Ioo_subset_Icc_self 2
    rw [lpNorm, hmem.eLpNorm_two_eq_ofReal_sqrt_integral,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
    congr 1
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb]
    have heq : (fun x : ℝ => ‖x ^ n‖ ^ 2) = fun x : ℝ => x ^ (2 * n) := by
      ext x
      rw [Real.norm_eq_abs, sq_abs, ← pow_mul, Nat.mul_comm]
    rw [heq, integral_pow]
    push_cast
    rw [zero_pow (by positivity), sub_zero]
  · have hodd : Odd (2 * n + 1) := ⟨n, rfl⟩
    rw [Set.Ioo_eq_empty hb.not_gt, Measure.restrict_empty, lpNorm_measure_zero,
      Real.sqrt_eq_zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (hodd.pow_nonpos hb.le) (by positivity))]

-- On Ω = (0, 1) at k = 1, p = 2, u(x) = x satisfies toOrderL le_rfl u = u, |u|_{1,2} = 1,
-- and graph norm ‖u‖ = 2 / √3.
example : ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 1,
    (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun x => x) ∧
    toOrderL (mu := volume) (Omega := ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩) (p := 2) (k := 1)
      le_rfl u = u ∧
    seminorm 1 1 le_rfl u = 1 ∧
    ‖u‖ = 2 / √3 := by
  have hf : ContDiff ℝ (1 : ℕ) (fun x : ℝ => x) := contDiff_id
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ hf.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have h0 : seminorm 1 0 (by omega) u = 1 / √3 := by
    rw [seminorm_zero_eq_lpNorm_of_ae_eq 1 _ u hu, Opens.coe_mk]
    have hpow := lpNorm_two_Ioo_pow 1 1
    simp only [pow_one] at hpow
    rw [hpow]
    norm_num
  have h1 : seminorm 1 1 le_rfl u = 1 := by
    rw [seminorm_eq_lpNorm_of_contDiffOn le_rfl u hf.contDiffOn hu, Opens.coe_mk]
    have hnorm : lpNorm (iteratedFDeriv ℝ 1 (fun x : ℝ => x)) 2
          (volume.restrict (Set.Ioo 0 1)) =
        lpNorm (fun x : ℝ => x ^ 0) 2 (volume.restrict (Set.Ioo 0 1)) := by
      rw [lpNorm, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae
        ((ContinuousOn.continuousOn_iteratedFDeriv hf.contDiffOn isOpen_Ioo
          le_rfl).aestronglyMeasurable measurableSet_Ioo)
        aestronglyMeasurable_const (.of_forall fun x => ?_)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, deriv_id'', pow_zero]
    rw [hnorm, lpNorm_two_Ioo_pow 1 0]
    norm_num
  refine ⟨u, hu, by simp, h1, ?_⟩
  rw [norm_eq_sqrt_sum_seminorm_sq u, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, h0, h1]
  have hsum : (1 / √3) ^ 2 + 1 ^ 2 = (4 : ℝ) / 3 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hfour : √(4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)]
    norm_num
  rw [hsum, Real.sqrt_div (by positivity), hfour]

-- On Ω = (0, 1) at k = 2, p = 2, u(x) = x² has seminorms |u|_0 = 1 / √5, |u|_1 = 2 / √3,
-- and |u|_2 = 2.
example : ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2 2,
    (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun x => x ^ 2) ∧
    seminorm 2 0 (by omega) u = 1 / √5 ∧
    seminorm 2 1 (by omega) u = 2 / √3 ∧
    seminorm 2 2 le_rfl u = 2 := by
  have hf : ContDiff ℝ (2 : ℕ) (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo (0 : ℝ) 1, isOpen_Ioo⟩) (p := 2) 2 isOpen_univ hf.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rw [seminorm_zero_eq_lpNorm_of_ae_eq 2 _ u hu, Opens.coe_mk, lpNorm_two_Ioo_pow 1 2]
    norm_num
  · have hf1 : ContDiffOn ℝ (1 : ℕ) (fun x : ℝ => x ^ 2) (Set.Ioo 0 1) :=
      hf.contDiffOn.of_le (by norm_num)
    rw [seminorm_eq_lpNorm_of_contDiffOn (by omega) u hf1 hu, Opens.coe_mk]
    have hnorm : lpNorm (iteratedFDeriv ℝ 1 (fun x : ℝ => x ^ 2)) 2
          (volume.restrict (Set.Ioo 0 1)) =
        lpNorm ((2 : ℝ) • fun x : ℝ => x ^ 1) 2 (volume.restrict (Set.Ioo 0 1)) := by
      rw [lpNorm, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae
        ((ContinuousOn.continuousOn_iteratedFDeriv hf1 isOpen_Ioo le_rfl).aestronglyMeasurable
          measurableSet_Ioo)
        (((continuous_pow 1).const_smul (2 : ℝ)).aestronglyMeasurable) (.of_forall fun x => ?_)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one]
      simp [smul_eq_mul]
    rw [hnorm, lpNorm_const_smul, coe_nnNorm, Real.norm_of_nonneg zero_le_two,
      lpNorm_two_Ioo_pow 1 1]
    norm_num
    ring
  · rw [seminorm_eq_lpNorm_of_contDiffOn le_rfl u hf.contDiffOn hu, Opens.coe_mk]
    have hnorm : lpNorm (iteratedFDeriv ℝ 2 (fun x : ℝ => x ^ 2)) 2
          (volume.restrict (Set.Ioo 0 1)) =
        lpNorm ((2 : ℝ) • fun x : ℝ => x ^ 0) 2 (volume.restrict (Set.Ioo 0 1)) := by
      rw [lpNorm, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae
        ((ContinuousOn.continuousOn_iteratedFDeriv hf.contDiffOn isOpen_Ioo
          le_rfl).aestronglyMeasurable measurableSet_Ioo)
        (((continuous_pow 0).const_smul (2 : ℝ)).aestronglyMeasurable) (.of_forall fun x => ?_)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ, iteratedDeriv_one]
      have hd1 : deriv (fun y : ℝ => y ^ 2) = fun y : ℝ => 2 * y := by
        ext y
        simp
      rw [hd1]
      simp [smul_eq_mul]
    rw [hnorm, lpNorm_const_smul, coe_nnNorm, Real.norm_of_nonneg zero_le_two,
      lpNorm_two_Ioo_pow 1 0]
    norm_num

-- On Ω = (0, 2) with q = 2 and p = 1, the constant function u = 1 has |u|_{0,2} = √2 and
-- |ofExponentLEL u|_{0,1} = 2 = 2^(1/2) · √2, saturating seminorm_ofExponentLEL_le.
example : ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ 2 1,
    seminorm 1 0 (by omega) u = √2 ∧
    seminorm 1 0 (by omega) (ofExponentLEL (p := 1) (q := 2) (by norm_num) 1 u) = 2 := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ
    (contDiff_const (c := (1 : ℝ))).contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self
    (Set.subset_univ _)
  refine ⟨u, ?_, ?_⟩
  · have hone : (fun _ : ℝ => (1 : ℝ)) = fun x : ℝ => x ^ 0 := by
      ext x
      simp
    rw [seminorm_zero_eq_lpNorm_of_ae_eq 1 _ u hu, Opens.coe_mk, hone, lpNorm_two_Ioo_pow 2 0]
    norm_num
  · have hu1 : (value 1 (ofExponentLEL (p := 1) (q := 2) (by norm_num) 1 u) : ℝ → ℝ) =ᵐ[
        volume.restrict (Set.Ioo (0 : ℝ) 2)] (fun _ => (1 : ℝ)) :=
      (value_ofExponentLEL_ae (by norm_num) 1 u).trans hu
    rw [seminorm_zero_eq_lpNorm_of_ae_eq 1 _ _ hu1, Opens.coe_mk,
      lpNorm_const' one_ne_zero ENNReal.one_ne_top, measureReal_restrict_apply_univ,
      Real.volume_real_Ioo_of_le zero_le_two]
    norm_num

end Examples

end TauCeti.Wkp
