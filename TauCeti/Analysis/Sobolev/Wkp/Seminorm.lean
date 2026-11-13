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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Order truncation and seminorms on arbitrary-order Sobolev spaces

An element of `TauCeti.Wkp mu Omega p k` is built recursively by adjoining one weak derivative at a
time through `TauCeti.Wkp.lowerOrderL`. Iterating `lowerOrderL` yields the order-truncation
operators `TauCeti.Wkp.toOrderL (h : j ≤ k) : W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)`, which forget weak
derivatives strictly above order `j`. Through `toOrderL`, each intermediate weak derivative of order
`j + 1 ≤ k` is accessed uniformly as `TauCeti.Wkp.iteratedGradient j (toOrderL h u)`.

Taking `Lᵖ` norms of the value (`j = 0`) and of each intermediate weak derivative (`1 ≤ j ≤ k`)
defines the standard family of Sobolev seminorms `TauCeti.Wkp.seminorm k j h` on `W^{k,p}(Ω)`,
bundled as Mathlib `Seminorm`s over `ℝ`. Truncation, subdomain restriction
(`TauCeti.Wkp.restrictL`), and exponent lowering on finite-measure domains
(`TauCeti.Wkp.ofExponentLEL`) all commute with `toOrderL` and obey the corresponding seminorm
estimates. On smooth representatives, each seminorm agrees with the classical multilinear
derivative `Lᵖ` norm `MeasureTheory.lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`.

At `p = 2`, the iterated graph norm on `W^{k,2}(Ω)` equals the Euclidean combination
`S(u) = √(∑_{j ≤ k} |u|_{j,2}²)` at every order `k`. For general `1 ≤ p ≤ ∞`, the first-order
norm is the `Lᵖ` norm of the pointwise Euclidean norm of `(u, ∇u)` rather than
`(‖u‖_p² + ‖∇u‖_p²)^{1/2}`, while every higher graph step uses an exact Euclidean product norm.
Consequently `S(u)` and `‖u‖` are equivalent up to a universal factor of `√2` independent of `k`,
`p`, the dimension, and the domain: `‖u‖ ≤ √2 · S(u)` and `S(u) ≤ √2 · ‖u‖`. On `(0, 2π)` at
`p = ∞` and `k = 1`, `sin` has graph norm `1` and `S(sin) = √2`, showing that the factor `√2` in
`TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm` is sharp.

## Main definitions

* `TauCeti.Wkp.toOrderL`: continuous linear truncation `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for `j ≤ k`.
* `TauCeti.Wkp.seminorm`: the order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`,
  bundled as a `Seminorm ℝ (Wkp mu Omega p k)`.

## Main results

* `TauCeti.Wkp.toOrderL_self`, `TauCeti.Wkp.toOrderL_comp_toOrderL`, `TauCeti.Wkp.value_toOrderL`:
  functoriality of `toOrderL` and preservation of the `Lᵖ` value.
* `TauCeti.Wkp.toOrderL_restrictL`, `TauCeti.Wkp.toOrderL_ofExponentLEL`: commutation of `toOrderL`
  with subdomain restriction and with exponent lowering.
* `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_of_contDiffOn`,
  `TauCeti.Wkp.norm_iteratedFDeriv_le_seminorm_top_of_contDiffOn`: classical identification of
  intermediate weak derivatives and seminorms for `C^j` representatives, together with pointwise
  `L^∞` bounds.
* `TauCeti.Wkp.seminorm_restrictL_le`, `TauCeti.Wkp.seminorm_ofExponentLEL_le`: monotonicity under
  subdomain restriction and Hölder scaling `μ(Ω) ^ (1/p - 1/q)` under exponent lowering.
* `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`, `TauCeti.Wkp.norm_le_sqrt_two_mul`,
  `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`: exact `p = 2` identity and sharp `√2` norm comparisons
  for every `k` and `p`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., §3.1.
* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  §§4.1–4.2.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-! ### Order truncation -/

/-- Forget weak derivatives above order `j`, as a continuous linear map
`W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for `j ≤ k`. At `j = k` this is the identity, and each step in `k`
precomposes with `TauCeti.Wkp.lowerOrderL`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j :=
  Nat.leRec (motive := fun k _ => Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun k _ ih => ih.comp (lowerOrderL k)) h

/-- Truncating a Sobolev space to its own order is the identity operator. -/
@[simp]
theorem toOrderL_self {k : ℕ} (h : k ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = ContinuousLinearMap.id ℝ _ := by
  obtain rfl : h = le_rfl := Subsingleton.elim _ _
  exact Nat.leRec_self _ _

/-- Truncation from order `k + 1` to order `j ≤ k` factors through forgetting the top derivative at
order `k + 1` followed by truncation from `k` to `j`. -/
theorem toOrderL_succ {j k : ℕ} (h₁ : j ≤ k) (h₂ : j ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h₂ = (toOrderL h₁).comp (lowerOrderL k) := by
  obtain rfl : h₂ = Nat.le_succ_of_le h₁ := Subsingleton.elim _ _
  exact Nat.leRec_succ _ _ _

/-- One-step truncation from `k + 1` to `k` is `TauCeti.Wkp.lowerOrderL`. -/
theorem toOrderL_le_succ (k : ℕ) (h : k ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = lowerOrderL k := by
  rw [toOrderL_succ le_rfl h, toOrderL_self, ContinuousLinearMap.id_comp]

/-- Order truncations compose transitively as continuous linear maps. -/
@[simp]
theorem toOrderL_comp_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) hij).comp (toOrderL hjk) =
      toOrderL (hij.trans hjk) := by
  induction hjk with
  | refl => simp
  | @step m hm ih =>
      rw [toOrderL_succ hm (Nat.le_succ_of_le hm), ← ContinuousLinearMap.comp_assoc, ih,
        ← toOrderL_succ (hij.trans hm) (hij.trans (Nat.le_succ_of_le hm))]

/-- Applying two successive order truncations equals truncating directly to the lowest order. -/
@[simp]
theorem toOrderL_toOrderL {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL hij (toOrderL hjk u) = toOrderL (hij.trans hjk) u := by
  rw [← ContinuousLinearMap.comp_apply, toOrderL_comp_toOrderL]

/-- Precomposing truncation with `lowerOrderL` increases the source order by one. -/
theorem toOrderL_comp_lowerOrderL {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) h).comp (lowerOrderL k) =
      toOrderL (Nat.le_succ_of_le h) :=
  (toOrderL_succ h (Nat.le_succ_of_le h)).symm

/-- Truncating after `lowerOrder` equals truncating directly from order `k + 1`. -/
@[simp]
theorem toOrderL_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    toOrderL h (lowerOrder k u) = toOrderL (Nat.le_succ_of_le h) u := by
  rw [← lowerOrderL_apply, ← ContinuousLinearMap.comp_apply, toOrderL_comp_lowerOrderL]

/-- Postcomposing truncation to order `j + 1` with `lowerOrderL j` truncates to order `j`. -/
theorem lowerOrderL_comp_toOrderL {j k : ℕ} (h : j + 1 ≤ k) :
    (lowerOrderL (mu := mu) (Omega := Omega) (p := p) j).comp (toOrderL h) =
      toOrderL (Nat.le_of_succ_le h) := by
  rw [← toOrderL_le_succ j (Nat.le_succ j), toOrderL_comp_toOrderL]

/-- Forgetting one further derivative after truncating to `j + 1` truncates to `j`. -/
theorem lowerOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    lowerOrder j (toOrderL h u) = toOrderL (Nat.le_of_succ_le h) u := by
  rw [← lowerOrderL_apply, ← ContinuousLinearMap.comp_apply, lowerOrderL_comp_toOrderL]

/-- Evaluating truncation to order zero yields the `Lᵖ` value component. -/
theorem toOrderL_zero_left_apply (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h u = value k u := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [toOrderL_succ (Nat.zero_le k) h, ContinuousLinearMap.comp_apply, lowerOrderL_apply,
        ih (Nat.zero_le k), ← value_succ]

/-- Truncating to order zero is the continuous `Lᵖ` value projection `valueL`. -/
theorem toOrderL_zero_left (k : ℕ) (h : 0 ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = valueL k :=
  ContinuousLinearMap.ext fun u => (toOrderL_zero_left_apply k h u).trans (valueL_apply k u).symm

/-- Evaluating truncation to order one on `W^{k+1,p}` agrees with `firstOrder`. -/
theorem toOrderL_one_left_apply (k : ℕ) (h : 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    toOrderL h u = firstOrder k u := by
  induction k with
  | zero =>
      rw [toOrderL_self, ContinuousLinearMap.id_apply]
      exact (firstOrder_zero u).symm
  | succ k ih =>
      rw [toOrderL_succ (Nat.succ_le_succ (Nat.zero_le k)) h, ContinuousLinearMap.comp_apply,
        lowerOrderL_apply, ih (Nat.succ_le_succ (Nat.zero_le k)) (lowerOrder (k + 1) u),
        ← firstOrder_succ]

/-- Truncating a positive-order Sobolev space to order one is `firstOrderL`. -/
theorem toOrderL_one_left (k : ℕ) (h : 1 ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = firstOrderL k :=
  ContinuousLinearMap.ext fun u =>
    (toOrderL_one_left_apply k h u).trans (firstOrderL_apply k u).symm

/-- The `Lᵖ` value projection commutes with order truncation at the operator level. -/
@[simp]
theorem valueL_comp_toOrderL {j k : ℕ} (h : j ≤ k) :
    (valueL (mu := mu) (Omega := Omega) (p := p) j).comp (toOrderL h) = valueL k := by
  rw [← toOrderL_zero_left j (Nat.zero_le j), toOrderL_comp_toOrderL, toOrderL_zero_left]

/-- Order truncation preserves the `Lᵖ` value component. -/
@[simp]
theorem value_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    value j (toOrderL h u) = value k u := by
  rw [← valueL_apply, ← ContinuousLinearMap.comp_apply, valueL_comp_toOrderL, valueL_apply]

/-- Truncating `mk k u D hw` to any order `j ≤ k + 1` forgets the adjoined derivative `D` and
truncates `u`. -/
theorem toOrderL_mk {j k : ℕ} (h₁ : j ≤ k + 1) (h₂ : j ≤ k + 2) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hw : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    toOrderL h₂ (mk k u D hw) = toOrderL h₁ u := by
  rw [toOrderL_succ h₁ h₂, ContinuousLinearMap.comp_apply, lowerOrderL_apply, lowerOrder_mk]

/-- Order truncation is injective because weak derivatives are determined uniquely by the `Lᵖ`
value component. -/
theorem toOrderL_injective {j k : ℕ} (h : j ≤ k) :
    Function.Injective (toOrderL (mu := mu) (Omega := Omega) (p := p) h) := by
  intro u v huv
  apply ext k
  rw [← value_toOrderL h u, ← value_toOrderL h v, huv]

/-- Order truncation is norm-nonincreasing. -/
theorem norm_toOrderL_le {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ := by
  induction h with
  | refl => simp
  | @step m hm ih =>
      rw [toOrderL_succ hm (Nat.le_succ_of_le hm), ContinuousLinearMap.comp_apply,
        lowerOrderL_apply]
      exact (ih (lowerOrder m u)).trans (norm_lowerOrder_le m u)

/-- The operator norm of `toOrderL` is at most one. -/
theorem norm_toOrderL_le_one {j k : ℕ} (h : j ≤ k) :
    ‖toOrderL (mu := mu) (Omega := Omega) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_le h u

/-- For `1 ≤ k`, the `Lᵖ` value of `u ∈ W^{k,p}(Ω)` has weak Fréchet derivative given by pairing
with the first weak gradient `iteratedGradient 0 (toOrderL h u)`. -/
theorem hasWeakFDerivOn_value_toOrderL {k : ℕ} (h : 1 ≤ k) (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (value k u)
      (fun x => innerSL ℝ (iteratedGradient 0 (toOrderL h u) x)) := by
  simpa only [value_toOrderL h u] using hasWeakFDerivOn_value (toOrderL h u)

/-- Adjacent intermediate weak derivatives extracted via `toOrderL` satisfy the weak Fréchet
derivative relation on `Ω`. -/
theorem hasWeakFDerivOn_iteratedGradient_toOrderL {j k : ℕ} (h : j + 2 ≤ k)
    (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega
      (iteratedGradient j (toOrderL (Nat.le_of_succ_le h) u))
      (iteratedGradient (j + 1) (toOrderL h u)) := by
  rw [← lowerOrder_toOrderL h u]
  exact hasWeakFDerivOn_iteratedGradient j (toOrderL h u)

/-! ### Compatibility of truncation with restriction, exponent change, and smooth representatives -/

/-- Order truncation commutes with restriction to an open subdomain. -/
theorem toOrderL_restrictL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h (restrictL hU k u) = restrictL hU j (toOrderL h u) := by
  apply ext j
  rw [value_toOrderL, value_restrictL, value_restrictL, value_toOrderL]

/-- Subdomain restriction and order truncation commute as continuous linear maps. -/
theorem restrictL_comp_toOrderL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) :
    (restrictL (mu := mu) (p := p) hU j).comp (toOrderL h) =
      (toOrderL h).comp (restrictL hU k) :=
  ContinuousLinearMap.ext fun u => (toOrderL_restrictL hU h u).symm

/-- Restricting to an open subdomain restricts each intermediate weak derivative via
`MeasureTheory.Lp.LpToLpOfMeasureLeSMul`. -/
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

section Exponent

variable [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- On a finite-measure domain, order truncation commutes with lowering the integrability
exponent. -/
theorem toOrderL_ofExponentLEL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    toOrderL h (ofExponentLEL hpq k u) = ofExponentLEL hpq j (toOrderL h u) := by
  apply ext j
  rw [value_toOrderL, value_ofExponentLEL, value_ofExponentLEL, value_toOrderL]

/-- Exponent lowering and order truncation commute as continuous linear maps. -/
theorem ofExponentLEL_comp_toOrderL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) :
    (ofExponentLEL (mu := mu) (Omega := Omega) hpq j).comp (toOrderL h) =
      (toOrderL h).comp (ofExponentLEL hpq k) :=
  ContinuousLinearMap.ext fun u => (toOrderL_ofExponentLEL hpq h u).symm

/-- Lowering the exponent maps each intermediate weak derivative to its `Lᵖ` copy. -/
theorem iteratedGradient_toOrderL_ofExponentLEL (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega q k) :
    iteratedGradient j (toOrderL h (ofExponentLEL hpq k u)) =
      Lp.ofExponentLEL ℝ _ hpq (iteratedGradient j (toOrderL h u)) := by
  rw [toOrderL_ofExponentLEL, iteratedGradient_ofExponentLEL]

/-- Lowering the exponent leaves each intermediate weak derivative unchanged almost everywhere. -/
theorem iteratedGradient_toOrderL_ofExponentLEL_ae (hpq : p ≤ q) {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega q k) :
    ⇑(iteratedGradient j (toOrderL h (ofExponentLEL hpq k u))) =ᵐ[mu.restrict Omega]
      iteratedGradient j (toOrderL h u) := by
  rw [toOrderL_ofExponentLEL]
  exact iteratedGradient_ofExponentLEL_ae hpq j (toOrderL h u)

end Exponent

/-- For any `u ∈ W^{k,p}(Ω)` represented almost everywhere on `Ω` by a `C^{j+1}` function `f` with
`j + 1 ≤ k`, the order-`(j + 1)` weak derivative `iteratedGradient j (toOrderL h u)` agrees almost
everywhere on `Ω` with the classical iterated gradient `iteratedGradientChain f j`. -/
theorem iteratedGradient_toOrderL_ae_eq_of_contDiffOn {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f j :=
  iteratedGradient_ae_eq_of_contDiffOn j (toOrderL h u) hf (by rwa [value_toOrderL])

/-! ### Sobolev seminorms -/

/-- The order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`, bundled as a Mathlib
`Seminorm` over `ℝ`. At order `0` it is the `Lᵖ` norm of the value; at order `j + 1` it is the `Lᵖ`
norm of the order-`(j + 1)` weak derivative `iteratedGradient j (toOrderL h u)`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ => (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
      (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, h => (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
      ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
        (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap

/-- The order-zero Sobolev seminorm is the pullback of the `Lᵖ` norm along `valueL k`. -/
theorem seminorm_zero (k : ℕ) (h : 0 ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k 0 h =
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap :=
  (rfl)

/-- The order-`(j + 1)` Sobolev seminorm is the pullback of the `Lᵖ` norm along
`(iteratedGradientL j).comp (toOrderL h)`. -/
theorem seminorm_succ (k j : ℕ) (h : j + 1 ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k (j + 1) h =
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL (mu := mu) (Omega := Omega) (p := p) h)).toLinearMap :=
  (rfl)

/-- Evaluating the order-zero seminorm gives the `Lᵖ` norm of `value k u`. -/
@[simp]
theorem seminorm_zero_apply (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = ‖value k u‖ := by
  rw [seminorm_zero, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    valueL_apply]

/-- On `W^{0,p}(Ω) = Lᵖ(Ω)`, the order-zero Sobolev seminorm is `normSeminorm`. -/
@[simp]
theorem seminorm_zero_zero (h : 0 ≤ 0) :
    seminorm (mu := mu) (Omega := Omega) (p := p) 0 0 h =
      normSeminorm ℝ (Lp ℝ p (mu.restrict Omega)) := by
  ext u
  rw [seminorm_zero_apply, value_zero, coe_normSeminorm]

/-- Evaluating the order-`(j + 1)` seminorm gives the `Lᵖ` norm of
`iteratedGradient j (toOrderL h u)`. -/
@[simp]
theorem seminorm_succ_apply (k j : ℕ) (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) h u = ‖iteratedGradient j (toOrderL h u)‖ := by
  rw [seminorm_succ, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply, iteratedGradientL_apply]

/-- Evaluating the top seminorm on `W^{k+1,p}(Ω)` gives the `Lᵖ` norm of `iteratedGradient k u`. -/
theorem seminorm_succ_self_apply (k : ℕ) (h : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) h u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ_apply, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Pulling back the order-`i` seminorm along truncation `toOrderL h₂` gives the order-`i` seminorm
on the higher-order space. -/
@[simp]
theorem seminorm_comp_toOrderL {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) j i h₁).comp (toOrderL h₂).toLinearMap =
      seminorm k i (h₁.trans h₂) := by
  ext u
  cases i with
  | zero => simp
  | succ i =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_succ_apply]
      rw [toOrderL_toOrderL]

/-- Order truncation preserves all seminorms up to the truncated order. -/
@[simp]
theorem seminorm_toOrderL {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm j i h₁ (toOrderL h₂ u) = seminorm k i (h₁.trans h₂) u := by
  rw [← ContinuousLinearMap.coe_coe, ← Seminorm.comp_apply, seminorm_comp_toOrderL]

/-- Forgetting the highest derivative preserves every lower-order seminorm. -/
@[simp]
theorem seminorm_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j h (lowerOrder k u) = seminorm (k + 1) j (Nat.le_succ_of_le h) u := by
  rw [← lowerOrderL_apply, ← toOrderL_le_succ k (Nat.le_succ k), seminorm_toOrderL]

/-- Adjoining a top derivative via `mk` preserves all seminorms of orders up to `k + 1`. -/
theorem seminorm_mk {j k : ℕ} (h₁ : j ≤ k + 1) (h₂ : j ≤ k + 2) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (hw : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) j h₂ (mk k u D hw) = seminorm (k + 1) j h₁ u := by
  rw [← seminorm_lowerOrder h₁ (mk k u D hw), lowerOrder_mk]

/-- The order-zero seminorm vanishes if and only if the Sobolev function itself is zero, since the
`Lᵖ` value determines all weak derivatives. -/
theorem seminorm_zero_eq_zero_iff (k : ℕ) (h : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 h u = 0 ↔ u = 0 := by
  rw [seminorm_zero_apply, norm_eq_zero, ← valueL_apply]
  exact ⟨fun hu => ext k (by rw [← valueL_apply, ← valueL_apply, hu, map_zero]),
    fun hu => by rw [hu, map_zero]⟩

/-- Every Sobolev seminorm is bounded by the full Sobolev norm. -/
theorem seminorm_le_norm {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      exact norm_value_le k u
  | succ j =>
      rw [seminorm_succ_apply]
      exact (norm_iteratedGradient_le j (toOrderL h u)).trans (norm_toOrderL_le h u)

/-- In the lattice of real seminorms, each Sobolev seminorm is bounded above by `normSeminorm`. -/
theorem seminorm_le_normSeminorm {j k : ℕ} (h : j ≤ k) :
    seminorm (mu := mu) (Omega := Omega) (p := p) k j h ≤
      normSeminorm ℝ (Wkp mu Omega p k) :=
  fun u => seminorm_le_norm h u

/-- Every Sobolev seminorm is continuous with respect to the `W^{k,p}` norm topology. -/
theorem continuous_seminorm {j k : ℕ} (h : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j h) :=
  Seminorm.continuous_of_le continuous_norm (seminorm_le_normSeminorm h)

/-- Restricting a Sobolev function to an open subdomain does not increase any of its seminorms. -/
theorem seminorm_restrictL_le (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j h (restrictL hU k u) ≤ seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply]
      have h0 := norm_restrictL_le hU 0 (value k u)
      rwa [restrictL_zero hU, ← value_restrictL hU k u] at h0
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_restrictL, iteratedGradient_restrictL]
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
      simpa only [one_mul] using r.le_of_opNorm_le hop (iteratedGradient j (toOrderL h u))

/-- On a finite-measure domain, lowering the integrability exponent from `q` to `p ≤ q` scales each
Sobolev seminorm by at most `μ(Ω) ^ (1/p - 1/q)`. -/
theorem seminorm_ofExponentLEL_le [IsFiniteMeasure (mu.restrict (Omega : Set E))]
    (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    seminorm k j h (ofExponentLEL hpq k u) ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * seminorm k j h u := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, seminorm_zero_apply, value_ofExponentLEL]
      simpa only [Measure.restrict_apply_univ] using
        Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (value k u)
  | succ j =>
      rw [seminorm_succ_apply, seminorm_succ_apply, toOrderL_ofExponentLEL,
        iteratedGradient_ofExponentLEL]
      simpa only [Measure.restrict_apply_univ] using
        Lp.norm_ofExponentLEL_apply_le (𝕜 := ℝ) hpq (iteratedGradient j (toOrderL h u))

/-- If `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a `C^j` function `f` with
`j ≤ k`, then its order-`j` Sobolev seminorm equals the classical `Lᵖ` derivative seminorm
`lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`. -/
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
  | succ j =>
      rw [seminorm_succ_apply]
      exact norm_iteratedGradient_eq_lpNorm_of_contDiffOn j (toOrderL h u) hf
        (by rwa [value_toOrderL])

/-- At exponent `p = ∞`, if `u ∈ W^{k,∞}(Ω)` is represented almost everywhere on `Ω` by a `C^j`
function `f` with `j ≤ k` whose `j`-th Fréchet derivative has norm at most `C ≥ 0` on `Ω`, then
`seminorm k j h u ≤ C`. -/
theorem seminorm_top_le_of_contDiffOn {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega ∞ k)
    {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Omega, ‖iteratedFDeriv ℝ j f x‖ ≤ C) :
    seminorm k j h u ≤ C := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply]
      refine Lp.norm_top_le_of_ae_bound hC ?_
      filter_upwards [hu, ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
      simpa only [hx, norm_iteratedFDeriv_zero] using hbound x hxΩ
  | succ j =>
      rw [seminorm_succ_apply]
      refine Lp.norm_top_le_of_ae_bound hC ?_
      filter_upwards [iteratedGradient_toOrderL_ae_eq_of_contDiffOn h u hf hu,
        ae_restrict_mem Omega.isOpen.measurableSet] with x hx hxΩ
      rw [hx, norm_iteratedGradientChain]
      exact hbound x hxΩ

/-- At exponent `p = ∞`, if `u ∈ W^{k,∞}(Ω)` is represented almost everywhere on `Ω` by a `C^j`
function `f` with `j ≤ k`, then `‖iteratedFDeriv ℝ j f x₀‖ ≤ seminorm k j h u` at every point
`x₀ ∈ Omega`. -/
theorem norm_iteratedFDeriv_le_seminorm_top_of_contDiffOn {j k : ℕ} (h : j ≤ k)
    (u : Wkp mu Omega ∞ k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) {x₀ : E} (hx₀ : x₀ ∈ Omega) :
    ‖iteratedFDeriv ℝ j f x₀‖ ≤ seminorm k j h u := by
  have hae : ∀ᵐ x ∂mu.restrict Omega, ‖iteratedFDeriv ℝ j f x‖ ≤ seminorm k j h u := by
    cases j with
    | zero =>
        rw [seminorm_zero_apply]
        filter_upwards [hu, Lp.ae_norm_le_norm_top (value k u)] with x hx hle
        rwa [norm_iteratedFDeriv_zero, ← hx]
    | succ j =>
        rw [seminorm_succ_apply]
        filter_upwards [iteratedGradient_toOrderL_ae_eq_of_contDiffOn h u hf hu,
          Lp.ae_norm_le_norm_top (iteratedGradient j (toOrderL h u))] with x hx hle
        rwa [← norm_iteratedGradientChain, ← hx]
  by_contra! hlt
  let V : Set E := (Omega : Set E) ∩ (fun x => ‖iteratedFDeriv ℝ j f x‖) ⁻¹'
    Set.Ioi (seminorm k j h u)
  have hVopen : IsOpen V :=
    ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen le_rfl).norm).isOpen_inter_preimage
      Omega.isOpen isOpen_Ioi
  have hVpos : mu.restrict Omega V ≠ 0 := by
    rw [Measure.restrict_apply hVopen.measurableSet, Set.inter_eq_left.2 Set.inter_subset_left]
    exact hVopen.measure_ne_zero mu ⟨x₀, hx₀, hlt⟩
  exact hVpos (measure_eq_zero_iff_ae_notMem.2
    (hae.mono fun _ hx hxV => not_lt_of_ge hx hxV.2))

/-! ### Comparison between the Sobolev norm and the seminorms -/

/-- At order zero, the sum of squared Sobolev seminorms reduces to the squared `Lᵖ` norm. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    ∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2 = ‖u‖ ^ 2 := by
  simp

/-- At order `k + 1`, the sum of squared seminorms splits into the sum of squared seminorms of
`lowerOrder k u` plus the squared norm of the highest weak derivative `iteratedGradient k u`. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    ∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2 =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2) +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [seminorm_lowerOrder j.is_le u]
    rfl
  · simp only [Fin.val_last]
    rw [seminorm_succ_self_apply]

/-- At exponent `p = 2`, the squared Sobolev norm equals the sum of the squared seminorms at every
order `k`. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ (k : ℕ) (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k u,
        norm_sq_eq_sum_seminorm_sq k (lowerOrder k u), sum_seminorm_sq_succ k u]

/-- At exponent `p = 2`, the Sobolev norm equals the square root of the sum of squared seminorms at
every order `k`. -/
theorem norm_eq_sqrt_sum_seminorm_sq (k : ℕ) (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq k u, Real.sqrt_sq (norm_nonneg u)]

/-- For every order `k` and exponent `p`, the squared Sobolev norm is at most twice the sum of the
squared seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
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
      have ih := norm_sq_le_two_mul_sum_seminorm_sq (k + 1) (lowerOrder (k + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- For every order `k` and exponent `p`, the sum of the squared seminorms is at most twice the
squared Sobolev norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ (k : ℕ) (u : Wkp mu Omega p k),
      ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2 ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have hval := norm_lowerOrder_le 0 u
      have hgrad := norm_iteratedGradient_le 0 u
      nlinarith [norm_nonneg (lowerOrder 0 u), norm_nonneg (iteratedGradient 0 u)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      have ih := sum_seminorm_sq_le_two_mul_norm_sq (k + 1) (lowerOrder (k + 1) u)
      nlinarith [sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Upper comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`p`, the `W^{k,p}` graph norm is at most `√2` times the Euclidean combination of the seminorms. -/
theorem norm_le_sqrt_two_mul (k : ℕ) (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  calc
    ‖u‖ = √(‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ √(2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
      Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq k u)
    _ = √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) :=
      Real.sqrt_mul zero_le_two _

/-- **Lower comparison of the Sobolev norm with the seminorms.** For every order `k` and exponent
`p`, the Euclidean combination of the seminorms is at most `√2` times the `W^{k,p}` graph norm. -/
theorem sqrt_le_sqrt_two_mul_norm (k : ℕ) (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ := by
  calc
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √(2 * ‖u‖ ^ 2) :=
      Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq k u)
    _ = √2 * √(‖u‖ ^ 2) := Real.sqrt_mul zero_le_two _
    _ = √2 * ‖u‖ := by rw [Real.sqrt_sq (norm_nonneg u)]

/-- Convergence in `W^{k,p}(Ω)` is equivalent to convergence to zero in every Sobolev seminorm of
order `j ≤ k`. -/
theorem tendsto_iff_forall_seminorm_sub (k : ℕ) {I : Type*} {l : Filter I}
    {v : I → Wkp mu Omega p k} {u : Wkp mu Omega p k} :
    Filter.Tendsto v l (nhds u) ↔
      ∀ (j : ℕ) (hj : j ≤ k), Filter.Tendsto (fun i => seminorm k j hj (v i - u)) l (nhds 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  constructor
  · intro h j hj
    exact squeeze_zero (fun i => apply_nonneg _ _) (fun i => seminorm_le_norm hj (v i - u)) h
  · intro h
    have hsum : Filter.Tendsto
        (fun i => ∑ j : Fin (k + 1), seminorm k j j.is_le (v i - u) ^ 2) l (nhds 0) := by
      simpa using
        tendsto_finsetSum (Finset.univ : Finset (Fin (k + 1))) fun j _ => (h j j.is_le).pow 2
    have hbound : Filter.Tendsto
        (fun i => √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le (v i - u) ^ 2)) l (nhds 0) := by
      simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hsum).const_mul √2
    exact squeeze_zero (fun i => norm_nonneg _) (fun i => norm_le_sqrt_two_mul k (v i - u)) hbound

/-- At exponent `p = 2`, if `u ∈ W^{k,2}(Ω)` is represented almost everywhere on `Ω` by a `C^j`
function `f` with `j ≤ k`, then the squared order-`j` seminorm equals the integral over `Ω` of
`‖iteratedFDeriv ℝ j f x‖ ^ 2`. -/
theorem seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn {j k : ℕ} (h : j ≤ k)
    (u : Wkp mu Omega 2 k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j h u ^ 2 = ∫ x in Omega, ‖iteratedFDeriv ℝ j f x‖ ^ 2 ∂mu := by
  cases j with
  | zero =>
      rw [seminorm_zero_apply, ← Lp.integral_norm_sq_eq_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [hu] with x hx
      rw [hx, norm_iteratedFDeriv_zero]
  | succ j =>
      rw [seminorm_succ_apply, ← Lp.integral_norm_sq_eq_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [iteratedGradient_toOrderL_ae_eq_of_contDiffOn h u hf hu] with x hx
      rw [hx, norm_iteratedGradientChain]

/-! ### Concrete checks -/

section Examples

-- Check 1: On Ω = (0, 1) with p = 2, u(x) = x in W^{1,2}(0, 1) has toOrderL le_rfl u = u,
-- |u|_{0,2} = 1 / √3, |u|_{1,2} = 1, and graph norm ‖u‖ = 2 / √3.
example :
    ∃ u : Wkp volume ⟨Set.Ioo 0 1, isOpen_Ioo⟩ 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo 0 1)] (fun x : ℝ => x) ∧
      toOrderL (le_rfl : 1 ≤ 1) u = u ∧
      seminorm 1 0 (Nat.zero_le 1) u = 1 / √3 ∧
      seminorm 1 1 le_rfl u = 1 ∧
      ‖u‖ = 2 / √3 := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo 0 1, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ contDiff_id.contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have h0sq : seminorm 1 0 (Nat.zero_le 1) u ^ 2 = 1 / 3 := by
    rw [seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn (Nat.zero_le 1) u
      contDiff_id.contDiffOn hu, Opens.coe_mk, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    simp only [norm_iteratedFDeriv_zero, id_eq, Real.norm_eq_abs, sq_abs, integral_pow]
    norm_num
  have h1sq : seminorm 1 1 le_rfl u ^ 2 = 1 := by
    rw [seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn le_rfl u
      contDiff_id.contDiffOn hu, Opens.coe_mk, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    simp only [norm_iteratedFDeriv_one, fderiv_id, ContinuousLinearMap.norm_id, one_pow,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = 1 / √3 := by
    rw [← Real.sqrt_sq (apply_nonneg _ u), h0sq, Real.sqrt_div zero_le_one, Real.sqrt_one]
  have h1 : seminorm 1 1 le_rfl u = 1 := by
    rw [← Real.sqrt_sq (apply_nonneg _ u), h1sq, Real.sqrt_one]
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [← Real.sqrt_sq zero_le_two]
    norm_num
  have hnorm : ‖u‖ = 2 / √3 := by
    have hnsq : ‖u‖ ^ 2 = 4 / 3 := by
      rw [norm_sq_eq_sum_seminorm_sq 1 u, Fin.sum_univ_two]
      simp only [Fin.val_zero, Fin.val_one]
      linarith
    rw [← Real.sqrt_sq (norm_nonneg u), hnsq, Real.sqrt_div (by positivity), hsqrt4]
  exact ⟨u, hu, by simp, h0, h1, hnorm⟩

-- Check 2: On Ω = (0, 1) with p = 2, u(x) = x² in W^{2,2}(0, 1) has
-- |u|_{0,2} = 1 / √5, |u|_{1,2} = 2 / √3, and |u|_{2,2} = 2.
example :
    ∃ u : Wkp volume ⟨Set.Ioo 0 1, isOpen_Ioo⟩ 2 2,
      (value 2 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo 0 1)] (fun x : ℝ => x ^ 2) ∧
      seminorm 2 0 (Nat.zero_le 2) u = 1 / √5 ∧
      seminorm 2 1 (by decide) u = 2 / √3 ∧
      seminorm 2 2 le_rfl u = 2 := by
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo 0 1, isOpen_Ioo⟩) (p := 2) 2 isOpen_univ (contDiff_fun_id.pow 2).contDiffOn
    isCompact_Icc Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have h0sq : seminorm 2 0 (Nat.zero_le 2) u ^ 2 = 1 / 5 := by
    rw [seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn (Nat.zero_le 2) u
      (contDiff_fun_id.pow 2).contDiffOn hu, Opens.coe_mk,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hfun : (fun x : ℝ => ‖iteratedFDeriv ℝ 0 (fun y : ℝ => y ^ 2) x‖ ^ 2) =
        fun x : ℝ => x ^ 4 := by
      ext x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, sq_abs]
      ring
    rw [hfun, integral_pow]
    norm_num
  have h1sq : seminorm 2 1 (by decide) u ^ 2 = 4 / 3 := by
    rw [seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn (by decide) u
      (contDiff_fun_id.pow 2).contDiffOn hu, Opens.coe_mk,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hfun : (fun x : ℝ => ‖iteratedFDeriv ℝ 1 (fun y : ℝ => y ^ 2) x‖ ^ 2) =
        fun x : ℝ => 4 * x ^ 2 := by
      ext x
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, deriv_pow_field,
        Real.norm_eq_abs, sq_abs]
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  have h2sq : seminorm 2 2 le_rfl u ^ 2 = 4 := by
    rw [seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn le_rfl u
      (contDiff_fun_id.pow 2).contDiffOn hu, Opens.coe_mk,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    have hfun : (fun x : ℝ => ‖iteratedFDeriv ℝ 2 (fun y : ℝ => y ^ 2) x‖ ^ 2) =
        fun _ : ℝ => (4 : ℝ) := by
      ext x
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ', iteratedDeriv_one]
      have hd : deriv (fun y : ℝ => y ^ 2) = fun y : ℝ => 2 * y := by
        ext y
        rw [deriv_pow_field]
        ring
      rw [hd, deriv_const_mul_field, deriv_id'', mul_one, Real.norm_eq_abs]
      norm_num
    rw [hfun, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    norm_num
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [← Real.sqrt_sq zero_le_two]
    norm_num
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · rw [← Real.sqrt_sq (apply_nonneg _ u), h0sq, Real.sqrt_div zero_le_one, Real.sqrt_one]
  · rw [← Real.sqrt_sq (apply_nonneg _ u), h1sq, Real.sqrt_div (by positivity), hsqrt4]
  · rw [← Real.sqrt_sq (apply_nonneg _ u), h2sq, hsqrt4]

-- Check 3: Sharpness of sqrt_le_sqrt_two_mul_norm at p = ∞, k = 1:
-- on Ω = (0, 2π), u(x) = sin x has ‖u‖ = 1 while √(|u|_{0,∞}² + |u|_{1,∞}²) = √2 = √2 * ‖u‖.
example :
    ∃ u : Wkp volume ⟨Set.Ioo 0 (2 * Real.pi), isOpen_Ioo⟩ ∞ 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo 0 (2 * Real.pi))] Real.sin ∧
      ‖u‖ = 1 ∧
      √(∑ j : Fin 2, seminorm 1 j j.is_le u ^ 2) = √2 := by
  let Ω : Opens ℝ := ⟨Set.Ioo 0 (2 * Real.pi), isOpen_Ioo⟩
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume) (Omega := Ω)
    (p := ∞) 1 isOpen_univ Real.contDiff_sin.contDiffOn isCompact_Icc
    Set.Ioo_subset_Icc_self (Set.subset_univ _)
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = 1 := by
    apply le_antisymm
    · exact seminorm_top_le_of_contDiffOn (Nat.zero_le 1) u Real.contDiff_sin.contDiffOn hu
        zero_le_one fun x _ => by
          rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          exact Real.abs_sin_le_one x
    · have hle := norm_iteratedFDeriv_le_seminorm_top_of_contDiffOn (Nat.zero_le 1) u
        Real.contDiff_sin.contDiffOn hu (x₀ := Real.pi / 2)
        ⟨div_pos Real.pi_pos zero_lt_two, by linarith [Real.pi_pos]⟩
      simpa only [norm_iteratedFDeriv_zero, Real.sin_pi_div_two, norm_one] using hle
  have h1 : seminorm 1 1 le_rfl u = 1 := by
    apply le_antisymm
    · exact seminorm_top_le_of_contDiffOn le_rfl u Real.contDiff_sin.contDiffOn hu
        zero_le_one fun x _ => by
          rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, Real.deriv_sin,
            Real.norm_eq_abs]
          exact Real.abs_cos_le_one x
    · have hle := norm_iteratedFDeriv_le_seminorm_top_of_contDiffOn le_rfl u
        Real.contDiff_sin.contDiffOn hu (x₀ := Real.pi) ⟨Real.pi_pos, by linarith [Real.pi_pos]⟩
      simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one, Real.deriv_sin,
        Real.cos_pi, norm_neg, norm_one] using hle
  have hgrad : (W1p.gradient u : ℝ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝ)] Real.cos := by
    have hg := iteratedGradient_ae_eq_of_contDiffOn 0 u Real.contDiff_sin.contDiffOn hu
    rw [iteratedGradient_zero] at hg
    filter_upwards [hg] with x hx
    rw [hx, iteratedGradientChain_zero, gradient, (Real.hasDerivAt_sin x).hasFDerivAt.fderiv]
    exact (InnerProductSpace.toDual ℝ ℝ).injective (ContinuousLinearMap.ext fun y => by
      simp [InnerProductSpace.toDual_apply_apply])
  have hu_norm : ‖u‖ = 1 := by
    apply le_antisymm
    · have hu1 : ‖u.1‖ ≤ 1 := by
        refine Lp.norm_top_le_of_ae_bound zero_le_one ?_
        filter_upwards [W1p.norm_apply_sq_ae u, hu, hgrad] with x hsq hv hg
        have hv' : W1p.value u x = Real.sin x := by
          simpa only [value_one] using hv
        have h1sq : ‖u.1 x‖ ^ 2 = 1 := by
          rw [hsq, hv', hg, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
            Real.sin_sq_add_cos_sq]
        nlinarith [norm_nonneg (u.1 x)]
      exact hu1
    · exact h0.symm.le.trans (seminorm_le_norm (Nat.zero_le 1) u)
  refine ⟨u, hu, hu_norm, ?_⟩
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one]
  rw [h0, h1]
  norm_num

-- Check 4: Exponent lowering on Ω = (0, 2) from q = 2 to p = 1 for the constant function 1:
-- |1|_{0,2} = √2, |1|_{0,1} = 2, and (volume Ω)^(1/1 - 1/2) * √2 = √2 * √2 = 2.
example :
    have : IsFiniteMeasure
        (volume.restrict ((⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
      Real.isFiniteMeasure_restrict_Ioo 0 2
    ∃ u : Wkp volume ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ 2 1,
      (value 1 u : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 2)] (fun _ : ℝ => (1 : ℝ)) ∧
      seminorm 1 0 (Nat.zero_le 1) u = √2 ∧
      seminorm 1 0 (Nat.zero_le 1) (ofExponentLEL (p := 1) (q := 2) (by norm_num) 1 u) = 2 := by
  intro _
  have : IsFiniteMeasure (volume.restrict ((⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)) :=
    Real.isFiniteMeasure_restrict_Ioo 0 2
  obtain ⟨u, hu⟩ := exists_value_ae_eq_of_contDiffOn_of_isCompact (mu := volume)
    (Omega := ⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩) (p := 2) 1 isOpen_univ
    (contDiff_const (c := (1 : ℝ))).contDiffOn isCompact_Icc Set.Ioo_subset_Icc_self
    (Set.subset_univ _)
  have h0sq : seminorm 1 0 (Nat.zero_le 1) u ^ 2 = 2 := by
    rw [seminorm_sq_eq_integral_norm_iteratedFDeriv_sq_of_contDiffOn (Nat.zero_le 1) u
      (contDiff_const (c := (1 : ℝ))).contDiffOn hu, Opens.coe_mk,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_two]
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_one, one_pow,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  have h0 : seminorm 1 0 (Nat.zero_le 1) u = √2 := by
    rw [← Real.sqrt_sq (apply_nonneg _ u), h0sq]
  let v := ofExponentLEL (p := 1) (q := 2) (by norm_num) 1 u
  have hv : (value 1 v : ℝ → ℝ) =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 2)] (fun _ : ℝ => (1 : ℝ)) :=
    (value_ofExponentLEL_ae (p := 1) (q := 2) (by norm_num) 1 u).trans hu
  have hv0 : seminorm 1 0 (Nat.zero_le 1) v = 2 := by
    rw [seminorm_zero_apply, L1.norm_eq_integral_norm]
    have hcongr : (fun x => ‖value 1 v x‖) =ᵐ[volume.restrict
        ((⟨Set.Ioo (0 : ℝ) 2, isOpen_Ioo⟩ : Opens ℝ) : Set ℝ)] (fun _ : ℝ => (1 : ℝ)) :=
      hv.mono fun _ hx => by
        dsimp only at hx ⊢
        rw [hx, Real.norm_eq_abs, abs_one]
    rw [integral_congr_ae hcongr, Opens.coe_mk, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_two, intervalIntegral.integral_const]
    norm_num
  exact ⟨u, hu, h0, hv0⟩

end Examples

end TauCeti.Wkp
