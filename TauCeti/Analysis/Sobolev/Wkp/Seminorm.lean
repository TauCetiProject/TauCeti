/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Classical
public import TauCeti.Analysis.Sobolev.Wkp.Exponent

/-!
# Order truncation and seminorms on higher-order Sobolev spaces

Iterating the one-step projection `TauCeti.Wkp.lowerOrderL` produces continuous linear order
truncations `TauCeti.Wkp.toOrderL : W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for every `j ≤ k`. Composing
with `TauCeti.Wkp.iteratedGradient` accesses the weak derivative field of any intermediate order
`j + 1 ≤ k` directly as `iteratedGradient j (toOrderL h u)` without re-indexing the Sobolev tower.

Taking the `Lᵖ` norm of the value at `j = 0` and of the order-`j` weak derivative for `1 ≤ j ≤ k`
defines the bundled `ℝ`-seminorms `TauCeti.Wkp.seminorm k j hj`, written `|u|_{j,p}`. Because
`TauCeti.Wkp` uses the pointwise Euclidean `Lᵖ` norm at order one (`TauCeti.W1p`) and Euclidean
(`WithLp 2`) product norms at every higher stage, the `ℓ²` combination
`S(u) = √(∑_{j ≤ k} |u|_{j,p}²)` equals the graph norm `‖u‖` at exponent `p = 2` for every order
`k`, and satisfies `S(u) ≤ √2 · ‖u‖` and `‖u‖ ≤ √2 · S(u)` for every exponent `1 ≤ p ≤ ∞` and
every order `k`. Both `√2` bounds are sharp: on `(0, 2π)` at `p = ∞`, `sin` has graph norm `1` and
`S(sin) = √2`. Consequently the finite family `(|·|_{j,p})_{0 ≤ j ≤ k}` generates the norm topology
of `W^{k,p}(Ω)` (`TauCeti.Wkp.withSeminorms_seminorm`).

Order truncation commutes with subdomain restriction (`TauCeti.Wkp.restrictL`) and, on finite
measure domains, with exponent lowering (`TauCeti.Wkp.ofExponentLEL`), yielding the corresponding
monotonicity and Hölder bounds on every seminorm `|·|_{j,p}`.

## Main definitions

* `TauCeti.Wkp.toOrderL`: the continuous linear truncation `W^{k,p}(Ω) →L[ℝ] W^{j,p}(Ω)` for
  `j ≤ k`.
* `TauCeti.Wkp.seminorm`: the order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` (`j ≤ k`), as
  a bundled `Seminorm ℝ (Wkp mu Omega p k)`.

## Main results

* `TauCeti.Wkp.toOrderL_self`, `TauCeti.Wkp.toOrderL_comp_toOrderL`,
  `TauCeti.Wkp.value_toOrderL`, `TauCeti.Wkp.toOrderL_injective`: functoriality and injectivity of
  order truncation and preservation of the `Lᵖ` value.
* `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_chain`,
  `TauCeti.Wkp.iteratedGradient_toOrderL_ae_eq_of_contDiffOn`,
  `TauCeti.Wkp.seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn`: identification of intermediate
  weak derivatives and seminorms along weak-derivative chains and classical `C^j` representatives.
* `TauCeti.Wkp.norm_le_sum_seminorm`, `TauCeti.Wkp.norm_le_sqrt_two_mul`,
  `TauCeti.Wkp.sqrt_le_sqrt_two_mul_norm`, `TauCeti.Wkp.withSeminorms_seminorm`: norm comparisons
  and topological generation by the Sobolev seminorms for all `1 ≤ p ≤ ∞`.
* `TauCeti.Wkp.norm_sq_eq_sum_seminorm_sq`, `TauCeti.Wkp.norm_eq_sqrt_sum_seminorm_sq`: exact
  equality `‖u‖ = √(∑_{j ≤ k} |u|_{j,2}²)` at `p = 2`.
* `TauCeti.Wkp.restrictL_toOrderL`, `TauCeti.Wkp.seminorm_restrictL_le`,
  `TauCeti.Wkp.ofExponentLEL_toOrderL`, `TauCeti.Wkp.seminorm_ofExponentLEL_le`: compatibility of
  truncation and seminorms with subdomain restriction and exponent lowering.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element Methods*, 3rd ed.,
  Springer, 2008, §1.3 and Chapter 4.
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003, §§3.1–3.5.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, §5.2.1.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open MeasureTheory TopologicalSpace
open scoped ENNReal ContDiff

section Basic

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-! ### Order truncation -/

/-- Forget the weak derivatives above order `j`: the iterate of `TauCeti.Wkp.lowerOrderL`, equal to
the identity at `j = k`. -/
def toOrderL {j k : ℕ} (h : j ≤ k) : Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j :=
  Nat.leRec (motive := fun k _ => Wkp mu Omega p k →L[ℝ] Wkp mu Omega p j)
    (ContinuousLinearMap.id ℝ _) (fun k _ ih => ih.comp (lowerOrderL k)) h

/-- Truncating from order `k` to itself is the identity continuous linear map. -/
@[simp]
theorem toOrderL_self {k : ℕ} (h : k ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h =
      ContinuousLinearMap.id ℝ (Wkp mu Omega p k) := by
  cases Subsingleton.elim h (Nat.le_refl k)
  exact Nat.leRec_self _ _

/-- Truncating from `k + 1` to `j` factors through `TauCeti.Wkp.lowerOrderL k` followed by
truncating from `k` to `j`. -/
theorem toOrderL_succ_right {j k : ℕ} (h : j ≤ k) (h' : j ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h' = (toOrderL h).comp (lowerOrderL k) := by
  cases Subsingleton.elim h' (Nat.le_succ_of_le h)
  exact Nat.leRec_succ _ _ h

/-- Precomposing truncation with `TauCeti.Wkp.lowerOrderL` shifts the source order up by one. -/
theorem toOrderL_comp_lowerOrderL {j k : ℕ} (h : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) h).comp (lowerOrderL k) =
      toOrderL (Nat.le_succ_of_le h) :=
  (toOrderL_succ_right h (Nat.le_succ_of_le h)).symm

/-- Applying order truncation after `TauCeti.Wkp.lowerOrder` agrees with truncating directly from
`k + 1`. -/
@[simp]
theorem toOrderL_lowerOrder {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    toOrderL h (lowerOrder k u) = toOrderL (Nat.le_succ_of_le h) u := by
  rw [← lowerOrderL_apply, ← ContinuousLinearMap.comp_apply, toOrderL_comp_lowerOrderL]

/-- Order truncation preserves the `Lᵖ` value component. -/
@[simp]
theorem value_toOrderL {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    value j (toOrderL h u) = value k u := by
  induction h using Nat.leRec with
  | refl => simp
  | le_succ_of_le h ih =>
      rw [toOrderL_succ_right h, ContinuousLinearMap.comp_apply, lowerOrderL_apply, ih, value_succ]

/-- Composing `TauCeti.Wkp.valueL` with order truncation gives `TauCeti.Wkp.valueL` at the higher
order. -/
@[simp]
theorem valueL_comp_toOrderL {j k : ℕ} (h : j ≤ k) :
    (valueL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h) = valueL k := by
  ext u
  simp

/-- The order-`j` truncation of `u` equals `v` if and only if `u` and `v` have the same `Lᵖ` value
component. -/
theorem toOrderL_eq_iff {j k : ℕ} (h : j ≤ k) {u : Wkp mu Omega p k} {v : Wkp mu Omega p j} :
    toOrderL h u = v ↔ value k u = value j v :=
  ⟨fun huv => huv ▸ (value_toOrderL h u).symm,
    fun hv => ext j ((value_toOrderL h u).trans hv)⟩

/-- Order truncation is injective, since a higher-order Sobolev function is uniquely determined by
its `Lᵖ` value. -/
theorem toOrderL_injective {j k : ℕ} (h : j ≤ k) :
    Function.Injective (toOrderL (mu := mu) (Omega := Omega) (p := p) h) := fun u v huv =>
  ext k (by rw [← value_toOrderL h u, huv, value_toOrderL])

/-- Order truncations compose transitively as continuous linear maps. -/
@[simp]
theorem toOrderL_comp_toOrderL {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) :
    (toOrderL (mu := mu) (Omega := Omega) (p := p) h₁).comp (toOrderL h₂) =
      toOrderL (h₁.trans h₂) :=
  ContinuousLinearMap.ext fun u => ext i (by simp)

/-- Applying two successive order truncations agrees with truncating along their composite
inequality. -/
@[simp]
theorem toOrderL_toOrderL {i j k : ℕ} (h₁ : i ≤ j) (h₂ : j ≤ k) (u : Wkp mu Omega p k) :
    toOrderL h₁ (toOrderL h₂ u) = toOrderL (h₁.trans h₂) u :=
  ext i (by simp)

/-- Truncating by one order is `TauCeti.Wkp.lowerOrderL`. -/
theorem toOrderL_succ_self {k : ℕ} (h : k ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = lowerOrderL k := by
  rw [toOrderL_succ_right le_rfl h, toOrderL_self, ContinuousLinearMap.id_comp]

/-- Postcomposing order truncation to `j + 1` with `TauCeti.Wkp.lowerOrderL j` truncates to `j`.
Use `rw` with this lemma when `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrderL_comp_toOrderL {j k : ℕ} (h : j + 1 ≤ k) :
    (lowerOrderL j).comp (toOrderL (mu := mu) (Omega := Omega) (p := p) h) =
      toOrderL (Nat.le_of_succ_le h) := by
  rw [← toOrderL_succ_self (Nat.le_succ j), toOrderL_comp_toOrderL]

/-- Forgetting one more derivative after truncating to `j + 1` agrees with truncating to `j`.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem lowerOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    lowerOrder j (toOrderL h u) = toOrderL (Nat.le_of_succ_le h) u :=
  ext j (by rw [← value_succ, value_toOrderL, value_toOrderL])

/-- Truncating to order zero is the value projection `TauCeti.Wkp.valueL`. -/
theorem toOrderL_zero {k : ℕ} (h : 0 ≤ k) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = valueL k :=
  ContinuousLinearMap.ext fun u =>
    (value_zero (toOrderL h u)).symm.trans ((value_toOrderL h u).trans (valueL_apply k u).symm)

/-- Truncating a positive-order Sobolev space to order one is `TauCeti.Wkp.firstOrderL`. -/
theorem toOrderL_one {k : ℕ} (h : 1 ≤ k + 1) :
    toOrderL (mu := mu) (Omega := Omega) (p := p) h = firstOrderL k :=
  ContinuousLinearMap.ext fun u => W1p.ext_value (u := toOrderL h u) (v := firstOrderL k u) (by
    rw [← value_one (toOrderL h u), value_toOrderL, firstOrderL_apply, value_firstOrder])

/-- Taking the first-order part after truncating to a positive order gives the original first-order
part. -/
theorem firstOrder_toOrderL {j k : ℕ} (h : j + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    firstOrder j (toOrderL h u) = firstOrder k u :=
  W1p.ext_value (by rw [value_firstOrder, value_toOrderL, value_firstOrder])

/-- Truncating `mk k u D h` to any order `j ≤ k + 1` truncates `u` to order `j`. -/
@[simp]
theorem toOrderL_mk {j k : ℕ} (hj : j ≤ k + 1) (u : Wkp mu Omega p (k + 1))
    (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    toOrderL (Nat.le_succ_of_le hj) (mk k u D h) = toOrderL hj u := by
  rw [← toOrderL_lowerOrder, lowerOrder_mk]

/-- Order truncation does not increase the Sobolev graph norm. -/
theorem norm_toOrderL_apply_le {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    ‖toOrderL h u‖ ≤ ‖u‖ := by
  induction h using Nat.leRec with
  | refl => simp
  | le_succ_of_le h ih =>
      rw [toOrderL_succ_right h, ContinuousLinearMap.comp_apply, lowerOrderL_apply]
      exact (ih (lowerOrder _ u)).trans (norm_lowerOrder_le _ u)

/-- The operator norm of `TauCeti.Wkp.toOrderL` is at most one. -/
theorem opNorm_toOrderL_le {j k : ℕ} (h : j ≤ k) :
    ‖toOrderL (mu := mu) (Omega := Omega) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    simpa only [one_mul] using norm_toOrderL_apply_le h u

/-! ### Intermediate weak derivatives -/

/-- For `1 ≤ k`, the order-one weak derivative `iteratedGradient 0 (toOrderL h u)` is the weak
gradient of `value k u` on `Ω`. -/
theorem hasWeakFDerivOn_value_toOrderL {k : ℕ} (h : 1 ≤ k) (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (value k u)
      (fun x => innerSL ℝ (iteratedGradient 0 (toOrderL h u) x)) := by
  rw [← value_toOrderL h u]
  exact hasWeakFDerivOn_value (toOrderL h u)

/-- Adjacent intermediate weak derivatives satisfy the weak Fréchet derivative identity: for
`j + 2 ≤ k`, `iteratedGradient (j + 1) (toOrderL h u)` is the weak Fréchet derivative on `Ω` of
`iteratedGradient j (toOrderL (Nat.le_of_succ_le h) u)`. -/
theorem hasWeakFDerivOn_iteratedGradient_toOrderL {j k : ℕ} (h : j + 2 ≤ k)
    (u : Wkp mu Omega p k) :
    HasWeakFDerivOn mu Omega (iteratedGradient j (toOrderL (Nat.le_of_succ_le h) u))
      (iteratedGradient (j + 1) (toOrderL h u)) := by
  rw [← lowerOrder_toOrderL h u]
  exact hasWeakFDerivOn_iteratedGradient j (toOrderL h u)

/-- Uniqueness of intermediate weak derivatives along a weak-derivative chain: if `value k u =ᵐ f`
on `Ω`, `f` has weak derivative `innerSL ℝ ∘ G 0`, and each `G i` (`i < j`) has weak Fréchet
derivative `G (i + 1)` on `Ω`, then `iteratedGradient j (toOrderL h u) =ᵐ G j` for `j + 1 ≤ k`. -/
theorem iteratedGradient_toOrderL_ae_eq_of_chain {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} {G : (i : ℕ) → E → IteratedGradient E i}
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f)
    (h₀ : HasWeakFDerivOn mu Omega f (fun x => innerSL ℝ (G 0 x)))
    (hG : ∀ i < j, HasWeakFDerivOn mu Omega (G i) (G (i + 1))) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega] G j := by
  induction j with
  | zero =>
      have hd := ((hasWeakFDerivOn_value_toOrderL h u).congr_ae hu).ae_eq h₀
      filter_upwards [hd] with x hx
      exact (InnerProductSpace.toDual ℝ E).injective (by
        ext y
        simpa only [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using
          congrArg (fun l : E →L[ℝ] ℝ => l y) hx)
  | succ j ih =>
      have hj' := ih (Nat.le_of_succ_le h) fun i hi => hG i (Nat.lt_succ_of_lt hi)
      exact ((hasWeakFDerivOn_iteratedGradient_toOrderL h u).congr_ae hj').ae_eq
        (hG j (Nat.lt_succ_self j))

/-- If `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a `C^{j+1}` function `f` with
`j + 1 ≤ k`, then its order-`(j + 1)` weak derivative `iteratedGradient j (toOrderL h u)` agrees
almost everywhere on `Ω` with the classical iterated-gradient field `iteratedGradientChain f j`. -/
theorem iteratedGradient_toOrderL_ae_eq_of_contDiffOn {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ (j + 1) f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    (iteratedGradient j (toOrderL h u) : E → IteratedGradient E j) =ᵐ[mu.restrict Omega]
      iteratedGradientChain f j :=
  iteratedGradient_ae_eq_of_contDiffOn j (toOrderL h u) hf (by rwa [value_toOrderL])

/-- If `u ∈ W^{k,p}(Ω)` vanishes almost everywhere on an open subset `V ≤ Ω`, then every
intermediate weak derivative `iteratedGradient j (toOrderL h u)` (`j + 1 ≤ k`) vanishes almost
everywhere on `V`. -/
theorem iteratedGradient_toOrderL_ae_eq_zero_of_value_ae_eq_zero {j k : ℕ} (h : j + 1 ≤ k)
    (u : Wkp mu Omega p k) {V : Opens E} (hV : V ≤ Omega)
    (hu : ∀ᵐ x ∂mu.restrict (V : Set E), value k u x = 0) :
    ∀ᵐ x ∂mu.restrict (V : Set E), iteratedGradient j (toOrderL h u) x = 0 :=
  iteratedGradient_ae_eq_zero_of_value_ae_eq_zero j (toOrderL h u) hV (by rwa [value_toOrderL])

/-! ### Sobolev seminorms and norm comparisons -/

/-- The order-`j` Sobolev seminorm `|·|_{j,p}` on `W^{k,p}(Ω)` for `j ≤ k`, bundled as a
`Seminorm ℝ (Wkp mu Omega p k)`: `‖value k u‖` at `j = 0`, and
`‖iteratedGradient (j - 1) (toOrderL hj u)‖` for `1 ≤ j ≤ k`. -/
def seminorm (k : ℕ) : (j : ℕ) → j ≤ k → Seminorm ℝ (Wkp mu Omega p k)
  | 0, _ =>
      (normSeminorm ℝ (Lp ℝ p (mu.restrict Omega))).comp
        (valueL (mu := mu) (Omega := Omega) (p := p) k).toLinearMap
  | j + 1, hj =>
      (normSeminorm ℝ (Lp (IteratedGradient E j) p (mu.restrict Omega))).comp
        ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
          (toOrderL hj)).toLinearMap

/-- At order zero, `seminorm k 0` is the `Lᵖ` norm of the value component. -/
@[simp]
theorem seminorm_zero (k : ℕ) (hj : 0 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k 0 hj u = ‖value k u‖ := by
  simp only [seminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    valueL_apply]

/-- At order zero, the unique Sobolev seminorm on `W^{0,p}(Ω)` is the `Lᵖ` norm itself.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem seminorm_zero_zero (hj : 0 ≤ 0) (u : Wkp mu Omega p 0) :
    seminorm 0 0 hj u = ‖u‖ := by
  rw [seminorm_zero, value_zero]

/-- At positive order `j + 1 ≤ k`, `seminorm k (j + 1)` is the `Lᵖ` norm of the order-`(j + 1)`
weak derivative `iteratedGradient j (toOrderL hj u)`. -/
@[simp]
theorem seminorm_succ (k j : ℕ) (hj : j + 1 ≤ k) (u : Wkp mu Omega p k) :
    seminorm k (j + 1) hj u = ‖iteratedGradient j (toOrderL hj u)‖ := by
  simp only [seminorm, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply]
  rw [iteratedGradientL_apply]

/-- The top-order Sobolev seminorm `|u|_{k+1,p}` on `W^{k+1,p}(Ω)` is the `Lᵖ` norm of
`iteratedGradient k u`.
Use `rw` with this lemma: `simp` does not match its dependently indexed left-hand side. -/
theorem seminorm_succ_self (k : ℕ) (hj : k + 1 ≤ k + 1) (u : Wkp mu Omega p (k + 1)) :
    seminorm (k + 1) (k + 1) hj u = ‖iteratedGradient k u‖ := by
  rw [seminorm_succ, toOrderL_self, ContinuousLinearMap.id_apply]

/-- Pulling back `seminorm k j hj` along `TauCeti.Wkp.toOrderL h` gives `seminorm l j (hj.trans h)`.
-/
@[simp]
theorem seminorm_comp_toOrderL {j k l : ℕ} (hj : j ≤ k) (h : k ≤ l) :
    (seminorm (mu := mu) (Omega := Omega) (p := p) k j hj).comp (toOrderL h).toLinearMap =
      seminorm l j (hj.trans h) := by
  ext u
  cases j with
  | zero => simp
  | succ j =>
      simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, seminorm_succ]
      rw [toOrderL_toOrderL]

/-- Evaluating `seminorm k j hj` on a truncated function `toOrderL h u` agrees with evaluating
`seminorm l j` on `u`. -/
@[simp]
theorem seminorm_toOrderL {j k l : ℕ} (hj : j ≤ k) (h : k ≤ l) (u : Wkp mu Omega p l) :
    seminorm k j hj (toOrderL h u) = seminorm l j (hj.trans h) u :=
  DFunLike.congr_fun (seminorm_comp_toOrderL hj h) u

/-- Evaluating `seminorm k j hj` on `lowerOrder k u` agrees with `seminorm (k + 1) j` on `u`. -/
@[simp]
theorem seminorm_lowerOrder {j k : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p (k + 1)) :
    seminorm k j hj (lowerOrder k u) = seminorm (k + 1) j (Nat.le_succ_of_le hj) u := by
  rw [← lowerOrderL_apply, ← toOrderL_succ_self (Nat.le_succ k), seminorm_toOrderL]

/-- On `mk k u D h`, every Sobolev seminorm below the top order agrees with that of `u`. -/
theorem seminorm_mk_of_le {j k : ℕ} (hj : j ≤ k + 1) (hj' : j ≤ k + 2)
    (u : Wkp mu Omega p (k + 1)) (D : Lp (IteratedGradient E (k + 1)) p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega (iteratedGradient k u) D) :
    seminorm (k + 2) j hj' (mk k u D h) = seminorm (k + 1) j hj u := by
  rw [← seminorm_lowerOrder hj (mk k u D h), lowerOrder_mk]

/-- Every Sobolev seminorm `|u|_{j,p}` (`j ≤ k`) is bounded by the Sobolev graph norm `‖u‖`. -/
theorem seminorm_le_norm {j k : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j hj u ≤ ‖u‖ := by
  cases j with
  | zero =>
      rw [seminorm_zero]
      exact norm_value_le k u
  | succ j =>
      rw [seminorm_succ]
      exact (norm_iteratedGradient_le j (toOrderL hj u)).trans (norm_toOrderL_apply_le hj u)

/-- Every Sobolev seminorm `|·|_{j,p}` is continuous on `W^{k,p}(Ω)`. -/
theorem continuous_seminorm (k j : ℕ) (hj : j ≤ k) :
    Continuous (seminorm (mu := mu) (Omega := Omega) (p := p) k j hj) := by
  cases j with
  | zero =>
      exact (valueL (mu := mu) (Omega := Omega) (p := p) k).continuous.norm.congr fun u => by
        rw [valueL_apply, ← seminorm_zero]
  | succ j =>
      exact ((iteratedGradientL (mu := mu) (Omega := Omega) (p := p) j).comp
        (toOrderL hj)).continuous.norm.congr fun u => by
        rw [ContinuousLinearMap.comp_apply, iteratedGradientL_apply, ← seminorm_succ]

/-- A Sobolev function vanishes if and only if all of its seminorms vanish. -/
theorem eq_zero_iff_forall_seminorm_eq_zero {k : ℕ} (u : Wkp mu Omega p k) :
    u = 0 ↔ ∀ (j : ℕ) (hj : j ≤ k), seminorm k j hj u = 0 :=
  ⟨fun hu j hj => by rw [hu, map_zero], fun h => ext k <| by
    rw [← valueL_apply k 0, map_zero]
    exact norm_eq_zero.mp (by rw [← seminorm_zero k (Nat.zero_le k) u]; exact h 0 (Nat.zero_le k))⟩

/-- If `u ∈ W^{k,p}(Ω)` is represented almost everywhere on `Ω` by a `C^j` function `f` (`j ≤ k`),
then `seminorm k j hj u` equals the classical `Lᵖ` derivative seminorm
`lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega)`. -/
theorem seminorm_eq_lpNorm_iteratedFDeriv_of_contDiffOn {j k : ℕ} (hj : j ≤ k)
    (u : Wkp mu Omega p k) {f : E → ℝ} (hf : ContDiffOn ℝ j f Omega)
    (hu : (value k u : E → ℝ) =ᵐ[mu.restrict Omega] f) :
    seminorm k j hj u = lpNorm (iteratedFDeriv ℝ j f) p (mu.restrict Omega) := by
  cases j with
  | zero =>
      rw [seminorm_zero, Lp.norm_def, lpNorm]
      congr 1
      refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _)
        ((ContinuousOn.continuousOn_iteratedFDeriv hf Omega.isOpen le_rfl).aestronglyMeasurable
          Omega.isOpen.measurableSet) ?_
      filter_upwards [hu] with x hx
      rw [hx, norm_iteratedFDeriv_zero]
  | succ j =>
      rw [seminorm_succ]
      exact norm_iteratedGradient_eq_lpNorm_of_contDiffOn j (toOrderL hj u) hf
        (by rwa [value_toOrderL])

/-- The Sobolev graph norm is bounded by the `ℓ¹` sum of the Sobolev seminorms `∑_{j ≤ k} |u|_{j,p}`
with constant one, for every order `k` and exponent `1 ≤ p ≤ ∞`. -/
theorem norm_le_sum_seminorm :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ≤ ∑ j : Fin (k + 1), seminorm k j j.is_le u
  | 0, u => by
      rw [Fin.sum_univ_one]
      simp only [Fin.val_zero]
      rw [seminorm_zero_zero]
  | k + 1, u => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last]
      rw [seminorm_succ_self]
      have hsum : (∑ i : Fin (k + 1), seminorm (k + 1) i.castSucc i.castSucc.is_le u) =
          ∑ i : Fin (k + 1), seminorm k i i.is_le (lowerOrder k u) :=
        Finset.sum_congr rfl fun i _ => (seminorm_lowerOrder i.is_le u).symm
      linarith [norm_le_norm_lowerOrder_add_norm_iteratedGradient k u,
        norm_le_sum_seminorm (lowerOrder k u)]

/-- The finite family of Sobolev seminorms `(|·|_{j,p})_{0 ≤ j ≤ k}` generates the norm topology of
`W^{k,p}(Ω)`. -/
theorem withSeminorms_seminorm (k : ℕ) :
    WithSeminorms (fun j : Fin (k + 1) =>
      seminorm (mu := mu) (Omega := Omega) (p := p) k j j.is_le) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
  refine le_antisymm ?_ ?_
  · refine le_iInf fun j => Filter.tendsto_iff_comap.mp ?_
    exact (continuous_seminorm k j j.is_le).tendsto' 0 0 (map_zero _)
  · rw [← Filter.tendsto_id']
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have hsum : Filter.Tendsto (fun u : Wkp mu Omega p k =>
        ∑ j : Fin (k + 1), seminorm k j j.is_le u)
        (⨅ j : Fin (k + 1), (nhds 0).comap (seminorm k j j.is_le)) (nhds 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum (M := ℝ) (a := fun _ => (0 : ℝ))
          (Finset.univ : Finset (Fin (k + 1))) fun j _ =>
            Filter.tendsto_iff_comap.mpr (iInf_le _ j)
    exact squeeze_zero (fun u => norm_nonneg u) (fun u => norm_le_sum_seminorm u) hsum

/-- At order zero, the sum of squared seminorms is `‖u‖ ^ 2`. -/
theorem sum_seminorm_sq_zero (u : Wkp mu Omega p 0) :
    (∑ j : Fin 1, seminorm 0 j j.is_le u ^ 2) = ‖u‖ ^ 2 := by
  simp only [Fin.sum_univ_one, Fin.val_zero]
  rw [seminorm_zero_zero]

/-- At order `k + 1`, the sum of squared seminorms splits into the sum for `lowerOrder k u` plus
the squared norm of the highest weak derivative `iteratedGradient k u`. -/
theorem sum_seminorm_sq_succ (k : ℕ) (u : Wkp mu Omega p (k + 1)) :
    (∑ j : Fin (k + 2), seminorm (k + 1) j j.is_le u ^ 2) =
      (∑ j : Fin (k + 1), seminorm k j j.is_le (lowerOrder k u) ^ 2) +
        ‖iteratedGradient k u‖ ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => congrArg (· ^ 2) (seminorm_lowerOrder j.is_le u).symm
  · simp only [Fin.val_last]
    rw [seminorm_succ_self]

/-- For every order `k` and exponent `1 ≤ p ≤ ∞`, the squared graph norm is at most twice the sum
of squared Sobolev seminorms. -/
theorem norm_sq_le_two_mul_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      ‖u‖ ^ 2 ≤ 2 * ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      nlinarith [norm_le_norm_lowerOrder_add_norm_iteratedGradient 0 u, norm_nonneg u,
        sq_nonneg (‖lowerOrder 0 u‖ - ‖iteratedGradient 0 u‖)]
  | k + 2, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u,
        sum_seminorm_sq_succ (k + 1) u]
      linarith [norm_sq_le_two_mul_sum_seminorm_sq (lowerOrder (k + 1) u),
        sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- For every order `k` and exponent `1 ≤ p ≤ ∞`, the sum of squared Sobolev seminorms is at most
twice the squared graph norm. -/
theorem sum_seminorm_sq_le_two_mul_norm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega p k),
      (∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ 2 * ‖u‖ ^ 2
  | 0, u => by
      rw [sum_seminorm_sq_zero]
      nlinarith [sq_nonneg ‖u‖]
  | 1, u => by
      rw [sum_seminorm_sq_succ 0 u, sum_seminorm_sq_zero]
      have h₀ : ‖lowerOrder 0 u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_lowerOrder_le 0 u) 2
      have h₁ : ‖iteratedGradient 0 u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_iteratedGradient_le 0 u) 2
      linarith
  | k + 2, u => by
      rw [sum_seminorm_sq_succ (k + 1) u,
        norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq_succ k u]
      linarith [sum_seminorm_sq_le_two_mul_norm_sq (lowerOrder (k + 1) u),
        sq_nonneg ‖iteratedGradient (k + 1) u‖]

/-- **Upper comparison of the Sobolev norm with the seminorms:**
`‖u‖ ≤ √2 · √(∑_{j ≤ k} |u|_{j,p}²)` for every order `k` and every exponent `1 ≤ p ≤ ∞`. -/
theorem norm_le_sqrt_two_mul {k : ℕ} (u : Wkp mu Omega p k) :
    ‖u‖ ≤ √2 * √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (norm_sq_le_two_mul_sum_seminorm_sq u)

/-- **Lower comparison of the Sobolev norm with the seminorms:**
`√(∑_{j ≤ k} |u|_{j,p}²) ≤ √2 · ‖u‖` for every order `k` and every exponent `1 ≤ p ≤ ∞`. -/
theorem sqrt_le_sqrt_two_mul_norm {k : ℕ} (u : Wkp mu Omega p k) :
    √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) ≤ √2 * ‖u‖ := by
  rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul zero_le_two]
  exact Real.sqrt_le_sqrt (sum_seminorm_sq_le_two_mul_norm_sq u)

end Basic

/-! ### Exact norm identity at `p = 2` -/

section L2

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

/-- At exponent `p = 2`, the squared graph norm equals the sum of squared Sobolev seminorms at
every order `k`. -/
theorem norm_sq_eq_sum_seminorm_sq :
    ∀ {k : ℕ} (u : Wkp mu Omega 2 k),
      ‖u‖ ^ 2 = ∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2
  | 0, u => (sum_seminorm_sq_zero u).symm
  | k + 1, u => by
      rw [norm_sq_eq_norm_lowerOrder_sq_add_norm_iteratedGradient_sq k u,
        sum_seminorm_sq_succ k u, norm_sq_eq_sum_seminorm_sq (lowerOrder k u)]

/-- At exponent `p = 2`, the Sobolev graph norm equals `√(∑_{j ≤ k} |u|_{j,2}²)` at every order
`k`. -/
theorem norm_eq_sqrt_sum_seminorm_sq {k : ℕ} (u : Wkp mu Omega 2 k) :
    ‖u‖ = √(∑ j : Fin (k + 1), seminorm k j j.is_le u ^ 2) := by
  rw [← norm_sq_eq_sum_seminorm_sq u, Real.sqrt_sq (norm_nonneg u)]

end L2

/-! ### Compatibility with subdomain restriction and exponent lowering -/

section Restriction

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega U : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Subdomain restriction commutes with order truncation as continuous linear maps. -/
theorem restrictL_comp_toOrderL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) :
    (restrictL (mu := mu) (p := p) hU j).comp (toOrderL h) =
      (toOrderL h).comp (restrictL hU k) :=
  ContinuousLinearMap.ext fun u => ext j (by simp)

/-- Restricting to an open subdomain commutes with order truncation. -/
theorem restrictL_toOrderL (hU : U ≤ Omega) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega p k) :
    restrictL hU j (toOrderL h u) = toOrderL h (restrictL hU k u) :=
  ext j (by simp)

/-- Restricting to an open subdomain does not increase any Sobolev seminorm. -/
theorem seminorm_restrictL_le (hU : U ≤ Omega) {j k : ℕ} (hj : j ≤ k) (u : Wkp mu Omega p k) :
    seminorm k j hj (restrictL hU k u) ≤ seminorm k j hj u := by
  have hmono : mu.restrict (U : Set E) ≤ mu.restrict (Omega : Set E) :=
    Measure.restrict_mono (SetLike.coe_subset_coe.mpr hU) le_rfl
  cases j with
  | zero =>
      simp only [seminorm_zero, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_lt_top _).ne ?_
      rw [eLpNorm_congr_ae (value_restrictL_ae hU k u)]
      exact eLpNorm_mono_measure _ hmono
  | succ j =>
      rw [seminorm_succ, seminorm_succ, ← restrictL_toOrderL, Lp.norm_def, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_lt_top _).ne ?_
      rw [eLpNorm_congr_ae (iteratedGradient_restrictL_ae hU j (toOrderL hj u))]
      exact eLpNorm_mono_measure _ hmono

end Restriction

section Exponent

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [IsFiniteMeasure (mu.restrict (Omega : Set E))]

/-- Lowering the integrability exponent commutes with order truncation as continuous linear maps. -/
theorem ofExponentLEL_comp_toOrderL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) :
    (ofExponentLEL (mu := mu) (Omega := Omega) hpq j).comp (toOrderL h) =
      (toOrderL h).comp (ofExponentLEL hpq k) :=
  ContinuousLinearMap.ext fun u => ext j (by simp)

/-- Lowering the integrability exponent commutes with order truncation. -/
theorem ofExponentLEL_toOrderL (hpq : p ≤ q) {j k : ℕ} (h : j ≤ k) (u : Wkp mu Omega q k) :
    ofExponentLEL hpq j (toOrderL h u) = toOrderL h (ofExponentLEL hpq k u) :=
  ext j (by simp)

/-- Lowering the exponent from `q` to `p` (`1 ≤ p ≤ q`) multiplies each Sobolev seminorm
`|u|_{j,q}` (`j ≤ k`) by at most `μ(Ω) ^ (1/p - 1/q)`. -/
theorem seminorm_ofExponentLEL_le (hpq : p ≤ q) {j k : ℕ} (hj : j ≤ k) (u : Wkp mu Omega q k) :
    seminorm k j hj (ofExponentLEL hpq k u) ≤
      (mu Omega ^ (1 / p.toReal - 1 / q.toReal)).toReal * seminorm k j hj u := by
  cases j with
  | zero =>
      rw [seminorm_zero, seminorm_zero, value_ofExponentLEL, ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq (value k u)
  | succ j =>
      rw [seminorm_succ, seminorm_succ, ← ofExponentLEL_toOrderL, iteratedGradient_ofExponentLEL,
        ← Measure.restrict_apply_univ]
      exact Lp.norm_ofExponentLEL_apply_le hpq (iteratedGradient j (toOrderL hj u))

end Exponent

end TauCeti.Wkp
