/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Topology.MetricSpace.Bounded

/-!
# Symbol classes at infinity

A map `f` from a real normed space `E` is a **symbol of order `ℓ` and regularity `k` at
infinity** (`TauCeti.IsSymbolAtInfinity k ℓ f`) when it is `Cᵏ` outside a bounded set and, for
every `j ≤ k`, its `j`-th derivative is `O(‖x‖ ^ (ℓ - j))` as `x → ∞`: a symbol of order `ℓ` and
regularity `k` along the cobounded filter in the sense of `TauCeti.IsSymbolAlong`. For
`ℓ = -t < 0` this is the class `O_k(‖x‖ ^ (-t))` of asymptotically Euclidean geometry: the
coefficients `g_ij - δ_ij` of an asymptotically Euclidean end of order `t` are
`O₂(‖x‖ ^ (-t))`, and so are the coefficients of the inverse metric and the volume density,
which differ from their Euclidean values by smooth functions of `g_ij - δ_ij`.

These classes form a graded calculus, the bookkeeping by which decay rates are propagated
through algebraic and analytic operations on the metric coefficients. Sums, linear images,
constants, products (which add orders), lower regularity and differentiation (which lowers the
order and the regularity by one) are the filter-independent rules of `TauCeti.IsSymbolAlong`
(`IsSymbolAlong.add`, `IsSymbolAlong.sum`, `IsSymbolAlong.continuousLinearMap_comp`,
`TauCeti.isSymbolAlong_const`, `IsSymbolAlong.bilinear`, `IsSymbolAlong.of_le`,
`TauCeti.isSymbolAlong_add_one_iff`, …). This file adds the rules particular to infinity:

* passage to larger orders (`IsSymbolAtInfinity.mono`), limits of maps of negative order
  (`IsSymbolAtInfinity.tendsto_zero`, `IsSymbolAtInfinity.tendsto_of_sub`), and differentiation
  with the regularity counted in `ℕ` (`IsSymbolAtInfinity.fderiv`);
* **composition with a map smooth at the limit**: if `f - c` has negative order `ℓ` and `G` is
  `Cᵏ` at `c`, then `G ∘ f` has order `0` (`IsSymbolAtInfinity.comp_of_contDiffAt`), and if `G`
  is moreover `C^(max k 1)` at `c`, then `G ∘ f - G c` has order `ℓ`
  (`IsSymbolAtInfinity.comp_sub`);
* **inversion**: in a complete normed algebra, if `a - 1` has negative order `ℓ`, then so does
  `Ring.inverse a - 1` (`IsSymbolAtInfinity.ringInverse_sub_one`).

The bounds are only asked for along the cobounded filter: they concern large `‖x‖` and say nothing
about a bounded region. The order `ℓ` is any real number, and the regularity `k` is finite, as
for the `C²` coefficients of an asymptotically Euclidean end; the punctured analogue at a point,
with all derivatives, is `TauCeti.IsPuncturedSymbol`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §8 and §9
  (the classes `O_k(r ^ (-t))` of asymptotically flat metrics).
* R. Bartnik, *The mass of an asymptotically flat manifold*, Comm. Pure Appl. Math. 39 (1986),
  §1 (weighted `Cᵏ` spaces).
-/

public section

open Set Filter Asymptotics Bornology
open scoped Topology ContDiff

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- A map `f` is a **symbol of order `ℓ` and regularity `k` at infinity** if it is `Cᵏ` near
infinity and, for every `j ≤ k`, its `j`-th derivative is `O(‖x‖ ^ (ℓ - j))` as `x → ∞`: a symbol
of order `ℓ` and regularity `k` along the cobounded filter. For `ℓ = -t` this is the class
`O_k(‖x‖ ^ (-t))` of maps decaying at rate `t` together with their derivatives up to order `k`,
each derivative gaining a further factor `‖x‖⁻¹`. -/
abbrev IsSymbolAtInfinity (k : ℕ) (ℓ : ℝ) (f : E → F) : Prop :=
  IsSymbolAlong (cobounded E) k ℓ f

/-- The defining properties of a symbol at infinity: `Cᵏ` regularity near infinity and the
bounds `D^j f = O(‖x‖ ^ (ℓ - j))` for `j ≤ k`. -/
theorem isSymbolAtInfinity_iff {k : ℕ} {ℓ : ℝ} {f : E → F} :
    IsSymbolAtInfinity k ℓ f ↔ (∀ᶠ x in cobounded E, ContDiffAt ℝ k f x) ∧
      ∀ j ≤ k, iteratedFDeriv ℝ j f =O[cobounded E] fun x ↦ ‖x‖ ^ (ℓ - j) :=
  isSymbolAlong_iff.trans (and_congr (by norm_cast) (forall_congr' fun _ ↦ by norm_cast))

/-! ### Basic properties -/

namespace IsSymbolAtInfinity

variable {k : ℕ} {ℓ m : ℝ} {f f₁ : E → F}

/-- A symbol of regularity `k` at infinity is `Cᵏ` near infinity. -/
theorem eventually_contDiffAt (hf : IsSymbolAtInfinity k ℓ f) :
    ∀ᶠ x in cobounded E, ContDiffAt ℝ k f x :=
  (isSymbolAtInfinity_iff.1 hf).1

/-- The `j`-th derivative of a symbol of order `ℓ` at infinity is `O(‖x‖ ^ (ℓ - j))`, for `j` at
most the regularity. -/
theorem isBigO_iteratedFDeriv (hf : IsSymbolAtInfinity k ℓ f) {j : ℕ} (hj : j ≤ k) :
    iteratedFDeriv ℝ j f =O[cobounded E] fun x ↦ ‖x‖ ^ (ℓ - j) :=
  (isSymbolAtInfinity_iff.1 hf).2 j hj

/-- A symbol of negative order tends to `0` at infinity. -/
theorem tendsto_zero (hf : IsSymbolAtInfinity k ℓ f) (hℓ : ℓ < 0) :
    Tendsto f (cobounded E) (𝓝 0) := by
  refine hf.isBigO.trans_tendsto ?_
  have h := (tendsto_rpow_neg_atTop (neg_pos.2 hℓ)).comp (tendsto_norm_cobounded_atTop (E := E))
  simp only [neg_neg] at h
  exact h

/-- If `f - c` is a symbol of negative order at infinity, then `f` tends to `c` at infinity. -/
theorem tendsto_of_sub {c : F} (hf : IsSymbolAtInfinity k ℓ fun x ↦ f x - c) (hℓ : ℓ < 0) :
    Tendsto f (cobounded E) (𝓝 c) := by
  simpa using (hf.tendsto_zero hℓ).add_const c

/-- Being a symbol at infinity only depends on the map near infinity. -/
theorem congr (hf : IsSymbolAtInfinity k ℓ f) (h : f =ᶠ[cobounded E] f₁) :
    IsSymbolAtInfinity k ℓ f₁ :=
  hf.congr_of_eventually_nhds (Metric.eventually_cobounded_eventually_nhds.2 h)

/-- A symbol of order `ℓ` at infinity has every larger order. -/
theorem mono (hf : IsSymbolAtInfinity k ℓ f) (h : ℓ ≤ m) : IsSymbolAtInfinity k m f :=
  isSymbolAlong_iff.2 ⟨IsSymbolAlong.eventually_contDiffAt hf, fun _ hj ↦
    (IsSymbolAlong.isBigO_iteratedFDeriv hf hj).trans
      (isBigO_norm_rpow_norm_rpow_cobounded (by linarith))⟩

/-- Differentiation lowers the order of a symbol at infinity by one, and its regularity by
one. -/
protected theorem fderiv (hf : IsSymbolAtInfinity (k + 1) ℓ f) :
    IsSymbolAtInfinity k (ℓ - 1) (fderiv ℝ f) :=
  IsSymbolAlong.fderiv (by exact_mod_cast hf)

end IsSymbolAtInfinity

/-! ### Composition with a map smooth at the limit -/

section Composition

variable {k : ℕ} {ℓ : ℝ} {f : E → F} {c : F} {g : F → G}

/-- The regularity facts behind the composition rule: near infinity, `g` is `Cᵏ` at `f x` and
`f` is `Cᵏ` at `x`. -/
private theorem eventually_contDiffAt_comp (hf : IsSymbolAtInfinity k ℓ fun x ↦ f x - c)
    (hℓ : ℓ < 0) (hg : ContDiffAt ℝ k g c) :
    ∀ᶠ x in cobounded E, ContDiffAt ℝ k g (f x) ∧ ContDiffAt ℝ k f x := by
  filter_upwards [(hf.tendsto_of_sub hℓ).eventually (hg.eventually (by simp)),
    hf.eventually_contDiffAt] with x hgx hfx
  exact ⟨hgx, by simpa using hfx.add (contDiffAt_const (c := c))⟩

/-- The derivative bounds of `(D^j g) ∘ f` at order `n + 1`: the derivative of `(D^j g) ∘ f` is
the bilinear expression `(D^{j+1} g ∘ f) ∘ Df`, and `Df` has order `ℓ - 1`, so if the derivatives
of `D^{j+1} g ∘ f` of order `i ≤ n` are `O(‖x‖ ^ (-i))`, then the derivative of `(D^j g) ∘ f` of
order `n + 1` is `O(‖x‖ ^ (ℓ - (n + 1)))`. -/
private theorem isBigO_iteratedFDeriv_comp_succ (hf : IsSymbolAtInfinity k ℓ fun x ↦ f x - c)
    (hℓ : ℓ < 0) (hg : ContDiffAt ℝ k g c) {j n : ℕ} (hjn : n + j + 1 ≤ k)
    (hlow : ∀ i ≤ n, iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ (j + 1) g (f x))
      =O[cobounded E] fun x ↦ ‖x‖ ^ (-(i : ℝ))) :
    iteratedFDeriv ℝ (n + 1) (fun x ↦ iteratedFDeriv ℝ j g (f x)) =O[cobounded E]
      fun x ↦ ‖x‖ ^ (ℓ - (n + 1 : ℕ)) := by
  have hs := eventually_contDiffAt_comp hf hℓ hg
  -- `Df` has order `ℓ - 1`: it is the derivative of `f - c`.
  have hDf : IsSymbolAtInfinity n (ℓ - 1) (fderiv ℝ f) := by
    have h := IsSymbolAtInfinity.fderiv
      (hf.of_le (n' := (n + 1 : ℕ)) (by exact_mod_cast (by omega : n + 1 ≤ k)))
    have hd : fderiv ℝ (fun x ↦ f x - c) = fderiv ℝ f := funext fun _ ↦ fderiv_sub_const c
    rwa [hd] at h
  refine isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq ?_
    (ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_rpow (ℓ := 0) (m := ℓ - 1)
      ((ContinuousLinearMap.compL ℝ E F (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)).comp
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ F)
          G).toContinuousLinearEquiv.toContinuousLinearMap) ?_ hDf.eventually_contDiffAt le_rfl
      (fun i hi ↦ by simpa using hlow i hi) fun i hi ↦ hDf.isBigO_iteratedFDeriv hi) (by ring)
  · filter_upwards [Metric.eventually_cobounded_eventually_nhds.2 hs] with x hx
    filter_upwards [hx] with y hy
    exact fderiv_iteratedFDeriv_comp
      ((hy.1.iteratedFDeriv_right (m := 1) (i := j)
        (by exact_mod_cast (by omega : 1 + j ≤ k))).differentiableAt one_ne_zero)
      (hy.2.differentiableAt (by exact_mod_cast (by omega : k ≠ 0)))
  · filter_upwards [hs] with x hx
    exact (hx.1.iteratedFDeriv_right (m := n) (i := j + 1)
      (by exact_mod_cast (by omega : n + (j + 1) ≤ k))).comp x
      (hx.2.of_le (by exact_mod_cast (by omega : n ≤ k)))

/-- The derivative bounds of `(D^j g) ∘ f` at order `0`, for all `j` at once, by induction on the
derivative order: the derivatives of order `i` with `i + j ≤ k` are `O(‖x‖ ^ (-i))`. -/
private theorem isBigO_iteratedFDeriv_comp (hf : IsSymbolAtInfinity k ℓ fun x ↦ f x - c)
    (hℓ : ℓ < 0) (hg : ContDiffAt ℝ k g c) (n : ℕ) :
    ∀ j i : ℕ, i ≤ n → i + j ≤ k → iteratedFDeriv ℝ i (fun x ↦ iteratedFDeriv ℝ j g (f x))
      =O[cobounded E] fun x ↦ ‖x‖ ^ (-(i : ℝ)) := by
  have hfc := hf.tendsto_of_sub hℓ
  induction n with
  | zero =>
    intro j i hi hij
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    -- `D^j g` is continuous at `c`, so `D^j g ∘ f` tends to `D^j g c` and is bounded.
    have hc : ContinuousAt (iteratedFDeriv ℝ j g) c :=
      (hg.iteratedFDeriv_right (m := 0) (i := j)
        (by exact_mod_cast (by omega : 0 + j ≤ k))).continuousAt
    exact isBigO_iteratedFDeriv_zero_iff.2 (((hc.tendsto.comp hfc).isBigO_one ℝ).congr'
      EventuallyEq.rfl (Eventually.of_forall fun x ↦ by simp))
  | succ n ih =>
    intro j i hi hij
    cases i with
    | zero => exact ih j 0 (Nat.zero_le _) hij
    | succ i =>
      refine (isBigO_iteratedFDeriv_comp_succ hf hℓ hg (by omega)
        fun i' hi' ↦ ih (j + 1) i' (by omega) (by omega)).trans
          (isBigO_norm_rpow_norm_rpow_cobounded ?_)
      push_cast
      linarith

namespace IsSymbolAtInfinity

/-- **Composition with a map smooth at the limit.** If `f - c` is a symbol of negative order at
infinity and regularity `k`, and `g` is `Cᵏ` at `c`, then `g ∘ f` is a symbol of order `0` and
regularity `k`: it is bounded near infinity, and its derivative of order `j ≤ k` is
`O(‖x‖ ^ (-j))`. -/
theorem comp_of_contDiffAt (hf : IsSymbolAtInfinity k ℓ fun x ↦ f x - c) (hℓ : ℓ < 0)
    (hg : ContDiffAt ℝ k g c) : IsSymbolAtInfinity k 0 fun x ↦ g (f x) := by
  refine isSymbolAtInfinity_iff.2 ⟨(eventually_contDiffAt_comp hf hℓ hg).mono
    fun x hx ↦ hx.1.comp x hx.2, fun j hj ↦ ?_⟩
  have h := (isBigO_iteratedFDeriv_comp hf hℓ hg j 0 j le_rfl (by omega)).norm_left
  simp_rw [norm_iteratedFDeriv_iteratedFDeriv_zero_comp] at h
  exact h.of_norm_left.congr' EventuallyEq.rfl (Eventually.of_forall fun x ↦ by simp)

/-- **Composition with a map smooth at the limit, with decay.** If `f - c` is a symbol of
negative order `ℓ` at infinity and regularity `k`, and `g` is `C^(max k 1)` at `c` (so at least
`C¹`), then `g ∘ f - g c` is a symbol of order `ℓ` and regularity `k`. -/
theorem comp_sub (hf : IsSymbolAtInfinity k ℓ fun x ↦ f x - c) (hℓ : ℓ < 0)
    (hg : ContDiffAt ℝ (max k 1 : ℕ) g c) : IsSymbolAtInfinity k ℓ fun x ↦ g (f x) - g c := by
  have hgk : ContDiffAt ℝ k g c := hg.of_le (by exact_mod_cast le_max_left k 1)
  have hs := eventually_contDiffAt_comp hf hℓ hgk
  refine isSymbolAtInfinity_iff.2 ⟨hs.mono fun x hx ↦ (hx.1.comp x hx.2).sub contDiffAt_const,
    fun j hj ↦ ?_⟩
  cases j with
  | zero =>
    -- `g` is differentiable at `c`, so `g ∘ f - g c = O(f - c) = O(‖x‖ ^ ℓ)`.
    have hd : DifferentiableAt ℝ g c := hg.differentiableAt (by exact_mod_cast (by omega))
    have h := (hd.hasFDerivAt.isBigO_sub.comp_tendsto (hf.tendsto_of_sub hℓ)).trans hf.isBigO
    exact isBigO_iteratedFDeriv_zero_iff.2 (by simpa [Function.comp_def] using h)
  | succ j =>
    have h := (isBigO_iteratedFDeriv_comp_succ hf hℓ hgk (j := 0) (by omega)
      fun i hi ↦ isBigO_iteratedFDeriv_comp hf hℓ hgk j 1 i hi (by omega)).norm_left
    simp_rw [norm_iteratedFDeriv_iteratedFDeriv_zero_comp] at h
    refine h.of_norm_left.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
    simp_rw [sub_eq_add_neg, iteratedFDeriv_succ_add_const]

end IsSymbolAtInfinity

end Composition

/-! ### Inversion -/

/-- **Inversion of symbols at infinity.** In a complete normed algebra, if `a - 1` is a symbol of
negative order `ℓ` at infinity, then so is `Ring.inverse a - 1`. Since `a x` tends to `1`, it is
a unit near infinity, where `Ring.inverse (a x)` is its inverse. -/
theorem IsSymbolAtInfinity.ringInverse_sub_one {k : ℕ} {ℓ : ℝ} {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] {a : E → A} (ha : IsSymbolAtInfinity k ℓ fun x ↦ a x - 1)
    (hℓ : ℓ < 0) : IsSymbolAtInfinity k ℓ fun x ↦ Ring.inverse (a x) - 1 := by
  have h := ha.comp_sub hℓ (g := Ring.inverse) (by simpa using contDiffAt_ringInverse ℝ (1 : Aˣ))
  rwa [Ring.inverse_one] at h

end TauCeti
