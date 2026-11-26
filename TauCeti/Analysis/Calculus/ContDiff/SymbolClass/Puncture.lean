/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Basic
import TauCeti.Analysis.Calculus.ContDiffZPow
import TauCeti.Analysis.Calculus.ContDiff.Puncture
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Holder.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Flat
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import TauCeti.Analysis.InnerProductSpace.NormPow

/-!
# Symbol classes at a puncture

A map `f` from a real normed space `E` is a **punctured symbol of order `ℓ`**
(`TauCeti.IsPuncturedSymbol ℓ f`) when it is smooth on a punctured neighbourhood of `0` and,
for every `j`, its `j`-th derivative is `O(‖z‖ ^ (ℓ - j))` as `z → 0`, `z ≠ 0`: a symbol of order
`ℓ` and regularity `∞` along `𝓝[≠] 0` in the sense of `TauCeti.IsSymbolAlong`. On the punctured
disc these are the functions behaving like a homogeneous function of degree `ℓ` together with
all their derivatives: on `ℂ`, `z ↦ z ^ k` has order `k` for every integer `k`
(`TauCeti.isPuncturedSymbol_zpow`). No smoothness at `0` itself is required, and the order is
any real number.

These classes are the bookkeeping device of the local analysis of pseudoholomorphic curves
near a critical point or a point of intersection, where one keeps track of the order of
vanishing of coefficients through products, derivatives, inverses and changes of coordinates.
They form a graded calculus. Sums, linear images, constants and products, where products add
orders, are the filter-independent rules of `TauCeti.IsSymbolAlong` (`IsSymbolAlong.add`,
`IsSymbolAlong.continuousLinearMap_comp`, `TauCeti.isSymbolAlong_const`,
`IsSymbolAlong.bilinear`, `IsSymbolAlong.mul`, `IsSymbolAlong.pow`, …). This file adds the rules
particular to the puncture:

* restrictions to smaller orders (`IsPuncturedSymbol.mono`), and continuous linear maps of order
  `1` (`ContinuousLinearMap.isPuncturedSymbol`);
* **differentiation lowers the order by one** (`IsPuncturedSymbol.fderiv`);
* **inverses negate the order**: a symbol `f` of order `ℓ` with values in a normed division
  algebra and with `‖f z‖ ≥ c ‖z‖ ^ ℓ` has an inverse `z ↦ (f z)⁻¹` of order `-ℓ`
  (`IsPuncturedSymbol.inv`);
* **composition with a reparametrization preserves the order**: if `g` has order `ℓ` and `φ` has
  order `1` with `‖φ z‖ ≥ c ‖z‖`, then `g ∘ φ` has order `ℓ` (`IsPuncturedSymbol.comp`);
* **composition with a smooth map**: if `φ` has order `ℓ ≥ 0` and `g` is smooth with bounded
  derivatives along the image of `φ`, then `g ∘ φ` has order `0`
  (`IsPuncturedSymbol.comp_left`), and order `ℓ` when moreover `g ∘ φ = O(‖z‖ ^ ℓ)`
  (`IsPuncturedSymbol.comp_left_of_isBigO`).

The last three are proved by induction on the order of the derivative: the derivative of
`(f z)⁻¹` is a bilinear expression in `(f z)⁻¹`, `(f z)⁻¹` and `Df z`, and the derivative of
`(D^j g) ∘ φ` is a bilinear expression in `(D^{j+1} g) ∘ φ` and `Dφ`, so the product rule at
lower derivative orders controls the next order.

**Examples.** Besides constants, continuous linear maps and the integer powers on `ℂ`, a map
smooth near `0` whose derivatives of order less than `n` vanish at `0` has order `n`
(`TauCeti.isPuncturedSymbol_of_iteratedFDeriv_eq_zero`). On a proper space, a map smooth away
from `0` and positively homogeneous of degree `ℓ` has order `ℓ`
(`TauCeti.isPuncturedSymbol_of_homogeneous`); in particular, on a proper real inner product
space, so does `z ↦ ‖z‖ ^ ℓ` (`TauCeti.isPuncturedSymbol_norm_rpow`).

**Removability at the puncture.** Nothing is asked of a symbol at `0`, but a symbol vanishing at
`0` is as regular across the puncture as its order allows:

* of positive order it is continuous at `0` (`IsPuncturedSymbol.continuousAt`), of order `ℓ > 1`
  it is differentiable at `0` with derivative `0` (`IsPuncturedSymbol.hasFDerivAt`), and of order
  `ℓ > k` it is `Cᵏ` at `0` and on a neighbourhood of `0` (`IsPuncturedSymbol.contDiffAt`,
  `IsPuncturedSymbol.eventually_nhds_contDiffAt`);
* it is `α`-Hölder on a ball about `0` for every `α ≤ min ℓ 1`
  (`IsPuncturedSymbol.exists_holderOnWith`), and `C¹` with `α`-Hölder derivative for every
  `0 < α ≤ 1` with `α + 1 ≤ ℓ` (`IsPuncturedSymbol.exists_contDiffOn_holderOnWith_fderiv`). In
  particular a symbol of order `ℓ ≥ 2` is `C^{1,1}` near `0`, hence, for a symbol on the plane
  with values in a finite-dimensional space, locally `W^{2,∞}`
  (`TauCeti.IsPuncturedSymbol.exists_memWkpLoc_two`).

So symbols of order at least two, such as the deviations of coefficients from their values at a
critical point, can serve as `C^{1,α}` coefficients of elliptic equations across the puncture.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix E (the Micallef–White theorem on the local
  behaviour of pseudoholomorphic curves, whose proof tracks functions on the punctured disc by
  derivative bounds of this kind).
-/

public section

open Set Filter Asymptotics
open scoped Topology ContDiff NNReal

namespace TauCeti

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NormedAddCommGroup H]

/-! ### Auxiliary facts about punctured neighbourhoods -/

private theorem eventually_norm_pos : ∀ᶠ z in 𝓝[≠] (0 : E), 0 < ‖z‖ := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact norm_pos_iff.2 hz

private theorem eventually_norm_le_one : ∀ᶠ z in 𝓝[≠] (0 : E), ‖z‖ ≤ 1 :=
  nhdsWithin_le_nhds <| by
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with z hz
    simpa using hz

/-- Near `0`, a power of the norm is dominated by every power with a smaller exponent. -/
private theorem isBigO_rpow_of_le {a b : ℝ} (h : b ≤ a) :
    (fun z : E ↦ ‖z‖ ^ a) =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ b := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_norm_pos, eventually_norm_le_one] with z hz hz1
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_ge hz hz1 h

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]

/-- A map `f` is a **punctured symbol of order `ℓ`** at `0` if it is smooth on a punctured
neighbourhood of `0` and its `j`-th derivative is `O(‖z‖ ^ (ℓ - j))` as `z → 0` with `z ≠ 0`, for
every `j`: a symbol of order `ℓ` and regularity `∞` along `𝓝[≠] 0`. Nothing is asked of `f` at
`0` itself. -/
abbrev IsPuncturedSymbol (ℓ : ℝ) (f : E → F) : Prop :=
  IsSymbolAlong (𝓝[≠] (0 : E)) ⊤ ℓ f

/-- The defining properties of a punctured symbol: smoothness on a punctured neighbourhood of `0`
and the bounds `D^j f = O(‖z‖ ^ (ℓ - j))` for every `j`. -/
theorem isPuncturedSymbol_iff {ℓ : ℝ} {f : E → F} :
    IsPuncturedSymbol ℓ f ↔ (∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z) ∧
      ∀ j : ℕ, iteratedFDeriv ℝ j f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j) :=
  isSymbolAlong_iff.trans (and_congr_right' <| forall_congr' fun _ ↦ forall_prop_of_true le_top)

/-! ### Basic properties -/

namespace IsPuncturedSymbol

variable {ℓ m : ℝ} {f f₁ : E → F}

/-- The `j`-th derivative of a punctured symbol of order `ℓ` is `O(‖z‖ ^ (ℓ - j))`. -/
theorem isBigO_iteratedFDeriv (hf : IsPuncturedSymbol ℓ f) (j : ℕ) :
    iteratedFDeriv ℝ j f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j) :=
  IsSymbolAlong.isBigO_iteratedFDeriv hf le_top

/-- A punctured symbol of positive order tends to `0` at the puncture. -/
theorem tendsto_zero (hf : IsPuncturedSymbol ℓ f) (hℓ : 0 < ℓ) :
    Tendsto f (𝓝[≠] (0 : E)) (𝓝 0) := by
  refine hf.isBigO.trans_tendsto ?_
  have hc : ContinuousAt (fun z : E ↦ ‖z‖ ^ ℓ) 0 :=
    (continuous_norm.rpow_const fun _ ↦ Or.inr hℓ.le).continuousAt
  simpa [Real.zero_rpow hℓ.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- Being a punctured symbol only depends on the map on a punctured neighbourhood of `0`. -/
theorem congr (hf : IsPuncturedSymbol ℓ f) (h : f =ᶠ[𝓝[≠] (0 : E)] f₁) :
    IsPuncturedSymbol ℓ f₁ :=
  hf.congr_of_eventually_nhds
    ((eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_compl_singleton).2 h)

/-- A punctured symbol of order `ℓ` has every smaller order. -/
theorem mono (hf : IsPuncturedSymbol ℓ f) (h : m ≤ ℓ) : IsPuncturedSymbol m f :=
  isPuncturedSymbol_iff.2 ⟨hf.eventually_contDiffAt,
    fun j ↦ (hf.isBigO_iteratedFDeriv j).trans (isBigO_rpow_of_le (by linarith))⟩

/-- Differentiation lowers the order of a punctured symbol by one. -/
protected theorem fderiv (hf : IsPuncturedSymbol ℓ f) :
    IsPuncturedSymbol (ℓ - 1) (fderiv ℝ f) :=
  IsSymbolAlong.fderiv (n := ⊤) (by rwa [top_add])

end IsPuncturedSymbol

/-- A continuous linear map is a punctured symbol of order `1`. -/
theorem _root_.ContinuousLinearMap.isPuncturedSymbol (L : E →L[ℝ] F) :
    IsPuncturedSymbol 1 L := by
  refine isSymbolAlong_iff.2 ⟨Eventually.of_forall fun _ ↦ L.contDiff.contDiffAt, fun j _ ↦ ?_⟩
  cases j with
  | zero =>
    refine IsBigO.of_bound ‖L‖ (Eventually.of_forall fun z ↦ ?_)
    simpa using L.le_opNorm z
  | succ j =>
    exact isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq (g := fun _ ↦ L)
      (Eventually.of_forall fun _ ↦ .of_forall fun _ ↦ L.fderiv)
      ((isSymbolAlong_const (n := ⊤) L).isBigO_iteratedFDeriv le_top) (by ring)

/-- The identity is a punctured symbol of order `1`. -/
theorem isPuncturedSymbol_id : IsPuncturedSymbol 1 fun z : E ↦ z :=
  (ContinuousLinearMap.id ℝ E).isPuncturedSymbol

/-! ### Inverses -/

section Inverse

variable {ℓ : ℝ} {R : Type*} [NormedDivisionRing R] [NormedAlgebra ℝ R] {f : E → R}

/-- Inversion is smooth wherever `f` is smooth and nonzero: `ContDiffAt.zpow` at exponent `-1`. -/
private theorem eventually_contDiffAt_inv
    (hf : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z ∧ f z ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ (fun z ↦ (f z)⁻¹) z :=
  hf.mono fun _ hz ↦ by simpa using hz.1.zpow (m := -1) (Or.inl hz.2)

/-- Near every point of a punctured neighbourhood where `f` is smooth and invertible, the
derivative of `f⁻¹` is the bilinear expression `-(f⁻¹ ⬝ f⁻¹) ∘ Df` in `f⁻¹ ⊗ f⁻¹` and `Df`. -/
private theorem eventually_fderiv_inv_eventuallyEq
    (hf : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z ∧ f z ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : E), fderiv ℝ (fun z ↦ (f z)⁻¹) =ᶠ[𝓝 z] fun y ↦
      (-ContinuousLinearMap.compL ℝ E R R)
        (ContinuousLinearMap.mulLeftRight ℝ R (f y)⁻¹ (f y)⁻¹) (fderiv ℝ f y) := by
  filter_upwards [(eventually_nhdsWithin_eventually_nhds_iff_of_isOpen
    isOpen_compl_singleton).2 hf] with z hz
  filter_upwards [hz] with y hy
  have hfd : HasFDerivAt f (fderiv ℝ f y) y := (hy.1.differentiableAt (by simp)).hasFDerivAt
  rw [← Function.comp_def, ((hasFDerivAt_inv' hy.2).comp y hfd).fderiv]
  simp [ContinuousLinearMap.neg_comp]

/-- The derivative bounds of `f⁻¹`, by induction on the derivative order: the derivative of
`f⁻¹` is a bilinear expression in `f⁻¹ ⊗ f⁻¹` and `Df`, whose derivatives of order `k` are
controlled by those of `f⁻¹` of order at most `k`. -/
private theorem isBigO_iteratedFDeriv_inv (hf : IsPuncturedSymbol ℓ f) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ^ ℓ ≤ ‖f z‖)
    (hne : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z ∧ f z ≠ 0) (n : ℕ) :
    ∀ i ≤ n, iteratedFDeriv ℝ i (fun z ↦ (f z)⁻¹) =O[𝓝[≠] (0 : E)]
      fun z ↦ ‖z‖ ^ (-ℓ - i) := by
  have hg := eventually_contDiffAt_inv hne
  have hDf := hf.fderiv
  induction n with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    refine IsBigO.of_bound c⁻¹ ?_
    filter_upwards [hlow, eventually_norm_pos] with z hz hz0
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, sub_zero, norm_inv, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), Real.rpow_neg hz0.le, ← mul_inv]
    exact inv_anti₀ (by positivity) hz
  | succ n ih =>
    intro i hi
    cases i with
    | zero => exact ih 0 (Nat.zero_le _)
    | succ k =>
      have hk : k ≤ n := Nat.succ_le_succ_iff.1 hi
      have hgg : ∀ᶠ z in 𝓝[≠] (0 : E),
          ContDiffAt ℝ ∞ (fun z ↦ ContinuousLinearMap.mulLeftRight ℝ R (f z)⁻¹ (f z)⁻¹) z :=
        hg.mono fun _ hz ↦ (ContinuousLinearMap.mulLeftRight ℝ R).isBoundedBilinearMap.contDiff
          |>.comp₂_contDiffAt hz hz
      have hprod := (-ContinuousLinearMap.compL ℝ E R R).isBigO_iteratedFDeriv_of_bilinear_rpow
        hgg hDf.eventually_contDiffAt (n := k) (ℓ := -ℓ + -ℓ) (m := ℓ - 1)
        (by exact_mod_cast le_top)
        (fun i hi ↦ (ContinuousLinearMap.mulLeftRight ℝ R).isBigO_iteratedFDeriv_of_bilinear_rpow
          hg hg (by exact_mod_cast le_top) (fun j hj ↦ ih j (hj.trans (hi.trans hk)))
          (fun j hj ↦ ih j (hj.trans (hi.trans hk))))
        (fun i _ ↦ hDf.isBigO_iteratedFDeriv i)
      exact isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq
        (eventually_fderiv_inv_eventuallyEq hne) hprod (by ring)

/-- **The inverse of a punctured symbol.** If `f` has order `ℓ`, with values in a normed
division algebra, and `‖f z‖ ≥ c ‖z‖ ^ ℓ` near `0` for some `c > 0`, then `z ↦ (f z)⁻¹` is a
punctured symbol of order `-ℓ`. -/
theorem IsPuncturedSymbol.inv (hf : IsPuncturedSymbol ℓ f) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ^ ℓ ≤ ‖f z‖) :
    IsPuncturedSymbol (-ℓ) fun z ↦ (f z)⁻¹ := by
  have hne : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z ∧ f z ≠ 0 := by
    filter_upwards [hf.eventually_contDiffAt, hlow, eventually_norm_pos] with z hfz hz hz0
    exact ⟨hfz, norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hz)⟩
  exact isSymbolAlong_iff.2 ⟨eventually_contDiffAt_inv hne,
    fun j _ ↦ isBigO_iteratedFDeriv_inv hf hc hlow hne j j le_rfl⟩

end Inverse

/-- On a normed division algebra, such as `ℂ`, the power `z ↦ z ^ k` is a punctured symbol of
order `k` for every integer `k`. -/
theorem isPuncturedSymbol_zpow {𝕜 : Type*} [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜] (k : ℤ) :
    IsPuncturedSymbol (k : ℝ) fun z : 𝕜 ↦ z ^ k := by
  have hpow (n : ℕ) : IsPuncturedSymbol (n : ℝ) fun z : 𝕜 ↦ z ^ n := by
    simpa using (isPuncturedSymbol_id (E := 𝕜)).pow n
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hpow n
  · have h := (hpow n).inv one_pos
      (Eventually.of_forall fun z ↦ by rw [one_mul, norm_pow, Real.rpow_natCast])
    simpa [zpow_neg] using h

/-! ### Composition with a reparametrization -/

section Composition

variable {ℓ : ℝ} {g : F → G} {φ : E → F}

/-- A punctured symbol of order `1` bounded below by `c ‖z‖` maps punctured neighbourhoods of `0`
to punctured neighbourhoods of `0`. -/
private theorem tendsto_nhdsNE_of_le (hφ : IsPuncturedSymbol 1 φ) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ≤ ‖φ z‖) :
    Tendsto φ (𝓝[≠] (0 : E)) (𝓝[≠] (0 : F)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨hφ.tendsto_zero one_pos, ?_⟩
  filter_upwards [hlow, eventually_norm_pos] with z hz hz0
  exact norm_pos_iff.1 (lt_of_lt_of_le (mul_pos hc hz0) hz)

/-- The chain rule for `(D^j g) ∘ φ`: near every point of a punctured neighbourhood where `g` is
smooth at `φ z` and `φ` is smooth at `z`, its derivative is the bilinear expression
`(D^{j+1} g ∘ φ) ∘ Dφ`, read through the currying of the first variable. -/
private theorem eventually_fderiv_comp_eventuallyEq
    (hs : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z) ∧ ContDiffAt ℝ ∞ φ z) (j : ℕ) :
    ∀ᶠ z in 𝓝[≠] (0 : E), fderiv ℝ (fun z ↦ iteratedFDeriv ℝ j g (φ z)) =ᶠ[𝓝 z] fun y ↦
      (ContinuousLinearMap.compL ℝ E F (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)).comp
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ F)
          G).toContinuousLinearEquiv.toContinuousLinearMap
        (iteratedFDeriv ℝ (j + 1) g (φ y)) (fderiv ℝ φ y) := by
  filter_upwards [(eventually_nhdsWithin_eventually_nhds_iff_of_isOpen
    isOpen_compl_singleton).2 hs] with z hz
  filter_upwards [hz] with y hy
  have hgd : DifferentiableAt ℝ (iteratedFDeriv ℝ j g) (φ y) :=
    (hy.1.iteratedFDeriv_right (m := 1) (i := j) (by simp)).differentiableAt one_ne_zero
  exact fderiv_iteratedFDeriv_comp hgd (hy.2.differentiableAt (by simp))

/-- The derivative bounds of `(D^j g) ∘ φ`, for all `j` at once, from those of derivative order
`0`, by induction on the derivative order: the derivative of `(D^j g) ∘ φ` is a bilinear
expression in `(D^{j+1} g) ∘ φ` and `Dφ`. If `(D^j g) ∘ φ` is `O(‖z‖ ^ a j)` for every `j`, and
`φ` has order `p` with `a j ≤ a (j + 1) + p`, then the `i`-th derivative of `(D^j g) ∘ φ` is
`O(‖z‖ ^ (a j - i))`. -/
private theorem isBigO_iteratedFDeriv_comp_of_isBigO {p : ℝ} {a : ℕ → ℝ}
    (hs : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z) ∧ ContDiffAt ℝ ∞ φ z)
    (hφ : IsPuncturedSymbol p φ) (ha : ∀ j, a j ≤ a (j + 1) + p)
    (h0 : ∀ j, (fun z ↦ iteratedFDeriv ℝ j g (φ z)) =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ a j)
    (n : ℕ) :
    ∀ j : ℕ, ∀ i ≤ n, iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j g (φ z))
      =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (a j - i) := by
  have hDφ := hφ.fderiv
  induction n with
  | zero =>
    intro j i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    exact isBigO_iteratedFDeriv_zero_iff.2 (by simpa using h0 j)
  | succ n ih =>
    intro j i hi
    cases i with
    | zero => exact ih j 0 (Nat.zero_le _)
    | succ k =>
      have hk : k ≤ n := Nat.succ_le_succ_iff.1 hi
      have hDj : ∀ᶠ z in 𝓝[≠] (0 : E),
          ContDiffAt ℝ ∞ (fun z ↦ iteratedFDeriv ℝ (j + 1) g (φ z)) z := by
        filter_upwards [hs] with z hz
        exact (hz.1.iteratedFDeriv_right (m := ∞) (i := j + 1) (by simp)).comp z hz.2
      have hprod := ContinuousLinearMap.isBigO_iteratedFDeriv_of_bilinear_rpow
        (Z := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)
        ((ContinuousLinearMap.compL ℝ E F (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)).comp
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ F)
            G).toContinuousLinearEquiv.toContinuousLinearMap) hDj hDφ.eventually_contDiffAt (n := k)
        (ℓ := a (j + 1)) (m := p - 1) (by exact_mod_cast le_top)
        (fun i hi ↦ ih (j + 1) i (hi.trans hk)) (fun i _ ↦ hDφ.isBigO_iteratedFDeriv i)
      exact (isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq
        (eventually_fderiv_comp_eventuallyEq hs j) hprod (b := a (j + 1) + p) (by ring)).trans
        (isBigO_rpow_of_le (by linarith [ha j]))

/-- A bound on the derivatives of `(D^0 g) ∘ φ` is one on those of `g ∘ φ`, since their norms
agree (`TauCeti.norm_iteratedFDeriv_iteratedFDeriv_zero_comp`). -/
private theorem isBigO_iteratedFDeriv_comp_of_iteratedFDeriv_zero {ρ : E → ℝ} {i : ℕ}
    (h : iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ 0 g (φ z)) =O[𝓝[≠] (0 : E)] ρ) :
    iteratedFDeriv ℝ i (fun z ↦ g (φ z)) =O[𝓝[≠] (0 : E)] ρ := by
  have h' := h.norm_left
  simp_rw [norm_iteratedFDeriv_iteratedFDeriv_zero_comp] at h'
  exact h'.of_norm_left

/-- **Composition with a reparametrization.** If `g` is a punctured symbol of order `ℓ` and
`φ` is a punctured symbol of order `1` with `‖φ z‖ ≥ c ‖z‖` near `0` for some `c > 0`, then
`g ∘ φ` is a punctured symbol of order `ℓ`. -/
theorem IsPuncturedSymbol.comp (hg : IsPuncturedSymbol ℓ g) (hφ : IsPuncturedSymbol 1 φ) {c : ℝ}
    (hc : 0 < c) (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ≤ ‖φ z‖) :
    IsPuncturedSymbol ℓ fun z ↦ g (φ z) := by
  have hφ0 := tendsto_nhdsNE_of_le hφ hc hlow
  have hs : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z) ∧ ContDiffAt ℝ ∞ φ z :=
    (hφ0.eventually hg.eventually_contDiffAt).and hφ.eventually_contDiffAt
  -- `(D^j g) ∘ φ` is `O(‖φ z‖ ^ (ℓ - j))`, and `‖φ z‖` is comparable to `‖z‖`.
  have hθ : (fun z ↦ ‖φ z‖) =Θ[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ := by
    refine ⟨hφ.isBigO.norm_left.congr' EventuallyEq.rfl
      (Eventually.of_forall fun z ↦ Real.rpow_one _), IsBigO.of_bound c⁻¹ ?_⟩
    filter_upwards [hlow] with z hz
    simpa only [norm_norm, le_inv_mul_iff₀ hc] using hz
  have h := isBigO_iteratedFDeriv_comp_of_isBigO hs hφ (a := fun j ↦ ℓ - j)
    (fun j ↦ by push_cast; linarith) (fun j ↦ IsBigO.of_norm_left
      (((hg.isBigO_iteratedFDeriv j).comp_tendsto hφ0).norm_left.trans
        (hθ.rpow (r := ℓ - j) (Eventually.of_forall fun _ ↦ norm_nonneg _)
          (Eventually.of_forall fun _ ↦ norm_nonneg _)).isBigO))
  refine isPuncturedSymbol_iff.2 ⟨?_, fun j ↦ ?_⟩
  · filter_upwards [hs] with z hz
    exact hz.1.comp z hz.2
  · simpa using isBigO_iteratedFDeriv_comp_of_iteratedFDeriv_zero (h j 0 j le_rfl)

/-! ### Composition with a smooth map -/

/-- **Composition with a smooth map, keeping the order.** Let `φ` be a punctured symbol of
order `ℓ ≥ 0`, and let `g` be smooth along the image of `φ` near `0`, with derivatives of
positive order bounded along it. If `g ∘ φ` is `O(‖z‖ ^ ℓ)`, then `g ∘ φ` is a punctured symbol
of order `ℓ`. -/
theorem IsPuncturedSymbol.comp_left_of_isBigO (hφ : IsPuncturedSymbol ℓ φ) (hℓ : 0 ≤ ℓ)
    (hg : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z))
    (hgb : ∀ j : ℕ,
      (fun z ↦ iteratedFDeriv ℝ (j + 1) g (φ z)) =O[𝓝[≠] (0 : E)] fun _ ↦ (1 : ℝ))
    (h0 : (fun z ↦ g (φ z)) =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ ℓ) :
    IsPuncturedSymbol ℓ fun z ↦ g (φ z) := by
  have hs : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z) ∧ ContDiffAt ℝ ∞ φ z :=
    hg.and hφ.eventually_contDiffAt
  -- `g ∘ φ` has order `ℓ` and `(D^{j+1} g) ∘ φ` has order `0`.
  have h := isBigO_iteratedFDeriv_comp_of_isBigO hs hφ (a := fun j ↦ if j = 0 then ℓ else 0)
    (fun j ↦ by split_ifs <;> simp_all) fun j ↦ ?_
  · refine isPuncturedSymbol_iff.2 ⟨?_, fun j ↦ ?_⟩
    · filter_upwards [hs] with z hz
      exact hz.1.comp z hz.2
    · simpa using isBigO_iteratedFDeriv_comp_of_iteratedFDeriv_zero (h j 0 j le_rfl)
  · cases j with
    | zero => exact IsBigO.of_norm_left (by simpa [norm_iteratedFDeriv_zero] using h0.norm_left)
    | succ j => simpa using hgb j

/-- **Composition with a smooth map.** If `φ` is a punctured symbol of order `ℓ ≥ 0` and `g` is
smooth along the image of `φ` near `0`, with all its derivatives bounded along it, then `g ∘ φ`
is a punctured symbol of order `0`. -/
theorem IsPuncturedSymbol.comp_left (hφ : IsPuncturedSymbol ℓ φ) (hℓ : 0 ≤ ℓ)
    (hg : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z))
    (hgb : ∀ j : ℕ, (fun z ↦ iteratedFDeriv ℝ j g (φ z)) =O[𝓝[≠] (0 : E)] fun _ ↦ (1 : ℝ)) :
    IsPuncturedSymbol 0 fun z ↦ g (φ z) :=
  (hφ.mono hℓ).comp_left_of_isBigO le_rfl hg (fun j ↦ hgb (j + 1))
    (by simpa [norm_iteratedFDeriv_zero] using (hgb 0).norm_left)

end Composition

/-! ### Examples -/

section Examples

open Function

variable {ℓ : ℝ} {f : E → F}

/-- **Smooth maps vanishing to order `n`.** A map smooth on a neighbourhood of `0` whose
derivatives of order less than `n` vanish at `0` is a punctured symbol of order `n`. -/
theorem isPuncturedSymbol_of_iteratedFDeriv_eq_zero {n : ℕ}
    (hf : ∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ ∞ f z) (hzero : ∀ i < n, iteratedFDeriv ℝ i f 0 = 0) :
    IsPuncturedSymbol n f := by
  -- every derivative is continuous at `0`, hence bounded near `0`
  have hbdd (k : ℕ) : iteratedFDeriv ℝ k f =O[𝓝 (0 : E)] fun _ ↦ (1 : ℝ) :=
    (hf.self_of_nhds.iteratedFDeriv_right (m := 0) (i := k) (by simp)).continuousAt.tendsto
      |>.isBigO_one ℝ
  refine isPuncturedSymbol_iff.2 ⟨hf.filter_mono nhdsWithin_le_nhds, fun k ↦ ?_⟩
  rcases lt_or_ge k n with hkn | hnk
  · -- Below the order of vanishing, iterate the mean value inequality from `0`.
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    obtain ⟨M, hM⟩ := (hbdd (p + 1)).bound
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and hM)
    have h := norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero (k := p)
      (fun y hy ↦ (hball y hy).1.of_le (by exact_mod_cast le_top)) (convex_ball 0 δ)
      (Metric.mem_ball_self hδ) (fun y hy ↦ by simpa using (hball y hy).2)
      (fun i _ hi ↦ hzero i (by omega)) (p - k) (by omega)
    refine IsBigO.of_bound M ?_
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : E) hδ)] with z hz
    have hz' := h z hz
    rw [show p - (p - k) = k by omega, hzero k hkn, sub_zero, sub_zero] at hz'
    rw [Real.norm_of_nonneg (by positivity)]
    refine hz'.trans_eq ?_
    rw [← Real.rpow_natCast]
    congr 2
    push_cast [show p - k + 1 = p + 1 - k by omega, Nat.cast_sub hkn.le]
    ring
  · -- Above it, the derivatives are bounded, and `‖z‖ ^ (n - k)` is bounded below near `0`.
    refine ((hbdd k).mono nhdsWithin_le_nhds).trans ?_
    simpa using isBigO_rpow_of_le (E := E) (a := 0) (b := n - k) (by simpa using hnk)

/-- **Homogeneous maps.** On a proper space, a map smooth away from `0` and positively homogeneous
of degree `ℓ` away from `0` is a punctured symbol of order `ℓ`. -/
theorem isPuncturedSymbol_of_homogeneous [ProperSpace E] (hf : ContDiffOn ℝ ∞ f {0}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x ≠ 0, f (t • x) = t ^ ℓ • f x) : IsPuncturedSymbol ℓ f := by
  classical
  -- `update f 0 0` agrees with `f` away from `0` and is positively homogeneous everywhere.
  have hhom' (t : ℝ) (ht : 0 < t) (x : E) :
      update f 0 0 (t • x) = t ^ ℓ • update f 0 0 x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [update_of_ne (smul_ne_zero ht.ne' hx), update_of_ne hx, hhom t ht x hx]
  have hf' : ContDiffOn ℝ ∞ (update f 0 0) {0}ᶜ :=
    hf.congr fun x hx ↦ update_of_ne hx _ _
  refine IsPuncturedSymbol.congr (isPuncturedSymbol_iff.2 ⟨eventually_nhdsWithin_of_forall
    fun x hx ↦ hf'.contDiffAt (isOpen_compl_singleton.mem_nhds hx), fun k ↦ ?_⟩)
    (eventually_nhdsWithin_of_forall fun x hx ↦ update_of_ne hx _ _)
  -- The derivative is bounded on the unit sphere, and homogeneity scales it from there.
  obtain ⟨M, -, hM⟩ := (hf'.of_le (m := k) (by exact_mod_cast le_top)
    ).exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_compl_singleton
    (isCompact_sphere (0 : E) 1) fun x hx ↦ Metric.ne_of_mem_sphere hx one_ne_zero
  refine IsBigO.of_bound M (eventually_nhdsWithin_of_forall fun z hz ↦ ?_)
  have hρ : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hρ.ne']
  have hscale := norm_iteratedFDeriv_smul_of_homogeneous hhom' hρ (x := ‖z‖⁻¹ • z) (j := k)
  rw [smul_inv_smul₀ hρ.ne'] at hscale
  rw [hscale, Real.norm_of_nonneg (by positivity), mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM k le_rfl _ hu) (by positivity)

/-- On a proper real inner product space, the power `z ↦ ‖z‖ ^ ℓ` of the norm is a punctured
symbol of order `ℓ`. -/
theorem isPuncturedSymbol_norm_rpow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [ProperSpace E] (ℓ : ℝ) : IsPuncturedSymbol ℓ fun z : E ↦ ‖z‖ ^ ℓ :=
  isPuncturedSymbol_of_homogeneous (fun x hx ↦
    (contDiffAt_norm_rpow_of_ne (n := ∞) ℓ hx).contDiffWithinAt)
    fun t ht x _ ↦ by
      rw [norm_smul, Real.norm_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg x), smul_eq_mul]

end Examples

/-! ### Removability at the puncture -/

section Removable

namespace IsPuncturedSymbol

variable {ℓ : ℝ} {f : E → F}

/-- Points near `0` other than `0` itself are points of smoothness of a punctured symbol, read on
the full neighbourhood filter. -/
private theorem eventually_nhds_contDiffAt_of_ne (hf : IsPuncturedSymbol ℓ f) :
    ∀ᶠ z in 𝓝 (0 : E), z ≠ 0 → ContDiffAt ℝ ∞ f z :=
  eventually_nhdsWithin_iff.1 hf.eventually_contDiffAt

/-- A punctured symbol of positive order which vanishes at `0` is continuous at `0`. -/
theorem continuousAt (hf : IsPuncturedSymbol ℓ f) (hℓ : 0 < ℓ) (h0 : f 0 = 0) :
    ContinuousAt f 0 := by
  rw [continuousAt_iff_punctured_nhds, h0]
  exact hf.tendsto_zero hℓ

/-- A punctured symbol of order `ℓ > 1` which vanishes at `0` is differentiable at `0`, with
derivative `0`. -/
theorem hasFDerivAt (hf : IsPuncturedSymbol ℓ f) (hℓ : 1 < ℓ) (h0 : f 0 = 0) :
    HasFDerivAt f (0 : E →L[ℝ] F) 0 :=
  hasFDerivAt_zero_of_isBigO_rpow h0 (by simpa using hf.isBigO) hℓ

universe u v in
/-- `IsPuncturedSymbol.contDiffAt` for a codomain in a universe at least that of `E`, where the
induction on `k`, which passes from `f` to `fderiv ℝ f`, stays in one universe. -/
private theorem contDiffAt_aux {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :
    ∀ {F : Type max u v} [NormedAddCommGroup F] [NormedSpace ℝ F] {ℓ : ℝ} {f : E → F},
      IsPuncturedSymbol ℓ f → (k : ℝ) < ℓ → f 0 = 0 → ContDiffAt ℝ k f 0 := by
  -- the derivative is a punctured symbol of order `ℓ - 1 > k - 1` vanishing at `0`
  induction k with
  | zero =>
    intro F _ _ ℓ f hf hk h0
    refine contDiffAt_zero.2 ⟨_, hf.eventually_nhds_contDiffAt_of_ne, fun z hz ↦ ?_⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · exact (hf.continuousAt (by simpa using hk) h0).continuousWithinAt
    · exact (hz hz0).continuousAt.continuousWithinAt
  | succ k ih =>
    intro F _ _ ℓ f hf hk h0
    have hk' : (k : ℝ) + 1 < ℓ := by exact_mod_cast hk
    have hD := hf.hasFDerivAt (by linarith [k.cast_nonneg (α := ℝ)]) h0
    rw [Nat.cast_succ]
    refine contDiffAt_succ_iff_hasFDerivAt.2 ⟨fderiv ℝ f, ⟨_, hf.eventually_nhds_contDiffAt_of_ne,
      fun z hz ↦ ?_⟩, ih hf.fderiv (by linarith) hD.fderiv⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · rwa [hD.fderiv]
    · exact ((hz hz0).differentiableAt (by simp)).hasFDerivAt

/-- **Removability.** A punctured symbol of order `ℓ > k` which vanishes at `0` is `Cᵏ` at `0`.
-/
theorem contDiffAt.{u, v} {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {k : ℕ} (hf : IsPuncturedSymbol ℓ f)
    (hk : (k : ℝ) < ℓ) (h0 : f 0 = 0) : ContDiffAt ℝ k f 0 := by
  -- lift the codomain to a universe containing that of `E`, as `contDiffAt_aux` needs
  let e : ULift.{u} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  have h := contDiffAt_aux k (hf.continuousLinearMap_comp (e.symm : F →L[ℝ] ULift F)) hk
    (by rw [h0]; exact map_zero _)
  -- `h` is about `fun z ↦ (e.symm : F →L[ℝ] ULift F) (f z)`, that is `⇑e.symm ∘ f`
  exact e.symm.comp_contDiffAt_iff.1 (by simpa only [ContinuousLinearEquiv.coe_coe,
    Function.comp_def] using h)

/-- A punctured symbol of order `ℓ > k` which vanishes at `0` is `Cᵏ` on a neighbourhood of `0`. -/
theorem eventually_nhds_contDiffAt {k : ℕ} (hf : IsPuncturedSymbol ℓ f) (hk : (k : ℝ) < ℓ)
    (h0 : f 0 = 0) : ∀ᶠ z in 𝓝 (0 : E), ContDiffAt ℝ k f z := by
  filter_upwards [hf.eventually_nhds_contDiffAt_of_ne] with z hz
  rcases eq_or_ne z 0 with rfl | hz0
  · exact hf.contDiffAt hk h0
  · exact (hz hz0).of_le (by exact_mod_cast le_top)

/-- The constants of a punctured symbol on a ball: differentiability off the centre and the bounds
`‖f z‖ ≤ A ‖z‖ ^ ℓ` and `‖Df z‖ ≤ B ‖z‖ ^ (ℓ - 1)`. -/
private theorem exists_ball_bounds (hf : IsPuncturedSymbol ℓ f) :
    ∃ r > 0, ∃ A B : ℝ≥0, ∀ z ∈ Metric.ball (0 : E) r, z ≠ 0 →
      DifferentiableAt ℝ f z ∧ ‖f z‖ ≤ A * ‖z‖ ^ ℓ ∧ ‖fderiv ℝ f z‖ ≤ B * ‖z‖ ^ (ℓ - 1) := by
  obtain ⟨A, hA, hAf⟩ := hf.isBigO.exists_nonneg
  obtain ⟨B, hB, hBf⟩ := hf.fderiv.isBigO.exists_nonneg
  have h := hf.eventually_contDiffAt.and (hAf.bound.and hBf.bound)
  obtain ⟨r, hr, hrf⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_nhdsWithin_iff.1 h)
  refine ⟨r, hr, A.toNNReal, B.toNNReal, fun z hz hz0 ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := hrf z hz hz0
  have hn : ∀ a : ℝ, ‖‖z‖ ^ a‖ = ‖z‖ ^ a := fun a ↦
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) a)
  rw [hn] at h2 h3
  rw [Real.coe_toNNReal _ hA, Real.coe_toNNReal _ hB]
  exact ⟨h1.differentiableAt (by simp), h2, h3⟩

/-- **Hölder continuity across the puncture.** A punctured symbol of order `ℓ` which vanishes at
`0` is `α`-Hölder on a ball about `0` for every exponent `α ≤ min ℓ 1`. -/
theorem exists_holderOnWith (hf : IsPuncturedSymbol ℓ f) {α : ℝ≥0} (hαℓ : (α : ℝ) ≤ ℓ)
    (hα1 : α ≤ 1) (h0 : f 0 = 0) :
    ∃ C : ℝ≥0, ∃ r > 0, HolderOnWith C α f (Metric.ball (0 : E) r) := by
  obtain ⟨r, hr, A, B, hbd⟩ := exists_ball_bounds (hf.mono hαℓ)
  exact ⟨B + 4 * A, r, hr, holderOnWith_ball_of_norm_le_rpow_of_norm_fderiv_le_rpow hα1 h0
    (fun z hz hz0 ↦ (hbd z hz hz0).1) (fun z hz hz0 ↦ (hbd z hz hz0).2.1)
    (fun z hz hz0 ↦ (hbd z hz hz0).2.2)⟩

/-- **`C^{1,α}` regularity across the puncture.** A punctured symbol of order `ℓ` which vanishes
at `0` is `C¹` on a ball about `0`, with `α`-Hölder derivative, for every exponent
`0 < α ≤ 1` with `α + 1 ≤ ℓ`. For `ℓ ≥ 2` this applies with `α = 1`: the derivative is Lipschitz
on the ball, so the symbol is `C^{1,1}` there. -/
theorem exists_contDiffOn_holderOnWith_fderiv (hf : IsPuncturedSymbol ℓ f) {α : ℝ≥0}
    (hα : 0 < α) (hαℓ : (α : ℝ) + 1 ≤ ℓ) (hα1 : α ≤ 1) (h0 : f 0 = 0) :
    ∃ r > 0, ContDiffOn ℝ 1 f (Metric.ball (0 : E) r) ∧
      ∃ C : ℝ≥0, HolderOnWith C α (fderiv ℝ f) (Metric.ball (0 : E) r) := by
  have hα' : (0 : ℝ) < α := hα
  obtain ⟨C, r₁, hr₁, hC⟩ := hf.fderiv.exists_holderOnWith (by linarith) hα1
    (hf.hasFDerivAt (by linarith) h0).fderiv
  obtain ⟨r₂, hr₂, hr₂f⟩ := Metric.eventually_nhds_iff_ball.1
    (hf.eventually_nhds_contDiffAt (k := 1) (by push_cast; linarith) h0)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun z hz ↦ ?_, C,
    hC.mono (Metric.ball_subset_ball (min_le_left _ _))⟩
  exact (hr₂f z (Metric.ball_subset_ball (min_le_right _ _) hz)).contDiffWithinAt

end IsPuncturedSymbol

end Removable

end TauCeti
