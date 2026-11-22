/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.MetricSpace.Holder
public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Basic
import TauCeti.Analysis.Calculus.ContDiffZPow
import TauCeti.Analysis.Calculus.ContDiff.Puncture
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.Holder.MeanValue

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
  order `1` with `‖φ z‖ ≥ c ‖z‖`, then `g ∘ φ` has order `ℓ` (`IsPuncturedSymbol.comp`).

The last two are proved by induction on the order of the derivative: the derivative of
`(f z)⁻¹` is a bilinear expression in `(f z)⁻¹`, `(f z)⁻¹` and `Df z`, and the derivative of
`(D^j g) ∘ φ` is a bilinear expression in `(D^{j+1} g) ∘ φ` and `Dφ`, so the product rule at
lower derivative orders controls the next order.

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
  and_congr_right' <| forall_congr' fun _ ↦ forall_prop_of_true le_top

/-! ### Basic properties -/

namespace IsPuncturedSymbol

variable {ℓ m : ℝ} {f f₁ : E → F}

/-- The `j`-th derivative of a punctured symbol of order `ℓ` is `O(‖z‖ ^ (ℓ - j))`. -/
theorem isBigO_iteratedFDeriv (hf : IsPuncturedSymbol ℓ f) (j : ℕ) :
    iteratedFDeriv ℝ j f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j) :=
  hf.2 j le_top

/-- A punctured symbol of positive order tends to `0` at the puncture. -/
theorem tendsto_zero (hf : IsPuncturedSymbol ℓ f) (hℓ : 0 < ℓ) :
    Tendsto f (𝓝[≠] (0 : E)) (𝓝 0) := by
  refine hf.isBigO.trans_tendsto ?_
  have hc : ContinuousAt (fun z : E ↦ ‖z‖ ^ ℓ) 0 :=
    (continuous_norm.rpow_const fun _ ↦ Or.inr hℓ.le).continuousAt
  simpa [Real.zero_rpow hℓ.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- Being a punctured symbol only depends on the map on a punctured neighbourhood of `0`. -/
theorem congr (hf : IsPuncturedSymbol ℓ f) (h : f =ᶠ[𝓝[≠] (0 : E)] f₁) :
    IsPuncturedSymbol ℓ f₁ := by
  have hloc : ∀ᶠ z in 𝓝[≠] (0 : E), f =ᶠ[𝓝 z] f₁ :=
    (eventually_nhdsWithin_eventually_nhds_iff_of_isOpen isOpen_compl_singleton).2 h
  refine ⟨?_, fun j hj ↦ (hf.2 j hj).congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1, hloc] with z hz hz'
    exact hz.congr_of_eventuallyEq hz'.symm
  · filter_upwards [hloc] with z hz
    exact (hz.iteratedFDeriv ℝ j).eq_of_nhds

/-- A punctured symbol of order `ℓ` has every smaller order. -/
theorem mono (hf : IsPuncturedSymbol ℓ f) (h : m ≤ ℓ) : IsPuncturedSymbol m f := by
  refine ⟨hf.1, fun j hj ↦ (hf.2 j hj).trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_norm_pos, eventually_norm_le_one] with z hz hz1
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_ge hz hz1 (by linarith)

/-- Differentiation lowers the order of a punctured symbol by one. -/
protected theorem fderiv (hf : IsPuncturedSymbol ℓ f) :
    IsPuncturedSymbol (ℓ - 1) (fderiv ℝ f) :=
  IsSymbolAlong.fderiv (n := ⊤) (by rwa [top_add])

end IsPuncturedSymbol

/-- A continuous linear map is a punctured symbol of order `1`. -/
theorem _root_.ContinuousLinearMap.isPuncturedSymbol (L : E →L[ℝ] F) :
    IsPuncturedSymbol 1 L := by
  refine ⟨Eventually.of_forall fun _ ↦ L.contDiff.contDiffAt, fun j _ ↦ ?_⟩
  cases j with
  | zero =>
    refine IsBigO.of_bound ‖L‖ (Eventually.of_forall fun z ↦ ?_)
    simpa using L.le_opNorm z
  | succ j =>
    exact isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq (g := fun _ ↦ L)
      (Eventually.of_forall fun _ ↦ .of_forall fun _ ↦ L.fderiv)
      ((isSymbolAlong_const (n := ⊤) L).2 j le_top) (by ring)

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
        hgg hDf.1 (n := k) (ℓ := -ℓ + -ℓ) (m := ℓ - 1) (by exact_mod_cast le_top)
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
    filter_upwards [hf.1, hlow, eventually_norm_pos] with z hfz hz hz0
    exact ⟨hfz, norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hz)⟩
  exact ⟨eventually_contDiffAt_inv hne,
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

/-- The derivative bounds of `(D^j g) ∘ φ`, for all `j` at once, by induction on the derivative
order: the derivative of `(D^j g) ∘ φ` is a bilinear expression in `(D^{j+1} g) ∘ φ` and `Dφ`. -/
private theorem isBigO_iteratedFDeriv_comp (hg : IsPuncturedSymbol ℓ g)
    (hφ : IsPuncturedSymbol 1 φ) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ≤ ‖φ z‖) (n : ℕ) :
    ∀ j : ℕ, ∀ i ≤ n, iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j g (φ z))
      =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j - i) := by
  have hφ0 := tendsto_nhdsNE_of_le hφ hc hlow
  have hs : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g (φ z) ∧ ContDiffAt ℝ ∞ φ z :=
    (hφ0.eventually hg.1).and hφ.1
  have hDφ := hφ.fderiv
  induction n with
  | zero =>
    intro j i hi
    obtain rfl : i = 0 := Nat.le_zero.1 hi
    have hθ : (fun z ↦ ‖φ z‖) =Θ[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ := by
      refine ⟨hφ.isBigO.norm_left.congr' EventuallyEq.rfl
        (Eventually.of_forall fun z ↦ Real.rpow_one _), IsBigO.of_bound c⁻¹ ?_⟩
      filter_upwards [hlow] with z hz
      simpa only [norm_norm, le_inv_mul_iff₀ hc] using hz
    have h := ((hg.isBigO_iteratedFDeriv j).comp_tendsto hφ0).norm_left.trans
      (hθ.rpow (r := ℓ - j) (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (Eventually.of_forall fun _ ↦ norm_nonneg _)).isBigO
    refine IsBigO.of_norm_left (h.congr' (Eventually.of_forall fun z ↦ ?_)
      (Eventually.of_forall fun z ↦ ?_))
    · simp [norm_iteratedFDeriv_zero]
    · simp
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
        (H := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)
        ((ContinuousLinearMap.compL ℝ E F (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)).comp
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ F)
            G).toContinuousLinearEquiv.toContinuousLinearMap) hDj hDφ.1 (n := k)
        (ℓ := ℓ - (j + 1 : ℕ)) (m := 1 - 1) (by exact_mod_cast le_top)
        (fun i hi ↦ ih (j + 1) i (hi.trans hk)) (fun i _ ↦ hDφ.isBigO_iteratedFDeriv i)
      exact isBigO_iteratedFDeriv_succ_rpow_of_eventuallyEq
        (eventually_fderiv_comp_eventuallyEq hs j) hprod (by push_cast; ring)

/-- **Composition with a reparametrization.** If `g` is a punctured symbol of order `ℓ` and
`φ` is a punctured symbol of order `1` with `‖φ z‖ ≥ c ‖z‖` near `0` for some `c > 0`, then
`g ∘ φ` is a punctured symbol of order `ℓ`. -/
theorem IsPuncturedSymbol.comp (hg : IsPuncturedSymbol ℓ g) (hφ : IsPuncturedSymbol 1 φ) {c : ℝ}
    (hc : 0 < c) (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ≤ ‖φ z‖) :
    IsPuncturedSymbol ℓ fun z ↦ g (φ z) := by
  refine ⟨?_, fun j _ ↦ ?_⟩
  · filter_upwards [(tendsto_nhdsNE_of_le hφ hc hlow).eventually hg.1, hφ.1] with z hgz hz
    exact hgz.comp z hz
  · -- `D^0 g ∘ φ` is `g ∘ φ` read through the isometry `G ≃ (Fin 0 → F) → G`.
    have heq : (fun z ↦ iteratedFDeriv ℝ 0 g (φ z)) =
        (continuousMultilinearCurryFin0 ℝ F G).symm ∘ fun z ↦ g (φ z) := by
      funext z
      simp [iteratedFDeriv_zero_eq_comp]
    have h := (isBigO_iteratedFDeriv_comp hg hφ hc hlow j 0 j le_rfl).norm_left
    rw [heq] at h
    simp_rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left] at h
    exact h.of_norm_left.congr' EventuallyEq.rfl (Eventually.of_forall fun z ↦ by simp)

end Composition

/-! ### Removability at the puncture -/

section Removable

namespace IsPuncturedSymbol

variable {ℓ : ℝ} {f : E → F}

/-- Points near `0` other than `0` itself are points of smoothness of a punctured symbol, read on
the full neighbourhood filter. -/
private theorem eventually_nhds_contDiffAt_of_ne (hf : IsPuncturedSymbol ℓ f) :
    ∀ᶠ z in 𝓝 (0 : E), z ≠ 0 → ContDiffAt ℝ ∞ f z :=
  eventually_nhdsWithin_iff.1 hf.1

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
  have h := hf.1.and (hAf.bound.and hBf.bound)
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
