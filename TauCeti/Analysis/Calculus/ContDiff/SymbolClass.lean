/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear
import TauCeti.Analysis.Calculus.ContDiffZPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Symbol classes at a puncture

A map `f` from a real normed space `E` is a **punctured symbol of order `ℓ`**
(`TauCeti.IsPuncturedSymbol ℓ f`) when it is smooth on a punctured neighbourhood of `0` and,
for every `j`, its `j`-th derivative is `O(‖z‖ ^ (ℓ - j))` as `z → 0`, `z ≠ 0`. On the punctured
disc these are the functions behaving like a homogeneous function of degree `ℓ` together with
all their derivatives: on `ℂ`, `z ↦ z ^ k` has order `k` for every integer `k`
(`TauCeti.isPuncturedSymbol_zpow`). No smoothness at `0` itself is required, and the order is
any real number.

These classes are the bookkeeping device of the local analysis of pseudoholomorphic curves
near a critical point or a point of intersection, where one keeps track of the order of
vanishing of coefficients through products, derivatives, inverses and changes of coordinates.
This file proves that they form a graded calculus:

* sums, constant multiples, linear images and restrictions to smaller orders
  (`IsPuncturedSymbol.add`, `IsPuncturedSymbol.const_smul`,
  `IsPuncturedSymbol.continuousLinearMap_comp`, `IsPuncturedSymbol.mono`), with constants of
  order `0` (`TauCeti.isPuncturedSymbol_const`) and continuous linear maps of order `1`
  (`ContinuousLinearMap.isPuncturedSymbol`);
* **products add orders**: for a continuous bilinear map `B`, if `f` has order `ℓ` and `g` has
  order `m`, then `z ↦ B (f z) (g z)` has order `ℓ + m` (`IsPuncturedSymbol.bilinear`, with the
  special cases `IsPuncturedSymbol.smul`, `IsPuncturedSymbol.mul` and `IsPuncturedSymbol.pow`);
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

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix E (the Micallef–White theorem on the local
  behaviour of pseudoholomorphic curves, whose proof tracks functions on the punctured disc by
  derivative bounds of this kind).
-/

public section

open Set Filter Asymptotics
open scoped Topology ContDiff

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

/-- On a punctured neighbourhood, powers of the norm multiply by adding exponents. -/
private theorem rpow_mul_rpow_eventuallyEq (a b : ℝ) :
    (fun z : E ↦ ‖z‖ ^ a * ‖z‖ ^ b) =ᶠ[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (a + b) := by
  filter_upwards [eventually_norm_pos] with z hz
  rw [Real.rpow_add hz]

/-- The exponents in the Leibniz rule for punctured derivative bounds add up: the product of the
bounds of orders `i` and `n - i` for symbols of orders `ℓ` and `m` is the bound of order `n` for
order `ℓ + m`. -/
private theorem isBigO_rpow_mul_rpow (ℓ m : ℝ) {n i : ℕ} (hi : i ≤ n) :
    (fun z : E ↦ ‖z‖ ^ (ℓ - i) * ‖z‖ ^ (m - (n - i : ℕ))) =O[𝓝[≠] (0 : E)]
      fun z ↦ ‖z‖ ^ (ℓ + m - n) := by
  refine ((rpow_mul_rpow_eventuallyEq _ _).trans (Eventually.of_forall fun z ↦ ?_)).isBigO
  push_cast [Nat.cast_sub hi]
  ring_nf

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]

/-- A map `f` is a **punctured symbol of order `ℓ`** at `0` if it is smooth on a punctured
neighbourhood of `0` and its `j`-th derivative is `O(‖z‖ ^ (ℓ - j))` as `z → 0` with `z ≠ 0`, for
every `j`. Nothing is asked of `f` at `0` itself. -/
def IsPuncturedSymbol (ℓ : ℝ) (f : E → F) : Prop :=
  (∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z) ∧
    ∀ j : ℕ, iteratedFDeriv ℝ j f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j)

/-- The defining properties of a punctured symbol: smoothness on a punctured neighbourhood of `0`
and the bounds `D^j f = O(‖z‖ ^ (ℓ - j))` for every `j`. -/
theorem isPuncturedSymbol_iff {ℓ : ℝ} {f : E → F} :
    IsPuncturedSymbol ℓ f ↔ (∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z) ∧
      ∀ j : ℕ, iteratedFDeriv ℝ j f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j) :=
  Iff.rfl

/-- The inductive step of the derivative bounds for linear maps, inverses and compositions: if
`fderiv F'` agrees near every point of a punctured neighbourhood with a map `G'` whose `k`-th
derivative is `O(‖z‖ ^ (a - k))`, then the `(k + 1)`-th derivative of `F'` is
`O(‖z‖ ^ (b - (k + 1)))` for `b = a + 1`. -/
private theorem isBigO_iteratedFDeriv_succ_of_eventuallyEq {F' : E → F} {G' : E → E →L[ℝ] F}
    {a b : ℝ} {k : ℕ} (hF : ∀ᶠ z in 𝓝[≠] (0 : E), fderiv ℝ F' =ᶠ[𝓝 z] G')
    (hG : iteratedFDeriv ℝ k G' =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (a - k)) (hab : a + 1 = b) :
    iteratedFDeriv ℝ (k + 1) F' =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (b - (k + 1 : ℕ)) := by
  subst hab
  refine IsBigO.of_norm_left (hG.norm_left.congr' ?_ (Eventually.of_forall fun z ↦ ?_))
  · filter_upwards [hF] with z hz
    rw [← (hz.iteratedFDeriv ℝ k).eq_of_nhds, norm_iteratedFDeriv_fderiv]
  · push_cast
    ring_nf

/-! ### Basic properties -/

namespace IsPuncturedSymbol

variable {ℓ m : ℝ} {f f₁ : E → F} {g : E → G}

/-- A punctured symbol is smooth on a punctured neighbourhood of `0`. -/
theorem eventually_contDiffAt (hf : IsPuncturedSymbol ℓ f) :
    ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z :=
  hf.1

/-- The `j`-th derivative of a punctured symbol of order `ℓ` is `O(‖z‖ ^ (ℓ - j))`. -/
theorem isBigO_iteratedFDeriv (hf : IsPuncturedSymbol ℓ f) (j : ℕ) :
    iteratedFDeriv ℝ j f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - j) :=
  hf.2 j

/-- A punctured symbol of order `ℓ` is `O(‖z‖ ^ ℓ)` near `0`. -/
theorem isBigO (hf : IsPuncturedSymbol ℓ f) : f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ ℓ := by
  have h := (hf.2 0).norm_left
  simp only [norm_iteratedFDeriv_zero, CharP.cast_eq_zero, sub_zero] at h
  exact h.of_norm_left

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
  refine ⟨?_, fun j ↦ (hf.2 j).congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1, hloc] with z hz hz'
    exact hz.congr_of_eventuallyEq hz'.symm
  · filter_upwards [hloc] with z hz
    exact (hz.iteratedFDeriv ℝ j).eq_of_nhds

/-- A punctured symbol of order `ℓ` has every smaller order. -/
theorem mono (hf : IsPuncturedSymbol ℓ f) (h : m ≤ ℓ) : IsPuncturedSymbol m f := by
  refine ⟨hf.1, fun j ↦ (hf.2 j).trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [eventually_norm_pos, eventually_norm_le_one] with z hz hz1
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_ge hz hz1 (by linarith)

/-- The sum of two punctured symbols of order `ℓ` has order `ℓ`. -/
theorem add (hf : IsPuncturedSymbol ℓ f) (hf₁ : IsPuncturedSymbol ℓ f₁) :
    IsPuncturedSymbol ℓ fun z ↦ f z + f₁ z := by
  refine ⟨?_, fun j ↦ ((hf.2 j).add (hf₁.2 j)).congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1, hf₁.1] with z hz hz₁
    exact hz.add hz₁
  · filter_upwards [hf.1, hf₁.1] with z hz hz₁
    exact (iteratedFDeriv_add_apply (hz.of_le (by exact_mod_cast le_top))
      (hz₁.of_le (by exact_mod_cast le_top))).symm

/-- The negative of a punctured symbol of order `ℓ` has order `ℓ`. -/
theorem neg (hf : IsPuncturedSymbol ℓ f) : IsPuncturedSymbol ℓ fun z ↦ -f z := by
  refine ⟨?_, fun j ↦ (hf.2 j).neg_left.congr' ?_ EventuallyEq.rfl⟩
  · filter_upwards [hf.1] with z hz
    exact hz.neg
  · exact Eventually.of_forall fun z ↦ (iteratedFDeriv_neg_apply (f := f)).symm

/-- The difference of two punctured symbols of order `ℓ` has order `ℓ`. -/
theorem sub (hf : IsPuncturedSymbol ℓ f) (hf₁ : IsPuncturedSymbol ℓ f₁) :
    IsPuncturedSymbol ℓ fun z ↦ f z - f₁ z := by
  simpa [sub_eq_add_neg] using hf.add hf₁.neg

/-- The image of a punctured symbol under a continuous linear map is a punctured symbol of the
same order. -/
theorem continuousLinearMap_comp (hf : IsPuncturedSymbol ℓ f) (L : F →L[ℝ] G) :
    IsPuncturedSymbol ℓ fun z ↦ L (f z) := by
  refine ⟨?_, fun j ↦ (IsBigO.of_bound ‖L‖ ?_).trans (hf.2 j)⟩
  · filter_upwards [hf.1] with z hz
    exact L.contDiff.contDiffAt.comp z hz
  · filter_upwards [hf.1] with z hz
    exact L.norm_iteratedFDeriv_comp_left (f := f) hz (by exact_mod_cast le_top)

/-- Differentiation lowers the order of a punctured symbol by one. -/
protected theorem fderiv (hf : IsPuncturedSymbol ℓ f) :
    IsPuncturedSymbol (ℓ - 1) (fderiv ℝ f) := by
  refine ⟨?_, fun j ↦ ?_⟩
  · filter_upwards [hf.1] with z hz
    exact hz.fderiv_right (m := ∞) le_rfl
  · have h := (hf.2 (j + 1)).norm_left
    simp_rw [← norm_iteratedFDeriv_fderiv (n := j)] at h
    refine h.of_norm_left.congr' EventuallyEq.rfl (Eventually.of_forall fun z ↦ ?_)
    push_cast
    ring_nf

end IsPuncturedSymbol

/-- A constant map is a punctured symbol of order `0`. -/
theorem isPuncturedSymbol_const (c : F) : IsPuncturedSymbol 0 fun _ : E ↦ c := by
  refine ⟨Eventually.of_forall fun _ ↦ contDiffAt_const, fun j ↦ ?_⟩
  rcases eq_or_ne j 0 with rfl | hj
  · refine IsBigO.of_bound ‖c‖ (Eventually.of_forall fun z ↦ ?_)
    simp
  · rw [iteratedFDeriv_const_of_ne hj]
    exact isBigO_zero _ _

/-- The zero map is a punctured symbol of every order. -/
theorem isPuncturedSymbol_zero (ℓ : ℝ) : IsPuncturedSymbol ℓ fun _ : E ↦ (0 : F) :=
  ⟨Eventually.of_forall fun _ ↦ contDiffAt_const, fun j ↦ by
    rw [iteratedFDeriv_fun_zero]
    exact isBigO_zero _ _⟩

/-- A continuous linear map is a punctured symbol of order `1`. -/
theorem _root_.ContinuousLinearMap.isPuncturedSymbol (L : E →L[ℝ] F) :
    IsPuncturedSymbol 1 L := by
  refine ⟨Eventually.of_forall fun _ ↦ L.contDiff.contDiffAt, fun j ↦ ?_⟩
  cases j with
  | zero =>
    refine IsBigO.of_bound ‖L‖ (Eventually.of_forall fun z ↦ ?_)
    simpa using L.le_opNorm z
  | succ j =>
    exact isBigO_iteratedFDeriv_succ_of_eventuallyEq (G' := fun _ ↦ L)
      (Eventually.of_forall fun _ ↦ .of_forall fun _ ↦ L.fderiv)
      ((isPuncturedSymbol_const L).2 j) (by ring)

/-- The identity is a punctured symbol of order `1`. -/
theorem isPuncturedSymbol_id : IsPuncturedSymbol 1 fun z : E ↦ z :=
  (ContinuousLinearMap.id ℝ E).isPuncturedSymbol

/-! ### Products -/

/-- The product rule for punctured derivative bounds at a fixed derivative order `n`, from the
bounds of the two factors at the orders at most `n`. -/
private theorem isBigO_iteratedFDeriv_bilinear (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z)
    (hg : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ g z) {ℓ m : ℝ} {n : ℕ}
    (hfn : ∀ i ≤ n, iteratedFDeriv ℝ i f =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (ℓ - i))
    (hgn : ∀ i ≤ n, iteratedFDeriv ℝ i g =O[𝓝[≠] (0 : E)] fun z ↦ ‖z‖ ^ (m - i)) :
    iteratedFDeriv ℝ n (fun z ↦ B (f z) (g z)) =O[𝓝[≠] (0 : E)]
      fun z ↦ ‖z‖ ^ (ℓ + m - n) :=
  B.isBigO_iteratedFDeriv_of_bilinear_of_contDiffAt (ρ₁ := fun i z ↦ ‖z‖ ^ (ℓ - i))
    (ρ₂ := fun i z ↦ ‖z‖ ^ (m - i)) hf hg (by exact_mod_cast le_top) hfn hgn
    fun _ hi ↦ isBigO_rpow_mul_rpow ℓ m hi

namespace IsPuncturedSymbol

variable {ℓ m : ℝ} {f : E → F} {g : E → G}

/-- **Products of punctured symbols add their orders.** For a continuous bilinear map `B`, if `f`
has order `ℓ` and `g` has order `m`, then `z ↦ B (f z) (g z)` has order `ℓ + m`. -/
theorem bilinear (hf : IsPuncturedSymbol ℓ f) (hg : IsPuncturedSymbol m g)
    (B : F →L[ℝ] G →L[ℝ] H) : IsPuncturedSymbol (ℓ + m) fun z ↦ B (f z) (g z) :=
  ⟨(hf.1.and hg.1).mono fun _ hz ↦ B.isBoundedBilinearMap.contDiff.comp₂_contDiffAt hz.1 hz.2,
    fun _ ↦ isBigO_iteratedFDeriv_bilinear B hf.1 hg.1 (fun i _ ↦ hf.2 i) (fun i _ ↦ hg.2 i)⟩

/-- A scalar punctured symbol of order `ℓ` times a vector punctured symbol of order `m` is a
punctured symbol of order `ℓ + m`. -/
theorem smul {𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 G] [IsBoundedSMul 𝕜 G]
    [IsScalarTower ℝ 𝕜 G] {a : E → 𝕜} (ha : IsPuncturedSymbol ℓ a) (hg : IsPuncturedSymbol m g) :
    IsPuncturedSymbol (ℓ + m) fun z ↦ a z • g z :=
  ha.bilinear hg (ContinuousLinearMap.lsmul ℝ 𝕜)

/-- A constant multiple of a punctured symbol of order `ℓ` has order `ℓ`. -/
theorem const_smul {𝕜 : Type*} [NormedRing 𝕜] [NormedAlgebra ℝ 𝕜] [Module 𝕜 G]
    [IsBoundedSMul 𝕜 G] [IsScalarTower ℝ 𝕜 G] (hg : IsPuncturedSymbol ℓ g) (a : 𝕜) :
    IsPuncturedSymbol ℓ fun z ↦ a • g z := by
  simpa using (isPuncturedSymbol_const a).smul hg

/-- Products of punctured symbols with values in a normed algebra add their orders. -/
theorem mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {a b : E → A}
    (ha : IsPuncturedSymbol ℓ a) (hb : IsPuncturedSymbol m b) :
    IsPuncturedSymbol (ℓ + m) fun z ↦ a z * b z :=
  ha.bilinear hb (ContinuousLinearMap.mul ℝ A)

/-- The `k`-th power of a punctured symbol of order `ℓ` has order `k * ℓ`. -/
theorem pow {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {a : E → A}
    (ha : IsPuncturedSymbol ℓ a) (k : ℕ) : IsPuncturedSymbol (k * ℓ) fun z ↦ a z ^ k := by
  induction k with
  | zero =>
    simpa using isPuncturedSymbol_const (E := E) (1 : A)
  | succ k ih =>
    simpa [pow_succ, add_mul] using ih.mul ha

end IsPuncturedSymbol

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
      have hprod := isBigO_iteratedFDeriv_bilinear (-ContinuousLinearMap.compL ℝ E R R) hgg hDf.1
        (n := k) (ℓ := -ℓ + -ℓ) (m := ℓ - 1)
        (fun i hi ↦ isBigO_iteratedFDeriv_bilinear (ContinuousLinearMap.mulLeftRight ℝ R) hg hg
          (fun j hj ↦ ih j (hj.trans (hi.trans hk))) (fun j hj ↦ ih j (hj.trans (hi.trans hk))))
        (fun i _ ↦ hDf.2 i)
      exact isBigO_iteratedFDeriv_succ_of_eventuallyEq (eventually_fderiv_inv_eventuallyEq hne)
        hprod (by ring)

/-- **The inverse of a punctured symbol.** If `f` has order `ℓ`, with values in a normed
division algebra, and `‖f z‖ ≥ c ‖z‖ ^ ℓ` near `0` for some `c > 0`, then `z ↦ (f z)⁻¹` is a
punctured symbol of order `-ℓ`. -/
theorem IsPuncturedSymbol.inv (hf : IsPuncturedSymbol ℓ f) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ^ ℓ ≤ ‖f z‖) :
    IsPuncturedSymbol (-ℓ) fun z ↦ (f z)⁻¹ := by
  have hne : ∀ᶠ z in 𝓝[≠] (0 : E), ContDiffAt ℝ ∞ f z ∧ f z ≠ 0 := by
    filter_upwards [hf.1, hlow, eventually_norm_pos] with z hfz hz hz0
    exact ⟨hfz, norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hz)⟩
  exact ⟨eventually_contDiffAt_inv hne, fun j ↦ isBigO_iteratedFDeriv_inv hf hc hlow hne j j le_rfl⟩

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
  rw [fderiv_fun_comp y hgd (hy.2.differentiableAt (by simp))]
  simp [iteratedFDeriv_succ_eq_comp_left]

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
    have h := ((hg.2 j).comp_tendsto hφ0).norm_left.trans
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
      have hprod := isBigO_iteratedFDeriv_bilinear
        (H := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)
        ((ContinuousLinearMap.compL ℝ E F (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ F) G)).comp
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ F)
            G).toContinuousLinearEquiv.toContinuousLinearMap) hDj hDφ.1 (n := k)
        (ℓ := ℓ - (j + 1 : ℕ)) (m := 1 - 1)
        (fun i hi ↦ ih (j + 1) i (hi.trans hk)) (fun i _ ↦ hDφ.2 i)
      exact isBigO_iteratedFDeriv_succ_of_eventuallyEq (eventually_fderiv_comp_eventuallyEq hs j)
        hprod (by push_cast; ring)

/-- **Composition with a reparametrization.** If `g` is a punctured symbol of order `ℓ` and
`φ` is a punctured symbol of order `1` with `‖φ z‖ ≥ c ‖z‖` near `0` for some `c > 0`, then
`g ∘ φ` is a punctured symbol of order `ℓ`. -/
theorem IsPuncturedSymbol.comp (hg : IsPuncturedSymbol ℓ g) (hφ : IsPuncturedSymbol 1 φ) {c : ℝ}
    (hc : 0 < c) (hlow : ∀ᶠ z in 𝓝[≠] (0 : E), c * ‖z‖ ≤ ‖φ z‖) :
    IsPuncturedSymbol ℓ fun z ↦ g (φ z) := by
  refine ⟨?_, fun j ↦ ?_⟩
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

end TauCeti
