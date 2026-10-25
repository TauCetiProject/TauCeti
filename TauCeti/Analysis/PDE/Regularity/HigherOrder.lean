/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DifferentiatedEquation
public import TauCeti.Analysis.PDE.Regularity.Interior
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Wkp.Leibniz

/-!
# Interior `Hᵏ` regularity

Let `a` be a uniformly elliptic coefficient field on `Ω` whose entries are smooth on `Ω`, and let
`u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, with `f ∈ W^{k,2}(Ω)`,

meaning `∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`
and nothing assumed about `∂Ω`. This file proves that `u ∈ H^{k+2}_loc(Ω)`: on every open `V`
whose closure is compact and contained in `Ω`, the restriction of `u` is the value of an element
of `W^{k+2,2}(V)`. Each derivative of the data buys one more derivative of the solution, so
smooth data give a solution in every `H^m_loc(Ω)`. A constant matrix `A` is the special case
`TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL`.

## Differentiating the equation

The induction on `k` rests on differentiating the equation. When `A` is constant, a weak
derivative of a weak solution is again a weak solution, with the derivative of the data as
right-hand side. If `u` solves `-div(A ∇u) = f`, `∂ₑu ∈ H¹(Ω)` and `∂ₑf ∈ L²(Ω)`, then `∂ₑu`
solves `-div(A ∇(∂ₑu)) = ∂ₑf` (`TauCeti.PDE.energyFormH1_eq_setIntegral_of_hasWeakLineDerivOn`).
Since weak derivatives commute (`TauCeti.HasWeakLineDerivOn.comm`), the derivative `∂ₑ` moves
from `∂ⱼ(∂ₑu)` onto the test function, so `a(∂ₑu, φ) = -a(u, ∂ₑφ) = -∫ f ∂ₑφ = ∫ (∂ₑf) φ`.

For a variable field the derivative also falls on `a`, and `∂ₑu` solves
`-∂ᵢ(aⁱʲ ∂ⱼ(∂ₑu)) = ∂ₑf + ∑ᵢⱼ (∂ᵢ∂ₑaⁱʲ ∂ⱼu + ∂ₑaⁱʲ ∂ᵢ∂ⱼu)`
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn`). On a set `Ω`
with compact closure inside the open set where `a` is smooth, multiplication by the derivatives
of `a` preserves `W^{k,2}(Ω)` (`TauCeti.Wkp.exists_value_ae_eq_mul_of_contDiffOn`), so for
`u ∈ H^{k+2}(Ω)` and `f ∈ W^{k+1,2}(Ω)` the right-hand side lies in `W^{k,2}(Ω)`
(`TauCeti.PDE.exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_contDiffOn`).

## The induction

The case `k = 0` is interior `H²` regularity for locally Lipschitz coefficients
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn`). For the
step, fix `V` and an open `W` with `closure V ⊆ W` and `closure W` compact in `Ω`. By the
induction hypothesis the solution lies in `H^{k+2}(W)`, so each `∂ᵢu` lies in `H¹(W)` and solves
an equation on `W` with data in `W^{k,2}(W)`. The induction hypothesis again puts `∂ᵢu` in
`W^{k+2,2}(V)` for every `i`, and a function whose first weak derivatives lie in `W^{k+2,2}(V)`
lies in `W^{k+3,2}(V)` (`TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn`).

## Main declarations

* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn`: a weak derivative
  moves from the solution to the test function across the constant-coefficient energy form.
* `TauCeti.PDE.energyFormH1_eq_setIntegral_of_hasWeakLineDerivOn`: a weak derivative of a weak
  solution of a constant-coefficient equation solves the differentiated equation.
* `TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_energyFormH1_eq_neg_setIntegral`:
  for `L²` data, each first derivative of a weak solution lies in `H¹` on compactly contained open
  sets and solves the equation with the distributional derivative of the data.
* `TauCeti.PDE.exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_contDiffOn`: for
  smooth coefficients, `u ∈ H^{k+2}` and data in `W^{k+1,2}`, each first derivative of a weak
  solution solves an equation with data in `W^{k,2}`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn`: interior
  `H^{k+2}` regularity for smooth coefficients and data in `W^{k,2}`.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL`: its constant-coefficient
  case.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 2 (higher interior regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.10.
-/

public section

noncomputable section

open LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal Gradient InnerProductSpace Matrix

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {A : Matrix ι ι ℝ}

/-! ### Differentiating the equation -/

/-- **A derivative moves across the constant-coefficient energy form.** Let `A` be a constant
matrix and `a(u, v) = ∫_Ω ⟨∇v, A ∇u⟩`. If `u, d ∈ H¹(Ω)` and `d` is the weak derivative of `u`
in a direction `e`, then `a(d, φ) = -a(u, ∂ₑφ)` for every test function `φ` on `Ω`.

No ellipticity is needed. This is the case `∂ₑA = 0` of
`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn`. -/
theorem energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn {u d : W1p mu Omega 2}
    {e : EuclideanSpace ℝ ι} (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e)
    (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => A) 0 0 d (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 (∂_{e} φ)) := by
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn (a := fun _ => A)
    (fun i j => contDiffOn_const) hd, sub_eq_self]
  -- The derivative of the constant field vanishes, and so does its energy form.
  have h0 : (fun x => Matrix.of fun i j => fderiv ℝ (fun _ => A i j) x e) = fun _ => 0 := by
    ext x i j
    simp
  rw [h0]
  simp [energyFormH1_zero_zero_eq_setIntegral, matrixBilinearForm_apply]

/-- **A weak derivative of a weak solution is a weak solution.** Let `A` be a constant matrix and
let `u ∈ H¹(Ω)` satisfy `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, where
`a(u, v) = ∫_Ω ⟨∇v, A ∇u⟩`. If, in a direction `e`, `u` has a weak derivative `∂ₑu ∈ H¹(Ω)` and
`f` has a weak derivative `∂ₑf ∈ L²(Ω)`, then `a(∂ₑu, v) = ∫_Ω (∂ₑf) v` for every
`v ∈ H¹₀(Ω)`: the derivative `∂ₑu` solves `-div(A ∇(∂ₑu)) = ∂ₑf` in `Ω`.

No ellipticity is needed, and no boundary condition is imposed on `u`. -/
theorem energyFormH1_eq_setIntegral_of_hasWeakLineDerivOn {f g : Lp ℝ 2 (mu.restrict Omega)}
    {u d : W1p mu Omega 2} {e : EuclideanSpace ℝ ι}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e)
    (hf : HasWeakLineDerivOn mu Omega f g e) (v : W1p0 mu Omega 2) :
    energyFormH1 (fun _ => A) 0 0 d (v : W1p mu Omega 2) =
      ∫ x in Omega, g x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  have hcoeff : MemLp (fun x => energyIntegrand ((fun _ => A) x)
      ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x) ((0 : EuclideanSpace ℝ ι → ℝ) x)) ⊤
      (mu.restrict Omega) := by
    simpa using memLp_top_const (μ := mu.restrict Omega) (energyIntegrand A 0 0)
  have hu' := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff f u).1 hu
  refine (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff g d).2 (fun φ => ?_) v
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn hd, hu' (∂_{e} φ)]
  -- `-∫ f ∂ₑφ = ∫ (∂ₑf) φ` is the definition of the weak derivative of `f`.
  have hfφ := hf.integral_lineDeriv_smul_eq_neg_integral_smul φ
  rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
    ← setIntegral_smul_eq_integral_smul] at hfφ
  simp only [TestFunction.lineDerivOp_apply, smul_eq_mul] at hfφ ⊢
  rw [neg_eq_iff_eq_neg]
  simpa only [mul_comm] using hfφ

/-- **The derivative of a weak solution with `L²` data.** Let `A` be a constant, uniformly
elliptic matrix, `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(Aⁱʲ ∂ⱼu) = f` in
`Ω`, in the sense that `∫_Ω ⟨∇v, A ∇u⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. Let `V` be open with
compact closure contained in `Ω`. Then in every direction `e` the weak derivative `∂ₑu` lies in
`H¹(V)` and satisfies `∫_V ⟨∇φ, A ∇∂ₑu⟩ = -∫_V f ∂ₑφ` for every test function `φ` on `V`: it is
a weak solution of `-∂ᵢ(Aⁱʲ ∂ⱼ∂ₑu) = ∂ₑf` in `V`, with the derivative of the data taken in the
sense of distributions.

No regularity of `f` beyond `L²` and no regularity of `∂Ω` is assumed. -/
theorem UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_energyFormH1_eq_neg_setIntegral
    {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ))
    {f : EuclideanSpace ℝ ι → ℝ} (hf : MemLp f 2 (mu.restrict Omega)) {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) (e : EuclideanSpace ℝ ι) :
    ∃ d : W1p mu V 2, HasWeakLineDerivOn mu V (W1p.value u) (W1p.value d) e ∧
      ∀ φ : 𝓓(V, ℝ), energyFormH1 (fun _ => A) 0 0 d (W1p.ofTestFunctionₗ mu V 2 φ) =
        -∫ x in V, f x * lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x e ∂mu := by
  have hVΩ' : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)
  -- Interior `H²` regularity puts `u` in `H²(V)`, so `∂ₑu` lies in `H¹(V)`.
  have hu' : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, hf.toLp f x * W1p.value (v : W1p mu Omega 2) x ∂mu := fun v => by
    rw [hu v]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  obtain ⟨U, hU⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL hlam hA
    MemLp.zero MemLp.zero hu' hV hVΩ
  have hUv : Wkp.value 2 U = W1p.value (W1p.restrictL hVΩ' u) := by
    rw [Wkp.value_succ, Wkp.value_one, hU]
  obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value 1 U e
  rw [hUv, Wkp.value_one] at hd
  refine ⟨d, hd.congr_ae (W1p.value_restrictL_ae hVΩ' u), fun φ => ?_⟩
  -- The derivative moves onto the test function, and `u` solves the equation on `V`.
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn hd,
    energyFormH1_restrictL_eq_setIntegral hVΩ' hu
      ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule (∂_{e} φ)⟩]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [testFunctionLp_apply_ae (mu := mu) 2 (∂_{e} φ)] with x hx
  rw [W1p.value_ofTestFunctionₗ, hx, TestFunction.lineDerivOp_apply]

/-! ### Differentiating the equation with smooth coefficients -/

/-- **The derivative of a weak solution with smooth coefficients.** Let the entries of `a` be
smooth on an open set `U`, let `Ω` have compact closure contained in `U`, let `F ∈ W^{k+1,2}(Ω)`,
and let `u ∈ H^{k+2}(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`, in the sense that
`∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω F v` for every `v ∈ H¹₀(Ω)`. Then in every direction `e` the weak
derivative `∂ₑu` lies in `H¹(Ω)` and is a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼ(∂ₑu)) = G` in `Ω`

for some `G ∈ W^{k,2}(Ω)`. The differentiated equation
(`TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn`) has right-hand
side `∂ₑF + ∑ᵢⱼ (∂ᵢ∂ₑaⁱʲ ∂ⱼu + ∂ₑaⁱʲ ∂ᵢ∂ⱼu)`, which lies in `W^{k,2}(Ω)` because multiplication
by the derivatives of `a` preserves it.

No ellipticity is needed, and no boundary condition is imposed on `u`. -/
theorem exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_contDiffOn
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {U : Set (EuclideanSpace ℝ ι)} (hU : IsOpen U)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) U)
    (hΩ : IsCompact (closure (Omega : Set (EuclideanSpace ℝ ι))))
    (hΩU : closure (Omega : Set (EuclideanSpace ℝ ι)) ⊆ U) (k : ℕ) {F : Wkp mu Omega 2 (k + 1)}
    {u : W1p mu Omega 2} (hw : ∃ w : Wkp mu Omega 2 (k + 2), Wkp.value (k + 2) w = W1p.value u)
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value (k + 1) F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    (e : EuclideanSpace ℝ ι) :
    ∃ (d : W1p mu Omega 2) (G : Wkp mu Omega 2 k),
      HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e ∧
      ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 d (v : W1p mu Omega 2) =
        ∫ x in Omega, Wkp.value k G x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  obtain ⟨w, hw⟩ := hw
  set b := EuclideanSpace.basisFun ι ℝ with hb
  have haΩ : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega := fun i j =>
    (ha i j).mono (subset_closure.trans hΩU)
  -- The energy integrand of `a` is bounded on `Ω`, so the equation may be tested on test functions.
  have hcoeff := memLp_energyIntegrand_of_continuousOn (mu := mu) (b := 0) (c := 0) hΩ
    ((continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (ha i j).continuousOn).mono hΩU)
    continuousOn_const continuousOn_const
  -- The first and second weak derivatives of `u`, from `u ∈ H^{k+2}(Ω)`.
  choose D hD using fun j => Wkp.exists_hasWeakLineDerivOn_value (k + 1) w (b j)
  choose E hE using fun i j => Wkp.exists_hasWeakLineDerivOn_value k (D j) (b i)
  obtain ⟨De, hDe⟩ := Wkp.exists_hasWeakLineDerivOn_value (k + 1) w e
  obtain ⟨Fe, hFe⟩ := Wkp.exists_hasWeakLineDerivOn_value k F e
  rw [hw] at hD hDe
  have hD' : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u)
      (W1p.value (Wkp.firstOrder k (D j))) (b j) := fun j => by
    rw [Wkp.value_firstOrder]; exact hD j
  -- The commutator terms `∂ᵢ∂ₑaⁱʲ ∂ⱼu` and `∂ₑaⁱʲ ∂ᵢ∂ⱼu` lie in `W^{k,2}(Ω)`.
  have hda : ∀ (f : EuclideanSpace ℝ ι → ℝ), ContDiffOn ℝ ∞ f U → ∀ v,
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) U := fun f hf v =>
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  choose M₁ hM₁ using fun i j => Wkp.exists_value_ae_eq_mul_of_contDiffOn hU hΩ hΩU k
    (hda _ (hda _ (ha i j) e) (b i)) (Wkp.lowerOrder k (D j))
  choose M₂ hM₂ using fun i j => Wkp.exists_value_ae_eq_mul_of_contDiffOn hU hΩ hΩU k
    (hda _ (ha i j) e) (E i j)
  have hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (Wkp.firstOrder k De)) e := by
    rw [Wkp.value_firstOrder]; exact hDe
  refine ⟨Wkp.firstOrder k De, Fe + ∑ i, ∑ j, (M₁ i j + M₂ i j), hd, ?_⟩
  -- The differentiated equation, tested on test functions.
  have hut := (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ u).1 hu
  refine (forall_energyFormH1_eq_setIntegral_iff_forall_testFunction hcoeff _ _).2 fun φ => ?_
  rw [energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn haΩ hut hd hD' hFe φ]
  refine integral_congr_ae ?_
  -- Identify the commutator terms with the values of `M₁` and `M₂`.
  have hu₁ : ∀ᵐ x ∂mu.restrict Omega, ∀ i j, Wkp.value k (M₁ i j) x =
      fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y e) x (b i) *
        ⟪W1p.gradient u x, b j⟫_ℝ := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    filter_upwards [hM₁ i j, (hD j).ae_eq ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b j))]
      with x h₁ h₂
    rw [h₁, ← Wkp.value_succ, h₂, innerSL_apply_apply]
  have hu₂ : ∀ᵐ x ∂mu.restrict Omega, ∀ i j, Wkp.value k (M₂ i j) x =
      fderiv ℝ (fun y => a y i j) x e *
        ⟪W1p.gradient (Wkp.firstOrder k (D j)) x, b i⟫_ℝ := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    have h := (W1p.hasWeakFDerivOn (Wkp.firstOrder k (D j))).hasWeakLineDerivOn (b i)
    rw [Wkp.value_firstOrder] at h
    filter_upwards [hM₂ i j, (hE i j).ae_eq h] with x h₁ h₂
    rw [h₁, h₂, innerSL_apply_apply]
  rw [Wkp.value_add]
  filter_upwards [Lp.coeFn_add (Wkp.value k Fe) _,
    Wkp.value_finsetSum_ae k Finset.univ fun i => ∑ j, (M₁ i j + M₂ i j),
    Filter.eventually_all.2 fun i => Wkp.value_finsetSum_ae k Finset.univ fun j => M₁ i j + M₂ i j,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Lp.coeFn_add (Wkp.value k (M₁ i j)) (Wkp.value k (M₂ i j)), hu₁, hu₂]
    with x h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, Pi.add_apply, h₂]
  simp only [h₃, Wkp.value_add, h₄, Pi.add_apply, h₅, h₆, hb]

/-! ### Interior `H^{k+2}` regularity -/

/-- **Interior `H^{k+2}` regularity for smooth coefficients.** Let `a` be uniformly elliptic on
`Ω`, with entries smooth on `Ω`, let `F ∈ W^{k,2}(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = F` in `Ω`,

in the sense that `∫_Ω ⟨∇v, a ∇u⟩ = ∫_Ω F v` for every `v ∈ H¹₀(Ω)`, with no boundary condition
on `u`. Then `u ∈ H^{k+2}_loc(Ω)`: on every open `V` whose closure is compact and contained in
`Ω`, the restriction of `u` is the value of an element of `W^{k+2,2}(V)`.

No regularity of `∂Ω` is assumed, and the derivatives of the coefficients need not be bounded
on `Ω`. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn [DecidableEq ι]
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}
    (ha : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hsmooth : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) Omega) (k : ℕ)
    {F : Wkp mu Omega 2 k} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value k F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp mu V 2 (k + 2), Wkp.value (k + 2) U =
      W1p.value (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u) := by
  induction k generalizing Omega V with
  | zero =>
    obtain ⟨U, hU⟩ := ha.exists_lowerOrder_eq_restrictL_of_locallyLipschitzOn
      (locallyLipschitzOn_matrixBilinearForm_of_contDiffOn Omega.isOpen
        fun i j => (hsmooth i j).of_le (by simp)) MemLp.zero
      MemLp.zero hu hV hVΩ
    exact ⟨U, by rw [Wkp.value_succ, Wkp.value_one, hU]⟩
  | succ k ih =>
    set b := EuclideanSpace.basisFun ι ℝ
    -- An intermediate open set `W` with `closure V ⊆ W` and `closure W` compact in `Ω`.
    obtain ⟨W₀, hW₀, hVW₀, hWΩ₀, hWc⟩ :=
      exists_open_between_and_isCompact_closure hV Omega.isOpen hVΩ
    set W : Opens (EuclideanSpace ℝ ι) := ⟨W₀, hW₀⟩
    have hWΩ : W ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hWΩ₀)
    have hVW : V ≤ W := SetLike.coe_subset_coe.mp (subset_closure.trans hVW₀)
    have hVΩ' : V ≤ Omega := hVW.trans hWΩ
    -- By induction, `u ∈ H^{k+2}(W)`, and on `W` it solves the equation with data `F|_W`.
    obtain ⟨U₂, hU₂⟩ := ih ha hsmooth (F := Wkp.lowerOrder k F)
      (fun v => by rw [hu v, Wkp.value_succ]) (V := W) hWc hWΩ₀
    set FW := Wkp.restrictL hWΩ (k + 1) F
    have huW : ∀ v : W1p0 mu W 2,
        energyFormH1 a 0 0 (W1p.restrictL hWΩ u) (v : W1p mu W 2) =
          ∫ x in W, Wkp.value (k + 1) FW x * W1p.value (v : W1p mu W 2) x ∂mu := fun v => by
      rw [energyFormH1_restrictL_eq_setIntegral hWΩ hu v]
      refine integral_congr_ae ?_
      filter_upwards [Wkp.value_restrictL_ae hWΩ (k + 1) F] with x hx
      rw [hx]
    -- Each `∂ₗu` solves an equation on `W` with data in `W^{k,2}(W)`, so by induction it lies in
    -- `W^{k+2,2}(V)`.
    have hderiv : ∀ l, ∃ Z : Wkp mu V 2 (k + 2), HasWeakLineDerivOn mu V
        (W1p.value (W1p.restrictL hVΩ' u)) (Wkp.value (k + 2) Z) (b l) := fun l => by
      obtain ⟨d, G, hd, hdG⟩ :=
        exists_hasWeakLineDerivOn_and_energyFormH1_eq_setIntegral_of_contDiffOn Omega.isOpen
          hsmooth hWc hWΩ₀ k ⟨U₂, hU₂⟩ huW (b l)
      obtain ⟨Z, hZ⟩ := ih (ha.mono_set (SetLike.coe_subset_coe.mpr hWΩ))
        (fun i j => (hsmooth i j).mono (SetLike.coe_subset_coe.mpr hWΩ)) hdG hV hVW₀
      refine ⟨Z, ((hd.mono hVW).congr_ae ?_).congr_ae_deriv ?_⟩
      · exact ((W1p.value_restrictL_ae hWΩ u).filter_mono
          (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hVW)))).trans
          (W1p.value_restrictL_ae hVΩ' u).symm
      · rw [hZ]
        exact (W1p.value_restrictL_ae hVW d).symm
    exact Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b _ (k + 2) hderiv

/-- **Interior `H^{k+2}` regularity for a constant principal coefficient.** Let `A` be a
constant, uniformly elliptic matrix, let `F ∈ W^{k,2}(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution
of

`-∂ᵢ(Aⁱʲ ∂ⱼu) = F` in `Ω`,

in the sense that `∫_Ω ⟨∇v, A ∇u⟩ = ∫_Ω F v` for every `v ∈ H¹₀(Ω)`, with no boundary condition
on `u`. Then `u ∈ H^{k+2}_loc(Ω)`: on every open `V` whose closure is compact and contained in
`Ω`, the restriction of `u` is the value of an element of `W^{k+2,2}(V)`. This is the constant
case of `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL_of_contDiffOn`.

No regularity of `∂Ω` is assumed. -/
theorem UniformlyEllipticOn.exists_value_eq_value_restrictL {lam : ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ dotProduct ξ (Matrix.mulVec A ξ)) (k : ℕ)
    {F : Wkp mu Omega 2 k} {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 (fun _ => A) 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, Wkp.value k F x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {V : Opens (EuclideanSpace ℝ ι)} (hV : IsCompact (closure (V : Set (EuclideanSpace ℝ ι))))
    (hVΩ : closure (V : Set (EuclideanSpace ℝ ι)) ⊆ Omega) :
    ∃ U : Wkp mu V 2 (k + 2), Wkp.value (k + 2) U =
      W1p.value (W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) u) := by
  classical
  exact (uniformlyEllipticOn_const _ hlam hA).exists_value_eq_value_restrictL_of_contDiffOn
    (fun _ _ => contDiffOn_const) k hu hV hVΩ

end PDE

end TauCeti
