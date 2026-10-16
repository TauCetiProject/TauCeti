/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Interior
public import TauCeti.Analysis.PDE.EnergyForm.Restriction
public import TauCeti.Analysis.Sobolev.Wkp.LineDeriv
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry

/-!
# Interior `Hᵏ` regularity for a constant principal coefficient

Let `A` be a constant, uniformly elliptic coefficient matrix and let `u ∈ H¹(Ω)` be a weak
solution of the divergence-form equation

`-∂ⱼ(Aⁱʲ ∂ᵢu) = f` in `Ω`, with `f ∈ W^{k,2}(Ω)`,

meaning `∫_Ω ⟨∇v, A ∇u⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`
and nothing assumed about `∂Ω`. This file proves that `u ∈ H^{k+2}_loc(Ω)`: on every open `V`
whose closure is compact and contained in `Ω`, the restriction of `u` is the value of an element
of `W^{k+2,2}(V)`. Each derivative of the data buys one more derivative of the solution, so
smooth data give a solution in every `H^m_loc(Ω)`.

## Differentiating the equation

The induction on `k` rests on one observation: because `A` is constant, a weak derivative of a
weak solution is again a weak solution, with the derivative of the data as right-hand side. If
`u` solves `-div(A ∇u) = f`, `∂ₑu ∈ H¹(Ω)` and `∂ₑf ∈ L²(Ω)`, then `∂ₑu` solves
`-div(A ∇(∂ₑu)) = ∂ₑf` (`TauCeti.PDE.energyFormH1_eq_setIntegral_of_hasWeakLineDerivOn`). Against
a test function `φ`, the energy form is a sum of integrals `∫ (∂_{cⱼ} φ) ∂ⱼw`, where `cⱼ` is the
`j`-th column of `A`. Since weak derivatives commute (`TauCeti.HasWeakLineDerivOn.comm`), the
derivative `∂ₑ` moves from `∂ⱼ(∂ₑu)` onto the test function, where it commutes with `∂_{cⱼ}`
(`TestFunction.lineDerivOp_comm`), so `a(∂ₑu, φ) = -a(u, ∂ₑφ) = -∫ f ∂ₑφ = ∫ (∂ₑf) φ`.

## The induction

The case `k = 0` is interior `H²` regularity
(`TauCeti.PDE.UniformlyEllipticOn.exists_lowerOrder_eq_restrictL`). For the step, fix `V` and an
open `W` with `closure V ⊆ W` and `closure W` compact in `Ω`. On `W` the solution lies in `H²`,
so each `∂ᵢu` lies in `H¹(W)` and, by the observation above, solves the equation on `W` with data
`∂ᵢf ∈ W^{k,2}(W)`. The induction hypothesis puts `∂ᵢu` in `W^{k+2,2}(V)` for every `i`, and a
function whose first weak derivatives lie in `W^{k+2,2}(V)` lies in `W^{k+3,2}(V)`
(`TauCeti.Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn`).

## Main declarations

* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn`: a weak derivative
  moves from the solution to the test function across the constant-coefficient energy form.
* `TauCeti.PDE.energyFormH1_eq_setIntegral_of_hasWeakLineDerivOn`: a weak derivative of a weak
  solution of a constant-coefficient equation solves the differentiated equation.
* `TauCeti.PDE.UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_energyFormH1_eq_neg_setIntegral`:
  for `L²` data, each first derivative of a weak solution lies in `H¹` on compactly contained open
  sets and solves the equation with the distributional derivative of the data.
* `TauCeti.PDE.UniformlyEllipticOn.exists_value_eq_value_restrictL`: interior `H^{k+2}`
  regularity for data in `W^{k,2}`.

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

No ellipticity is needed. -/
theorem energyFormH1_ofTestFunctionₗ_eq_neg_of_hasWeakLineDerivOn {u d : W1p mu Omega 2}
    {e : EuclideanSpace ℝ ι} (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e)
    (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => A) 0 0 d (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 (∂_{e} φ)) := by
  set b := EuclideanSpace.basisFun ι ℝ
  -- The components `∂ⱼu` of the weak gradient of `u` have the weak derivatives `∂ⱼ(∂ₑu)`.
  have hcomm : ∀ j, HasWeakLineDerivOn mu Omega (fun x => innerSL ℝ (W1p.gradient u x) (b j))
      (fun x => innerSL ℝ (W1p.gradient d x) (b j)) e := fun j =>
    hd.comm ((W1p.hasWeakFDerivOn d).hasWeakLineDerivOn (b j))
      ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b j))
  -- Each term `∫ (∂_{cⱼ} φ) ∂ⱼ(∂ₑu)` moves `∂ₑ` onto the test function.
  have hterm : ∀ j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (WithLp.toLp 2 (Aᵀ j)) •
        innerSL ℝ (W1p.gradient d x) (b j) ∂mu =
      -∫ x, lineDeriv ℝ (∂_{e} φ : 𝓓(Omega, ℝ)) x (WithLp.toLp 2 (Aᵀ j)) •
        innerSL ℝ (W1p.gradient u x) (b j) ∂mu := fun j => by
    have h := (hcomm j).integral_lineDeriv_smul_eq_neg_integral_smul (∂_{WithLp.toLp 2 (Aᵀ j)} φ)
    simp only [TestFunction.lineDerivOp_apply,
      TestFunction.lineDeriv_lineDerivOp_comm φ (WithLp.toLp 2 (Aᵀ j)) e] at h
    rw [h, neg_neg]
  rw [energyFormH1_ofTestFunctionₗ_eq_sum, Finset.sum_congr rfl fun j _ => hterm j,
    Finset.sum_neg_distrib, ← energyFormH1_ofTestFunctionₗ_eq_sum]

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
elliptic matrix, `f ∈ L²(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(Aⁱʲ ∂ᵢu) = f` in
`Ω`, in the sense that `∫_Ω ⟨∇v, A ∇u⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. Let `V` be open with
compact closure contained in `Ω`. Then in every direction `e` the weak derivative `∂ₑu` lies in
`H¹(V)` and satisfies `∫_V ⟨∇φ, A ∇∂ₑu⟩ = -∫_V f ∂ₑφ` for every test function `φ` on `V`: it is
a weak solution of `-∂ⱼ(Aⁱʲ ∂ᵢ∂ₑu) = ∂ₑf` in `V`, with the derivative of the data taken in the
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

/-! ### Interior `H^{k+2}` regularity -/

/-- **Interior `H^{k+2}` regularity for a constant principal coefficient.** Let `A` be a
constant, uniformly elliptic matrix, let `F ∈ W^{k,2}(Ω)`, and let `u ∈ H¹(Ω)` be a weak solution
of

`-∂ⱼ(Aⁱʲ ∂ᵢu) = F` in `Ω`,

in the sense that `∫_Ω ⟨∇v, A ∇u⟩ = ∫_Ω F v` for every `v ∈ H¹₀(Ω)`, with no boundary condition
on `u`. Then `u ∈ H^{k+2}_loc(Ω)`: on every open `V` whose closure is compact and contained in
`Ω`, the restriction of `u` is the value of an element of `W^{k+2,2}(V)`.

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
  induction k generalizing Omega V with
  | zero =>
    obtain ⟨U, hU⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL hlam hA
      MemLp.zero MemLp.zero hu hV hVΩ
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
    -- On `W`, `u` lies in `H²` and solves the equation with data `F|_W`.
    obtain ⟨U₂, hU₂⟩ := UniformlyEllipticOn.exists_lowerOrder_eq_restrictL hlam hA
      MemLp.zero MemLp.zero hu (V := W) hWc hWΩ₀
    have hU₂v : Wkp.value 2 U₂ = W1p.value (W1p.restrictL hWΩ u) := by
      rw [Wkp.value_succ, Wkp.value_one, hU₂]
    set FW := Wkp.restrictL hWΩ (k + 1) F
    have huW : ∀ v : W1p0 mu W 2,
        energyFormH1 (fun _ => A) 0 0 (W1p.restrictL hWΩ u) (v : W1p mu W 2) =
          ∫ x in W, Wkp.value (k + 1) FW x * W1p.value (v : W1p mu W 2) x ∂mu := fun v => by
      rw [energyFormH1_restrictL_eq_setIntegral hWΩ hu v]
      refine integral_congr_ae ?_
      filter_upwards [Wkp.value_restrictL_ae hWΩ (k + 1) F] with x hx
      rw [hx]
    -- Each `∂ᵢu` lies in `H¹(W)` and solves the equation on `W` with data `∂ᵢF ∈ W^{k,2}(W)`,
    -- so by induction it lies in `W^{k+2,2}(V)`.
    have hderiv : ∀ i, ∃ D : Wkp mu V 2 (k + 2), HasWeakLineDerivOn mu V
        (W1p.value (W1p.restrictL hVΩ' u)) (Wkp.value (k + 2) D) (b i) := fun i => by
      obtain ⟨d, hd⟩ := Wkp.exists_hasWeakLineDerivOn_value 1 U₂ (b i)
      obtain ⟨G, hG⟩ := Wkp.exists_hasWeakLineDerivOn_value k FW (b i)
      rw [hU₂v, Wkp.value_one] at hd
      obtain ⟨D, hD⟩ := ih (F := G) (u := d)
        (fun v => energyFormH1_eq_setIntegral_of_hasWeakLineDerivOn huW hd hG v) hV hVW₀
      refine ⟨D, ((hd.mono hVW).congr_ae ?_).congr_ae_deriv ?_⟩
      · exact ((W1p.value_restrictL_ae hWΩ u).filter_mono
          (ae_mono (Measure.restrict_mono_set mu (SetLike.coe_subset_coe.mpr hVW)))).trans
          (W1p.value_restrictL_ae hVΩ' u).symm
      · rw [hD]
        exact (W1p.value_restrictL_ae hVW d).symm
    exact Wkp.exists_value_eq_of_forall_hasWeakLineDerivOn b _ (k + 2) hderiv

end PDE

end TauCeti
