/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.PDE.ClassicalSolution
import TauCeti.Analysis.Sobolev.Leibniz
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Differentiating a divergence-form equation with differentiable coefficients

Let `a` be a matrix-valued coefficient field whose entries are `C²` on an open `Ω ⊆ ℝⁿ`, and let
`u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`,

meaning `∫_Ω ⟨∇φ, a ∇u⟩ = ∫_Ω f φ` for every test function `φ`. When the coefficients are
constant, a weak derivative `∂ₑu ∈ H¹(Ω)` solves the same equation with data `∂ₑf`. For variable
coefficients the derivative also falls on `a`, and `∂ₑu` solves

`-∂ᵢ(aⁱʲ ∂ⱼ(∂ₑu)) = ∂ₑf + ∂ᵢ((∂ₑaⁱʲ) ∂ⱼu)` in `Ω`.

The commutator `∂ᵢ((∂ₑaⁱʲ) ∂ⱼu)` is a distribution in general. Once `u` has second weak
derivatives it is the function `∑ᵢⱼ (∂ᵢ∂ₑaⁱʲ ∂ⱼu + ∂ₑaⁱʲ ∂ᵢ∂ⱼu)`, which lies in `L²_loc(Ω)` when
`u ∈ H²_loc(Ω)`. This is the induction step of interior `Hᵏ` regularity for differentiable
coefficients: interior `H²` regularity for `∂ₑu`, a solution of an equation with `L²` data, puts
`u` in `H³`, and so on.

All three statements are identities against test functions and need neither ellipticity, nor
boundedness of the coefficients, nor a boundary condition on `u`. Moving a derivative across the
energy form needs the coefficients to be `C¹` on `Ω`, and the differentiated equation, whose
right-hand side contains `∂ᵢ∂ₑaⁱʲ`, needs them to be `C²`; the Leibniz rule for a `C¹` factor
`TauCeti.HasWeakLineDerivOn.contDiffOn_smul_of_ne_zero` supplies the products.

## Main declarations

* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn`: a weak derivative
  `∂ₑ` moves from the solution onto the test function across the energy form of a `C¹`
  coefficient field, at the cost of the energy form of the coefficient field `∂ₑa`.
* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_of_hasWeakLineDerivOn`: for `u`
  with second weak derivatives, the energy form of a `C¹` coefficient field against a test
  function is integration against the function `-∂ᵢ(Bⁱʲ ∂ⱼu)`.
* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn`: the weak
  derivative `∂ₑu` of a weak solution with second weak derivatives solves the differentiated
  equation with the data `∂ₑf + ∑ᵢⱼ (∂ᵢ∂ₑaⁱʲ ∂ⱼu + ∂ₑaⁱʲ ∂ᵢ∂ⱼu)`.
* `TauCeti.PDE.energyFormH1_ofTestFunctionₗ_eq_setIntegral_inner_laplacian_smul`: for a `C²`
  function `u`, a representative of `∂ₑu` solves `-Δ(∂ₑu) = -div ((Δu) e)` weakly.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1, Theorem 2 (higher interior regularity),
  where the differentiated equation is derived in the proof.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.10.
-/

public section

noncomputable section

open LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}

/-- The drift- and mass-free energy form of `w ∈ H¹(Ω)` against a test function `φ`, entry by
entry: `a(w, φ) = ∑ᵢ ∑ⱼ ∫ (∂ᵢφ) (aⁱʲ ∂ⱼw)`, each integral taken over the whole space. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_sum_sum {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (ha : ∀ i j, ContinuousOn (fun x => a x i j) Omega) (w : W1p mu Omega 2)
    (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 a 0 0 w (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∑ i, ∑ j, ∫ x, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (EuclideanSpace.basisFun ι ℝ i) •
        (a x i j • innerSL ℝ (W1p.gradient w x) (EuclideanSpace.basisFun ι ℝ j)) ∂mu := by
  set b := EuclideanSpace.basisFun ι ℝ
  have hloc : ∀ i j, LocallyIntegrableOn
      (fun x => a x i j • innerSL ℝ (W1p.gradient w x) (b j)) Omega mu := fun i j =>
    ((W1p.hasWeakFDerivOn w).hasWeakLineDerivOn (b j)).locallyIntegrableOn_deriv.continuousOn_smul
      Omega.isOpen.isLocallyClosed (ha i j)
  -- Pointwise, `⟨η, A ξ⟩ = ∑ᵢ ∑ⱼ ηᵢ Aᵢⱼ ξⱼ`.
  have hB : ∀ (A : Matrix ι ι ℝ) (η ξ : EuclideanSpace ℝ ι), matrixBilinearForm A η ξ =
      ∑ i, ∑ j, ⟪η, b i⟫_ℝ * (A i j * innerSL ℝ ξ (b j)) := fun A η ξ => by
    simp only [b, innerSL_apply_apply, EuclideanSpace.inner_basisFun_real, matrixBilinearForm_apply,
      dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [energyFormH1_zero_zero_eq_setIntegral]
  calc ∫ x in Omega, matrixBilinearForm (a x)
        (W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ) x) (W1p.gradient w x) ∂mu
      = ∫ x in Omega, ∑ i, ∑ j, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (b i) •
          (a x i j • innerSL ℝ (W1p.gradient w x) (b j)) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) 2 φ] with x hx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hB]
        simp only [smul_eq_mul, inner_gradient_left,
          (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
    _ = ∑ i, ∑ j, ∫ x in Omega, lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x (b i) •
          (a x i j • innerSL ℝ (W1p.gradient w x) (b j)) ∂mu := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc i j) φ (b i)).restrict]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
          (integrable_lineDeriv_smul_of_locallyIntegrableOn (hloc i j) φ (b i)).restrict
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
        setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul φ (b i)

/-- **A derivative moves across a `C¹`-coefficient energy form.** Let the entries of `a` be `C¹`
on `Ω` and `a(u, v) = ∫_Ω ⟨∇v, a ∇u⟩`. If `u, d ∈ H¹(Ω)` and `d` is the weak derivative of
`u` in a direction `e`, then for every test function `φ` on `Ω`

`a(d, φ) = -a(u, ∂ₑφ) - ∫_Ω ⟨∇φ, (∂ₑa) ∇u⟩`,

the last term being the energy form of the coefficient field `∂ₑa`.

No ellipticity or boundedness of `a` is needed. -/
theorem energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) Omega)
    {u d : W1p mu Omega 2} {e : EuclideanSpace ℝ ι}
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 a 0 0 d (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 (∂_{e} φ)) -
        energyFormH1 (fun x => Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e) 0 0 u
          (W1p.ofTestFunctionₗ mu Omega 2 φ) := by
  have hΩ : IsLocallyClosed (Omega : Set (EuclideanSpace ℝ ι)) := Omega.isOpen.isLocallyClosed
  have hda : ∀ i j, ContinuousOn (fun x => fderiv ℝ (fun y => a y i j) x e) Omega := fun i j =>
    ((ha i j).continuousOn_fderiv_of_isOpen Omega.isOpen le_rfl).clm_apply continuousOn_const
  rw [energyFormH1_ofTestFunctionₗ_eq_sum_sum (fun i j => (ha i j).continuousOn),
    energyFormH1_ofTestFunctionₗ_eq_sum_sum (fun i j => (ha i j).continuousOn),
    energyFormH1_ofTestFunctionₗ_eq_sum_sum (fun i j => by simpa using hda i j)]
  simp only [Matrix.of_apply, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
  set b := EuclideanSpace.basisFun ι ℝ
  -- The components `∂ⱼu` of the weak gradient of `u` have the weak derivatives `∂ⱼd`.
  have hcomm : ∀ j, HasWeakLineDerivOn mu Omega (fun x => innerSL ℝ (W1p.gradient u x) (b j))
      (fun x => innerSL ℝ (W1p.gradient d x) (b j)) e := fun j =>
    hd.comm ((W1p.hasWeakFDerivOn d).hasWeakLineDerivOn (b j))
      ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn (b j))
  -- Each term `∫ (∂ᵢφ) (aⁱʲ ∂ⱼd)` moves `∂ₑ` onto the test function by the Leibniz rule.
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := ((hcomm j).contDiffOn_smul_of_ne_zero (ha i j) one_ne_zero)
    |>.integral_lineDeriv_smul_eq_neg_integral_smul (∂_{b i} φ)
  have hint₁ := TestFunction.integrable_smul (∂_{b i} φ)
    ((hcomm j).locallyIntegrableOn_deriv.continuousOn_smul hΩ (ha i j).continuousOn)
  have hint₂ := TestFunction.integrable_smul (∂_{b i} φ)
    ((hcomm j).locallyIntegrableOn.continuousOn_smul hΩ (hda i j))
  simp only [smul_add] at h
  rw [integral_add hint₁ hint₂] at h
  simp only [TestFunction.lineDerivOp_apply,
    TestFunction.lineDeriv_lineDerivOp_comm φ (b i) e] at h ⊢
  linear_combination h

/-- The Leibniz rule for the products `Bⁱʲ ∂ⱼu` of the entries of a coefficient field `C¹` on
`Ω` with the components of the weak gradient of `u`, differentiated in the direction `bᵢ`, when
`u` has the second weak derivatives `∂ᵢ∂ⱼu = ⟪∇(∂ⱼu), bᵢ⟫`. -/
private theorem hasWeakLineDerivOn_smul_inner_gradient {B : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hB : ∀ i j, ContDiffOn ℝ 1 (fun x => B x i j) Omega) {u : W1p mu Omega 2}
    {D : ι → W1p mu Omega 2}
    (hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (D j))
      (EuclideanSpace.basisFun ι ℝ j)) (i j : ι) :
    HasWeakLineDerivOn mu Omega
      (fun x => B x i j • innerSL ℝ (W1p.gradient u x) (EuclideanSpace.basisFun ι ℝ j))
      (fun x => B x i j • innerSL ℝ (W1p.gradient (D j) x) (EuclideanSpace.basisFun ι ℝ i) +
        fderiv ℝ (fun y => B y i j) x (EuclideanSpace.basisFun ι ℝ i) •
          innerSL ℝ (W1p.gradient u x) (EuclideanSpace.basisFun ι ℝ j))
      (EuclideanSpace.basisFun ι ℝ i) := by
  -- `∂ⱼu` agrees with the value of `D j` almost everywhere on `Ω`, so it has the same weak
  -- derivatives.
  have hae : W1p.value (D j) =ᵐ[mu.restrict Omega]
      fun x => innerSL ℝ (W1p.gradient u x) (EuclideanSpace.basisFun ι ℝ j) :=
    (hD j).ae_eq ((W1p.hasWeakFDerivOn u).hasWeakLineDerivOn _)
  exact (((W1p.hasWeakFDerivOn (D j)).hasWeakLineDerivOn _).congr_ae hae).contDiffOn_smul_of_ne_zero
    (hB i j) one_ne_zero

/-- The function `∂ᵢ(Bⁱʲ ∂ⱼu) = ∑ᵢⱼ (∂ᵢBⁱʲ ∂ⱼu + Bⁱʲ ∂ᵢ∂ⱼu)`, times a test function, is
integrable. -/
private theorem integrable_smul_sum_sum {B : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
    (hB : ∀ i j, ContDiffOn ℝ 1 (fun x => B x i j) Omega) {u : W1p mu Omega 2}
    {D : ι → W1p mu Omega 2}
    (hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (D j))
      (EuclideanSpace.basisFun ι ℝ j)) (φ : 𝓓(Omega, ℝ)) :
    Integrable (fun x => (φ : EuclideanSpace ℝ ι → ℝ) x • ∑ i, ∑ j,
      (fderiv ℝ (fun y => B y i j) x (EuclideanSpace.basisFun ι ℝ i) *
          ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ +
        B x i j * ⟪W1p.gradient (D j) x, EuclideanSpace.basisFun ι ℝ i⟫_ℝ)) mu := by
  have hL := hasWeakLineDerivOn_smul_inner_gradient hB hD
  refine (integrable_finsetSum Finset.univ fun i _ => integrable_finsetSum Finset.univ fun j _ =>
    φ.integrable_smul (hL i j).locallyIntegrableOn_deriv).congr
      (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, innerSL_apply_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The energy form of a `C¹` coefficient field on an `H²` function.** Let the entries of `B`
be `C¹` on `Ω`, and let `u ∈ H¹(Ω)` have its first weak derivatives `∂ⱼu` in `H¹(Ω)`, given as
`D j ∈ H¹(Ω)`. Then for every test function `φ` on `Ω`

`∫_Ω ⟨∇φ, B ∇u⟩ = -∫_Ω (∑ᵢⱼ (∂ᵢBⁱʲ ∂ⱼu + Bⁱʲ ∂ᵢ∂ⱼu)) φ`,

where `∂ᵢ∂ⱼu = ⟪∇(D j), bᵢ⟫` and `(bᵢ)` is the standard basis: the energy form of `B` is
integration against `-∂ᵢ(Bⁱʲ ∂ⱼu)`. -/
theorem energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_of_hasWeakLineDerivOn
    {B : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (hB : ∀ i j, ContDiffOn ℝ 1 (fun x => B x i j) Omega)
    {u : W1p mu Omega 2} {D : ι → W1p mu Omega 2}
    (hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (D j))
      (EuclideanSpace.basisFun ι ℝ j)) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 B 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      -∫ x in Omega, (∑ i, ∑ j,
        (fderiv ℝ (fun y => B y i j) x (EuclideanSpace.basisFun ι ℝ i) *
            ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ +
          B x i j * ⟪W1p.gradient (D j) x, EuclideanSpace.basisFun ι ℝ i⟫_ℝ)) * φ x ∂mu := by
  have hL := hasWeakLineDerivOn_smul_inner_gradient hB hD
  have hint : ∀ i j, Integrable (fun x => (φ : EuclideanSpace ℝ ι → ℝ) x •
      (B x i j • innerSL ℝ (W1p.gradient (D j) x) (EuclideanSpace.basisFun ι ℝ i) +
        fderiv ℝ (fun y => B y i j) x (EuclideanSpace.basisFun ι ℝ i) •
          innerSL ℝ (W1p.gradient u x) (EuclideanSpace.basisFun ι ℝ j))) mu :=
    fun i j => φ.integrable_smul (hL i j).locallyIntegrableOn_deriv
  rw [energyFormH1_ofTestFunctionₗ_eq_sum_sum (fun i j => (hB i j).continuousOn),
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      (hL i j).integral_lineDeriv_smul_eq_neg_integral_smul φ]
  simp only [Finset.sum_neg_distrib, neg_inj]
  rw [Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hint i j).symm,
    ← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  -- The integrand vanishes off `Ω`, where `φ` does.
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport fun hmem => hx (φ.tsupport_subset hmem)]]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, innerSL_apply_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The differentiated equation for `C²` coefficients.** Let the entries of `a` be `C²` on
`Ω`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, in the sense that
`∫_Ω ⟨∇φ, a ∇u⟩ = ∫_Ω f φ` for every test function `φ`. Suppose that the first weak derivatives
`∂ⱼu` lie in `H¹(Ω)`, given as `D j`, that `d ∈ H¹(Ω)` is the weak derivative of `u` in a
direction `e`, and that `g` is the weak derivative of `f` in the direction `e`. Then `d` solves

`-∂ᵢ(aⁱʲ ∂ⱼd) = g + ∑ᵢⱼ (∂ᵢ∂ₑaⁱʲ ∂ⱼu + ∂ₑaⁱʲ ∂ᵢ∂ⱼu)` in `Ω`

against every test function, where `∂ᵢ∂ⱼu = ⟪∇(D j), bᵢ⟫` and `(bᵢ)` is the standard basis.

No ellipticity or boundedness of `a` is needed, and no boundary condition is imposed on `u`. -/
theorem energyFormH1_ofTestFunctionₗ_eq_setIntegral_of_hasWeakLineDerivOn
    {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} (ha : ∀ i j, ContDiffOn ℝ 2 (fun x => a x i j) Omega)
    {f g : EuclideanSpace ℝ ι → ℝ} {u d : W1p mu Omega 2} {D : ι → W1p mu Omega 2}
    {e : EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) = ∫ x in Omega, f x * φ x ∂mu)
    (hd : HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value d) e)
    (hD : ∀ j, HasWeakLineDerivOn mu Omega (W1p.value u) (W1p.value (D j))
      (EuclideanSpace.basisFun ι ℝ j))
    (hf : HasWeakLineDerivOn mu Omega f g e) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 a 0 0 d (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, (g x + ∑ i, ∑ j,
        (fderiv ℝ (fun y => fderiv ℝ (fun z => a z i j) y e) x (EuclideanSpace.basisFun ι ℝ i) *
            ⟪W1p.gradient u x, EuclideanSpace.basisFun ι ℝ j⟫_ℝ +
          fderiv ℝ (fun y => a y i j) x e *
            ⟪W1p.gradient (D j) x, EuclideanSpace.basisFun ι ℝ i⟫_ℝ)) * φ x ∂mu := by
  have hda : ∀ i j, ContDiffOn ℝ 1
      (fun x => (Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e) i j) Omega := fun i j => by
    simpa using ((ha i j).fderiv_of_isOpen Omega.isOpen (by norm_num)).clm_apply contDiffOn_const
  -- `∫_Ω f ∂ₑφ = -∫_Ω g φ` is the definition of the weak derivative of `f`.
  have hfφ : ∫ x in Omega, f x * lineDeriv ℝ (φ : EuclideanSpace ℝ ι → ℝ) x e ∂mu =
      -∫ x in Omega, g x * φ x ∂mu := by
    have h := hf.integral_lineDeriv_smul_eq_neg_integral_smul φ
    rw [← setIntegral_lineDeriv_smul_eq_integral_lineDeriv_smul,
      ← setIntegral_smul_eq_integral_smul] at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hgφ : IntegrableOn (fun x => g x * φ x) Omega mu :=
    (φ.integrable_smul hf.locallyIntegrableOn_deriv).restrict.congr
      (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hcomm := (integrable_smul_sum_sum hda hD φ).restrict (s := Omega)
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn
      (fun i j => (ha i j).of_le (by norm_num)) hd,
    energyFormH1_ofTestFunctionₗ_eq_neg_setIntegral_of_hasWeakLineDerivOn hda hD, hu]
  simp only [TestFunction.lineDerivOp_apply, Matrix.of_apply] at hcomm ⊢
  rw [hfφ, neg_neg, sub_neg_eq_add, ← integral_add hgφ (hcomm.congr
    (Filter.Eventually.of_forall fun x => smul_eq_mul _ _ |>.trans (mul_comm _ _)))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [add_mul]

open InnerProductSpace Laplacian in
/-- **The equation of a directional derivative.** Let `u` be `C²` on an open set `U₀`, let `Ω` be
bounded with `closure Ω ⊆ U₀`, and let `d ∈ H¹(Ω)` represent `∂ₑu` on `Ω`. Then `d` solves
`-Δd = -div ((Δu) e)` weakly in `Ω`: `∫_Ω ⟨∇d, ∇φ⟩ = ∫_Ω ⟨(Δu) e, ∇φ⟩` for every test function
`φ`. -/
theorem energyFormH1_ofTestFunctionₗ_eq_setIntegral_inner_laplacian_smul [DecidableEq ι]
    {U₀ : Set (EuclideanSpace ℝ ι)} {u : EuclideanSpace ℝ ι → ℝ} {e : EuclideanSpace ℝ ι}
    (hU₀ : IsOpen U₀) (hu : ContDiffOn ℝ 2 u U₀)
    (hΩb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ ι)))
    (hΩU : closure (Omega : Set (EuclideanSpace ℝ ι)) ⊆ U₀) {d : W1p mu Omega 2}
    (hd : W1p.value d =ᵐ[mu.restrict Omega] fun x => fderiv ℝ u x e) (φ : 𝓓(Omega, ℝ)) :
    energyFormH1 (fun _ => 1) 0 0 d (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, ⟪Δ u x • e, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
  have hΩc : IsCompact (closure (Omega : Set (EuclideanSpace ℝ ι))) := hΩb.isCompact_closure
  obtain ⟨v, hv, -⟩ := W1p.exists_value_gradient_ae_eq_of_contDiffOn_of_isCompact (mu := mu)
    (Omega := Omega) (p := 2) hU₀ (hu.of_le one_le_two) hΩc subset_closure hΩU
  have hΩU' : (Omega : Set (EuclideanSpace ℝ ι)) ⊆ U₀ := subset_closure.trans hΩU
  -- `d` is the weak derivative of `v` along `e`.
  have hline : HasWeakLineDerivOn mu Omega (W1p.value v) (W1p.value d) e := by
    refine (((hasWeakFDerivOn_gradient_of_contDiffOn (μ := mu)
      ((hu.of_le one_le_two).mono hΩU')).hasWeakLineDerivOn e).congr_ae hv.symm).congr_ae_deriv ?_
    filter_upwards [hd] with x hx
    rw [hx]
    simp [inner_gradient_left]
  have hΔ : MemLp (Δ u) 2 (mu.restrict Omega) :=
    ((hu.continuousOn_laplacian hU₀).mono hΩU).memLp_restrict_of_subset_isCompact hΩc
      Omega.isOpen.measurableSet subset_closure 2
  have hgreen : energyFormH1 (fun _ => 1) 0 0 v (W1p.ofTestFunctionₗ mu Omega 2 (∂_{e} φ)) =
      ∫ x in Omega, -Δ u x * W1p.value (W1p.ofTestFunctionₗ mu Omega 2 (∂_{e} φ)) x ∂mu :=
    energyFormH1_one_zero_zero_eq_setIntegral_neg_laplacian_mul (hu.mono hΩU') hv hΔ
      ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule (∂_{e} φ)⟩
  -- The coefficient field `∂ₑ 1` of the commutator term vanishes.
  have h0 : energyFormH1 (fun x => Matrix.of fun i j =>
      fderiv ℝ (fun _ : EuclideanSpace ℝ ι => (1 : Matrix ι ι ℝ) i j) x e) 0 0 v
        (W1p.ofTestFunctionₗ mu Omega 2 φ) = 0 := by
    have hz : (Matrix.of fun _ _ => 0 : Matrix ι ι ℝ) = 0 := Matrix.ext fun _ _ => rfl
    rw [energyFormH1_zero_zero_eq_setIntegral]
    simp [hz]
  rw [energyFormH1_ofTestFunctionₗ_eq_neg_sub_of_hasWeakLineDerivOn
    (a := fun _ => 1) (fun _ _ => contDiffOn_const) hline φ, h0, sub_zero, hgreen,
    ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := mu) (p := 2) (∂_{e} φ)] with x hx
  rw [hx, TestFunction.lineDerivOp_apply_eq_fderiv, inner_smul_left, real_inner_comm,
    inner_gradient_left]
  simp

end PDE

end TauCeti
