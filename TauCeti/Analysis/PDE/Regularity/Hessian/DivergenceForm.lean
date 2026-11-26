/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Basic
public import TauCeti.Analysis.PDE.Regularity.Interior.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.Analysis.PDE.Regularity.HigherOrder
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of the second derivatives for divergence-form equations

Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be open, and let `u ∈ H¹(Ω)` be a weak solution of

`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`,

that is `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, where `a` is uniformly elliptic on `Ω`,
its entries are `C¹` on `Ω` with locally `α`-Hölder derivatives, and `f ∈ L²(Ω)` is locally
`α`-Hölder. This file proves that the second derivatives of `u` are locally `α`-Hölder
(`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn`):
on every open `V` whose closure is compact and contained in `Ω`, each weak derivative `∂ₑu` lies in
`H¹(V)`, and the precise representative of its gradient is `α`-Hölder on every compact subset of
`V`. So the second weak derivatives of a weak solution of an equation with `C^{1,α}` coefficients
and `C^α` data have locally `α`-Hölder representatives: this is interior `C^{2,α}` regularity. In
classical form, `u` agrees almost everywhere with a function that is `C²` on `Ω` and whose second
derivative is `α`-Hölder on every compact subset of `Ω`
(`exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_contDiffOn`). No
boundary condition on `u` and no regularity of `∂Ω` are used. For `a = 1` this
is the qualitative content of
`TauCeti.PDE.exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient`, which also
gives an explicit constant.

Divergence-form equations with coefficients that are only `C^α` have solutions in `C^{1,α}` and
no better
(`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm` is the
corresponding estimate); one more derivative of the coefficients buys one more derivative
of the solution. This is the linear step of the regularity bootstrap for quasilinear equations
`-div(A(x, u) ∇u) = f`: once `∇u` is Hölder, the coefficient `x ↦ A(x, u(x))` is `C^{1,β}` when
`A` is, and the theorem applies to `u` as a solution of a linear equation.

## The argument

* **The differentiated equation.** Since the bilinear forms of `a` are locally Lipschitz,
  `u ∈ H²(V)`, so `d = ∂ₑu` lies in `H¹(V)`, and moving `∂ₑ` across the energy form shows that `d`
  solves `-∂ᵢ(aⁱʲ ∂ⱼd) = -div G` in `V`, with the field `G = -f e - (∂ₑa) ∇u`
  (`UniformlyEllipticOn.exists_hasWeakLineDerivOn_and_energyFormH1_eq_neg_sub_of_contDiffOn`).
  Since `∂ₑa` is only Hölder, the term `div((∂ₑa) ∇u)` is kept as a divergence datum rather than
  expanded.
* **The datum is Hölder.** Since `f` is bounded near a compact set, the Schauder estimate for a
  bounded scalar datum
  (`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`)
  makes the precise representative of `∇u` `α`-Hölder there. Products of bounded Hölder functions
  are Hölder (`ContinuousLinearMap.exists_holderOnWith_comp₂_of_isCompact`), so `G`, written with
  this representative, is `α`-Hölder near the compact set.
* **Schauder for `d`.** The Schauder estimate for a divergence datum
  (`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`)
  applied to `d` gives the conclusion.

## Main declarations

* `exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn`:
  interior `C^{2,α}` regularity for divergence-form equations with `C^{1,α}` coefficients.
* `exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_contDiffOn`: the same
  in classical form, a `C²` representative with locally `α`-Hölder second derivative. The
  continuous representatives of the second weak derivatives give `C¹` representatives of the first
  derivatives (`TauCeti.W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative`),
  which assemble into a `C¹` derivative of `u`.
* `exists_holderOnWith_smul_neg_sub_toDual_symm_matrixBilinearForm`: the divergence datum
  `G = -f e - (∂ₑa) P` of the differentiated equation is Hölder on a compact set where the
  derivatives of the coefficients, the data and the field `P` are.
* `energyFormH1_eq_setIntegral_inner_of_eq_neg_sub`: the differentiated equation written with the
  divergence datum `G = -f e - (∂ₑa) ∇u`, for any representative of `∇u` and on any relatively
  compact `V ≤ Ω`, such as a half-ball at a flat boundary.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.10 (differentiating the equation) and Theorem 8.32 (the `C^{1,α}` estimate).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates in divergence form).
-/

public section

open InnerProductSpace LineDeriv MeasureTheory Metric Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- **The datum of the differentiated equation is Hölder.** Let the derivatives of the entries of
`a` and the function `f` be `α`-Hölder near each point of a set `Ω`, and let `P` be `α`-Hölder on a
compact set `S ⊆ Ω`. Then the field `G = -f e - (∂ₑa) P`, the divergence datum of the equation
differentiated along `e` when `P` is the gradient of the solution, is `α`-Hölder on `S`. -/
theorem exists_holderOnWith_smul_neg_sub_toDual_symm_matrixBilinearForm {Omega : Set E}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {α : ℝ≥0} (hα : 0 < α)
    (hda : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x r))
    {f : E → ℝ} (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    {S : Set E} (hS : IsCompact S) (hSΩ : S ⊆ Omega) {P : E → E} {CP : ℝ≥0}
    (hP : HolderOnWith CP α P S) (e : E) :
    ∃ K : ℝ≥0, HolderOnWith K α (fun x => f x • (-e) - (toDual ℝ E).symm
      (matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e) (P x))) S := by
  -- The transposed derivatives `(∂ₑa)ᵀ` are Hölder on `S`: the entry `∂ₑaʲⁱ` is the derivative of
  -- `aʲⁱ` evaluated at `e`.
  choose δ hδ L M hL _ using fun i j => hS.exists_holderOnWith_thickening_and_norm_le
    (f := fderiv ℝ (fun y => a y i j)) fun x hx => by
      obtain ⟨r, hr, L, hL⟩ := hda x (hSΩ hx)
      exact ⟨r, hr, L, hL i j⟩
  have hKd := holderOnWith_matrixBilinearForm_of_forall
    (a := fun x => Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e)
    (L := fun i j => ‖ContinuousLinearMap.apply ℝ ℝ e‖₊ * L j i) fun i j =>
      (ContinuousLinearMap.apply ℝ ℝ e).lipschitzWith.comp_holderOnWith
        ((hL j i).mono (self_subset_thickening (hδ j i) S))
  -- Its product with `P` is Hölder on the compact set `S`, and so is `f e`.
  obtain ⟨KT, hT⟩ := ContinuousLinearMap.exists_holderOnWith_comp₂_of_isCompact (𝕜 := ℝ) (𝕜₂ := ℝ)
    (𝕜₃ := ℝ) (σ₁₃ := RingHom.id ℝ) (σ₂₃ := RingHom.id ℝ)
    (ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ)) hS hα hKd hP
  obtain ⟨δf, hδf, Lf, -, hLf, -⟩ :=
    hS.exists_holderOnWith_thickening_and_norm_le fun x hx => hfH x (hSΩ hx)
  have hF : HolderOnWith (‖e‖₊ * Lf) α (fun x => f x • (-e)) S := by
    have h := (ContinuousLinearMap.toSpanSingleton ℝ (-e)).lipschitzWith.comp_holderOnWith
      (hLf.mono (self_subset_thickening hδf _))
    rwa [ContinuousLinearMap.nnNorm_toSpanSingleton, nnNorm_neg] at h
  exact ⟨_, (hF.sub ((toDual ℝ E).symm.isometry.comp_holderOnWith hT)).congr fun _ _ => rfl⟩

/-- **The gradient is Hölder.** For a weak solution `u` of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω` with uniformly
elliptic `a` whose entries are `C¹`, and `f ∈ L²(Ω)` which is `α`-Hölder near each point, the
precise representative of `∇u` is `α`-Hölder on every compact subset of `Ω`. -/
private theorem exists_holderOnWith_preciseRepresentative_gradient_of_contDiffOn {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Omega : Opens E}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (Omega : Set E) a lam Lam)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) Omega) {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {S : Set E} (hS : IsCompact S) (hSΩ : S ⊆ Omega) :
    ∃ C : ℝ≥0, HolderOnWith C α (preciseRepresentative volume (W1p.gradient u : E → E)) S := by
  obtain ⟨δ, hδ, hSδ⟩ := hS.exists_cthickening_subset_open Omega.isOpen hSΩ
  have hth : thickening δ S ⊆ cthickening δ S := thickening_subset_cthickening δ S
  obtain ⟨Ka, hKa⟩ :=
    exists_holderOnWith_matrixBilinearForm_of_contDiffOn Omega.isOpen ha hS.cthickening hSδ hα1.le
  -- The datum `f` is bounded near `S`.
  obtain ⟨δ', hδ', -, M, -, hM⟩ :=
    hS.cthickening.exists_holderOnWith_thickening_and_norm_le fun x hx => hfH x (hSδ hx)
  have hf' : MemLp f ⊤ (volume.restrict (thickening δ S)) :=
    memLp_top_of_bound (hf.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (hth.trans hSδ) le_rfl)) M
      (ae_restrict_of_forall_mem isOpen_thickening.measurableSet fun x hx =>
        hM x (self_subset_thickening hδ' _ (hth hx)))
  obtain ⟨C, -, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp
      (n := n) hα hα1 le_rfl (q := ⊤) le_top (by simpa using hα1.le) (lam := lam) (Lam := Lam)
      (M := Ka * δ ^ (α : ℝ))
  refine ⟨_, h (hell.mono_set hSΩ) (hKa.mono hth) ((HolderWith.zero (C := 0)).holderOnWith _)
    le_rfl hf' (fun φ => (hu ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩).trans ?_) hδ
    (hth.trans hSδ)⟩
  simp only [Pi.zero_apply, inner_zero_left, integral_zero, zero_add]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with x hx
  rw [hx]

/-- **The differentiated equation in divergence form.** Let `V ≤ Ω` have compact closure,
contained in an open set `W` on which the entries of `a` are `C¹`, and let `d ∈ H¹(V)` satisfy
`a(d, φ) = -∫_V f ∂ₑφ - ∫_V ⟨∇φ, (∂ₑa) ∇u⟩` for a test function `φ` on `V`, where `f ∈ L²(Ω)` and
`u ∈ H¹(Ω)`. Then `a(d, φ) = ∫_V ⟨G, ∇φ⟩` for the field `G = -f e - (∂ₑa) P`, for every `P` equal
to `∇u` almost everywhere on `V`, such as a precise representative of `∇u`. The closure of `V`
need not lie in `Ω`: at a flat boundary, `V` is a half-ball. -/
theorem energyFormH1_eq_setIntegral_inner_of_eq_neg_sub {Omega V : Opens E} {W : Set E}
    (hV : IsCompact (closure (V : Set E))) (hVΩ : V ≤ Omega) (hW : IsOpen W)
    (hVW : closure (V : Set E) ⊆ W) {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) W) {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict Omega)) {u : W1p volume Omega 2} {e : E} {P : E → E}
    (hP : P =ᵐ[volume.restrict V] W1p.gradient u) {d : W1p volume V 2} {φ : 𝓓(V, ℝ)}
    (hdeq : energyFormH1 a 0 0 d (W1p.ofTestFunctionₗ volume V 2 φ) =
        -(∫ x in V, f x * lineDeriv ℝ (φ : E → ℝ) x e) -
          ∫ x in V, matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e)
            (∇ (φ : E → ℝ) x) (W1p.gradient u x)) :
    energyFormH1 a 0 0 d (W1p.ofTestFunctionₗ volume V 2 φ) =
      ∫ x in V, ⟪f x • (-e) - (toDual ℝ E).symm
        (matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e) (P x)),
          ∇ (φ : E → ℝ) x⟫_ℝ := by
  -- Pointwise, `⟨G, ∇φ⟩ = -f ∂ₑφ - ⟨∇φ, (∂ₑa) P⟩`.
  have hpt : ∀ x, ⟪f x • (-e) - (toDual ℝ E).symm
      (matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e) (P x)),
        ∇ (φ : E → ℝ) x⟫_ℝ = -(f x * lineDeriv ℝ (φ : E → ℝ) x e) -
          matrixBilinearForm (Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e)
            (∇ (φ : E → ℝ) x) (P x) := fun x => by
    have hT : (Matrix.of fun i j => fderiv ℝ (fun y => a y j i) x e) =
        Matrix.transpose (Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e) := by
      ext i j
      simp
    rw [inner_sub_left, toDual_symm_apply, hT, matrixBilinearForm_transpose_apply,
      inner_gradient_right, (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
    simp
  have hI₁ : Integrable (fun x => f x * lineDeriv ℝ (φ : E → ℝ) x e) (volume.restrict V) :=
    (integrable_lineDeriv_smul_of_locallyIntegrableOn
      ((locallyIntegrableOn_of_locallyIntegrable_restrict
        (hf.locallyIntegrable one_le_two)).mono_set
          (SetLike.coe_subset_coe.mpr hVΩ)) φ e).restrict.congr
      (Filter.Eventually.of_forall fun x => (smul_eq_mul _ _).trans (mul_comm _ _))
  -- The coefficients `∂ₑa` are bounded on `V`, so the energy density is integrable there.
  have hB : ContinuousOn (fun x => Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e)
      (closure (V : Set E)) := fun x hx => by
    refine continuousWithinAt_pi.2 fun i => continuousWithinAt_pi.2 fun j => ?_
    exact ((((ha i j).continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply
      continuousOn_const).mono hVW) x hx
  have hI₂ : Integrable (fun x => matrixBilinearForm
      (Matrix.of fun i j => fderiv ℝ (fun y => a y i j) x e) (∇ (φ : E → ℝ) x) (P x))
      (volume.restrict V) := by
    refine (integrable_energyIntegrand_jetField (memLp_energyIntegrand_of_continuousOn
      (b := 0) (c := 0) hV hB continuousOn_const continuousOn_const) (W1p.restrictL hVΩ u)
        (W1p.ofTestFunctionₗ volume V 2 φ)).congr ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) 2 φ,
      W1p.gradient_restrictL_ae hVΩ u, hP] with x hx hux hPx
    simp only [energyIntegrand_apply, jetField_apply, W1p.gradient_ofTestFunctionₗ, hx, hux, hPx]
    simp
  rw [hdeq]
  simp only [hpt]
  rw [integral_sub (f := fun x => -(f x * lineDeriv ℝ (φ : E → ℝ) x e)) hI₁.neg hI₂, integral_neg]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hP] with x hx
  rw [hx]

/-- **Interior `C^{2,α}` regularity for divergence-form equations with `C^{1,α}` coefficients.**
Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be open, and let `u ∈ H¹(Ω)` be a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, that is `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. Suppose that
`a` is uniformly elliptic on `Ω`, that its entries are `C¹` on `Ω` with derivatives `α`-Hölder near
each point of `Ω`, and that `f ∈ L²(Ω)` is `α`-Hölder near each point of `Ω`. Let `V` be open with
compact closure contained in `Ω`. Then for every direction `e`, the weak derivative `∂ₑu` lies in
`H¹(V)`, and the precise representative of its gradient is `α`-Hölder on every compact subset of
`V`.

So the second weak derivatives of `u` have locally `α`-Hölder representatives. No boundary condition
is imposed on `u` and nothing is assumed about `∂Ω`. The precise representative agrees with
`∇∂ₑu` almost everywhere on `V` (`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). -/
theorem exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Omega V : Opens E}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (Omega : Set E) a lam Lam)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) Omega)
    (hda : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x r))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Omega))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    (hV : IsCompact (closure (V : Set E))) (hVΩ : closure (V : Set E) ⊆ Omega) (e : E) :
    ∃ d : W1p volume V 2, HasWeakLineDerivOn volume V (W1p.value u) (W1p.value d) e ∧
      ∀ K ⊆ (V : Set E), IsCompact K → ∃ C : ℝ≥0,
        HolderOnWith C α (preciseRepresentative volume (W1p.gradient d : E → E)) K := by
  obtain ⟨d, hd, hdeq⟩ :=
    hell.exists_hasWeakLineDerivOn_and_energyFormH1_eq_neg_sub_of_contDiffOn ha hf hu hV hVΩ e
  refine ⟨d, hd, fun K hKV hK => ?_⟩
  -- The precise representative of `∇u` is `∇u` almost everywhere on `V`.
  have hP' : preciseRepresentative volume (W1p.gradient u : E → E) =ᵐ[volume.restrict V]
      W1p.gradient u :=
    ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVΩ)
      (ae_eq_restrict_preciseRepresentative Omega.isOpen (W1p.locallyIntegrableOn_gradient u)).symm
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open V.isOpen hKV
  have hC : IsCompact (cthickening δ K) := hK.cthickening
  have hCΩ : cthickening δ K ⊆ Omega := hKδ.trans (subset_closure.trans hVΩ)
  have hth : thickening δ K ⊆ cthickening δ K := thickening_subset_cthickening δ K
  -- The gradient of `u`, the coefficients and their derivatives are Hölder near `K`.
  obtain ⟨CP, hP⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_contDiffOn hα hα1 hell ha hf hfH hu hC hCΩ
  obtain ⟨Ka, hKa⟩ :=
    exists_holderOnWith_matrixBilinearForm_of_contDiffOn Omega.isOpen ha hC hCΩ hα1.le
  -- Hence so is the divergence datum `G = -f e - (∂ₑa) ∇u` of the equation for `∂ₑu`.
  obtain ⟨KG, hG⟩ := exists_holderOnWith_smul_neg_sub_toDual_symm_matrixBilinearForm hα hda hfH hC
    hCΩ hP e
  obtain ⟨C, -, h⟩ :=
    exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm
      (n := n) hα hα1 (lam := lam) (Lam := Lam) (M := Ka * δ ^ (α : ℝ))
  exact ⟨_, h (hell.mono_set (hKV.trans (subset_closure.trans hVΩ))) (hKa.mono hth) (hG.mono hth)
    le_rfl (fun φ => energyFormH1_eq_setIntegral_inner_of_eq_neg_sub hV
      (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)) Omega.isOpen hVΩ ha hf hP' (hdeq φ)) hδ
    (hth.trans hKδ)⟩

/-- On the ball `B(x, r / 2)`, where `closedBall x r ⊆ Ω`, each directional derivative `∂ₑu` of a
weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `C^{1,α}` coefficients and `C^α` data has a `C¹`
representative `gₑ` whose derivative is `⟪G, ·⟫` for an `α`-Hölder field `G`. -/
private theorem exists_contDiffOn_hasWeakLineDerivOn_and_holderOnWith_of_contDiffOn {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Omega : Opens E}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (Omega : Set E) a lam Lam)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) Omega)
    (hda : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x r))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Omega))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {x : E} {r : ℝ} (hr : 0 < r) (hrΩ : closedBall x r ⊆ Omega) (e : E) :
    ∃ (ge : E → ℝ) (G : E → E) (C : ℝ≥0), ContDiffOn ℝ 1 ge (ball x (r / 2)) ∧
      HolderOnWith C α G (ball x (r / 2)) ∧
      HasWeakLineDerivOn volume ⟨ball x (r / 2), isOpen_ball⟩ (W1p.value u) ge e ∧
      ∀ y ∈ ball x (r / 2), HasFDerivAt ge (innerSL ℝ (G y)) y := by
  let V : Opens E := ⟨ball x r, isOpen_ball⟩
  let W : Opens E := ⟨ball x (r / 2), isOpen_ball⟩
  have hWV : W ≤ V := ball_subset_ball (half_le_self hr.le)
  obtain ⟨d, hd, hG⟩ :=
    exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn
      hα hα1 hell ha hda hf hfH hu (V := V) ((isCompact_closedBall x r).of_isClosed_subset
        isClosed_closure closure_ball_subset_closedBall)
      (closure_ball_subset_closedBall.trans hrΩ) e
  obtain ⟨C, hC⟩ := hG (closedBall x (r / 2)) (closedBall_subset_ball (half_lt_self hr))
    (isCompact_closedBall _ _)
  have hCW : HolderOnWith C α (preciseRepresentative volume (W1p.gradient d : E → E)) W :=
    hC.mono ball_subset_closedBall
  -- The precise representative of `∇d` is a continuous weak derivative of `d = ∂ₑu` on `W`.
  obtain ⟨ge, hge, hdge, hgd⟩ :=
    W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative d hWV
      (hCW.continuousOn hα)
  exact ⟨ge, _, C, hge, hCW, (hd.mono hWV).congr_ae_deriv hdge, hgd⟩

/-- Near each point of `Ω`, a continuous representative `g` of a weak solution of
`-∂ᵢ(aⁱʲ ∂ⱼu) = f` with `C^{1,α}` coefficients and `C^α` data is `C²`, with `α`-Hölder second
derivative. -/
private theorem exists_ball_contDiffOn_two_and_holderOnWith_iteratedFDeriv_two {α : ℝ≥0}
    (hα : 0 < α) (hα1 : α < 1) {Omega : Opens E}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (Omega : Set E) a lam Lam)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) Omega)
    (hda : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x r))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Omega))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x)
    {g : E → ℝ} (hg : ContinuousOn g Omega) (hug : W1p.value u =ᵐ[volume.restrict Omega] g)
    {x : E} (hx : x ∈ Omega) :
    ∃ r > 0, ContDiffOn ℝ 2 g (ball x r) ∧
      ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ 2 g) (ball x r) := by
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  let W : Opens E := ⟨ball x (r / 2), isOpen_ball⟩
  have hWΩ : W ≤ Omega := (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (half_le_self hr.le))).trans hrΩ
  let b := EuclideanSpace.basisFun (Fin (n + 1)) ℝ
  choose gi G C hgi hCG hdg hgd using fun i =>
    exists_contDiffOn_hasWeakLineDerivOn_and_holderOnWith_of_contDiffOn hα hα1 hell ha hda hf
      hfH hu hr hrΩ (b i)
  -- The `C¹` fields `gᵢ` assemble into a `C¹` weak derivative of the continuous `g`, so `g` is
  -- `C²`, with `∂ᵢg = gᵢ`.
  obtain ⟨hD, huD⟩ := contDiffOn_sum_innerSL_and_hasWeakFDerivOn (Ω := W) hgi
    ((W1p.hasWeakFDerivOn u).locallyIntegrableOn.mono_set hWΩ) hdg
  have hgD := huD.congr_ae (ae_restrict_of_ae_restrict_of_subset hWΩ hug)
  have hg2 : ContDiffOn ℝ 2 g W := by exact_mod_cast hgD.contDiffOn_succ (hg.mono hWΩ) hD
  have hfd : ∀ i, ∀ y ∈ W, fderiv ℝ g y (b i) = gi i y := fun i y hy => by
    rw [hgD.fderiv_eq_of_continuousOn (hg.mono hWΩ) hD.continuousOn hy]
    simp [b.inner_eq_ite]
  -- The gradient of `∂ᵢg` is `Gᵢ`, which is `α`-Hölder.
  refine ⟨r / 2, half_pos hr, hg2, _, b.holderOnWith_iteratedFDeriv_two_of_dist_gradient_le
    (D := ∑ i, (C i : ℝ)) (by positivity) (fun y hy => ?_) fun i y hy z hz => ?_⟩
  · exact ((hg2.fderiv_of_isOpen W.isOpen (by norm_num)).differentiableOn one_ne_zero
      |>.differentiableAt (W.isOpen.mem_nhds hy))
  · have hgrad : ∀ w ∈ W, ∇ (fun z => fderiv ℝ g z (b i)) w = G i w := fun w hw => by
      refine (HasGradientAt.gradient ?_)
      rw [hasGradientAt_iff_hasFDerivAt]
      refine ((hgd i w hw).congr_fderiv ?_).congr_of_eventuallyEq
        (Filter.eventually_of_mem (W.isOpen.mem_nhds hw) fun z hz => hfd i z hz)
      ext v
      simp
    rw [hgrad y hy, hgrad z hz]
    exact ((hCG i).dist_le hy hz).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := fun i => (C i : ℝ)) (fun _ _ => NNReal.coe_nonneg _)
        (Finset.mem_univ i)) (by positivity))

/-- **Classical interior `C^{2,α}` regularity for divergence-form equations with `C^{1,α}`
coefficients.** Let `0 < α < 1`, let `Ω ⊆ ℝ^{n+1}` be open, and let `u ∈ H¹(Ω)` be a weak
solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f` in `Ω`, where `a` is uniformly elliptic on `Ω` with entries `C¹`
on `Ω` and derivatives `α`-Hölder near each point of `Ω`, and `f ∈ L²(Ω)` is `α`-Hölder near each
point of `Ω`. Then `u` agrees almost everywhere on `Ω` with a function `g` that is `C²` on `Ω`
and whose second derivative is `α`-Hölder on every compact subset of `Ω`.

This is the classical form of
`exists_hasWeakLineDerivOn_and_holderOnWith_preciseRepresentative_gradient_of_contDiffOn`. No
boundary condition is imposed on `u` and nothing is assumed about `∂Ω`. -/
theorem exists_contDiffOn_two_ae_eq_and_holderOnWith_iteratedFDeriv_two_of_contDiffOn
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) {Omega : Opens E}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (Omega : Set E) a lam Lam)
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) Omega)
    (hda : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, ∀ i j,
      HolderOnWith L α (fderiv ℝ (fun y => a y i j)) (ball x r))
    {f : E → ℝ} (hf : MemLp f 2 (volume.restrict Omega))
    (hfH : ∀ x ∈ Omega, ∃ r > 0, ∃ L : ℝ≥0, HolderOnWith L α f (ball x r))
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2, energyFormH1 a 0 0 u (v : W1p volume Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p volume Omega 2) x) :
    ∃ g : E → ℝ, ContDiffOn ℝ 2 g Omega ∧ W1p.value u =ᵐ[volume.restrict Omega] g ∧
      ∀ K ⊆ (Omega : Set E), IsCompact K →
        ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ 2 g) K := by
  -- The gradient of `u` has a continuous representative, so `u` has a `C¹` representative `g`.
  have hP : ContinuousOn (preciseRepresentative volume (W1p.gradient u : E → E)) Omega :=
    fun x hx => by
      obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
      obtain ⟨C, hC⟩ := exists_holderOnWith_preciseRepresentative_gradient_of_contDiffOn hα hα1
        hell ha hf hfH hu (isCompact_closedBall x r) hrΩ
      exact ((hC.continuousOn hα).continuousAt (closedBall_mem_nhds x hr)).continuousWithinAt
  obtain ⟨g, hg, hug, -⟩ :=
    W1p.exists_contDiffOn_one_ae_eq_of_continuousOn_preciseRepresentative u le_rfl hP
  have hloc := fun x (hx : x ∈ Omega) =>
    exists_ball_contDiffOn_two_and_holderOnWith_iteratedFDeriv_two hα hα1 hell ha hda hf hfH hu
      hg.continuousOn hug hx
  refine ⟨g, contDiffOn_of_locally_contDiffOn fun x hx => ?_, hug, fun K hKΩ hK => ?_⟩
  · obtain ⟨r, hr, hg2, -⟩ := hloc x hx
    exact ⟨ball x r, isOpen_ball, mem_ball_self hr, hg2.mono inter_subset_right⟩
  · obtain ⟨δ, hδ, C, -, hC, -⟩ := hK.exists_holderOnWith_thickening_and_norm_le fun x hx => by
      obtain ⟨r, hr, -, C, hC⟩ := hloc x (hKΩ hx)
      exact ⟨r, hr, C, hC⟩
    exact ⟨C, hC.mono (self_subset_thickening hδ K)⟩

end PDE

end TauCeti
