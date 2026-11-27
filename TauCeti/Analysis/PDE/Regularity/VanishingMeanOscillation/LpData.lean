/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.VanishingMeanOscillation.ZeroOrderShift
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Matrix.EuclideanLin.Measurable
import TauCeti.Analysis.PDE.DirichletProblem.WholeSpace
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Krylov's whole-space `W^{1,p}` theorem with a zero-order shift for data in `Lᵖ`

Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic with constants
`0 < λ ≤ Λ` and not necessarily symmetric, whose mean oscillation is small below a radius `r₀`,
let `2 < p < ∞` and `κ ≥ 16 / r₀²`. The shifted equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` in `ℝ^{n+1}`

was solved in `TauCeti/Analysis/PDE/Regularity/VanishingMeanOscillation/ZeroOrderShift.lean` for
data in `L² ∩ Lᵖ`, by solutions in `H¹(ℝ^{n+1})`. This file treats data `f, G ∈ Lᵖ` that need
not be square integrable, with solutions in `W^{1,p}(ℝ^{n+1})`, which need not lie in `H¹`. A
solution `u ∈ W^{1,p}(ℝ^{n+1})` is meant in the sense of distributions,

`∫ ⟨a ∇u, ∇φ⟩ + κ ∫ u φ = ∫ f φ + ∫ ⟨G, ∇φ⟩` for every test function `φ`,

written with the integrated energy form `TauCeti.PDE.energyFormIntegral`.

* `TauCeti.PDE.exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le_of_memLp`:
  every such solution satisfies Krylov's estimate
  `‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`, with the constant `C` of the
  estimate for `H¹` solutions. Applied to differences of solutions, it makes solutions in
  `W^{1,p}(ℝ^{n+1})` unique.
* `TauCeti.PDE.existsUnique_forall_energyFormIntegral_eq_of_vmoModulus_le`: for coefficients
  whose VMO modulus at the scale `r₀` is small, the equation has exactly one solution in
  `W^{1,p}(ℝ^{n+1})` for all `f, G ∈ Lᵖ`.
* `TauCeti.PDE.existsUnique_forall_energyFormIntegral_eq_of_memVMO`: for coefficients of vanishing
  mean oscillation the same holds for every `κ` above a threshold `κ₀(a)`.

Together with the estimate these give Krylov's theorem for `2 < p < ∞` in the form in which it is
stated for data in `Lᵖ`: the unique solution in `W^{1,p}(ℝ^{n+1})` is bounded in `W^{1,p}` by the
data.

## The argument

* **The estimate.** Let `ψ` be a smooth cutoff equal to `1` on `B(0, R)`, supported in
  `B(0, 2R)`, with `‖∇ψ‖ ≤ c / R`. Since `p > 2` and `ψ` has compact support, `ψ u` lies in
  `H¹(ℝ^{n+1})`, with gradient `ψ ∇u + u ∇ψ`. Testing the equation of `u` against `ψ φ` shows
  that `ψ u` solves the shifted equation with the data

  `f_R = ψ f + ⟨G, ∇ψ⟩ - ⟨a ∇u, ∇ψ⟩`, `G_R = ψ G + u a ∇ψ`,

  which lie in `L² ∩ Lᵖ`. The estimate for `H¹` solutions applies to `ψ u`, and the terms carrying
  `∇ψ` are `O(1 / R)` in `Lᵖ`. Letting `R → ∞` gives the estimate for `u`.
* **Existence.** Cut the data off to the balls `B(0, k + 1)`. The cut-off data lie in `L² ∩ Lᵖ`,
  so the shifted equation has an `H¹` solution `uₖ`, which lies in `W^{1,p}` by the regularity
  theorem for coefficients of small VMO modulus. The estimate for `uₖ - uⱼ` makes `(uₖ)` a Cauchy
  sequence in `W^{1,p}(ℝ^{n+1})`. Its limit solves the equation, since both sides of the weak
  formulation are continuous in `Lᵖ` for a fixed test function.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475, Theorem 2.8.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace Matrix
open scoped ENNReal NNReal ContDiff Distributions Gradient InnerProductSpace Topology

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-! ### Cutoffs of `W^{1,p}` solutions -/

/-- The matrix bilinear form as the inner product with the matrix acting on Euclidean space:
`ηᵀ A ξ = ⟪A ξ, η⟫`. -/
private theorem matrixBilinearForm_eq_inner_toEuclideanCLM
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (η ξ : EuclideanSpace ℝ (Fin (n + 1))) :
    matrixBilinearForm A η ξ = ⟪toEuclideanCLM (𝕜 := ℝ) A ξ, η⟫_ℝ := by
  rw [matrixBilinearForm_apply, real_inner_comm, inner_toEuclideanCLM]

/-- A function bounded by a multiple of an `Lᵖ` function, `2 ≤ p`, and vanishing off a compact set
is square integrable. -/
private theorem memLp_two_of_norm_le_mul {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    (hp2 : 2 ≤ p) {g : EuclideanSpace ℝ (Fin (n + 1)) → F} (hg : AEStronglyMeasurable g volume)
    {F' : Type*} [NormedAddCommGroup F'] {h : EuclideanSpace ℝ (Fin (n + 1)) → F'}
    (hh : MemLp h p volume) {C : ℝ} (hle : ∀ x, ‖g x‖ ≤ C * ‖h x‖)
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K) (h0 : ∀ x ∉ K, g x = 0) :
    MemLp g p volume ∧ MemLp g 2 volume := by
  have hgp : MemLp g p volume := hh.of_le_mul hg (ae_of_all _ hle)
  exact ⟨hgp, hgp.mono_exponent_of_measure_support_ne_top h0 hK.measure_lt_top.ne hp2⟩

/-- An element of `W^{1,p}(ℝ^{n+1})` whose value and weak gradient lie in `L^q` is an element of
`W^{1,q}(ℝ^{n+1})`. -/
private theorem exists_w1p_value_gradient_ae_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    (hv : MemLp (W1p.value v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) q volume)
    (hg : MemLp (W1p.gradient v : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) q volume) :
    ∃ w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) q,
      (∀ᵐ x, W1p.value w x = W1p.value v x) ∧ ∀ᵐ x, W1p.gradient w x = W1p.gradient v x := by
  obtain ⟨w, hwv, hwg⟩ := W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn (p := q)
    (hv.restrict _) (((innerSL ℝ).comp_memLp' hg).restrict _) (W1p.hasWeakFDerivOn v)
  have hT := (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))).isOpen.measurableSet
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [(ae_restrict_iff' hT).1 hwv] with x h1
    exact h1 trivial
  · filter_upwards [(ae_restrict_iff' hT).1 hwg] with x h1
    rw [h1 trivial, Function.comp_apply]
    exact (InnerProductSpace.toDual ℝ _).symm_apply_eq.2
      (ContinuousLinearMap.ext fun z => by simp [InnerProductSpace.toDual_apply_apply])

/-- A smooth compactly supported cutoff `ψ u` of `u ∈ W^{1,p}(ℝ^{n+1})`, `2 ≤ p < ∞`, lies in
`H¹(ℝ^{n+1})`, with weak gradient `ψ ∇u + u ∇ψ`. -/
private theorem exists_w1p_two_value_gradient_ae_eq_mul {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : 2 ≤ p)
    (hp : p ≠ ⊤) (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∃ w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ᵐ x, W1p.value w x = ψ x * W1p.value u x) ∧
        ∀ᵐ x, W1p.gradient w x = ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x := by
  obtain ⟨v, hv, hg⟩ := W1p.exists_top_value_gradient_ae_eq_mul_sub_const hp u hψ hψc
    (subset_univ _) 0
  simp only [sub_zero] at hv hg
  have hK : volume (tsupport ψ) ≠ ⊤ := hψc.isCompact.measure_lt_top.ne
  -- Both components vanish off the compact support of `ψ`, so they are square integrable.
  have hv2 : MemLp (W1p.value v : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 volume :=
    (((W1p.memLp_value v).ae_eq hv).mono_exponent_of_measure_support_ne_top
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]) hK hp2).ae_eq
      (EventuallyEq.symm hv)
  have hg2 : MemLp (W1p.gradient v : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 volume :=
    (((W1p.memLp_gradient v).ae_eq hg).mono_exponent_of_measure_support_ne_top
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx,
        gradient_of_notMem_tsupport hx]) hK hp2).ae_eq (EventuallyEq.symm hg)
  obtain ⟨w, hwv, hwg⟩ := exists_w1p_value_gradient_ae_eq v hv2 hg2
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hwv, hv] with x h1 h2
    rw [h1, h2]
  · filter_upwards [hwg, hg] with x h1 h2
    rw [h1, h2]

/-- Applying a measurable field of operators to a measurable field of vectors. -/
private theorem aestronglyMeasurable_clm_apply
    {T : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    (hT : AEStronglyMeasurable T volume)
    {v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hv : AEStronglyMeasurable v volume) : AEStronglyMeasurable (fun x => T x (v x)) volume :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hT.prodMk hv)

/-- The terms of the equation of a cutoff `ψ u` of `u ∈ W^{1,p}(ℝ^{n+1})`, `2 ≤ p`, are square
integrable: the products of `ψ` or `∇ψ` with `u`, `∇u` and the data `f, G ∈ Lᵖ`. Here `T x` is the
matrix `a x` acting on Euclidean space, bounded by `Λ`. -/
private theorem memLp_two_cutoff_terms {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : 2 ≤ p)
    {T : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1))}
    (hT : AEStronglyMeasurable T volume) {Lam : ℝ} (hTb : ∀ x v, ‖T x v‖ ≤ Lam * ‖v‖)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G p volume) (hf : MemLp f p volume)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    MemLp (fun x => ψ x • T x (W1p.gradient u x)) 2 volume ∧
      MemLp (fun x => W1p.value u x • T x (∇ ψ x)) 2 volume ∧
      MemLp (fun x => ψ x * W1p.value u x) 2 volume ∧
      MemLp (fun x => ⟪T x (W1p.gradient u x), ∇ ψ x⟫_ℝ) 2 volume ∧
      MemLp (fun x => ψ x * f x) 2 volume ∧ MemLp (fun x => ψ x • G x) 2 volume ∧
      MemLp (fun x => ⟪G x, ∇ ψ x⟫_ℝ) 2 volume := by
  obtain ⟨M, hM0, hψM, hgψM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hψc
  have hK := hψc.isCompact
  have hψ0 : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hgψ0 : ∀ x ∉ tsupport ψ, ∇ ψ x = 0 := fun x hx => gradient_of_notMem_tsupport hx
  have hψm : AEStronglyMeasurable ψ volume := hψ.continuous.aestronglyMeasurable
  have hgψm : AEStronglyMeasurable (∇ ψ) volume :=
    (hψ.continuous_gradient (by simp)).aestronglyMeasurable
  have hum := (W1p.memLp_value u).aestronglyMeasurable
  have hgum := (W1p.memLp_gradient u).aestronglyMeasurable
  have hLam : 0 ≤ Lam := by
    obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin (n + 1)))
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hTb 0 v)) (norm_pos_iff.2 hv)
  refine ⟨(memLp_two_of_norm_le_mul hp2 (hψm.smul (aestronglyMeasurable_clm_apply hT hgum))
      (W1p.memLp_gradient u) (C := M * Lam) (fun x => ?_) hK fun x hx => by simp [hψ0 x hx]).2,
    (memLp_two_of_norm_le_mul hp2 (hum.smul (aestronglyMeasurable_clm_apply hT hgψm))
      (W1p.memLp_value u) (C := Lam * M) (fun x => ?_) hK fun x hx => by simp [hgψ0 x hx]).2,
    (memLp_two_of_norm_le_mul hp2 (hψm.mul hum) (W1p.memLp_value u) (C := M) (fun x => ?_) hK
      fun x hx => by simp [hψ0 x hx]).2,
    (memLp_two_of_norm_le_mul hp2 ((aestronglyMeasurable_clm_apply hT hgum).inner hgψm)
      (W1p.memLp_gradient u) (C := Lam * M) (fun x => ?_) hK fun x hx => by simp [hgψ0 x hx]).2,
    (memLp_two_of_norm_le_mul hp2 (hψm.mul hf.aestronglyMeasurable) hf (C := M) (fun x => ?_) hK
      fun x hx => by simp [hψ0 x hx]).2,
    (memLp_two_of_norm_le_mul hp2 (hψm.smul hG.aestronglyMeasurable) hG (C := M) (fun x => ?_) hK
      fun x hx => by simp [hψ0 x hx]).2,
    (memLp_two_of_norm_le_mul hp2 (hG.aestronglyMeasurable.inner hgψm) hG (C := M)
      (fun x => ?_) hK fun x hx => by simp [hgψ0 x hx]).2⟩
  · simp only [Pi.smul_apply']
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul (hψM x) (hTb x _) (norm_nonneg _) hM0
  · simp only [Pi.smul_apply']
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hTb x _).trans (mul_le_mul_of_nonneg_left (hgψM x) hLam))
      (norm_nonneg _)
  · simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hψM x) (norm_nonneg _)
  · calc ‖⟪T x (W1p.gradient u x), ∇ ψ x⟫_ℝ‖ ≤ ‖T x (W1p.gradient u x)‖ * ‖∇ ψ x‖ :=
          norm_inner_le_norm _ _
      _ ≤ (Lam * ‖W1p.gradient u x‖) * M := mul_le_mul (hTb x _) (hgψM x) (norm_nonneg _)
          (by positivity)
      _ = Lam * M * ‖W1p.gradient u x‖ := by ring
  · simp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hψM x) (norm_nonneg _)
  · simp only [Pi.smul_apply']
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hψM x) (norm_nonneg _)
  · calc ‖⟪G x, ∇ ψ x⟫_ℝ‖ ≤ ‖G x‖ * ‖∇ ψ x‖ := norm_inner_le_norm _ _
      _ ≤ ‖G x‖ * M := mul_le_mul_of_nonneg_left (hgψM x) (norm_nonneg _)
      _ = M * ‖G x‖ := mul_comm _ _

/-- Each test function and its gradient are square integrable. -/
private theorem memLp_two_testFunction (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    MemLp (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) 2 volume ∧
      MemLp (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) 2 volume :=
  ⟨φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport,
    (φ.contDiff.continuous_gradient (by simp)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro φ.hasCompactSupport.isCompact fun _ hx =>
        gradient_of_notMem_tsupport hx)⟩

/-- The pairings into which the equations of `u` and of its cutoff `ψ u` split, tested against a
test function `φ`, are integrable. -/
private theorem integrable_cutoff_pairings {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : 2 ≤ p)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G p volume) (hf : MemLp f p volume)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    Integrable (fun x => ⟪ψ x • toEuclideanCLM (𝕜 := ℝ) (a x) (W1p.gradient u x),
      ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) ∧
    Integrable (fun x => ⟪W1p.value u x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x),
      ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) ∧
    Integrable (fun x => ψ x * W1p.value u x * φ x) ∧
    Integrable (fun x => ⟪toEuclideanCLM (𝕜 := ℝ) (a x) (W1p.gradient u x), ∇ ψ x⟫_ℝ * φ x) ∧
    Integrable (fun x => ψ x * f x * φ x) ∧
    Integrable (fun x => ⟪ψ x • G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) ∧
    Integrable (fun x => ⟪G x, ∇ ψ x⟫_ℝ * φ x) := by
  have hTb : ∀ x v, ‖toEuclideanCLM (𝕜 := ℝ) (a x) v‖ ≤ Lam * ‖v‖ := fun x v =>
    (norm_toEuclideanCLM_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (hell.opNorm_matrixBilinearForm_le (mem_univ x)) (norm_nonneg v))
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := memLp_two_cutoff_terms hp2
    (aestronglyMeasurable_toEuclideanCLM_iff.2 ham) hTb u hG hf hψ hψc
  obtain ⟨hφ2, hgφ2⟩ := memLp_two_testFunction φ
  exact ⟨i1.integrable_inner_of_holderConjugate (𝕜 := ℝ) hgφ2,
    i2.integrable_inner_of_holderConjugate (𝕜 := ℝ) hgφ2, i3.integrable_mul hφ2,
    i4.integrable_mul hφ2, i5.integrable_mul hφ2,
    i6.integrable_inner_of_holderConjugate (𝕜 := ℝ) hgφ2, i7.integrable_mul hφ2⟩

/-- **The equation of `u` tested against `ψ φ`**, split into the pairings of
`integrable_cutoff_pairings`: since `∇(ψ φ) = ψ ∇φ + φ ∇ψ`,

`∫ ⟪ψ a ∇u, ∇φ⟫ + ∫ ⟪a ∇u, ∇ψ⟫ φ + κ ∫ ψ u φ = ∫ ψ f φ + ∫ ⟪ψ G, ∇φ⟫ + ∫ ⟪G, ∇ψ⟫ φ`. -/
private theorem integral_eq_of_cutoff_test {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : 2 ≤ p)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G p volume) (hf : MemLp f p volume)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) {κ : ℝ}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f x * φ x) + ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) :
    (∫ x, ⟪ψ x • toEuclideanCLM (𝕜 := ℝ) (a x) (W1p.gradient u x),
      ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
      (∫ x, ⟪toEuclideanCLM (𝕜 := ℝ) (a x) (W1p.gradient u x), ∇ ψ x⟫_ℝ * φ x) +
        κ * (∫ x, ψ x * W1p.value u x * φ x) =
      (∫ x, ψ x * f x * φ x) +
        (∫ x, ⟪ψ x • G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x, ⟪G x, ∇ ψ x⟫_ℝ * φ x := by
  obtain ⟨j1, -, j3, j4, -, j6, j7⟩ := integrable_cutoff_pairings hp2 ham hell u hG hf hψ hψc φ
  set gφ := ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
  set gu : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  let χ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ) :=
    ⟨fun x => ψ x * φ x, hψ.mul φ.contDiff, hψc.mul_right, subset_univ _⟩
  have hχ : (χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) = fun x => ψ x * φ x := TestFunction.coe_mk
  have hgχ : ∀ x, ∇ (χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x = ψ x • gφ x + φ x • ∇ ψ x :=
    fun x => by
      rw [hχ]
      simpa only [conj_trivial] using gradient_fun_mul (hψ.differentiable (by simp) x)
        (φ.contDiff.differentiable (by simp) x)
  have heq := hu χ
  rw [energyFormIntegral_def] at heq
  have hL : ∫ x, energyIntegrand (a x) ((0 : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) x) κ (jetField u x)
        ((χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x,
          ∇ (χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x) =
      ∫ x, (⟪ψ x • toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), gφ x⟫_ℝ +
        ⟪toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), ∇ ψ x⟫_ℝ * φ x +
          κ * (ψ x * W1p.value u x * φ x)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [energyIntegrand_apply, jetField_apply, hgχ x]
    simp only [driftForm_apply, massForm_apply, Pi.zero_apply, inner_zero_left, zero_mul,
      add_zero, hχ, matrixBilinearForm_eq_inner_toEuclideanCLM, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real, gu]
    ring
  have hR : (∫ x, f x * (χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x) +
      ∫ x, ⟪G x, ∇ (χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ =
      (∫ x, ψ x * f x * φ x) + ∫ x, (⟪ψ x • G x, gφ x⟫_ℝ + ⟪G x, ∇ ψ x⟫_ℝ * φ x) := by
    congr 1
    · exact integral_congr_ae (ae_of_all _ fun x => by simp only [hχ]; ring)
    · refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hgχ, inner_add_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      ring
  have j14 : Integrable (fun x => ⟪ψ x • toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), gφ x⟫_ℝ +
      ⟪toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), ∇ ψ x⟫_ℝ * φ x) := j1.add j4
  rw [hL, hR, integral_add j14 (j3.const_mul κ), integral_add j1 j4, integral_const_mul,
    integral_add j6 j7] at heq
  rw [heq, add_assoc]

/-- **The equation of a cutoff of a `W^{1,p}` solution.** Let `u ∈ W^{1,p}(ℝ^{n+1})`, `2 ≤ p`,
solve `-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G` with `f, G ∈ Lᵖ`, and let `w ∈ H¹(ℝ^{n+1})` be the cutoff
`ψ u` of `u` by a smooth compactly supported `ψ`, with weak gradient `ψ ∇u + u ∇ψ`. Then `w`
solves the same equation with the scalar datum `ψ f + ⟨G, ∇ψ⟩ - ⟨a ∇u, ∇ψ⟩` and the divergence
datum `ψ G + u a ∇ψ`. -/
private theorem energyFormH1_eq_of_cutoff {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp2 : 2 ≤ p)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G p volume) (hf : MemLp f p volume)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) {κ : ℝ}
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f x * φ x) + ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hwv : ∀ᵐ x, W1p.value w x = ψ x * W1p.value u x)
    (hwg : ∀ᵐ x, W1p.gradient w x = ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) :
    energyFormH1 a 0 (fun _ => κ) w (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      (∫ x, (ψ x * f x + ⟪G x, ∇ ψ x⟫_ℝ -
          matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) * φ x) +
        ∫ x, ⟪ψ x • G x + W1p.value u x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x),
          ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  obtain ⟨j1, j2, j3, j4, j5, j6, j7⟩ :=
    integrable_cutoff_pairings hp2 ham hell u hG hf hψ hψc φ
  have heq := integral_eq_of_cutoff_test hp2 ham hell u hG hf hψ hψc φ hu
  set gφ := ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
  set gu : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set vu : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := ⇑(W1p.value u)
  -- The energy form of `w`, by its value and gradient.
  have hlhs : energyFormH1 a 0 (fun _ => κ) w (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
      ∫ x, (⟪ψ x • toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), gφ x⟫_ℝ +
        ⟪vu x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x), gφ x⟫_ℝ + κ * (ψ x * vu x * φ x)) := by
    rw [energyFormH1_def]
    simp only [Opens.coe_top, Measure.restrict_univ]
    refine integral_congr_ae ?_
    filter_upwards [hwv, hwg, W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ,
      W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ] with x h1 h2 h3 h4
    simp only [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply,
      Pi.zero_apply, inner_zero_left, zero_mul, h1, h2, h3, h4,
      matrixBilinearForm_eq_inner_toEuclideanCLM, map_add, map_smul, inner_smul_left,
      RCLike.conj_to_real, gu, vu, gφ]
    ring
  have hrhs : ∫ x, (ψ x * f x + ⟪G x, ∇ ψ x⟫_ℝ -
      matrixBilinearForm (a x) (∇ ψ x) (gu x)) * φ x =
      ∫ x, (ψ x * f x * φ x + ⟪G x, ∇ ψ x⟫_ℝ * φ x -
        ⟪toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), ∇ ψ x⟫_ℝ * φ x) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [matrixBilinearForm_eq_inner_toEuclideanCLM]
    ring
  have hrhs' : ∫ x, ⟪ψ x • G x + vu x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x), gφ x⟫_ℝ =
      ∫ x, (⟪ψ x • G x, gφ x⟫_ℝ + ⟪vu x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x), gφ x⟫_ℝ) :=
    integral_congr_ae (ae_of_all _ fun x => inner_add_left _ _ _)
  have j12 : Integrable (fun x => ⟪ψ x • toEuclideanCLM (𝕜 := ℝ) (a x) (gu x), gφ x⟫_ℝ +
      ⟪vu x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x), gφ x⟫_ℝ) := j1.add j2
  have j57 : Integrable (fun x => ψ x * f x * φ x + ⟪G x, ∇ ψ x⟫_ℝ * φ x) := j5.add j7
  rw [hlhs, hrhs, hrhs', integral_add j12 (j3.const_mul κ), integral_add j1 j2,
    integral_const_mul, integral_sub j57 j4, integral_add j5 j7, integral_add j6 j2]
  linarith

/-! ### The estimate for solutions in `W^{1,p}(ℝ^{n+1})` -/

/-- The `Lᵖ` seminorms of `g` on the balls `B(0, k + 1)` increase to its `Lᵖ` seminorm. -/
private theorem tendsto_eLpNorm_restrict_ball {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞}
    {g : EuclideanSpace ℝ (Fin (n + 1)) → F} (hg : AEStronglyMeasurable g volume) :
    Tendsto (fun k : ℕ => eLpNorm g p (volume.restrict (ball 0 ((k : ℝ) + 1)))) atTop
      (𝓝 (eLpNorm g p volume)) := by
  set s : ℕ → Set (EuclideanSpace ℝ (Fin (n + 1))) := fun k => ball 0 ((k : ℝ) + 1)
  have hs : Monotone s := fun k l hkl => ball_subset_ball (by gcongr)
  have hmono : Monotone fun k => eLpNorm g p (volume.restrict (s k)) := fun k l hkl =>
    eLpNorm_mono_measure _ (Measure.restrict_mono (hs hkl) le_rfl)
  convert tendsto_atTop_iSup hmono
  -- `‖g‖ₑ` is the increasing limit of its cutoffs to the balls.
  have hsup : (fun x => ‖g x‖ₑ) = fun x => ⨆ k, (s k).indicator (fun x => ‖g x‖ₑ) x := by
    funext x
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine le_antisymm (le_iSup_of_le N ?_) (iSup_le fun k => indicator_le_self _ _ x)
    rw [indicator_of_mem (mem_ball_zero_iff.2 (by linarith))]
  rw [← eLpNorm_eNorm g hg, hsup, eLpNorm_iSup_eq_iSup_eLpNorm
    (fun k => hg.eNorm.indicator measurableSet_ball)
    (ae_of_all _ fun x k l hkl => indicator_le_indicator_of_subset (hs hkl) (fun _ => bot_le) x)]
  congr 1
  funext k
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet,
    eLpNorm_eNorm g hg.restrict]

/-- If on every ball `B(0, R)` the sum `‖g₁‖_{Lᵖ(B)} + s ‖g₂‖_{Lᵖ(B)}` is at most `A + B / R`
with `s, B < ∞`, then `‖g₁‖_{Lᵖ} + s ‖g₂‖_{Lᵖ} ≤ A`. -/
private theorem add_mul_eLpNorm_le_of_forall_restrict_ball_le {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedAddCommGroup F₂] {p : ℝ≥0∞}
    {g₁ : EuclideanSpace ℝ (Fin (n + 1)) → F₁} {g₂ : EuclideanSpace ℝ (Fin (n + 1)) → F₂}
    (hg₁ : AEStronglyMeasurable g₁ volume) (hg₂ : AEStronglyMeasurable g₂ volume)
    {s A B : ℝ≥0∞} (hs : s ≠ ⊤) (hB : B ≠ ⊤)
    (h : ∀ R : ℝ, 0 < R → eLpNorm g₁ p (volume.restrict (ball 0 R)) +
      s * eLpNorm g₂ p (volume.restrict (ball 0 R)) ≤ A + ENNReal.ofReal R⁻¹ * B) :
    eLpNorm g₁ p volume + s * eLpNorm g₂ p volume ≤ A := by
  have h0 : Tendsto (fun k : ℕ => ENNReal.ofReal ((k : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (by simpa only [one_div] using
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim : Tendsto (fun k : ℕ => A + ENNReal.ofReal ((k : ℝ) + 1)⁻¹ * B) atTop (𝓝 A) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (ENNReal.Tendsto.mul_const h0 (Or.inr hB))
  exact le_of_tendsto_of_tendsto' ((tendsto_eLpNorm_restrict_ball hg₁).add
    (ENNReal.Tendsto.const_mul (tendsto_eLpNorm_restrict_ball hg₂) (Or.inr hs))) hlim
    fun k => h _ (by positivity)

/-- The data of the equation of a cutoff `ψ u`, where `|ψ| ≤ 1` and `‖∇ψ‖ ≤ N`, are bounded in `Lᵖ`
by the data of `u` and by `N` times the `Lᵖ` norms of `u` and `∇u`. -/
private theorem eLpNorm_cutoff_data_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : AEStronglyMeasurable G volume)
    (hf : AEStronglyMeasurable f volume) {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψ1 : ∀ x, |ψ x| ≤ 1) {N : ℝ} (hN : ∀ x, ‖∇ ψ x‖ ≤ N) :
    eLpNorm (fun x => ψ x • G x + W1p.value u x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x)) p
        volume ≤ eLpNorm G p volume +
          ENNReal.ofReal (N * Lam) * eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p
            volume ∧
      eLpNorm (fun x => ψ x * f x + ⟪G x, ∇ ψ x⟫_ℝ -
          matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) p volume ≤
        eLpNorm f p volume + ENNReal.ofReal N * eLpNorm G p volume +
          ENNReal.ofReal (N * Lam) * eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
            EuclideanSpace ℝ (Fin (n + 1))) p volume := by
  have hp1 : 1 ≤ p := Fact.out
  have hLam := hell.upper_nonneg
  have hTb : ∀ x v, ‖toEuclideanCLM (𝕜 := ℝ) (a x) v‖ ≤ Lam * ‖v‖ := fun x v =>
    (norm_toEuclideanCLM_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (hell.opNorm_matrixBilinearForm_le (mem_univ x)) (norm_nonneg v))
  have hψm := hψ.continuous.aestronglyMeasurable (μ := volume)
  have hgψm := (hψ.continuous_gradient (by simp)).aestronglyMeasurable (μ := volume)
  have hgum := (W1p.memLp_gradient u).aestronglyMeasurable
  refine ⟨(eLpNorm_add_le (f := fun x => ψ x • G x)
      (g := fun x => W1p.value u x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x)) hp1).trans
      (add_le_add (eLpNorm_mono (hψm.smul hG) fun x => ?_)
        (eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((W1p.memLp_value u).aestronglyMeasurable.smul
          (aestronglyMeasurable_clm_apply (aestronglyMeasurable_toEuclideanCLM_iff.2 ham) hgψm))
          (ae_of_all _ fun x => ?_) p)),
    (eLpNorm_sub_le (f := fun x => ψ x * f x + ⟪G x, ∇ ψ x⟫_ℝ)
      (g := fun x => matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x)) hp1).trans
      (add_le_add ((eLpNorm_add_le (f := fun x => ψ x * f x)
        (g := fun x => ⟪G x, ∇ ψ x⟫_ℝ) hp1).trans
        (add_le_add (eLpNorm_mono (hψm.mul hf) fun x => ?_)
          (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hG.inner hgψm) (ae_of_all _ fun x => ?_) p)))
        (eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ (ae_of_all _ fun x => ?_) p))⟩
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψ1 x)
  · simp only [Pi.smul_apply']
    rw [norm_smul, mul_comm (N * Lam), mul_comm N]
    exact mul_le_mul_of_nonneg_left ((hTb x _).trans
      (mul_le_mul_of_nonneg_left (hN x) hLam)) (norm_nonneg _)
  · rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hψ1 x)
  · exact (norm_inner_le_norm _ _).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hN x) (norm_nonneg _))
  · exact ((aestronglyMeasurable_clm_apply (aestronglyMeasurable_toEuclideanCLM_iff.2 ham)
      hgum).inner hgψm).congr (ae_of_all _ fun x =>
        (matrixBilinearForm_eq_inner_toEuclideanCLM _ _ _).symm)
  · rw [matrixBilinearForm_eq_inner_toEuclideanCLM]
    refine (norm_inner_le_norm _ _).trans ?_
    calc ‖toEuclideanCLM (𝕜 := ℝ) (a x) (W1p.gradient u x)‖ * ‖∇ ψ x‖ ≤
          (Lam * ‖W1p.gradient u x‖) * N :=
          mul_le_mul (hTb x _) (hN x) (norm_nonneg _) (by positivity)
      _ = N * Lam * ‖W1p.gradient u x‖ := by ring

/-- If the cutoff `ψ` is `1` on the closed ball `closedBall 0 R`, then `w = ψ u` and its gradient
`ψ ∇u + u ∇ψ` agree with `u` and `∇u` on `B(0, R)`, so the `Lᵖ` norms of `u` and `∇u` on
`B(0, R)` are at most those of `w` and `∇w`. -/
private theorem eLpNorm_restrict_ball_le_of_eqOn_one {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) q}
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {R : ℝ} (hψ1 : EqOn ψ 1 (closedBall 0 R))
    (hwv : ∀ᵐ x, W1p.value w x = ψ x * W1p.value u x)
    (hwg : ∀ᵐ x, W1p.gradient w x = ψ x • W1p.gradient u x + W1p.value u x • ∇ ψ x) :
    eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) p
        (volume.restrict (ball 0 R)) ≤ eLpNorm (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) p volume ∧
      eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p (volume.restrict (ball 0 R)) ≤
        eLpNorm (W1p.value w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume := by
  have hball : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R, ψ x = 1 ∧ ∇ ψ x = 0 :=
    fun x hx => by
      have hev : ψ =ᶠ[𝓝 x] fun _ => (1 : ℝ) := Filter.mem_of_superset
        (isOpen_ball.mem_nhds hx) fun y hy => hψ1 (ball_subset_closedBall hy)
      exact ⟨hev.eq_of_nhds, by rw [_root_.gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]⟩
  refine ⟨(eLpNorm_congr_ae ?_).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self),
    (eLpNorm_congr_ae ?_).trans_le (eLpNorm_mono_measure _ Measure.restrict_le_self)⟩
  · rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [hwg] with x hx hxB
    rw [hx, (hball x hxB).1, (hball x hxB).2, one_smul, smul_zero, add_zero]
  · rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
    filter_upwards [hwv] with x hx hxB
    rw [hx, (hball x hxB).1, one_mul]

/-- **The estimate on a ball.** Assume the estimate for `H¹` solutions with the constant `C`. For a
solution `u ∈ W^{1,p}(ℝ^{n+1})` with data in `Lᵖ` and every `R > 0`, the norms of `∇u` and `u` on
`B(0, R)` satisfy the estimate up to an error `B / R`, where `B` does not depend on `R`. -/
private theorem eLpNorm_restrict_ball_add_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 < p)
    (hp_top : p ≠ ⊤)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) {C : ℝ≥0}
    (hest : ∀ (w : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
      (G' : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      (f' : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G' 2 volume → MemLp f' 2 volume →
      (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
        energyFormH1 a 0 (fun _ => κ) w (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
          ∫ x, f' x * φ x ∂volume +
            ∫ x, ⟪G' x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume) →
      MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        p volume →
      eLpNorm (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) p volume +
        ENNReal.ofReal √κ * eLpNorm (W1p.value w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
        C * (eLpNorm G' p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f' p volume))
    {c : ℝ} (hcut : ∀ {R : ℝ}, 0 < R → ∃ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, |ψ x| ≤ 1) ∧ EqOn ψ 1 (closedBall 0 R) ∧
        ∀ x, ‖∇ ψ x‖ ≤ c / R)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG : MemLp G p volume) (hf : MemLp f p volume)
    (hu : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f x * φ x) + ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    {R : ℝ} (hR : 0 < R) :
    eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) p
        (volume.restrict (ball 0 R)) + ENNReal.ofReal √κ *
          eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p
            (volume.restrict (ball 0 R)) ≤
      C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume) +
        ENNReal.ofReal R⁻¹ * (C * (ENNReal.ofReal (c * Lam) *
          eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume +
          ENNReal.ofReal (√κ)⁻¹ * (ENNReal.ofReal c * eLpNorm G p volume +
            ENNReal.ofReal (c * Lam) * eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1))) p volume))) := by
  have hum := W1p.memLp_value u
  have hgum := W1p.memLp_gradient u
  obtain ⟨ψ, hψ, hψc, hψ01, hψ1, hgψ⟩ := hcut hR
  obtain ⟨w, hwv, hwg⟩ := exists_w1p_two_value_gradient_ae_eq_mul hp.le hp_top u hψ hψc
  have hTb : ∀ x v, ‖toEuclideanCLM (𝕜 := ℝ) (a x) v‖ ≤ Lam * ‖v‖ := fun x v =>
    (norm_toEuclideanCLM_apply_le _ _).trans
      (mul_le_mul_of_nonneg_right (hell.opNorm_matrixBilinearForm_le (mem_univ x)) (norm_nonneg v))
  obtain ⟨-, i2, -, i4, i5, i6, i7⟩ := memLp_two_cutoff_terms hp.le
    (aestronglyMeasurable_toEuclideanCLM_iff.2 ham) hTb u hG hf hψ hψc
  -- The gradient `ψ ∇u + u ∇ψ` of `w = ψ u` lies in `Lᵖ`.
  have hgw : MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) p volume := by
    refine (MemLp.add (hgum.of_le_mul (c := 1)
      (hψ.continuous.aestronglyMeasurable.smul hgum.aestronglyMeasurable) (ae_of_all _ fun x => ?_))
      (hum.of_le_mul (c := c / R) (hum.aestronglyMeasurable.smul
        (hψ.continuous_gradient (by simp)).aestronglyMeasurable) (ae_of_all _ fun x => ?_))).ae_eq
      (EventuallyEq.symm hwg)
    · simp only [Pi.smul_apply', norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hψ01 x) (norm_nonneg _)
    · simp only [Pi.smul_apply', norm_smul, Real.norm_eq_abs]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hgψ x) (abs_nonneg _)
  -- The estimate for `w`, which solves the equation with the data of `eLpNorm_cutoff_data_le`.
  have key := hest w (fun x => ψ x • G x + W1p.value u x • toEuclideanCLM (𝕜 := ℝ) (a x) (∇ ψ x))
    (fun x => ψ x * f x + ⟪G x, ∇ ψ x⟫_ℝ - matrixBilinearForm (a x) (∇ ψ x) (W1p.gradient u x))
    (i6.add i2) (((i5.add i7).sub i4).ae_eq (ae_of_all _ fun x => by
      simp only [Pi.add_apply, Pi.sub_apply, matrixBilinearForm_eq_inner_toEuclideanCLM]))
    (fun φ => energyFormH1_eq_of_cutoff hp.le ham hell u hG hf hψ hψc φ hu hwv hwg) hgw
  obtain ⟨hloc₁, hloc₂⟩ := eLpNorm_restrict_ball_le_of_eqOn_one u hψ1 hwv hwg
  obtain ⟨hG'b, hf'b⟩ := eLpNorm_cutoff_data_le ham hell u hG.aestronglyMeasurable
    hf.aestronglyMeasurable hψ hψ01 hgψ
  have e : ∀ b : ℝ, ENNReal.ofReal (c / R * b) = ENNReal.ofReal R⁻¹ * ENNReal.ofReal (c * b) :=
    fun b => by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hR.le)]
      congr 1
      ring
  calc _ ≤ _ := add_le_add hloc₁ (by gcongr)
    _ ≤ _ := key
    _ ≤ C * ((eLpNorm G p volume + ENNReal.ofReal (c / R * Lam) *
          eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume) +
          ENNReal.ofReal (√κ)⁻¹ * (eLpNorm f p volume + ENNReal.ofReal (c / R * 1) *
            eLpNorm G p volume + ENNReal.ofReal (c / R * Lam) *
              eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
                EuclideanSpace ℝ (Fin (n + 1))) p volume)) := by
        rw [mul_one]
        gcongr
    _ = _ := by
        rw [e Lam, e 1, mul_one]
        ring

/-- **Krylov's estimate with a zero-order shift for solutions in `W^{1,p}`.** Let `2 < p < ∞` and
`0 < λ ≤ Λ`. There are constants `C` and `δ > 0`, depending only on `n`, `p`, `λ` and `Λ`, with the
following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`, uniformly elliptic
with constants `λ, Λ`, such that on every ball `B` of radius at most `r₀` some constant matrix `A`,
uniformly elliptic with the same constants, has mean deviation `⨍_B ‖a - A‖ ≤ δ` from `a`. Let
`κ ≥ 16 / r₀²` and let `u ∈ W^{1,p}(ℝ^{n+1})` solve

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

in the sense of distributions, with `f, G ∈ Lᵖ`. Then

`‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`.

Neither `u` nor the data need be square integrable. The constants are those of the estimate for
solutions in `H¹(ℝ^{n+1})`,
`TauCeti.PDE.exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le`. Applied to
the difference of two solutions with the same data, it shows that the equation has at most one
solution in `W^{1,p}(ℝ^{n+1})`; see
`TauCeti.PDE.existsUnique_forall_energyFormIntegral_eq_of_vmoModulus_le`. -/
theorem exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_forall_energyFormIntegral_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {r₀ κ : ℝ}, 0 < r₀ → 16 / r₀ ^ 2 ≤ κ → AEStronglyMeasurable a volume →
        UniformlyEllipticOn univ a lam Lam →
        (∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ), 0 < r → r ≤ r₀ →
          ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            UniformlyEllipticOn (ball c r) (fun _ => A) lam Lam ∧
              ⨍ x in ball c r, ‖matrixBilinearForm (a x) - matrixBilinearForm A‖ ≤ δ) →
        ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
          (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G p volume → MemLp f p volume →
          (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
            energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
                (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
              (∫ x, f x * φ x) +
                ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
          eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
              EuclideanSpace ℝ (Fin (n + 1))) p volume +
            ENNReal.ofReal √κ *
              eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
            C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume) := by
  obtain ⟨C, δ, hδ, hest⟩ :=
    exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_setAverage_le (n := n) hp hp_top
      lam Lam
  obtain ⟨c, -, hcut⟩ := exists_forall_contDiff_cutoff_ball (E := EuclideanSpace ℝ (Fin (n + 1)))
  -- Cutoffs equal to `1` on `closedBall 0 R`, supported in `B(0, 2R)`, with `‖∇ψ‖ ≤ c / R`.
  have hcut' : ∀ {R : ℝ}, 0 < R → ∃ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ x, |ψ x| ≤ 1) ∧ EqOn ψ 1 (closedBall 0 R) ∧
        ∀ x, ‖∇ ψ x‖ ≤ c / R := fun {R} hR => by
    obtain ⟨ψ, hψ, hψc, hψr, hψ1, -, hgψ⟩ := hcut 0 hR.le (show R < 2 * R by linarith)
    refine ⟨ψ, hψ, hψc, fun x => abs_le.2 ⟨by linarith [(hψr ⟨x, rfl⟩).1], (hψr ⟨x, rfl⟩).2⟩,
      hψ1, fun x => (hgψ x).trans_eq (by rw [show 2 * R - R = R by ring])⟩
  refine ⟨C, δ, hδ, fun {a r₀ κ} hr₀ hκ ham hell hosc u G f hG hf hu => ?_⟩
  have hum := W1p.memLp_value u
  have hgum := W1p.memLp_gradient u
  refine add_mul_eLpNorm_le_of_forall_restrict_ball_le hgum.aestronglyMeasurable
    hum.aestronglyMeasurable ENNReal.ofReal_ne_top ?_ fun R hR =>
      eLpNorm_restrict_ball_add_le hp hp_top ham hell (hest hr₀ hκ ham hell hosc) hcut' u hG hf
        hu hR
  have := hum.eLpNorm_ne_top
  have := hgum.eLpNorm_ne_top
  have := hG.eLpNorm_ne_top
  finiteness

/-! ### Existence for data in `Lᵖ` -/

/-- For a test function `φ`, the left side of the weak formulation is a pairing of `∇u` and `u`
with fixed functions in `L^q`, `q` the Hölder conjugate exponent of `p`:
`∫ ⟨a ∇u, ∇φ⟩ + κ ∫ u φ = ∫ ⟪∇u, aᵀ ∇φ⟫ + κ ∫ ⟪u, φ⟫`, and both pairings are integrable. -/
private theorem energyFormIntegral_testFunction_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [p.HolderConjugate q]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam) (κ : ℝ)
    (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    MemLp (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ
        (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) q volume ∧
      MemLp (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) q volume ∧
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, ⟪W1p.gradient u x, toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ
          (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)⟫_ℝ) +
          κ * ∫ x, ⟪W1p.value u x, φ x⟫_ℝ := by
  have hgφ : MemLp (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) q volume :=
    (φ.contDiff.continuous_gradient (by simp)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro φ.hasCompactSupport.isCompact fun _ hx =>
        gradient_of_notMem_tsupport hx)
  have hφ : MemLp (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) q volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hT : AEStronglyMeasurable (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ) volume :=
    aestronglyMeasurable_toEuclideanCLM_iff.2
      ((continuous_id.matrix_transpose).comp_aestronglyMeasurable ham)
  have hh : MemLp (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ
      (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) q volume :=
    hgφ.of_le_mul (aestronglyMeasurable_clm_apply hT hgφ.aestronglyMeasurable)
      (ae_of_all _ fun x => (norm_toEuclideanCLM_apply_le _ _).trans
        (mul_le_mul_of_nonneg_right (hell.transpose.opNorm_matrixBilinearForm_le (mem_univ x))
          (norm_nonneg _)))
  refine ⟨hh, hφ, ?_⟩
  rw [energyFormIntegral_def, ← integral_const_mul, ← integral_add
    ((W1p.memLp_gradient u).integrable_inner_of_holderConjugate (𝕜 := ℝ) hh)
    (((W1p.memLp_value u).integrable_inner_of_holderConjugate (𝕜 := ℝ) hφ).const_mul κ)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [energyIntegrand_apply, jetField_apply, driftForm_apply, massForm_apply,
    Pi.zero_apply, inner_zero_left, zero_mul, add_zero]
  rw [← matrixBilinearForm_transpose_apply, matrixBilinearForm_eq_inner_toEuclideanCLM,
    real_inner_comm, RCLike.inner_apply, conj_trivial]
  ring

/-- The difference of two solutions solves the equation with the difference of the data. -/
private theorem forall_energyFormIntegral_sub {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    {u₁ u₂ : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p}
    {G₁ G₂ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG₁ : MemLp G₁ p volume)
    (hG₂ : MemLp G₂ p volume) (hf₁ : MemLp f₁ p volume) (hf₂ : MemLp f₂ p volume)
    (hu₁ : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u₁)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f₁ x * φ x) + ∫ x, ⟪G₁ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hu₂ : ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u₂)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f₂ x * φ x) + ∫ x, ⟪G₂ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    energyFormIntegral volume a 0 (fun _ => κ) (jetField (u₁ - u₂))
        (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
      (∫ x, (f₁ - f₂) x * φ x) +
        ∫ x, ⟪(G₁ - G₂) x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  have : Fact (1 ≤ (1 - p⁻¹)⁻¹) := ⟨by simp⟩
  have : p.HolderConjugate (1 - p⁻¹)⁻¹ := ENNReal.HolderConjugate.inv_one_sub_inv' Fact.out
  obtain ⟨hh, hφ, e⟩ :=
    energyFormIntegral_testFunction_eq (q := (1 - p⁻¹)⁻¹) ham hell κ (u₁ - u₂) φ
  obtain ⟨-, -, e₁⟩ := energyFormIntegral_testFunction_eq (q := (1 - p⁻¹)⁻¹) ham hell κ u₁ φ
  obtain ⟨-, -, e₂⟩ := energyFormIntegral_testFunction_eq (q := (1 - p⁻¹)⁻¹) ham hell κ u₂ φ
  have hgφq : MemLp (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) (1 - p⁻¹)⁻¹ volume :=
    (φ.contDiff.continuous_gradient (by simp)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro φ.hasCompactSupport.isCompact fun _ hx =>
        gradient_of_notMem_tsupport hx)
  have hT : volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
      Set (EuclideanSpace ℝ (Fin (n + 1)))) = volume := by simp
  have hv : ⇑(W1p.value (u₁ - u₂)) =ᵐ[volume] ⇑(W1p.value u₁) - ⇑(W1p.value u₂) := by
    simpa only [hT] using W1p.value_sub_ae u₁ u₂
  have hg : ⇑(W1p.gradient (u₁ - u₂)) =ᵐ[volume] ⇑(W1p.gradient u₁) - ⇑(W1p.gradient u₂) := by
    simpa only [hT] using W1p.gradient_sub_ae u₁ u₂
  have ig₁ := (W1p.memLp_gradient u₁).integrable_inner_of_holderConjugate (𝕜 := ℝ) hh
  have ig₂ := (W1p.memLp_gradient u₂).integrable_inner_of_holderConjugate (𝕜 := ℝ) hh
  have iv₁ := (W1p.memLp_value u₁).integrable_inner_of_holderConjugate (𝕜 := ℝ) hφ
  have iv₂ := (W1p.memLp_value u₂).integrable_inner_of_holderConjugate (𝕜 := ℝ) hφ
  have if₁ := hf₁.integrable_inner_of_holderConjugate (𝕜 := ℝ) hφ
  have if₂ := hf₂.integrable_inner_of_holderConjugate (𝕜 := ℝ) hφ
  have iG₁ := hG₁.integrable_inner_of_holderConjugate (𝕜 := ℝ) hgφq
  have iG₂ := hG₂.integrable_inner_of_holderConjugate (𝕜 := ℝ) hgφq
  have h₁ := hu₁ φ
  have h₂ := hu₂ φ
  rw [e₁] at h₁
  rw [e₂] at h₂
  have eg : ∫ x, ⟪W1p.gradient (u₁ - u₂) x, toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ
      (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)⟫_ℝ =
      (∫ x, ⟪W1p.gradient u₁ x, toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ
        (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)⟫_ℝ) -
      ∫ x, ⟪W1p.gradient u₂ x, toEuclideanCLM (𝕜 := ℝ) (a x)ᵀ
        (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)⟫_ℝ := by
    rw [← integral_sub ig₁ ig₂]
    exact integral_congr_ae (hg.mono fun x hx => by
      dsimp only
      rw [hx, Pi.sub_apply, inner_sub_left])
  have ev : ∫ x, ⟪W1p.value (u₁ - u₂) x, φ x⟫_ℝ =
      (∫ x, ⟪W1p.value u₁ x, φ x⟫_ℝ) - ∫ x, ⟪W1p.value u₂ x, φ x⟫_ℝ := by
    rw [← integral_sub iv₁ iv₂]
    exact integral_congr_ae (hv.mono fun x hx => by
      dsimp only
      rw [hx, Pi.sub_apply, inner_sub_left])
  rw [e, eg, ev]
  simp only [Pi.sub_apply, sub_mul, inner_sub_left]
  rw [integral_sub iG₁ iG₂, integral_sub (if₁.congr (ae_of_all _ fun x => by
      simp [RCLike.inner_apply, mul_comm])) (if₂.congr (ae_of_all _ fun x => by
      simp [RCLike.inner_apply, mul_comm]))]
  linarith

/-- The `Lᵖ` seminorm of `g` outside the ball `B(0, N + 1)` tends to `0` as `N → ∞`. -/
private theorem tendsto_eLpNorm_indicator_compl_ball {F : Type*} [NormedAddCommGroup F]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) {g : EuclideanSpace ℝ (Fin (n + 1)) → F} (hg : MemLp g p volume) :
    Tendsto (fun N : ℕ => eLpNorm ((ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      ((N : ℝ) + 1))ᶜ.indicator g) p volume) atTop (𝓝 0) := by
  have h := tendsto_eLpNorm_sub_of_ae_tendsto (m := volume) (l := atTop) (C := 1) hp
    (f := fun N : ℕ => (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((N : ℝ) + 1))ᶜ.indicator g)
    (g := 0) (Eventually.of_forall fun N =>
      hg.aestronglyMeasurable.indicator measurableSet_ball.compl) hg
    (Eventually.of_forall fun N => Eventually.of_forall fun x => by
      rw [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul]
      exact eNorm_indicator_le_eNorm_self _ x)
    (Eventually.of_forall fun x => tendsto_const_nhds.congr' <| by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      rw [Pi.zero_apply, indicator_of_notMem (show x ∉ (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
        ((k : ℝ) + 1))ᶜ from fun h => h (mem_ball_zero_iff.2 (by linarith)))])
  simpa only [sub_zero] using h

/-- For `N ≤ k, j`, the difference of the cutoffs of `g` to `B(0, k + 1)` and `B(0, j + 1)` is
pointwise bounded by the cutoff of `g` outside `B(0, N + 1)`. -/
private theorem norm_indicator_ball_sub_le {F : Type*} [NormedAddCommGroup F]
    (g : EuclideanSpace ℝ (Fin (n + 1)) → F) {N k j : ℕ} (hk : N ≤ k) (hj : N ≤ j)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖(ball 0 ((k : ℝ) + 1)).indicator g x - (ball 0 ((j : ℝ) + 1)).indicator g x‖ ≤
      ‖(ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((N : ℝ) + 1))ᶜ.indicator g x‖ := by
  by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((N : ℝ) + 1)
  · have hxk : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((k : ℝ) + 1) :=
      ball_subset_ball (by gcongr) hx
    have hxj : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((j : ℝ) + 1) :=
      ball_subset_ball (by gcongr) hx
    simp [indicator_of_mem hxk, indicator_of_mem hxj]
  · rw [indicator_of_mem (show x ∈ (ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
      ((N : ℝ) + 1))ᶜ from hx)]
    by_cases hxk : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((k : ℝ) + 1) <;>
      by_cases hxj : x ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) ((j : ℝ) + 1) <;>
      simp [hxk, hxj]

/-- A function in `W^{1,p}(ℝ^{n+1})` with the value and weak gradient of `u ∈ H¹(ℝ^{n+1})` has the
energy form of `u` against every test function. -/
private theorem energyFormIntegral_eq_energyFormH1 {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {κ : ℝ}
    {v : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p}
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hv : ∀ᵐ x, W1p.value v x = W1p.value u x) (hg : ∀ᵐ x, W1p.gradient v x = W1p.gradient u x)
    (φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ)) :
    energyFormIntegral volume a 0 (fun _ => κ) (jetField v)
        (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
      energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) := by
  rw [energyFormIntegral_def, energyFormH1_def]
  simp only [Opens.coe_top, Measure.restrict_univ]
  refine integral_congr_ae ?_
  filter_upwards [hv, hg, W1p.value_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ,
    W1p.gradient_ofTestFunctionₗ_top_ae (mu := volume) (p := 2) φ] with x h1 h2 h3 h4
  simp only [jetField_apply, h1, h2, h3, h4]

/-- **Distance of two solutions.** Given the estimate for solutions in `W^{1,p}(ℝ^{n+1})` with the
constant `C`, two solutions are at distance at most
`(κ^{-1/2} + 1) C (‖G₁ - G₂‖ + κ^{-1/2} ‖f₁ - f₂‖)` in `W^{1,p}`. -/
private theorem edist_le_of_forall_energyFormIntegral_eq {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (hκ : 0 < κ) {C : ℝ≥0}
    (hest : ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p)
      (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G p volume → MemLp f p volume →
      (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f x * φ x) + ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1))) p volume +
        ENNReal.ofReal √κ * eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
        C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume))
    {u₁ u₂ : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p}
    {G₁ G₂ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f₁ f₂ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG₁ : MemLp G₁ p volume)
    (hG₂ : MemLp G₂ p volume) (hf₁ : MemLp f₁ p volume) (hf₂ : MemLp f₂ p volume)
    (hu₁ : (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u₁)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f₁ x * φ x) + ∫ x, ⟪G₁ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ))
    (hu₂ : (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u₂)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f₂ x * φ x) + ∫ x, ⟪G₂ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)) :
    edist u₁ u₂ ≤ ((ENNReal.ofReal √κ)⁻¹ + 1) * C *
      (eLpNorm (G₁ - G₂) p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm (f₁ - f₂) p volume) := by
  have h := hest (u₁ - u₂) (G₁ - G₂) (f₁ - f₂) (hG₁.sub hG₂) (hf₁.sub hf₂)
    (forall_energyFormIntegral_sub ham hell hG₁ hG₂ hf₁ hf₂ hu₁ hu₂)
  set D := C * (eLpNorm (G₁ - G₂) p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm (f₁ - f₂) p volume)
  set s := ENNReal.ofReal √κ
  have hs0 : s ≠ 0 := (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hκ)).ne'
  have hT : volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
      Set (EuclideanSpace ℝ (Fin (n + 1)))) = volume := by simp
  have hTn : ∀ {F : Type _} [NormedAddCommGroup F] (g : EuclideanSpace ℝ (Fin (n + 1)) → F),
      eLpNorm g p (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))) = eLpNorm g p volume := fun g => by rw [hT]
  set v := eLpNorm (W1p.value (u₁ - u₂) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume
  have hv : v ≤ s⁻¹ * D := by
    calc v = s⁻¹ * (s * v) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hs0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ s⁻¹ * D := by gcongr; exact le_add_self.trans h
  rw [eDist_eq_eNorm_sub]
  calc ‖u₁ - u₂‖ₑ ≤ ‖W1p.value (u₁ - u₂)‖ₑ + ‖W1p.gradient (u₁ - u₂)‖ₑ :=
        W1p.enorm_le_enorm_value_add_enorm_gradient _
    _ ≤ s⁻¹ * D + D := by
        rw [Lp.eNorm_def, Lp.eNorm_def, hTn, hTn]
        exact add_le_add hv (le_self_add.trans h)
    _ = (s⁻¹ + 1) * C * (eLpNorm (G₁ - G₂) p volume +
          ENNReal.ofReal (√κ)⁻¹ * eLpNorm (f₁ - f₂) p volume) := by
        simp only [D]
        ring

/-- **Solutions for data in `L² ∩ Lᵖ`.** Given the `W^{1,p}` regularity of `H¹` solutions with
data in `L² ∩ Lᵖ`, the equation has a solution in `W^{1,p}(ℝ^{n+1})` for such data. -/
private theorem exists_forall_energyFormIntegral_eq_of_memLp_two {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    (hκ : 0 < κ)
    (hreg : ∀ (u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2)
      (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
      (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G 2 volume → MemLp f 2 volume →
      MemLp G p volume → MemLp f p volume →
      (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
        energyFormH1 a 0 (fun _ => κ) u (W1p.ofTestFunctionₗ volume ⊤ 2 φ) =
          ∫ x, f x * φ x ∂volume +
            ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ ∂volume) →
      MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          p volume ∧
        MemLp (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hG2 : MemLp G 2 volume) (hf2 : MemLp f 2 volume)
    (hG : MemLp G p volume) (hf : MemLp f p volume) :
    ∃ u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p,
    (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f x * φ x) + ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) := by
  obtain ⟨u, hu, -⟩ := hell.existsUnique_forall_energyFormH1_eq_of_pos ham hκ hG2 hf2
  obtain ⟨hgp, hvp⟩ := hreg u G f hG2 hf2 hG hf hu
  obtain ⟨v, hv, hg⟩ := exists_w1p_value_gradient_ae_eq (q := p) u hvp hgp
  exact ⟨v, fun φ => (energyFormIntegral_eq_energyFormH1 hv hg φ).trans (hu φ)⟩

/-- **Passing to the limit in the equation.** If `uₖ → u` in `W^{1,p}(ℝ^{n+1})`, each `uₖ` solves
the equation with data `fₖ, Gₖ`, and `fₖ → f`, `Gₖ → G` in `Lᵖ`, then `u` solves the equation with
the data `f, G`. -/
private theorem forall_energyFormIntegral_eq_of_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam κ : ℝ}
    (ham : AEStronglyMeasurable a volume) (hell : UniformlyEllipticOn univ a lam Lam)
    {U : ℕ → W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p}
    {u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p}
    (hlim : Tendsto U atTop (𝓝 u))
    {Gk : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {fk : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hGk : ∀ k, MemLp (Gk k) p volume)
    (hfk : ∀ k, MemLp (fk k) p volume) (hG : MemLp G p volume) (hf : MemLp f p volume)
    (hGl : Tendsto (fun k => eLpNorm (G - Gk k) p volume) atTop (𝓝 0))
    (hfl : Tendsto (fun k => eLpNorm (f - fk k) p volume) atTop (𝓝 0))
    (hU : ∀ k, (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField (U k))
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, fk k x * φ x) +
          ∫ x, ⟪Gk k x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)) :
    (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
      energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
          (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
        (∫ x, f x * φ x) + ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) := by
  intro φ
  have : Fact (1 ≤ (1 - p⁻¹)⁻¹) := ⟨by simp⟩
  have : p.HolderConjugate (1 - p⁻¹)⁻¹ := ENNReal.HolderConjugate.inv_one_sub_inv' Fact.out
  have hT : volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
      Set (EuclideanSpace ℝ (Fin (n + 1)))) = volume := by simp
  have hTn : ∀ {F : Type _} [NormedAddCommGroup F] (g : EuclideanSpace ℝ (Fin (n + 1)) → F),
      eLpNorm g p (volume.restrict ((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) :
        Set (EuclideanSpace ℝ (Fin (n + 1))))) = eLpNorm g p volume := fun g => by rw [hT]
  obtain ⟨hh, hφ, e⟩ := energyFormIntegral_testFunction_eq (q := (1 - p⁻¹)⁻¹) ham hell κ u φ
  have hgφ : MemLp (∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)) (1 - p⁻¹)⁻¹ volume :=
    (φ.contDiff.continuous_gradient (by simp)).memLp_of_hasCompactSupport
      (HasCompactSupport.intro φ.hasCompactSupport.isCompact fun _ hx =>
        gradient_of_notMem_tsupport hx)
  -- The values and the gradients converge in `Lᵖ`.
  have hgl : Tendsto (fun k => eLpNorm (⇑(W1p.gradient u) - ⇑(W1p.gradient (U k))) p volume)
      atTop (𝓝 0) := by
    have h1 := ((W1p.gradientL (mu := volume) (Omega := ⊤) (p := p)).continuous.tendsto u).comp
      hlim
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply, W1p.gradientL_apply]
    rw [hTn, eLpNorm_sub_comm]
  have hvl : Tendsto (fun k => eLpNorm (⇑(W1p.value u) - ⇑(W1p.value (U k))) p volume)
      atTop (𝓝 0) := by
    have h1 := ((W1p.valueL (mu := volume) (Omega := ⊤) (p := p)).continuous.tendsto u).comp
      hlim
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'] at h1
    refine h1.congr fun k => ?_
    simp only [Function.comp_apply, W1p.valueL_apply]
    rw [hTn, eLpNorm_sub_comm]
  have hLHS := ((tendsto_integral_inner_of_tendsto_eLpNorm_sub (𝕜 := ℝ) (W1p.memLp_gradient u)
    (fun k => W1p.memLp_gradient (U k)) hh hgl).add
      ((tendsto_integral_inner_of_tendsto_eLpNorm_sub (𝕜 := ℝ) (W1p.memLp_value u)
        (fun k => W1p.memLp_value (U k)) hφ hvl).const_mul κ)).congr fun k =>
    ((energyFormIntegral_testFunction_eq (q := (1 - p⁻¹)⁻¹) ham hell κ (U k) φ).2.2.symm.trans
      (hU k φ))
  have hmul : ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ∫ x, ⟪g x, φ x⟫_ℝ = ∫ x, g x * φ x := fun g =>
    integral_congr_ae (ae_of_all _ fun x => by
      simp only [RCLike.inner_apply, conj_trivial, mul_comm])
  have hRHS := ((tendsto_integral_inner_of_tendsto_eLpNorm_sub (𝕜 := ℝ) hf hfk hφ hfl).congr
    fun k => hmul (fk k)).add
    (tendsto_integral_inner_of_tendsto_eLpNorm_sub (𝕜 := ℝ) hG hGk hgφ hGl)
  rw [e, tendsto_nhds_unique hLHS hRHS, hmul]

/-- **Krylov's whole-space `W^{1,p}` theorem with a zero-order shift, for data in `Lᵖ`.** Let
`2 < p < ∞` and `0 < λ ≤ Λ`. There is a threshold `δ > 0`, depending only on `n`, `p`, `λ` and
`Λ`, with the following property. Let `a` be a measurable coefficient matrix on `ℝ^{n+1}`,
uniformly elliptic with constants `λ, Λ`, not necessarily symmetric, whose VMO modulus at a scale
`r₀ > 0` is at most `δ`, and let `κ ≥ 16 / r₀²`. For all `f ∈ Lᵖ` and `G ∈ Lᵖ(ℝ^{n+1}; ℝ^{n+1})`
the equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

has exactly one solution `u ∈ W^{1,p}(ℝ^{n+1})` in the sense of distributions. It satisfies
Krylov's estimate
(`exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_forall_energyFormIntegral_eq`). The data
need not be square integrable. This is N. V. Krylov, *Parabolic and elliptic equations
with VMO coefficients*, Theorem 2.8, for `2 < p < ∞`. -/
theorem existsUnique_forall_energyFormIntegral_eq_of_vmoModulus_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {r₀ κ : ℝ}, 0 < r₀ → 16 / r₀ ^ 2 ≤ κ → AEStronglyMeasurable a volume →
        UniformlyEllipticOn univ a lam Lam →
        vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume r₀ ≤ ENNReal.ofReal δ →
        ∀ (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G p volume → MemLp f p volume →
          ∃! u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p,
            ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
              energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
                  (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
                (∫ x, f x * φ x) +
                  ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ := by
  obtain ⟨δ₁, hδ₁, hreg⟩ :=
    exists_memLp_gradient_and_memLp_value_of_vmoModulus_le (n := n) hp hp_top lam Lam
  obtain ⟨C, δ₂, hδ₂, hest⟩ :=
    exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_forall_energyFormIntegral_eq
      (n := n) hp hp_top lam Lam
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {a r₀ κ} hr₀ hκ ham hell hη G f hG hf => ?_⟩
  have hκ0 : 0 < κ := (by positivity : (0 : ℝ) < 16 / r₀ ^ 2).trans_le hκ
  have hest' := hest hr₀ hκ ham hell fun c r hr hrr =>
    exists_uniformlyEllipticOn_const_and_setAverage_le_of_vmoModulus_le ham hell hδ₂.le
      (hη.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))) c r hr hrr
  -- Uniqueness.
  refine existsUnique_of_exists_of_unique ?_ fun u₁ u₂ hu₁ hu₂ => by
    have h := edist_le_of_forall_energyFormIntegral_eq ham hell hκ0 hest' hG hG hf hf hu₁ hu₂
    simp only [sub_self, eLpNorm_zero, mul_zero, add_zero] at h
    exact edist_le_zero.1 h
  -- Existence: the solutions `U k` for the data cut off to the balls `B(0, k + 1)`.
  set fk : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun k => (ball 0 ((k : ℝ) + 1)).indicator f
  set Gk : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := fun k =>
    (ball 0 ((k : ℝ) + 1)).indicator G
  have hfkp : ∀ k, MemLp (fk k) p volume := fun k =>
    hf.indicator measurableSet_ball.nullMeasurableSet
  have hGkp : ∀ k, MemLp (Gk k) p volume := fun k =>
    hG.indicator measurableSet_ball.nullMeasurableSet
  choose U hU using fun k => exists_forall_energyFormIntegral_eq_of_memLp_two ham hell hκ0
    (hreg hr₀ hκ0 ham hell (hη.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))))
    ((hGkp k).mono_exponent_of_measure_support_ne_top (fun x hx => indicator_of_notMem hx _)
      measure_ball_lt_top.ne hp.le)
    ((hfkp k).mono_exponent_of_measure_support_ne_top (fun x hx => indicator_of_notMem hx _)
      measure_ball_lt_top.ne hp.le) (hGkp k) (hfkp k)
  -- They form a Cauchy sequence in `W^{1,p}(ℝ^{n+1})`, controlled by the tails of the data.
  set K := ((ENNReal.ofReal √κ)⁻¹ + 1) * C
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2
    (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hκ0)).ne', ENNReal.one_ne_top⟩) ENNReal.coe_ne_top
  have hcauchy : CauchySeq U := by
    refine EMetric.cauchySeq_iff_le_tendsto_0.2 ⟨fun N => K *
      (eLpNorm ((ball 0 ((N : ℝ) + 1))ᶜ.indicator G) p volume + ENNReal.ofReal (√κ)⁻¹ *
        eLpNorm ((ball 0 ((N : ℝ) + 1))ᶜ.indicator f) p volume), fun k j N hk hj =>
      (edist_le_of_forall_energyFormIntegral_eq ham hell hκ0 hest' (hGkp k) (hGkp j) (hfkp k)
        (hfkp j) (hU k) (hU j)).trans ?_, ?_⟩
    · beta_reduce
      gcongr
      · exact eLpNorm_mono ((hGkp k).sub (hGkp j)).aestronglyMeasurable
          fun x => norm_indicator_ball_sub_le G hk hj x
      · exact eLpNorm_mono ((hfkp k).sub (hfkp j)).aestronglyMeasurable
          fun x => norm_indicator_ball_sub_le f hk hj x
    · simpa using ENNReal.Tendsto.const_mul ((tendsto_eLpNorm_indicator_compl_ball hp_top hG).add
        (ENNReal.Tendsto.const_mul (tendsto_eLpNorm_indicator_compl_ball hp_top hf)
          (Or.inr ENNReal.ofReal_ne_top))) (Or.inr hK)
  -- Its limit solves the equation.
  obtain ⟨u, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨u, forall_energyFormIntegral_eq_of_tendsto ham hell hlim hGkp hfkp hG hf
    ((tendsto_eLpNorm_indicator_compl_ball hp_top hG).congr fun k => by rw [indicator_compl])
    ((tendsto_eLpNorm_indicator_compl_ball hp_top hf).congr fun k => by rw [indicator_compl]) hU⟩

/-- **Krylov's whole-space `W^{1,p}` theorem with a zero-order shift, for coefficients of vanishing
mean oscillation and data in `Lᵖ`.** Let `2 < p < ∞` and `0 < λ ≤ Λ`. There is a constant `C`,
depending only on `n`, `p`, `λ` and `Λ`, with the following property. Let `a` be a coefficient
matrix on `ℝ^{n+1}`, uniformly elliptic with constants `λ, Λ`, not necessarily symmetric, whose
operators `a(x)` have vanishing mean oscillation. Then there is a threshold `κ₀ > 0` such that for
every `κ ≥ κ₀` and all `f ∈ Lᵖ`, `G ∈ Lᵖ(ℝ^{n+1}; ℝ^{n+1})`, the equation

`-∂ᵢ(aⁱʲ ∂ⱼu) + κ u = f - div G`

has exactly one solution `u ∈ W^{1,p}(ℝ^{n+1})` in the sense of distributions, and every solution
`u ∈ W^{1,p}(ℝ^{n+1})` satisfies

`‖∇u‖_{Lᵖ} + √κ ‖u‖_{Lᵖ} ≤ C (‖G‖_{Lᵖ} + κ^{-1/2} ‖f‖_{Lᵖ})`.

The threshold `κ₀` depends on `a` only through its VMO modulus. This is N. V. Krylov, *Parabolic
and elliptic equations with VMO coefficients*, Theorem 2.8, for `2 < p < ∞`. -/
theorem existsUnique_forall_energyFormIntegral_eq_of_memVMO {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 2 < p) (hp_top : p ≠ ⊤) (lam Lam : ℝ) :
    ∃ C : ℝ≥0, ∀ {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ},
      MemVMO (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume →
      UniformlyEllipticOn univ a lam Lam →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ {κ : ℝ}, κ₀ ≤ κ →
        ∀ (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
          (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ), MemLp G p volume → MemLp f p volume →
          (∃! u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p,
            ∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
              energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
                  (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
                (∫ x, f x * φ x) +
                  ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) ∧
          ∀ u : W1p volume (⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) p,
            (∀ φ : 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin (n + 1)))), ℝ),
              energyFormIntegral volume a 0 (fun _ => κ) (jetField u)
                  (fun x => (φ x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x)) =
                (∫ x, f x * φ x) +
                  ∫ x, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
            eLpNorm (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
                EuclideanSpace ℝ (Fin (n + 1))) p volume +
              ENNReal.ofReal √κ *
                eLpNorm (W1p.value u : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) p volume ≤
              C * (eLpNorm G p volume + ENNReal.ofReal (√κ)⁻¹ * eLpNorm f p volume) := by
  obtain ⟨C, δ₂, hδ₂, hest⟩ :=
    exists_eLpNorm_gradient_add_sqrt_mul_eLpNorm_value_le_of_forall_energyFormIntegral_eq
      (n := n) hp hp_top lam Lam
  obtain ⟨δ₁, hδ₁, hex⟩ :=
    existsUnique_forall_energyFormIntegral_eq_of_vmoModulus_le (n := n) hp hp_top lam Lam
  refine ⟨C, fun {a} hvmo hell => ?_⟩
  obtain ⟨hbmo, hlim⟩ := memVMO_iff_tendsto.1 hvmo
  -- The VMO modulus is below `min δ₁ δ₂` on `(0, r₁)`.
  obtain ⟨r₁, hr₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1
    (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (lt_min hδ₁ hδ₂))))
  have hr₁' : 0 < r₁ := hr₁
  have ham := aestronglyMeasurable_toEuclideanCLM_iff.1 hbmo.locallyIntegrable.aestronglyMeasurable
  have hη : vmoModulus (fun x => toEuclideanCLM (𝕜 := ℝ) (a x)) volume (r₁ / 2) ≤
      ENNReal.ofReal (min δ₁ δ₂) := (hsub ⟨by positivity, by linarith⟩).le
  refine ⟨16 / (r₁ / 2) ^ 2, by positivity, fun {κ} hκ G f hG hf => ⟨hex (by positivity) hκ ham
    hell (hη.trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))) G f hG hf, fun u hu => ?_⟩⟩
  exact hest (by positivity) hκ ham hell (fun c r hr hrr =>
    exists_uniformlyEllipticOn_const_and_setAverage_le_of_vmoModulus_le ham hell hδ₂.le
      (hη.trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))) c r hr hrr) u G f hG hf hu

end PDE

end TauCeti
