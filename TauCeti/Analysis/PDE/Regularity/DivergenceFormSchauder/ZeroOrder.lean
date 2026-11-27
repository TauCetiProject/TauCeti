/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundaryData
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.PDE.EnergyForm.SmallDrift
import TauCeti.Analysis.PDE.MaximumPrinciple.GlobalBoundedness.LowerOrder
import TauCeti.Analysis.PDE.Regularity.FrozenCoefficient
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith

/-!
# Global Schauder theory for divergence-form equations with a zero-order term

Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary, given by rigid graph charts at its
frontier points as in `TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.BoundaryData`, and
consider the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f - div G` in `Ω`, `u = g` on `∂Ω`,

with `a` uniformly elliptic and `α`-Hölder on `closure Ω`, `c` bounded and measurable, `G` and the
gradient of the boundary datum `g` `α`-Hölder on `closure Ω`, and `f ∈ L^q(Ω)`. A weak solution is
a `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and `∫_Ω ⟨a ∇u, ∇v⟩ + ∫_Ω c u v = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v`.
This file adds the zero-order term to the global `C^{1,β}` theory without lower-order terms.

* **The global estimate** (Gilbarg–Trudinger, Theorem 8.33). For `0 < β < 1` with `β ≤ α` and
  `β ≤ 1 - (n + 1) / q`, and `|c| ≤ Γ`, the gradient of a weak solution that is essentially
  bounded agrees almost everywhere with a function `β`-Hölder on `closure Ω`, with Hölder constant
  and supremum at most

  `C (K_G + ‖f‖_{L^q(Ω)} + ‖u - g‖_{H¹(Ω)} + K_g + M_g + ‖u‖_{L^∞(Ω)})`,

  where `C` depends only on `Ω`, `n`, `α`, `β`, `q`, `λ`, `Λ`, a bound for the Hölder constant of
  `a` and `Γ` (`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule_of_mass`).
  No sign of `c` is needed; as in Gilbarg–Trudinger, the supremum of `u` enters the estimate.
* **Solvability** (Gilbarg–Trudinger, Theorem 8.34). For `c ≥ 0` and a boundary datum `g` that is
  moreover essentially bounded, the Dirichlet problem has exactly one weak solution; it is
  essentially bounded and its gradient agrees almost everywhere with a function `β`-Hölder on
  `closure Ω`, so the estimate above applies to it. In the `TauCeti.PDE` namespace, this theorem
  carries the name of its counterpart without lower-order terms,
  `existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_and_holderOnWith_gradient_closure`,
  with the suffix `_of_mass`. The weak solvability step for `c ≥ 0` alone is
  `UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_isBounded`.
  Without a sign condition on `c` uniqueness fails: on
  `(0, π)` the function `sin x` solves `-u'' - u = 0` with zero boundary values.

## The argument

For the estimate, the zero-order term is moved to the right-hand side: `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = (f - c u) - div G`, and `‖f - c u‖_{L^q} ≤ ‖f‖_{L^q} + Γ |Ω|^{1/q} ‖u‖_{L^∞}`, so
the estimate without lower-order terms
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`) applies.

For solvability, the energy form is coercive on `H¹₀(Ω)` when `c ≥ 0`, since `Ω` lies in a ball,
and Lax–Milgram gives the weak solution. It is essentially bounded by Stampacchia's maximum
principle with boundary values (`TauCeti.PDE.exists_ae_abs_value_le_add_of_sub_mem_w1p0Submodule`),
applied at an exponent `r > max 2 (n + 1)` with `f ∈ L^{r/2}(Ω)`, which exists because
`q > n + 1`. The estimate then gives the regularity of the gradient.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.16 (the global bound), Theorem 8.33 (the global `C^{1,α}` estimate) and Theorem 8.34
  (solvability of the Dirichlet problem in `C^{1,α}(closure Ω)`).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Gradient InnerProductSpace Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ}

/-- **Moving the zero-order term to the right-hand side.** If `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f - div G` weakly in `Ω`, tested against test functions, with an essentially
bounded principal energy density, an essentially bounded `c` and `f ∈ L²(Ω)`, then `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = (f - c u) - div G` in the same sense. -/
private theorem energyFormH1_ofTestFunctionₗ_eq_sub_mul
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {u : W1p volume Ω 2}
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict Ω))
    (hc : MemLp c ⊤ (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 c u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, f x * φ x) (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in Ω, (f x - c x * W1p.value u x) * φ x := by
  have hφ := memLp_testFunction (mu := volume) (Omega := Ω) 2 φ
  have hcu : MemLp (fun x => c x * W1p.value u x) 2 (volume.restrict Ω) :=
    hc.fun_mul (Lp.memLp _)
  have hval : ∫ x in Ω, c x * W1p.value u x * W1p.value (W1p.ofTestFunctionₗ volume Ω 2 φ) x =
      ∫ x in Ω, c x * W1p.value u x * φ x :=
    integral_congr_ae ((W1p.value_ofTestFunctionₗ_ae (p := 2) φ).mono fun x hx => by
      simp only [hx])
  have hsplit : ∫ x in Ω, (f x - c x * W1p.value u x) * φ x =
      (∫ x in Ω, f x * φ x) - ∫ x in Ω, c x * W1p.value u x * φ x := by
    simp_rw [sub_mul]
    exact integral_sub (hf.integrable_mul hφ) (hcu.integrable_mul hφ)
  rw [hsplit]
  linarith [hu φ, hval, energyFormH1_eq_energyFormH1_zero_add_setIntegral (b := 0) ha hc u
    (W1p.ofTestFunctionₗ volume Ω 2 φ)]

/-- **The datum without zero-order term.** If `|c| ≤ Γ` almost everywhere on `Ω`, which has finite
measure, and `u` is essentially bounded, then the datum `f - c u` of the equation
`-∂ᵢ(aⁱʲ ∂ⱼu) = (f - c u) - div G` lies in `L^q(Ω)` whenever `f` does, with
`‖f - c u‖_{L^q} ≤ ‖f‖_{L^q} + Γ |Ω|^{1/q} ‖u‖_{L^∞}`. -/
private theorem memLp_sub_mul_value_and_toReal_eLpNorm_le
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    [IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))]
    {q : ℝ≥0∞} (hq : 1 ≤ q) {c f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Γ : ℝ}
    {u : W1p volume Ω 2} (hf : MemLp f q (volume.restrict Ω))
    (hc : AEStronglyMeasurable c (volume.restrict Ω))
    (hcΓ : ∀ᵐ x ∂volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ Γ)
    (hΓ : 0 ≤ Γ)
    (hu : MemLp (W1p.value u) ⊤ (volume.restrict Ω)) :
    MemLp (fun x => f x - c x * W1p.value u x) q (volume.restrict Ω) ∧
      (eLpNorm (fun x => f x - c x * W1p.value u x) q (volume.restrict Ω)).toReal ≤
        (eLpNorm f q (volume.restrict Ω)).toReal +
          Γ * ((volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) univ).toReal ^
          q.toReal⁻¹ * (eLpNorm (W1p.value u) ⊤ (volume.restrict Ω)).toReal := by
  set ν := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  set U := (eLpNorm (W1p.value u) ⊤ ν).toReal
  -- `|c u| ≤ Γ ‖u‖_∞` almost everywhere.
  have hcu : ∀ᵐ x ∂ν, ‖c x * W1p.value u x‖ ≤ Γ * U := by
    filter_upwards [hcΓ, ae_le_lpNorm_exponent_top hu] with x hcx hux
    rw [← toReal_eLpNorm] at hux
    rw [norm_mul]
    exact mul_le_mul hcx hux (norm_nonneg _) hΓ
  have hcum : AEStronglyMeasurable (fun x => c x * W1p.value u x) ν :=
    hc.mul hu.aestronglyMeasurable
  refine ⟨hf.sub (MemLp.of_bound hcum _ hcu), ?_⟩
  have hle := (eLpNorm_sub_le (f := f) (g := fun x => c x * W1p.value u x) hq).trans
    (add_le_add le_rfl (eLpNorm_le_of_ae_bound (p := q) hcum hcu))
  refine (ENNReal.toReal_mono (by finiteness) hle).trans_eq ?_
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top (by finiteness), ENNReal.toReal_mul,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (by positivity)]
  ring

/-- For `2 ≤ q` with `β ≤ 1 - (n + 1) / q` and `β > 0`, and `f ∈ L^q(Ω)` on a set of finite
measure, there is an exponent `r > max 2 (n + 1)` with `f ∈ L^{r/2}(Ω)`: `r = 2q` if `q < ∞`, and
`r = n + 3` if `q = ∞`. This is the exponent at which Stampacchia's global bound applies. -/
private theorem exists_two_lt_and_lt_and_memLp_div_two {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {β : ℝ≥0} (hβ : 0 < β) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {f : X → ℝ} (hf : MemLp f q μ) :
    ∃ r : ℝ≥0, 2 < (r : ℝ) ∧ (n : ℝ) + 1 < r ∧ MemLp f (r / 2 : ℝ≥0) μ := by
  rcases eq_or_ne q ⊤ with rfl | hqt
  · refine ⟨n + 3, by push_cast; linarith [n.cast_nonneg (α := ℝ)], by push_cast; linarith,
      hf.mono_exponent le_top⟩
  have hq2 : (2 : ℝ) ≤ q.toReal := by
    simpa using ENNReal.toReal_mono hqt hq
  -- `β > 0` forces `n + 1 < q`.
  have hnq : (n : ℝ) + 1 < q.toReal := by
    have : ((n : ℝ) + 1) / q.toReal < 1 := by linarith [(NNReal.coe_pos.2 hβ)]
    rwa [div_lt_one (by linarith)] at this
  refine ⟨2 * q.toNNReal, ?_, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith
  · rw [mul_div_cancel_left₀ _ two_ne_zero, ENNReal.coe_toNNReal hqt]
    exact hf

/-- **The global `C^{1,β}` estimate with a zero-order term** (Gilbarg–Trudinger, Theorem 8.33).
Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary: for every frontier point `x` there
are rigid coordinates `e` with `e x = 0` and a `C¹` function `γ` with `γ 0 = 0` and `α`-Hölder
derivative such that, inside a normal cylinder, `Ω` is the region above the graph of `γ`. Let
`0 < β < 1` with `β ≤ α`, let `2 ≤ q` with `β ≤ 1 - (n + 1) / q`, where `(n + 1) / ∞ = 0`, and let
`λ, Λ, M, Γ` be given. Then there is a constant `C`, depending only on these data, with the
following property.

Let `u, g ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and let `u` solve `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f - div G` weakly
in `Ω`, that is `∫_Ω ⟨a ∇u, ∇φ⟩ + ∫_Ω c u φ = ∫_Ω ⟨G, ∇φ⟩ + ∫_Ω f φ` for every test function `φ`.
Suppose that on `closure Ω` the coefficient `a` is uniformly elliptic with constants `λ, Λ` and
`α`-Hölder with constant `K_a ≤ M`, `G` is `α`-Hölder with constant `K_G`, and `∇g` agrees almost
everywhere on `Ω` with a field `Dg` that is `α`-Hölder with constant `K_g` and bounded by `M_g`;
let `c` be measurable with `|c| ≤ Γ` on `Ω`, let `f ∈ L^q(Ω)`, and let `u` be essentially bounded.
Then `∇u` agrees almost everywhere on `Ω` with a function `h` that is `β`-Hölder on `closure Ω`,
with Hölder constant and supremum at most
`C (K_G + ‖f‖_{L^q(Ω)} + ‖u - g‖_{H¹(Ω)} + K_g + M_g + ‖u‖_{L^∞(Ω)})`.

No sign condition on `c` is needed. For `c = 0` the term `‖u‖_{L^∞(Ω)}` is superfluous, by
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`. -/
theorem exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule_of_mass {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1)
    (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M Γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u g : W1p volume Ω 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {c f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
      {G Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {Ka KG Kg Mg : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set _)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set _)) →
      (Ka : ℝ) ≤ M → AEStronglyMeasurable c (volume.restrict (Ω : Set _)) →
      (∀ x ∈ (Ω : Set _), ‖c x‖ ≤ Γ) → HolderOnWith KG α G (closure (Ω : Set _)) →
      MemLp f q (volume.restrict (Ω : Set _)) →
      u - g ∈ w1p0Submodule volume Ω 2 →
      ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg →
      HolderOnWith Kg α Dg (closure (Ω : Set _)) → (∀ y ∈ closure (Ω : Set _), ‖Dg y‖ ≤ Mg) →
      MemLp (W1p.value u) ⊤ (volume.restrict (Ω : Set _)) →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 c u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in Ω, f x * φ x) →
      ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        ⇑(W1p.gradient u) =ᵐ[volume.restrict Ω] h ∧
        HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u - g‖ +
          Kg + Mg + (eLpNorm (W1p.value u) ⊤ (volume.restrict (Ω : Set _))).toReal)).toNNReal β h
          (closure (Ω : Set _)) ∧
        ∀ y ∈ closure (Ω : Set _), ‖h y‖ ≤
          C * (KG + (eLpNorm f q (volume.restrict (Ω : Set _))).toReal + ‖u - g‖ + Kg + Mg +
            (eLpNorm (W1p.value u) ⊤ (volume.restrict (Ω : Set _))).toReal) := by
  obtain ⟨C₀, hC₀, H₀⟩ :=
    exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule hβ hβ1 hβα hq hβq hΩ hchart lam
      Lam M
  set ν := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  -- `V = |Ω|^{1/q}` and `Γ' = max Γ 0` enter the bound `‖c u‖_q ≤ Γ' V ‖u‖_∞`.
  set V : ℝ := (ν univ).toReal ^ q.toReal⁻¹
  set Γ' : ℝ := max Γ 0
  have hV : 0 ≤ V := by positivity
  have hΓ' : 0 ≤ Γ' := le_max_right _ _
  refine ⟨C₀ * (1 + Γ' * V), by positivity,
    fun {u g a c f G Dg Ka KG Kg Mg} hell hKa hKaM hc hcΓ hKG hf hug hDg hDgK hDgM huinf hu => ?_⟩
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hα : 0 < α := hβ.trans_le hβα
  have hcae : ∀ᵐ x ∂ν, ‖c x‖ ≤ Γ' := (ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx =>
    (hcΓ x hx).trans (le_max_left _ _)
  -- The datum `f - c u` of the equation without zero-order term lies in `L^q(Ω)`.
  obtain ⟨hf', hf'le⟩ := memLp_sub_mul_value_and_toReal_eLpNorm_le (one_le_two.trans hq) hf hc
    hcae hΓ' huinf
  have hcoeff := memLp_energyIntegrand_of_holderOnWith (mu := volume) subset_closure
    (hell.mono_set subset_closure) hα hKa
  obtain ⟨h, hae, hK, hM⟩ := H₀ hell hKa hKaM hKG hf' hug hDg hDgK hDgM
    (energyFormH1_ofTestFunctionₗ_eq_sub_mul hcoeff (memLp_top_of_bound hc Γ' hcae)
      (hf.mono_exponent hq) hu)
  -- The constants: `‖f - c u‖_q ≤ ‖f‖_q + Γ' V ‖u‖_∞`.
  have key : C₀ * (KG + (eLpNorm (fun x => f x - c x * W1p.value u x) q ν).toReal + ‖u - g‖ +
        Kg + Mg) ≤
      C₀ * (1 + Γ' * V) * (KG + (eLpNorm f q ν).toReal + ‖u - g‖ + Kg + Mg +
        (eLpNorm (W1p.value u) ⊤ ν).toReal) := by
    have hN : 0 ≤ (KG : ℝ) + (eLpNorm f q ν).toReal + ‖u - g‖ + Kg + Mg := by positivity
    have hU : 0 ≤ (eLpNorm (W1p.value u) ⊤ ν).toReal := ENNReal.toReal_nonneg
    have := mul_nonneg (mul_nonneg hΓ' hV) hN
    calc _ ≤ C₀ * (KG + ((eLpNorm f q ν).toReal + Γ' * V * (eLpNorm (W1p.value u) ⊤ ν).toReal) +
          ‖u - g‖ + Kg + Mg) := by gcongr
      _ ≤ _ := by
        rw [mul_assoc C₀]
        exact mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg (mul_nonneg hΓ' hV) hU]) hC₀
  refine ⟨h, hae, hK.mono_const (Real.toNNReal_le_toNNReal key), fun y hy => (hM y hy).trans key⟩

/-- **The Dirichlet problem with a nonnegative zero-order term on a `C^{1,α}` domain is uniquely
solvable, with a gradient Hölder up to the boundary** (Gilbarg–Trudinger, Theorem 8.34). Let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary, given by rigid graph charts at its
frontier points as in
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule_of_mass`, and let
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, `q ≥ 2`.

Let `a` be uniformly elliptic and `α`-Hölder on `closure Ω`, let `c` be measurable with
`0 ≤ c ≤ Γ` on `Ω`, let `G` be `α`-Hölder on `closure Ω`, and let `f ∈ L^q(Ω)`. Let `g ∈ H¹(Ω)` be
essentially bounded, with a gradient that agrees almost everywhere on `Ω` with a function `Dg` that
is `α`-Hölder and bounded on `closure Ω`. Then there is exactly one `u ∈ H¹(Ω)` with
`u - g ∈ H¹₀(Ω)` and

`∫_Ω ⟨a ∇u, ∇v⟩ + ∫_Ω c u v = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

the weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) + c u = f - div G` in `Ω`, `u = g` on `∂Ω`. It is essentially
bounded, and its gradient agrees almost everywhere on `Ω` with a function that is `β`-Hölder on
`closure Ω`. Its Hölder constant and supremum are bounded by
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule_of_mass`.

Some sign condition on `c` is needed for uniqueness: `sin x` solves `-u'' - u = 0` on `(0, π)` with
zero boundary values. -/
theorem
existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_and_holderOnWith_gradient_closure_of_mass
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β)
    (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΩ : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    (hchart : ∀ x ∈ frontier (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)) (γ : E → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
        HolderWith Kγ α (fderiv ℝ γ) ∧
        ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    {g : W1p volume Ω 2}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {c f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {G Dg : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {Ka KG Kg Mg : ℝ≥0} {lam Lam Γ : ℝ}
    (hell : UniformlyEllipticOn (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) a lam Lam)
    (hKa : HolderOnWith Ka α (fun x => matrixBilinearForm (a x))
      (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hc : AEStronglyMeasurable c (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hcΓ : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖c x‖ ≤ Γ)
    (hc0 : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), 0 ≤ c x)
    (hG : HolderOnWith KG α G (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hf : MemLp f q (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hgD : ⇑(W1p.gradient g) =ᵐ[volume.restrict Ω] Dg)
    (hDg : HolderOnWith Kg α Dg (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
    (hMg : ∀ y ∈ closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))), ‖Dg y‖ ≤ Mg)
    (hg : MemLp (W1p.value g) ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))))) :
    (∃! u : W1p volume Ω 2, u - g ∈ w1p0Submodule volume Ω 2 ∧
        ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 c u (v : W1p volume Ω 2) =
          (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
            ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x) ∧
    ∀ u : W1p volume Ω 2, u - g ∈ w1p0Submodule volume Ω 2 →
      (∀ v : W1p0 volume Ω 2, energyFormH1 a 0 c u (v : W1p volume Ω 2) =
        (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
          ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x) →
      MemLp (W1p.value u) ⊤ (volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) ∧
      ∃ h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
        ⇑(W1p.gradient u) =ᵐ[volume.restrict Ω] h ∧
        ∃ K : ℝ≥0, HolderOnWith K β h (closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))) := by
  set ν := volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hα : 0 < α := hβ.trans_le hβα
  have hellΩ := hell.mono_set (subset_closure (s := (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))))
  have ha := aestronglyMeasurable_of_holderOnWith_matrixBilinearForm (mu := volume)
    Ω.isOpen.measurableSet subset_closure hα hKa
  have hGinf : MemLp G ⊤ ν := hG.memLp_top hα hΩ.closure Ω.isOpen.measurableSet subset_closure
  refine ⟨hellΩ.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_isBounded hΩ ha hc
    hcΓ hc0 (hf.mono_exponent hq) (hGinf.mono_exponent le_top) g, fun u hu0 hu => ?_⟩
  -- The weak equation with the divergence datum written as `-div (-G)`.
  have hu' : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 c u (v : W1p volume Ω 2) =
      (∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x) -
        ∫ x in Ω, ⟪(-G) x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ := fun v => by
    rw [hu v]
    simp only [Pi.neg_apply, inner_neg_left, integral_neg, sub_neg_eq_add, add_comm]
  -- `u` is essentially bounded, by Stampacchia's bound with the boundary values of `g`.
  obtain ⟨r, hr2, hrn, hfr⟩ := exists_two_lt_and_lt_and_memLp_div_two hβ hq hβq hf
  obtain ⟨CS, -, HS⟩ := exists_ae_abs_value_le_add_of_sub_mem_w1p0Submodule (mu := volume)
    (ι := Fin (n + 1)) hr2 (by simpa using hrn) 0
  have hbd := HS (b := 0) (beta := 0) (k := (eLpNorm (W1p.value g) ⊤ ν).toReal)
    hΩ.measure_lt_top.ne hellΩ ha aestronglyMeasurable_zero hc (fun _ _ => by simp) hcΓ hc0
    (by simp) hfr (hGinf.mono_exponent le_top).neg hu' hu0
    ((ae_le_lpNorm_exponent_top hg).mono fun x hx => by rwa [← Real.norm_eq_abs, toReal_eLpNorm])
  have huinf : MemLp (W1p.value u) ⊤ ν :=
    memLp_top_of_bound (Lp.aestronglyMeasurable _) _ (hbd.mono fun x hx => by
      rwa [Real.norm_eq_abs])
  -- The weak equation against the test functions, and the estimate.
  obtain ⟨C, -, hreg⟩ := exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule_of_mass hβ
    hβ1 hβα hq hβq hΩ hchart lam Lam Ka Γ
  obtain ⟨h, hae, hK, -⟩ := hreg hell hKa le_rfl hc hcΓ hG hf hu0 hgD hDg hMg huinf
    (by simpa only [neg_neg] using energyFormH1_ofTestFunctionₗ_eq_of_forall_w1p0 hu')
  exact ⟨huinf, h, hae, _, hK⟩

end PDE

end TauCeti
