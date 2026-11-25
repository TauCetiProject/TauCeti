/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.Global
import TauCeti.MeasureTheory.Function.LpSeminorm.HolderOnWith

/-!
# The Dirichlet problem with `C^{1,α}` boundary values

Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary: near each of its boundary points,
in rigid coordinates, `Ω` is the region above the graph of a `C¹` function whose derivative is
`α`-Hölder. Consider the Dirichlet problem

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, `u = g` on `∂Ω`,

where `a` is uniformly elliptic with constants `λ`, `Λ` and `α`-Hölder on `closure Ω` with constant
`K_a ≤ M`, `G` is `α`-Hölder on `closure Ω` with constant `K_G`, `f ∈ L^q(Ω)` with `q ≥ 2`, and the
boundary values are given by `g ∈ H¹(Ω)` whose gradient agrees almost everywhere on `Ω` with a
function `Dg` that is `α`-Hölder on `closure Ω` with constant `K_g` and bounded there by `N_g`. A
weak solution is a `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and
`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v` for the test functions `v`. Let `0 < β < 1` with `β ≤ α`
and `β ≤ 1 - (n + 1) / q`.

* **Regularity.** The gradient of every weak solution agrees almost everywhere on `Ω` with a
  function `D` that is `β`-Hölder on `closure Ω`, whose Hölder constant `[D]_{β; closure Ω}` and
  supremum `sup_{closure Ω} ‖D‖` are each at most

  `C (K_G + ‖f‖_{L^q(Ω)} + K_g + N_g + ‖u - g‖_{H¹(Ω)})`,

  where `C` depends on `Ω`, its boundary charts, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`, but not on
  `u`, `g`, `a`, `G` or `f` otherwise
  (`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`).
* **Solvability.** There is exactly one `u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and
  `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v` for every `v ∈ H¹₀(Ω)`. It is a weak solution, so its
  gradient is `β`-Hölder up to the boundary, with the estimate above
  (`existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_and_holderOnWith_gradient_closure`).

This is Gilbarg–Trudinger's Theorem 8.34 for the operator without lower-order terms, with the
estimate of Theorem 8.33, for data `f ∈ L^q` and `G ∈ C^{0,α}`. The uniformity of the constant in
the coefficients is what comparison arguments for families of operators, such as the rescalings
of an equation at a boundary point in the proof of Hopf's lemma for weak solutions, need.

## The argument

The difference `w = u - g` lies in `H¹₀(Ω)` and solves the problem with zero boundary values

`-∂ᵢ(aⁱʲ ∂ⱼw) = f - div (G - a Dg)` in `Ω`,

since `∫_Ω ⟨a ∇g, ∇φ⟩ = ∫_Ω ⟨a Dg, ∇φ⟩`. By the product rule, the product `a Dg` of two bounded
Hölder fields is `α`-Hölder on `closure Ω` with constant `Λ K_g + N_g K_a`, so the global estimate
for zero boundary values
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`) applies to `w`, and
`∇u = ∇w + Dg`. Existence and uniqueness of the weak solution is Lax–Milgram on `H¹₀(Ω)`, which is
coercive since `Ω` lies in a ball (in the `TauCeti.PDE` namespace,
`UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.33 (the global `C^{1,α}` estimate) and Theorem 8.34 (solvability of the Dirichlet
  problem in `C^{1,α}(closure Ω)`).
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology Gradient InnerProductSpace Distributions

namespace TauCeti

namespace PDE


variable {n : ℕ} {Ω : Opens (EuclideanSpace ℝ (Fin (n + 1)))}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

/-- **Reduction to zero boundary values.** If `u ∈ H¹(Ω)` solves `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly
in `Ω`, tested against test functions, and the gradient of `g ∈ H¹(Ω)` agrees almost everywhere on
`Ω` with `Dg`, then `u - g` solves the equation with the datum `G - a Dg` in place of `G`. -/
private theorem energyFormH1_sub_ofTestFunctionₗ_eq {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {lam Lam : ℝ} (hell : UniformlyEllipticOn (Ω : Set E) a lam Lam)
    (ha : AEStronglyMeasurable a (volume.restrict (Ω : Set E))) {G Dg : E → E} {f : E → ℝ}
    (hG2 : MemLp G 2 (volume.restrict (Ω : Set E))) {u g : W1p volume Ω 2}
    (hgD : (W1p.gradient g : E → E) =ᵐ[volume.restrict Ω] Dg)
    (hu : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x) (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 a 0 0 (u - g) (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x - coefficientField a Dg x, ∇ (φ : E → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x := by
  have hcoeff : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict (Ω : Set E)) :=
    memLp_energyIntegrand_of_memLp_top hell.upper_nonneg ha (fun _ hx => hell.upper_bound hx)
      (memLp_top_const 0) (memLp_top_const 0)
  set w := W1p.ofTestFunctionₗ volume Ω 2 φ
  have hw : (W1p.gradient w : E → E) =ᵐ[volume.restrict Ω] ∇ (φ : E → ℝ) := by
    rw [W1p.gradient_ofTestFunctionₗ]
    exact gradientTestFunctionLp_apply_ae 2 φ
  -- Both sides of `∫ ⟨a ∇g, ∇φ⟩ = ∫ ⟨a Dg, ∇φ⟩` are integrable.
  have hgV : ∀ᵐ x ∂volume.restrict (Ω : Set E), matrixBilinearForm (a x) (W1p.gradient w x)
      (W1p.gradient g x) = ⟪coefficientField a Dg x, ∇ (φ : E → ℝ) x⟫_ℝ := by
    filter_upwards [hw, hgD] with x hx hx'
    rw [inner_coefficientField, hx, hx']
  have hGi : Integrable (fun x => ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) (volume.restrict (Ω : Set E)) :=
    (hG2.integrable_inner_of_holderConjugate (Lp.memLp (W1p.gradient w))).congr <| by
      filter_upwards [hw] with x hx
      rw [hx]
  have hVi := (hell.integrable_matrixBilinearForm_gradient ha g w).congr hgV
  simp only [inner_sub_left]
  rw [energyFormH1_sub_left (b := 0) (c := 0) hcoeff, hu φ, energyFormH1_zero_zero_eq_setIntegral,
    integral_congr_ae hgV, integral_sub hGi hVi]
  ring

/-- The comparison of constants that closes the global estimate with boundary values. -/
private theorem constant_le {C₀ Lam M KG F P Kg Ng Ka L : ℝ} (hC₀ : 0 ≤ C₀) (hKG : 0 ≤ KG)
    (hF : 0 ≤ F) (hP : 0 ≤ P) (hKg : 0 ≤ Kg) (hNg : 0 ≤ Ng) (hL : L ≤ |Lam|) (hKa : Ka ≤ |M|) :
    C₀ * (KG + (L * Kg + Ng * Ka) + F + P) + (Kg + 2 * Ng) ≤
      (C₀ * (1 + |Lam| + |M|) + 2) * (KG + F + Kg + Ng + P) := by
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hL hKg) hC₀,
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKa hNg) hC₀,
    mul_nonneg (mul_nonneg hC₀ (abs_nonneg Lam)) (by positivity : 0 ≤ KG + F + Ng + P),
    mul_nonneg (mul_nonneg hC₀ (abs_nonneg M)) (by positivity : 0 ≤ KG + F + Kg + P)]

/-- **The global `C^{1,β}` estimate for the Dirichlet problem with `C^{1,α}` boundary values.** Let
`Ω ⊆ ℝ^{n+1}` be a bounded open set with `C^{1,α}` boundary, given by rigid graph charts at its
frontier points as in `TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`, and let
`0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, `q ≥ 2`. Let `0 < λ`, `Λ` and `M` be given.
Then there is a constant `C ≥ 0` with the following property.

Let `a` be uniformly elliptic with constants `λ, Λ` and `α`-Hölder with constant `K_a ≤ M` on
`closure Ω`, let `G` be `α`-Hölder with constant `K_G` on `closure Ω`, and let `f ∈ L^q(Ω)`. Let
`g ∈ H¹(Ω)` have a gradient that agrees almost everywhere on `Ω` with a function `Dg` that is
`α`-Hölder with constant `K_g` and bounded by `N_g` on `closure Ω`. If `u ∈ H¹(Ω)` has boundary
values `g`, that is `u - g ∈ H¹₀(Ω)`, and solves `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly in `Ω`, then
`∇u` agrees almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, whose
Hölder constant and supremum on `closure Ω` are at most
`C (K_G + ‖f‖_{L^q(Ω)} + K_g + N_g + ‖u - g‖_{H¹(Ω)})`.

This is Gilbarg–Trudinger's Theorem 8.33 for the operator without lower-order terms, with
boundary values in `C^{1,α}`. -/
theorem exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1)
    (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΩ : Bornology.IsBounded (Ω : Set E))
    (hbdry : ∀ x ∈ frontier (Ω : Set E),
      ∃ (e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × F)) (γ : F → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u g : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G Dg : E → E} {f : E → ℝ} {Ka KG Kg Ng : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set E)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set E)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set E)) →
      MemLp f q (volume.restrict Ω) →
      (W1p.gradient g : E → E) =ᵐ[volume.restrict Ω] Dg →
      HolderOnWith Kg α Dg (closure (Ω : Set E)) → (∀ y ∈ closure (Ω : Set E), ‖Dg y‖ ≤ Ng) →
      u - g ∈ w1p0Submodule volume Ω 2 →
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
        (∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x) →
      ∃ D : E → E, (W1p.gradient u : E → E) =ᵐ[volume.restrict Ω] D ∧
        HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + Kg + Ng +
          ‖u - g‖)).toNNReal β D (closure (Ω : Set E)) ∧
        ∀ y ∈ closure (Ω : Set E), ‖D y‖ ≤
          C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + Kg + Ng + ‖u - g‖) := by
  obtain ⟨C₀, hC₀, hglob⟩ :=
    exists_holderOnWith_gradient_closure_of_forall_graph hβ hβ1 hβα hq hβq hΩ hbdry lam Lam M
  refine ⟨C₀ * (1 + |Lam| + |M|) + 2, by positivity, fun {u g a G Dg f Ka KG Kg Ng} hell hKa
    hKaM hG hf hgD hDg hNg hu0 hu => ?_⟩
  have hα : 0 < α := hβ.trans_le hβα
  have hellΩ := hell.mono_set (subset_closure (s := (Ω : Set E)))
  have ha := aestronglyMeasurable_of_holderOnWith_matrixBilinearForm (mu := volume)
    Ω.isOpen.measurableSet subset_closure hα hKa
  have hG2 := MeasureTheory.memLp_of_holderOnWith (μ := volume) (p := 2) Ω.isOpen.measurableSet
    subset_closure hΩ.closure hα hG
  -- `u - g ∈ H¹₀(Ω)` solves the problem with the datum `G - a Dg` in place of `G`.
  have hψ : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 ((⟨u - g, hu0⟩ : W1p0 volume Ω 2) : W1p volume Ω 2)
      (W1p.ofTestFunctionₗ volume Ω 2 φ) = (∫ x in Ω, ⟪G x - coefficientField a Dg x,
        ∇ (φ : E → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x :=
    energyFormH1_sub_ofTestFunctionₗ_eq hellΩ ha hG2 hgD hu
  -- The field `G - a Dg` is Hölder on `closure Ω`.
  have hV := holderOnWith_coefficientField hKa hDg (L := Lam.toNNReal)
    (fun x hx => (hell.opNorm_matrixBilinearForm_le hx).trans (Real.le_coe_toNNReal _)) hNg
  obtain ⟨D', hD'ae, hD'hol, hD'bd⟩ := hglob hell hKa hKaM (hG.sub hV) hf hψ
  -- The Hölder constant of `Dg` for the exponent `β`.
  have hDgβ : HolderOnWith (Kg + 2 * Ng) β Dg (closure (Ω : Set E)) := by
    simpa using hDg.of_le_of_norm_le hNg hβα one_pos
  -- The constants of the global estimate and of `Dg` are bounded by the final constant.
  have hnorm : ‖(⟨u - g, hu0⟩ : W1p0 volume Ω 2)‖ = ‖u - g‖ :=
    (Submodule.norm_coe (⟨u - g, hu0⟩ : W1p0 volume Ω 2)).symm
  rw [hnorm] at hD'hol hD'bd
  have hLam : (Lam.toNNReal : ℝ) ≤ |Lam| := by
    rw [Real.coe_toNNReal']
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hkey := constant_le (F := (eLpNorm f q (volume.restrict Ω)).toReal) hC₀ KG.coe_nonneg
    ENNReal.toReal_nonneg (norm_nonneg (u - g)) Kg.coe_nonneg Ng.coe_nonneg hLam
    (hKaM.trans (le_abs_self _))
  push_cast at hD'hol hD'bd
  have hQ₀nn : 0 ≤ C₀ * (KG + (Lam.toNNReal * Kg + Ng * Ka) +
      (eLpNorm f q (volume.restrict Ω)).toReal + ‖u - g‖) := mul_nonneg hC₀ (by positivity)
  refine ⟨D' + Dg, ?_, ?_, fun y hy => ?_⟩
  · filter_upwards [W1p.gradient_sub_ae u g, hD'ae, hgD] with x h1 h2 h3
    rw [Pi.add_apply, ← h2, ← h3, h1, Pi.sub_apply, sub_add_cancel]
  · refine (hD'hol.add hDgβ).mono_const ?_
    rw [← NNReal.coe_le_coe, NNReal.coe_add, Real.coe_toNNReal _ hQ₀nn,
      Real.coe_toNNReal _ (hQ₀nn.trans ((le_add_of_nonneg_right (by positivity)).trans hkey))]
    push_cast
    exact hkey
  · calc ‖(D' + Dg) y‖ ≤ ‖D' y‖ + ‖Dg y‖ := norm_add_le _ _
      _ ≤ _ := add_le_add (hD'bd y hy) (by linarith [hNg y hy, Kg.coe_nonneg, Ng.coe_nonneg])
      _ ≤ _ := hkey

/-- **The Dirichlet problem with `C^{1,α}` boundary values on a `C^{1,α}` domain is uniquely
solvable, with a gradient Hölder up to the boundary.** Let `Ω ⊆ ℝ^{n+1}` be a bounded open set with
`C^{1,α}` boundary, given by rigid graph charts at its frontier points as in
`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_forall_graph`, and let `0 < β < 1` with
`β ≤ α` and `β ≤ 1 - (n + 1) / q`, `q ≥ 2`. Let `0 < λ`, `Λ` and `M` be given. Then there is a
constant `C ≥ 0` with the following property.

Let `a` be uniformly elliptic with constants `λ, Λ` and `α`-Hölder with constant `K_a ≤ M` on
`closure Ω`, let `G` be `α`-Hölder with constant `K_G` on `closure Ω`, and let `f ∈ L^q(Ω)`. Let
`g ∈ H¹(Ω)` have a gradient that agrees almost everywhere on `Ω` with a function `Dg` that is
`α`-Hölder with constant `K_g` and bounded by `N_g` on `closure Ω`. Then there is exactly one
`u ∈ H¹(Ω)` with `u - g ∈ H¹₀(Ω)` and

`∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω ⟨G, ∇v⟩ + ∫_Ω f v` for every `v ∈ H¹₀(Ω)`,

the weak solution of `-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` in `Ω`, `u = g` on `∂Ω`, and its gradient agrees
almost everywhere on `Ω` with a function that is `β`-Hölder on `closure Ω`, with Hölder constant and
supremum at most `C (K_G + ‖f‖_{L^q(Ω)} + K_g + N_g + ‖u - g‖_{H¹(Ω)})`. Every weak solution with
these boundary values has this regularity
(`TauCeti.PDE.exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule`).

This is Gilbarg–Trudinger's Theorem 8.34 for the operator without lower-order terms. -/
theorem existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_and_holderOnWith_gradient_closure
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {α β : ℝ≥0} (hβ : 0 < β)
    (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) (hΩ : Bornology.IsBounded (Ω : Set E))
    (hbdry : ∀ x ∈ frontier (Ω : Set E),
      ∃ (e : E ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × F)) (γ : F → ℝ) (h₀ r₀ : ℝ)
        (Kγ : ℝ≥0), e x = 0 ∧ 0 < h₀ ∧ 0 < r₀ ∧ γ 0 = 0 ∧ ContDiff ℝ 1 γ ∧
          HolderWith Kγ α (fderiv ℝ γ) ∧
          ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst))
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {g : W1p volume Ω 2} {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G Dg : E → E} {f : E → ℝ} {Ka KG Kg Ng : ℝ≥0},
      UniformlyEllipticOn (closure (Ω : Set E)) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (closure (Ω : Set E)) →
      (Ka : ℝ) ≤ M → HolderOnWith KG α G (closure (Ω : Set E)) →
      MemLp f q (volume.restrict Ω) →
      (W1p.gradient g : E → E) =ᵐ[volume.restrict Ω] Dg →
      HolderOnWith Kg α Dg (closure (Ω : Set E)) → (∀ y ∈ closure (Ω : Set E), ‖Dg y‖ ≤ Ng) →
      ∃! u : W1p volume Ω 2, (u - g ∈ w1p0Submodule volume Ω 2 ∧
          ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
            (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
              ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x) ∧
        ∃ D : E → E, (W1p.gradient u : E → E) =ᵐ[volume.restrict Ω] D ∧
          HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + Kg + Ng +
            ‖u - g‖)).toNNReal β D (closure (Ω : Set E)) ∧
          ∀ y ∈ closure (Ω : Set E), ‖D y‖ ≤
            C * (KG + (eLpNorm f q (volume.restrict Ω)).toReal + Kg + Ng + ‖u - g‖) := by
  obtain ⟨C, hC, hreg⟩ := exists_holderOnWith_gradient_closure_of_sub_mem_w1p0Submodule hβ hβ1
    hβα hq hβq hΩ hbdry lam Lam M
  refine ⟨C, hC, fun {g a G Dg f Ka KG Kg Ng} hell hKa hKaM hG hf hgD hDg hNg => ?_⟩
  have : IsFiniteMeasure (volume.restrict (Ω : Set E)) :=
    isFiniteMeasure_restrict.2 hΩ.measure_lt_top.ne
  have hα : 0 < α := hβ.trans_le hβα
  have hellΩ := hell.mono_set (subset_closure (s := (Ω : Set E)))
  have ha := aestronglyMeasurable_of_holderOnWith_matrixBilinearForm (mu := volume)
    Ω.isOpen.measurableSet subset_closure hα hKa
  have hG2 := MeasureTheory.memLp_of_holderOnWith (μ := volume) (p := 2) Ω.isOpen.measurableSet
    subset_closure hΩ.closure hα hG
  have hf2 : MemLp f 2 (volume.restrict (Ω : Set E)) := hf.mono_exponent hq
  -- The right-hand side as a functional on `H¹₀(Ω)`.
  set ℓ := dirichletForcing (hf2.toLp f) - divergenceForcing (hG2.toLp G)
  have hℓ : ∀ v : W1p0 volume Ω 2, ℓ v =
      (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
        ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x := fun v => by
    rw [sub_apply, divergenceForcing_toLp_apply hG2,
      dirichletForcing_apply_eq_setIntegral, sub_neg_eq_add, add_comm]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
  obtain ⟨R, hR⟩ := hΩ.subset_ball 0
  obtain ⟨u, ⟨hu0, hu⟩, huniq⟩ :=
    hellΩ.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (b := 0) (c := 0) (beta := 0) (gamma := 0) ha aestronglyMeasurable_const
      aestronglyMeasurable_const (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => le_rfl) hR
      (by simpa using hellΩ.pos) ℓ g
  have hu' : ∀ v : W1p0 volume Ω 2, energyFormH1 a 0 0 u (v : W1p volume Ω 2) =
      (∫ x in Ω, ⟪G x, W1p.gradient (v : W1p volume Ω 2) x⟫_ℝ) +
        ∫ x in Ω, f x * W1p.value (v : W1p volume Ω 2) x := fun v => (hu v).trans (hℓ v)
  -- The weak equation against `H¹₀(Ω)` gives it against the test functions.
  have htest : ∀ φ : 𝓓(Ω, ℝ), energyFormH1 a 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      (∫ x in Ω, ⟪G x, ∇ (φ : E → ℝ) x⟫_ℝ) + ∫ x in Ω, f x * φ x := fun φ => by
    rw [hu' ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := Ω) 2 φ] with x hx
      rw [← hx, ← W1p.gradient_ofTestFunctionₗ (mu := volume) (Omega := Ω) (p := 2) φ]
    · refine integral_congr_ae ?_
      filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with x hx
      exact congrArg (f x * ·) hx
  have hR := hreg hell hKa hKaM hG hf hgD hDg hNg hu0 htest
  refine ⟨u, ⟨⟨hu0, hu'⟩, hR⟩, fun u' hu'' => ?_⟩
  exact huniq u' ⟨hu''.1.1, fun v => (hu''.1.2 v).trans (hℓ v).symm⟩

end PDE

end TauCeti
