/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.DivergenceFormSchauder.FlatBoundary
public import TauCeti.Analysis.PDE.EnergyForm.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
import TauCeti.Analysis.Calculus.GraphFlattening.Basic
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.Normed.Affine.Isometry.Basic
import TauCeti.Analysis.Normed.Operator.Holder
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.Analysis.Sobolev.LipschitzDomain.Flattening
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace

/-!
# Schauder estimates near a curved boundary for divergence-form equations

Let `Ω ⊆ ℝ^{n+1}` be open and let `x₀` be a boundary point near which `∂Ω` is a `C^{1,α}`
hypersurface. Let `u ∈ H¹(W)`, on an open set `W` containing a ball around `x₀`, vanish on
`W ∖ Ω` and solve

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `W ∩ Ω`,

so that `u` has zero boundary values on `∂Ω` near `x₀`. This file proves the `C^{1,β}` estimate for
`u` up to the boundary near `x₀`, for coefficients `a` and fields `G` that are `α`-Hölder on
`closure Ω` and data `f ∈ L^q`: for `0 < β < 1` with `β ≤ α` and `β ≤ 1 - (n + 1) / q`, the gradient
`∇u` agrees almost everywhere near `x₀` with a function `g` that is `β`-Hölder on `closure Ω` near
`x₀`, with Hölder constant and supremum at most

`C (K_G + ‖f‖_{L^q} + ‖u‖_{H¹(W)})`,

where `K_G` is the Hölder constant of `G` and `C` depends on the boundary chart, `n`, `α`, `β`, `q`,
the ellipticity constants of `a` and a bound for its Hölder constant, but not on `u`, `a`, `G` or
`f` otherwise. The estimate is stated in a flattening chart
(`TauCeti.PDE.exists_holderOnWith_gradient_of_isChangeOfVariables`) and for a boundary that is
locally the graph of a `C¹` function with `α`-Hölder derivative
(`TauCeti.PDE.exists_holderOnWith_gradient_of_graph`). This is the boundary version of the
divergence-form Schauder estimate, whose interior and flat-boundary cases are
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm`
and
`TauCeti.PDE.exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp`.
The uniformity of the constant over the coefficients is what compactness arguments for families of
operators, such as rescalings at a boundary point, need.

## The argument

The boundary is flattened, as in Gilbarg–Trudinger, Section 6.2 and the proof of Theorem 8.33.

* **Flattening.** Let `Φ` map a neighbourhood `U'` of a point `y₀` of the hyperplane
  `{⟪y, ν⟫ = c₀}` onto a neighbourhood `U` of `x₀ = Φ y₀`, with inverse `Ψ`, carrying the open
  half-space `H = {c₀ < ⟪y, ν⟫}` onto `Ω`, both with Jacobian determinant one and `DΨ` `α`-Hölder.
  The flattened function `v = u ∘ Φ` lies in `H¹` of a ball `B` around `y₀`, vanishes on `B ∖ H`,
  and solves `-∂ᵢ(a'ⁱʲ ∂ⱼv) = f' - div G'` weakly on `B ∩ H`
  (`TauCeti.PDE.energyFormH1_compL_eq_setIntegral_add_setIntegral_inner`), where
  `a' = DΨ(Φ ·) (a ∘ Φ) DΨ(Φ ·)ᵀ`, `G' = DΨ(Φ ·) (G ∘ Φ - G x₀)` and `f' = f ∘ Φ`. These are
  uniformly elliptic and `α`-Hölder on the closed half-ball, with explicit constants
  (`TauCeti.PDE.holderOnWith_matrixBilinearForm_pullbackPrincipal`,
  `TauCeti.PDE.holderOnWith_pullbackDrift`), and `‖f'‖_{L^q} ≤ ‖f‖_{L^q}`
  (`TauCeti.PDE.eLpNorm_pullbackDensity_le`).
* **Folding.** The flat estimate asks for the coefficients on a full ball, so `a'` and `G'` are
  extended across the hyperplane by composing with the fold `y ↦ y` on the closed half-space and
  `y ↦` its mirror image elsewhere, which is `1`-Lipschitz
  (`TauCeti.lipschitzWith_one_ite_hyperplaneReflection`). The extension does not change the
  equation, which only sees `B ∩ H`.
* **The flat estimate.** The precise representative `P` of `∇v` for the Lebesgue measure on `H`
  is `β`-Hölder on a closed half-ball by the flat-boundary estimate. Its supremum there follows
  from the Hölder bound and the `L²` norm of `∇v`, since `H` fills at least half of every ball
  centred in its closure.
* **Back to `Ω`.** By the chain rule `∇u(x) = DΨ(x)* P(Ψ x)` for almost every `x ∈ Ω` near `x₀`,
  and the right-hand side is `β`-Hölder on `closure Ω` near `x₀`, since `Ψ` is Lipschitz and maps
  `closure Ω` into the closed half-space.

## Main declarations

All in the `TauCeti.PDE` namespace.

* `exists_holderOnWith_gradient_of_isChangeOfVariables`: the `C^{1,β}` estimate up to the boundary
  in a flattening chart.
* `exists_holderOnWith_gradient_of_graph`: the same near a boundary that is locally the graph of a
  `C^{1,α}` function.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.2 (flattening the boundary) and Theorem 8.33 (the `C^{1,α}` estimate up to the
  boundary).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Section 5.4.
-/

public section

noncomputable section

open Filter InnerProductSpace MeasureTheory Metric Set TopologicalSpace
open scoped ENNReal NNReal Topology Gradient InnerProductSpace Distributions

namespace TauCeti

namespace PDE

variable {n : ℕ}

variable {Ω U' U : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
  {Φ Ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
  {ν : EuclideanSpace ℝ (Fin (n + 1))} {c₀ : ℝ}

/-! ### The flattened weak equation -/

section Equation

variable {L : ℝ}

/-- **The flattened weak equation.** Let `Φ` map the flat piece `B ⊓ H` onto `D ⊆ W ⊓ Ω`, with
inverse `Ψ`, both changes of variables with Jacobian determinant one. If `u` solves
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `W ⊓ Ω`, tested against test functions, then the flattened
function `u ∘ Φ` solves `-∂ᵢ(a'ⁱʲ ∂ⱼu') = f' - div G'` weakly on `B ⊓ H`, tested against test
functions, with `a' = pullbackPrincipal Φ a`, `f' = pullbackDensity Φ f` and the transformed field
`G' = pullbackDrift Φ (G - c)` of `G` minus any constant `c`. -/
private theorem energyFormH1_restrictL_w1pCompL_eq
    {W B V D H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hVW : V ≤ W) (hDWΩ : D ≤ W ⊓ Ω)
    (hΦB : Wkp.IsChangeOfVariables 1 B V Φ L 1) (hΦD : Wkp.IsChangeOfVariables 1 (B ⊓ H) D Φ L 1)
    (hΨD : Wkp.IsChangeOfVariables 1 D (B ⊓ H) Ψ L 1) (hΨΦ : LeftInvOn Ψ Φ (B ⊓ H))
    (hΦΨ : RightInvOn Ψ Φ D)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {u : W1p volume W 2}
    (hu : ∀ φ : 𝓓(W ⊓ Ω, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
        (W1p.ofTestFunctionₗ volume (W ⊓ Ω) 2 φ) =
      (∫ x in W ⊓ Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in W ⊓ Ω, f x * φ x)
    (ha : MemLp (fun x => energyIntegrand (a x) 0 0) ⊤ (volume.restrict D))
    {c : EuclideanSpace ℝ (Fin (n + 1))} (hGc : MemLp (fun x => G x - c) 2 (volume.restrict D))
    (hf : MemLp f 2 (volume.restrict D)) (φ : 𝓓(B ⊓ H, ℝ)) :
    energyFormH1 (pullbackPrincipal Φ a) 0 0
        (W1p.restrictL inf_le_left (hΦB.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hVW u)))
        (W1p.ofTestFunctionₗ volume (B ⊓ H) 2 φ) =
      (∫ x in B ⊓ H, ⟪pullbackDrift Φ (fun y => G y - c) x,
          ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in B ⊓ H, pullbackDensity Φ f x * φ x := by
  -- The equation on `D`, tested against `H¹₀(D)`, in integral form.
  have hD (w : W1p0 volume D 2) : energyFormH1 a 0 0
      (W1p.restrictL (hDWΩ.trans inf_le_left) u) (w : W1p volume D 2) =
      (∫ y in D, f y * W1p.value (w : W1p volume D 2) y) +
        ∫ y in D, ⟪G y - c, W1p.gradient (w : W1p volume D 2) y⟫_ℝ := by
    have h := forall_energyFormH1_restrictL_eq_inner_add_inner hDWΩ ha hu hGc hf w
    rw [W1p.restrictL_restrictL] at h
    rw [h, L2.inner_def, L2.inner_def, add_comm]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [hf.coeFn_toLp] with y hy
      rw [hy, RCLike.inner_apply, conj_trivial, mul_comm]
    · refine integral_congr_ae ?_
      filter_upwards [hGc.coeFn_toLp] with y hy
      rw [hy]
  -- Transfer it to the flat side.
  have h := energyFormH1_compL_eq_setIntegral_add_setIntegral_inner hΦD.differentiableOn
    hΦD.injOn hΦD.mapsTo hΦD.norm_fderiv_le hΦD.pos hΦD.le_abs_det hΨD.differentiableOn
    hΨD.mapsTo hΨD.norm_fderiv_le hΨD.pos hΨD.le_abs_det hΨΦ hΦΨ
    (b := 0) (c := 0) hD ⟨_, W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩
  rw [pullbackDrift_zero, pullbackDensity_zero] at h
  have hcomp := hΦB.w1pCompL_restrictL_eq_restrictL_w1pCompL hΦD inf_le_left ENNReal.ofNat_ne_top
    hVW (hDWΩ.trans inf_le_left) u
  simp only [Wkp.IsChangeOfVariables.w1pCompL] at hcomp
  rw [← hcomp, h, add_comm]
  congr 1
  · refine integral_congr_ae ?_
    filter_upwards [gradientTestFunctionLp_apply_ae (mu := volume) (Omega := B ⊓ H) 2 φ]
      with y hy
    rw [W1p.gradient_ofTestFunctionₗ, hy]
  · refine integral_congr_ae ?_
    filter_upwards [W1p.value_ofTestFunctionₗ_ae (mu := volume) (p := 2) φ] with y hy
    rw [hy]

end Equation

/-! ### Bounds on the flat side -/

section Flat

/-- **Sup bound for the precise representative of a gradient at a flat boundary.** If the
precise representative `P` of `∇v` for the Lebesgue measure on the half-space `H` is `β`-Hölder
with constant `K` on a set `S` containing a point `y` of the closed half-space together with
`closedBall y R ∩ H`, and `closedBall y R ⊆ B`, then
`‖P y‖ ≤ K R^β + ‖∇v‖_{L²(B)} √(2 / |B_R|)`, where `|B_R|` is the volume of a ball of radius `R`. -/
private theorem norm_preciseRepresentative_le_of_holderOnWith {H B : Opens
    (EuclideanSpace ℝ (Fin (n + 1)))} (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ)
    (v : W1p volume B 2) {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {K β : ℝ≥0}
    (hP : HolderOnWith K β (MeasureTheory.preciseRepresentative
      (volume.restrict (H : Set (EuclideanSpace ℝ (Fin (n + 1))))) (W1p.gradient v)) S)
    {y : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 < R) (hy : y ∈ S)
    (hyH : c₀ ≤ ⟪y, ν⟫_ℝ) (hAS : closedBall y R ∩ H ⊆ S) (hAB : closedBall y R ⊆ B) :
    ‖MeasureTheory.preciseRepresentative (volume.restrict (H : Set (EuclideanSpace ℝ
        (Fin (n + 1))))) (W1p.gradient v) y‖ ≤
      K * R ^ (β : ℝ) + ‖W1p.gradient v‖ *
        √(2 / volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) R)) := by
  set A := closedBall y R ∩ (H : Set (EuclideanSpace ℝ (Fin (n + 1))))
  set ω := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) R)
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_closedBall_pos volume _ hR).ne' measure_closedBall_lt_top.ne
  have hHset : (H : Set (EuclideanSpace ℝ (Fin (n + 1)))) = {x | c₀ < ⟪x, ν⟫_ℝ} := Set.ext hH
  -- `A` contains at least half of `closedBall y R`.
  have hdens := volume.inv_two_mul_addHaar_closedBall_le_addHaar_closedBall_inter_setOf_lt_inner
    hν hyH (r := R)
  rw [← hHset, Measure.addHaar_closedBall_center] at hdens
  have hAt : volume A ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt measure_closedBall_lt_top).ne
  have hA0 : volume A ≠ 0 := by
    refine fun h => (measure_closedBall_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) hR).ne' ?_
    have h' : ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * volume (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) R)
        = 0 := le_antisymm (hdens.trans_eq h) zero_le
    simpa using h'
  have hAω : ω / 2 ≤ volume.real A := by
    have h := ENNReal.toReal_mono hAt hdens
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_inv, NNReal.coe_ofNat] at h
    simpa [ω, Measure.real, div_eq_inv_mul] using h
  have hAB' : A ⊆ (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ H := fun z hz => ⟨hAB hz.1, hz.2⟩
  have h := norm_le_add_sqrt_of_ae_eq (measurableSet_closedBall.inter H.isOpen.measurableSet) hA0
    hAt ((Lp.memLp (W1p.gradient v)).mono_measure
      (Measure.restrict_mono (hAB'.trans inter_subset_left) le_rfl))
    (ae_restrict_of_ae_restrict_of_subset hAB'
      (MeasureTheory.ae_eq_restrict_inter_preciseRepresentative_restrict B.isOpen
        (((Lp.memLp (W1p.gradient v)).mono_measure
          (Measure.restrict_mono inter_subset_left le_rfl)).locallyIntegrable (by norm_num))))
    (y := y) (M := K * R ^ (β : ℝ)) (C := ‖W1p.gradient v‖ ^ 2)
    (fun z hz => by
      rw [← dist_eq_norm]
      refine (hP.dist_le (hAS hz) hy).trans ?_
      gcongr
      exact mem_closedBall.1 hz.1)
    (Lp.setIntegral_norm_sq_le_norm_sq _ (hAB'.trans inter_subset_left))
  refine h.trans (add_le_add_right ?_ _)
  calc √(‖W1p.gradient v‖ ^ 2 / volume.real A)
      ≤ √(‖W1p.gradient v‖ ^ 2 / (ω / 2)) :=
        Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hAω)
    _ = ‖W1p.gradient v‖ * √(2 / ω) := by
        rw [show ‖W1p.gradient v‖ ^ 2 / (ω / 2) = ‖W1p.gradient v‖ ^ 2 * (2 / ω) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- **The flat estimate on a ball.** Let `B = B(y₀, r)` and let `H = {c₀ < ⟪y, ν⟫}`. There is a
constant `C`, depending only on `n`, `α`, `β`, `q`, `λ`, `Λ`, `M` and `r`, such that whenever
`v ∈ H¹(B)` vanishes on `B ∖ H` and solves `-∂ᵢ(aⁱʲ ∂ⱼv) = f - div G` weakly on `B ∩ H`, with `a`
uniformly elliptic and `a`, `G` Hölder on `B`, the precise representative `P` of `∇v` for the
Lebesgue measure on `H` is `β`-Hölder on `closedBall y₀ (r / 2) ∩ closure H` with constant `C Q`,
and bounded by `C Q` on `closedBall y₀ (r / 4) ∩ closure H`, where
`Q = K_G + ‖f‖_{L^q(B ∩ H)} + ‖∇v‖_{L²(B)}`. -/
private theorem exists_holderOnWith_preciseRepresentative_and_norm_le
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal) {H B : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hν : ν ≠ 0) (hH : ∀ x, x ∈ H ↔ c₀ < ⟪x, ν⟫_ℝ) {y₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {r : ℝ} (hr : 0 < r) (hB : (B : Set _) = ball y₀ r)
    (lam Lam M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : W1p volume B 2}
      {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
      UniformlyEllipticOn (ball y₀ r) a lam Lam →
      HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) (ball y₀ r) →
      (Ka : ℝ) * (r / 4) ^ (α : ℝ) ≤ M → HolderOnWith KG α G (ball y₀ r) →
      MemLp f q (volume.restrict ((B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ H)) →
      (∀ᵐ x ∂volume.restrict B, x ∉ H → W1p.value v x = 0) →
      (∀ φ : 𝓓(B ⊓ H, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left v)
          (W1p.ofTestFunctionₗ volume (B ⊓ H) 2 φ) =
        (∫ x in B ⊓ H, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
          ∫ x in B ⊓ H, f x * φ x) →
      HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict ((B : Set _) ∩ H))).toReal +
          ‖W1p.gradient v‖)).toNNReal β
        (MeasureTheory.preciseRepresentative (volume.restrict (H : Set _)) (W1p.gradient v))
        (closedBall y₀ (r / 2) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) ∧
      ∀ y ∈ closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ},
        ‖MeasureTheory.preciseRepresentative (volume.restrict (H : Set _)) (W1p.gradient v) y‖ ≤
          C * (KG + (eLpNorm f q (volume.restrict ((B : Set _) ∩ H))).toReal +
            ‖W1p.gradient v‖) := by
  obtain ⟨C₀, hC₀, hflat⟩ :=
    exists_holderOnWith_preciseRepresentative_restrict_gradient_of_holderOnWith_of_memLp
      (n := n) hβ hβ1 hβα hq hβq (lam := lam) (Lam := Lam) (M := M)
  set R := r / 4 with hRdef
  have hR : 0 < R := by positivity
  set S := closedBall y₀ (r / 2) ∩ {y : EuclideanSpace ℝ (Fin (n + 1)) | c₀ ≤ ⟪y, ν⟫_ℝ}
  have hthick : thickening R S ⊆ ball y₀ r := by
    refine (thickening_subset_of_subset R (inter_subset_left : S ⊆ closedBall y₀ (r / 2))).trans ?_
    rw [thickening_closedBall hR (by positivity)]
    exact ball_subset_ball (by linarith)
  set c₁ := max (R ^ ((α : ℝ) - β)) (max (R ^ (1 - ((n : ℝ) + 1) / q.toReal - β))
    (R ^ (-(((n : ℝ) + 1) / 2 + β))))
  set ω := volume.real (closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) R)
  refine ⟨C₀ * c₁ * (1 + R ^ (β : ℝ)) + √(2 / ω), by positivity, ?_⟩
  intro v a G f Ka KG ha haK hM hGK hf hv0 hv
  set Q := KG + (eLpNorm f q (volume.restrict ((B : Set _) ∩ H))).toReal + ‖W1p.gradient v‖
  have hQ : 0 ≤ Q := by positivity
  -- The flat Schauder estimate, with the data norm on the thickening bounded by `Q`.
  have hRS : thickening R S ⊆ (B : Set _) := hB ▸ hthick
  have hfthick : (eLpNorm f q (volume.restrict (thickening R S ∩ H))).toReal ≤
      (eLpNorm f q (volume.restrict ((B : Set _) ∩ H))).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono (inter_subset_inter_left _ hRS) le_rfl))
  have hP := hflat (S := S) hν hH (fun x hx => hx.2) (ha.mono_set hthick) (haK.mono hthick)
    (hGK.mono hthick) hM
    (hf.mono_measure (Measure.restrict_mono (inter_subset_inter_left _ hRS) le_rfl)) hv0 hv hR
    hRS
  have hKP : C₀ * (KG * R ^ ((α : ℝ) - β) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
      (eLpNorm f q (volume.restrict (thickening R S ∩ H))).toReal +
      R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient v‖) ≤ C₀ * c₁ * Q := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hC₀
    have h1 : R ^ ((α : ℝ) - β) ≤ c₁ := le_max_left _ _
    have h2 : R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) ≤ c₁ :=
      (le_max_left _ _).trans (le_max_right _ _)
    have h3 : R ^ (-(((n : ℝ) + 1) / 2 + β)) ≤ c₁ := (le_max_right _ _).trans (le_max_right _ _)
    calc KG * R ^ ((α : ℝ) - β) + R ^ (1 - ((n : ℝ) + 1) / q.toReal - β) *
          (eLpNorm f q (volume.restrict (thickening R S ∩ H))).toReal +
          R ^ (-(((n : ℝ) + 1) / 2 + β)) * ‖W1p.gradient v‖
        ≤ KG * c₁ + c₁ * (eLpNorm f q (volume.restrict ((B : Set _) ∩ H))).toReal +
            c₁ * ‖W1p.gradient v‖ := by
          gcongr
      _ = c₁ * Q := by ring
  have hc₁ : 0 ≤ C₀ * c₁ := by positivity
  have hPQ := hP.mono_const (Real.toNNReal_le_toNNReal hKP)
  refine ⟨hPQ.mono_const (Real.toNNReal_le_toNNReal ?_), fun y hy => ?_⟩
  · refine mul_le_mul_of_nonneg_right ?_ hQ
    nlinarith [Real.sqrt_nonneg (2 / ω), Real.rpow_nonneg hR.le (β : ℝ)]
  · -- The sup bound at `y`, from the Hölder bound on `closedBall y R ∩ H ⊆ S`.
    have hyS : y ∈ S := ⟨closedBall_subset_closedBall (by linarith) hy.1, hy.2⟩
    have hAS : closedBall y R ∩ H ⊆ S := fun z hz =>
      ⟨mem_closedBall.2 ((dist_triangle z y y₀).trans (by
        linarith [mem_closedBall.1 hz.1, mem_closedBall.1 hy.1])),
        le_of_lt ((hH z).1 hz.2)⟩
    have hAB : closedBall y R ⊆ (B : Set _) := fun z hz => hB ▸ mem_ball.2
      ((dist_triangle z y y₀).trans_lt (by
        linarith [mem_closedBall.1 hz, mem_closedBall.1 hy.1]))
    refine (norm_preciseRepresentative_le_of_holderOnWith hν hH v hPQ hR hyS hy.2 hAS hAB).trans ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    have hv' : ‖W1p.gradient v‖ ≤ Q := by
      have : 0 ≤ (eLpNorm f q (volume.restrict ((B : Set _) ∩ H))).toReal := ENNReal.toReal_nonneg
      simp only [Q]
      linarith [KG.coe_nonneg]
    nlinarith [Real.sqrt_nonneg (2 / ω), Real.rpow_nonneg hR.le (β : ℝ)]

end Flat

/-! ### Back to the curved side -/

section Back

variable {L : ℝ} {α : ℝ≥0}

/-- **Hölder and sup bounds for the unflattened gradient.** If `P` is `β`-Hölder with constant
`K` and bounded by `K` on `S'`, `Ψ` is `L`-Lipschitz on `T ⊆ U` and maps `T` into `S'`, and `DΨ` is
`α`-Hölder on `U` with constant `K_T` and `‖DΨ‖ ≤ L`, then for `β ≤ α` the field
`g x = DΨ(x)* P(Ψ x)` is `β`-Hölder on `T` and bounded there, with constants
`(L c L^β + c K_T D^(α - β) + L c) Q` whenever `K ≤ c Q`, where `D` bounds the distances in `T`. -/
private theorem holderOnWith_adjoint_fderiv_apply_comp
    (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L 1) (hL : 0 ≤ L)
    {T S' : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hTU : T ⊆ U) {D : ℝ≥0}
    (hD : ∀ x ∈ T, ∀ x' ∈ T, edist x x' ≤ D) (hΨl : LipschitzOnWith L.toNNReal Ψ T)
    (hΨT : MapsTo Ψ T S') {β KT : ℝ≥0} (hβα : β ≤ α) (hT : HolderOnWith KT α (fderiv ℝ Ψ) U)
    {P : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K c Q : ℝ}
    (hP : HolderOnWith K.toNNReal β P S') (hPb : ∀ y ∈ S', ‖P y‖ ≤ K) (hc : 0 ≤ c)
    (hQ : 0 ≤ Q) (hKQ : K ≤ c * Q) :
    HolderOnWith ((L * c * L ^ (β : ℝ) + c * (KT * D ^ ((α : ℝ) - β)) + L * c) * Q).toNNReal β
        (fun x => (fderiv ℝ Ψ x).adjoint (P (Ψ x))) T ∧
      ∀ x ∈ T, ‖(fderiv ℝ Ψ x).adjoint (P (Ψ x))‖ ≤
        (L * c * L ^ (β : ℝ) + c * (KT * D ^ ((α : ℝ) - β)) + L * c) * Q := by
  have hTL (x) (hx : x ∈ T) : ‖(fderiv ℝ Ψ x).adjoint‖ ≤ L.toNNReal := by
    rw [LinearIsometryEquiv.norm_map]
    exact (hΨ.norm_fderiv_le (k := 0) x (hTU hx)).trans (Real.le_coe_toNNReal L)
  have hTa : HolderOnWith (KT * D ^ ((α : ℝ) - β)) β (fun x => (fderiv ℝ Ψ x).adjoint) T :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin (n + 1)))
      (F := EuclideanSpace ℝ (Fin (n + 1)))).isometry.comp_holderOnWith (hT.mono hTU)).of_le hD
      hβα
  have hPΨ : HolderOnWith (K.toNNReal * L.toNNReal ^ (β : ℝ)) β (fun x => P (Ψ x)) T := by
    simpa only [mul_one, Function.comp_def] using hP.comp hΨl.holderOnWith hΨT
  have hPb' : ∀ y ∈ S', ‖P y‖ ≤ K.toNNReal := fun y hy =>
    (hPb y hy).trans (Real.le_coe_toNNReal K)
  have hKQ' : (K.toNNReal : ℝ) ≤ c * Q := by
    rw [Real.coe_toNNReal']
    exact max_le hKQ (by positivity)
  have hKD : 0 ≤ (KT : ℝ) * (D : ℝ) ^ ((α : ℝ) - β) := by positivity
  have hLβ : 0 ≤ L ^ (β : ℝ) := by positivity
  refine ⟨?_, fun x hx => ?_⟩
  · have h := (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)))).holderOnWith_comp₂ hTa hPΨ hTL fun x hx => hPb' _ (hΨT hx)
    refine (h.mono_const (mul_le_of_le_one_left zero_le ContinuousLinearMap.norm_id_le)).mono_const
      ((Real.le_toNNReal_iff_coe_le (by positivity)).2 ?_)
    push_cast
    rw [Real.coe_toNNReal _ hL]
    nlinarith [mul_le_mul_of_nonneg_left hKQ' (mul_nonneg hL hLβ),
      mul_le_mul_of_nonneg_right hKQ' hKD, mul_nonneg (mul_nonneg hL hc) hQ]
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ((mul_le_mul (hTL x hx) (hPb' _ (hΨT hx))
      (norm_nonneg _) (by positivity)).trans ?_)
    rw [Real.coe_toNNReal _ hL]
    nlinarith [mul_le_mul_of_nonneg_left hKQ' hL, mul_nonneg (mul_nonneg (mul_nonneg hL hc) hLβ) hQ,
      mul_nonneg (mul_nonneg hc hKD) hQ]

/-- **The gradient on the curved side.** If `P` agrees almost everywhere on `B ∩ H` with the
gradient of the flattened function `v = u ∘ Φ`, then `∇u(x) = DΨ(x)* P(Ψ x)` for almost every
`x ∈ D = Φ (B ∩ H)`. -/
private theorem ae_gradient_eq_adjoint_fderiv_apply
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U)
    {W B V D H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hVW : V ≤ W) (hDU : D ≤ U)
    (hΦB : Wkp.IsChangeOfVariables 1 B V Φ L 1) (hΨD : Wkp.IsChangeOfVariables 1 D (B ⊓ H) Ψ L 1)
    (u : W1p volume W 2) {P : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hP : ∀ᵐ y ∂volume.restrict ((B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ H),
      (W1p.gradient (hΦB.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hVW u)) :
        EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) y = P y) :
    ∀ᵐ x ∂volume.restrict (D : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) x =
        (fderiv ℝ Ψ x).adjoint (P (Ψ x)) := by
  have hBH : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ H ⊆ B := inter_subset_left
  -- On the flat side, `P y = DΦ(y)* ∇u(Φ y)` for almost every `y ∈ B ∩ H`.
  have hflat : ∀ᵐ y ∂volume.restrict (((B ⊓ H : Opens _) : Set (EuclideanSpace ℝ (Fin (n + 1))))),
      P y = (fderiv ℝ Φ y).adjoint (W1p.gradient u (Φ y)) := by
    filter_upwards [hP, ae_restrict_of_ae_restrict_of_subset hBH
      (W1p.gradient_compL_ae Φ ENNReal.ofNat_ne_top hΦB.differentiableOn hΦB.injOn hΦB.mapsTo
        hΦB.norm_fderiv_le hΦB.pos hΦB.le_abs_det (W1p.restrictL hVW u)),
      ae_restrict_of_ae_restrict_of_subset hBH (hΦB.ae_comp (W1p.gradient_restrictL_ae hVW u))]
      with y h1 h2 h3
    rw [← h1, h2, h3]
  filter_upwards [hΨD.ae_comp hflat, ae_restrict_mem D.isOpen.measurableSet] with x hx hxD
  rw [hx, hΦΨ (hDU hxD), ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp,
    hΨ.fderiv_comp_fderiv_eq_id hΦ hΦΨ hΨΦ (hDU hxD),
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]

end Back

/-! ### The estimate near a curved boundary -/

section Main

variable {L : ℝ} {α : ℝ≥0}

/-- **Radii for a flattening chart.** Around a point `y₀ ∈ U'` there are a radius `r` with
`B(y₀, r) ⊆ U'`, on which `Φ` is `L`-Lipschitz and maps into `B(Φ y₀, (L + 1) r)`, and a radius
`ρ'` with `B(Φ y₀, ρ') ⊆ U`, on which `Ψ` is `L`-Lipschitz and maps into `B(y₀, r / 4)`. -/
private theorem exists_radii_of_isChangeOfVariables
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') {y₀ : EuclideanSpace ℝ (Fin (n + 1))} (hy₀ : y₀ ∈ U') :
    ∃ r ρ' : ℝ, 0 < r ∧ 0 < ρ' ∧ 0 ≤ L ∧ ball y₀ r ⊆ U' ∧ ball (Φ y₀) ρ' ⊆ U ∧
      LipschitzOnWith L.toNNReal Φ (ball y₀ r) ∧ MapsTo Φ (ball y₀ r) (ball (Φ y₀) ((L + 1) * r)) ∧
      LipschitzOnWith L.toNNReal Ψ (ball (Φ y₀) ρ') ∧
      MapsTo Ψ (ball (Φ y₀) ρ') (ball y₀ (r / 4)) := by
  have hL : 0 ≤ L := (norm_nonneg _).trans (hΦ.norm_fderiv_le (k := 0) y₀ hy₀)
  obtain ⟨r, hr, hrU'⟩ := Metric.isOpen_iff.1 U'.isOpen y₀ hy₀
  obtain ⟨ρ₁, hρ₁, hρ₁U⟩ := Metric.isOpen_iff.1 U.isOpen (Φ y₀) (hΦ.mapsTo hy₀)
  -- A map with `‖Df‖ ≤ L` on a ball inside its domain is `L`-Lipschitz there.
  have hlip {f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
      {V₁ V₂ : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hf : Wkp.IsChangeOfVariables 1 V₁ V₂ f L 1)
      {z : EuclideanSpace ℝ (Fin (n + 1))} {ε : ℝ} (hε : ball z ε ⊆ V₁) :
      LipschitzOnWith L.toNNReal f (ball z ε) :=
    Convex.lipschitzOnWith_of_nnNorm_fderiv_le
      (fun y hy => (hf.differentiableOn y (hε hy)).differentiableAt (V₁.isOpen.mem_nhds (hε hy)))
      (fun y hy => by
        rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal _ hL]
        exact hf.norm_fderiv_le (k := 0) y (hε hy)) (convex_ball z ε)
  set ρ' := min ρ₁ (r / (4 * (L + 1)))
  have hρ' : 0 < ρ' := lt_min hρ₁ (by positivity)
  have hρ'U : ball (Φ y₀) ρ' ⊆ U := (ball_subset_ball (min_le_left _ _)).trans hρ₁U
  refine ⟨r, ρ', hr, hρ', hL, hrU', hρ'U, hlip hΦ hrU', fun y hy => ?_, hlip hΨ hρ'U,
    fun x hx => ?_⟩
  · have h := (hlip hΦ hrU').dist_le_mul y hy y₀ (mem_ball_self hr)
    rw [Real.coe_toNNReal _ hL] at h
    rw [mem_ball] at hy ⊢
    nlinarith
  · have h := (hlip hΨ hρ'U).dist_le_mul x hx (Φ y₀) (mem_ball_self hρ')
    rw [Real.coe_toNNReal _ hL, hΨΦ hy₀] at h
    rw [mem_ball] at hx ⊢
    have hx' : dist x (Φ y₀) < r / (4 * (L + 1)) := hx.trans_le (min_le_right _ _)
    have h4 : (L + 1) * (r / (4 * (L + 1))) = r / 4 := by field_simp
    nlinarith [dist_nonneg (x := x) (y := Φ y₀)]

/-- **The flattened function vanishes off the half-space.** If `u ∈ H¹(W)` vanishes on `W ∖ Ω`
and `Φ` maps the part of `U'` in the half-space `H = {c₀ < ⟪y, ν⟫}` onto `Ω ∩ U`, injectively,
then `u ∘ Φ` vanishes almost everywhere on `B ∖ H`, for every ball `B ⊆ U'` that `Φ` maps into
`V ⊆ W`. -/
private theorem ae_value_w1pCompL_eq_zero (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (himage : Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') = (Ω : Set _) ∩ U)
    {W B V H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hrU' : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ U') (hVW : V ≤ W)
    (hΦB : Wkp.IsChangeOfVariables 1 B V Φ L 1) {u : W1p volume W 2}
    (hu0 : ∀ᵐ x ∂volume.restrict W, x ∉ Ω → W1p.value u x = 0)
    (hH : ∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ) :
    ∀ᵐ y ∂volume.restrict B, y ∉ H →
      W1p.value (hΦB.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hVW u)) y = 0 := by
  filter_upwards [hΦB.value_w1pCompL_ae ENNReal.ofNat_ne_top (W1p.restrictL hVW u),
    hΦB.ae_comp (W1p.value_restrictL_ae hVW u),
    hΦB.ae_comp (ae_restrict_of_ae_restrict_of_subset hVW hu0),
    ae_restrict_mem B.isOpen.measurableSet] with y h1 h2 h3 hyB hyH
  rw [h1, h2]
  refine h3 fun hΦy => hyH ?_
  have hx' : Φ y ∈ Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') := by
    rw [himage]
    exact ⟨hΦy, hΦ.mapsTo (hrU' hyB)⟩
  obtain ⟨y', hy', hyy'⟩ := hx'
  have : y' = y := by rw [← hΨΦ hy'.2, hyy', hΨΦ (hrU' hyB)]
  exact (hH y).2 (this ▸ hy'.1)

/-- **The flat data are bounded by the curved data.** For the flattened function `v = u ∘ Φ`,
the flattened datum `f' = pullbackDensity Φ f` and a constant `c_G`,
`K_G c_G + ‖f'‖_{L^q(B ∩ H)} + ‖∇v‖_{L²(B)} ≤ max c_G (max 1 L) (K_G + ‖f‖_{L^q(S)} + ‖u‖_{H¹(W)})`
whenever `Φ` maps `B ∩ H` onto `D ⊆ S`. -/
private theorem flat_data_le {W B V D H : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hΦB : Wkp.IsChangeOfVariables 1 B V Φ L 1) (hΦD : Wkp.IsChangeOfVariables 1 (B ⊓ H) D Φ L 1)
    (hΨD : Wkp.IsChangeOfVariables 1 D (B ⊓ H) Ψ L 1) (hΨΦ : LeftInvOn Ψ Φ (B ⊓ H))
    (hΦΨ : RightInvOn Ψ Φ D) (hVW : V ≤ W) {S : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hDS : (D : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ S) {u : W1p volume W 2}
    {q : ℝ≥0∞} {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hf : MemLp f q (volume.restrict S))
    {KG cG : ℝ≥0} :
    ((KG * cG : ℝ≥0) : ℝ) + (eLpNorm (pullbackDensity Φ f) q
        (volume.restrict ((B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ H))).toReal +
        ‖W1p.gradient (hΦB.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hVW u))‖ ≤
      max (cG : ℝ) (max 1 L) * (KG + (eLpNorm f q (volume.restrict S)).toReal + ‖u‖) := by
  have hfb : (eLpNorm (pullbackDensity Φ f) q (volume.restrict ((B : Set _) ∩ H))).toReal ≤
      (eLpNorm f q (volume.restrict S)).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top ((eLpNorm_pullbackDensity_le hΦD hΨD hΨΦ hΦΨ
      (hf.mono_measure (Measure.restrict_mono hDS le_rfl)).aestronglyMeasurable).trans
        (eLpNorm_mono_measure f (Measure.restrict_mono hDS le_rfl)))
  have hvb : ‖W1p.gradient (hΦB.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hVW u))‖ ≤
      max 1 L * ‖u‖ := by
    refine (W1p.norm_gradient_le _).trans ((W1p.norm_compL_le Φ _ _ _ _ _ _ _ _).trans ?_)
    simp only [inv_one, Real.one_rpow, mul_one]
    exact mul_le_mul_of_nonneg_left (W1p.norm_restrictL_le hVW u) (by positivity)
  have h1 : (cG : ℝ) ≤ max (cG : ℝ) (max 1 L) := le_max_left _ _
  have h2 : 1 ≤ max (cG : ℝ) (max 1 L) := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : max 1 L ≤ max (cG : ℝ) (max 1 L) := le_max_right _ _
  have hf0 : 0 ≤ (eLpNorm f q (volume.restrict S)).toReal := ENNReal.toReal_nonneg
  rw [NNReal.coe_mul]
  nlinarith [KG.coe_nonneg, norm_nonneg u, cG.coe_nonneg]

/-- **The pieces of a flattening chart over a ball.** For an open `B ⊆ U'` there are open sets
`V` and `D` such that `Φ` is a change of variables from `B` into `V` and from `B ∩ H` into `D`,
with inverse `Ψ` from `D` into `B ∩ H`, where `V ⊆ U`, `D ⊆ V ∩ Ω` and `D` contains every point of
`Ω ∩ U` that `Ψ` maps into `B`. -/
private theorem exists_opens_of_isChangeOfVariables
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U')
    (himage : Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') = (Ω : Set _) ∩ U)
    {B H : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (hH : ∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ)
    (hBU' : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ U') :
    ∃ V D : Opens (EuclideanSpace ℝ (Fin (n + 1))),
      (∀ x ∈ (V : Set (EuclideanSpace ℝ (Fin (n + 1)))), Ψ x ∈ B) ∧ D ≤ V ∧
      (D : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Ω ∧ V ≤ U ∧
      (∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ U, Ψ x ∈ B → x ∈ D) ∧
      Wkp.IsChangeOfVariables 1 B V Φ L 1 ∧ Wkp.IsChangeOfVariables 1 (B ⊓ H) D Φ L 1 ∧
      Wkp.IsChangeOfVariables 1 D (B ⊓ H) Ψ L 1 := by
  let V : Opens (EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨U ∩ Ψ ⁻¹' B, hΨ.differentiableOn.continuousOn.isOpen_inter_preimage U.isOpen B.isOpen⟩
  have hΦB : Wkp.IsChangeOfVariables 1 B V Φ L 1 :=
    hΦ.mono_set (fun y hy => hBU' hy) fun y hy =>
      ⟨hΦ.mapsTo (hBU' hy), by rw [mem_preimage, hΨΦ (hBU' hy)]; exact hy⟩
  refine ⟨V, V ⊓ Ω, fun x hx => hx.2, inf_le_left, fun x hx => hx.2, fun x hx => hx.1,
    fun x hx hxB => ⟨⟨hx.2, hxB⟩, hx.1⟩, hΦB, ?_, ?_⟩
  · refine hΦ.mono_set (fun y hy => hBU' hy.1) fun y hy => ⟨hΦB.mapsTo hy.1, ?_⟩
    have hmem : Φ y ∈ (Ω : Set _) ∩ U := by
      rw [← himage]
      exact mem_image_of_mem Φ ⟨(hH y).1 hy.2, hBU' hy.1⟩
    exact hmem.1
  · refine hΨ.mono_set (fun x hx => hx.1.1) fun x hx => ?_
    have hx' : x ∈ Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') := by
      rw [himage]
      exact ⟨hx.2, hx.1.1⟩
    obtain ⟨y, hy, rfl⟩ := hx'
    exact ⟨hx.1.2, by rw [hΨΦ hy.2]; exact (hH y).2 hy.1⟩

/-- **The folded flattened coefficients.** Let `Φ` and `Ψ` be mutually inverse changes of
variables with Jacobian determinant one and `DΨ` `α`-Hölder, let `B(y₀, r) ⊆ U'` be centred on the
hyperplane `{⟪y, ν⟫ = c₀}`, and let `Φ` be `L`-Lipschitz on `B(y₀, r)` and map its part in the
closed half-space into `t`. If `a` is uniformly elliptic and `α`-Hölder on `t`, and `G` is
`α`-Hölder and bounded by `D` on `t`, then the flattened coefficients `pullbackPrincipal Φ a` and
`pullbackDrift Φ G`, composed with the fold across the hyperplane, are uniformly elliptic and
`α`-Hölder on all of `B(y₀, r)`, with explicit constants. -/
private theorem folded_coefficient_bounds
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) (hν : ν ≠ 0)
    {y₀ : EuclideanSpace ℝ (Fin (n + 1))} (hy₀ν : ⟪y₀, ν⟫_ℝ = c₀) {r : ℝ} (hr : 0 < r)
    (hrU' : ball y₀ r ⊆ U') {t : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hst : MapsTo Φ (ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) t)
    (hΦl : LipschitzOnWith L.toNNReal Φ (ball y₀ r)) {KT : ℝ≥0}
    (hT : HolderOnWith KT α (fderiv ℝ Ψ) U)
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {lam Lam : ℝ}
    {Ka : ℝ≥0} (hell : UniformlyEllipticOn t a lam Lam)
    (hKa : HolderOnWith Ka α (fun x => matrixBilinearForm (a x)) t)
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {KG D : ℝ≥0}
    (hG : HolderOnWith KG α G t) (hGD : ∀ x ∈ t, ‖G x‖ ≤ D) :
    UniformlyEllipticOn (ball y₀ r)
        (pullbackPrincipal Φ a ∘ fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y)
        (1 * lam / L ^ 2) (L ^ Fintype.card (Fin (n + 1)) * L ^ 2 * Lam) ∧
      HolderOnWith (Ka * L.toNNReal ^ (α : ℝ) * L.toNNReal * L.toNNReal +
          Lam.toNNReal * (KT * L.toNNReal ^ (α : ℝ)) * L.toNNReal +
          Lam.toNNReal * L.toNNReal * (KT * L.toNNReal ^ (α : ℝ))) α
        (fun y => matrixBilinearForm ((pullbackPrincipal Φ a ∘
          fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y) y)) (ball y₀ r) ∧
      HolderOnWith (L.toNNReal * (KG * L.toNNReal ^ (α : ℝ)) + D * (KT * L.toNNReal ^ (α : ℝ))) α
        (pullbackDrift Φ G ∘
          fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y) (ball y₀ r) := by
  set s := ball y₀ r ∩ {y : EuclideanSpace ℝ (Fin (n + 1)) | c₀ ≤ ⟪y, ν⟫_ℝ}
  have hsU' : s ⊆ U' := fun y hy => hrU' hy.1
  have hell' : UniformlyEllipticOn s (pullbackPrincipal Φ a) (1 * lam / L ^ 2)
      (L ^ Fintype.card (Fin (n + 1)) * L ^ 2 * Lam) :=
    hell.pullbackPrincipal hst ⟨y₀, mem_ball_self hr, hy₀ν.ge⟩
      (fun y hy => hΦ.norm_fderiv_le (k := 0) y (hsU' hy))
      (fun y hy w => by
        calc ‖w‖ = ‖fderiv ℝ Ψ (Φ y) (fderiv ℝ Φ y w)‖ := by
              rw [← ContinuousLinearMap.comp_apply, hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ
                (hsU' hy), ContinuousLinearMap.id_apply]
          _ ≤ L * ‖fderiv ℝ Φ y w‖ := (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hΨ.norm_fderiv_le (k := 0) _ (hΦ.mapsTo (hsU' hy)))
                (norm_nonneg _)))
      one_pos fun y hy => hΦ.le_abs_det y (hsU' hy)
  -- The fold maps `B(y₀, r)` into its part in the closed half-space and is `1`-Lipschitz.
  have hFs : MapsTo (fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y)
      (ball y₀ r) s := fun y hy =>
    ⟨mapsTo_ite_hyperplaneReflection_ball hy₀ν r hy, le_inner_ite_hyperplaneReflection hν c₀ y⟩
  have hF1 := (lipschitzWith_one_ite_hyperplaneReflection ν c₀).lipschitzOnWith
    (s := ball y₀ r)
  -- On `s`, `DΨ ∘ Φ` is an `α`-Hölder left inverse of `DΦ` bounded by `L`, and `|det DΦ| = 1`.
  have hcomp (y) (hy : y ∈ s) :=
    hΦ.fderiv_comp_fderiv_eq_id hΨ hΨΦ hΦΨ (hsU' hy)
  have habs (y) (hy : y ∈ s) : |(fderiv ℝ Φ y).det| = 1 :=
    hΦ.abs_det_fderiv_eq_one hΨ hΨΦ hΦΨ (hsU' hy)
  have hTs : HolderOnWith (KT * L.toNNReal ^ (α : ℝ)) α (fun y => fderiv ℝ Ψ (Φ y)) s := by
    simpa only [mul_one, Function.comp_def] using
      hT.comp (hΦl.mono inter_subset_left).holderOnWith fun y hy => hΦ.mapsTo (hsU' hy)
  have hTL (y) (hy : y ∈ s) : ‖fderiv ℝ Ψ (Φ y)‖ ≤ L.toNNReal :=
    (hΨ.norm_fderiv_le (k := 0) _ (hΦ.mapsTo (hsU' hy))).trans (Real.le_coe_toNNReal L)
  have hJ : HolderOnWith 0 α (fun y => |(fderiv ℝ Φ y).det|) s := fun x hx y hy => by
    simp only [habs x hx, habs y hy, edist_self, zero_le]
  have hJb (y) (hy : y ∈ s) : |(fderiv ℝ Φ y).det| ≤ ((1 : ℝ≥0) : ℝ) := by
    rw [habs y hy, NNReal.coe_one]
  refine ⟨hell'.comp hFs, ?_, ?_⟩
  · simpa only [NNReal.one_rpow, one_mul, mul_zero, add_zero, mul_one, Function.comp_def] using
      (holderOnWith_matrixBilinearForm_pullbackPrincipal hst hcomp (hΦl.mono inter_subset_left)
        hTs hTL hJ hJb hKa fun y hy =>
          (hell.opNorm_matrixBilinearForm_le hy).trans (Real.le_coe_toNNReal Lam)).comp
        hF1.holderOnWith hFs
  · simpa only [NNReal.one_rpow, one_mul, mul_zero, add_zero, mul_one] using
      (holderOnWith_pullbackDrift hst hcomp (hΦl.mono inter_subset_left) hTs hTL hJ hJb hG
        hGD).comp hF1.holderOnWith hFs

/-- **Schauder estimate near a curved boundary for divergence-form equations**, in a flattening
chart. Let `Φ : U' → U` and `Ψ : U → U'` be mutually inverse changes of variables of order one
with Jacobian determinant one, with `DΨ` `α`-Hölder on `U`, such that `Φ` maps the part of `U'`
in the half-space `{c₀ < ⟪y, ν⟫}` onto `Ω ∩ U`, and let `y₀ ∈ U'` lie on the boundary
hyperplane, so that `x₀ = Φ y₀` is a boundary point of `Ω`. Let `0 < β < 1` with `β ≤ α`, let
`2 ≤ q ≤ ∞` and `β ≤ 1 - (n + 1) / q`, and fix `λ`, `Λ` and `M`. There are radii `ρ, ρ' > 0` and
a constant `C` such that the following holds for every open `W ⊇ B(x₀, ρ)` and every
`u ∈ H¹(W)` vanishing on `W ∖ Ω` and solving

`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `W ∩ Ω`

(tested against test functions), where on `closure Ω ∩ B(x₀, ρ)` the coefficient `a` is uniformly
elliptic with constants `λ, Λ` and `α`-Hölder with constant `K_a ≤ M`, the field `G` is
`α`-Hölder with constant `K_G`, and `f ∈ L^q(Ω ∩ B(x₀, ρ))`: the gradient `∇u` agrees almost
everywhere on `Ω ∩ B(x₀, ρ')` with a function `g` that is `β`-Hölder on `closure Ω ∩ B(x₀, ρ')`
with constant `C Q` and bounded there by `C Q`, where

`Q = K_G + ‖f‖_{L^q(Ω ∩ B(x₀, ρ))} + ‖u‖_{H¹(W)}`.

So `u` is `C^{1,β}` up to the boundary near `x₀`. The constant does not depend on `u`, `a`, `G` or
`f`, only on the chart, `n`, `α`, `β`, `q`, `λ`, `Λ` and `M`. -/
theorem exists_holderOnWith_gradient_of_isChangeOfVariables
    {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞} (hq : 2 ≤ q)
    (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    (hΦ : Wkp.IsChangeOfVariables 1 U' U Φ L 1) (hΨ : Wkp.IsChangeOfVariables 1 U U' Ψ L 1)
    (hΨΦ : LeftInvOn Ψ Φ U') (hΦΨ : RightInvOn Ψ Φ U) (hν : ν ≠ 0)
    (himage : Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') = (Ω : Set _) ∩ U) {KT : ℝ≥0}
    (hT : HolderOnWith KT α (fderiv ℝ Ψ) U) {y₀ : EuclideanSpace ℝ (Fin (n + 1))}
    (hy₀ : y₀ ∈ U') (hy₀ν : ⟪y₀, ν⟫_ℝ = c₀) (lam Lam M : ℝ) :
    ∃ ρ ρ' C : ℝ, 0 < ρ ∧ 0 < ρ' ∧ 0 ≤ C ∧
      ∀ {W : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume W 2}
        {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
        ball (Φ y₀) ρ ⊆ W →
        UniformlyEllipticOn (closure (Ω : Set _) ∩ ball (Φ y₀) ρ) a lam Lam →
        HolderOnWith Ka α (fun x => matrixBilinearForm (a x))
          (closure (Ω : Set _) ∩ ball (Φ y₀) ρ) → (Ka : ℝ) ≤ M →
        HolderOnWith KG α G (closure (Ω : Set _) ∩ ball (Φ y₀) ρ) →
        MemLp f q (volume.restrict ((Ω : Set _) ∩ ball (Φ y₀) ρ)) →
        (∀ᵐ x ∂volume.restrict W, x ∉ Ω → W1p.value u x = 0) →
        (∀ φ : 𝓓(W ⊓ Ω, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
            (W1p.ofTestFunctionₗ volume (W ⊓ Ω) 2 φ) =
          (∫ x in W ⊓ Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
            ∫ x in W ⊓ Ω, f x * φ x) →
        ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            =ᵐ[volume.restrict ((Ω : Set _) ∩ ball (Φ y₀) ρ')] g ∧
          HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩
            ball (Φ y₀) ρ))).toReal + ‖u‖)).toNNReal β g (closure (Ω : Set _) ∩ ball (Φ y₀) ρ') ∧
          ∀ x ∈ closure (Ω : Set _) ∩ ball (Φ y₀) ρ', ‖g x‖ ≤
            C * (KG + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩ ball (Φ y₀) ρ))).toReal + ‖u‖)
    := by
  -- The flat half-space, the radii of the chart, and the constants, fixed before the data.
  let H : Opens (EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨{y | c₀ < ⟪y, ν⟫_ℝ}, isOpen_lt continuous_const (continuous_id.inner continuous_const)⟩
  have hH : ∀ y, y ∈ H ↔ c₀ < ⟪y, ν⟫_ℝ := fun _ => Iff.rfl
  obtain ⟨r, ρ', hr, hρ', hL, hrU', hρ'U, hΦl, hΦball, hΨl, hΨball⟩ :=
    exists_radii_of_isChangeOfVariables hΦ hΨ hΨΦ hy₀
  set ρ := (L + 1) * r
  have hρ : 0 < ρ := by positivity
  let B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball y₀ r, isOpen_ball⟩
  have hB : (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) = ball y₀ r := rfl
  set KΦ := L.toNNReal
  set Ka₀ : ℝ≥0 := M.toNNReal * KΦ ^ (α : ℝ) * KΦ * KΦ + Lam.toNNReal * (KT * KΦ ^ (α : ℝ)) * KΦ +
    Lam.toNNReal * KΦ * (KT * KΦ ^ (α : ℝ))
  set cG : ℝ≥0 := KΦ * KΦ ^ (α : ℝ) + ρ.toNNReal ^ (α : ℝ) * (KT * KΦ ^ (α : ℝ))
  obtain ⟨C₁, hC₁, hflat⟩ := exists_holderOnWith_preciseRepresentative_and_norm_le hβ hβ1 hβα hq
    hβq hν hH hr hB (1 * lam / L ^ 2) (L ^ Fintype.card (Fin (n + 1)) * L ^ 2 * Lam)
    (Ka₀ * (r / 4) ^ (α : ℝ))
  set c₂ : ℝ := max (cG : ℝ) (max 1 L)
  set D : ℝ≥0 := (2 * ρ').toNNReal
  refine ⟨ρ, ρ', L * (C₁ * c₂) * L ^ (β : ℝ) + C₁ * c₂ * (KT * D ^ ((α : ℝ) - β)) + L * (C₁ * c₂),
    hρ, hρ', by positivity, ?_⟩
  intro W u a G f Ka KG hW hell hKa hKaM hGK hf hu0 hu
  set Q := KG + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩ ball (Φ y₀) ρ))).toReal + ‖u‖
  have hQ : 0 ≤ Q := by positivity
  -- The pieces of the chart: `Φ` maps `B` onto `V ⊆ W`, and `B ∩ H` onto `D' ⊆ V ∩ Ω`.
  set t := closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball (Φ y₀) ρ
  have hst : MapsTo Φ (ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) t := fun y hy =>
    ⟨mapsTo_closure_of_image_eq hν U'.isOpen hΦ.differentiableOn.continuousOn himage
      ⟨hy.2, hrU' hy.1⟩,
      hΦball hy.1⟩
  have hy₀s : y₀ ∈ ball y₀ r ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ} := ⟨mem_ball_self hr, hy₀ν.ge⟩
  obtain ⟨V, D', hVB, hDV, hDΩ, hVU, hsubD, hΦB, hΦD, hΨD⟩ :=
    exists_opens_of_isChangeOfVariables hΦ hΨ hΨΦ himage hH (B := B) hrU'
  have hD'U : D' ≤ U := hDV.trans hVU
  have hΨΦB : LeftInvOn Ψ Φ (B ⊓ H) := hΨΦ.mono fun y hy => hrU' hy.1
  have hΦΨD : RightInvOn Ψ Φ D' := hΦΨ.mono hD'U
  have hVρ : (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ ball (Φ y₀) ρ := fun x hx => by
    rw [← hΦΨ (hVU hx)]
    exact hΦball (hVB x hx)
  have hVW : V ≤ W := fun x hx => hW (hVρ hx)
  have hD't : (D' : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ (Ω : Set _) ∩ ball (Φ y₀) ρ :=
    fun x hx => ⟨hDΩ hx, hVρ (hDV hx)⟩
  -- The flattened coefficients, folded across the hyperplane to all of `B`.
  set c := G (Φ y₀)
  have hKa' : HolderOnWith M.toNNReal α (fun x => matrixBilinearForm (a x)) t :=
    hKa.mono_const ((Real.le_toNNReal_iff_coe_le (Ka.coe_nonneg.trans hKaM)).2 hKaM)
  have hGD : ∀ x ∈ t, ‖G x - c‖ ≤ ((KG * ρ.toNNReal ^ (α : ℝ) : ℝ≥0) : ℝ) := fun x hx => by
    rw [← dist_eq_norm]
    refine (hGK.dist_le hx (hst hy₀s)).trans ?_
    push_cast
    rw [Real.coe_toNNReal _ hρ.le]
    gcongr
    exact (mem_ball.1 hx.2).le
  have hGc : HolderOnWith KG α (fun x => G x - c) t := fun x hx y hy => by
    simp only [edist_sub_right]
    exact hGK x hx y hy
  obtain ⟨hellF, haKF, hGKF'⟩ := folded_coefficient_bounds hΦ hΨ hΨΦ hΦΨ hν hy₀ν hr hrU' hst hΦl
    hT hell hKa' hGc hGD
  set F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y => if c₀ ≤ ⟪y, ν⟫_ℝ then y else hyperplaneReflection ν c₀ y
  have hGKF : HolderOnWith (KG * cG) α (pullbackDrift Φ (fun x => G x - c) ∘ F) (ball y₀ r) :=
    hGKF'.mono_const (le_of_eq (by simp only [cG, KΦ]; ring))
  have hFH : ∀ y ∈ (H : Set (EuclideanSpace ℝ (Fin (n + 1)))), F y = y := fun y hy => by
    simp only [F, le_of_lt ((hH y).1 hy), ↓reduceIte]
  -- The flattened function `v = u ∘ Φ` on `B` and the hypotheses of the flat estimate.
  set v := hΦB.w1pCompL ENNReal.ofNat_ne_top (W1p.restrictL hVW u)
  have : IsFiniteMeasure (volume.restrict (D' : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2
      ((measure_mono (hD't.trans inter_subset_right)).trans_lt measure_ball_lt_top).ne
  have hfD : MemLp f q (volume.restrict D') := hf.mono_measure (Measure.restrict_mono hD't le_rfl)
  have hf' : MemLp (pullbackDensity Φ f) q
      (volume.restrict ((B : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ H)) :=
    memLp_pullbackDensity hΦD.differentiableOn hΦD.injOn hΦD.mapsTo hΦD.norm_fderiv_le hΦD.pos
      hΦD.le_abs_det hfD
  have hv0 := ae_value_w1pCompL_eq_zero hΦ hΨΦ himage hrU' hVW hΦB hu0 hH
  have hD'cl : (D' : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ t :=
    fun x hx => ⟨subset_closure (hD't hx).1, (hD't hx).2⟩
  obtain ⟨ha, hGcD⟩ := memLp_energyIntegrand_and_memLp_of_holderOnWith (mu := volume)
    (hβ.trans_le hβα) hD'cl hell hKa hGc hGD
  have hDWΩ : D' ≤ W ⊓ Ω := fun x hx => ⟨hVW (hDV hx), hDΩ hx⟩
  have hveq := energyFormH1_restrictL_w1pCompL_eq hVW hDWΩ hΦB hΦD hΨD
    hΨΦB hΦΨD hu ha hGcD (hfD.mono_exponent hq)
  -- On `B ∩ H` the folded coefficients are the flattened ones.
  have hBHm := (B ⊓ H).isOpen.measurableSet
  have hveqF : ∀ φ : 𝓓(B ⊓ H, ℝ), energyFormH1 (pullbackPrincipal Φ a ∘ F) 0 0
      (W1p.restrictL inf_le_left v) (W1p.ofTestFunctionₗ volume (B ⊓ H) 2 φ) =
      (∫ x in B ⊓ H, ⟪(pullbackDrift Φ (fun y => G y - c) ∘ F) x,
          ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
        ∫ x in B ⊓ H, pullbackDensity Φ f x * φ x := fun φ => by
    rw [energyFormH1_congr_ae (a' := pullbackPrincipal Φ a) ?_ .rfl .rfl, hveq φ]
    · congr 1
      exact setIntegral_congr_fun hBHm fun x hx => by simp only [Function.comp_apply, hFH x hx.2]
    · filter_upwards [ae_restrict_mem hBHm] with x hx
      simp only [Function.comp_apply, hFH x hx.2]
  obtain ⟨hPhol, hPsup⟩ := hflat (v := v) hellF haKF le_rfl hGKF hf' hv0 hveqF
  set P := MeasureTheory.preciseRepresentative (volume.restrict (H : Set _)) (W1p.gradient v)
  set Q₁ := ((KG * cG : ℝ≥0) : ℝ) + (eLpNorm (pullbackDensity Φ f) q
    (volume.restrict ((B : Set _) ∩ H))).toReal + ‖W1p.gradient v‖
  -- The data of the flat problem are bounded by those of the curved one.
  have hQ₁ : Q₁ ≤ c₂ * Q :=
    flat_data_le hΦB hΦD hΨD hΨΦB hΦΨD hVW hD't hf
  -- Back to the curved side.
  set T := closure (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball (Φ y₀) ρ'
  have hTU : T ⊆ U := fun x hx => hρ'U hx.2
  have hΨT : MapsTo Ψ T (closedBall y₀ (r / 4) ∩ {y | c₀ ≤ ⟪y, ν⟫_ℝ}) := fun x hx =>
    ⟨ball_subset_closedBall (hΨball hx.2),
      mapsTo_setOf_le_inner_of_image_eq U.isOpen hΨ.differentiableOn.continuousOn
        (hΨΦ.mono inter_subset_right) himage
        ⟨hx.1, hρ'U hx.2⟩⟩
  have hTD : ∀ x ∈ T, ∀ x' ∈ T, edist x x' ≤ D := fun x hx x' hx' => by
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((dist_triangle_right x x' (Φ y₀)).trans ?_)
    linarith [mem_ball.1 hx.2, mem_ball.1 hx'.2]
  have hc₂ : 0 ≤ c₂ := le_trans cG.coe_nonneg (le_max_left _ _)
  obtain ⟨hghol, hgb⟩ := holderOnWith_adjoint_fderiv_apply_comp hΨ hL hTU hTD
    (hΨl.mono inter_subset_right) hΨT hβα hT
    (hPhol.mono (inter_subset_inter_left _ (closedBall_subset_closedBall (by linarith)))) hPsup
    (mul_nonneg hC₁ hc₂) hQ (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hQ₁ hC₁)
  refine ⟨fun x => (fderiv ℝ Ψ x).adjoint (P (Ψ x)), ?_, hghol, hgb⟩
  -- `∇u = DΨ* (P ∘ Ψ)` almost everywhere on `D' ⊇ Ω ∩ B(x₀, ρ')`.
  have hsub : (Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))) ∩ ball (Φ y₀) ρ' ⊆ D' := fun x hx =>
    hsubD x ⟨hx.1, hρ'U hx.2⟩ (ball_subset_ball (by linarith : r / 4 ≤ r) (hΨball hx.2))
  exact ae_restrict_of_ae_restrict_of_subset hsub
    (ae_gradient_eq_adjoint_fderiv_apply hΦ hΨ hΨΦ hΦΨ hVW hD'U hΦB hΨD u
      (MeasureTheory.ae_eq_restrict_inter_preciseRepresentative_restrict B.isOpen
        (((Lp.memLp (W1p.gradient v)).mono_measure
          (Measure.restrict_mono inter_subset_left le_rfl)).locallyIntegrable (by norm_num))))

/-- **Schauder estimate near a `C^{1,α}` boundary for divergence-form equations.** Suppose that in
rigid coordinates `e` centred at `x₀ = e⁻¹ 0`, inside the normal cylinder of half-height `h₀` and
radius `r₀`, the open set `Ω` is the region above the graph of a `C¹` function `γ` with `γ 0 = 0`
and `α`-Hölder derivative. Let `0 < β < 1` with `β ≤ α`, let `2 ≤ q ≤ ∞` and
`β ≤ 1 - (n + 1) / q`, and fix `λ`, `Λ` and `M`. There are radii `ρ, ρ' > 0` and a constant `C`
such that for every open `W ⊇ B(x₀, ρ)` and every `u ∈ H¹(W)` vanishing on `W ∖ Ω` and solving
`-∂ᵢ(aⁱʲ ∂ⱼu) = f - div G` weakly on `W ∩ Ω`, where on `closure Ω ∩ B(x₀, ρ)` the coefficient `a`
is uniformly elliptic with constants `λ, Λ` and `α`-Hölder with constant `K_a ≤ M`, the field `G`
is `α`-Hölder with constant `K_G`, and `f ∈ L^q(Ω ∩ B(x₀, ρ))`, the gradient `∇u` agrees almost
everywhere on `Ω ∩ B(x₀, ρ')` with a function that is `β`-Hölder on `closure Ω ∩ B(x₀, ρ')` with
constant `C Q` and bounded there by `C Q`, where
`Q = K_G + ‖f‖_{L^q(Ω ∩ B(x₀, ρ))} + ‖u‖_{H¹(W)}`. -/
theorem exists_holderOnWith_gradient_of_graph {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α β : ℝ≥0} (hβ : 0 < β) (hβ1 : β < 1) (hβα : β ≤ α) {q : ℝ≥0∞}
    (hq : 2 ≤ q) (hβq : (β : ℝ) ≤ 1 - ((n : ℝ) + 1) / q.toReal)
    {e : EuclideanSpace ℝ (Fin (n + 1)) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {h₀ r₀ : ℝ}
    (hh₀ : 0 < h₀) (hr₀ : 0 < r₀) (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ 1 γ) {Kγ : ℝ≥0}
    (hγK : HolderWith Kγ α (fderiv ℝ γ))
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Ω ↔ γ z.snd < z.fst)) (lam Lam M : ℝ) :
    ∃ ρ ρ' C : ℝ, 0 < ρ ∧ 0 < ρ' ∧ 0 ≤ C ∧
      ∀ {W : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume W 2}
        {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
        {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
        {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {Ka KG : ℝ≥0},
        ball (e.symm 0) ρ ⊆ W →
        UniformlyEllipticOn (closure (Ω : Set _) ∩ ball (e.symm 0) ρ) a lam Lam →
        HolderOnWith Ka α (fun x => matrixBilinearForm (a x))
          (closure (Ω : Set _) ∩ ball (e.symm 0) ρ) → (Ka : ℝ) ≤ M →
        HolderOnWith KG α G (closure (Ω : Set _) ∩ ball (e.symm 0) ρ) →
        MemLp f q (volume.restrict ((Ω : Set _) ∩ ball (e.symm 0) ρ)) →
        (∀ᵐ x ∂volume.restrict W, x ∉ Ω → W1p.value u x = 0) →
        (∀ φ : 𝓓(W ⊓ Ω, ℝ), energyFormH1 a 0 0 (W1p.restrictL inf_le_left u)
            (W1p.ofTestFunctionₗ volume (W ⊓ Ω) 2 φ) =
          (∫ x in W ⊓ Ω, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) +
            ∫ x in W ⊓ Ω, f x * φ x) →
        ∃ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
          (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
            =ᵐ[volume.restrict ((Ω : Set _) ∩ ball (e.symm 0) ρ')] g ∧
          HolderOnWith (C * (KG + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩
            ball (e.symm 0) ρ))).toReal + ‖u‖)).toNNReal β g
            (closure (Ω : Set _) ∩ ball (e.symm 0) ρ') ∧
          ∀ x ∈ closure (Ω : Set _) ∩ ball (e.symm 0) ρ', ‖g x‖ ≤
            C * (KG + (eLpNorm f q (volume.restrict ((Ω : Set _) ∩ ball (e.symm 0) ρ))).toReal +
              ‖u‖) := by
  set G₀ := graphFlattening γ hγ.continuous
  obtain ⟨U', U, L, ν, c₀, hΦ, hΨ, hν, himage, hx₀U', hx₀H, hΦx₀⟩ :=
    exists_isChangeOfVariables_halfSpace_of_contDiff_graph (k := 1) le_rfl hh₀ hr₀ hγ0
      (by exact_mod_cast hγ) hgraph
  set Φ := e.symm ∘ G₀.symm ∘ e
  set Ψ := e.symm ∘ G₀ ∘ e
  have hΨΦ : LeftInvOn Ψ Φ U' := fun y _ => by simp [Φ, Ψ]
  have hΦΨ : RightInvOn Ψ Φ U := fun x _ => by simp [Φ, Ψ]
  -- The boundary point lies on the hyperplane: it is in the closure of the flat side, but not
  -- in the flat side, since `Φ` fixes it and it is not in `Ω`.
  have hx₀Ω : e.symm 0 ∉ (Ω : Set _) := fun h => by
    have := (hgraph 0 (mem_normalCylinder.2 ⟨by simpa using hh₀, by simpa using hh₀,
      by simpa using hr₀⟩)).1 h
    simp [hγ0] at this
  have hx₀ν : ⟪e.symm 0, ν⟫_ℝ = c₀ := by
    refine le_antisymm (not_lt.1 fun h => hx₀Ω ?_) (closure_setOf_lt_inner_subset ν c₀ hx₀H)
    have hmem : Φ (e.symm 0) ∈ (Ω : Set _) ∩ U := by
      rw [← himage]
      exact mem_image_of_mem Φ ⟨h, hx₀U'⟩
    rw [hΦx₀] at hmem
    exact hmem.1
  -- `DΨ` is `α`-Hölder: it is the derivative of graph flattening, conjugated by isometries.
  have hT : HolderOnWith Kγ α (fderiv ℝ Ψ) U :=
    (AffineIsometry.holderWith_fderiv_comp_comp e.toAffineIsometry e.symm.toAffineIsometry
      ((contDiff_graphFlattening hγ).differentiable one_ne_zero)
      (holderWith_fderiv_graphFlattening (hγ.differentiable one_ne_zero) hγK)).holderOnWith _
  have h := exists_holderOnWith_gradient_of_isChangeOfVariables hβ hβ1 hβα hq hβq hΦ hΨ hΨΦ hΦΨ
    hν himage hT hx₀U' hx₀ν lam Lam M
  rwa [hΦx₀] at h

end Main

end PDE

end TauCeti
