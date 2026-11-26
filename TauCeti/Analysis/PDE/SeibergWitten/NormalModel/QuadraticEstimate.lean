/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Expansion
public import TauCeti.Analysis.PDE.SeibergWitten.RescaledNorm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The quadratic estimate for the flat Seiberg–Witten equations in the rescaled norms

The flat limiting Seiberg–Witten equations have no terms beyond the quadratic ones
(`TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Expansion`): at a pair `(b, ψ)`, the nonlinear
part `N(b', ζ)` of each row, the row at `(b + b', ψ + ζ)` minus its linearization, is

* `i c(b') ζ` for the Dirac row, the Clifford multiplication of the spinor variation by the
  connection variation (`TauCeti.SeibergWitten.flatDirac_add_eq_add_flatDeformationDirac_add`);
* `q(ζ) / 2` for the curvature row (`TauCeti.SeibergWitten.flatCurvature_add`).

Both are pointwise bilinear expressions in the variation, and pointwise they obey the quadratic
Lipschitz bounds of that file. This file integrates those bounds into the rescaled Hilbert norms
of Taubes's gluing construction (`TauCeti.Analysis.PDE.SeibergWitten.RescaledNorm`): with
`E = E_(r,s)` the field norm `‖(b, ζ)‖_E² = ∑_{j ≤ s} h^(2j) (h² ‖Dʲ b‖₂² + ‖Dʲ ζ‖₂² / 4)` and
`F` the target norm `‖y‖_F² = ∑_{j ≤ s} h^(2j) ‖Dʲ y‖₂²` through order `s`, at the scale
`h = (2r)^(-1/2)` on the oriented Euclidean four-space `V`, and for `s ≥ 3`, there is a constant
`K` independent of `h` with

`‖N(x₁) - N(x₂)‖_F ≤ K h⁻² (‖x₁‖_E + ‖x₂‖_E) ‖x₁ - x₂‖_E`

for all variations `x₁ = (b₁, ζ₁)` and `x₂ = (b₂, ζ₂)` of class `Cˢ` with square-integrable
derivatives through order `s`. This is the quadratic Lipschitz bound on the nonlinear part that
the contraction mapping argument of the gluing construction needs, with the constant
`L_quad = 2 K h⁻² = 4 K r` explicit in `h`. The target norm through order `s` bounds the norm
`F_(r,s-1)` of the gauge-fixed section, which stops at order `s - 1`.

* **Dirac row.** The connection variation carries the weight `h` in `E`, and the Dirac row is
  weighted to match: in the rescaled coordinate `w = λ y`, `λ = h⁻¹`, the flat Dirac operator of
  the rescaled fields `b_w(w) = h b(h w)`, `ζ_w(w) = ζ(h w)` is `h` times the flat Dirac operator
  of `(b, ζ)` at `y = h w`. The estimate is for `h (N(b₁, ζ₁) - N(b₂, ζ₂))`
  (`TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_smul_flatDirac_const_sub_le`, and for
  the nonlinear parts written through the flat Dirac operator and its linearization,
  `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_smul_flatDirac_sub_le`).
* **Curvature row.** The nonlinear part `q(ζ) / 2` does not involve the connection, and its
  differences are `q'(ζ₁ - ζ₂, ζ₁ + ζ₂) / 4` with the real polarization `q'` of `q`
  (`TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le`, and
  `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_flatCurvature_sub_le` for the nonlinear
  parts written through the curvature side and its linearization).

The proofs combine the pointwise identities of the expansion with the algebra estimate for the
target norm (`TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_bilinear_le`), applied to
continuous bilinear maps: the Clifford multiplication `(β, φ) ↦ i c(β) φ` and the polarization of
`q`. The factor `h⁻² = h^(-n/2)`, `n = 4`, is the loss of the algebra estimate in norms without
volume normalization; the condition `s ≥ 3` is `2 s > 4`, the Sobolev threshold for that
estimate. The constants depend on `s` and on the Clifford module; no hypothesis on the quadratic
form or on the adjoints of the Clifford generators is needed, only finite dimension.

## Main results

* `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_smul_flatDirac_const_sub_le`: the
  quadratic estimate for the Clifford multiplication `i c(b) ζ`.
* `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_smul_flatDirac_sub_le`: the quadratic
  estimate for the nonlinear part of the flat Dirac operator.
* `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le`: the quadratic
  estimate for the quadratic two-form `q`.
* `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_flatCurvature_sub_le`: the quadratic
  estimate for the nonlinear part of the flat curvature equation.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

open MeasureTheory Module CliffordAlgebra Complex

namespace TauCeti.SeibergWitten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable [Fact (finrank ℝ V = 4)]

/-- The covectors of `V` form a finite-dimensional space. -/
private theorem finiteDimensional_covector : FiniteDimensional ℝ (V [⋀^Fin 1]→L[ℝ] ℝ) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).toLinearEquiv.finiteDimensional

attribute [local instance] finiteDimensional_covector

/-- `h^(-n/2) = h⁻²` on the four-space. -/
private theorem rpow_neg_finrank_div_two {h : ℝ} (hh : 0 < h) :
    h ^ (-(finrank ℝ V : ℝ) / 2) = (h ^ 2)⁻¹ := by
  rw [Fact.out (p := finrank ℝ V = 4), neg_div, Real.rpow_neg hh.le]
  norm_num

variable (ρ) in
/-- The Clifford multiplication `(β, φ) ↦ i c(β) φ` of a positive spinor by a covector, the flat
Dirac operator of constant fields, is a continuous real-bilinear map. -/
private theorem exists_clm_flatDirac_const :
    ∃ L : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] positiveHalfSpinors o ρ →L[ℝ] W,
      ∀ (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (φ : positiveHalfSpinors o ρ) (x : V),
        flatDirac ρ b (fun _ ↦ (φ : W)) x = L (b x) φ := by
  let L₀ : (V [⋀^Fin 1]→L[ℝ] ℝ) →ₗ[ℝ] positiveHalfSpinors o ρ →ₗ[ℝ] W :=
    LinearMap.mk₂ ℝ (fun β φ ↦ flatDirac ρ (fun _ ↦ β) (fun _ ↦ (φ : W)) 0)
      (fun β₁ β₂ _ ↦ flatDirac_add_connection ρ (fun _ ↦ β₁) (fun _ ↦ β₂) _ 0)
      (fun c _ _ ↦ flatDirac_smul_connection_const ρ c _)
      (fun _ _ _ ↦ flatDirac_add ρ (differentiableAt_const _) (differentiableAt_const _))
      (fun c β φ ↦ by
        have hc : (fun _ : V ↦ ((c • φ : positiveHalfSpinors o ρ) : W)) =
            (c : ℂ) • fun _ ↦ (φ : W) :=
          funext fun _ ↦ by simp [Complex.coe_smul]
        rw [hc, flatDirac_smul, Complex.coe_smul])
  refine ⟨LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (positiveHalfSpinors o ρ →ₗ[ℝ] W) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      L₀), fun b φ x ↦ ?_⟩
  simp only [L₀, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe, LinearMap.mk₂_apply]
  rw [flatDirac_const_eq_smul_ι, flatDirac_const_eq_smul_ι]

variable [MeasurableSpace V] [BorelSpace V]

/-- The iterated derivatives of `f ± g` are square integrable through order `s` when those of
`f` and `g` are. -/
private theorem memLp_iteratedFDeriv_add_sub {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {s : ℕ} {f g : V → T} (hf : ContDiff ℝ s f) (hg : ContDiff ℝ s g)
    (hfm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i f) 2)
    (hgm : ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i g) 2) :
    (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i (f + g)) 2) ∧
      ∀ i ≤ s, MemLp (iteratedFDeriv ℝ i (f - g)) 2 :=
  ⟨fun i hi ↦ by
    rw [iteratedFDeriv_add (hf.of_le (by exact_mod_cast hi)) (hg.of_le (by exact_mod_cast hi))]
    exact (hfm i hi).add (hgm i hi),
  fun i hi ↦ by
    rw [iteratedFDeriv_sub (hf.of_le (by exact_mod_cast hi)) (hg.of_le (by exact_mod_cast hi))]
    exact (hfm i hi).sub (hgm i hi)⟩

/-- The algebra estimate of the target norm on the four-space for one continuous bilinear map
`L`: `‖L (f, g)‖_F ≤ C h⁻² ‖f‖_F ‖g‖_F` for `s ≥ 3`, with `C` independent of `h`. -/
private theorem exists_sqrt_rescaledTargetNormSq_apply_apply_le {B S T : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
    [NormedAddCommGroup T] [NormedSpace ℝ T] {s : ℕ} (hs : 2 < s) (L : B →L[ℝ] S →L[ℝ] T) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ (f : V → B) (g : V → S),
      ContDiff ℝ s f → ContDiff ℝ s g → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i f) 2) →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i g) 2) →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i fun x ↦ L (f x) (g x)) 2) ∧
        √(rescaledTargetNormSq (s + 1) h fun x ↦ L (f x) (g x)) ≤
          C * (h ^ 2)⁻¹ * √(rescaledTargetNormSq (s + 1) h f) *
            √(rescaledTargetNormSq (s + 1) h g) := by
  obtain ⟨C, hC, hB⟩ := exists_sqrt_rescaledTargetNormSq_bilinear_le (V := V) (B := B) (S := S)
    (T := T) (k := s) (by rw [Fact.out (p := finrank ℝ V = 4)]; omega)
  refine ⟨C * ‖L‖, by positivity, fun h hh f g hf hg hfm hgm ↦ ?_⟩
  obtain ⟨hm, hle⟩ := hB h hh L f g hf hg hfm hgm
  rw [rpow_neg_finrank_div_two hh] at hle
  exact ⟨hm, hle⟩

/-! ### The Dirac row -/

section Dirac

/-- **The quadratic estimate for the Clifford multiplication in the rescaled norms.** For
`s ≥ 3` there is a constant `K ≥ 0` such that for every scale `h > 0` and all connection forms
`b₁`, `b₂` and positive spinor fields `ζ₁`, `ζ₂` of class `Cˢ` with square-integrable
derivatives through order `s`, the Clifford multiplications `i c(bₖ) ζₖ`, weighted by `h`,
satisfy

`‖h (i c(b₁) ζ₁ - i c(b₂) ζ₂)‖_F ≤ K h⁻² (‖(b₁, ζ₁)‖_E + ‖(b₂, ζ₂)‖_E) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_E`,

where `‖·‖_F` is the target norm through order `s` and `‖·‖_E` the rescaled norm `E_(r,s)`.
The Clifford multiplication `i c(b) ζ` is the flat Dirac operator of the constant field `ζ y`
for the connection `b`, the nonlinear part of the flat Dirac operator
(`TauCeti.SeibergWitten.flatDirac_add_eq_add_flatDeformationDirac_add`). -/
theorem exists_sqrt_rescaledTargetNormSq_smul_flatDirac_const_sub_le {s : ℕ} (hs : 2 < s) :
    ∃ K, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → ∀ (b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
      (ζ₁ ζ₂ : V → positiveHalfSpinors o ρ),
      ContDiff ℝ s b₁ → ContDiff ℝ s b₂ → ContDiff ℝ s ζ₁ → ContDiff ℝ s ζ₂ →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i b₁) 2) → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i b₂) 2) →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (s + 1) h fun y ↦
          h • (flatDirac ρ b₁ (fun _ ↦ (ζ₁ y : W)) y - flatDirac ρ b₂ (fun _ ↦ (ζ₂ y : W)) y)) ≤
        K * (h ^ 2)⁻¹ * (√(rescaledFieldNormSq s h b₁ ζ₁) + √(rescaledFieldNormSq s h b₂ ζ₂)) *
          √(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  obtain ⟨L, hL⟩ := exists_clm_flatDirac_const (V := V) (o := o) ρ
  obtain ⟨C, hC, hB⟩ := exists_sqrt_rescaledTargetNormSq_apply_apply_le (V := V) hs L
  refine ⟨2 * C, by positivity, fun h hh b₁ b₂ ζ₁ ζ₂ hb₁ hb₂ hζ₁ hζ₂ hb₁m hb₂m hζ₁m hζ₂m ↦ ?_⟩
  -- `i c(b₁) ζ₁ - i c(b₂) ζ₂ = L (b₁ - b₂, ζ₁) + L (b₂, ζ₁ - ζ₂)`.
  have hdec : (fun y ↦
      h • (flatDirac ρ b₁ (fun _ ↦ (ζ₁ y : W)) y - flatDirac ρ b₂ (fun _ ↦ (ζ₂ y : W)) y)) =
      h • ((fun y ↦ L ((b₁ - b₂) y) (ζ₁ y)) + fun y ↦ L (b₂ y) ((ζ₁ - ζ₂) y)) := by
    funext y
    simp only [hL, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, map_sub, sub_apply]
    congr 1
    abel
  obtain ⟨-, hdbm⟩ := memLp_iteratedFDeriv_add_sub hb₁ hb₂ hb₁m hb₂m
  obtain ⟨-, hdζm⟩ := memLp_iteratedFDeriv_add_sub hζ₁ hζ₂ hζ₁m hζ₂m
  obtain ⟨h₁m, h₁⟩ := hB h hh (b₁ - b₂) ζ₁ (hb₁.sub hb₂) hζ₁ hdbm hζ₁m
  obtain ⟨-, h₂⟩ := hB h hh b₂ (ζ₁ - ζ₂) hb₂ (hζ₁.sub hζ₂) hb₂m hdζm
  have hadd := sqrt_rescaledTargetNormSq_add_le (s := s + 1)
    (y := fun y ↦ L ((b₁ - b₂) y) (ζ₁ y)) (y' := fun y ↦ L (b₂ y) ((ζ₁ - ζ₂) y))
    (by simpa using (L.contDiff.comp (hb₁.sub hb₂)).clm_apply hζ₁)
    (by simpa using (L.contDiff.comp hb₂).clm_apply (hζ₁.sub hζ₂))
    (fun j hj ↦ h₁m j (Nat.lt_succ_iff.1 hj)) hh.le
  rw [hdec, rescaledTargetNormSq_smul, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  -- Each term is bounded through `h ‖b‖_F ≤ ‖(b, ζ)‖_E` and `‖ζ‖_F ≤ 2 ‖(b, ζ)‖_E`.
  have hE₁ := sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq s h b₁ ζ₁
  have hEd := sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq s h (b₁ - b₂)
    (ζ₁ - ζ₂)
  have hFd := mul_sqrt_rescaledTargetNormSq_le_sqrt_rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)
  have hF₂ := mul_sqrt_rescaledTargetNormSq_le_sqrt_rescaledFieldNormSq s h b₂ ζ₂
  have hc : 0 ≤ C * (h ^ 2)⁻¹ := by positivity
  calc h * √(rescaledTargetNormSq (s + 1) h
          ((fun y ↦ L ((b₁ - b₂) y) (ζ₁ y)) + fun y ↦ L (b₂ y) ((ζ₁ - ζ₂) y)))
      ≤ h * (C * (h ^ 2)⁻¹ * √(rescaledTargetNormSq (s + 1) h (b₁ - b₂)) *
            √(rescaledTargetNormSq (s + 1) h ζ₁) +
          C * (h ^ 2)⁻¹ * √(rescaledTargetNormSq (s + 1) h b₂) *
            √(rescaledTargetNormSq (s + 1) h (ζ₁ - ζ₂))) :=
        mul_le_mul_of_nonneg_left (hadd.trans (add_le_add h₁ h₂)) hh.le
    _ = C * (h ^ 2)⁻¹ * ((h * √(rescaledTargetNormSq (s + 1) h (b₁ - b₂))) *
            √(rescaledTargetNormSq (s + 1) h ζ₁) +
          (h * √(rescaledTargetNormSq (s + 1) h b₂)) *
            √(rescaledTargetNormSq (s + 1) h (ζ₁ - ζ₂))) := by ring
    _ ≤ C * (h ^ 2)⁻¹ * (√(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)) *
            (2 * √(rescaledFieldNormSq s h b₁ ζ₁)) +
          √(rescaledFieldNormSq s h b₂ ζ₂) *
            (2 * √(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)))) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul hFd hE₁ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (mul_le_mul hF₂ hEd (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) hc
    _ = _ := by ring

variable (e : OrthonormalBasis (Fin 4) ℝ V)

/-- **The quadratic estimate for the nonlinear part of the flat Dirac operator.** For `s ≥ 3`
there is a constant `K ≥ 0` such that for every scale `h > 0`, every pair `(b, ψ)` with `ψ`
differentiable, and all variations `(b₁, ζ₁)` and `(b₂, ζ₂)` of class `Cˢ` with
square-integrable derivatives through order `s`, the nonlinear parts
`N(bₖ, ζₖ) = D_{b + bₖ} (ψ + ζₖ) - D'_{(b, ψ)}(bₖ, ζₖ)` of the flat Dirac operator, weighted by
`h`, satisfy

`‖h (N(b₁, ζ₁) - N(b₂, ζ₂))‖_F ≤ K h⁻² (‖(b₁, ζ₁)‖_E + ‖(b₂, ζ₂)‖_E) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_E`.

The constant does not depend on `h` or on `(b, ψ)`. -/
theorem exists_sqrt_rescaledTargetNormSq_smul_flatDirac_sub_le {s : ℕ} (hs : 2 < s) :
    ∃ K, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → ∀ (b b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
      (ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ), Differentiable ℝ (fun y ↦ (ψ y : W)) →
      ContDiff ℝ s b₁ → ContDiff ℝ s b₂ → ContDiff ℝ s ζ₁ → ContDiff ℝ s ζ₂ →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i b₁) 2) → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i b₂) 2) →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (s + 1) h fun y ↦
          h • ((flatDirac ρ (b + b₁) (fun z ↦ ((ψ + ζ₁) z : W)) y -
              flatDeformationDirac e b b₁ ψ ζ₁ y) -
            (flatDirac ρ (b + b₂) (fun z ↦ ((ψ + ζ₂) z : W)) y -
              flatDeformationDirac e b b₂ ψ ζ₂ y))) ≤
        K * (h ^ 2)⁻¹ * (√(rescaledFieldNormSq s h b₁ ζ₁) + √(rescaledFieldNormSq s h b₂ ζ₂)) *
          √(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  obtain ⟨K, hK, hDirac⟩ :=
    exists_sqrt_rescaledTargetNormSq_smul_flatDirac_const_sub_le (V := V) (o := o) (ρ := ρ) hs
  refine ⟨K, hK, fun h hh b b₁ b₂ ψ ζ₁ ζ₂ hψ hb₁ hb₂ hζ₁ hζ₂ hb₁m hb₂m hζ₁m hζ₂m ↦ ?_⟩
  -- The underlying spinor fields in `W` are differentiable.
  have hcoe {ζ : V → positiveHalfSpinors o ρ} (hζ : ContDiff ℝ s ζ) :
      Differentiable ℝ (fun y ↦ (ζ y : W)) :=
    (((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ).contDiff.comp hζ).differentiable
      (by norm_cast; omega)
  -- The nonlinear parts differ by the difference of the Clifford multiplications.
  have hN : (fun y ↦ h • ((flatDirac ρ (b + b₁) (fun z ↦ ((ψ + ζ₁) z : W)) y -
        flatDeformationDirac e b b₁ ψ ζ₁ y) -
      (flatDirac ρ (b + b₂) (fun z ↦ ((ψ + ζ₂) z : W)) y -
        flatDeformationDirac e b b₂ ψ ζ₂ y))) =
      fun y ↦ h • (flatDirac ρ b₁ (fun _ ↦ (ζ₁ y : W)) y -
        flatDirac ρ b₂ (fun _ ↦ (ζ₂ y : W)) y) := by
    funext y
    rw [flatDirac_add_eq_add_flatDeformationDirac_add e (hψ y) (hcoe hζ₁ y),
      flatDirac_add_eq_add_flatDeformationDirac_add e (hψ y) (hcoe hζ₂ y)]
    congr 1
    abel
  rw [hN]
  exact hDirac h hh b₁ b₂ ζ₁ ζ₂ hb₁ hb₂ hζ₁ hζ₂ hb₁m hb₂m hζ₁m hζ₂m

end Dirac

/-! ### The curvature row -/

section Curvature

variable (hkl : 2 + 2 = finrank ℝ V)

/-- **The quadratic estimate for `q` in the rescaled norms.** For `s ≥ 3` there is a constant
`K ≥ 0` such that for every scale `h > 0`, all connection forms `b₁`, `b₂`, and all positive spinor
fields `ζ₁`, `ζ₂` of class `Cˢ` with square-integrable derivatives through order `s`,

`‖(q(ζ₁) - q(ζ₂)) / 2‖_F ≤ K h⁻² (‖(b₁, ζ₁)‖_E + ‖(b₂, ζ₂)‖_E) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_E`,

where `q` is the quadratic two-form (`TauCeti.SeibergWitten.quadraticTwoForm`), read as a
two-vector. The connection forms enter only through the norms, which they increase. -/
theorem exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le {s : ℕ} (hs : 2 < s) :
    ∃ K, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → ∀ (b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
      (ζ₁ ζ₂ : V → positiveHalfSpinors o ρ), ContDiff ℝ s ζ₁ → ContDiff ℝ s ζ₂ →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (s + 1) h fun y ↦
          (2⁻¹ : ℝ) • ((quadraticTwoForm o ρ hkl (ζ₁ y) : ⋀[ℝ]^2 V) -
            quadraticTwoForm o ρ hkl (ζ₂ y))) ≤
        K * (h ^ 2)⁻¹ * (√(rescaledFieldNormSq s h b₁ ζ₁) + √(rescaledFieldNormSq s h b₂ ζ₂)) *
          √(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  -- The bilinear map `(φ, φ') ↦ q'(φ, φ') / 4`, with values read as two-vectors.
  obtain ⟨L, hL⟩ : ∃ L : positiveHalfSpinors o ρ →L[ℝ] positiveHalfSpinors o ρ →L[ℝ] ⋀[ℝ]^2 V,
      ∀ φ φ', L φ φ' = (4⁻¹ : ℝ) • (quadraticTwoFormPolar o ρ hkl φ φ' : ⋀[ℝ]^2 V) :=
    ⟨(4⁻¹ : ℝ) • (ContinuousLinearMap.compL ℝ _ _ _ (Submodule.subtypeL _)).comp
      (quadraticTwoFormPolar o ρ hkl), fun _ _ ↦ rfl⟩
  obtain ⟨C, hC, hB⟩ := exists_sqrt_rescaledTargetNormSq_apply_apply_le (V := V) hs L
  refine ⟨4 * C, by positivity, fun h hh b₁ b₂ ζ₁ ζ₂ hζ₁ hζ₂ hζ₁m hζ₂m ↦ ?_⟩
  -- `(q(ζ₁) - q(ζ₂)) / 2 = q'(ζ₁ - ζ₂, ζ₁ + ζ₂) / 4`.
  have hdec : (fun y ↦ (2⁻¹ : ℝ) • ((quadraticTwoForm o ρ hkl (ζ₁ y) : ⋀[ℝ]^2 V) -
      quadraticTwoForm o ρ hkl (ζ₂ y))) = fun y ↦ L ((ζ₁ - ζ₂) y) ((ζ₁ + ζ₂) y) := by
    funext y
    rw [hL, Pi.sub_apply, Pi.add_apply, quadraticTwoFormPolar_sub_add, Submodule.coe_smul,
      Submodule.coe_sub, smul_smul]
    norm_num
  obtain ⟨hσm, hdm⟩ := memLp_iteratedFDeriv_add_sub hζ₁ hζ₂ hζ₁m hζ₂m
  obtain ⟨-, hq⟩ := hB h hh (ζ₁ - ζ₂) (ζ₁ + ζ₂) (hζ₁.sub hζ₂) (hζ₁.add hζ₂) hdm hσm
  rw [hdec]
  -- `‖ζ₁ - ζ₂‖_F ≤ 2 ‖x₁ - x₂‖_E` and `‖ζ₁ + ζ₂‖_F ≤ ‖ζ₁‖_F + ‖ζ₂‖_F ≤ 2 (‖x₁‖_E + ‖x₂‖_E)`.
  have hEd := sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq s h (b₁ - b₂)
    (ζ₁ - ζ₂)
  have hE₁ := sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq s h b₁ ζ₁
  have hE₂ := sqrt_rescaledTargetNormSq_le_two_mul_sqrt_rescaledFieldNormSq s h b₂ ζ₂
  have hσ := sqrt_rescaledTargetNormSq_add_le (s := s + 1) (by simpa using hζ₁)
    (by simpa using hζ₂) (fun j hj ↦ hζ₁m j (Nat.lt_succ_iff.1 hj)) hh.le
  have hc : 0 ≤ C * (h ^ 2)⁻¹ := by positivity
  calc _ ≤ C * (h ^ 2)⁻¹ * √(rescaledTargetNormSq (s + 1) h (ζ₁ - ζ₂)) *
        √(rescaledTargetNormSq (s + 1) h (ζ₁ + ζ₂)) := hq
    _ ≤ C * (h ^ 2)⁻¹ * (2 * √(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂))) *
        (2 * √(rescaledFieldNormSq s h b₁ ζ₁) + 2 * √(rescaledFieldNormSq s h b₂ ζ₂)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hEd hc) (hσ.trans (add_le_add hE₁ hE₂))
        (Real.sqrt_nonneg _) (mul_nonneg hc (by positivity))
    _ = _ := by ring

/-- **The quadratic estimate for the nonlinear part of the flat curvature equation.** For `s ≥ 3`
there is a constant `K ≥ 0` such that for every scale `h > 0`, every pair `(b, ψ)` with `b`
differentiable, and all variations `(b₁, ζ₁)` and `(b₂, ζ₂)` with `b₁`, `b₂` differentiable and
`ζ₁`, `ζ₂` of class `Cˢ` with square-integrable derivatives through order `s`, the nonlinear
parts `N(bₖ, ζₖ) = flatCurvature (b + bₖ) (ψ + ζₖ) - F'_ψ(bₖ, ζₖ)` of the flat curvature equation
satisfy

`‖N(b₁, ζ₁) - N(b₂, ζ₂)‖_F ≤ K h⁻² (‖(b₁, ζ₁)‖_E + ‖(b₂, ζ₂)‖_E) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_E`.

The constant does not depend on `h` or on `(b, ψ)`. -/
theorem exists_sqrt_rescaledTargetNormSq_flatCurvature_sub_le {s : ℕ} (hs : 2 < s) :
    ∃ K, 0 ≤ K ∧ ∀ h : ℝ, 0 < h → ∀ (b b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
      (ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ), Differentiable ℝ b → Differentiable ℝ b₁ →
      Differentiable ℝ b₂ → ContDiff ℝ s ζ₁ → ContDiff ℝ s ζ₂ →
      (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ s, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (s + 1) h fun y ↦
          (flatCurvature o ρ hkl (b + b₁) (ψ + ζ₁) y -
              flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ y) -
            (flatCurvature o ρ hkl (b + b₂) (ψ + ζ₂) y -
              flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ y)) ≤
        K * (h ^ 2)⁻¹ * (√(rescaledFieldNormSq s h b₁ ζ₁) + √(rescaledFieldNormSq s h b₂ ζ₂)) *
          √(rescaledFieldNormSq s h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  obtain ⟨K, hK, hq⟩ :=
    exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le (o := o) (ρ := ρ) hkl hs
  refine ⟨K, hK, fun h hh b b₁ b₂ ψ ζ₁ ζ₂ hb hb₁ hb₂ hζ₁ hζ₂ hζ₁m hζ₂m ↦ ?_⟩
  -- The nonlinear parts differ by `(q(ζ₁) - q(ζ₂)) / 2`.
  have hN : (fun y ↦ (flatCurvature o ρ hkl (b + b₁) (ψ + ζ₁) y -
        flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ y) -
      (flatCurvature o ρ hkl (b + b₂) (ψ + ζ₂) y - flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ y)) =
      fun y ↦ (2⁻¹ : ℝ) • ((quadraticTwoForm o ρ hkl (ζ₁ y) : ⋀[ℝ]^2 V) -
        quadraticTwoForm o ρ hkl (ζ₂ y)) := by
    funext y
    rw [flatCurvature_add hkl (hb y) (hb₁ y), flatCurvature_add hkl (hb y) (hb₂ y), smul_sub]
    abel
  rw [hN]
  exact hq h hh b₁ b₂ ζ₁ ζ₂ hζ₁ hζ₂ hζ₁m hζ₂m

end Curvature

end TauCeti.SeibergWitten
