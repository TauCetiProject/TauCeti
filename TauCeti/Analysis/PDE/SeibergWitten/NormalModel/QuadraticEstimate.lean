/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Expansion
public import TauCeti.Analysis.PDE.SeibergWitten.RescaledNorm
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp

/-!
# The quadratic estimate of the flat Seiberg–Witten nonlinearity in the rescaled norms

The flat limiting Seiberg–Witten equations on an oriented Euclidean four-space `V` are exactly
quadratic (`TauCeti.Analysis.PDE.SeibergWitten.NormalModel.Expansion`): at a pair `(b, ψ)` the
Dirac row and the curvature row at `(b + b', ψ + ζ)` are the rows at `(b, ψ)`, plus the
deformation rows of the normal model applied to `(b', ζ)`, plus the nonlinear remainders

* `i c(b') ζ`, the flat Dirac operator of the constant field `ζ x` for the connection `b'`
  (`TauCeti.SeibergWitten.flatDirac_add_eq_add_flatDeformationDirac_add`), and
* `q(ζ) / 2`, with `q` the quadratic two-form (`TauCeti.SeibergWitten.flatCurvature_add`).

Taubes's gluing construction solves the equations at parameter `r` by a contraction in the
rescaled Hilbert norms `E_(r,s)` of the increments and `F_(r,s-1)` of the values
(`TauCeti.SeibergWitten.rescaledFieldNormSq`, `TauCeti.SeibergWitten.rescaledTargetNormSq`), at
the length scale `h = (2r)^(-1/2)`. The contraction needs a quadratic estimate on the nonlinear
part `N`, of the form `‖N(x₁) - N(x₂)‖ ≤ (L / 2) (‖x₁‖ + ‖x₂‖) ‖x₁ - x₂‖`, with an explicit
dependence of `L` on `r`. This file proves it for the two remainders in a flat chart.

The flat equations are written in the unit-scale coordinate `w = y / h`, in which a connection
increment `b` and a spinor increment `ζ` of the physical coordinate `y` have the plane
coefficients `b_w(w) = h b(h w)` and `ζ_w(w) = ζ(h w)`, as in the scaling check
`TauCeti.SeibergWitten.rescaledFieldNormSq_eq_rpow_mul`. So, read at `y`, the remainders are
`i c(h b) ζ` and `q(ζ) / 2`. For an integer `k ≥ 3`, so that `2k` exceeds the dimension four,
there is a constant `C`, independent of `h`, with

`‖N(x₁) - N(x₂)‖_(F_(r,k)) ≤ (C / h²) (‖x₁‖_(E_(r,k)) + ‖x₂‖_(E_(r,k))) ‖x₁ - x₂‖_(E_(r,k))`

for each of the two remainders and all increments `xᵢ = (bᵢ, ζᵢ)` of class `Cᵏ` with
square-integrable derivatives through order `k`
(`TauCeti.SeibergWitten.`
`exists_sqrt_rescaledTargetNormSq_flatDirac_const_sub_flatDirac_const_le`,
`TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le`). In Taubes's
notation the quadratic constant is `L = 2C / h² = 4 C r`.

The factor `h⁻²` is the volume factor `h^(-n/2)` for `n = 4`: the norms `E_(r,k)` and `F_(r,k)`
carry no volume normalization, so an increment of size one concentrated in a ball of radius `h`
has norm of order `h²`, and so does its square, while the product of two such norms is of order
`h⁴`. The proof passes to the
semiclassical Sobolev norms, `hⁿ (h² ‖b‖_{k,h}² + ‖ζ‖_{k,h}² / 4) ≤ (k + 1) ‖(b, ζ)‖_(E_(r,k))²`
(`TauCeti.SeibergWitten.rpow_mul_le_mul_rescaledFieldNormSq`) and
`‖y‖_(F_(r,k))² ≤ hⁿ ‖y‖_{k,h}²` (`TauCeti.SeibergWitten.rescaledTargetNormSq_succ_le_rpow_mul`),
in which bilinear maps are bounded uniformly in `h`
(`TauCeti.exists_semiclassicalSobolevNorm_bilinear_le`). The remainders are bilinear:
`i c(h b₁) ζ₁ - i c(h b₂) ζ₂ = i c(h (b₁ - b₂)) ζ₁ + i c(h b₂) (ζ₁ - ζ₂)`, and
`q(ζ₁) - q(ζ₂) = q'(ζ₁ - ζ₂, ζ₁ + ζ₂) / 2` for the polarization `q'` of `q`
(`TauCeti.SeibergWitten.quadraticTwoFormPolar_sub_add`).

The statements are for fields on the flat chart; the curvature of the tube, the background
connection and the cutoffs, which enter the section on a four-manifold, are not treated here.

## Main results

* `TauCeti.SeibergWitten.`
  `exists_sqrt_rescaledTargetNormSq_flatDirac_const_sub_flatDirac_const_le`: the quadratic estimate
  for the Dirac remainder `i c(h b) ζ`.
* `TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le`: the quadratic
  estimate for the curvature remainder `q(ζ) / 2`.
* `TauCeti.SeibergWitten.`
  `exists_sqrt_rescaledTargetNormSq_smul_flatDirac_sub_flatDeformationDirac_sub_le`,
  `TauCeti.SeibergWitten.`
  `exists_sqrt_rescaledTargetNormSq_flatCurvature_sub_flatDeformationCurvature_sub_le`: the same
  estimates for the nonlinear parts written through the flat Dirac and curvature operators and
  their linearizations, in which the base-point values cancel.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

open exteriorPower MeasureTheory Module

namespace TauCeti.SeibergWitten

open CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

-- The dimension `Fact` makes the oriented four-space finite-dimensional.
attribute [local instance] finiteDimensional_of_finrank_four

variable [Fact (finrank ℝ V = 4)]

/-! ### From the rescaled norms to the semiclassical norms -/

section Norms

variable {B S T : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup S]
  [NormedSpace ℝ S] [NormedAddCommGroup T] [NormedSpace ℝ T] {h : ℝ}

variable (V) in
/-- `hⁿ = h⁴` on the oriented four-space. -/
private theorem rpow_finrank_eq (h : ℝ) : h ^ (finrank ℝ V : ℝ) = h ^ 4 := by
  rw [Fact.out (p := finrank ℝ V = 4)]
  norm_num

variable [MeasurableSpace V] [BorelSpace V]

/-- The bilinear algebra estimate of the semiclassical norms on the four-space
(`TauCeti.exists_semiclassicalSobolevNorm_bilinear_le`) for one fixed continuous bilinear map `L`,
with its operator norm absorbed into the constant. -/
private theorem exists_semiclassicalSobolevNorm_apply_apply_le [FiniteDimensional ℝ B]
    [FiniteDimensional ℝ S] {k : ℕ} (hk : finrank ℝ V < 2 * k) (L : B →L[ℝ] S →L[ℝ] T) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ (f : V → B) (g : V → S), ContDiff ℝ k f → ContDiff ℝ k g →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i f) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i g) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i fun x ↦ L (f x) (g x)) 2) ∧
        semiclassicalSobolevNorm k h (fun x ↦ L (f x) (g x)) ≤
          C * semiclassicalSobolevNorm k h f * semiclassicalSobolevNorm k h g := by
  obtain ⟨C, hC, hB⟩ := exists_semiclassicalSobolevNorm_bilinear_le (F := B) hk S T
  exact ⟨C * ‖L‖, by positivity, fun h hh f g hf hg hfm hgm ↦ hB h hh L f g hf hg hfm hgm⟩

/-- The target norm through order `k` is at most `h²` times the semiclassical norm of order `k`:
`‖y‖_(F_(r,k)) ≤ h² ‖y‖_{k,h}`. -/
private theorem sqrt_rescaledTargetNormSq_le (k : ℕ) (hh : 0 < h) (y : V → T) :
    √(rescaledTargetNormSq (k + 1) h y) ≤ h ^ 2 * semiclassicalSobolevNorm k h y := by
  have hy := rescaledTargetNormSq_succ_le_rpow_mul k hh y
  rw [rpow_finrank_eq V] at hy
  refine Real.sqrt_le_iff.2 ⟨mul_nonneg (by positivity)
    (semiclassicalSobolevNorm_nonneg k hh.le y), ?_⟩
  nlinarith

/-- The semiclassical norms of the two components of an increment are controlled by its rescaled
norm: `h² (h ‖b‖_{k,h}) ≤ √(k + 1) ‖(b, ζ)‖_(E_(r,k))` and
`h² ‖ζ‖_{k,h} ≤ 2 √(k + 1) ‖(b, ζ)‖_(E_(r,k))`. -/
private theorem sq_mul_semiclassicalSobolevNorm_le (k : ℕ) (hh : 0 < h) (b : V → B)
    (ζ : V → S) :
    h ^ 2 * (h * semiclassicalSobolevNorm k h b) ≤
        √(k + 1) * √(rescaledFieldNormSq k h b ζ) ∧
      h ^ 2 * semiclassicalSobolevNorm k h ζ ≤
        2 * (√(k + 1) * √(rescaledFieldNormSq k h b ζ)) := by
  have hE := rpow_mul_le_mul_rescaledFieldNormSq k hh b ζ
  rw [rpow_finrank_eq V] at hE
  have := semiclassicalSobolevNorm_nonneg k hh.le b
  have := semiclassicalSobolevNorm_nonneg k hh.le ζ
  rw [← Real.sqrt_mul (by positivity)]
  refine ⟨Real.le_sqrt_of_sq_le ?_, ?_⟩
  · nlinarith [sq_nonneg (h ^ 2 * semiclassicalSobolevNorm k h ζ)]
  · rw [← div_le_iff₀' two_pos]
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [sq_nonneg (h ^ 2 * (h * semiclassicalSobolevNorm k h b))]

/-- **From a semiclassical bound on a nonlinear term to the rescaled norms.** If the semiclassical
norm of `y` is at most `C₀ (h ‖b₁ - b₂‖ ‖ζ₁‖ + h ‖b₂‖ ‖ζ₁ - ζ₂‖ + ‖ζ₁ - ζ₂‖ (‖ζ₁‖ + ‖ζ₂‖))`, the
shape of the bilinear and quadratic terms of the flat equations, then
`‖y‖_(F_(r,k)) ≤ (6 (k + 1) C₀ / h²) (‖x₁‖_(E_(r,k)) + ‖x₂‖_(E_(r,k))) ‖x₁ - x₂‖_(E_(r,k))` for
`xᵢ = (bᵢ, ζᵢ)`. -/
private theorem sqrt_rescaledTargetNormSq_le_of_le {k : ℕ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hh : 0 < h)
    {y : V → T} {b₁ b₂ : V → B} {ζ₁ ζ₂ : V → S}
    (hy : semiclassicalSobolevNorm k h y ≤
      C₀ * (h * semiclassicalSobolevNorm k h (b₁ - b₂) * semiclassicalSobolevNorm k h ζ₁ +
        h * semiclassicalSobolevNorm k h b₂ * semiclassicalSobolevNorm k h (ζ₁ - ζ₂) +
        semiclassicalSobolevNorm k h (ζ₁ - ζ₂) *
          (semiclassicalSobolevNorm k h ζ₁ + semiclassicalSobolevNorm k h ζ₂))) :
    √(rescaledTargetNormSq (k + 1) h y) ≤
      6 * (k + 1) * C₀ / h ^ 2 *
        (√(rescaledFieldNormSq k h b₁ ζ₁) + √(rescaledFieldNormSq k h b₂ ζ₂)) *
          √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  obtain ⟨hδb, hδζ⟩ := sq_mul_semiclassicalSobolevNorm_le k hh (b₁ - b₂) (ζ₁ - ζ₂)
  obtain ⟨-, hζ₁⟩ := sq_mul_semiclassicalSobolevNorm_le k hh b₁ ζ₁
  obtain ⟨hb₂, hζ₂⟩ := sq_mul_semiclassicalSobolevNorm_le k hh b₂ ζ₂
  set nδb := semiclassicalSobolevNorm k h (b₁ - b₂)
  set nb₂ := semiclassicalSobolevNorm k h b₂
  set nζ₁ := semiclassicalSobolevNorm k h ζ₁
  set nζ₂ := semiclassicalSobolevNorm k h ζ₂
  set nδζ := semiclassicalSobolevNorm k h (ζ₁ - ζ₂)
  have : 0 ≤ nδb := semiclassicalSobolevNorm_nonneg k hh.le _
  have : 0 ≤ nb₂ := semiclassicalSobolevNorm_nonneg k hh.le _
  have : 0 ≤ nζ₁ := semiclassicalSobolevNorm_nonneg k hh.le _
  have : 0 ≤ nζ₂ := semiclassicalSobolevNorm_nonneg k hh.le _
  have : 0 ≤ nδζ := semiclassicalSobolevNorm_nonneg k hh.le _
  set s := √((k : ℝ) + 1)
  have hs : s ^ 2 = k + 1 := Real.sq_sqrt (by positivity)
  calc √(rescaledTargetNormSq (k + 1) h y) ≤ h ^ 2 * semiclassicalSobolevNorm k h y :=
        sqrt_rescaledTargetNormSq_le k hh y
    _ ≤ h ^ 2 * (C₀ * (h * nδb * nζ₁ + h * nb₂ * nδζ + nδζ * (nζ₁ + nζ₂))) := by gcongr
    -- Each factor carries one `h²`; the leftover `h⁻²` is the volume factor `h^(-n/2)`.
    _ = C₀ / h ^ 2 * (h ^ 2 * (h * nδb) * (h ^ 2 * nζ₁) + h ^ 2 * (h * nb₂) * (h ^ 2 * nδζ) +
          h ^ 2 * nδζ * (h ^ 2 * nζ₁ + h ^ 2 * nζ₂)) := by field_simp
    _ ≤ C₀ / h ^ 2 * ((s * √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂))) *
        (2 * (s * √(rescaledFieldNormSq k h b₁ ζ₁))) +
          (s * √(rescaledFieldNormSq k h b₂ ζ₂)) *
            (2 * (s * √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)))) +
          (2 * (s * √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)))) *
            (2 * (s * √(rescaledFieldNormSq k h b₁ ζ₁)) +
              2 * (s * √(rescaledFieldNormSq k h b₂ ζ₂)))) := by
        gcongr
    _ = _ := by rw [← hs]; ring

end Norms

/-! ### The Dirac remainder -/

section Dirac

variable (o ρ) in
/-- Clifford multiplication `(β, φ) ↦ i c(β) φ` of a positive spinor by a covector, as a
continuous real-bilinear map: the flat Dirac operator of the constant fields `β` and `φ`. -/
private def cliffordMulL :
    (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] positiveHalfSpinors o ρ →L[ℝ] W :=
  LinearMap.toContinuousBilinearMap <| LinearMap.mk₂ ℝ
    (fun β (φ : positiveHalfSpinors o ρ) ↦ flatDirac ρ (fun _ ↦ β) (fun _ ↦ (φ : W)) 0)
    (fun β₁ β₂ φ ↦ flatDirac_add_connection ρ (fun _ ↦ β₁) (fun _ ↦ β₂) _ 0)
    (fun c β φ ↦ flatDirac_smul_connection_const (b := fun _ ↦ β) ρ c _)
    (fun β φ₁ φ₂ ↦ by
      simp only [Submodule.coe_add]
      exact flatDirac_add ρ (differentiableAt_const _) (differentiableAt_const _))
    (fun c β φ ↦ by
      simp only [Submodule.coe_smul_of_tower, ← Complex.coe_smul]
      exact flatDirac_smul ρ (c : ℂ))

/-- The flat Dirac operator of a constant field `φ` for the connection `b` at `x` is the Clifford
multiplication `i c(b x) φ`. -/
private theorem flatDirac_const_eq_cliffordMulL (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (φ : positiveHalfSpinors o ρ) (x : V) :
    flatDirac ρ b (fun _ ↦ (φ : W)) x = cliffordMulL o ρ (b x) φ := by
  rw [cliffordMulL, LinearMap.toContinuousBilinearMap_apply, LinearMap.mk₂_apply,
    flatDirac_const_eq_smul_ι, flatDirac_const_eq_smul_ι]

variable [MeasurableSpace V] [BorelSpace V]

/-- **The quadratic estimate for the Dirac remainder in the rescaled norms.** Let `k ≥ 3`. There
is a constant `C ≥ 0` such that for every scale `h > 0` and all connection increments `b₁`, `b₂`
and positive spinor increments `ζ₁`, `ζ₂` of class `Cᵏ` with square-integrable derivatives
through order `k`, the Clifford multiplications `i c(h bᵢ) ζᵢ`, the nonlinear remainders of the
flat Dirac row read at scale `h`, satisfy

`‖i c(h b₁) ζ₁ - i c(h b₂) ζ₂‖_(F_(r,k)) ≤
  (C / h²) (‖(b₁, ζ₁)‖_(E_(r,k)) + ‖(b₂, ζ₂)‖_(E_(r,k))) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_(E_(r,k))`. -/
theorem exists_sqrt_rescaledTargetNormSq_flatDirac_const_sub_flatDirac_const_le {k : ℕ}
    (hk : 2 < k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      ∀ (b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ₁ ζ₂ : V → positiveHalfSpinors o ρ),
      ContDiff ℝ k b₁ → ContDiff ℝ k b₂ → ContDiff ℝ k ζ₁ → ContDiff ℝ k ζ₂ →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i b₁) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i b₂) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (k + 1) h fun x ↦
          flatDirac ρ (h • b₁) (fun _ ↦ (ζ₁ x : W)) x -
            flatDirac ρ (h • b₂) (fun _ ↦ (ζ₂ x : W)) x) ≤
        C / h ^ 2 * (√(rescaledFieldNormSq k h b₁ ζ₁) + √(rescaledFieldNormSq k h b₂ ζ₂)) *
          √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  have hk' : finrank ℝ V < 2 * k := by rw [Fact.out (p := finrank ℝ V = 4)]; omega
  obtain ⟨C₀, hC₀, hB⟩ := exists_semiclassicalSobolevNorm_apply_apply_le hk' (cliffordMulL o ρ)
  refine ⟨6 * (k + 1) * C₀, by positivity, fun h hh b₁ b₂ ζ₁ ζ₂ hb₁ hb₂ hζ₁ hζ₂ hb₁m hb₂m hζ₁m
    hζ₂m ↦ sqrt_rescaledTargetNormSq_le_of_le hC₀ hh ?_⟩
  -- The difference of the remainders splits as `i c(h (b₁ - b₂)) ζ₁ + i c(h b₂) (ζ₁ - ζ₂)`.
  have hsplit : (fun x ↦ flatDirac ρ (h • b₁) (fun _ ↦ (ζ₁ x : W)) x -
      flatDirac ρ (h • b₂) (fun _ ↦ (ζ₂ x : W)) x) =
      (fun x ↦ cliffordMulL o ρ ((h • (b₁ - b₂)) x) (ζ₁ x)) +
        fun x ↦ cliffordMulL o ρ ((h • b₂) x) ((ζ₁ - ζ₂) x) := by
    ext x
    simp only [flatDirac_const_eq_cliffordMulL, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_sub, map_sub, _root_.sub_apply]
    abel
  have hδb := hb₁.sub hb₂
  have hδζ := hζ₁.sub hζ₂
  obtain ⟨h₁m, h₁⟩ := hB h hh (h • (b₁ - b₂)) ζ₁ (hδb.const_smul h) hζ₁
    (fun i hi ↦ (hb₁.memLp_iteratedFDeriv_sub (by exact_mod_cast hi) hb₂ (hb₁m i hi)
      (hb₂m i hi)).iteratedFDeriv_const_smul h) hζ₁m
  obtain ⟨-, h₂⟩ := hB h hh (h • b₂) (ζ₁ - ζ₂) (hb₂.const_smul h) hδζ
    (fun i hi ↦ (hb₂m i hi).iteratedFDeriv_const_smul h)
    fun i hi ↦ hζ₁.memLp_iteratedFDeriv_sub (by exact_mod_cast hi) hζ₂ (hζ₁m i hi) (hζ₂m i hi)
  rw [semiclassicalSobolevNorm_const_smul, abs_of_pos hh] at h₁ h₂
  have hc₁ : ContDiff ℝ k fun x ↦ cliffordMulL o ρ ((h • (b₁ - b₂)) x) (ζ₁ x) :=
    (cliffordMulL o ρ).isBoundedBilinearMap.contDiff.comp ((hδb.const_smul h).prodMk hζ₁)
  have hc₂ : ContDiff ℝ k fun x ↦ cliffordMulL o ρ ((h • b₂) x) ((ζ₁ - ζ₂) x) :=
    (cliffordMulL o ρ).isBoundedBilinearMap.contDiff.comp ((hb₂.const_smul h).prodMk hδζ)
  have := semiclassicalSobolevNorm_nonneg k hh.le (ζ₁ - ζ₂)
  have := semiclassicalSobolevNorm_nonneg k hh.le ζ₁
  have := semiclassicalSobolevNorm_nonneg k hh.le ζ₂
  rw [hsplit]
  refine (semiclassicalSobolevNorm_add_le hc₁ hc₂ h₁m hh.le).trans ?_
  nlinarith [mul_nonneg hC₀ (mul_nonneg ‹0 ≤ semiclassicalSobolevNorm k h (ζ₁ - ζ₂)›
    (add_nonneg ‹0 ≤ semiclassicalSobolevNorm k h ζ₁› ‹0 ≤ semiclassicalSobolevNorm k h ζ₂›))]

variable (e : OrthonormalBasis (Fin 4) ℝ V)

/-- **The quadratic estimate for the nonlinear part of the flat Dirac operator.** Let `k ≥ 3`.
There is a constant `C ≥ 0` such that for every scale `h > 0`, every pair `(b, ψ)` with `ψ`
differentiable, and all increments `(b₁, ζ₁)` and `(b₂, ζ₂)` of class `Cᵏ` with square-integrable
derivatives through order `k`, the expressions
`M(bᵢ, ζᵢ) = D_{b + bᵢ} (ψ + ζᵢ) - D'_{(b, ψ)}(bᵢ, ζᵢ)`, weighted by `h`, satisfy

`‖h (M(b₁, ζ₁) - M(b₂, ζ₂))‖_(F_(r,k)) ≤
  (C / h²) (‖(b₁, ζ₁)‖_(E_(r,k)) + ‖(b₂, ζ₂)‖_(E_(r,k))) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_(E_(r,k))`.

Each `M(bᵢ, ζᵢ)` is the nonlinear part `i c(bᵢ) ζᵢ` of the flat Dirac operator plus the base-point
value `D_b ψ` (`TauCeti.SeibergWitten.flatDirac_add_eq_add_flatDeformationDirac_add`); that common
term cancels, and `h i c(bᵢ) ζᵢ = i c(h bᵢ) ζᵢ` is the Dirac remainder read at scale `h`
(`TauCeti.SeibergWitten.`
`exists_sqrt_rescaledTargetNormSq_flatDirac_const_sub_flatDirac_const_le`). The constant does not
depend on `h` or on `(b, ψ)`. -/
theorem exists_sqrt_rescaledTargetNormSq_smul_flatDirac_sub_flatDeformationDirac_sub_le {k : ℕ}
    (hk : 2 < k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ (b b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
      (ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ), Differentiable ℝ (fun y ↦ (ψ y : W)) →
      ContDiff ℝ k b₁ → ContDiff ℝ k b₂ → ContDiff ℝ k ζ₁ → ContDiff ℝ k ζ₂ →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i b₁) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i b₂) 2) →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (k + 1) h fun y ↦
          h • ((flatDirac ρ (b + b₁) (fun z ↦ ((ψ + ζ₁) z : W)) y -
              flatDeformationDirac e b b₁ ψ ζ₁ y) -
            (flatDirac ρ (b + b₂) (fun z ↦ ((ψ + ζ₂) z : W)) y -
              flatDeformationDirac e b b₂ ψ ζ₂ y))) ≤
        C / h ^ 2 * (√(rescaledFieldNormSq k h b₁ ζ₁) + √(rescaledFieldNormSq k h b₂ ζ₂)) *
          √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  obtain ⟨C, hC, hDirac⟩ :=
    exists_sqrt_rescaledTargetNormSq_flatDirac_const_sub_flatDirac_const_le (V := V) (o := o)
      (ρ := ρ) hk
  refine ⟨C, hC, fun h hh b b₁ b₂ ψ ζ₁ ζ₂ hψ hb₁ hb₂ hζ₁ hζ₂ hb₁m hb₂m hζ₁m hζ₂m ↦ ?_⟩
  -- The underlying spinor fields in `W` are differentiable.
  have hcoe {ζ : V → positiveHalfSpinors o ρ} (hζ : ContDiff ℝ k ζ) :
      Differentiable ℝ (fun y ↦ (ζ y : W)) :=
    (((positiveHalfSpinors o ρ).subtypeL.restrictScalars ℝ).contDiff.comp hζ).differentiable
      (by norm_cast; omega)
  -- The weighted nonlinear parts differ by the difference of the Dirac remainders.
  have hN : (fun y ↦ h • ((flatDirac ρ (b + b₁) (fun z ↦ ((ψ + ζ₁) z : W)) y -
        flatDeformationDirac e b b₁ ψ ζ₁ y) -
      (flatDirac ρ (b + b₂) (fun z ↦ ((ψ + ζ₂) z : W)) y -
        flatDeformationDirac e b b₂ ψ ζ₂ y))) =
      fun y ↦ flatDirac ρ (h • b₁) (fun _ ↦ (ζ₁ y : W)) y -
        flatDirac ρ (h • b₂) (fun _ ↦ (ζ₂ y : W)) y := by
    funext y
    rw [flatDirac_add_eq_add_flatDeformationDirac_add e (hψ y) (hcoe hζ₁ y),
      flatDirac_add_eq_add_flatDeformationDirac_add e (hψ y) (hcoe hζ₂ y),
      flatDirac_smul_connection_const, flatDirac_smul_connection_const, ← smul_sub]
    congr 1
    abel
  rw [hN]
  exact hDirac h hh b₁ b₂ ζ₁ ζ₂ hb₁ hb₂ hζ₁ hζ₂ hb₁m hb₂m hζ₁m hζ₂m

end Dirac

/-! ### The curvature remainder -/

section Curvature

variable (hkl : 2 + 2 = finrank ℝ V)

variable (o ρ) in
/-- The polarization `q'` of the quadratic two-form with values in the two-vectors, as a
continuous real-bilinear map. -/
private def quadraticTwoFormPolarL :
    positiveHalfSpinors o ρ →L[ℝ] positiveHalfSpinors o ρ →L[ℝ] ⋀[ℝ]^2 V :=
  (ContinuousLinearMap.compL ℝ _ _ _ (Submodule.subtypeL _)).comp (quadraticTwoFormPolar o ρ hkl)

variable [MeasurableSpace V] [BorelSpace V]

/-- **The quadratic estimate for the curvature remainder in the rescaled norms.** Let `k ≥ 3`.
There is a constant `C ≥ 0` such that for every scale `h > 0`, all connection increments `b₁`,
`b₂` and all positive spinor increments `ζ₁`, `ζ₂` of class `Cᵏ` with square-integrable derivatives
through order `k`, the halved quadratic two-forms `q(ζᵢ) / 2`, the nonlinear remainders of the
flat curvature row, satisfy

`‖q(ζ₁) / 2 - q(ζ₂) / 2‖_(F_(r,k)) ≤
  (C / h²) (‖(b₁, ζ₁)‖_(E_(r,k)) + ‖(b₂, ζ₂)‖_(E_(r,k))) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_(E_(r,k))`. -/
theorem exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le {k : ℕ} (hk : 2 < k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      ∀ (b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ζ₁ ζ₂ : V → positiveHalfSpinors o ρ),
      ContDiff ℝ k ζ₁ → ContDiff ℝ k ζ₂ →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (k + 1) h fun x ↦
          (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ₁ x) : ⋀[ℝ]^2 V) -
            (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ₂ x) : ⋀[ℝ]^2 V)) ≤
        C / h ^ 2 * (√(rescaledFieldNormSq k h b₁ ζ₁) + √(rescaledFieldNormSq k h b₂ ζ₂)) *
          √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  have hk' : finrank ℝ V < 2 * k := by rw [Fact.out (p := finrank ℝ V = 4)]; omega
  obtain ⟨C₀, hC₀, hB⟩ :=
    exists_semiclassicalSobolevNorm_apply_apply_le hk' (quadraticTwoFormPolarL o ρ hkl)
  refine ⟨6 * (k + 1) * C₀, by positivity, fun h hh b₁ b₂ ζ₁ ζ₂ hζ₁ hζ₂ hζ₁m hζ₂m ↦
    sqrt_rescaledTargetNormSq_le_of_le hC₀ hh ?_⟩
  -- `q(ζ₁) / 2 - q(ζ₂) / 2 = q'(ζ₁ - ζ₂, ζ₁ + ζ₂) / 4`.
  have hsplit : (fun x ↦ (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ₁ x) : ⋀[ℝ]^2 V) -
      (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ₂ x) : ⋀[ℝ]^2 V)) =
      (4⁻¹ : ℝ) • fun x ↦ quadraticTwoFormPolarL o ρ hkl ((ζ₁ - ζ₂) x) ((ζ₁ + ζ₂) x) := by
    ext1 x
    simp only [quadraticTwoFormPolarL, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, Submodule.coe_subtypeL, Submodule.coe_subtype,
      Pi.smul_apply, Pi.sub_apply, Pi.add_apply,
      quadraticTwoFormPolar_sub_add, Submodule.coe_smul, Submodule.coe_sub, smul_sub, smul_smul]
    norm_num
  obtain ⟨-, hN⟩ := hB h hh (ζ₁ - ζ₂) (ζ₁ + ζ₂) (hζ₁.sub hζ₂) (hζ₁.add hζ₂)
    (fun i hi ↦ hζ₁.memLp_iteratedFDeriv_sub (by exact_mod_cast hi) hζ₂ (hζ₁m i hi) (hζ₂m i hi))
    fun i hi ↦ hζ₁.memLp_iteratedFDeriv_add (by exact_mod_cast hi) hζ₂ (hζ₁m i hi) (hζ₂m i hi)
  have hσ := semiclassicalSobolevNorm_add_le hζ₁ hζ₂ hζ₁m hh.le
  have := semiclassicalSobolevNorm_nonneg k hh.le (b₁ - b₂)
  have := semiclassicalSobolevNorm_nonneg k hh.le b₂
  have := semiclassicalSobolevNorm_nonneg k hh.le ζ₁
  have := semiclassicalSobolevNorm_nonneg k hh.le (ζ₁ - ζ₂)
  have := semiclassicalSobolevNorm_nonneg k hh.le (ζ₁ + ζ₂)
  have := semiclassicalSobolevNorm_nonneg k hh.le
    fun x ↦ quadraticTwoFormPolarL o ρ hkl ((ζ₁ - ζ₂) x) ((ζ₁ + ζ₂) x)
  rw [hsplit, semiclassicalSobolevNorm_const_smul, abs_of_pos (by norm_num)]
  nlinarith [mul_le_mul_of_nonneg_left hσ
    (mul_nonneg hC₀ ‹0 ≤ semiclassicalSobolevNorm k h (ζ₁ - ζ₂)›),
    mul_nonneg hC₀ (mul_nonneg (mul_nonneg hh.le ‹0 ≤ semiclassicalSobolevNorm k h (b₁ - b₂)›)
      ‹0 ≤ semiclassicalSobolevNorm k h ζ₁›),
    mul_nonneg hC₀ (mul_nonneg (mul_nonneg hh.le ‹0 ≤ semiclassicalSobolevNorm k h b₂›)
      ‹0 ≤ semiclassicalSobolevNorm k h (ζ₁ - ζ₂)›)]

/-- **The quadratic estimate for the nonlinear part of the flat curvature equation.** Let
`k ≥ 3`. There is a constant `C ≥ 0` such that for every scale `h > 0`, every pair `(b, ψ)` with
`b` differentiable, and all increments `(b₁, ζ₁)` and `(b₂, ζ₂)` with `b₁`, `b₂` differentiable
and `ζ₁`, `ζ₂` of class `Cᵏ` with square-integrable derivatives through order `k`, the expressions
`M(bᵢ, ζᵢ) = flatCurvature (b + bᵢ) (ψ + ζᵢ) - F'_ψ(bᵢ, ζᵢ)` satisfy

`‖M(b₁, ζ₁) - M(b₂, ζ₂)‖_(F_(r,k)) ≤
  (C / h²) (‖(b₁, ζ₁)‖_(E_(r,k)) + ‖(b₂, ζ₂)‖_(E_(r,k))) ‖(b₁ - b₂, ζ₁ - ζ₂)‖_(E_(r,k))`.

Each `M(bᵢ, ζᵢ)` is the nonlinear part `q(ζᵢ) / 2` of the flat curvature equation plus the
base-point value `flatCurvature b ψ` (`TauCeti.SeibergWitten.flatCurvature_add`); that common term
cancels, so `M(b₁, ζ₁) - M(b₂, ζ₂)` is the difference of the curvature remainders
(`TauCeti.SeibergWitten.exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le`). The constant
does not depend on `h` or on `(b, ψ)`. -/
theorem exists_sqrt_rescaledTargetNormSq_flatCurvature_sub_flatDeformationCurvature_sub_le
    {k : ℕ} (hk : 2 < k) :
    ∃ C, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → ∀ (b b₁ b₂ : V → V [⋀^Fin 1]→L[ℝ] ℝ)
      (ψ ζ₁ ζ₂ : V → positiveHalfSpinors o ρ), Differentiable ℝ b → Differentiable ℝ b₁ →
      Differentiable ℝ b₂ → ContDiff ℝ k ζ₁ → ContDiff ℝ k ζ₂ →
      (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₁) 2) → (∀ i ≤ k, MemLp (iteratedFDeriv ℝ i ζ₂) 2) →
      √(rescaledTargetNormSq (k + 1) h fun y ↦
          (flatCurvature o ρ hkl (b + b₁) (ψ + ζ₁) y -
              flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ y) -
            (flatCurvature o ρ hkl (b + b₂) (ψ + ζ₂) y -
              flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ y)) ≤
        C / h ^ 2 * (√(rescaledFieldNormSq k h b₁ ζ₁) + √(rescaledFieldNormSq k h b₂ ζ₂)) *
          √(rescaledFieldNormSq k h (b₁ - b₂) (ζ₁ - ζ₂)) := by
  obtain ⟨C, hC, hq⟩ :=
    exists_sqrt_rescaledTargetNormSq_quadraticTwoForm_sub_le (o := o) (ρ := ρ) hkl hk
  refine ⟨C, hC, fun h hh b b₁ b₂ ψ ζ₁ ζ₂ hb hb₁ hb₂ hζ₁ hζ₂ hζ₁m hζ₂m ↦ ?_⟩
  -- The nonlinear parts differ by `q(ζ₁) / 2 - q(ζ₂) / 2`.
  have hN : (fun y ↦ (flatCurvature o ρ hkl (b + b₁) (ψ + ζ₁) y -
        flatDeformationCurvature o ρ hkl b₁ ψ ζ₁ y) -
      (flatCurvature o ρ hkl (b + b₂) (ψ + ζ₂) y - flatDeformationCurvature o ρ hkl b₂ ψ ζ₂ y)) =
      fun y ↦ (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ₁ y) : ⋀[ℝ]^2 V) -
        (2⁻¹ : ℝ) • (quadraticTwoForm o ρ hkl (ζ₂ y) : ⋀[ℝ]^2 V) := by
    funext y
    rw [flatCurvature_add hkl (hb y) (hb₁ y), flatCurvature_add hkl (hb y) (hb₂ y)]
    abel
  rw [hN]
  exact hq h hh b₁ b₂ ζ₁ ζ₂ hζ₁ hζ₂ hζ₁m hζ₂m

end Curvature

end TauCeti.SeibergWitten
