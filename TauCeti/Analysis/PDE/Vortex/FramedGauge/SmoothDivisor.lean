/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor.Normalized
public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Atlas
public import TauCeti.Analysis.Polynomial.SymmetricPower
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Analysis.Calculus.ContDiff.SuperpositionIntegral
import TauCeti.Analysis.Polynomial.PrescribedPowerSums
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.BesselPotential.Real
import TauCeti.Analysis.Sobolev.BesselPotential.ZeroAtInfty
import TauCeti.Analysis.PDE.Vortex.Flux.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The vortex moduli space is diffeomorphic to the divisor space

For an integer `k ≥ 4`, the vortex moduli space in `A_m^k / G_(k+1)`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuli`) is a smooth manifold modelled on `ℝ^(2m)`
(`TauCeti.Vortex.SobolevFieldSpace.isManifold_vortexModuli`), and the zero divisor is a
homeomorphism onto `Sym ℂ m` (`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph`). The
symmetric power `Sym ℂ m` is identified with `ℂᵐ` by the coefficients of the monic polynomial with
the given roots (`Sym.coeffHomeomorph`), collisions of zeros included. This file shows that, in
these coordinates, the divisor is a diffeomorphism from the vortex moduli space onto `ℂᵐ`
(`TauCeti.Vortex.SobolevFieldSpace.vortexModuliDiffeomorph`): Taubes's identification of the
moduli space of framed vortices of degree `m` with the symmetric product of `m` points of the
plane, as smooth manifolds.

**The inverse is smooth.** The orbit with divisor coefficients `c` is the orbit of the normalized
vortex `y_c` (`TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph_symm_coeffHomeomorph_symm`),
the plane vortex of the monic polynomial `P_c` moved into `A_m^k` by its end-normalizing gauge, and
its real coordinates in `A_m^k` depend smoothly on `c`
(`TauCeti.Vortex.SobolevFieldSpace.contDiff_subRef_normalizedVortex`). Every chart of the atlas of
the vortex moduli space is, near each vortex, the restriction of a map smooth in the real
coordinates of the fields (`TauCeti.Vortex.SobolevFieldSpace.IsSmoothVortexModuliChart`), so in
every chart the orbit of `y_c` is a smooth function of `c`.

**The divisor is smooth.** The power sums `∑_{z ∈ D} zʲ` of the zero divisor `D` of a vortex are
moments of its section `α`: the distributional scalar equation
`Δ log |α|² = (|α|² - 1) / 4 + 4π ∑_{z ∈ D} δ_z`
(`TauCeti.Vortex.integral_laplacian_mul_log_normSq`) tested against `χ L (zʲ)`, for a cutoff `χ`
equal to `1` on a disc containing the zeros and a real linear functional `L`, reads

`4π ∑_{z ∈ D} L (zʲ) = ∫ Δ(χ L (zʲ)) log |α|² - ∫ χ L (zʲ) (|α|² - 1) / 4`.

Since `L (zʲ)` is harmonic, `Δ(χ L (zʲ))` vanishes where `χ = 1`, so only values of `α` bounded
away from zero enter the first integral. Near a given field the sections of all fields are
uniformly close, so one cutoff serves all the vortices near it, and both integrals are smooth in
the real coordinates of the field: the section is a continuous affine function of the coordinates
with values in the bounded continuous functions, and integrals of smooth functions of it against
compactly supported weights are smooth
(`BoundedContinuousFunction.contDiff_integral_mul_comp`). The coefficients of the divisor are the
Newton coefficients of its power sums (`TauCeti.newtonCoeff_sum_map_pow`,
`TauCeti.contDiffAt_newtonCoeff`), so they are smooth functions of the field near every field
(`TauCeti.Vortex.SobolevFieldSpace.exists_contDiffAt_coeffEquiv_sobolevVortexDivisor`). In a chart,
the inverse lifts to a smooth family of vortices, so the divisor coefficients are smooth in every
chart.

## Main definitions

* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliDiffeomorph`: for `k ≥ 4`, the diffeomorphism from
  the vortex moduli space onto `ℂᵐ` given by the coefficients of the zero divisor.

## Main results

* `TauCeti.Vortex.SobolevFieldSpace.vortexModuliHomeomorph_symm_coeffHomeomorph_symm`: the vortex
  orbit with divisor coefficients `c` is the orbit of the normalized vortex `y_c`.
* `TauCeti.Vortex.SobolevFieldSpace.exists_contDiffAt_coeffEquiv_sobolevVortexDivisor`: near every
  field of `A_m^k`, the divisor coefficients of the vortices are a smooth function of their real
  coordinates.
* `TauCeti.Vortex.SobolevFieldSpace.contMDiff_vortexModuliHomeomorph_symm_coeffHomeomorph_symm`,
  `TauCeti.Vortex.SobolevFieldSpace.contMDiff_coeffHomeomorph_vortexModuliHomeomorph`: the vortex
  orbit is a smooth function of its divisor coefficients, and conversely.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Proposition 4.1.
-/

public section

noncomputable section

open BesselPotentialSpace Complex Filter InnerProductSpace Laplacian MeasureTheory Metric Topology
  TauCeti.Polynomial
open scoped BesselPotentialSpace BoundedContinuousFunction ContDiff Manifold Real

namespace TauCeti.Vortex

/-! ### A smooth substitute for `log ‖a‖²` -/

/-- A smooth function on `ℂ` equal to `log ‖a‖²` where `‖a‖ ≥ η`. -/
private def logNormSqCut (η : ℝ) (a : ℂ) : ℝ :=
  Real.log (‖a‖ ^ 2 + Real.smoothTransition ((η ^ 2 - ‖a‖ ^ 2) / η ^ 2))

private theorem contDiff_logNormSqCut {η : ℝ} (hη : η ≠ 0) : ContDiff ℝ ∞ (logNormSqCut η) := by
  have hn : ContDiff ℝ ∞ fun a : ℂ ↦ ‖a‖ ^ 2 := contDiff_norm_sq ℝ
  refine (hn.add (Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub hn).div_const _))).log fun a ↦ ?_
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Function.comp_apply, norm_zero, zero_pow two_ne_zero, sub_zero,
      div_self (pow_ne_zero 2 hη), Real.smoothTransition.one_of_one_le le_rfl]
    norm_num
  · exact (add_pos_of_pos_of_nonneg (by positivity) (Real.smoothTransition.nonneg _)).ne'

private theorem logNormSqCut_of_le {η : ℝ} (hη : 0 < η) {a : ℂ} (ha : η ≤ ‖a‖) :
    logNormSqCut η a = Real.log (‖a‖ ^ 2) := by
  rw [logNormSqCut, Real.smoothTransition.zero_of_nonpos, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)

namespace SobolevFieldSpace

variable {f : ContDiffBump (0 : ℝ)} {m k : ℕ}

/-! ### The normalized vortices as points of the moduli space -/

variable [Fact (1 < k)] {hs : 1 < (k : ℝ) + 1}

/-- **The vortex orbit with divisor coefficients `c`** is the orbit of the normalized vortex `y_c`,
for `k ≥ 4` and `m ≥ 1`. -/
theorem vortexModuliHomeomorph_symm_coeffHomeomorph_symm (hm : 0 < m) (hk : 3 < k)
    (c : Fin m → ℂ) :
    (vortexModuliHomeomorph f m hs hk).symm ((Sym.coeffHomeomorph ℂ m).symm c) =
      ⟨Quotient.mk _ (normalizedVortex hm f k c),
        mk_mem_vortexModuli (equation_normalizedVortex hm f k c)⟩ := by
  rw [Sym.coeffHomeomorph_symm_apply]
  exact vortexModuliHomeomorph_symm_apply_mk hk (equation_normalizedVortex hm f k c)
    (sobolevVortexDivisor_eq_iff.2 <| by
    simpa only [coe_toFramedFieldSpace, coe_normalizedVortex] using
      isZeroMultiplicity_sectionValue_normalizedVortex c)

/-! ### The divisor coefficients as smooth functions of the field -/

section DivisorCoeff

variable {s : ℝ} {h : 0 ≤ s}

/-- The section of the field of real coordinates `u ∈ (H^s_ℝ)⁴`, `s > 1`, as a bounded continuous
function, real-linear and continuous in `u` (`sectionCLM_apply`). -/
private def sectionCLM (hs : 1 < s) : (Fin 4 → realSubmodule ℂ h) →L[ℝ] ℂ →ᵇ ℂ :=
  let T : realSubmodule ℂ h →L[ℝ] ℂ →ᵇ ℂ :=
    ((toBCF (finrank_real_complex_lt_two_mul hs)).restrictScalars ℝ).comp
      (realSubmodule ℂ h).subtypeL
  (2 : ℂ) • (T.comp (ContinuousLinearMap.proj 2) + (I : ℂ) • T.comp (ContinuousLinearMap.proj 3))

private theorem sectionCLM_apply (hs : 1 < s) (u : Fin 4 → realSubmodule ℂ h) (z : ℂ) :
    sectionCLM hs u z = sectionValue (continuousRepField u) z := by
  simp only [sectionCLM, smul_add, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Submodule.coe_subtypeL, Submodule.subtype_apply,
    ContinuousLinearMap.coe_restrictScalars', coe_toBCF, toZeroAtInfty_coe_apply_eq_continuousRep,
    smul_eq_mul, sectionValue_apply, continuousRepField_apply]
  ring

/-- The reference section `α_m`, as a bounded continuous function. -/
private def referenceSectionBCF (f : ContDiffBump (0 : ℝ)) (m : ℕ) : ℂ →ᵇ ℂ :=
  .ofNormedAddCommGroup (referenceSection f m) (contDiff_referenceSection f m).continuous 1
    (norm_referenceSection_le_one f m)

/-- The section of a field of `A_m^s`, `s > 1`, is `α_m` plus the section of its real
coordinates. -/
private theorem referenceSectionBCF_add_sectionCLM_realSubRef (hs : 1 < s)
    (x : SobolevFieldSpace f m s) (z : ℂ) :
    (referenceSectionBCF f m + sectionCLM hs (x.realSubRef h)) z = sectionValue x z := by
  conv_rhs => rw [← ofRealSubRef_realSubRef hs (h := h) x]
  rw [add_apply, sectionCLM_apply, coe_ofRealSubRef]
  simp only [referenceSectionBCF, BoundedContinuousFunction.coe_ofNormedAddCommGroup,
    ← sectionValue_referenceField f m z, sectionValue_apply, Pi.add_apply, PiLp.add_apply]
  push_cast
  ring

end DivisorCoeff

/-! ### The power sums of the zeros as smooth functionals of the section -/

/-- The functional of a section `α` that gives `∑_{z ∈ D} L (zʲ)` for a vortex with zero divisor `D`
whose section has norm above `1 / 4` where the cutoff `χ` is not identically `1`
(`sum_map_eq_zeroMoment`):
`(4π)⁻¹ (∫ Δ(χ L (zʲ)) log |α|² - ∫ χ L (zʲ) (|α|² - 1) / 4)`, with `log |α|²` replaced by the
smooth function `logNormSqCut (1 / 4)` of `α`. -/
private def zeroMoment (χ : ContDiffBump (0 : ℂ)) (L : ℂ →L[ℝ] ℝ) (j : ℕ) (α : ℂ → ℂ) : ℝ :=
  (4 * π)⁻¹ * ((∫ z, Δ (fun y ↦ χ y * L (y ^ j)) z * logNormSqCut (1 / 4) (α z)) -
    ∫ z, (χ z * L (z ^ j)) * ((‖α z‖ ^ 2 - 1) / 4))

/-- A real-linear functional of a power, `y ↦ L (yʲ)`, is smooth. -/
private theorem contDiff_clm_pow (L : ℂ →L[ℝ] ℝ) (j : ℕ) : ContDiff ℝ ∞ fun y : ℂ ↦ L (y ^ j) :=
  L.contDiff.comp ((contDiff_id.pow j : ContDiff ℂ ∞ fun z : ℂ ↦ z ^ j).restrict_scalars ℝ)

/-- The moment functional is smooth along a smooth family of bounded continuous sections. -/
private theorem contDiff_zeroMoment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℂ →ᵇ ℂ} (hF : ContDiff ℝ ∞ F) (χ : ContDiffBump (0 : ℂ)) (L : ℂ →L[ℝ] ℝ) (j : ℕ) :
    ContDiff ℝ ∞ fun u ↦ zeroMoment χ L j (F u) := by
  have hχw : ContDiff ℝ ∞ fun y ↦ χ y * L (y ^ j) :=
    χ.contDiff.mul (contDiff_clm_pow L j)
  have hχwc : HasCompactSupport fun y ↦ χ y * L (y ^ j) := χ.hasCompactSupport.mul_right
  have hΔc : HasCompactSupport (Δ fun y ↦ χ y * L (y ^ j)) :=
    hχwc.mono' ((subset_tsupport _).trans (tsupport_laplacian_subset _))
  exact contDiff_const.mul ((BoundedContinuousFunction.contDiff_integral_mul_comp hF
    (contDiff_logNormSqCut (by norm_num)) (((hχw.of_le (by simp)).continuous_laplacian
      ).integrable_of_hasCompactSupport hΔc)).sub
    (BoundedContinuousFunction.contDiff_integral_mul_comp hF
      (((contDiff_norm_sq ℝ).sub contDiff_const).div_const _)
      (hχw.continuous.integrable_of_hasCompactSupport hχwc)))

/-- **The power sums of the zeros of a vortex as moments.** Let `x` be a `C²` vortex whose section
has zero divisor `D` and norm above `1 / 4` outside the disc of radius `χ.rIn`. Then
`∑_{z ∈ D} L (zʲ)` is the moment functional of the section: by the distributional scalar equation
`Δ log |α|² = (|α|² - 1) / 4 + 4π ∑_{z ∈ D} δ_z` tested against `χ L (zʲ)`, where `Δ(χ L (zʲ))`
vanishes on the disc, `L (zʲ)` being harmonic. -/
private theorem sum_map_eq_zeroMoment {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ i : Fin 4, ContDiff ℝ 2 fun y ↦ x y i) (hsol : ∀ z, equation x z = 0) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (χ : ContDiffBump (0 : ℂ))
    (hout : ∀ z : ℂ, χ.rIn ≤ ‖z‖ → 1 / 4 < ‖sectionValue x z‖) (L : ℂ →L[ℝ] ℝ) (j : ℕ) :
    (D.map fun z ↦ L (z ^ j)).sum = zeroMoment χ L j (sectionValue x) := by
  have hχ1 (z : ℂ) (hz : sectionValue x z = 0) : χ z = 1 := by
    refine χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (not_lt.1 fun hz' ↦ ?_))
    have := hout z hz'.le
    rw [hz, norm_zero] at this
    norm_num at this
  have hfin : {z | sectionValue x z = 0}.Finite :=
    D.toFinset.finite_toSet.subset fun z hz ↦
      Multiset.mem_toFinset.2 (Multiset.count_pos.1 (hD.pos_iff.2 hz))
  have hid := integral_laplacian_mul_log_normSq_of_eq_one (hx 0) (hx 1) (hx 2) (hx 3) hsol hfin
    (isZeroMultiplicity_iff.1 hD) χ.contDiff χ.hasCompactSupport hχ1 (h := fun z ↦ L (z ^ j))
    (contDiff_clm_pow L j)
  simp_rw [← nsmul_eq_mul, Multiset.finsum_count_nsmul_eq_sum_map] at hid
  -- Where `‖z‖ < χ.rIn`, `χ L (zʲ) = L (zʲ)` near `z`, which is harmonic.
  have hΔ0 {z : ℂ} (hz : ‖z‖ < χ.rIn) : Δ (fun y ↦ χ y * L (y ^ j)) z = 0 := by
    have hev : (fun y ↦ χ y * L (y ^ j)) =ᶠ[𝓝 z] fun y ↦ L (y ^ j) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with y hy
      rw [χ.one_of_mem_closedBall (ball_subset_closedBall hy), one_mul]
    rw [(laplacian_congr_nhds hev).self_of_nhds]
    exact ((contDiff_id.pow j).contDiffAt.harmonicAt.comp_CLM L).2.self_of_nhds
  have h₁ : ∫ z, Δ (fun y ↦ χ y * L (y ^ j)) z * Real.log (4 * (x z 2 ^ 2 + x z 3 ^ 2)) =
      ∫ z, Δ (fun y ↦ χ y * L (y ^ j)) z * logNormSqCut (1 / 4) (sectionValue x z) := by
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    dsimp only
    by_cases hz : ‖z‖ < χ.rIn
    · simp only [hΔ0 hz, zero_mul]
    · rw [logNormSqCut_of_le (by norm_num) (hout z (not_lt.1 hz)).le, sq_norm_sectionValue]
  have h₂ : ∫ z, χ z * L (z ^ j) * ((4 * (x z 2 ^ 2 + x z 3 ^ 2) - 1) / 4) =
      ∫ z, (χ z * L (z ^ j)) * ((‖sectionValue x z‖ ^ 2 - 1) / 4) :=
    integral_congr_ae (.of_forall fun z ↦ by simp only [sq_norm_sectionValue])
  rw [zeroMoment, ← h₁, ← h₂, hid]
  field_simp
  ring

/-- The power sums of the zeros of a vortex as moments of its section (`sum_map_eq_zeroMoment`),
with `L` the real and imaginary parts. -/
private theorem sum_map_pow_eq_zeroMoment {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : ∀ i : Fin 4, ContDiff ℝ 2 fun y ↦ x y i) (hsol : ∀ z, equation x z = 0) {D : Multiset ℂ}
    (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z) (χ : ContDiffBump (0 : ℂ))
    (hout : ∀ z : ℂ, χ.rIn ≤ ‖z‖ → 1 / 4 < ‖sectionValue x z‖) (j : ℕ) :
    (D.map (· ^ j)).sum = (zeroMoment χ reCLM j (sectionValue x) : ℂ) +
      (zeroMoment χ imCLM j (sectionValue x) : ℂ) * I := by
  have hre := sum_map_eq_zeroMoment hx hsol hD χ hout reCLM j
  have him := sum_map_eq_zeroMoment hx hsol hD χ hout imCLM j
  simp only [reCLM_apply, imCLM_apply] at hre him
  apply Complex.ext
  · simpa [← hre, Multiset.map_map] using map_multiset_sum reAddGroupHom (D.map (· ^ j))
  · simpa [← him, Multiset.map_map] using map_multiset_sum imAddGroupHom (D.map (· ^ j))

/-- Outside a disc, the section of a continuous field of `A_m^s`, `s > 1`, has norm above `1 / 2`,
since it tends to the winding phase at infinity. -/
private theorem exists_forall_le_norm_lt_norm_sectionValue (hs : 1 < s)
    (x : SobolevFieldSpace f m s) : ∃ R, ∀ z : ℂ, R ≤ ‖z‖ → 1 / 2 < ‖sectionValue x z‖ := by
  have hev := (tendsto_normSq_of_mem_framedFieldSpace hs x.mem_framedFieldSpace
    x.continuous).eventually (lt_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1))
  rw [← Metric.cobounded_eq_cocompact] at hev
  obtain ⟨R, -, hR⟩ := (Metric.hasBasis_cobounded_compl_closedBall (0 : ℂ)).eventually_iff.1 hev
  refine ⟨R + 1, fun z hz ↦ ?_⟩
  have h4 := hR (show z ∈ (closedBall 0 R)ᶜ by
    rw [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le]; linarith)
  rw [← sq_norm_sectionValue] at h4
  nlinarith [norm_nonneg (sectionValue x z)]

/-- **The divisor coefficients are smooth functions of the field near every field.** For `k ≥ 4`
and every continuous field `x₀` of `A_m^k`, there is a map `Φ` on the real coordinates of the
fields, smooth at those of `x₀`, such that the coefficients of the divisor of every vortex `x`
near `x₀` are `Φ` of the real coordinates of `x`.

The power sums of the zeros of the vortices near `x₀` are integrals, over a fixed disc, of smooth
functions of their sections, by the distributional scalar equation
`Δ log |α|² = (|α|² - 1) / 4 + 4π ∑_{z ∈ D} δ_z`, and the sections are affine and continuous in the
real coordinates; the coefficients are the Newton coefficients of the power sums. -/
theorem exists_contDiffAt_coeffEquiv_sobolevVortexDivisor (hk : 3 < k)
    (x₀ : SobolevFieldSpace f m k) :
    ∃ Φ : (Fin 4 → realSubmodule ℂ (Nat.cast_nonneg k : (0 : ℝ) ≤ k)) → Fin m → ℂ,
      ContDiffAt ℝ ∞ Φ (x₀.realSubRef (Nat.cast_nonneg k)) ∧
      ∀ᶠ x : SobolevFieldSpace f m k in 𝓝 x₀, ∀ hx : ∀ z, equation x z = 0,
        Sym.coeffEquiv ℂ m
          (sobolevVortexDivisor ⟨_, toFramedFieldSpace_mem_sobolevVortices hk hx⟩) =
            Φ (x.realSubRef (Nat.cast_nonneg k)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  set h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- The section, as a smooth function of the real coordinates.
  set F : (Fin 4 → realSubmodule ℂ h0) → ℂ →ᵇ ℂ := fun u ↦
    referenceSectionBCF f m + sectionCLM hk1 u
  have hF : ContDiff ℝ ∞ F := contDiff_const.add (sectionCLM hk1).contDiff
  have hFx (x : SobolevFieldSpace f m k) : ⇑(F (x.realSubRef h0)) = sectionValue x :=
    funext (referenceSectionBCF_add_sectionCLM_realSubRef hk1 x)
  -- A cutoff equal to `1` on a disc outside which the section of `x₀` has norm above `1 / 2`.
  obtain ⟨R, hR⟩ := exists_forall_le_norm_lt_norm_sectionValue hk1 x₀
  let χ : ContDiffBump (0 : ℂ) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  set M : (Fin 4 → realSubmodule ℂ h0) → ℕ → ℂ := fun u j ↦
    (zeroMoment χ reCLM j (F u) : ℂ) + (zeroMoment χ imCLM j (F u) : ℂ) * I
  refine ⟨fun u i ↦ (-1) ^ (m - (i : ℕ)) * newtonCoeff (M u) (m - i),
    contDiffAt_pi.2 fun i ↦ contDiffAt_const.mul (contDiffAt_newtonCoeff (fun j ↦ ?_) _), ?_⟩
  · exact ((ofRealCLM.contDiff.comp (contDiff_zeroMoment hF χ reCLM j)).add
      ((ofRealCLM.contDiff.comp (contDiff_zeroMoment hF χ imCLM j)).mul
        contDiff_const)).contDiffAt
  have hcont : ContinuousAt (fun x : SobolevFieldSpace f m k ↦ F (x.realSubRef h0)) x₀ :=
    (hF.continuous.comp (continuous_realSubRef h0)).continuousAt
  filter_upwards [hcont.eventually (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 4))] with x hx hsol
  -- Outside the disc where `χ = 1`, the section of `x` has norm above `1 / 4`.
  have hout (z : ℂ) (hz : χ.rIn ≤ ‖z‖) : 1 / 4 < ‖sectionValue x z‖ := by
    have hd := (BoundedContinuousFunction.dist_coe_le_dist z).trans_lt (mem_ball.1 hx)
    rw [hFx, hFx, dist_eq_norm] at hd
    linarith [hR z (by linarith [le_max_left R 0, show χ.rIn = max R 0 + 1 from rfl]),
      norm_sub_norm_le (sectionValue x₀ z) (sectionValue x z),
      norm_sub_rev (sectionValue x z) (sectionValue x₀ z)]
  have hD := isZeroMultiplicity_sectionValue_sobolevVortexDivisor
    ⟨_, toFramedFieldSpace_mem_sobolevVortices hk hsol⟩
  simp only [coe_toFramedFieldSpace] at hD
  have hpow := sum_map_pow_eq_zeroMoment
    (fun i ↦ (contDiff_piLp 2).1 (x.contDiff (n := 2) (by exact_mod_cast hk)) i) hsol hD χ hout
  funext i
  rw [Sym.coeffEquiv_apply, ← newtonCoeff_sum_map_pow]
  simp only [M, hFx, ← hpow]

/-! ### Smoothness in the coefficients -/

/-- In a chart smooth in the field coordinates, the orbit of the normalized vortex `y_c` is smooth
in `c` at every `c₀` whose orbit lies in the source of the chart. -/
private theorem contDiffAt_chart_mk_normalizedVortex (hm : 0 < m)
    {e : OpenPartialHomeomorph (vortexModuli f m hs) (Fin (2 * m) → ℝ)}
    (he : IsSmoothVortexModuliChart f m hs e) {c₀ : Fin m → ℂ}
    (hc₀ : (⟨Quotient.mk _ (normalizedVortex hm f k c₀),
      mk_mem_vortexModuli (equation_normalizedVortex hm f k c₀)⟩ : vortexModuli f m hs) ∈
        e.source) :
    ContDiffAt ℝ ∞ (fun c ↦ e ⟨Quotient.mk _ (normalizedVortex hm f k c),
      mk_mem_vortexModuli (equation_normalizedVortex hm f k c)⟩) c₀ := by
  set q : (Fin m → ℂ) → vortexModuli f m hs := fun c ↦ ⟨Quotient.mk _ (normalizedVortex hm f k c),
    mk_mem_vortexModuli (equation_normalizedVortex hm f k c)⟩
  obtain ⟨F, hF, hFev⟩ := he.exists_contDiffAt_eventually_eq _
    (equation_normalizedVortex hm f k c₀) hc₀
  have hy := continuous_normalizedVortex hm f (s := k) (Nat.cast_nonneg k)
  -- The real coordinates of `y_c` are smooth in `c`.
  have hu : ContDiff ℝ ∞ fun c ↦ (normalizedVortex hm f k c).realSubRef (Nat.cast_nonneg k) := by
    simp_rw [realSubRef_eq_realPartCLM_subRef]
    exact contDiff_pi.2 fun j ↦ (BesselPotentialSpace.realPartCLM ℂ _).contDiff.comp
      ((contDiff_apply ℝ _ j).comp (contDiff_subRef_normalizedVortex hm f (Nat.cast_nonneg k)))
  have hq : Continuous q := (continuous_quotient_mk'.comp hy).subtype_mk _
  refine (hF.comp c₀ hu.contDiffAt).congr_of_eventuallyEq ?_
  filter_upwards [hy.continuousAt.eventually hFev, hq.continuousAt.eventually
    (e.open_source.mem_nhds hc₀)] with c hc hcs
  exact hc (equation_normalizedVortex hm f k c) hcs

/-- **The vortex orbit is a smooth function of its divisor coefficients.** For `k ≥ 4`, the orbit of
the vortex of `A_m^k` whose divisor has coefficients `c ∈ ℂᵐ`, that is, the inverse of the divisor
homeomorphism read through the elementary symmetric chart `Sym.coeffHomeomorph`, is a smooth map
from `ℂᵐ` into the vortex moduli space with its atlas `vortexModuliChartedSpace`. Collisions of
zeros are included. -/
theorem contMDiff_vortexModuliHomeomorph_symm_coeffHomeomorph_symm (hk : 3 < k) :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    ContMDiff 𝓘(ℝ, Fin m → ℂ) 𝓘(ℝ, Fin (2 * m) → ℝ) ∞
      fun c ↦ (vortexModuliHomeomorph f m hs hk).symm ((Sym.coeffHomeomorph ℂ m).symm c) := by
  let _i := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  obtain rfl | hm := m.eq_zero_or_pos
  · -- `ℂ⁰` is a point, so the map is constant.
    rw [show (fun c ↦ (vortexModuliHomeomorph f 0 hs hk).symm ((Sym.coeffHomeomorph ℂ 0).symm c)) =
      fun _ ↦ (vortexModuliHomeomorph f 0 hs hk).symm ((Sym.coeffHomeomorph ℂ 0).symm 0) from
        funext fun c ↦ by rw [Subsingleton.elim c 0]]
    exact contMDiff_const
  intro c₀
  rw [contMDiffAt_iff_target]
  refine ⟨((vortexModuliHomeomorph f m hs hk).symm.continuous.comp
    (Sym.coeffHomeomorph ℂ m).symm.continuous).continuousAt, ?_⟩
  rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, contMDiffAt_iff_contDiffAt]
  simp_rw [vortexModuliHomeomorph_symm_coeffHomeomorph_symm hm hk]
  exact contDiffAt_chart_mk_normalizedVortex hm (isSmoothVortexModuliChart_chartAt hk _)
    (mem_chart_source _ _)

/-- **The divisor coefficients of a vortex orbit are smooth.** For `k ≥ 4`, the coefficients of the
monic polynomial whose roots are the zero divisor, that is, the divisor homeomorphism read through
the elementary symmetric chart `Sym.coeffHomeomorph`, form a smooth map from the vortex moduli space
with its atlas `vortexModuliChartedSpace` to `ℂᵐ`. Collisions of zeros are included. -/
theorem contMDiff_coeffHomeomorph_vortexModuliHomeomorph (hk : 3 < k) :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    ContMDiff 𝓘(ℝ, Fin (2 * m) → ℝ) 𝓘(ℝ, Fin m → ℂ) ∞
      fun q ↦ Sym.coeffHomeomorph ℂ m (vortexModuliHomeomorph f m hs hk q) := by
  let _i := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  intro q₀
  set e := chartAt (Fin (2 * m) → ℝ) q₀
  have he : IsSmoothVortexModuliChart f m hs e := isSmoothVortexModuliChart_chartAt hk q₀
  rw [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt, modelWithCornersSelf_coe,
    Set.range_id, contDiffWithinAt_univ, extChartAt_coe_symm, extChartAt_coe]
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_id,
    Function.id_comp]
  obtain ⟨σ, hσc, hσ⟩ := he.exists_contDiffOn_lift
  have hv₀ : e q₀ ∈ e.target := e.map_source (mem_chart_source _ q₀)
  have hσd : ContDiffAt ℝ ∞ (fun v ↦ (σ v).realSubRef (Nat.cast_nonneg k)) (e q₀) :=
    hσc.contDiffAt (e.open_target.mem_nhds hv₀)
  -- `σ` is continuous at `e q₀`, being smooth in the real chart of `A_m^k`.
  have hσcont : ContinuousAt σ (e q₀) := by
    have h := (continuous_ofRealSubRef (f := f) (m := m) (by exact_mod_cast (Fact.out : 1 < k))
      (h := Nat.cast_nonneg k)).continuousAt.comp hσd.continuousAt
    simpa only [Function.comp_def, ofRealSubRef_realSubRef] using h
  obtain ⟨Φ, hΦ, hΦev⟩ := exists_contDiffAt_coeffEquiv_sobolevVortexDivisor hk (σ (e q₀))
  refine (hΦ.comp (f := fun v ↦ (σ v).realSubRef (Nat.cast_nonneg k)) _
    hσd).congr_of_eventuallyEq ?_
  filter_upwards [hσcont.eventually hΦev, e.open_target.mem_nhds hv₀] with v hv hvt
  obtain ⟨hσv, hev⟩ := hσ v hvt
  rw [Function.comp_apply, hev, Sym.coeffHomeomorph_apply, vortexModuliHomeomorph_apply,
    vortexModuliDivisor_mk hk hσv]
  exact hv hσv

/-- **The vortex moduli space is diffeomorphic to `ℂᵐ`** (Taubes). For `k ≥ 4`, the zero divisor,
read through the coefficients of the monic polynomial with the given roots, is a diffeomorphism from
the vortex moduli space in `A_m^k / G_(k+1)`, with its atlas `vortexModuliChartedSpace`, onto
`ℂᵐ`, the symmetric product `Sym ℂ m` in its elementary symmetric coordinates; collisions of zeros
are included. -/
def vortexModuliDiffeomorph (hk : 3 < k) :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    Diffeomorph 𝓘(ℝ, Fin (2 * m) → ℝ) 𝓘(ℝ, Fin m → ℂ) (vortexModuli f m hs) (Fin m → ℂ) ∞ :=
  letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
  { toEquiv := ((vortexModuliHomeomorph f m hs hk).trans (Sym.coeffHomeomorph ℂ m)).toEquiv
    contMDiff_toFun := contMDiff_coeffHomeomorph_vortexModuliHomeomorph hk
    contMDiff_invFun := contMDiff_vortexModuliHomeomorph_symm_coeffHomeomorph_symm hk }

/-- The diffeomorphism sends a vortex orbit to the coefficients of its zero divisor. -/
@[simp]
theorem vortexModuliDiffeomorph_apply (hk : 3 < k) (q : vortexModuli f m hs) :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    vortexModuliDiffeomorph hk q = Sym.coeffEquiv ℂ m (vortexModuliDivisor hs hk q) := by
  rw [← vortexModuliHomeomorph_apply, ← Sym.coeffHomeomorph_apply]
  rfl

/-- The inverse of the diffeomorphism sends divisor coefficients `c ∈ ℂᵐ`, `m ≥ 1`, to the orbit of
the normalized vortex `y_c`. -/
theorem vortexModuliDiffeomorph_symm_apply (hm : 0 < m) (hk : 3 < k) (c : Fin m → ℂ) :
    letI := vortexModuliChartedSpace (f := f) (m := m) (hs := hs) hk
    (vortexModuliDiffeomorph (f := f) (hs := hs) hk).symm c =
      ⟨Quotient.mk _ (normalizedVortex hm f k c),
        mk_mem_vortexModuli (equation_normalizedVortex hm f k c)⟩ := by
  rw [← vortexModuliHomeomorph_symm_coeffHomeomorph_symm hm hk]
  rfl

end SobolevFieldSpace

end TauCeti.Vortex
