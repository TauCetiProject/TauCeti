/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Sobolev.Stationary
public import TauCeti.Geometry.Symplectic.Floer.TimeIndependent.Sobolev
public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.ODE.EnergyEstimate.Index
import TauCeti.Analysis.Normed.Operator.MethodOfContinuity
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace
import TauCeti.Geometry.Symplectic.Complex.Module.Exp
import TauCeti.Geometry.Symplectic.Hamiltonian.Basic

/-!
# The cokernel and index of the linearized operator along a time-independent cylinder

Let `(V, ω)` be a finite-dimensional symplectic vector space with a compatible complex structure
`J`, let `H = H_s : V → ℝ` be jointly `C²` Hamiltonians depending on `s ∈ ℝ` alone, such as an
autonomous Hamiltonian or continuation data `K = H_s dt`, and `γ` a continuous curve with
`‖dX_H(γ(s))‖ ≤ a < 2π` for every `s`, where `dX_H(γ(s))` stands for `dX_{H_s}(γ(s))`, and let

`D ξ = ∂s ξ + J (∂t ξ - dX_H(γ(s)) ξ)`

be the Sobolev realization `W^{1,2}(ℝ × S¹, V) → L²(ℝ × S¹, V)` of the linearized Floer operator
of `K = H_s dt` along the time-independent cylinder `(s, t) ↦ γ(s)`
(`TauCeti.SymplecticForm.floerSobolevOperator`). On the zero Fourier mode `D` is the Morse operator
`M ζ = ζ' - J dX_H(γ) ζ` on `W^{1,2}(ℝ, V)` (`TauCeti.WeakDerivStep.trajectoryOperator`), and the
nonzero modes carry no kernel; so `D` and `M` have the same kernel
(`TauCeti.SymplecticForm.ker_floerSobolevOperator_eq_map_zeroModeL`). This file compares their
cokernels, so that `D` and `M` are Fredholm together and have the same index. Only the statement on
the zero mode of the range holds for a general compatible pair `(ω, J)`; the cokernel comparison,
the Fredholm equivalence and the equality of indices are proved in a unitary trivialization, where
`V = F` is a complex inner product space with `ω = Im ⟪·, ·⟫` and `J = i`.

* **The zero mode of the range.** The zero mode of `f ∈ L²(ℝ, V)` lies in the range of `D` exactly
  when `f` lies in the range of `M`
  (`TauCeti.SymplecticForm.zeroModeLp_mem_range_floerSobolevOperator_iff`), because `D` commutes
  with the slice average and maps the zero mode of a path `ζ` to the zero mode of `M ζ`.
* **The nonzero modes lie in the range.** In a unitary trivialization, where `V = F` is a complex
  inner product space with `ω = Im ⟪·, ·⟫` and `J = i`, every section of `L²` whose slice average
  vanishes is `D x` for some `x`
  (`TauCeti.SymplecticForm.ker_sliceAverageLp_le_range_floerSobolevOperator`). This is the method of
  continuity (`ContinuousLinearMap.surjective_iff_of_forall_norm_le_lineMap`) on the nonzero modes,
  along the segment of Hamiltonians `(1 - τ) H + τ Q` from `H` to `Q(y) = (π / 2) ‖y‖²`. Along it
  `‖dX(γ(s))‖` stays at most `max a π < 2π`, so the gap estimate on the nonzero modes
  (`mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero`) holds uniformly.
  At `τ = 1` the operator is `∂s + i ∂t - π`, the stationary cylinder operator over the orbit `0`
  of `Q`, whose return map `exp (-π i) = -1` has no eigenvalue `1`; it is an
  isomorphism `W^{1,2} ≃ L²` (`TauCeti.Floer.bijective_stationarySobolevOperator_ofComplexModule`)
  that commutes with the slice average, so it maps the nonzero modes onto the nonzero modes.
* **The range and the cokernel.** Hence the range of `D` is the zero mode of the range of `M` plus
  the nonzero modes (`TauCeti.SymplecticForm.range_floerSobolevOperator_eq_map_sup_ker`), `D` is
  onto exactly when `M` is
  (`TauCeti.SymplecticForm.surjective_floerSobolevOperator_iff_surjective_trajectoryOperator`), and
  the zero mode induces an isomorphism of cokernels, so that they have the same dimension
  (`finrank_quotient_range_floerSobolevOperator_eq_finrank_quotient_range_trajectoryOperator`).
* **Fredholm property and index.** Together with the comparison of kernels, `D` is Fredholm exactly
  when `M` is
  (`TauCeti.SymplecticForm.isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator`), and
  the two have the same index
  (`TauCeti.SymplecticForm.index_floerSobolevOperator_eq_index_trajectoryOperator`).
* **The index between nondegenerate zeros.** When `H_s` is `H₋` near `s = -∞` and `H₊` near
  `s = +∞`, and `γ` converges at `±∞` to points `p±` where `dX_{H±}` is injective, such as
  nondegenerate critical points of `H±`, the index of the Morse operator is a difference of Morse
  indices (`WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank`),
  and so is that of `D` (`index_floerSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank`,
  in the namespace `TauCeti.SymplecticForm`): it is `dim E⁻(H₋, p₋) - dim E⁻(H₊, p₊)`, where
  `E⁻(G, p)` is the sum of the eigenspaces of `-i dX_G(p)`, the negative of the Hessian of `G` at
  `p`, at negative eigenvalues.

So along a time-independent Floer cylinder of a `C²`-small autonomous Hamiltonian, a gradient line,
in a unitary trivialization (`ω = Im ⟪·, ·⟫`, `J = i`), both the Fredholm index of the linearized
Floer operator and its surjectivity, the regularity of the Floer cylinder, are those of the
gradient line as a Morse trajectory.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221.
* D. Salamon and E. Zehnder, *Morse theory for periodic solutions of Hamiltonian systems and the
  Maslov index*, Comm. Pure Appl. Math. **45** (1992), 1303–1360, on the linearized operator at
  time-independent solutions of a small Hamiltonian.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 5.2, the method of continuity.
-/

public section

noncomputable section

open Real Set Filter Topology MeasureTheory ContinuousLinearMap
open TauCeti.StripSobolev TauCeti.CylinderSobolev
open scoped RealInnerProductSpace ENNReal

namespace TauCeti.SymplecticForm

section ZeroMode

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : ℝ → V → ℝ} {γ : ℝ → V}
  {A : Lp (V →L[ℝ] V) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}

/-- **The zero mode of the range of the linearized operator.** Let `H_s` be jointly `C²`
Hamiltonians depending on `s` and `γ` a continuous curve along which `dX_{H_s}` is bounded, and let
`A` be the `L∞` class of `s ↦ -J dX_{H_s}(γ(s))`. The zero mode of `f ∈ L²(ℝ, V)` lies in the range
of the Sobolev realization of the linearized operator along the time-independent cylinder
`(s, t) ↦ γ(s)` exactly when `f` lies in the range of the Morse operator `ζ ↦ ζ' - J dX_{H_s}(γ) ζ`
on `W^{1,2}(ℝ, V)`. -/
theorem zeroModeLp_mem_range_floerSobolevOperator_iff (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ} (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -(J.toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s))))
    (f : Lp V 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))) :
    zeroModeLp V f ∈ (ω.floerSobolevOperator 2
        (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ H z.1)
        (fun z ↦ γ z.1)).range ↔
      f ∈ (WeakDerivStep.trajectoryOperator (p := 2) A).range := by
  constructor
  · -- If `D x` is a zero mode, it is the image of the zero mode `P x` of `x`, a path `u`.
    rintro ⟨x, hx⟩
    obtain ⟨u, hu⟩ := sliceAverageL_mem_range_zeroModeL x
    refine ⟨u, (zeroModeLp V).injective ?_⟩
    rw [ContinuousLinearMap.coe_coe] at hx ⊢
    rw [← floerSobolevOperator_zeroModeL hH hγ haγ hA, hu, floerSobolevOperator_sliceAverageL, hx,
      sliceAverageLp_zeroModeLp]
  · rintro ⟨u, rfl⟩
    exact ⟨zeroModeL V u, floerSobolevOperator_zeroModeL hH hγ haγ hA u⟩

/-- Along a segment `(1 - τ) H_s + τ G_s` of jointly `C²` Hamiltonians depending on `s`, the Sobolev
realization of the linearized operator along `(s, t) ↦ γ(s)` is affine in `τ`, as long as `dX_{H_s}`
and `dX_{G_s}` are bounded along `γ`. -/
private theorem floerSobolevOperator_lineMap {G : ℝ → V → ℝ}
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hG : ContDiff ℝ 2 (Function.uncurry G))
    (hγ : Continuous γ) {a b : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hbγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (G s)) (γ s)‖ ≤ b) (τ : ℝ) :
    ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun z y ↦ (1 - τ) * H z.1 y + τ * G z.1 y) (fun z ↦ γ z.1) =
      AffineMap.lineMap
        (ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun z ↦ H z.1) (fun z ↦ γ z.1))
        (ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun z ↦ G z.1) (fun z ↦ γ z.1)) τ := by
  have hHτ : ContDiff ℝ 2 (Function.uncurry fun s y ↦ (1 - τ) * H s y + τ * G s y) :=
    (contDiff_const.mul hH).add (contDiff_const.mul hG)
  have hHs (s : ℝ) : ContDiff ℝ 2 (H s) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hGs (s : ℝ) : ContDiff ℝ 2 (G s) := hG.comp (contDiff_const.prodMk contDiff_id)
  set DH := ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
    (fun z ↦ H z.1) (fun z ↦ γ z.1)
  set DG := ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
    (fun z ↦ G z.1) (fun z ↦ γ z.1)
  ext x : 1
  rw [AffineMap.lineMap_apply_module, add_apply, smul_apply, smul_apply]
  refine Lp.ext ?_
  filter_upwards [coeFn_floerSobolevOperator ω (memLp_floerJetCoeff_const_comp_fst hHτ hγ
      fun s ↦ (ω.norm_fderiv_hamiltonianVectorField_const_mul_add_const_mul_le (hHs s) (hGs s) _ _
        _).trans
        (add_le_add (mul_le_mul_of_nonneg_left (haγ s) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hbγ s) (abs_nonneg _)))) x,
    Lp.coeFn_add ((1 - τ) • DH x) (τ • DG x), Lp.coeFn_smul (1 - τ) (DH x), Lp.coeFn_smul τ (DG x),
    coeFn_floerSobolevOperator ω (memLp_floerJetCoeff_const_comp_fst hH hγ haγ) x,
    coeFn_floerSobolevOperator ω (memLp_floerJetCoeff_const_comp_fst hG hγ hbγ) x]
    with z h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₂, Pi.add_apply, h₃, h₄, Pi.smul_apply, Pi.smul_apply, h₅, h₆, floerJetCoeff_const_eq,
    floerJetCoeff_const_eq, floerJetCoeff_const_eq,
    ω.fderiv_hamiltonianVectorField_const_mul_add_const_mul (hHs z.1) (hGs z.1)]
  simp only [firstOrderJetCoeff_apply, comp_add, comp_smul, neg_add_rev, add_apply, neg_apply,
    smul_apply, coe_comp, Function.comp_apply]
  module

/-- An `L²` jet in `W^{1,2}` whose `L²` slice average vanishes has vanishing slice average in
`W^{1,2}`. -/
private theorem sliceAverageL_mk_eq_zero {x : Lp (V × V × V) 2 stripMeasure}
    (hx : x ∈ H1 V ⊓ (sliceAverageLp : Lp (V × V × V) 2 stripMeasure →L[ℝ] _).ker) :
    sliceAverageL (⟨x, hx.1⟩ : H1 V) = 0 :=
  Subtype.ext (by
    rw [coe_sliceAverageL]
    exact hx.2)

/-- On the nonzero modes of `W^{1,2}`, read as `L²` jets with vanishing slice average, the
first-order operator of the coefficient field of the linearized operator along `(s, t) ↦ γ(s)`
takes values with vanishing slice average. -/
private theorem jetOperator_floerJetCoeff_mem_ker_sliceAverageLp (G : ℝ → V → ℝ)
    {x : Lp (V × V × V) 2 stripMeasure}
    (hx : x ∈ H1 V ⊓ (sliceAverageLp : Lp (V × V × V) 2 stripMeasure →L[ℝ] _).ker) :
    jetOperator 2 stripMeasure (ω.floerJetCoeff (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun z ↦ G z.1) (fun z ↦ γ z.1)) x ∈
        (sliceAverageLp : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure).ker := by
  have h := floerSobolevOperator_sliceAverageL ω J G γ ⟨x, hx.1⟩
  rw [sliceAverageL_mk_eq_zero hx, map_zero, floerSobolevOperator_def, comp_apply,
    Submodule.subtypeL_apply] at h
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  exact h.symm

/-- A bijective linearized operator along `(s, t) ↦ γ(s)` maps the nonzero modes onto the nonzero
modes: it commutes with the slice average, so the preimage of a section with vanishing slice
average has vanishing slice average. -/
private theorem surjective_restrict_jetOperator_floerJetCoeff_of_bijective {G : ℝ → V → ℝ}
    (hG : Function.Bijective (ω.floerSobolevOperator 2
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ G z.1)
        (fun z ↦ γ z.1))) :
    Function.Surjective ((jetOperator 2 stripMeasure (ω.floerJetCoeff
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ G z.1)
      (fun z ↦ γ z.1))).restrict
        fun _ hx ↦ jetOperator_floerJetCoeff_mem_ker_sliceAverageLp G hx) := by
  rintro ⟨y, hy⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy
  obtain ⟨x, rfl⟩ := hG.2 y
  have hx : sliceAverageL x = 0 := hG.1 (by rw [floerSobolevOperator_sliceAverageL, hy, map_zero])
  refine ⟨⟨x, x.property, LinearMap.mem_ker.2 ?_⟩, Subtype.ext ?_⟩
  · rw [ContinuousLinearMap.coe_coe, ← coe_sliceAverageL, hx, Submodule.coe_zero]
  · simp only [coe_restrict_apply, floerSobolevOperator_def, comp_apply, Submodule.subtypeL_apply]

end ZeroMode

section Quadratic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V}

/-- **The gap on the nonzero modes, without squares.** Under the hypotheses of
`TauCeti.SymplecticForm.mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero`
with `b < 2π`, an element `x` of `W^{1,2}` whose slice average vanishes satisfies
`‖x‖ ≤ ((2π)² + 1) / (2π - b) ‖D x‖`. -/
private theorem norm_le_mul_norm_floerSobolevOperator_of_sliceAverageL_eq_zero
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {H : ℝ → V → ℝ} {γ : ℝ → V}
    (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {b : ℝ} (hb : b < 2 * π)
    (hbγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ b) {x : H1 V}
    (hx : sliceAverageL x = 0) :
    ‖x‖ ≤ ((2 * π) ^ 2 + 1) / (2 * π - b) * ‖ω.floerSobolevOperator 2
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ H z.1)
      (fun z ↦ γ z.1) x‖ := by
  have hgap := mul_sq_norm_le_mul_sq_norm_floerSobolevOperator_of_sliceAverageL_eq_zero hg hH hγ
    hb.le hbγ hx
  set d := ‖ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1) x‖
  have he : 0 < 2 * π - b := by linarith
  have hK : 1 ≤ (2 * π) ^ 2 + 1 := by nlinarith [sq_nonneg (2 * π)]
  -- `(2π - b)² ‖x‖² ≤ K d² ≤ K² d²`, and both bases are nonnegative.
  have hsq : ((2 * π - b) * ‖x‖) ^ 2 ≤ (((2 * π) ^ 2 + 1) * d) ^ 2 := by
    nlinarith [sq_nonneg d, hK, hgap]
  have hle := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  rw [div_mul_eq_mul_div, le_div_iff₀ he]
  linarith

/-- Along the segment `(1 - τ) H_s + τ Q`, `τ ∈ [0, 1]`, from Hamiltonians `H_s` with
`‖dX_{H_s}(γ(s))‖ ≤ a` to `Q(y) = (π / 2) ‖y‖²`, the linearized vector fields along `γ` have norm
at most `max a π`. -/
private theorem norm_fderiv_hamiltonianVectorField_segment_le (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {H : ℝ → V → ℝ} {γ : ℝ → V} (hH : ContDiff ℝ 2 (Function.uncurry H)) {a : ℝ}
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) (s : ℝ) :
    ‖fderiv ℝ (ω.hamiltonianVectorField fun y ↦ (1 - τ) * H s y + τ * (π / 2 * ‖y‖ ^ 2))
      (γ s)‖ ≤ max a π := by
  have hHs : ContDiff ℝ 2 (H s) := hH.comp (contDiff_const.prodMk contDiff_id)
  refine (ω.norm_fderiv_hamiltonianVectorField_const_mul_add_const_mul_le hHs
    (contDiff_const.mul (contDiff_norm_sq ℝ)) _ _ _).trans ?_
  have hQ : ‖fderiv ℝ (ω.hamiltonianVectorField fun y : V ↦ π / 2 * ‖y‖ ^ 2) (γ s)‖ ≤ π :=
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le hg π (γ s)).trans_eq
      (abs_of_pos pi_pos)
  rw [abs_of_nonneg (sub_nonneg.2 hτ.2), abs_of_nonneg hτ.1]
  nlinarith [le_max_left a π, le_max_right a π, hτ.1, hτ.2,
    mul_le_mul_of_nonneg_left (haγ s) (sub_nonneg.2 hτ.2), mul_le_mul_of_nonneg_left hQ hτ.1]

/-- **The method of continuity on the nonzero modes.** Let the inner product of `V` be the metric
`ω(·, J ·)`, let `H_s` be jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π`. If the linearized operator of the quadratic Hamiltonian
`Q(y) = (π / 2) ‖y‖²` along `(s, t) ↦ γ(s)` is bijective, then every section of `L²` whose slice
average vanishes lies in the range of the linearized operator of `H_s`. Along the segment
`(1 - τ) H + τ Q` the gap estimate on the nonzero modes is uniform, with `max a π` in place of
`a`. -/
private theorem ker_sliceAverageLp_le_range_floerSobolevOperator_of_bijective
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {H : ℝ → V → ℝ} {γ : ℝ → V}
    (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hQ : Function.Bijective (ω.floerSobolevOperator 2
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
      (fun _ ↦ fun y ↦ π / 2 * ‖y‖ ^ 2) (fun z ↦ γ z.1))) :
    (sliceAverageLp : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure).ker ≤
      (ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
        (fun z ↦ H z.1) (fun z ↦ γ z.1)).range := by
  set Q : V → ℝ := fun y ↦ π / 2 * ‖y‖ ^ 2
  have hQ₂ : ContDiff ℝ 2 Q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have hQ₂' : ContDiff ℝ 2 (Function.uncurry fun (_ : ℝ) ↦ Q) := hQ₂.comp contDiff_snd
  have hQγ (s : ℝ) : ‖fderiv ℝ (ω.hamiltonianVectorField Q) (γ s)‖ ≤ π :=
    (norm_fderiv_hamiltonianVectorField_div_two_mul_norm_sq_le hg π (γ s)).trans_eq
      (abs_of_pos pi_pos)
  set b := max a π
  have hb : b < 2 * π := max_lt ha (by linarith [pi_pos])
  -- The nonzero modes of `W^{1,2}`, as `L²` jets, and of `L²`. Every operator of the segment, the
  -- first-order operator of its coefficient field, maps the first to the second.
  set N₁ := H1 V ⊓
    (sliceAverageLp : Lp (V × V × V) 2 stripMeasure →L[ℝ] Lp (V × V × V) 2 stripMeasure).ker
  set N₂ := (sliceAverageLp : Lp V 2 stripMeasure →L[ℝ] Lp V 2 stripMeasure).ker
  have hmaps (G : ℝ → V → ℝ) : ∀ x ∈ N₁, jetOperator 2 stripMeasure (ω.floerJetCoeff
      (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ G z.1)
      (fun z ↦ γ z.1)) x ∈ N₂ := fun _ hx ↦ jetOperator_floerJetCoeff_mem_ker_sliceAverageLp G hx
  have : CompleteSpace N₁ := ((isClosed_jetClosure 2 _).inter
    (isClosed_ker (sliceAverageLp : Lp (V × V × V) 2 stripMeasure →L[ℝ] _))).completeSpace_coe
  set R₀ := (jetOperator 2 stripMeasure (ω.floerJetCoeff
    (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun z ↦ H z.1)
    (fun z ↦ γ z.1))).restrict (hmaps H)
  set R₁ := (jetOperator 2 stripMeasure (ω.floerJetCoeff
    (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0) (fun _ ↦ Q)
    (fun z ↦ γ z.1))).restrict (hmaps fun _ ↦ Q)
  -- The uniform gap estimate on the nonzero modes along the segment.
  have hC : ∀ τ ∈ Icc (0 : ℝ) 1, ∀ x : N₁,
      ‖x‖ ≤ ((2 * π) ^ 2 + 1) / (2 * π - b) * ‖AffineMap.lineMap R₀ R₁ τ x‖ := by
    intro τ hτ x
    have hcoe : ((AffineMap.lineMap R₀ R₁ τ x : N₂) : Lp V 2 stripMeasure) =
        ω.floerSobolevOperator 2 (fun _ _ ↦ J.toLinearMap.toContinuousLinearMap) (fun _ _ ↦ 0)
          (fun z y ↦ (1 - τ) * H z.1 y + τ * Q y) (fun z ↦ γ z.1) ⟨x, x.property.1⟩ := by
      rw [floerSobolevOperator_lineMap hH hQ₂' hγ haγ hQγ τ]
      simp [AffineMap.lineMap_apply_module, R₀, R₁, floerSobolevOperator_def]
    have hn : ‖(⟨x, x.property.1⟩ : H1 V)‖ = ‖x‖ := by
      rw [← Submodule.norm_coe, Submodule.coe_mk, Submodule.norm_coe]
    rw [← Submodule.norm_coe (AffineMap.lineMap R₀ R₁ τ x), hcoe, ← hn]
    exact norm_le_mul_norm_floerSobolevOperator_of_sliceAverageL_eq_zero hg
      (H := fun s y ↦ (1 - τ) * H s y + τ * Q y)
      ((contDiff_const.mul hH).add (contDiff_const.mul hQ₂')) hγ hb
      (norm_fderiv_hamiltonianVectorField_segment_le hg hH haγ hτ)
      (sliceAverageL_mk_eq_zero x.property)
  intro g hg'
  -- At the quadratic end the operator is onto the nonzero modes; transport this along the segment.
  obtain ⟨x, hx⟩ := (surjective_iff_of_forall_norm_le_lineMap hC).2
    (surjective_restrict_jetOperator_floerJetCoeff_of_bijective (G := fun _ ↦ Q) hQ) ⟨g, hg'⟩
  have hx' := congrArg Subtype.val hx
  rw [coe_restrict_apply] at hx'
  refine ⟨⟨x, x.property.1⟩, ?_⟩
  rw [ContinuousLinearMap.coe_coe, floerSobolevOperator_def, comp_apply, Submodule.subtypeL_apply]
  exact hx'

end Quadratic

section Unitary

/-! ### The cokernel in a unitary trivialization -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {ω : SymplecticForm F} {H : ℝ → F → ℝ} {γ : ℝ → F}
  {A : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ))}

/-- **The linearized operator of the quadratic Hamiltonian.** For `Q(y) = (π / 2) ‖y‖²` and any
curve `γ`, the Sobolev realization of the linearized operator along `(s, t) ↦ γ(s)` is the
stationary cylinder operator `∂s + i ∂t - π` over the orbit `0` of `Q`. Its return map is
`exp (-π i) = -1`, so it is an isomorphism `W^{1,2} ≃ L²`. -/
private theorem bijective_floerSobolevOperator_quadratic (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (γ : ℝ → F) :
    Function.Bijective (ω.floerSobolevOperator 2
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun _ ↦ fun y ↦ π / 2 * ‖y‖ ^ 2) (fun z ↦ γ z.1)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  set Jc := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  set B : F →L[ℝ] F := -π • Jc
  have hX := hamiltonianVectorField_div_two_mul_norm_sq (ω.apply_ofComplexModule_eq_inner hω) π
  have hcoeff : ω.floerJetCoeff (fun _ _ ↦ Jc) (fun _ _ ↦ 0)
      (fun _ ↦ fun y ↦ π / 2 * ‖y‖ ^ 2) (fun z ↦ γ z.1) =
      Floer.stationaryJetCoeff (fun _ ↦ AlmostComplexStructure.ofComplexModule F) fun _ ↦ B := by
    funext z
    rw [floerJetCoeff_const_eq, hX, ContinuousLinearMap.fderiv]
    ext v <;> simp [Floer.stationaryJetCoeff_apply, B, Jc, sub_eq_add_neg]
  have hS : ∀ (t : AddCircle (1 : ℝ)) (v w : F),
      (inner ℂ ((ContinuousMap.const _ B : C(AddCircle (1 : ℝ), F →L[ℝ] F)) t v) w).im +
        (inner ℂ v ((ContinuousMap.const _ B : C(AddCircle (1 : ℝ), F →L[ℝ] F)) t w)).im = 0 := by
    intro t v w
    simp [B, Jc, AlmostComplexStructure.ofComplexModule_apply, inner_smul_left, inner_smul_right,
      ← Complex.coe_smul]
  have hdet : LinearMap.det ((1 - dysonSeriesLeft
      (fun t : ℝ ↦ (ContinuousMap.const _ B : C(AddCircle (1 : ℝ), F →L[ℝ] F)) t) 1 :
        F →L[ℝ] F) : F →ₗ[ℝ] F) ≠ 0 := by
    have h2 : (1 - dysonSeriesLeft
        (fun t : ℝ ↦ (ContinuousMap.const _ B : C(AddCircle (1 : ℝ), F →L[ℝ] F)) t) 1 :
          F →L[ℝ] F) = (2 : ℝ) • ContinuousLinearMap.id ℝ F := by
      have hconst : (fun t : ℝ ↦ (ContinuousMap.const _ B : C(AddCircle (1 : ℝ), F →L[ℝ] F)) t) =
          fun _ ↦ B := rfl
      rw [hconst, dysonSeriesLeft_const, one_smul,
        AlmostComplexStructure.exp_neg_pi_smul_ofComplexModule]
      ext v
      simp [two_smul]
    rw [h2, toLinearMap_smul, coe_id, LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ two_ne_zero
  rw [floerSobolevOperator_def, hcoeff, ← Floer.stationarySobolevOperator_def]
  exact Floer.bijective_stationarySobolevOperator_ofComplexModule contDiff_const hS hdet

/-- **The nonzero modes lie in the range of the linearized operator.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`. Then every section of `L²(ℝ × S¹, F)` whose slice average
vanishes is `D x` for some `x`, where `D` is the Sobolev realization of the linearized operator
along `(s, t) ↦ γ(s)` for the complex structure `i`. -/
theorem ker_sliceAverageLp_le_range_floerSobolevOperator (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a) :
    (sliceAverageLp : Lp F 2 stripMeasure →L[ℝ] Lp F 2 stripMeasure).ker ≤
      (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact ker_sliceAverageLp_le_range_floerSobolevOperator_of_bijective
    (ω.apply_ofComplexModule_eq_inner hω) hH hγ ha haγ
    (bijective_floerSobolevOperator_quadratic hω γ)

/-- Under the hypotheses of
`TauCeti.SymplecticForm.ker_sliceAverageLp_le_range_floerSobolevOperator`, a section of `L²` and
its slice average differ by an element of the range of the linearized operator. -/
private theorem sub_sliceAverageLp_mem_range_floerSobolevOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (g : Lp F 2 stripMeasure) :
    g - sliceAverageLp g ∈ (ω.floerSobolevOperator 2
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range := by
  refine ker_sliceAverageLp_le_range_floerSobolevOperator hω hH hγ ha haγ ?_
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sliceAverageLp_sliceAverageLp,
    sub_self]

/-- **The range of the linearized operator.** Let `F` be a finite-dimensional complex inner product
space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s` be jointly `C²` Hamiltonians depending on
`s` and `γ` a continuous curve with `‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the
`L∞` class of `s ↦ -i dX_{H_s}(γ(s))`. The range of the Sobolev realization of the linearized
operator along `(s, t) ↦ γ(s)` consists of the sections whose slice average is the zero mode of an
element of the range of the Morse operator `ζ ↦ ζ' - i dX_{H_s}(γ) ζ`: it is the zero mode of that
range plus the sections whose slice average vanishes. -/
theorem range_floerSobolevOperator_eq_map_sup_ker (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))) :
    (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range =
      (WeakDerivStep.trajectoryOperator (p := 2) A).range.map (zeroModeLp F).toLinearMap ⊔
        (sliceAverageLp : Lp F 2 stripMeasure →L[ℝ] Lp F 2 stripMeasure).ker := by
  refine le_antisymm (fun g hg ↦ ?_) (sup_le ?_ (ker_sliceAverageLp_le_range_floerSobolevOperator
    hω hH hγ ha haγ))
  · -- The slice average of `g = D x` is `D (P x)`, the zero mode of an element of the range of `M`.
    obtain ⟨f, hf⟩ := sliceAverageLp_mem_range_zeroModeLp g
    have hPg : zeroModeLp F f ∈ (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range := by
      obtain ⟨x, rfl⟩ := hg
      refine ⟨sliceAverageL x, ?_⟩
      rw [ContinuousLinearMap.coe_coe, floerSobolevOperator_sliceAverageL, hf,
        ContinuousLinearMap.coe_coe]
    rw [← sub_add_cancel g (sliceAverageLp g), add_comm, ← hf]
    refine Submodule.add_mem_sup ⟨f, (zeroModeLp_mem_range_floerSobolevOperator_iff hH hγ haγ hA
      f).1 hPg, rfl⟩ ?_
    rw [hf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, sliceAverageLp_sliceAverageLp,
      sub_self]
  · rintro _ ⟨f, hf, rfl⟩
    exact (zeroModeLp_mem_range_floerSobolevOperator_iff hH hγ haγ hA f).2 hf

/-- **Surjectivity of the linearized operator is that of the Morse operator.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the `L∞` class of `s ↦ -i dX_{H_s}(γ(s))`.
The Sobolev realization of the linearized operator along `(s, t) ↦ γ(s)` maps `W^{1,2}(ℝ × S¹, F)`
onto `L²(ℝ × S¹, F)` exactly when the Morse operator `ζ ↦ ζ' - i dX_{H_s}(γ) ζ` maps `W^{1,2}(ℝ, F)`
onto `L²(ℝ, F)`. -/
theorem surjective_floerSobolevOperator_iff_surjective_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))) :
    Function.Surjective (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)) ↔
      Function.Surjective (WeakDerivStep.trajectoryOperator (p := 2) A) := by
  constructor
  · intro hD f
    obtain ⟨x, hx⟩ := hD (zeroModeLp F f)
    obtain ⟨u, hu⟩ := (zeroModeLp_mem_range_floerSobolevOperator_iff hH hγ haγ hA f).1 ⟨x, hx⟩
    exact ⟨u, hu⟩
  · intro hM g
    obtain ⟨f, hf⟩ := sliceAverageLp_mem_range_zeroModeLp g
    obtain ⟨u, hu⟩ := hM f
    obtain ⟨x, hx⟩ := sub_sliceAverageLp_mem_range_floerSobolevOperator hω hH hγ ha haγ g
    refine ⟨x + zeroModeL F u, ?_⟩
    rw [map_add, ← ContinuousLinearMap.coe_coe, hx, ContinuousLinearMap.coe_coe,
      floerSobolevOperator_zeroModeL hH hγ haγ hA, hu, hf, sub_add_cancel]

/-- The zero mode induces an isomorphism from the cokernel of the Morse operator onto that of the
linearized operator. -/
private theorem nonempty_linearEquiv_quotient_range (hω : ∀ v w, ω v w = (inner ℂ v w).im)
    (hH : ContDiff ℝ 2 (Function.uncurry H)) (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))) :
    Nonempty ((Lp F 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) ⧸
        (WeakDerivStep.trajectoryOperator (p := 2) A).range) ≃ₗ[ℝ]
      (Lp F 2 stripMeasure ⧸ (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range)) := by
  set φ := (ω.floerSobolevOperator 2
    (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
    (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range.mkQ ∘ₗ (zeroModeLp F).toLinearMap
  have hker : LinearMap.ker φ = (WeakDerivStep.trajectoryOperator (p := 2) A).range := by
    ext f
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact zeroModeLp_mem_range_floerSobolevOperator_iff hH hγ haγ hA f
  -- Every class has a representative in the zero mode, its slice average.
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨f, hf⟩ := sliceAverageLp_mem_range_zeroModeLp g
    refine ⟨f, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, LinearIsometry.coe_toLinearMap, hf,
      Submodule.Quotient.eq, ← neg_mem_iff, neg_sub]
    exact sub_sliceAverageLp_mem_range_floerSobolevOperator hω hH hγ ha haγ g
  exact ⟨(Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)⟩

/-- **The cokernels of the linearized operator and of the Morse operator have the same dimension.**
Let `F` be a finite-dimensional complex inner product space whose symplectic form `ω` is
`Im ⟪·, ·⟫`, let `H_s` be jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the `L∞` class of `s ↦ -i dX_{H_s}(γ(s))`.
The cokernel of the Sobolev realization of the linearized operator along `(s, t) ↦ γ(s)` and that of
the Morse operator `ζ ↦ ζ' - i dX_{H_s}(γ) ζ` have the same dimension: the zero mode induces an
isomorphism between them. -/
theorem finrank_quotient_range_floerSobolevOperator_eq_finrank_quotient_range_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))) :
    Module.finrank ℝ (Lp F 2 stripMeasure ⧸ (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).range) =
      Module.finrank ℝ (Lp F 2 (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) ⧸
        (WeakDerivStep.trajectoryOperator (p := 2) A).range) :=
  (nonempty_linearEquiv_quotient_range hω hH hγ ha haγ hA).some.finrank_eq.symm

/-- **The linearized operator is Fredholm exactly when the Morse operator is.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the `L∞` class of `s ↦ -i dX_{H_s}(γ(s))`.
The Sobolev realization `W^{1,2}(ℝ × S¹, F) → L²(ℝ × S¹, F)` of the linearized operator along
`(s, t) ↦ γ(s)` is Fredholm exactly when the Morse operator `ζ ↦ ζ' - i dX_{H_s}(γ) ζ` on
`W^{1,2}(ℝ, F)` is. -/
theorem isFredholm_floerSobolevOperator_iff_isFredholm_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))) :
    (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).IsFredholm ↔
      (WeakDerivStep.trajectoryOperator (p := 2) A).IsFredholm := by
  obtain ⟨e⟩ := nonempty_linearEquiv_quotient_range hω hH hγ ha haγ hA
  -- The zero mode identifies the kernels.
  have hker : (ω.floerSobolevOperator 2
      (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
      (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).ker =
        (WeakDerivStep.trajectoryOperator (p := 2) A).ker.map (zeroModeL F).toLinearMap := by
    let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
    exact ker_floerSobolevOperator_eq_map_zeroModeL (ω.apply_ofComplexModule_eq_inner hω) hH hγ ha
      haγ hA
  have ek := (Submodule.equivMapOfInjective _ zeroModeL_injective _).trans
    (LinearEquiv.ofEq _ _ hker.symm)
  rw [isFredholm_iff_finite_ker_coker, isFredholm_iff_finite_ker_coker]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨Module.Finite.equiv ek.symm, Module.Finite.equiv e.symm⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Module.Finite.equiv ek, Module.Finite.equiv e⟩

/-- **The index of the linearized operator is that of the Morse operator.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s` and `γ` a continuous curve with
`‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`, and let `A` be the `L∞` class of `s ↦ -i dX_{H_s}(γ(s))`.
The Sobolev realization of the linearized operator along `(s, t) ↦ γ(s)` and the Morse operator
`ζ ↦ ζ' - i dX_{H_s}(γ) ζ` have the same index. -/
theorem index_floerSobolevOperator_eq_index_trajectoryOperator
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ}
    (ha : a < 2 * π) (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a)
    (hA : ⇑A =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)]
      fun s ↦ -((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
        (fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)))) :
    (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).index =
      (WeakDerivStep.trajectoryOperator (p := 2) A).index := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  rw [index_eq_finrank_sub, index_eq_finrank_sub,
    finrank_ker_floerSobolevOperator_eq_finrank_ker_trajectoryOperator
      (ω.apply_ofComplexModule_eq_inner hω) hH hγ ha haγ hA,
    finrank_quotient_range_floerSobolevOperator_eq_finrank_quotient_range_trajectoryOperator hω hH
      hγ ha haγ hA]

/-- **The index along a time-independent cylinder between nondegenerate zeros.** Let `F` be a
finite-dimensional complex inner product space whose symplectic form `ω` is `Im ⟪·, ·⟫`, let `H_s`
be jointly `C²` Hamiltonians depending on `s`, equal to `H₋` for `s` near `-∞` and to `H₊` for `s`
near `+∞`, and let `γ` be a continuous curve with `‖dX_{H_s}(γ(s))‖ ≤ a < 2π` for every `s`,
converging to `p₋` at `-∞` and to `p₊` at `+∞`, where `dX_{H₋}(p₋)` and `dX_{H₊}(p₊)` are
injective. Then the Sobolev realization of the linearized operator of `K = H_s dt` along
`(s, t) ↦ γ(s)` has index `dim E⁻(H₋, p₋) - dim E⁻(H₊, p₊)`, where `E⁻(G, p)` is the sum of the
eigenspaces at negative eigenvalues of `-i dX_G(p)`, the negative of the Hessian of `G` at `p` for
the metric `Re ⟪·, ·⟫`. For an autonomous Hamiltonian, `H₋ = H₊ = H`, the cylinder is a gradient
line of `H` when `γ' = ∇H(γ)`, but `γ` need not be one. -/
theorem index_floerSobolevOperator_eq_finrank_pointSpectralSubspace_sub_finrank
    (hω : ∀ v w, ω v w = (inner ℂ v w).im) (hH : ContDiff ℝ 2 (Function.uncurry H))
    (hγ : Continuous γ) {a : ℝ} (ha : a < 2 * π)
    (haγ : ∀ s, ‖fderiv ℝ (ω.hamiltonianVectorField (H s)) (γ s)‖ ≤ a) {Hm Hp : F → ℝ}
    (hHm : ∀ᶠ s in atBot, H s = Hm) (hHp : ∀ᶠ s in atTop, H s = Hp)
    {pminus pplus : F} (hbot : Tendsto γ atBot (𝓝 pminus)) (htop : Tendsto γ atTop (𝓝 pplus))
    (hpminus : Function.Injective (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus))
    (hpplus : Function.Injective (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) :
    (ω.floerSobolevOperator 2
        (fun _ _ ↦ (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap)
        (fun _ _ ↦ 0) (fun z ↦ H z.1) (fun z ↦ γ z.1)).index =
      (Module.finrank ℝ (Module.End.pointSpectralSubspace
        ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
          (fderiv ℝ (ω.hamiltonianVectorField Hm) pminus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) (Iio 0)) :
            ℤ) -
        Module.finrank ℝ (Module.End.pointSpectralSubspace
          ((-((AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap.comp
            (fderiv ℝ (ω.hamiltonianVectorField Hp) pplus)) : F →L[ℝ] F) : F →ₗ[ℝ] F) (Iio 0)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  have hg := ω.apply_ofComplexModule_eq_inner hω
  set Jc := (AlmostComplexStructure.ofComplexModule F).toLinearMap.toContinuousLinearMap
  -- The coefficient `B_G(y) = -i dX_G(y)` of a `C²` Hamiltonian `G`, continuous in `y`.
  set B : (F → ℝ) → F → F →L[ℝ] F := fun G y ↦ -(Jc.comp (fderiv ℝ (ω.hamiltonianVectorField G) y))
  have hBc {G : F → ℝ} (hG : ContDiff ℝ 2 G) : Continuous (B G) := (continuous_const.clm_comp
    ((ω.contDiff_hamiltonianVectorField (n := 1) hG).continuous_fderiv one_ne_zero)).neg
  -- The end Hamiltonians are members of the family, hence `C²`.
  have hend {G : F → ℝ} {l : Filter ℝ} [l.NeBot] (hl : ∀ᶠ s in l, H s = G) : ContDiff ℝ 2 G := by
    obtain ⟨s, hs⟩ := hl.exists
    exact hs ▸ hH.comp (contDiff_const.prodMk contDiff_id)
  -- The coefficient `s ↦ -i dX_{H_s}(γ(s))` of the Morse operator, continuous and bounded.
  have hSc : Continuous fun s ↦ B (H s) (γ s) :=
    (continuous_const.clm_comp (ω.continuous_fderiv_hamiltonianVectorField_comp hH hγ)).neg
  have hAL : MemLp (fun s ↦ B (H s) (γ s)) ∞
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝ) : Set ℝ)) :=
    memLp_top_of_bound hSc.aestronglyMeasurable (‖Jc‖ * a) (.of_forall fun s ↦ by
      rw [norm_neg]
      exact (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (haγ s) (norm_nonneg _)))
  rw [index_floerSobolevOperator_eq_index_trajectoryOperator hω hH hγ ha haγ hAL.coeFn_toLp]
  -- `B_G(p)` is the negative of the Hessian, symmetric for the real inner product.
  have hsym {G : F → ℝ} (hG : ContDiff ℝ 2 G) (p : F) :
      ((B G p : F →L[ℝ] F) : F →ₗ[ℝ] F).IsSymmetric := fun u v ↦ by
    have h := (ω.invariant_of_apply_apply_eq_inner
      hg).associatedBilinForm_apply_fderiv_hamiltonianVectorField_comm (hG.contDiffAt (x := p)) u v
    rw [associatedBilinForm_apply, associatedBilinForm_apply, hg, hg] at h
    simpa [B, Jc, inner_neg_left, inner_neg_right] using h
  -- At the limits, `B_{H±}(p±)` is injective, hence bounded below.
  have hbound (G : F → ℝ) (p : F)
      (hp : Function.Injective (fderiv ℝ (ω.hamiltonianVectorField G) p)) :
      ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖B G p v‖ := by
    have hinj : Function.Injective ((B G p : F →L[ℝ] F) : F →ₗ[ℝ] F) := fun u v huv ↦ by
      refine hp ((AlmostComplexStructure.ofComplexModule F).injective (neg_injective ?_))
      simpa [B, Jc] using huv
    obtain ⟨K, -, hK⟩ := ((B G p : F →L[ℝ] F) : F →ₗ[ℝ] F).exists_antilipschitzWith
      (LinearMap.ker_eq_bot.2 hinj)
    exact antilipschitzWith_iff_exists_mul_le_norm.1 ⟨K, hK⟩
  obtain ⟨cm, hcm, hm⟩ := hbound Hm pminus hpminus
  obtain ⟨cp, hcp, hp⟩ := hbound Hp pplus hpplus
  -- Near the ends the coefficient is that of the end Hamiltonian along `γ`.
  have hlim {G : F → ℝ} (hG : ContDiff ℝ 2 G) {l : Filter ℝ} {p : F} (hl : ∀ᶠ s in l, H s = G)
      (hγl : Tendsto γ l (𝓝 p)) : Tendsto (fun s ↦ B (H s) (γ s)) l (𝓝 (B G p)) :=
    ((hBc hG).tendsto p |>.comp hγl).congr'
      (hl.mono fun s hs ↦ by simp only [Function.comp_apply, hs])
  exact WeakDerivStep.index_trajectoryOperator_eq_finrank_pointSpectralSubspace_sub_finrank
    hSc (hsym (hend hHm) pminus) (hsym (hend hHp) pplus) (lt_min hcm hcp)
    (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hm v))
    (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (hp v))
    (hlim (hend hHm) hHm hbot) (hlim (hend hHp) hHp htop) _ hAL.coeFn_toLp

end Unitary

end TauCeti.SymplecticForm
