/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Cylinder
public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Eigenbasis
public import TauCeti.Geometry.Symplectic.Floer.AsymptoticOperator
public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
import TauCeti.Analysis.Distribution.DuBoisReymond
import TauCeti.Analysis.ODE.Regularity
import TauCeti.Analysis.Sobolev.Cylinder.Slice.Basic

/-!
# The stationary cylinder operator at a nondegenerate orbit has dense range

Let `F` be a finite-dimensional complex inner product space, such as `ℂⁿ`, with its standard
complex structure `J₀ = i`, and let `S` be a loop of real-linear maps of `F` of period one, of
class `C¹`, infinitesimally symplectic for `ω₀ = Im ⟪·, ·⟫` and nondegenerate: the linear equation
`ζ' = S_t ζ` has no nonzero periodic solution. The stationary cylinder operator

`D ξ = ∂s ξ + J₀ (∂t ξ - S_t ξ)`

(`TauCeti.Floer.stationaryCylinderOperator` for the constant structure
`AlmostComplexStructure.ofComplexModule F`) is the linearized Floer operator along the stationary
cylinder over a nondegenerate orbit, written in a unitary trivialization. This file proves that
its image is dense in `L²` of the cylinder: a square integrable section `η` with
`∫ Re ⟪D ξ, η⟫ = 0` for every test section `ξ` vanishes almost everywhere
(`TauCeti.Floer.ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero`).
Together with the a priori estimate of `TauCeti.Geometry.Symplectic.Floer.SpectralGap`, which makes
`D` injective with closed range on the Sobolev completion, this is the surjectivity half of the
invertibility of `D`, the invertible block of a stationary cylinder.

The proof uses the eigenbasis of the asymptotic operator `A = J₀ (d/dt - S_t)`
(`TauCeti.CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul`): a Hilbert basis of
`H⁰ = L²(S¹, F)` of eigenfunctions `e` with real eigenvalues `λ ≠ 0`. It does not use any
regularity theory for weak solutions of the adjoint equation.

* **Eigenmodes.** An eigenfunction solves `e' = S_t e - λ J₀ e`, so it is of class `C²` when `S`
  is `C¹`. On the product section `φ(s) e(t)`, `D` acts as the scalar operator
  `(φ' + λ φ) e`.
* **The weak equation of a mode.** Testing against these sections shows that the slice pairing
  `A(s) = ∫₀¹ Re ⟪e, η(s, ·)⟫` is a distributional solution of `A' = λ A`, so `A = c e^{λ s}` on
  every bounded interval, by the du Bois-Reymond lemma
  (`LocallyIntegrableOn.exists_ae_eq_exp_smul_Ioo_of_integral_deriv_add_mul_smul_eq_zero`, in the
  namespace `MeasureTheory`).
  The integrals of `|A|` over unit intervals are bounded by `‖e‖² + ‖η‖²_{L²}`, while those of
  `e^{λ s}` are not, so `c = 0`.
* **All loops.** For a test function `φ`, the functional `ψ ↦ ∫ φ(s) ∫₀¹ Re ⟪ψ, η(s, ·)⟫` on
  continuous loops is bounded by `‖φ‖_{L²} ‖η‖_{L²} ‖ψ‖_{H⁰}`, by Cauchy–Schwarz on the strip and
  Parseval's identity, and vanishes on the eigenfunctions, which span a dense subspace of `H⁰`.
  So the slice pairing of `η` with every continuous loop vanishes almost everywhere
  (`TauCeti.CylinderSobolev.slice_re_inner_ae_eq_zero_of_hilbertBasis`).
* **Slices.** By separability of the space of loops, for almost every `s` the slice pairing
  vanishes for all loops at once; testing against loops `g(t) v` with `g` supported in `(0, 1)`
  shows that the slice `η(s, ·)` vanishes, and Fubini's theorem gives `η = 0`
  (`TauCeti.CylinderSobolev.ae_eq_zero_of_forall_slice_re_inner_ae_eq_zero`).

## Main results

* `TauCeti.Floer.ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero`: a
  square integrable section orthogonal to the image of the test sections under the stationary
  cylinder operator at a nondegenerate orbit vanishes.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2 (the invertibility of `∂s + A` at a nondegenerate orbit via the
  spectral decomposition of `A`).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995), 1–33.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff

namespace TauCeti.Floer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open CylinderSobolev
open StripSobolev (stripMeasure)

omit [FiniteDimensional ℂ F] in
/-- **The slice pairing with an eigenmode vanishes.** If `e` solves `e' = S_t e - λ J₀ e` with
`λ ≠ 0` and `η` is orthogonal to the image of the test sections under `D`, then the slice pairing
`A(s) = ∫₀¹ Re ⟪e, η(s, ·)⟫` vanishes almost everywhere: on product sections `φ(s) e(t)` the
orthogonality says that `A` solves `A' = λ A` weakly, and `A` has uniformly bounded integrals
over unit intervals. -/
private theorem slice_re_inner_ae_eq_zero_of_hasDerivAt {S : ℝ → F →L[ℝ] F}
    (hS₁ : ContDiff ℝ 1 S) {e : C(AddCircle (1 : ℝ), F)} {lam : ℝ} (hlam : lam ≠ 0)
    (he : ∀ y : ℝ, HasDerivAt (fun y : ℝ ↦ e y) (S y (e y) - lam • I • e y) y)
    {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    (h : ∀ ξ ∈ testSection F, ∫ z, (inner ℂ (stationaryCylinderOperator
      (fun _ ↦ AlmostComplexStructure.ofComplexModule F) S ξ z) (η z)).re ∂stripMeasure = 0) :
    (fun s ↦ ∫ t in Icc (0 : ℝ) 1, (inner ℂ (e t) (η (s, t))).re) =ᵐ[volume] 0 := by
  -- `e` solves `e' = S_t e - λ J₀ e` for `J₀ = ofComplexModule F`, so it is of class `C²`.
  have heJ (y : ℝ) : HasDerivAt (fun y : ℝ ↦ e y)
      (S y (e y) - lam • AlmostComplexStructure.ofComplexModule F (e y)) y := by
    simpa only [AlmostComplexStructure.ofComplexModule_apply] using he y
  have he2 : ContDiff ℝ 2 fun t : ℝ ↦ e t :=
    contDiff_succ_of_hasDerivAt_clm_apply (n := 1)
      (A := fun y ↦ S y - lam • (I • ContinuousLinearMap.id ℝ F)) (hS₁.sub contDiff_const)
      fun y ↦ by simpa using he y
  have hbd (t : ℝ) : ‖e t‖ ≤ ‖e‖ := e.norm_coe_le_norm _
  have he' : Continuous fun t : ℝ ↦ e t := e.continuous.comp (AddCircle.continuous_mk' 1)
  refine (locallyIntegrable_slice_re_inner hη e).ae_eq_zero_of_integral_deriv_add_mul_smul_eq_zero
    hlam (M := (‖e‖ ^ 2 + ∫ z, ‖η z‖ ^ 2 ∂stripMeasure) / 2)
    (fun n ↦ by
      simpa [Real.norm_eq_abs] using integral_abs_slice_re_inner_le hη he' hbd
        (a := n) (b := n + 1) (by linarith))
    fun φ hφ hφc ↦ ?_
  -- Test the orthogonality against the product section `φ(s) e(t)`.
  obtain ⟨R, -, hR⟩ := hφc.exists_pos_le_norm
  have hξ : (fun z : ℝ × ℝ ↦ φ z.1 • e z.2) ∈ testSection F := by
    refine mem_testSection_iff.2 ⟨((hφ.of_le (by simp)).comp contDiff_fst).smul
      (he2.comp contDiff_snd), fun s t ↦ ?_, R,
      fun s t hs ↦ ?_⟩
    · simp only [AddCircle.coe_add_period]
    · simp [hR s (by rwa [Real.norm_eq_abs])]
  have h0 := h _ hξ
  simp_rw [stationaryCylinderOperator_smul_of_hasDerivAt heJ (hφ.differentiable (by simp))] at h0
  simp_rw [smul_eq_mul]
  rw [← integral_re_inner_smul_eq_integral_mul_slice hη (φ := fun s ↦ deriv φ s + lam * φ s)
    ((hφ.continuous_deriv (by simp)).add (continuous_const.mul hφ.continuous))
    (hφc.deriv.add (hφc.smul_left (f := fun _ ↦ lam))) he']
  exact h0

/-- **The stationary cylinder operator at a nondegenerate orbit has dense range.** Let `S` be a
loop of real-linear maps of `F`, of class `C¹` and infinitesimally symplectic for
`ω₀ = Im ⟪·, ·⟫`, such that `ζ' = S_t ζ` has no nonzero periodic solution. If a square integrable
section `η` of the cylinder is `L²`-orthogonal to `D ξ = ∂s ξ + J₀ (∂t ξ - S_t ξ)` for every test
section `ξ`, where `J₀ = i`, then `η = 0` almost everywhere. -/
theorem ae_eq_zero_of_forall_integral_re_inner_stationaryCylinderOperator_eq_zero
    {S : C(AddCircle (1 : ℝ), F →L[ℝ] F)} (hS₁ : ContDiff ℝ 1 fun t : ℝ ↦ S t)
    (hS : ∀ t v w, (inner ℂ (S t v) w).im + (inner ℂ v (S t w)).im = 0)
    (hnd : ∀ ζ : C(AddCircle (1 : ℝ), F),
      (∀ x : ℝ, HasDerivAt (fun y : ℝ ↦ ζ y) (S x (ζ x)) x) → ζ = 0)
    {η : ℝ × ℝ → F} (hη : MemLp η 2 stripMeasure)
    (h : ∀ ξ ∈ testSection F, ∫ z, (inner ℂ (stationaryCylinderOperator
      (fun _ ↦ AlmostComplexStructure.ofComplexModule F) (fun t ↦ S t) ξ z) (η z)).re
        ∂stripMeasure = 0) :
    η =ᵐ[stripMeasure] 0 := by
  -- The eigenbasis `e i` of the asymptotic operator, with eigenvalues `λ i ≠ 0`.
  obtain ⟨ι, b, a, lam, c, hc, hab⟩ :=
    CircleSobolev.exists_hilbertBasis_I_smul_loopOperator_eq_smul 1 S hS
      ((CircleSobolev.isInvertible_loopOperator_iff 1 S).2 hnd)
  set e : ι → C(AddCircle (1 : ℝ), F) :=
    fun i ↦ CircleSobolev.toContinuousMap 1 (by norm_num) (a i)
  have hb (i : ι) : b i = CircleSobolev.ofContinuousMap 1 (e i) := by
    rw [← (hab i).1, CircleSobolev.ofContinuousMap_toContinuousMap]
  refine ae_eq_zero_of_forall_slice_re_inner_ae_eq_zero hη
    (slice_re_inner_ae_eq_zero_of_hilbertBasis hη b e hb fun i ↦ ?_)
  refine slice_re_inner_ae_eq_zero_of_hasDerivAt hS₁ (fun h0 ↦ ?_)
    ((CircleSobolev.I_smul_loopOperator_eq_smul_iff 1 S (a i) (lam i)).1
      (by rw [(hab i).2.2, (hab i).1])) hη h
  have := (hab i).2.1
  rw [h0, abs_zero] at this
  linarith

end TauCeti.Floer
