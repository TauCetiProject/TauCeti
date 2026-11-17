/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Instances.Int

/-!
# Derivatives of matrix-vector products

For a matrix field `A`, a vector field `v`, and specified coordinate directions `e i`,
the sum of the directional derivatives of the components of `A *ᵥ v` is the trace contraction
of `A` with the directional Jacobian of `v`, plus the column-divergence term of `A` applied to
`v`. In particular, the latter term vanishes when every column has zero directional divergence.

The field and the directions may be defined on any normed vector space over a nontrivially
normed field. Neither completeness nor independence of the directions is required.

For a constant matrix `M`, a map that agrees near `x` with `M *ᵥ f + b` has derivative `M f'(x)`
at `x` (`HasFDerivAt.of_eventuallyEq_mulVec_add`). Conversely, if the derivatives of two `C¹`
maps `A` and `A'` on an open preconnected set differ at each point by an integer matrix, and the
derivative of `A` is injective, then `A' = M A + b` for a constant integer matrix `M`
(`TauCeti.exists_eq_mulVec_add_of_forall_exists_fderiv_eq`).
-/

public section

namespace Matrix

variable {ι E 𝕜 : Type*} [Fintype ι] [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The componentwise divergence product rule for a matrix field times a vector field. -/
theorem sum_fderiv_mulVec_eq_trace_add
    (A : E → Matrix ι ι 𝕜) (v : E → ι → 𝕜) (e : ι → E) (x : E)
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y ↦ A y i j) x)
    (hv : ∀ j, DifferentiableAt 𝕜 (fun y ↦ v y j) x) :
    ∑ i, fderiv 𝕜 (fun y ↦ (A y *ᵥ v y) i) x (e i) =
      (A x * Matrix.of (fun j i ↦ fderiv 𝕜 (fun y ↦ v y j) x (e i))).trace +
        ∑ j, v x j * (∑ i, fderiv 𝕜 (fun y ↦ A y i j) x (e i)) := by
  have hdc (i : ι) : fderiv 𝕜 (fun y ↦ (A y *ᵥ v y) i) x (e i) =
      ∑ j, (A x i j * fderiv 𝕜 (fun y ↦ v y j) x (e i) +
        v x j * fderiv 𝕜 (fun y ↦ A y i j) x (e i)) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y ↦ A y i j * v y j)
      (fun j _ ↦ (hA i j).mul (hv j))]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hv j)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  simp_rw [hdc, Finset.sum_add_distrib]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.of_apply]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- If every column of a matrix field has zero directional divergence, the divergence of its
flux is the trace contraction with the directional Jacobian of the vector field. -/
theorem sum_fderiv_mulVec_eq_trace_of_sum_fderiv_eq_zero
    (A : E → Matrix ι ι 𝕜) (v : E → ι → 𝕜) (e : ι → E) (x : E)
    (hA : ∀ i j, DifferentiableAt 𝕜 (fun y ↦ A y i j) x)
    (hv : ∀ j, DifferentiableAt 𝕜 (fun y ↦ v y j) x)
    (hdiv : ∀ j, ∑ i, fderiv 𝕜 (fun y ↦ A y i j) x (e i) = 0) :
    ∑ i, fderiv 𝕜 (fun y ↦ (A y *ᵥ v y) i) x (e i) =
      (A x * Matrix.of (fun j i ↦ fderiv 𝕜 (fun y ↦ v y j) x (e i))).trace := by
  rw [sum_fderiv_mulVec_eq_trace_add A v e x hA hv]
  simp only [hdiv, mul_zero, Finset.sum_const_zero, add_zero]

end Matrix

open Matrix Topology in
/-- If `g = M *ᵥ f + b` near `x` for a constant matrix `M` and a constant vector `b`, and `f` has
derivative `f'` at `x`, then `g` has derivative `M f'` at `x`. -/
theorem HasFDerivAt.of_eventuallyEq_mulVec_add {ι κ E 𝕜 : Type*} [Fintype ι] [DecidableEq ι]
    [Finite κ] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    {f : E → ι → 𝕜} {g : E → κ → 𝕜} {f' : E →L[𝕜] ι → 𝕜} {M : Matrix κ ι 𝕜} {b : κ → 𝕜}
    {x : E} (hf : HasFDerivAt f f' x) (h : ∀ᶠ y in 𝓝 x, g y = M *ᵥ f y + b) :
    HasFDerivAt g ((Matrix.toLin' M).toContinuousLinearMap.comp f') x := by
  have := Fintype.ofFinite κ
  refine (((Matrix.toLin' M).toContinuousLinearMap.hasFDerivAt.comp x hf).add_const
    b).congr_of_eventuallyEq ?_
  filter_upwards [h] with y hy
  simp [hy]

namespace TauCeti

open Set Function Matrix

variable {ι : Type*} [Fintype ι] {D : Set (ι → ℝ)} {A A' : (ι → ℝ) → ι → ℝ}

/-- **Derivatives related by integer matrices force an integral affine relation.** Let `A` and `A'`
be `C¹` maps on an open preconnected set `D`, with the derivative of `A` injective on `D`. If at
each point `c ∈ D` the derivative of `A'` is `M_c` times that of `A` for some integer matrix `M_c`,
then `M_c` does not depend on `c`, and `A' = M A + b` on `D` for some constant `b`. -/
theorem exists_eq_mulVec_add_of_forall_exists_fderiv_eq (hDo : IsOpen D) (hD : IsPreconnected D)
    (hA : ContDiffOn ℝ 1 A D) (hA' : ContDiffOn ℝ 1 A' D)
    (hinj : ∀ c ∈ D, Injective (fderiv ℝ A c))
    (hpt : ∀ c ∈ D, ∃ M : Matrix ι ι ℤ, ∀ w, fderiv ℝ A' c w = M.map (↑) *ᵥ fderiv ℝ A c w) :
    ∃ (M : Matrix ι ι ℤ) (b : ι → ℝ), ∀ c ∈ D, A' c = M.map (↑) *ᵥ A c + b := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | ⟨c₀, hc₀⟩
  · exact ⟨1, 0, by simp⟩
  choose! M hM using hpt
  -- The matrix `M c` is the value at `c` of the map `R c = DA'(c) DA(c)⁻¹`, continuous on `D`.
  set R : (ι → ℝ) → (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    fun c ↦ fderiv ℝ A' c * Ring.inverse (fderiv ℝ A c)
  have hsurj {c} (hc : c ∈ D) : Surjective (fderiv ℝ A c) :=
    LinearMap.injective_iff_surjective (f := (fderiv ℝ A c : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))).1
      (hinj c hc)
  have hunit {c} (hc : c ∈ D) : IsUnit (fderiv ℝ A c) :=
    ContinuousLinearMap.isUnit_iff_bijective.2 ⟨hinj c hc, hsurj hc⟩
  have hR : ContinuousOn R D := fun c hc ↦ by
    have hinv := NormedRing.inverse_continuousAt (hunit hc).unit
    rw [IsUnit.unit_spec] at hinv
    exact ((hA'.continuousOn_fderiv_of_isOpen hDo le_rfl) c hc).mul
      (hinv.comp_continuousWithinAt ((hA.continuousOn_fderiv_of_isOpen hDo le_rfl) c hc))
  have hRM {c} (hc : c ∈ D) (w : ι → ℝ) : R c w = (M c).map (↑) *ᵥ w := by
    obtain ⟨u, rfl⟩ := hsurj hc w
    rw [← hM c hc, ← mul_apply_eq_comp, mul_assoc,
      Ring.inverse_mul_cancel _ (hunit hc), mul_one]
  -- The entries of `M c` are continuous and integral, hence constant on `D`.
  have hconst {c} (hc : c ∈ D) : M c = M c₀ := by
    refine Matrix.ext fun i k ↦ hD.constant (f := fun c ↦ M c i k) ?_ hc hc₀
    have hentry : EqOn (fun c ↦ (M c i k : ℝ)) (fun c ↦ R c (Pi.single k 1) i)
        D := fun c hc ↦ by simp [hRM hc, mulVec_single]
    refine Int.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.2 ?_
    exact ((continuous_apply i).comp_continuousOn (hR.clm_apply continuousOn_const)).congr hentry
  -- So `A' - M A` has zero derivative on `D`.
  set N : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' ((M c₀).map (↑)))
  have hN (w : ι → ℝ) : N w = (M c₀).map (↑) *ᵥ w := Matrix.toLin'_apply _ _
  have hdA {c} (hc : c ∈ D) : DifferentiableAt ℝ A c :=
    (hA.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  have hdA' {c} (hc : c ∈ D) : DifferentiableAt ℝ A' c :=
    (hA'.differentiableOn one_ne_zero c hc).differentiableAt (hDo.mem_nhds hc)
  have hg : EqOn (fderiv ℝ fun c ↦ A' c - N (A c)) 0 D := fun c hc ↦ by
    have h : HasFDerivAt (fun c ↦ A' c - N (A c)) (fderiv ℝ A' c - N.comp (fderiv ℝ A c)) c :=
      (hdA' hc).hasFDerivAt.sub (N.hasFDerivAt.comp c (hdA hc).hasFDerivAt)
    rw [h.fderiv]
    ext1 w
    simp [hN, hM c hc, hconst hc]
  have hgd : DifferentiableOn ℝ (fun c ↦ A' c - N (A c)) D := fun c hc ↦
    ((hdA' hc).sub (N.differentiableAt.comp c (hdA hc))).differentiableWithinAt
  refine ⟨M c₀, A' c₀ - N (A c₀), fun c hc ↦ ?_⟩
  rw [← hN, ← hDo.is_const_of_fderiv_eq_zero hD hgd hg hc hc₀]
  abel

end TauCeti
