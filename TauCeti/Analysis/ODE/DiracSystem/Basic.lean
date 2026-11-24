/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator.Holomorphic
public import TauCeti.Analysis.ODE.Propagator.Liouville
public import Mathlib.Analysis.CStarAlgebra.Matrix
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# The Dirac system and its fundamental matrix

A potential `q : ℝ → ℂ`, integrable on bounded subintervals of `[0, ∞)`, with `f = Re q` and
`g = Im q`, determines the Dirac system `Ω X' = z X - Q_q X` for `X(t) ∈ ℂ²`, where
`Ω = [[0, 1], [-1, 0]]`, `Q_q = [[g, f], [f, -g]]` and `z ∈ ℂ` is the spectral parameter.
Equivalently `X' = -Ω (z - Q_q) X`, and the coefficient is
`-Ω (z - Q_q(t)) = [[f, -z - g], [z - g, -f]]` (`TauCeti.diracCoeff`).

The fundamental matrix `M_q(t, z) = [[A, B], [C, D]]` (`TauCeti.diracFundamentalMatrix`) is the
matrix in the standard basis of the propagator `N(t, 0)` (`TauCeti.propagator`) of this
coefficient on `EuclideanSpace ℂ (Fin 2)`. Its first column `(A, C)` is the Neumann solution, with
initial value `(1, 0)`, and its second column `(B, D)` the Dirichlet solution, with initial value
`(0, 1)`.

## Main definitions

* `TauCeti.diracCoeff q z t`: the coefficient `-Ω (z - Q_q(t))`.
* `TauCeti.IsDiracSolution q z X`: `X` is continuous on `[0, ∞)` and solves the integral equation
  `X t = X 0 + ∫₀ᵗ -Ω (z - Q_q(s)) X s ds` for `t ≥ 0`.
* `TauCeti.diracFundamentalMatrix q t z`: the fundamental matrix `M_q(t, z)`.

## Main results

* `TauCeti.diracFundamentalMatrix_mulVec_eq_add_integral`: the integral equation
  `M_q(t, z) v = v + ∫₀ᵗ -Ω (z - Q_q(s)) M_q(s, z) v ds`, with `M_q(0, z) = 1`
  (`TauCeti.diracFundamentalMatrix_zero`);
* `TauCeti.isDiracSolution_diracFundamentalMatrix_mulVec`: for every initial value `v`,
  `t ↦ M_q(t, z) v` solves the Dirac system;
* `TauCeti.IsDiracSolution.eq_diracFundamentalMatrix_mulVec`: every solution is of this form, so
  two solutions with the same initial value agree on `[0, ∞)` (`TauCeti.IsDiracSolution.eqOn`);
* `TauCeti.differentiable_diracFundamentalMatrix_apply`: the entries `A, B, C, D` of `M_q(t, ·)`
  are entire functions of the spectral parameter;
* `TauCeti.det_diracFundamentalMatrix`: `det M_q(t, z) = 1`, by Liouville's formula, since the
  coefficient is trace-free (`TauCeti.trace_diracCoeff`);
* `TauCeti.diracFundamentalMatrix_zero_potential`: for `q = 0`,
  `M_0(t, z) = [[cos tz, -sin tz], [sin tz, cos tz]]`;
* `TauCeti.diracFundamentalMatrix_ofReal_const_zero`: for a real constant `q = c`,
  `M_c(t, 0) = diag(e^{ct}, e^{-ct})`, which fixes the sign convention of the system.

## Implementation notes

The fundamental matrix is defined through the propagator of `TauCeti.propagator`, so existence,
uniqueness, continuity, holomorphy in `z` (`TauCeti.differentiable_propagator_smul_add`, since
the coefficient is affine in `z`) and Liouville's formula (`TauCeti.det_propagator`) are
inherited from the general theory of linear equations with integrable coefficients. The integral
equation is stated on the coordinate space `Fin 2 → ℂ`; it does not depend on the norm, and
`EuclideanSpace.equiv` is the identity on coordinates.

## References

* A. Poltoratski, *Pointwise convergence of the non-linear Fourier transform*, Ann. of Math. (2)
  199 (2024), 741–793, §2.
* L. Mauth, *On pointwise convergence of the non-linear Fourier transform*, arXiv:2210.12286,
  §3.1.
* R. Romanov, *Canonical systems and de Branges spaces*, arXiv:1408.6022, §1.
-/

public section

open MeasureTheory Set Matrix Complex
open scoped Matrix Topology

namespace TauCeti

/-- The coefficient `-Ω (z - Q_q(t)) = [[f, -z - g], [z - g, -f]]` of the Dirac system
`Ω X' = z X - Q_q X` with potential `q` and spectral parameter `z`, where
`Ω = [[0, 1], [-1, 0]]`, `Q_q = [[g, f], [f, -g]]`, `f = Re q` and `g = Im q`. -/
def diracCoeff (q : ℝ → ℂ) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((q t).re : ℂ), -z - ((q t).im : ℂ); z - ((q t).im : ℂ), -((q t).re : ℂ)]

/-- The entries of the Dirac coefficient. -/
theorem diracCoeff_def (q : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    diracCoeff q z t =
      !![((q t).re : ℂ), -z - ((q t).im : ℂ); z - ((q t).im : ℂ), -((q t).re : ℂ)] := by
  rw [diracCoeff]

/-- The Dirac coefficient is trace-free. -/
@[simp]
theorem trace_diracCoeff (q : ℝ → ℂ) (z : ℂ) (t : ℝ) : (diracCoeff q z t).trace = 0 := by
  simp [diracCoeff, Matrix.trace_fin_two]

/-- `X` solves the Dirac system with potential `q` at the spectral parameter `z` on `[0, ∞)`:
`X` is continuous on `[0, ∞)` and `X t = X 0 + ∫₀ᵗ -Ω (z - Q_q(s)) X s ds` for every `t ≥ 0`. -/
def IsDiracSolution (q : ℝ → ℂ) (z : ℂ) (X : ℝ → Fin 2 → ℂ) : Prop :=
  ContinuousOn X (Ici 0) ∧ ∀ t, 0 ≤ t → X t = X 0 + ∫ s in (0 : ℝ)..t, diracCoeff q z s *ᵥ X s

/-- The fundamental matrix `M_q(t, z) = [[A, B], [C, D]]` of the Dirac system with potential `q`:
the matrix in the standard basis of the propagator `N(t, 0)` of the coefficient
`-Ω (z - Q_q)` acting on `EuclideanSpace ℂ (Fin 2)`. Its columns are the Neumann solution
`(A, C)` and the Dirichlet solution `(B, D)`, with initial values `(1, 0)` and `(0, 1)`. -/
noncomputable def diracFundamentalMatrix (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm
    (propagator (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s)) t 0)

/-- The fundamental matrix acts on `EuclideanSpace ℂ (Fin 2)` as the propagator `N(t, 0)` of the
Dirac coefficient. -/
@[simp]
theorem toEuclideanCLM_diracFundamentalMatrix (q : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracFundamentalMatrix q t z) =
      propagator (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s)) t 0 := by
  simp [diracFundamentalMatrix]

/-- The fundamental matrix at time `0` is the identity. -/
@[simp]
theorem diracFundamentalMatrix_zero (q : ℝ → ℂ) (z : ℂ) : diracFundamentalMatrix q 0 z = 1 := by
  simp [diracFundamentalMatrix]

variable {q : ℝ → ℂ} {z : ℂ} {a b t T : ℝ}

/-- The generator `-Ω = [[0, -1], [1, 0]]` multiplying the spectral parameter. -/
private noncomputable def diracGen : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, -1; 1, 0]

/-- The potential part `f [[1, 0], [0, -1]] + g [[0, -1], [-1, 0]]` of the Dirac coefficient. -/
private noncomputable def diracPotential (q : ℝ → ℂ) (s : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  ((q s).re : ℂ) • toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![1, 0; 0, -1] +
    ((q s).im : ℂ) • toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, -1; -1, 0]

/-- The generator `-Ω` squares to `-1`. -/
private theorem diracGen_mul_diracGen : diracGen * diracGen = -1 := by
  rw [diracGen, ← map_mul, ← map_one (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)), ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The Dirac coefficient as an operator: `z` times the generator `-Ω` plus the potential part
`f [[1, 0], [0, -1]] + g [[0, -1], [-1, 0]]`. -/
private theorem toEuclideanCLM_diracCoeff (q : ℝ → ℂ) (z : ℂ) (s : ℝ) :
    toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s) =
      z • diracGen + diracPotential q s := by
  simp only [diracGen, diracPotential, ← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diracCoeff] <;> ring

/-- The potential part of the Dirac coefficient is integrable where `q` is. -/
private theorem integrableOn_diracPotential (hq : IntegrableOn q (Icc a b)) :
    IntegrableOn (diracPotential q) (Icc a b) :=
  (hq.re.ofReal.smul_const _).add (hq.im.ofReal.smul_const _)

/-- The Dirac coefficient, as an operator on `EuclideanSpace ℂ (Fin 2)`, is integrable on every
compact interval on which the potential is integrable. -/
theorem integrableOn_toEuclideanCLM_diracCoeff (hq : IntegrableOn q (Icc a b)) (z : ℂ) :
    IntegrableOn (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s))
      (Icc a b) := by
  simp_rw [toEuclideanCLM_diracCoeff]
  exact (integrableOn_const measure_Icc_lt_top.ne).add (integrableOn_diracPotential hq)

/-- The action of the fundamental matrix on a vector, through the propagator. -/
private theorem diracFundamentalMatrix_mulVec_eq (q : ℝ → ℂ) (t : ℝ) (z : ℂ) (v : Fin 2 → ℂ) :
    diracFundamentalMatrix q t z *ᵥ v =
      WithLp.ofLp (propagator (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s))
        t 0 (WithLp.toLp 2 v)) := by
  rw [← toEuclideanCLM_diracFundamentalMatrix, ofLp_toEuclideanCLM]

/-- `t ↦ M_q(t, z) v` is continuous on `[0, T]` when `q` is integrable there. -/
theorem continuousOn_diracFundamentalMatrix_mulVec (hq : IntegrableOn q (Icc 0 T)) (z : ℂ)
    (v : Fin 2 → ℂ) : ContinuousOn (fun t ↦ diracFundamentalMatrix q t z *ᵥ v) (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · simp [Icc_eq_empty_of_lt hT]
  simp_rw [diracFundamentalMatrix_mulVec_eq]
  exact (PiLp.continuous_ofLp 2 _).comp_continuousOn
    ((continuousOn_propagator_left (integrableOn_toEuclideanCLM_diracCoeff hq z)
      (left_mem_Icc.2 hT)).clm_apply continuousOn_const)

/-- **The integral equation of the fundamental matrix.** For `t ∈ [0, T]`, with `q` integrable on
`[0, T]`, `M_q(t, z) v = v + ∫₀ᵗ -Ω (z - Q_q(s)) M_q(s, z) v ds`. -/
theorem diracFundamentalMatrix_mulVec_eq_add_integral (hq : IntegrableOn q (Icc 0 T))
    (ht : t ∈ Icc 0 T) (z : ℂ) (v : Fin 2 → ℂ) :
    diracFundamentalMatrix q t z *ᵥ v =
      v + ∫ s in (0 : ℝ)..t, diracCoeff q z s *ᵥ (diracFundamentalMatrix q s z *ᵥ v) := by
  set P := fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s)
  have hP : IntegrableOn P (Icc 0 T) := integrableOn_toEuclideanCLM_diracCoeff hq z
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.2 (ht.1.trans ht.2)
  have hx : ContinuousOn (fun s ↦ propagator P s 0 (WithLp.toLp 2 v)) (Icc 0 T) :=
    (continuousOn_propagator_left hP h0).clm_apply continuousOn_const
  have hI : IntervalIntegrable (fun s ↦ P s (propagator P s 0 (WithLp.toLp 2 v))) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
      ((hP.clm_apply_continuousOn hx isCompact_Icc).mono_set (Icc_subset_Icc_right ht.2))
  rw [diracFundamentalMatrix_mulVec_eq, propagator_apply_eq_add_integral hP h0 ht, WithLp.ofLp_add,
    WithLp.ofLp_toLp]
  congr 1
  have := (EuclideanSpace.equiv (Fin 2) ℂ).toContinuousLinearMap.intervalIntegral_comp_comm hI
  simp only [ContinuousLinearEquiv.coe_coe, PiLp.coe_continuousLinearEquiv] at this
  rw [← this]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  simp [P, diracFundamentalMatrix_mulVec_eq]

/-- **Existence of solutions.** If `q` is locally integrable on `[0, ∞)`, then for every initial
value `v` the function `t ↦ M_q(t, z) v` solves the Dirac system at `z`. -/
theorem isDiracSolution_diracFundamentalMatrix_mulVec (hq : LocallyIntegrableOn q (Ici 0))
    (z : ℂ) (v : Fin 2 → ℂ) :
    IsDiracSolution q z fun t ↦ diracFundamentalMatrix q t z *ᵥ v := by
  have hqT (T : ℝ) : IntegrableOn q (Icc 0 T) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · have hmem : Icc 0 (t + 1) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic]
      exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
    exact ((continuousOn_diracFundamentalMatrix_mulVec (hqT (t + 1)) z v) t
      ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem
  · simpa using diracFundamentalMatrix_mulVec_eq_add_integral (hqT t) ⟨ht, le_rfl⟩ z v

/-- **Uniqueness of solutions.** If `q` is integrable on `[0, t]`, every solution `X` of the Dirac
system at `z` satisfies `X t = M_q(t, z) X 0`. -/
theorem IsDiracSolution.eq_diracFundamentalMatrix_mulVec {X : ℝ → Fin 2 → ℂ}
    (hX : IsDiracSolution q z X) (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) :
    X t = diracFundamentalMatrix q t z *ᵥ X 0 := by
  set P := fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff q z s)
  have hP : IntegrableOn P (Icc 0 t) := integrableOn_toEuclideanCLM_diracCoeff hq z
  have h0 : (0 : ℝ) ∈ Icc 0 t := left_mem_Icc.2 ht
  set x : ℝ → EuclideanSpace ℂ (Fin 2) := fun s ↦ WithLp.toLp 2 (X s)
  have hx : ContinuousOn x (Icc 0 t) :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn (hX.1.mono Icc_subset_Ici_self)
  have key := eq_propagator_apply hP h0 (right_mem_Icc.2 ht) hx fun r hr ↦ by
    have hI : IntervalIntegrable (fun s ↦ diracCoeff q z s *ᵥ X s) volume 0 r := by
      have := (hP.clm_apply_continuousOn hx isCompact_Icc).mono_set (Icc_subset_Icc_right hr.2)
      have h2 := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 ↦ ℂ)).toContinuousLinearMap
        |>.integrable_comp this
      have h3 : IntegrableOn (fun s ↦ diracCoeff q z s *ᵥ X s) (Icc 0 r) :=
        h2.congr (ae_of_all _ fun s ↦ by simp [P, x, PiLp.coe_continuousLinearEquiv])
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hr.1).2 h3
    have := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 ↦ ℂ)).symm.toContinuousLinearMap
      |>.intervalIntegral_comp_comm hI
    simp only [ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv] at this
    simp only [x, hX.2 r hr.1, WithLp.toLp_add, ← this]
    simp only [P, toEuclideanCLM_toLp]
  have := congrArg WithLp.ofLp key
  simpa [x, diracFundamentalMatrix_mulVec_eq] using this

/-- Two solutions of the Dirac system with the same initial value agree on `[0, ∞)`. -/
theorem IsDiracSolution.eqOn (hq : LocallyIntegrableOn q (Ici 0)) {X Y : ℝ → Fin 2 → ℂ}
    (hX : IsDiracSolution q z X) (hY : IsDiracSolution q z Y) (h : X 0 = Y 0) :
    EqOn X Y (Ici 0) := fun t ht ↦ by
  have hqt : IntegrableOn q (Icc 0 t) :=
    hq.integrableOn_compact_subset Icc_subset_Ici_self isCompact_Icc
  rw [hX.eq_diracFundamentalMatrix_mulVec hqt ht, hY.eq_diracFundamentalMatrix_mulVec hqt ht, h]

/-- **The fundamental matrix is entire in the spectral parameter.** If `q` is integrable on
`[0, t]`, every entry of `M_q(t, ·)` is an entire function. -/
theorem differentiable_diracFundamentalMatrix_apply (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t)
    (i j : Fin 2) : Differentiable ℂ fun z ↦ diracFundamentalMatrix q t z i j := by
  have hd := differentiable_propagator_smul_add diracGen (integrableOn_diracPotential hq)
    (left_mem_Icc.2 ht) (right_mem_Icc.2 ht)
  have key (z : ℂ) : diracFundamentalMatrix q t z i j =
      WithLp.ofLp (propagator (fun s ↦ z • diracGen + diracPotential q s) t 0
        (EuclideanSpace.single j 1)) i := by
    have := congrFun (diracFundamentalMatrix_mulVec_eq q t z (Pi.single j 1)) i
    simp_rw [toEuclideanCLM_diracCoeff] at this
    simpa [Matrix.mulVec_single] using this
  simp_rw [key]
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp
    (hd.clm_apply (differentiable_const _))

/-- **Liouville's formula for the Dirac system.** The coefficient is trace-free, so
`det M_q(t, z) = 1` whenever `q` is integrable on `[0, t]`. -/
theorem det_diracFundamentalMatrix (hq : IntegrableOn q (Icc 0 t)) (ht : 0 ≤ t) (z : ℂ) :
    (diracFundamentalMatrix q t z).det = 1 := by
  rw [← det_toEuclideanCLM, toEuclideanCLM_diracFundamentalMatrix, ContinuousLinearMap.det,
    det_propagator (integrableOn_toEuclideanCLM_diracCoeff hq z) (left_mem_Icc.2 ht)
      (right_mem_Icc.2 ht)]
  simp

/-- **The free Dirac system.** For the zero potential the fundamental matrix is the rotation
`M_0(t, z) = [[cos tz, -sin tz], [sin tz, cos tz]]`. -/
theorem diracFundamentalMatrix_zero_potential (t : ℝ) (z : ℂ) :
    diracFundamentalMatrix 0 t z = !![cos (t * z), -sin (t * z); sin (t * z), cos (t * z)] := by
  have hP : (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff 0 z s)) =
      fun _ ↦ z • diracGen := by
    ext1 s
    rw [diracGen, ← map_smul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracCoeff]
  -- `M_0(r, z)` acts as `cos (r z) + sin (r z) (-Ω)`, which solves `N' = z (-Ω) N` since
  -- `(-Ω)² = -1`.
  have hX : propagator (fun _ ↦ z • diracGen) t 0 =
      cos (t * z) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) +
        sin (t * z) • diracGen := by
    refine propagator_eq_of_hasDerivAt (a := min 0 t) (b := max 0 t)
      (X := fun r : ℝ ↦ cos (r * z) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] _) +
        sin (r * z) • diracGen) continuousOn_const.integrableOn_Icc
      ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
      (fun r _ ↦ ?_) (by simp)
    have hc : HasDerivAt (fun r : ℝ ↦ cos (r * z)) (-sin (r * z) * z) r := by
      simpa [Function.comp_def] using ((Complex.hasDerivAt_cos ((r : ℂ) * z)).comp (r : ℂ)
        ((hasDerivAt_id (r : ℂ)).mul_const z)).comp_ofReal
    have hs : HasDerivAt (fun r : ℝ ↦ sin (r * z)) (cos (r * z) * z) r := by
      simpa [Function.comp_def] using ((Complex.hasDerivAt_sin ((r : ℂ) * z)).comp (r : ℂ)
        ((hasDerivAt_id (r : ℂ)).mul_const z)).comp_ofReal
    refine ((hc.smul_const _).add (hs.smul_const _)).congr_deriv ?_
    simp only [← ContinuousLinearMap.mul_def, smul_mul_assoc, mul_add, mul_smul_comm, mul_one,
      diracGen_mul_diracGen]
    module
  rw [diracFundamentalMatrix, hP, hX, map_add, map_smul, map_smul, map_one, diracGen,
    StarAlgEquiv.symm_apply_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **A real constant potential at `z = 0`.** For `q = c` real, the fundamental matrix at the
spectral parameter `0` is `M_c(t, 0) = diag(e^{ct}, e^{-ct})`. The opposite sign convention
`Ω X' = z X + Q_q X` would give `diag(e^{-ct}, e^{ct})`. -/
theorem diracFundamentalMatrix_ofReal_const_zero (c t : ℝ) :
    diracFundamentalMatrix (fun _ ↦ (c : ℂ)) t 0 =
      !![(Real.exp (c * t) : ℂ), 0; 0, (Real.exp (-(c * t)) : ℂ)] := by
  set E₁ := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![1, 0; 0, 0]
  set E₂ := toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) !![0, 0; 0, 1]
  have hP : (fun s ↦ toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (diracCoeff (fun _ ↦ (c : ℂ)) 0 s)) =
      fun _ ↦ (c : ℂ) • (E₁ - E₂) := by
    ext1 s
    rw [← map_sub, ← map_smul]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diracCoeff]
  have hmul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
      toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A * toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) B =
        toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (A * B) :=
    (map_mul _ A B).symm
  have h11 : E₁ * E₁ = E₁ := by rw [hmul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp
  have h22 : E₂ * E₂ = E₂ := by rw [hmul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp
  have h12 : E₁ * E₂ = 0 := by
    rw [hmul, ← map_zero (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp
  have h21 : E₂ * E₁ = 0 := by
    rw [hmul, ← map_zero (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hE : E₁ + E₂ = 1 := by
    rw [← map_add, ← map_one (toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))]
    congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp
  -- `M_c(r, 0)` acts as `e^{cr} E₁ + e^{-cr} E₂`, which solves `N' = c (E₁ - E₂) N`.
  have hX : propagator (fun _ ↦ (c : ℂ) • (E₁ - E₂)) t 0 =
      cexp (c * t) • E₁ + cexp (-(c * t)) • E₂ := by
    refine propagator_eq_of_hasDerivAt (a := min 0 t) (b := max 0 t)
      (X := fun r : ℝ ↦ cexp (c * r) • E₁ + cexp (-(c * r)) • E₂)
      continuousOn_const.integrableOn_Icc ⟨min_le_left _ _, le_max_left _ _⟩
      ⟨min_le_right _ _, le_max_right _ _⟩ (fun r _ ↦ ?_) (by simp [hE])
    have h₁ : HasDerivAt (fun r : ℝ ↦ cexp (c * r)) (cexp (c * r) * c) r := by
      simpa [Function.comp_def] using ((Complex.hasDerivAt_exp ((c : ℂ) * r)).comp (r : ℂ)
        ((hasDerivAt_id (r : ℂ)).const_mul (c : ℂ))).comp_ofReal
    have h₂ : HasDerivAt (fun r : ℝ ↦ cexp (-(c * r))) (cexp (-(c * r)) * -c) r := by
      simpa [Function.comp_def] using ((Complex.hasDerivAt_exp (-((c : ℂ) * r))).comp (r : ℂ)
        ((hasDerivAt_id (r : ℂ)).const_mul (c : ℂ)).neg).comp_ofReal
    refine ((h₁.smul_const _).add (h₂.smul_const _)).congr_deriv ?_
    simp only [← ContinuousLinearMap.mul_def, smul_mul_assoc, mul_add, mul_smul_comm, sub_mul,
      h11, h22, h12, h21]
    module
  rw [diracFundamentalMatrix, hP, hX, map_add, map_smul, map_smul, StarAlgEquiv.symm_apply_apply,
    StarAlgEquiv.symm_apply_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Complex.ofReal_exp]

end TauCeti
