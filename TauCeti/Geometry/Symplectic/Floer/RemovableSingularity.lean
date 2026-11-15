/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Graph
public import TauCeti.Geometry.Symplectic.JHolomorphic.Energy.HigherIntegrability
public import TauCeti.Geometry.Symplectic.JHolomorphic.WeakDerivative
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.ProdL2
import TauCeti.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Geometry.Symplectic.Prod.Basic
import TauCeti.Geometry.Symplectic.SymplecticTransport
import TauCeti.Geometry.Symplectic.Transport

/-!
# Removal of finite-energy punctures for Floer solutions

In local coordinates `z = s + i t ∈ ℂ` on the domain and `x ∈ V` on the target, the
inhomogeneous Cauchy–Riemann equation of Hamiltonian Floer theory reads

`∂ₜu - X(z, u) i = J(z, u) (∂ₛu - X(z, u) 1)`,

for a domain-dependent structure `J(z, x)` on `V` and the Hamiltonian one-form
`X(z, x) : ℂ →L[ℝ] V`. This file proves that a solution on a punctured neighbourhood `Ω \ {z₀}` of
a point, with image in a compact set, tame structures `J(z, u z)` and finite energy `∫ ‖∂ₛu‖²`,
extends continuously across the puncture
(`TauCeti.Floer.exists_continuousOn_update_of_finite_energy`). The extension is weakly
differentiable on `Ω`, with weak derivative the classical differential of `u`, and that
differential lies in `Lᵖ` near the puncture for some `p > 2`
(`TauCeti.Floer.exists_hasWeakFDerivOn_update_of_finite_energy`).

In Gromov–Floer compactness the limit of a sequence of Floer solutions is first obtained off
finitely many bubbling points
(`TauCeti.Floer.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`). Where that limit
is a `C³` solution of finite energy, the results here extend it across a bubbling point; its value
there is the point at which the bubble is attached.

The proof is Gromov's graph construction. The map `U(z) = (λ z, u z)` into the Euclidean product
`WithLp 2 (ℂ × V)` solves `∂ₜU = J'(U) ∂ₛU` for the structure `J' = TauCeti.Floer.graphStructure`
of the rescaled data `J(λ⁻¹ ζ, x)` and `λ⁻¹ X(λ⁻¹ ζ, x)`. If `ω(·, J₀ ·)` is the inner product of
`V` and `ω` tames `J(z, u z)` with a uniform constant, then for `λ` large, depending only on the
bounds of `J` and `X` near the puncture, the constant split form `ω_std ⊕ ω` tames `J'` along `U`:
the rescaling makes the off-diagonal terms of `J'` coming from `X` small. The removal theorems for
pseudoholomorphic curves with tame varying structures
(`TauCeti.SymplecticForm.exists_continuousOn_update_of_finite_energy`,
`TauCeti.SymplecticForm.exists_pos_forall_memLp_fderiv_of_finite_energy`) then apply to `U`, whose
energy density is `λ² + ‖∂ₛu‖²`, and `u` is the second component of `U`.

Smoothness of the extension at the puncture, which requires elliptic regularity, is not treated
here.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.5
  (removal of singularities) and Section 8.1 (the graph construction for the inhomogeneous
  equation).
-/

public section

open Complex Filter MeasureTheory Metric Set Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

section GraphForm

variable (ω : SymplecticForm V) (J₀ : AlmostComplexStructure V)

/-- The split symplectic form `ω_std ⊕ ω` on the Euclidean product `WithLp 2 (ℂ × V)`. -/
private noncomputable def graphForm : SymplecticForm (WithLp 2 (ℂ × V)) :=
  (stdComplexSymplecticForm.prod ω).transport (WithLp.linearEquiv 2 ℝ (ℂ × V)).symm

/-- The split structure `i ⊕ J₀` on the Euclidean product `WithLp 2 (ℂ × V)`. -/
private noncomputable def graphJ₀ : AlmostComplexStructure (WithLp 2 (ℂ × V)) :=
  ((AlmostComplexStructure.ofComplexModule ℂ).prod J₀).transport
    (WithLp.linearEquiv 2 ℝ (ℂ × V)).symm

private theorem graphForm_apply (ξ η : WithLp 2 (ℂ × V)) :
    graphForm ω ξ η = stdComplexSymplecticForm ξ.fst η.fst + ω ξ.snd η.snd :=
  rfl

private theorem graphJ₀_apply (η : WithLp 2 (ℂ × V)) :
    graphJ₀ J₀ η = WithLp.toLp 2 (I * η.fst, J₀ η.snd) := by
  simp [graphJ₀, AlmostComplexStructure.ofComplexModule_apply]

variable {ω J₀}

/-- The split form `ω_std ⊕ ω` and the split structure `i ⊕ J₀` give the Euclidean inner product
of `WithLp 2 (ℂ × V)` when `ω` and `J₀` give the inner product of `V`. -/
private theorem graphForm_graphJ₀ (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    (ξ η : WithLp 2 (ℂ × V)) : graphForm ω ξ (graphJ₀ J₀ η) = inner ℝ ξ η := by
  simp only [graphForm_apply, graphJ₀_apply, WithLp.prod_inner_apply, WithLp.toLp_fst,
    WithLp.toLp_snd, WithLp.ofLp_fst, WithLp.ofLp_snd, hg, stdComplexSymplecticForm_apply,
    Complex.inner, mul_re, mul_im, I_re, I_im, conj_re, conj_im]
  ring

/-- **The split form tames the graph structure of small one-forms.** Let `ω(·, J₀ ·)` be the inner
product of `V`, and let `ω` tame `A = J(z, x)` with constant `c > 0`. If `‖A‖ ≤ M` and the one-form
`Y = X(z, x)` satisfies `‖Y‖ ≤ N` with `N (M + 1) ≤ min 1 c`, then `ω_std ⊕ ω` tames Gromov's
structure at `(z, x)` with constant `min 1 c / 2`. -/
private theorem mul_norm_sq_le_graphForm_graphStructure (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w)
    {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {p : WithLp 2 (ℂ × V)} {c M N : ℝ}
    (hc : 0 < c) (htame : ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J p.ofLp v)) (hM : ‖J p.ofLp‖ ≤ M)
    (hN : ‖X p.ofLp‖ ≤ N) (hsmall : N * (M + 1) ≤ min 1 c) (ξ : WithLp 2 (ℂ × V)) :
    min 1 c / 2 * ‖ξ‖ ^ 2 ≤ graphForm ω ξ (graphStructure J X p ξ) := by
  set a := ‖ξ.fst‖
  set b := ‖ξ.snd‖
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  -- The two cross terms coming from the one-form are bounded by `b M N a` and `b N a`.
  have h₁ : |ω ξ.snd (J p.ofLp (X p.ofLp ξ.fst))| ≤ b * (M * N * a) := by
    refine (ω.abs_apply_le_norm_mul_norm hg _ _).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    calc ‖J p.ofLp (X p.ofLp ξ.fst)‖ ≤ ‖J p.ofLp‖ * (‖X p.ofLp‖ * a) :=
          (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
      _ ≤ M * (N * a) := by gcongr
      _ = M * N * a := by ring
  have h₂ : |ω ξ.snd (X p.ofLp (I * ξ.fst))| ≤ b * (N * a) := by
    refine (ω.abs_apply_le_norm_mul_norm hg _ _).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    calc ‖X p.ofLp (I * ξ.fst)‖ ≤ ‖X p.ofLp‖ * ‖I * ξ.fst‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * a := by rw [norm_mul, norm_I, one_mul]; gcongr
  have hstd : stdComplexSymplecticForm ξ.fst (I * ξ.fst) = a ^ 2 := by
    rw [stdComplexSymplecticForm_apply, Complex.sq_norm, Complex.normSq_apply]
    simp only [mul_re, mul_im, I_re, I_im]
    ring
  have hval : graphForm ω ξ (graphStructure J X p ξ) = a ^ 2 + ω ξ.snd (J p.ofLp ξ.snd) -
      ω ξ.snd (J p.ofLp (X p.ofLp ξ.fst)) + ω ξ.snd (X p.ofLp (I * ξ.fst)) := by
    simp only [graphForm_apply, graphStructure_apply, WithLp.toLp_fst, WithLp.toLp_snd, hstd,
      map_sub, map_add]
    ring
  have hnorm : ‖ξ‖ ^ 2 = a ^ 2 + b ^ 2 := WithLp.prod_norm_sq_eq_of_L2 ξ
  have hcb := htame ξ.snd
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have hmc : min 1 c ≤ c := min_le_right _ _
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hab : b * (M * N * a) + b * (N * a) ≤ min 1 c * (a * b) := by
    have : b * (M * N * a) + b * (N * a) = N * (M + 1) * (a * b) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hsmall (by positivity)
  rw [hval, hnorm]
  nlinarith [abs_le.mp h₁, abs_le.mp h₂, sq_nonneg (a - b), sq_nonneg a, sq_nonneg b,
    mul_nonneg (norm_nonneg ξ.fst) (norm_nonneg ξ.snd)]

end GraphForm

variable [FiniteDimensional ℝ V] {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
  {J : ℂ × V → V →L[ℝ] V} {X : ℂ × V → ℂ →L[ℝ] V} {W : Set (ℂ × V)} {K : Set V} {Ω : Set ℂ}
  {u : ℂ → V} {z₀ : ℂ} {c : ℝ}

omit [FiniteDimensional ℝ V] in
/-- The graph `z ↦ (λ z, u z)` of a solution of the inhomogeneous equation solves `∂ₜU = J'(U) ∂ₛU`
for Gromov's structure of the rescaled data `J(λ⁻¹ ζ, x)` and `λ⁻¹ X(λ⁻¹ ζ, x)`. -/
private theorem fderiv_toLp_smul_prodMk_I_eq_graphStructure {lam : ℝ} (hlam : lam ≠ 0) {y : ℂ}
    (hu : DifferentiableAt ℝ u y)
    (hfl : fderiv ℝ u y I - X (y, u y) I = J (y, u y) (fderiv ℝ u y 1 - X (y, u y) 1)) :
    fderiv ℝ (fun w ↦ WithLp.toLp 2 (lam • w, u w)) y I =
      graphStructure (fun q ↦ J (lam⁻¹ • q.1, q.2)) (fun q ↦ lam⁻¹ • X (lam⁻¹ • q.1, q.2))
        (WithLp.toLp 2 (lam • y, u y))
        (fderiv ℝ (fun w ↦ WithLp.toLp 2 (lam • w, u w)) y 1) := by
  have hs : DifferentiableAt ℝ (fun w : ℂ ↦ lam • w) y := (differentiableAt_id).const_smul lam
  have hsd (v : ℂ) : fderiv ℝ (fun w : ℂ ↦ lam • w) y v = lam • v := by
    have h : HasFDerivAt (fun w : ℂ ↦ lam • w) (lam • ContinuousLinearMap.id ℝ ℂ) y :=
      (hasFDerivAt_id y).const_smul lam
    rw [h.fderiv]
    rfl
  have hy : lam⁻¹ • lam • y = y := inv_smul_smul₀ hlam y
  have hI : I * (lam • (1 : ℂ)) = lam • I := by rw [mul_smul_comm, mul_one]
  rw [fderiv_toLp_prodMk_apply hs hu, fderiv_toLp_prodMk_apply hs hu, graphStructure_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, hsd, hy, hI, map_smul,
    smul_apply, smul_smul, mul_inv_cancel₀ hlam, one_smul, WithLp.toLp.injEq,
    Prod.mk.injEq, true_and]
  exact eq_add_of_sub_eq hfl

omit [FiniteDimensional ℝ V] in
/-- The rescaled graph structure `J'` of the data `J(λ⁻¹ ζ, x)` and `λ⁻¹ X(λ⁻¹ ζ, x)` is `C²` on an
open set `W'` containing a compact set `K'`, on which it squares to `-1`; `K'` consists of the
points `(λ z, x)` for `(z, x)` in a compact set `S` where `J` and `X` are `C²` and `J² = -1`. -/
private theorem exists_rescaled_graphStructure_data {lam : ℝ} (hlam : lam ≠ 0) {S : Set (ℂ × V)}
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W) (hS : IsCompact S)
    (hSW : S ⊆ W) (hJsq : ∀ q ∈ S, ∀ v, J q (J q v) = -v) :
    ∃ W' K' : Set (WithLp 2 (ℂ × V)), IsOpen W' ∧
      ContDiffOn ℝ 2
        (graphStructure (fun q ↦ J (lam⁻¹ • q.1, q.2)) (fun q ↦ lam⁻¹ • X (lam⁻¹ • q.1, q.2)))
        W' ∧ IsCompact K' ∧ K' ⊆ W' ∧
      (∀ p ∈ K', ∀ ζ, graphStructure (fun q ↦ J (lam⁻¹ • q.1, q.2))
        (fun q ↦ lam⁻¹ • X (lam⁻¹ • q.1, q.2)) p (graphStructure (fun q ↦ J (lam⁻¹ • q.1, q.2))
          (fun q ↦ lam⁻¹ • X (lam⁻¹ • q.1, q.2)) p ζ) = -ζ) ∧
      (∀ q ∈ S, WithLp.toLp 2 (lam • q.1, q.2) ∈ K') ∧
      ∀ p ∈ K', (lam⁻¹ • p.fst, p.snd) ∈ S := by
  set σ : ℂ × V → ℂ × V := fun q ↦ (lam⁻¹ • q.1, q.2)
  have hσ : ContDiff ℝ 2 σ := (contDiff_fst.const_smul _).prodMk contDiff_snd
  set e : ℂ × V → WithLp 2 (ℂ × V) := fun q ↦ WithLp.toLp 2 (lam • q.1, q.2)
  have he : Continuous e :=
    (WithLp.contDiff_toLp (𝕜 := ℝ) (n := 0)).continuous.comp
      ((continuous_fst.const_smul lam).prodMk continuous_snd)
  have hσe (q : ℂ × V) : σ (e q).ofLp = q := by
    simp only [σ, e, inv_smul_smul₀ hlam]
  refine ⟨WithLp.ofLp ⁻¹' (σ ⁻¹' W), e '' S,
    (hW.preimage hσ.continuous).preimage (WithLp.contDiff_ofLp (𝕜 := ℝ) (n := 0)).continuous,
    contDiffOn_graphStructure (hJ.comp hσ.contDiffOn (mapsTo_preimage σ W))
      ((hX.comp hσ.contDiffOn (mapsTo_preimage σ W)).const_smul _),
    hS.image he, ?_, ?_, fun q hq ↦ ⟨q, hq, rfl⟩, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    change σ (e q).ofLp ∈ W
    rw [hσe]
    exact hSW hq
  · rintro _ ⟨q, hq, rfl⟩ ζ
    exact graphStructure_graphStructure (fun v ↦ by
      change J (σ (e q).ofLp) (J (σ (e q).ofLp) v) = -v
      rw [hσe]
      exact hJsq q hq v) ζ
  · rintro _ ⟨q, hq, rfl⟩
    change σ (e q).ofLp ∈ S
    rw [hσe]
    exact hq

omit [FiniteDimensional ℝ V] in
/-- The graph `z ↦ (λ z, u z)` has energy density `λ² + ‖∂ₛu‖²`, so it has finite energy on a disc
on which `u` has finite energy. -/
private theorem integrableOn_norm_fderiv_toLp_smul_prodMk_sq (lam : ℝ) {r : ℝ}
    (hdiff : ∀ z ∈ ball z₀ r \ {z₀}, DifferentiableAt ℝ u z)
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) (ball z₀ r)) :
    IntegrableOn (fun z ↦ ‖fderiv ℝ (fun w ↦ WithLp.toLp 2 (lam • w, u w)) z 1‖ ^ 2)
      (ball z₀ r) := by
  refine ((integrableOn_const (C := lam ^ 2) measure_ball_lt_top.ne).add henergy).congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne z₀)] with z hz hzne
  have hs : DifferentiableAt ℝ (fun w : ℂ ↦ lam • w) z := differentiableAt_fun_id.const_smul lam
  rw [Pi.add_apply, norm_fderiv_toLp_prodMk_apply_sq hs (hdiff z ⟨hz, hzne⟩),
    fderiv_fun_const_smul differentiableAt_fun_id, fderiv_fun_id]
  simp

/-- **Reduction to the graph, for a given rescaling.** Let `J` and `X` be bounded by `M` and `N` on
`D × K`, for the closed disc `D` of radius `r` about `z₀`, and let `λ > 0` make
`λ⁻¹ N (M + 1) ≤ min 1 c`. Then a tamed solution of finite energy on `Ω \ {z₀}` has a limit `q` at
`z₀`, and its differential lies in `Lᵖ` on a small disc about `z₀` for some `p > 2`. -/
private theorem exists_tendsto_memLp_fderiv_of_rescale
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hK : IsCompact K) (hΩ : IsOpen Ω) {r : ℝ} (hr : 0 < r) (hrΩ : closedBall z₀ r ⊆ Ω)
    (hΩKW : Ω ×ˢ K ⊆ W) (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (Ω \ {z₀}))
    (hfl : ∀ z ∈ Ω \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (Ω \ {z₀}) K)
    (htame : ∀ z ∈ Ω \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) Ω) {M N lam : ℝ}
    (hM : ∀ q ∈ closedBall z₀ r ×ˢ K, ‖J q‖ ≤ M) (hN : ∀ q ∈ closedBall z₀ r ×ˢ K, ‖X q‖ ≤ N)
    (hlam : 0 < lam) (hsmall : lam⁻¹ * N * (M + 1) ≤ min 1 c) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ ∃ ε > 0, ball z₀ ε ⊆ Ω ∧ ∃ p : ℝ, 2 < p ∧
      MemLp (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ ε)) := by
  have hDK := (isCompact_closedBall z₀ r).prod hK
  obtain ⟨W', K', hW', hJ', hK', hK'W', hJsq', hK'mem, hK'S⟩ := exists_rescaled_graphStructure_data
    hlam.ne' hW hJ hX hDK ((prod_mono hrΩ subset_rfl).trans hΩKW)
    fun q hq ↦ hJsq q.1 (hrΩ hq.1) q.2 hq.2
  obtain ⟨B₀, hB₀⟩ := IsCompact.exists_bound_of_continuousOn
    (E := WithLp 2 (ℂ × V) →L[ℝ] WithLp 2 (ℂ × V)) hK' (hJ'.continuousOn.mono hK'W')
  -- The graph `U` on the punctured disc `P = B_r(z₀) \ {z₀}`.
  set U : ℂ → WithLp 2 (ℂ × V) := fun z ↦ WithLp.toLp 2 (lam • z, u z)
  have hPΩ : ball z₀ r \ {z₀} ⊆ Ω \ {z₀} :=
    sdiff_subset_sdiff_left (ball_subset_closedBall.trans hrΩ)
  have hdiff (z : ℂ) (hz : z ∈ Ω \ {z₀}) : DifferentiableAt ℝ u z :=
    (hu.differentiableOn (by norm_num)).differentiableAt ((hΩ.sdiff isClosed_singleton).mem_nhds hz)
  have hq (z : ℂ) (hz : z ∈ ball z₀ r \ {z₀}) : (z, u z) ∈ closedBall z₀ r ×ˢ K :=
    ⟨ball_subset_closedBall hz.1, huK (hPΩ hz)⟩
  have hUK : MapsTo U (ball z₀ r \ {z₀}) K' := fun z hz ↦ hK'mem _ (hq z hz)
  have hσU (z : ℂ) : (lam⁻¹ • (U z).ofLp.1, (U z).ofLp.2) = (z, u z) := by
    simp only [U]
    rw [inv_smul_smul₀ hlam.ne']
  -- Along `U`, the split form tames the rescaled graph structure with constant `min 1 c / 2`.
  have htame' (z : ℂ) (hz : z ∈ ball z₀ r \ {z₀}) (ξ : WithLp 2 (ℂ × V)) :
      min 1 c / 2 * ‖ξ‖ ^ 2 ≤ graphForm ω ξ (graphStructure (fun q ↦ J (lam⁻¹ • q.1, q.2))
        (fun q ↦ lam⁻¹ • X (lam⁻¹ • q.1, q.2)) (U z) ξ) := by
    refine mul_norm_sq_le_graphForm_graphStructure hg hc (M := M) (N := lam⁻¹ * N)
      (fun v ↦ by rw [hσU]; exact htame z (hPΩ hz) v) (by rw [hσU]; exact hM _ (hq z hz)) ?_
      hsmall ξ
    rw [hσU, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hlam.le)]
    exact mul_le_mul_of_nonneg_left (hN _ (hq z hz)) (inv_nonneg.2 hlam.le)
  have hU : ContDiffOn ℝ 3 U (ball z₀ r \ {z₀}) := WithLp.contDiff_toLp.comp_contDiffOn
    ((contDiffOn_id.const_smul lam).prodMk (hu.mono hPΩ))
  have hCR (z : ℂ) (hz : z ∈ ball z₀ r \ {z₀}) := fderiv_toLp_smul_prodMk_I_eq_graphStructure
    hlam.ne' (hdiff z (hPΩ hz)) (hfl z (hPΩ hz))
  have henergy' := integrableOn_norm_fderiv_toLp_smul_prodMk_sq lam (fun z hz ↦ hdiff z (hPΩ hz))
    (henergy.mono_set (ball_subset_closedBall.trans hrΩ))
  have hm2 : 0 < min 1 c / 2 := half_pos (lt_min one_pos hc)
  -- Apply the removal theorems for pseudoholomorphic curves to `U`.
  obtain ⟨q', hq', hlim, -, -⟩ := (graphForm ω).exists_continuousOn_update_of_finite_energy
    (graphForm_graphJ₀ hg) hm2 hr hW' hJ' hK' hK'W' hJsq' hU hCR hUK htame' henergy'
  obtain ⟨ε, hε, hεr, hmem⟩ := (graphForm ω).exists_pos_forall_memLp_fderiv_of_finite_energy
    (graphForm_graphJ₀ hg) hm2 hr hW' hJ' hK' hK'W' hJsq' hU hCR hUK htame'
    (fun z hz ↦ (hB₀ _ (hUK hz)).trans (le_max_left B₀ 0)) henergy'
  obtain ⟨β, hβdef⟩ : ∃ β, β = min 1 c / 2 / (1 + max B₀ 0) ^ 2 := ⟨_, rfl⟩
  have hβ : 0 < β := by rw [hβdef]; positivity
  refine ⟨q'.snd, (hK'S q' hq').2, ?_, ε, hε, (ball_subset_ball hεr.le).trans
    (ball_subset_closedBall.trans hrΩ), 2 + β, by linarith, ?_⟩
  · -- `u` is the second component of `U`.
    exact (((WithLp.sndL 2 ℝ ℂ V).continuous.tendsto _).comp hlim).congr fun z ↦ by simp [U]
  · -- The differential of `u` is dominated by that of its graph.
    refine (hmem (2 + β) (by linarith) (by rw [← hβdef]; nlinarith [sq_nonneg β])).of_le
      (measurable_fderiv ℝ u).aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
    exact norm_fderiv_le_norm_fderiv_toLp_prodMk_right (differentiableAt_fun_id.const_smul lam)

/-- **Reduction to the graph.** A solution of the inhomogeneous equation on a punctured
neighbourhood of `z₀`, tamed and of finite energy, has a limit `q` at `z₀`, and its differential
lies in `Lᵖ` on a small disc about `z₀` for some `p > 2`. -/
private theorem exists_tendsto_memLp_fderiv_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (hΩKW : Ω ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (Ω \ {z₀}))
    (hfl : ∀ z ∈ Ω \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (Ω \ {z₀}) K)
    (htame : ∀ z ∈ Ω \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) Ω) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧ ∃ ε > 0, ball z₀ ε ⊆ Ω ∧ ∃ p : ℝ, 2 < p ∧
      MemLp (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ ε)) := by
  -- A closed disc about `z₀` in `Ω`, and bounds for `J` and `X` over it.
  obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hz₀)
  have hDK := (isCompact_closedBall z₀ r).prod hK
  have hDKW : closedBall z₀ r ×ˢ K ⊆ W := (prod_mono hrΩ subset_rfl).trans hΩKW
  obtain ⟨M₀, hM₀⟩ := hDK.exists_bound_of_continuousOn (hJ.continuousOn.mono hDKW)
  obtain ⟨N₀, hN₀⟩ := hDK.exists_bound_of_continuousOn (hX.continuousOn.mono hDKW)
  set M := max M₀ 0
  set N := max N₀ 0
  have hm : 0 < min 1 c := lt_min one_pos hc
  -- The rescaling factor, large enough that `ω_std ⊕ ω` tames the rescaled graph structure.
  set lam := N * (M + 1) / min 1 c + 1
  have hlam : 0 < lam := by positivity
  refine exists_tendsto_memLp_fderiv_of_rescale hg hc hW hJ hX hK hΩ hr hrΩ hΩKW hJsq hu hfl huK
    htame henergy (fun q hq ↦ (hM₀ q hq).trans (le_max_left M₀ 0))
    (fun q hq ↦ (hN₀ q hq).trans (le_max_left N₀ 0)) hlam ?_
  have hle : N * (M + 1) ≤ min 1 c * lam := by
    have : min 1 c * lam = N * (M + 1) + min 1 c := by
      change min 1 c * (N * (M + 1) / min 1 c + 1) = _
      rw [mul_add, mul_div_cancel₀ _ hm.ne', mul_one]
    linarith
  calc lam⁻¹ * N * (M + 1) = lam⁻¹ * (N * (M + 1)) := by ring
    _ ≤ lam⁻¹ * (min 1 c * lam) := mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hlam.le)
    _ = min 1 c := by field_simp

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
open Classical in
/-- Updating a map continuous on `Ω \ {z₀}` at `z₀` to its limit there gives a map continuous on
`Ω`, with values in `K` if the map and the limit lie in `K`. -/
private theorem continuousOn_update_mapsTo {q : V} (hu : ContinuousOn u (Ω \ {z₀}))
    (huK : MapsTo u (Ω \ {z₀}) K) (hqK : q ∈ K) (hlim : Tendsto u (𝓝[≠] z₀) (𝓝 q)) :
    ContinuousOn (Function.update u z₀ q) Ω ∧ MapsTo (Function.update u z₀ q) Ω K := by
  refine ⟨continuousOn_update_iff.2 ⟨hu, fun _ ↦
    hlim.mono_left (nhdsWithin_mono _ (sdiff_subset_compl _ _))⟩, fun z hz ↦ ?_⟩
  by_cases hzz : z = z₀
  · subst z
    simpa using hqK
  · simpa [Function.update_of_ne hzz] using huK ⟨hz, hzz⟩

open Classical in
/-- **Continuous removal of a finite-energy puncture for Floer solutions.** Let `J` and `X` be `C²`
on an open set `W ⊆ ℂ × V` containing `Ω × K`, for an open neighbourhood `Ω` of `z₀` and a compact
`K ⊆ V`, with `J(z, x)² = -1` on `Ω × K`. Let `ω(·, J₀ ·)` be the inner product of `V`. Let `u` be
`C³` on `Ω \ {z₀}` with image in `K`, solving `∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)`, such
that `ω` tames `J(z, u z)` with a uniform constant `c > 0` and the energy `∫_Ω ‖∂ₛu‖²` is finite.
Then `u` has a limit `q ∈ K` at `z₀`, and updating `u` at `z₀` to `q` gives a continuous map on
`Ω` with image in `K`. -/
theorem exists_continuousOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (hΩKW : Ω ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (Ω \ {z₀}))
    (hfl : ∀ z ∈ Ω \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (Ω \ {z₀}) K)
    (htame : ∀ z ∈ Ω \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) Ω) :
    ∃ q ∈ K, Tendsto u (𝓝[≠] z₀) (𝓝 q) ∧
      ContinuousOn (Function.update u z₀ q) Ω ∧ MapsTo (Function.update u z₀ q) Ω K := by
  obtain ⟨q, hqK, hlim, -⟩ := exists_tendsto_memLp_fderiv_of_finite_energy hg hc hW hJ hX hK hΩ
    hz₀ hΩKW hJsq hu hfl huK htame henergy
  exact ⟨q, hqK, hlim, continuousOn_update_mapsTo hu.continuousOn huK hqK hlim⟩

open Classical in
/-- **Weak differentiability across a finite-energy puncture for Floer solutions.** Under the
hypotheses of `TauCeti.Floer.exists_continuousOn_update_of_finite_energy`, the continuous extension
of `u` across `z₀` is weakly differentiable on `Ω`, with weak derivative the classical differential
of `u` off `z₀`, and this differential lies in `Lᵖ` on a disc about `z₀` for some `p > 2`. No
differentiability at `z₀` is asserted. -/
theorem exists_hasWeakFDerivOn_update_of_finite_energy
    (hg : ∀ v w, ω v (J₀ w) = inner ℝ v w) (hc : 0 < c)
    (hW : IsOpen W) (hJ : ContDiffOn ℝ 2 J W) (hX : ContDiffOn ℝ 2 X W)
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω) (hΩKW : Ω ×ˢ K ⊆ W)
    (hJsq : ∀ z ∈ Ω, ∀ x ∈ K, ∀ v, J (z, x) (J (z, x) v) = -v)
    (hu : ContDiffOn ℝ 3 u (Ω \ {z₀}))
    (hfl : ∀ z ∈ Ω \ {z₀},
      fderiv ℝ u z I - X (z, u z) I = J (z, u z) (fderiv ℝ u z 1 - X (z, u z) 1))
    (huK : MapsTo u (Ω \ {z₀}) K)
    (htame : ∀ z ∈ Ω \ {z₀}, ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (z, u z) v))
    (henergy : IntegrableOn (fun z ↦ ‖fderiv ℝ u z 1‖ ^ 2) Ω) :
    ∃ q ∈ K, ContinuousOn (Function.update u z₀ q) Ω ∧ MapsTo (Function.update u z₀ q) Ω K ∧
      HasWeakFDerivOn volume ⟨Ω, hΩ⟩ (Function.update u z₀ q) (fderiv ℝ u) ∧
      ∃ ε > 0, ball z₀ ε ⊆ Ω ∧ ∃ p : ℝ, 2 < p ∧
        MemLp (fderiv ℝ u) (ENNReal.ofReal p) (volume.restrict (ball z₀ ε)) := by
  obtain ⟨q, hqK, hlim, ε, hε, hεΩ, p, hp, hmem⟩ := exists_tendsto_memLp_fderiv_of_finite_energy
    hg hc hW hJ hX hK hΩ hz₀ hΩKW hJsq hu hfl huK htame henergy
  obtain ⟨hcont, hmaps⟩ := continuousOn_update_mapsTo hu.continuousOn huK hqK hlim
  have hP : IsOpen (Ω \ {z₀}) := hΩ.sdiff isClosed_singleton
  -- The differential is integrable near `z₀` by higher integrability, and continuous elsewhere.
  have hloc : LocallyIntegrableOn (fderiv ℝ u) Ω := by
    intro x hx
    by_cases hxz : x = z₀
    · subst x
      have : IsFiniteMeasure (volume.restrict (ball z₀ ε)) :=
        ⟨by simpa using measure_ball_lt_top⟩
      exact ⟨ball z₀ ε, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z₀ hε),
        hmem.integrable (by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))⟩
    · have h := (hu.continuousOn_fderiv_of_isOpen hP (by norm_num)).integrableAt_nhdsWithin
        (μ := volume) hP.measurableSet ⟨hx, hxz⟩
      rwa [sdiff_eq, nhdsWithin_inter_of_mem'
        (mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hxz))] at h
  refine ⟨q, hqK, hcont, hmaps, hasWeakFDerivOn_of_hasFDerivAt_off_countable
    (countable_singleton z₀) hcont hloc fun z hz ↦ ?_, ε, hε, hεΩ, p, hp, hmem⟩
  have hdu := ((hu.differentiableOn (by norm_num)) z hz).differentiableAt (hP.mem_nhds hz)
  have heq : Function.update u z₀ q =ᶠ[𝓝 z] u := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hz.2] with w hw
    exact Function.update_of_ne hw _ _
  exact hdu.hasFDerivAt.congr_of_eventuallyEq heq

end TauCeti.Floer
