/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Basic
public import TauCeti.Dynamics.Flow.Variational
import TauCeti.Dynamics.Flow.LieBracket
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Autonomous Hamiltonian flows

A globally Lipschitz Hamiltonian vector field on a finite-dimensional symplectic vector space
has a canonical global flow. This applies in particular to every `C²` Hamiltonian with compact
support (`TauCeti.SymplecticForm.exists_lipschitzWith_hamiltonianVectorField`). The Hamiltonian
is constant along each orbit. For a `C²` Hamiltonian, every time map preserves the symplectic
form on tangent vectors: differentiating the pairing of two variations and using symmetry of the
Hessian gives zero.

The time maps carry the Hamiltonian vector field to itself
(`TauCeti.SymplecticForm.fderiv_hamiltonianFlow_apply_hamiltonianVectorField`), and the flow of a
`C^(n + 2)` Hamiltonian is `C^(n + 1)` jointly in time and space
(`TauCeti.SymplecticForm.contDiff_uncurry_hamiltonianFlow`). Consequently, for maps `τ` to times
and `k` to points, the map `q ↦ φ_{τ q} (k q)` pulls `ω` back to the pullback along `k`
corrected by `dτ ∧ d(H ∘ k)` (`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow_comp`). A
function whose derivative along the Hamiltonian vector field is a constant `c` on a region grows
at the rate `c` along the pieces of flow lines in that region
(`TauCeti.SymplecticForm.apply_hamiltonianFlow_eq_add_mul`).

The construction and variational equation reuse `TauCeti.flowOfLipschitz`.
See McDuff--Salamon, *Introduction to Symplectic Topology*, Hamiltonian flows.
-/

public section

open scoped NNReal

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) (H : V → ℝ) {K : ℝ≥0}

/-- The autonomous Hamiltonian flow, defined for all real times when its vector field is
globally Lipschitz. -/
noncomputable def hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H)) :
    Flow ℝ V :=
  flowOfLipschitz (ω.hamiltonianVectorField H) hX

/-- The Hamiltonian flow is the canonical Lipschitz flow of its Hamiltonian vector field. -/
theorem hamiltonianFlow_eq (hX : LipschitzWith K (ω.hamiltonianVectorField H)) :
    ω.hamiltonianFlow H hX = flowOfLipschitz (ω.hamiltonianVectorField H) hX := (rfl)

/-- Hamiltonian orbits solve Hamilton's differential equation. -/
theorem hasDerivAt_hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (x : V) (t : ℝ) :
    HasDerivAt (fun s ↦ ω.hamiltonianFlow H hX s x)
      (ω.hamiltonianVectorField H (ω.hamiltonianFlow H hX t x)) t :=
  hasDerivAt_flowOfLipschitz hX x t

/-- An autonomous Hamiltonian is conserved by its flow. Where `H` is not differentiable, its
Hamiltonian vector field vanishes by convention, so the orbit is a rest point. -/
theorem hamiltonianFlow_conserves (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (t : ℝ) (x : V) : H (ω.hamiltonianFlow H hX t x) = H x := by
  by_cases hz : ∃ s, ω.hamiltonianVectorField H (ω.hamiltonianFlow H hX s x) = 0
  · -- The orbit through `x` meets a rest point, hence it is constant.
    obtain ⟨s, hs⟩ := hz
    rw [hamiltonianFlow_eq] at hs ⊢
    rw [flowOfLipschitz_eq_self_of_vectorField_flow_eq_zero hX hs t]
  · push Not at hz
    have hdiff (s : ℝ) : DifferentiableAt ℝ H (ω.hamiltonianFlow H hX s x) := by
      by_contra h
      exact hz s ((ω.hamiltonianVectorField_eq_zero_iff H _).2
        (fderiv_zero_of_not_differentiableAt h))
    have hd (s : ℝ) : HasDerivAt (fun s ↦ H (ω.hamiltonianFlow H hX s x)) 0 s := by
      convert (hdiff s).hasFDerivAt.comp_hasDerivAt s
        (ω.hasDerivAt_hamiltonianFlow H hX x s) using 1
      · rfl
      · simp
    have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
      (fun s ↦ (hd s).deriv) t 0
    simpa using hc

/-- The time maps of a globally Lipschitz Hamiltonian flow are `C^(n+1)` when the
Hamiltonian is `C^(n+2)`. -/
theorem contDiff_hamiltonianFlow_apply (n : ℕ)
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ (n + 2) H)
    (t : ℝ) : ContDiff ℝ (n + 1) (ω.hamiltonianFlow H hX t) :=
  contDiff_flowOfLipschitz_apply n _ hX
    (ω.contDiff_hamiltonianVectorField
      (by simpa only [add_assoc, one_add_one_eq_two] using hH)) t

/-- Each time map of a `C²` Hamiltonian flow preserves the symplectic form on tangent
vectors. No nondegeneracy of the Hessian is required. -/
@[simp]
theorem apply_fderiv_hamiltonianFlow (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (hH : ContDiff ℝ 2 H) (t : ℝ) (x u v : V) :
    ω (fderiv ℝ (ω.hamiltonianFlow H hX t) x u)
      (fderiv ℝ (ω.hamiltonianFlow H hX t) x v) = ω u v := by
  have hXs : ContDiff ℝ 1 (ω.hamiltonianVectorField H) :=
    ω.contDiff_hamiltonianVectorField hH
  have hd (s : ℝ) : HasDerivAt
      (fun s ↦ ω (fderiv ℝ (ω.hamiltonianFlow H hX s) x u)
        (fderiv ℝ (ω.hamiltonianFlow H hX s) x v)) 0 s := by
    have hu := hasDerivAt_fderiv_flowOfLipschitz_apply hX hXs x u s
    have hv := hasDerivAt_fderiv_flowOfLipschitz_apply hX hXs x v s
    have hp := ω.toBilinForm.toContinuousBilinearMap.hasDerivAt_of_bilinear
      (fun _ ↦ hu) (fun _ ↦ hv)
    convert hp using 1
    · rfl
    · simpa only [hamiltonianFlow_eq, LinearMap.toContinuousBilinearMap_apply, add_comm] using
        (ω.apply_fderiv_hamiltonianVectorField_add hH.contDiffAt
          (fderiv ℝ (ω.hamiltonianFlow H hX s) x u)
          (fderiv ℝ (ω.hamiltonianFlow H hX s) x v)).symm
  have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd s).differentiableAt)
    (fun s ↦ (hd s).deriv) t 0
  simpa using hc

/-- The time-`t` map of a Hamiltonian flow carries the Hamiltonian vector field to itself. -/
theorem fderiv_hamiltonianFlow_apply_hamiltonianVectorField
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H) (t : ℝ) (x : V) :
    fderiv ℝ (ω.hamiltonianFlow H hX t) x (ω.hamiltonianVectorField H x) =
      ω.hamiltonianVectorField H (ω.hamiltonianFlow H hX t x) := by
  have hXs : ContDiff ℝ 1 (ω.hamiltonianVectorField H) := ω.contDiff_hamiltonianVectorField hH
  rw [hamiltonianFlow_eq]
  exact fderiv_flowOfLipschitz_apply_of_lieBracket_eq_zero hX hXs (hXs.differentiable one_ne_zero)
    VectorField.lieBracket_self t x

/-- The time maps of the flow of a `C²` Hamiltonian are differentiable. -/
theorem differentiable_hamiltonianFlow_apply
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H) (t : ℝ) :
    Differentiable ℝ (ω.hamiltonianFlow H hX t) := by
  rw [hamiltonianFlow_eq]
  exact differentiable_flowOfLipschitz_apply hX (ω.contDiff_hamiltonianVectorField hH) t

/-- The flow of a `C^(n + 2)` Hamiltonian is `C^(n + 1)` jointly in time and space. -/
theorem contDiff_uncurry_hamiltonianFlow (n : ℕ)
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ (n + 2) H) :
    ContDiff ℝ (n + 1) (Function.uncurry fun t x ↦ ω.hamiltonianFlow H hX t x) := by
  rw [hamiltonianFlow_eq]
  exact contDiff_flowOfLipschitz n _ hX
    (ω.contDiff_hamiltonianVectorField (by simpa only [add_assoc, one_add_one_eq_two] using hH))

/-- The derivative of `q ↦ φ_{τ q} (k q)`, where `φ` is the flow of a `C²` Hamiltonian with
globally Lipschitz vector field. -/
theorem hasFDerivAt_hamiltonianFlow_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H)
    {τ : P → ℝ} {k : P → V} {τ' : P →L[ℝ] ℝ} {k' : P →L[ℝ] V} {p : P}
    (hτ : HasFDerivAt τ τ' p) (hk : HasFDerivAt k k' p) :
    HasFDerivAt (fun q ↦ ω.hamiltonianFlow H hX (τ q) (k q))
      (τ'.smulRight (ω.hamiltonianVectorField H (ω.hamiltonianFlow H hX (τ p) (k p))) +
        (fderiv ℝ (ω.hamiltonianFlow H hX (τ p)) (k p)).comp k') p := by
  set Φ := ω.hamiltonianFlow H hX
  have hU : ContDiff ℝ 1 (Function.uncurry fun t x ↦ Φ t x) := by
    simpa using ω.contDiff_uncurry_hamiltonianFlow H 0 hX (by simpa using hH)
  set D := fderiv ℝ (Function.uncurry fun t x ↦ Φ t x) (τ p, k p)
  have hD : HasFDerivAt (Function.uncurry fun t x ↦ Φ t x) D (τ p, k p) :=
    (hU.differentiable one_ne_zero _).hasFDerivAt
  -- The derivative in the time direction is the Hamiltonian vector field.
  have h₁ : D.comp (ContinuousLinearMap.inl ℝ ℝ V) =
      ContinuousLinearMap.toSpanSingleton ℝ (ω.hamiltonianVectorField H (Φ (τ p) (k p))) := by
    have h' := hD.comp (τ p) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (τ p) (k p))
    have h : HasFDerivAt (fun t ↦ Φ t (k p)) (D.comp (ContinuousLinearMap.inl ℝ ℝ V)) (τ p) := h'
    exact h.unique (ω.hasDerivAt_hamiltonianFlow H hX (k p) (τ p)).hasFDerivAt
  -- The derivative in the space direction is that of the time map.
  have h₂ : D.comp (ContinuousLinearMap.inr ℝ ℝ V) = fderiv ℝ (Φ (τ p)) (k p) := by
    have h' := hD.comp (k p) (hasFDerivAt_prodMk_right (𝕜 := ℝ) (τ p) (k p))
    have h : HasFDerivAt (Φ (τ p)) (D.comp (ContinuousLinearMap.inr ℝ ℝ V)) (k p) := h'
    exact h.unique ((ω.differentiable_hamiltonianFlow_apply H hX hH (τ p)) (k p)).hasFDerivAt
  refine (hD.comp p (hτ.prodMk hk)).congr_fderiv ?_
  ext ξ
  have h₃ : D (τ' ξ, k' ξ) = D.comp (ContinuousLinearMap.inl ℝ ℝ V) (τ' ξ) +
      D.comp (ContinuousLinearMap.inr ℝ ℝ V) (k' ξ) := by
    simp [← map_add]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, h₃, h₁, h₂]
  simp [Φ]

/-- The pullback of `ω` along `q ↦ φ_{τ q} (k q)`, where `φ` is the flow of a `C²` Hamiltonian
`H`: it is the pullback along `k`, corrected by `dτ ∧ d(H ∘ k)`. -/
theorem apply_fderiv_hamiltonianFlow_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H)
    {τ : P → ℝ} {k : P → V} {τ' : P →L[ℝ] ℝ} {k' : P →L[ℝ] V} {p : P}
    (hτ : HasFDerivAt τ τ' p) (hk : HasFDerivAt k k' p) (ξ ξ' : P) :
    ω (fderiv ℝ (fun q ↦ ω.hamiltonianFlow H hX (τ q) (k q)) p ξ)
        (fderiv ℝ (fun q ↦ ω.hamiltonianFlow H hX (τ q) (k q)) p ξ') =
      ω (k' ξ) (k' ξ') + τ' ξ * fderiv ℝ H (k p) (k' ξ') -
        τ' ξ' * fderiv ℝ H (k p) (k' ξ) := by
  set Φ := ω.hamiltonianFlow H hX
  set X := ω.hamiltonianVectorField H
  set A := fderiv ℝ (Φ (τ p)) (k p)
  rw [(ω.hasFDerivAt_hamiltonianFlow_comp H hX hH hτ hk).fderiv]
  -- Both tangent vectors are images under `A` of `τ' ζ • X (k p) + k' ζ`.
  have hA (ζ : P) : (τ'.smulRight (X (Φ (τ p) (k p))) + A.comp k') ζ =
      A (τ' ζ • X (k p) + k' ζ) := by
    simp [A, X, Φ, map_add, map_smul, ω.fderiv_hamiltonianFlow_apply_hamiltonianVectorField H hX hH]
  rw [hA, hA, ω.apply_fderiv_hamiltonianFlow H hX hH]
  have h₁ : ω.toBilinForm (X (k p)) (X (k p)) = 0 := ω.self_eq_zero _
  have h₂ (v : V) : ω.toBilinForm (X (k p)) v = fderiv ℝ H (k p) v :=
    ω.apply_hamiltonianVectorField H (k p) v
  have h₃ (v : V) : ω.toBilinForm v (X (k p)) = -fderiv ℝ H (k p) v := by
    rw [← h₂]
    exact (ω.neg_eq (X (k p)) v).symm
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h₁, h₂,
    h₃]
  ring

/-- **A first integral up to a constant rate.** If the derivative of `F` along the Hamiltonian
vector field of `H` is the constant `c` at every point of `R`, and the flow line of `H` through `y`
stays in `R` between the times `0` and `t`, then `F` grows at the rate `c` along it:
`F (φ_t y) = F y + c t`. -/
theorem apply_hamiltonianFlow_eq_add_mul (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    {F : V → ℝ} {R : Set V} {c : ℝ} (hF : ∀ z ∈ R, DifferentiableAt ℝ F z)
    (hc : ∀ z ∈ R, fderiv ℝ F z (ω.hamiltonianVectorField H z) = c) {y : V} {t : ℝ}
    (hy : ∀ s ∈ Set.uIcc 0 t, ω.hamiltonianFlow H hX s y ∈ R) :
    F (ω.hamiltonianFlow H hX t y) = F y + c * t := by
  have hd (s : ℝ) (hs : s ∈ Set.uIcc 0 t) :
      HasDerivAt (fun s ↦ F (ω.hamiltonianFlow H hX s y) - c * s) 0 s := by
    have h₁ : HasDerivAt (fun s ↦ F (ω.hamiltonianFlow H hX s y)) c s := by
      have h := (hF _ (hy s hs)).hasFDerivAt.comp_hasDerivAt s
        (ω.hasDerivAt_hamiltonianFlow H hX y s)
      rw [hc _ (hy s hs)] at h
      exact h
    have h₂ := h₁.fun_sub ((hasDerivAt_id' s).const_mul c)
    rwa [mul_one, sub_self] at h₂
  have h := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0)
    (fun s hs ↦ (hd s hs).hasDerivWithinAt) (fun _ _ ↦ by simp) Set.left_mem_uIcc
    Set.right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
  simp only [mul_zero, sub_zero, Flow.map_zero_apply] at h
  linarith

/-- **A first integral up to a constant rate, near a point.** If the derivative of `F` along the
Hamiltonian vector field of `H` is the constant `c` near `x₀`, then for some `δ > 0` and every
point `z` near `x₀`, `F (φ_t z) = F z + c t` for `t ∈ (-δ, δ)`. -/
theorem exists_pos_eventually_apply_hamiltonianFlow_eq_add_mul
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) {F : V → ℝ} {c : ℝ} {x₀ : V}
    (hc : ∀ᶠ z in nhds x₀,
      DifferentiableAt ℝ F z ∧ fderiv ℝ F z (ω.hamiltonianVectorField H z) = c) :
    ∃ δ > 0, ∀ᶠ z in nhds x₀, ∀ t ∈ Set.Ioo (-δ) δ,
      F (ω.hamiltonianFlow H hX t z) = F z + c * t := by
  obtain ⟨R, hRc, hRo, hx₀R⟩ := mem_nhds_iff.1 hc
  have hpre : (Function.uncurry fun t x ↦ ω.hamiltonianFlow H hX t x) ⁻¹' R ∈
      nhds ((0 : ℝ), x₀) := by
    refine (ω.hamiltonianFlow H hX).cont'.continuousAt.preimage_mem_nhds ?_
    simpa [Function.uncurry, Flow.map_zero_apply] using hRo.mem_nhds hx₀R
  obtain ⟨I, hI, N, hN, hIN⟩ := mem_nhds_prod_iff.1 hpre
  obtain ⟨δ, hδ, hδI⟩ := Metric.mem_nhds_iff.1 hI
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hN] with z hz t ht
  refine ω.apply_hamiltonianFlow_eq_add_mul H hX (fun z hz ↦ (hRc hz).1) (fun z hz ↦ (hRc hz).2)
    fun s hs ↦ hIN (Set.mk_mem_prod (hδI ?_) hz)
  rw [Real.ball_eq_Ioo, zero_sub, zero_add]
  exact Set.ordConnected_Ioo.uIcc_subset ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩ ht hs

end TauCeti.SymplecticForm
