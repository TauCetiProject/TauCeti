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
is constant along each orbit. The rest points of the flow are the critical points of the
Hamiltonian, and the flow only sees the Hamiltonian near the orbit: two Hamiltonians that agree
near an orbit segment of one of them move its initial point to the same place. For a `C²`
Hamiltonian, every time map preserves the symplectic form on tangent vectors: differentiating the
pairing of two variations and using symmetry of the Hessian gives zero.

The time maps carry the Hamiltonian vector field to itself
(`TauCeti.SymplecticForm.fderiv_hamiltonianFlow_apply_hamiltonianVectorField`), and the flow of a
`C^(n + 2)` Hamiltonian is `C^(n + 1)` jointly in time and space
(`TauCeti.SymplecticForm.contDiff_uncurry_hamiltonianFlow`). For maps `τ` to times and `k` to
points, the map `q ↦ φ_{τ q} (k q)` pulls `ω` back to the pullback along `k`
corrected by `dτ ∧ d(H ∘ k)` (`TauCeti.SymplecticForm.apply_fderiv_hamiltonianFlow_comp`). A
function whose derivative along the Hamiltonian vector field is a constant `c` on a region grows
at the rate `c` along the pieces of flow lines in that region
(`TauCeti.SymplecticForm.apply_hamiltonianFlow_eq_add_mul`). The derivative at varying time and the
constant-rate statement specialize `TauCeti.hasFDerivAt_flowOfLipschitz_comp` and
`TauCeti.apply_flowOfLipschitz_eq_add_mul`.

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

/-- **The rest points of a Hamiltonian flow are the critical points of the Hamiltonian**: `x` is
fixed by every time map exactly when `fderiv ℝ H x = 0`. -/
theorem forall_hamiltonianFlow_apply_eq_self_iff
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (x : V) :
    (∀ t, ω.hamiltonianFlow H hX t x = x) ↔ fderiv ℝ H x = 0 := by
  rw [hamiltonianFlow_eq, forall_flowOfLipschitz_eq_self_iff, hamiltonianVectorField_eq_zero_iff]

/-- **Hamiltonian flows agree where the Hamiltonians agree locally.** If `H` agrees with `H'` near
every point of the orbit segment `{ψ'_τ x | τ ∈ [[0, t]]}` of the flow `ψ'` of `H'`, then the
flow of `H` sends `x` at time `t` to the same point as `ψ'`. -/
theorem hamiltonianFlow_apply_eq_of_eventuallyEq {H' : V → ℝ} {K' : ℝ≥0}
    (hX : LipschitzWith K (ω.hamiltonianVectorField H))
    (hX' : LipschitzWith K' (ω.hamiltonianVectorField H')) {x : V} {t : ℝ}
    (h : ∀ τ ∈ Set.uIcc 0 t, H =ᶠ[nhds (ω.hamiltonianFlow H' hX' τ x)] H') :
    ω.hamiltonianFlow H hX t x = ω.hamiltonianFlow H' hX' t x :=
  flowOfLipschitz_apply_eq_of_eqOn hX hX' fun τ hτ ↦
    ω.hamiltonianVectorField_congr_of_eventuallyEq (h τ hτ)

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

/-- The flow of a `C^(n + 2)` Hamiltonian is `C^(n + 1)` jointly in time and space; for `n = ∞`,
the flow of a smooth Hamiltonian is smooth. -/
theorem contDiff_uncurry_hamiltonianFlow (n : ℕ∞)
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ (n + 2) H) :
    ContDiff ℝ (n + 1) (Function.uncurry fun t x ↦ ω.hamiltonianFlow H hX t x) := by
  induction n using ENat.recTopCoe with
  | top =>
    refine contDiff_infty.2 fun n ↦ ?_
    rw [hamiltonianFlow_eq]
    exact (contDiff_flowOfLipschitz n _ hX (ω.contDiff_hamiltonianVectorField
      (hH.of_le ((WithTop.coe_le_coe.2 le_top).trans le_self_add)))).of_le le_self_add
  | coe n =>
    rw [hamiltonianFlow_eq]
    exact contDiff_flowOfLipschitz n _ hX
      (ω.contDiff_hamiltonianVectorField (by exact_mod_cast hH))

/-- The derivative of `q ↦ φ_{τ q} (k q)`, where `φ` is the flow of a `C²` Hamiltonian with
globally Lipschitz vector field. -/
theorem hasFDerivAt_hamiltonianFlow_comp {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) (hH : ContDiff ℝ 2 H)
    {τ : P → ℝ} {k : P → V} {τ' : P →L[ℝ] ℝ} {k' : P →L[ℝ] V} {p : P}
    (hτ : HasFDerivAt τ τ' p) (hk : HasFDerivAt k k' p) :
    HasFDerivAt (fun q ↦ ω.hamiltonianFlow H hX (τ q) (k q))
      (τ'.smulRight (ω.hamiltonianVectorField H (ω.hamiltonianFlow H hX (τ p) (k p))) +
        (fderiv ℝ (ω.hamiltonianFlow H hX (τ p)) (k p)).comp k') p := by
  rw [hamiltonianFlow_eq]
  exact hasFDerivAt_flowOfLipschitz_comp hX (ω.contDiff_hamiltonianVectorField hH) hτ hk

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
  rw [mul_comm, ← smul_eq_mul]
  exact apply_flowOfLipschitz_eq_add_mul hX hF hc hy

/-- **A first integral up to a constant rate, near a point.** If the derivative of `F` along the
Hamiltonian vector field of `H` is the constant `c` near `x₀`, then for some `δ > 0` and every
point `z` near `x₀`, `F (φ_t z) = F z + c t` for `t ∈ (-δ, δ)`. -/
theorem exists_pos_eventually_apply_hamiltonianFlow_eq_add_mul
    (hX : LipschitzWith K (ω.hamiltonianVectorField H)) {F : V → ℝ} {c : ℝ} {x₀ : V}
    (hc : ∀ᶠ z in nhds x₀,
      DifferentiableAt ℝ F z ∧ fderiv ℝ F z (ω.hamiltonianVectorField H z) = c) :
    ∃ δ > 0, ∀ᶠ z in nhds x₀, ∀ t ∈ Set.Ioo (-δ) δ,
      F (ω.hamiltonianFlow H hX t z) = F z + c * t := by
  rw [hamiltonianFlow_eq]
  simpa only [smul_eq_mul, mul_comm] using
    exists_pos_eventually_apply_flowOfLipschitz_eq_add_mul hX hc

end TauCeti.SymplecticForm
