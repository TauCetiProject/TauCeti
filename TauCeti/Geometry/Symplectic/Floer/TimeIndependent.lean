/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.FlowExistence
public import TauCeti.Dynamics.Flow.Stable
public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Geometry.Symplectic.Hamiltonian.Standard

/-!
# Time-independent Floer solutions are gradient lines

Let `(V, ω)` be a symplectic vector space, `J` an almost complex structure and `H : V → ℝ` an
autonomous Hamiltonian. For the cylindrical perturbation `K = H dt`, the Floer equation for a
map `u` of the strip `(s, t)` reads `∂_s u + J (∂_t u - X_H(u)) = 0`. A solution that does not
depend on `t`, `u(s, t) = γ(s)`, therefore solves the ordinary differential equation
`γ' = J X_H(γ)`. When `ω` is `J`-invariant, `J X_H` is the gradient of `H` for the bilinear form
`g = ω(·, J ·)`, so the time-independent Floer solutions are exactly the gradient lines of `H`
for `g`, and their Floer energy density is `dH(γ(s)) γ'(s)`.

In the cotangent model `V × V` of a Euclidean space `V`, with its standard symplectic form
`ω₀ = Σ dqᵢ ∧ dpᵢ` and complex structure `J(q, p) = (-p, q)`, take `H(q, p) = h(q)`. Then
`J X_H(q, p) = (∇h(q), 0)`. A map `γ = (q, p)` is a time-independent Floer solution with boundary
on the zero section `p = 0` exactly when `q` is an upward gradient line of `h`, that is, when
`q(s) = φ₋ₛ(q(0))` for the negative gradient flow `φ` of `h`. Such a solution runs from `(a, 0)`
at `s → -∞` to `(b, 0)` at `s → +∞` exactly when `q(0)` lies in the stable set of `a` and the
unstable set of `b` for `φ`. So the time-independent Floer strips between the zero section and
itself, perturbed by `h`, are parametrized by the Morse trajectory spaces of `h`. Their energy
density is `‖∇h(q)‖²`.

This is the elementary half of Floer's comparison of the Floer complex of the zero section and its
Hamiltonian image, the graph of `-dh`, with the Morse complex of `h`. The other half, that for
`C²`-small `h` every finite-energy Floer strip is time-independent, is not proved here, and neither
is the passage from the perturbed equation to holomorphic strips between the two Lagrangians.

## Main results

* `TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_fst_iff`: a time-independent
  map solves the Floer equation for `K = H dt` exactly when `γ' = J X_H(γ)`.
* `TauCeti.SymplecticForm.Invariant.isComplexLinearMap_perturbedFDeriv_comp_fst_iff`: for a
  `J`-invariant form, exactly when `γ'` is the gradient of `H` for `g = ω(·, J ·)`.
* `TauCeti.SymplecticForm.floerEnergyDensity_comp_fst`: the energy density of a time-independent
  map is `dH(γ(s)) γ'(s)`.
* `TauCeti.isComplexLinearMap_perturbedFDeriv_comp_fst_iff_hasDerivAt`: in the cotangent model,
  a time-independent map solves the Floer equation exactly when `γ' = (∇h(q), 0)`.
* `TauCeti.floerEnergyDensity_comp_fst_eq_norm_gradient_sq`: in the cotangent model, the energy
  density of a time-independent solution is `‖∇h(q)‖²`.
* `TauCeti.isComplexLinearMap_perturbedFDeriv_comp_fst_and_snd_eq_zero_iff`: time-independent
  Floer solutions with boundary on the zero section are the reversed negative gradient
  trajectories.
* `TauCeti.tendsto_atBot_and_tendsto_atTop_iff_mem_stableSet_inter_unstableSet`: their limits
  at the two ends are read off from the stable and unstable sets of the gradient flow.

## References

* A. Floer, *Witten's complex and infinite dimensional Morse theory*, J. Differential Geom.
  **30** (1989), 207–221 (time-independent solutions of the Floer equation and the comparison
  with the Morse complex).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 10 (solutions of the Floer equation independent of `t` are gradient trajectories).
-/

public section

open Filter Topology
open scoped Gradient NNReal

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J : AlmostComplexStructure V} {H : V → ℝ} {γ : ℝ → V} {z : ℝ × ℝ}

/-- The perturbed derivative of a time-independent map `(s, t) ↦ γ(s)` for `K = H dt` sends
`(a, b)` to `a γ'(s) - b X_H(γ(s))`. -/
private theorem perturbedFDeriv_comp_fst_apply (hγ : DifferentiableAt ℝ γ z.1) (v : ℝ × ℝ) :
    ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z v =
      v.1 • deriv γ z.1 - v.2 • ω.hamiltonianVectorField H (γ z.1) := by
  have h : HasFDerivAt (fun w : ℝ × ℝ ↦ γ w.1)
      ((fderiv ℝ γ z.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) z :=
    hγ.hasFDerivAt.comp z hasFDerivAt_fst
  rw [perturbedFDeriv_apply, h.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ← fderiv_apply_one_eq_deriv, ← map_smul, smul_eq_mul, mul_one,
    hamiltonianVectorField_const]
  simp

/-- **Time-independent Floer solutions.** For the cylindrical perturbation `K = H dt` of an
autonomous Hamiltonian, the map `(s, t) ↦ γ(s)` solves the Floer equation at `z` exactly when
`γ'(s) = J X_H(γ(s))`, where `s = z.1`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_fst_iff (hγ : DifferentiableAt ℝ γ z.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z : ℝ × ℝ →ₗ[ℝ] V) ↔
      deriv γ z.1 = J (ω.hamiltonianVectorField H (γ z.1)) := by
  rw [isComplexLinearMap_stdComplexLine_iff, ContinuousLinearMap.coe_coe,
    perturbedFDeriv_comp_fst_apply hγ, perturbedFDeriv_comp_fst_apply hγ]
  simp only [stdComplexLineImag_fst, stdComplexLineImag_snd, stdComplexLineReal_fst,
    stdComplexLineReal_snd, zero_smul, one_smul, zero_sub, sub_zero]
  -- `-X_H = J γ'` and `γ' = J X_H` are equivalent since `J² = -1`.
  constructor
  · intro h
    have hJ := congrArg J h
    rw [map_neg, AlmostComplexStructure.apply_apply] at hJ
    exact (neg_inj.mp hJ).symm
  · intro h
    rw [h, AlmostComplexStructure.apply_apply]

/-- **Time-independent Floer solutions are gradient lines.** For a `J`-invariant symplectic form
and the perturbation `K = H dt`, the map `(s, t) ↦ γ(s)` solves the Floer equation at `z` exactly
when `γ'(s)` is the gradient of `H` at `γ(s)` for the bilinear form `g = ω(·, J ·)`. -/
theorem Invariant.isComplexLinearMap_perturbedFDeriv_comp_fst_iff (hJ : ω.Invariant J)
    (hγ : DifferentiableAt ℝ γ z.1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z : ℝ × ℝ →ₗ[ℝ] V) ↔
      ∀ w, ω.associatedBilinForm J (deriv γ z.1) w = fderiv ℝ H (γ z.1) w := by
  rw [SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_fst_iff hγ]
  refine ⟨fun h w ↦ h ▸ hJ.associatedBilinForm_hamiltonianVectorField H _ w, fun h ↦ ?_⟩
  -- Both vectors are `g`-gradients of `H`, and `g` is nondegenerate.
  rw [← sub_eq_zero]
  refine (ω.associatedBilinForm_nondegenerate J).1 _ fun w ↦ ?_
  rw [map_sub, LinearMap.sub_apply, h, hJ.associatedBilinForm_hamiltonianVectorField, sub_self]

/-- **The energy density of a time-independent map.** For the perturbation `K = H dt`, the Floer
energy density of `(s, t) ↦ γ(s)` at `z` is `fderiv ℝ H (γ(s)) (γ'(s))`. When `H` is
differentiable at `γ(s)`, this is the derivative of `H ∘ γ` at `s`. -/
theorem floerEnergyDensity_comp_fst (hγ : DifferentiableAt ℝ γ z.1) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ ↦ H) (fun w ↦ γ w.1) z =
      fderiv ℝ H (γ z.1) (deriv γ z.1) := by
  simp only [floerEnergyDensity_def, perturbedFDeriv_comp_fst_apply hγ, stdComplexLineReal_fst,
    stdComplexLineReal_snd, stdComplexLineImag_fst, stdComplexLineImag_snd, zero_smul, one_smul,
    zero_sub, sub_zero]
  calc ω (deriv γ z.1) (-ω.hamiltonianVectorField H (γ z.1))
      = -ω (deriv γ z.1) (ω.hamiltonianVectorField H (γ z.1)) := map_neg (ω.toBilinForm _) _
    _ = fderiv ℝ H (γ z.1) (deriv γ z.1) := by rw [ω.neg_eq, apply_hamiltonianVectorField]

end SymplecticForm

open SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {h : V → ℝ}

/-- **Time-independent Floer solutions in the cotangent model.** For `H(q, p) = h(q)` on `V × V`
with the standard symplectic and complex structures, the map `(s, t) ↦ γ(s)` solves the Floer
equation for `K = H dt` at `z` exactly when `γ'(s) = (∇h(q(s)), 0)`, where `γ(s) = (q(s), p(s))`
and `s = z.1`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_fst_iff_hasDerivAt {γ : ℝ → V × V} {z : ℝ × ℝ}
    (hγ : DifferentiableAt ℝ γ z.1) (hh : DifferentiableAt ℝ h (γ z.1).1) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (AlmostComplexStructure.product V)
        ((stdSymplecticForm (V := V)).perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ h y.1)
          (fun w ↦ γ w.1) z : ℝ × ℝ →ₗ[ℝ] V × V) ↔
      HasDerivAt γ (∇ h (γ z.1).1, 0) z.1 := by
  rw [SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_fst_iff hγ,
    stdSymplecticForm_hamiltonianVectorField_comp_fst hh, AlmostComplexStructure.product_apply]
  refine ⟨fun hd ↦ ?_, fun hd ↦ ?_⟩
  · simpa [hd] using hγ.hasDerivAt
  · simp [hd.deriv]

/-- **The energy density of a time-independent solution in the cotangent model.** If
`γ'(s) = (∇h(q(s)), 0)`, then the Floer energy density of `(s, t) ↦ γ(s)` for `H(q, p) = h(q)`
is `‖∇h(q(s))‖²`. -/
theorem floerEnergyDensity_comp_fst_eq_norm_gradient_sq {γ : ℝ → V × V} {z : ℝ × ℝ}
    (hγ : HasDerivAt γ (∇ h (γ z.1).1, 0) z.1) (hh : DifferentiableAt ℝ h (γ z.1).1) :
    (stdSymplecticForm (V := V)).floerEnergyDensity (fun _ _ ↦ 0) (fun _ y ↦ h y.1)
        (fun w ↦ γ w.1) z = ‖∇ h (γ z.1).1‖ ^ 2 := by
  have hcomp : HasFDerivAt (fun y : V × V ↦ h y.1)
      ((fderiv ℝ h (γ z.1).1).comp (ContinuousLinearMap.fst ℝ V V)) (γ z.1) :=
    hh.hasFDerivAt.comp (γ z.1) hasFDerivAt_fst
  rw [SymplecticForm.floerEnergyDensity_comp_fst hγ.differentiableAt, hγ.deriv, hcomp.fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ← inner_gradient_left,
    real_inner_self_eq_norm_sq]

/-- **Time-independent Floer strips on the zero section are gradient lines.** Let `h` be
differentiable with globally Lipschitz gradient, and let `φ` be its negative gradient flow. For
`H(q, p) = h(q)` on `V × V`, a map `(s, t) ↦ γ(s)` is a differentiable solution of the Floer
equation for `K = H dt` with boundary on the zero section `p = 0` exactly when
`γ(s) = (φ₋ₛ(q₀), 0)` for every `s`, where `q₀` is the position of `γ(0)`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_fst_and_snd_eq_zero_iff
    (hd : Differentiable ℝ h) {K : ℝ≥0} (hf : LipschitzWith K (∇ h)) {γ : ℝ → V × V} :
    (Differentiable ℝ γ ∧
        (∀ z : ℝ × ℝ, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (AlmostComplexStructure.product V)
          ((stdSymplecticForm (V := V)).perturbedFDeriv (fun _ _ ↦ 0) (fun _ y ↦ h y.1)
            (fun w ↦ γ w.1) z : ℝ × ℝ →ₗ[ℝ] V × V)) ∧
        ∀ s, (γ s).2 = 0) ↔
      ∀ s, γ s = (negativeGradientFlow h hf (-s) (γ 0).1, 0) := by
  have hφ := (isNegativeGradient_negativeGradientFlow h hf).isIntegralCurve
  constructor
  · rintro ⟨hγ, hF, h0⟩ s
    -- The position, run backwards, is a negative gradient trajectory.
    have hq : IsIntegralCurve (fun τ ↦ (γ (-τ)).1) fun _ y ↦ -∇ h y := fun τ ↦ by
      have hγτ : HasDerivAt γ (∇ h (γ (-τ)).1, 0) (-τ) :=
        (isComplexLinearMap_perturbedFDeriv_comp_fst_iff_hasDerivAt (z := (-τ, 0))
          (hγ _) (hd _)).mp (hF _)
      have hqτ := (hasFDerivAt_fst.comp_hasDerivAt (-τ) hγτ).scomp τ (hasDerivAt_neg τ)
      simpa [Function.comp_def] using hqτ
    have := eq_negativeGradientFlow h hf hq (-s)
    simp only [neg_neg, neg_zero] at this
    exact Prod.ext this (h0 s)
  · intro hγ
    -- Along the orbit, `s ↦ (φ₋ₛ q₀, 0)` has velocity `(∇h, 0)`.
    have hderiv : ∀ s, HasDerivAt γ (∇ h (γ s).1, 0) s := fun s ↦ by
      have h1 : HasDerivAt (fun s ↦ negativeGradientFlow h hf (-s) (γ 0).1)
          (∇ h (negativeGradientFlow h hf (-s) (γ 0).1)) s := by
        simpa [Function.comp_def] using (hφ (γ 0).1 (-s)).scomp s (hasDerivAt_neg s)
      rw [hγ s]
      exact HasDerivAt.congr_of_eventuallyEq (h1.prodMk (hasDerivAt_const s (0 : V)))
        (Filter.EventuallyEq.of_eq (funext hγ))
    refine ⟨fun s ↦ (hderiv s).differentiableAt, fun z ↦ ?_, fun s ↦ by rw [hγ s]⟩
    exact (isComplexLinearMap_perturbedFDeriv_comp_fst_iff_hasDerivAt
      (hderiv z.1).differentiableAt (hd _)).mpr (hderiv z.1)

/-- **The ends of a time-independent Floer strip on the zero section.** A time-independent
Floer strip `γ(s) = (φ₋ₛ(q₀), 0)` converges to `(a, 0)` as `s → -∞` and to `(b, 0)` as
`s → +∞` exactly when `q₀` lies in the stable set of `a` and the unstable set of `b` for the
negative gradient flow `φ` of `h`. So these strips from `a` to `b` are parametrized by the
Morse trajectories of `h` from `b` down to `a`. -/
theorem tendsto_atBot_and_tendsto_atTop_iff_mem_stableSet_inter_unstableSet {K : ℝ≥0}
    (hf : LipschitzWith K (∇ h)) {γ : ℝ → V × V}
    (hγ : ∀ s, γ s = (negativeGradientFlow h hf (-s) (γ 0).1, 0)) (a b : V) :
    (Tendsto γ atBot (𝓝 (a, 0)) ∧ Tendsto γ atTop (𝓝 (b, 0))) ↔
      (γ 0).1 ∈ Flow.stableSet (negativeGradientFlow h hf) a ∩
        Flow.unstableSet (negativeGradientFlow h hf) b := by
  generalize (γ 0).1 = x at hγ ⊢
  rw [funext hγ, Set.mem_inter_iff, Flow.mem_stableSet, Flow.mem_unstableSet]
  simp only [nhds_prod_eq, tendsto_prod_iff', tendsto_const_nhds, and_true]
  -- Reversing time exchanges the two ends of the strip.
  refine and_congr ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩ ⟨fun ht ↦ ?_, fun ht ↦ ?_⟩
  · simpa [Function.comp_def] using ht.comp tendsto_neg_atTop_atBot
  · simpa [Function.comp_def] using ht.comp tendsto_neg_atBot_atTop
  · simpa [Function.comp_def] using ht.comp tendsto_neg_atBot_atTop
  · simpa [Function.comp_def] using ht.comp tendsto_neg_atTop_atBot

end TauCeti
