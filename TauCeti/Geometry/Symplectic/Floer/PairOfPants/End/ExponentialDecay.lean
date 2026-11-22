/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence
import TauCeti.Algebra.Ring.Periodic
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.PeriodicOrbit

/-!
# Exponential convergence of the ends of a Floer pair of pants

Let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in a
symplectic vector space `(V, ω)`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q`,
for one-periodic `C³` Hamiltonians `H_q` whose suspended Hamiltonian vector fields are globally
Lipschitz. Let `u` be a `C³` finite-energy solution of the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with image in a compact set `B` in which every one-periodic orbit of
`H_q` is nondegenerate. Suppose that on each end beyond `T₀` the almost complex structure is
cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a one-periodic family `J_q(t, x)` which
is `C²` on an open neighbourhood of `ℝ × B` and tamed by `ω` on `ℝ × B`. By
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` each end loop
`t ↦ u(φ_q(±s, t))` then converges uniformly to a one-periodic orbit `y_q` of `H_q` as `s → ∞`.
This file shows that the convergence is exponentially fast: there are `κ > 0` and `C` with

`‖u(φ_q(±s, t)) - y_q(t)‖ ≤ C exp (-κ s)`

for all large `s` and all `t`. Without the cylindrical assumption, the same estimate holds on an
end that is already known to converge uniformly to a nondegenerate orbit, given only `C²`
regularity of `H_q` and `u` (keeping the Lipschitz assumption), a bound on the `s`-derivative of
`u` in the positive end chart and uniform taming constants on a half-cylinder of that end.

The convergence also holds in `C¹`: on a cylindrical end the derivative of `u` read in the end
chart converges exponentially fast to the derivative `(σ, τ) ↦ τ X_{H_q(t)}(y_q(t))` of the
stationary cylinder `(s, t) ↦ y_q(t)`,

`‖d(u ∘ φ_q)(±s, t) - dt ⊗ X_{H_q(t)}(y_q(t))‖ ≤ C exp (-κ s)`.

Exponential convergence of `u - y_q` and of its derivative on each end are the asymptotic
conditions under which a pair of pants with nondegenerate ends lies in the exponentially weighted
function spaces of the linearized Floer operator, and under which its ends can be pre-glued to
Floer cylinders.

**Nondegeneracy in the positive end chart.** In the positive end chart `φ'_q` the end is a Floer
half-cylinder for the Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`), asymptotic to the orbit `t ↦ y_q(±t)` of `H'_q`. The
half-cylinder estimate `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp` asks the
return map `Ψ'(1)` of the linearized equation `ζ' = S'_t ζ` along this orbit to have no nonzero
fixed vector. On the input ends `H'_q = H_q`, and nondegeneracy of `y_q(0)` as a fixed point of
the time-one map of `H_q` gives this directly
(`TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_apply_eq_self`). On the output end `H'_q` is
the reversed Hamiltonian `-H_q(-t)`, for which time reversal carries nondegeneracy over
(`TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_reverse_apply_eq_self`); together these give
`TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self`.

**`C¹` convergence.** In the positive end chart a cylindrical end is a finite-energy Floer
half-cylinder for `H'_q` and the structure `J'_q(t, x) = J_q(±t, x)`
(`TauCeti.SymplecticForm.floer_comp_positiveEndChart_of_cylindrical`), so the exponential `C¹`
convergence of Floer half-cylinders at a nondegenerate end,
`TauCeti.SymplecticForm.exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp`, applies to
`u ∘ φ'_q`. The end chart is the positive end chart after the reflection `z ↦ ±z`
(`TauCeti.Floer.fderiv_comp_endChart`), and `X_{H'_q(±t)} = ±X_{H_q(t)}`, so the derivative of
`u ∘ φ_q` at `(±s, t)` differs from that of the stationary cylinder of `y_q` by `±` the defect of
`u ∘ φ'_q` at `(s, ±t)`.

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `exists_pos_eventually_norm_sub_le_exp_endChart_of_floer`: an end that converges uniformly to a
  nondegenerate orbit converges exponentially fast, under a bound on the `s`-derivative of
  `u ∘ φ'_q` and uniform taming constants on a half-cylinder of the end.
* `exists_pos_eventually_norm_fderiv_comp_positiveEndChart_sub_le_exp_of_cylindrical`: on a
  cylindrical end converging to a nondegenerate orbit `y`, the derivative of `u ∘ φ'_q` converges
  exponentially fast to that of the stationary cylinder of `t ↦ y(±t)`.
* `exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_cylindrical`: when the
  almost complex structure is cylindrical on the end and all orbits in `B` are nondegenerate, the
  end converges exponentially fast in `C¹` to the stationary cylinder of an orbit, with no bounds
  assumed. Its `C⁰` part is
  `exists_pos_eventually_norm_sub_le_exp_endChart_of_floer_of_cylindrical`.
* `exists_pos_forall_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_cylindrical`: when
  the structure is cylindrical on all three ends, one rate `κ` and one constant `C` serve for all
  of them. Its `C⁰` part is
  `exists_pos_forall_eventually_norm_sub_le_exp_endChart_of_floer_of_cylindrical`.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on exponential decay at nondegenerate ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics of the pair-of-pants product.
-/

public section

open Set Filter Topology Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped ENNReal NNReal Manifold

namespace TauCeti.SymplecticForm

open Floer

section NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {c M : ℝ}

/-- **Nondegeneracy in the positive end chart.** Let `y` be a `1`-periodic orbit of a `1`-periodic
`C²` Hamiltonian `H_q` whose suspended Hamiltonian vector field is globally Lipschitz, and suppose
that `y(0)` is a nondegenerate fixed point of the time-one map of `H_q`. Then the return map of the
linearized equation of the positive end Hamiltonian `H'_q` along the orbit `t ↦ y(±t)` has no
nonzero fixed vector. -/
theorem eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self {q : Puncture}
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q)))
    (hHs : ContDiff ℝ 2 (uncurry (H q))) (hH : Periodic (H q) 1) {y : ℝ → V}
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) (hyper : Periodic y 1)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0))
    {v : V} (hv : dysonSeriesLeft (fun t ↦ fderiv ℝ
      (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (y (q.endSign * t))) 1 v = v) :
    v = 0 := by
  rcases q.endSign_eq_one_or_eq_neg_one with h | h
  · simp only [positiveEndHamiltonian_of_endSign_eq_one H h, h, one_mul] at hv
    exact ω.eq_zero_of_dysonSeriesLeft_apply_eq_self hL hHs hy hnd hv
  -- On the output end `H'_q` is the reversed Hamiltonian `-H_q(-t)`, with the orbit `t ↦ y(-t)`.
  simp only [positiveEndHamiltonian_of_endSign_eq_neg_one H h, h, neg_one_mul] at hv
  refine ω.eq_zero_of_dysonSeriesLeft_reverse_apply_eq_self hL hHs hH hyper.comp_neg
    (fun t ↦ ω.hasDerivAt_comp_neg_of_hasDerivAt_hamiltonianVectorField_neg ?_)
    (by simpa only [neg_zero] using hnd) hv
  simpa only [Pi.neg_def, neg_neg] using hy (-t)

/-- Read in the end chart at `(±s, t)`, the distance of the derivative of `u` from that of the
stationary cylinder of `y` is the distance of the derivative of `u ∘ φ'_q` at `(s, ±t)` from that
of the stationary cylinder of the orbit `t ↦ y(±t)` of `H'_q`. -/
private theorem norm_fderiv_comp_endChart_sub_smulRight (q : Puncture) (u : ℝ × ℝ → V)
    (y : ℝ → V) (s t : ℝ) :
    ‖fderiv ℝ (u ∘ endChart q) (q.endSign * s, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H q t) (y t))‖ =
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, q.endSign * t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField
          (positiveEndHamiltonian H q (q.endSign * t)) (y (q.endSign * (q.endSign * t))))‖ := by
  have hz : q.endSign • ((q.endSign * s, t) : ℝ × ℝ) = (s, q.endSign * t) := by
    simp [← mul_assoc]
  rw [fderiv_comp_endChart, hz, hamiltonianVectorField_positiveEndHamiltonian_endSign_mul,
    endSign_mul_endSign_mul]
  -- The reflection `v ↦ ±v` multiplies both derivatives by the sign of the end.
  have h : q.endSign • fderiv ℝ (u ∘ positiveEndChart q) (s, q.endSign * t) -
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H q t) (y t)) =
        q.endSign • (fderiv ℝ (u ∘ positiveEndChart q) (s, q.endSign * t) -
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
            ((q.endSign • ω.hamiltonianVectorField (H q t)) (y t))) := by
    ext <;> simp [smul_sub, smul_smul]
  rw [h, norm_smul, Real.norm_eq_abs, abs_endSign, one_mul]

/-- **The ends of a Floer pair of pants converge exponentially to nondegenerate orbits.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C²` Hamiltonians `H_q`, and
let `u` be `C²` on `S`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy.
Fix an end `q`, and suppose that on some half-cylinder `s > b` of the positive end chart `φ'_q` the
`s`-derivative `∂_s(u ∘ φ'_q)` is bounded and the almost complex structures are uniformly tame,
`c ‖v‖² ≤ ω(v, J v)` and `‖J v‖ ≤ M ‖v‖`. Suppose that the loops `t ↦ u(φ_q(±s, t))` converge
uniformly, as `s → ∞`, to a `1`-periodic orbit `y` of `H_q` which is nondegenerate: the suspension
of the Hamiltonian vector field of `H_q` is globally Lipschitz and `y(0)` is a nondegenerate fixed
point of the time-one map. Then the convergence is exponentially fast: for some `κ > 0` and `C`,
eventually `‖u(φ_q(±s, t)) - y(t)‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_endChart_of_floer
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 2 (uncurry (H q)))
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) (q : Puncture)
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q))) {y : ℝ → V}
    (hyper : Periodic y 1) (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0))
    (hconv : TendstoUniformly (fun s t ↦ u (endChart q (q.endSign * s, t))) y atTop)
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positiveEndChart q) z (1, 0)‖ ≤ C)
    (hc : 0 < c)
    (hJc : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, c * ‖v‖ ^ 2 ≤ ω v (J (positiveEndChart q z) v))
    (hJM : ∀ z : ℝ × ℝ, b < z.1 → ∀ v, ‖J (positiveEndChart q z) v‖ ≤ M * ‖v‖) :
    ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
      ‖u (endChart q (q.endSign * s, t)) - y t‖ ≤ A * Real.exp (-(κ * s)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab (z : ℝ × ℝ) (hz : a < z.1) : b < z.1 := (le_max_right _ _).trans_lt hz
  have hHd : ∀ q t, Differentiable ℝ (H q t) := fun q t ↦
    ((hHs q).differentiable two_ne_zero).comp (differentiable_const t |>.prodMk differentiable_id)
  have hmem (z : ℝ × ℝ) (hz : a < z.1) : positiveEndChart q z ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hz)
  -- In the positive end chart, `u` is a Floer half-cylinder for `H'_q` asymptotic to `y(±t)`.
  obtain ⟨κ, hκ, A, hdecay⟩ := exists_pos_eventually_norm_sub_le_exp (a := a) (L := C)
    (J := J ∘ positiveEndChart q) (contDiff_uncurry_positiveEndHamiltonian (hHs q))
    (periodic_positiveEndHamiltonian (hH q))
    (hu.comp (contDiff_positiveEndChart q 2).contDiffOn fun z hz ↦ hmem z hz.1)
    (fun s _ t ↦ by simp only [comp_apply, positiveEndChart_add_one]) hc
    (fun z hz v ↦ hJc z (hab z hz.1) v) (fun z hz v ↦ hJM z (hab z hz.1) v)
    (fun z hz ↦ isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart hKH hH hHd
      (haT.trans hz.1.le)
      (((hu.differentiableOn two_ne_zero) _ (hmem z hz.1)).differentiableAt
        (isOpen_thricePuncturedSphereReal.mem_nhds (hmem z hz.1)))
      (hfloer _ (hmem z hz.1)))
    (ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le hKH hH hHd
      (hu.differentiableOn two_ne_zero) q ha₀ haT))
    (fun z hz ↦ hC z (hab z hz.1))
    (periodic_comp_endSign_mul hyper) (hasDerivAt_comp_endSign_mul_positiveEndHamiltonian hy)
    (fun v hv ↦ eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self hL (hHs q) (hH q)
      hy hyper hnd hv) (tendstoUniformly_comp_positiveEndChart hconv)
  refine ⟨κ, hκ, A, hdecay.mono fun s hs t ↦ ?_⟩
  -- The end loop at the height `±s` is the loop of `u ∘ φ'_q` at the height `s`, read with the
  -- time `±t` of the end.
  have h := hs (q.endSign * t)
  rwa [comp_apply, endSign_mul_endSign_mul, ← endChart_eq_positiveEndChart] at h

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {W : Set (ℝ × V)}

/-- **Exponential `C¹` convergence on a cylindrical end, in the positive end chart.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C³` Hamiltonians `H_q`, and
let `u` be `C³` on `S`, with image in a compact set `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix an end `q`, and suppose that on it beyond `T₀`
the almost complex structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a
`1`-periodic family `J_q(t, x)` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`. Suppose that the loops `t ↦ u(φ_q(±s, t))` converge uniformly to a `1`-periodic orbit `y`
of `H_q` which is nondegenerate: the suspension of the Hamiltonian vector field of `H_q` is
globally Lipschitz and `y(0)` is a nondegenerate fixed point of the time-one map. Then the
derivative of `u ∘ φ'_q` converges exponentially fast to the derivative
`(σ, τ) ↦ τ X_{H'_q(t)}(y(±t))` of the stationary cylinder of the orbit `t ↦ y(±t)` of the end
Hamiltonian `H'_q` of the positive end: for some `κ > 0` and `C`, eventually

`‖d(u ∘ φ'_q)(s, t) - dt ⊗ X_{H'_q(t)}(y(±t))‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_fderiv_comp_positiveEndChart_sub_le_exp_of_cylindrical
    {Jq : ℝ → V → AlmostComplexStructure V}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hBW : univ ×ˢ B ⊆ W) (hJqt : ∀ t, ∀ x ∈ B, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q)))
    {y : ℝ → V} (hyper : Periodic y 1)
    (hy : ∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t)
    (hnd : IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0))
    (hconv : TendstoUniformly (fun s t ↦ u (endChart q (q.endSign * s, t))) y atTop) :
    ∃ κ > 0, ∃ C, ∀ᶠ s in atTop, ∀ t,
      ‖fderiv ℝ (u ∘ positiveEndChart q) (s, t) - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
        (ω.hamiltonianVectorField (positiveEndHamiltonian H q t) (y (q.endSign * t)))‖ ≤
          C * Real.exp (-(κ * s)) := by
  have hHd : ∀ q t, Differentiable ℝ (H q t) := fun q t ↦
    ((hHs q).differentiable (by norm_num)).comp (differentiable_const t |>.prodMk differentiable_id)
  -- In the positive end chart the end is a finite-energy Floer half-cylinder for `H'_q` and the
  -- structure `J'(t, x) = J_q(±t, x)`, asymptotic to the orbit `t ↦ y(±t)` of `H'_q`.
  obtain ⟨hW', hJq', hJqper', hBW', hJqt', hu', hper', huB', hfloer', hE'⟩ :=
    floer_comp_positiveEndChart_of_cylindrical hKH hH hHd hu (by norm_num) huB hfloer hE hW hJq
      hJqper hBW hJqt hJ
  exact exists_pos_eventually_norm_fderiv_sub_smulRight_le_exp
    (J := fun t x ↦ Jq (q.endSign * t) x)
    (contDiff_uncurry_positiveEndHamiltonian (hHs q)) (periodic_positiveEndHamiltonian (hH q))
    hW' hJq' hJqper' hB hBW' hJqt' hu' hper' huB' hfloer' hE'
    (periodic_comp_endSign_mul hyper) (hasDerivAt_comp_endSign_mul_positiveEndHamiltonian hy)
    (fun v hv ↦ eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self hL
      ((hHs q).of_le (by norm_num)) (hH q) hy hyper hnd hv)
    (tendstoUniformly_comp_positiveEndChart hconv)

/-- **The ends of a Floer pair of pants with cylindrical ends converge exponentially in `C¹`.** Let
`K` be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C³` Hamiltonians `H_q`,
and let `u` be `C³` on `S`, with image in a compact set `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix an end `q`, and suppose that on it beyond `T₀`
the almost complex structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a
`1`-periodic family `J_q(t, x)` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`. Suppose moreover that the suspension of the Hamiltonian vector field of `H_q` is globally
Lipschitz and that every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate. Then, in the end
chart `φ_q`, `u` converges exponentially fast in `C¹` to the stationary cylinder `(s, t) ↦ y(t)` of
a `1`-periodic orbit `y` of `H_q`: for some `κ > 0` and `C`, eventually

`‖u(φ_q(±s, t)) - y(t)‖ + ‖d(u ∘ φ_q)(±s, t) - dt ⊗ X_{H_q(t)}(y(t))‖ ≤ C exp (-κ s)`

for every `t`. -/
theorem exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_cylindrical
    {Jq : ℝ → V → AlmostComplexStructure V}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hBW : univ ×ˢ B ⊆ W) (hJqt : ∀ t, ∀ x ∈ B, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0)) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (endChart q (q.endSign * s, t)) - y t‖ +
            ‖fderiv ℝ (u ∘ endChart q) (q.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H q t) (y t))‖ ≤
          A * Real.exp (-(κ * s)) := by
  obtain ⟨b, C, c, hc, M, hC, hJc, hJM⟩ :=
    exists_forall_norm_fderiv_comp_positiveEndChart_le_and_tame hKH hH hHs hu hB huB hfloer hE q
      hW hJq hJqper hBW hJqt hJ
  obtain ⟨y, hyper, hy, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer_of_cylindrical hKH hH hHs
      hu hB huB hfloer hE q hW hJq hJqper hBW hJqt hJ hL hnd
  -- The limit orbit lies in `B`, so it is nondegenerate.
  have hyB (t : ℝ) : y t ∈ B := by
    refine hB.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop 0).mono fun s hs ↦ huB _ ?_)
    rw [endChart_eq_positiveEndChart]
    exact positiveEndChart_mem_thricePuncturedSphereReal hs
  have hndy := hnd y hyper hy hyB
  -- The loops and the derivative converge exponentially, at possibly different rates.
  obtain ⟨κ₀, hκ₀, A₀, h₀⟩ := exists_pos_eventually_norm_sub_le_exp_endChart_of_floer hKH hH
    (fun q ↦ (hHs q).of_le (by norm_num)) (hu.of_le (by norm_num)) hfloer hE q hL hyper hy hndy
    hconv (fun z hz ↦ ((fderiv ℝ (u ∘ positiveEndChart q) z).le_opNorm _).trans <| by
      simpa using hC z hz) hc hJc hJM
  obtain ⟨κ₁, hκ₁, A₁, h₁⟩ :=
    exists_pos_eventually_norm_fderiv_comp_positiveEndChart_sub_le_exp_of_cylindrical hKH
      hH hHs hu hB huB hfloer hE q hW hJq hJqper hBW hJqt hJ hL hyper hy hndy hconv
  -- Both bounds hold with one rate and one constant, so their sum is bounded by twice it.
  obtain ⟨κ, hκ, A, h⟩ := exists_pos_eventually_forall_le_mul_exp (ι := Bool)
    (f := fun b s t ↦ bif b then
      ‖fderiv ℝ (u ∘ endChart q) (q.endSign * s, t) -
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (H q t) (y t))‖
      else ‖u (endChart q (q.endSign * s, t)) - y t‖)
    (Bool.forall_bool.2 ⟨⟨κ₀, hκ₀, A₀, h₀⟩, ⟨κ₁, hκ₁, A₁, h₁.mono fun s hs t ↦ by
      rw [Bool.cond_true, norm_fderiv_comp_endChart_sub_smulRight]
      exact hs _⟩⟩)
  refine ⟨y, hyper, hy, κ, hκ, A + A, h.mono fun s hs t ↦ ?_⟩
  rw [add_mul]
  exact add_le_add (hs false t) (hs true t)

/-- **The ends of a Floer pair of pants with cylindrical ends converge exponentially.** Let `K` be
equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C³` Hamiltonians `H_q`, and
let `u` be `C³` on `S`, with image in a compact set `B`, solving the Floer equation
`(du - X_K)^{0,1} = 0` on `S` with finite energy. Fix an end `q`, and suppose that on it beyond `T₀`
the almost complex structure is cylindrical, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for a
`1`-periodic family `J_q(t, x)` which is `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`. Suppose moreover that the suspension of the Hamiltonian vector field of `H_q` is globally
Lipschitz and that every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate. Then the loops
`t ↦ u(φ_q(±s, t))` converge exponentially fast to a `1`-periodic orbit `y` of `H_q`: for some
`κ > 0` and `C`, eventually `‖u(φ_q(±s, t)) - y(t)‖ ≤ C exp (-κ s)` for every `t`. -/
theorem exists_pos_eventually_norm_sub_le_exp_endChart_of_floer_of_cylindrical
    {Jq : ℝ → V → AlmostComplexStructure V}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) (hW : IsOpen W)
    (hJq : ContDiffOn ℝ 2 (fun p : ℝ × V ↦ (Jq p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : Periodic Jq 1) (hBW : univ ×ˢ B ⊆ W) (hJqt : ∀ t, ∀ x ∈ B, ω.Tames (Jq t x))
    (hJ : ∀ s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq t (u (endChart q (q.endSign * s, t))))
    {L : ℝ≥0} (hL : LipschitzWith L (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ y : ℝ → V, Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) hL 0 1) (y 0)) :
    ∃ y : ℝ → V, Periodic y 1 ∧ (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ t,
        ‖u (endChart q (q.endSign * s, t)) - y t‖ ≤ A * Real.exp (-(κ * s)) := by
  obtain ⟨y, hyper, hy, κ, hκ, A, h⟩ :=
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_cylindrical hKH
      hH hHs hu hB huB hfloer hE q hW hJq hJqper hBW hJqt hJ hL hnd
  exact ⟨y, hyper, hy, κ, hκ, A,
    h.mono fun s hs t ↦ (le_add_of_nonneg_right (norm_nonneg _)).trans (hs t)⟩

/-- **One exponential `C¹` rate for all three ends.** Let `K` be equal to `H_q(t) dt` beyond `T₀`
on each end `q`, for `1`-periodic `C³` Hamiltonians `H_q` whose suspended Hamiltonian vector fields
are globally Lipschitz, and let `u` be `C³` on `S`, with image in a compact set `B`, solving the
Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy. Suppose that on every end the
almost complex structure is cylindrical beyond `T₀`, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for
`1`-periodic families `J_q(t, x)` which are `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`, and that every `1`-periodic orbit of every `H_q` in `B` is nondegenerate. Then there are
`1`-periodic orbits `y_q` of the `H_q`, a rate `κ > 0` and a constant `C` such that for all large
`s`, every end `q` and every `t`,

`‖u(φ_q(±s, t)) - y_q(t)‖ + ‖d(u ∘ φ_q)(±s, t) - dt ⊗ X_{H_q(t)}(y_q(t))‖ ≤ C exp (-κ s)`. -/
theorem exists_pos_forall_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_cylindrical
    {Jq : Puncture → ℝ → V → AlmostComplexStructure V}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ∀ q, ContDiffOn ℝ 2
      (fun p : ℝ × V ↦ (Jq q p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : ∀ q, Periodic (Jq q) 1) (hBW : univ ×ˢ B ⊆ W)
    (hJqt : ∀ q t, ∀ x ∈ B, ω.Tames (Jq q t x))
    (hJ : ∀ q s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq q t (u (endChart q (q.endSign * s, t))))
    {L : Puncture → ℝ≥0}
    (hL : ∀ q, LipschitzWith (L q) (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ q (y : ℝ → V), Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) (hL q) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → V, (∀ q, Periodic (y q) 1 ∧
        (∀ t, HasDerivAt (y q) (ω.hamiltonianVectorField (H q t) (y q t)) t)) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ q t,
        ‖u (endChart q (q.endSign * s, t)) - y q t‖ +
            ‖fderiv ℝ (u ∘ endChart q) (q.endSign * s, t) -
              (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
                (ω.hamiltonianVectorField (H q t) (y q t))‖ ≤
          A * Real.exp (-(κ * s)) := by
  choose y hyper hy hdecay using fun q ↦
    exists_pos_eventually_norm_sub_add_norm_fderiv_sub_le_exp_endChart_of_cylindrical hKH
      hH hHs hu hB huB hfloer hE q hW (hJq q) (hJqper q) hBW (hJqt q) (hJ q) (hL q) (hnd q)
  exact ⟨y, fun q ↦ ⟨hyper q, hy q⟩, exists_pos_eventually_forall_le_mul_exp hdecay⟩

/-- **One exponential rate for all three ends.** Let `K` be equal to `H_q(t) dt` beyond `T₀` on
each end `q`, for `1`-periodic `C³` Hamiltonians `H_q` whose suspended Hamiltonian vector fields
are globally Lipschitz, and let `u` be `C³` on `S`, with image in a compact set `B`, solving the
Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy. Suppose that on every end the
almost complex structure is cylindrical beyond `T₀`, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for
`1`-periodic families `J_q(t, x)` which are `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`, and that every `1`-periodic orbit of every `H_q` in `B` is nondegenerate. Then there are
`1`-periodic orbits `y_q` of the `H_q`, a rate `κ > 0` and a constant `C` such that for all large
`s`, every end `q` and every `t`, `‖u(φ_q(±s, t)) - y_q(t)‖ ≤ C exp (-κ s)`. -/
theorem exists_pos_forall_eventually_norm_sub_le_exp_endChart_of_floer_of_cylindrical
    {Jq : Puncture → ℝ → V → AlmostComplexStructure V}
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    (hu : ContDiffOn ℝ 3 u thricePuncturedSphereReal) (hB : IsCompact B)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hW : IsOpen W)
    (hJq : ∀ q, ContDiffOn ℝ 2
      (fun p : ℝ × V ↦ (Jq q p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJqper : ∀ q, Periodic (Jq q) 1) (hBW : univ ×ˢ B ⊆ W)
    (hJqt : ∀ q t, ∀ x ∈ B, ω.Tames (Jq q t x))
    (hJ : ∀ q s t, T₀ ≤ s →
      J (endChart q (q.endSign * s, t)) = Jq q t (u (endChart q (q.endSign * s, t))))
    {L : Puncture → ℝ≥0}
    (hL : ∀ q, LipschitzWith (L q) (ω.timeDependentHamiltonianSuspension (H q)))
    (hnd : ∀ q (y : ℝ → V), Periodic y 1 →
      (∀ t, HasDerivAt y (ω.hamiltonianVectorField (H q t) (y t)) t) → (∀ t, y t ∈ B) →
      IsNondegenerateFixedPt 𝓘(ℝ, V) (ω.timeDependentHamiltonianFlow (H q) (hL q) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → V, (∀ q, Periodic (y q) 1 ∧
        (∀ t, HasDerivAt (y q) (ω.hamiltonianVectorField (H q t) (y q t)) t)) ∧
      ∃ κ > 0, ∃ A, ∀ᶠ s in atTop, ∀ q t,
        ‖u (endChart q (q.endSign * s, t)) - y q t‖ ≤ A * Real.exp (-(κ * s)) := by
  choose y hyper hy hdecay using fun q ↦
    exists_pos_eventually_norm_sub_le_exp_endChart_of_floer_of_cylindrical hKH hH hHs hu hB huB
      hfloer hE q hW (hJq q) (hJqper q) hBW (hJqt q) (hJ q) (hL q) (hnd q)
  exact ⟨y, fun q ↦ ⟨hyper q, hy q⟩, exists_pos_eventually_forall_le_mul_exp hdecay⟩

end InnerProductSpace

end TauCeti.SymplecticForm
