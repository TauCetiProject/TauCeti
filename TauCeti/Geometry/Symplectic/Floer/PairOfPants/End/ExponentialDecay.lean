/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.ExponentialDecay
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence

/-!
# Exponential convergence of the ends of a Floer pair of pants

Let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}` with values in a
symplectic vector space `(V, ω)`, equal to `H_q(t) dt` beyond some height `T₀` on each end `q`,
and let `u` be a finite-energy solution of the Floer equation `(du - X_K)^{0,1} = 0` on `S` with
image in a compact set `B` in which every one-periodic orbit of `H_q` is nondegenerate. By
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence` each end loop
`t ↦ u(φ_q(±s, t))` converges uniformly to a one-periodic orbit `y_q` of `H_q` as `s → ∞`. This
file shows that the convergence is exponentially fast: there are `κ > 0` and `C` with

`‖u(φ_q(±s, t)) - y_q(t)‖ ≤ C exp (-κ s)`

for all large `s` and all `t`. Exponential convergence of `u - y_q` on each end is one of the
asymptotic conditions under which a pair of pants with nondegenerate ends lies in the exponentially
weighted function spaces of the linearized Floer operator, and under which its ends can be
pre-glued to Floer cylinders. Exponential decay of the derivatives of `u` along the ends is not
treated here.

**Nondegeneracy in the positive end chart.** In the positive end chart `φ'_q` the end is a Floer
half-cylinder for the Hamiltonian `H'_q(t, x) = ±H_q(±t, x)`
(`TauCeti.Floer.positiveEndHamiltonian`), asymptotic to the orbit `t ↦ y_q(±t)` of `H'_q`. The
half-cylinder estimate `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp` asks the
return map `Ψ'(1)` of the linearized equation `ζ' = S'_t ζ` along this orbit to have no nonzero
fixed vector. Here `S'_{±t} = ±S_t`, where `S_t = dX_{H_{q,t}}(y_q(t))`, so `t ↦ ζ(±t)` turns a
periodic solution of `ζ' = S'_t ζ` into one of `ζ' = S_t ζ`. Nondegeneracy of `y_q(0)` as a fixed
point of the time-one map of `H_q` therefore gives the hypothesis
(`TauCeti.SymplecticForm.eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self`).

## Main results

* `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_endChart_of_floer`: an end that
  converges uniformly to a nondegenerate orbit converges exponentially fast, under a bound on the
  derivative of `u ∘ φ'_q` and uniform taming constants on a half-cylinder of the end.
* `TauCeti.SymplecticForm.exists_pos_eventually_norm_sub_le_exp_endChart_of_cylindrical`: when the
  almost complex structure is cylindrical on the end and all orbits in `B` are nondegenerate, the
  end converges exponentially fast to an orbit, with no bounds assumed.
* `TauCeti.SymplecticForm.exists_pos_forall_eventually_norm_sub_le_exp_endChart_of_cylindrical`:
  when the structure is cylindrical on all three ends, one rate `κ` and one constant `C` serve for
  all of them.

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
  set S : ℝ → V →L[ℝ] V := fun t ↦ fderiv ℝ (ω.hamiltonianVectorField (H q t)) (y t)
  set S' : ℝ → V →L[ℝ] V := fun t ↦
    fderiv ℝ (ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) (y (q.endSign * t))
  have hyc : Continuous y := continuous_iff_continuousAt.2 fun t ↦ (hy t).continuousAt
  have hSc : Continuous S := ω.continuous_fderiv_hamiltonianVectorField_comp hHs hyc
  have hS'c : Continuous S' := ω.continuous_fderiv_hamiltonianVectorField_comp
    (contDiff_uncurry_positiveEndHamiltonian hHs) (hyc.comp (continuous_const.mul continuous_id))
  have hS'p : Periodic S' 1 := fun t ↦ by
    simp only [S', periodic_positiveEndHamiltonian hH t]
    exact congrArg _ (periodic_comp_endSign_mul hyper t)
  -- The linearization in the positive end chart is `S'_{±t} = ±S_t`.
  have hS' (t : ℝ) : S' (q.endSign * t) = q.endSign • S t := by
    have hX : ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t)) =
        q.endSign • ω.hamiltonianVectorField (H q t) := by
      funext z
      rw [Pi.smul_apply, ← hamiltonianVectorField_const_mul]
      congr 1
      funext w
      rw [positiveEndHamiltonian_apply, ← mul_assoc, endSign_mul_self, one_mul]
    simp only [S', S, hX, fderiv_const_smul_field, Pi.smul_apply, ← mul_assoc, endSign_mul_self,
      one_mul]
  -- The periodic solution `ζ' t = Ψ'(t) v` of `ζ' = S'_t ζ`, read with the time `±t`, is a periodic
  -- solution of `ζ' = S_t ζ` starting at `v`.
  set ζ : ℝ → V := fun t ↦ dysonSeriesLeft S' (q.endSign * t) v
  have hζ (t : ℝ) : HasDerivAt ζ (S t (ζ t)) t := by
    have h := (hasDerivAt_dysonSeriesLeft_apply hS'c v (q.endSign * t)).scomp t
      ((hasDerivAt_id' t).const_mul q.endSign)
    rw [hS', mul_one, smul_apply, smul_smul, endSign_mul_self, one_smul] at h
    exact h
  have hζp : Periodic ζ 1 :=
    periodic_comp_endSign_mul ((periodic_dysonSeriesLeft_apply_iff hS'c hS'p v).2 hv)
  have hζ0 : ζ 0 = v := by simp [ζ, dysonSeriesLeft_zero]
  -- So `v` is fixed by the return map `Ψ(1)` of `H_q`, the derivative of the time-one map.
  have hΨ : dysonSeriesLeft S 1 v = v := by
    rw [← hζ0, ← eq_dysonSeriesLeft_apply hSc hζ, ← zero_add (1 : ℝ), hζp 0]
  have hD := (ω.differentiable_timeDependentHamiltonianFlow hL hHs 0 1 (y 0)).hasFDerivAt
  refine (isNondegenerateFixedPt_iff.1 hnd).2.2 v ?_
  rw [hD.hasMFDerivAt.mfderiv, fderiv_timeDependentHamiltonianFlow_eq_dysonSeriesLeft ω hL hHs hy]
  simp only [zero_add, sub_zero]
  exact hΨ

/-- **The ends of a Floer pair of pants converge exponentially to nondegenerate orbits.** Let `K`
be equal to `H_q(t) dt` beyond `T₀` on each end `q`, for `1`-periodic `C²` Hamiltonians `H_q`, and
let `u` be `C²` on `S`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy.
Fix an end `q`, and suppose that on some half-cylinder `s > b` of the positive end chart `φ'_q` the
derivative of `u ∘ φ'_q` is bounded and the almost complex structures are uniformly tame,
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
    {b C : ℝ} (hC : ∀ z : ℝ × ℝ, b < z.1 → ‖fderiv ℝ (u ∘ positiveEndChart q) z‖ ≤ C)
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
  have hux : TendstoUniformly (fun s t ↦ (u ∘ positiveEndChart q) (s, t))
      (fun t ↦ y (q.endSign * t)) atTop := by
    have h : (fun s t ↦ (u ∘ positiveEndChart q) (s, t)) =
        fun s ↦ (fun t ↦ u (endChart q (q.endSign * s, t))) ∘ fun t ↦ q.endSign * t := by
      funext s t
      simp only [comp_apply, positiveEndChart_mk]
    rw [h]
    exact hconv.comp _
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
    (fun z hz ↦ ((fderiv ℝ (u ∘ positiveEndChart q) z).le_opNorm _).trans <| by
      simpa using hC z (hab z hz.1))
    (periodic_comp_endSign_mul hyper) (hasDerivAt_comp_endSign_mul_positiveEndHamiltonian hy)
    (fun v hv ↦ eq_zero_of_dysonSeriesLeft_positiveEndHamiltonian_apply_eq_self hL (hHs q) (hH q)
      hy hyper hnd hv) hux
  refine ⟨κ, hκ, A, hdecay.mono fun s hs t ↦ ?_⟩
  -- The end loop at the height `±s` is the loop of `u ∘ φ'_q` at the height `s`, read with the
  -- time `±t` of the end.
  have h := hs (q.endSign * t)
  rwa [comp_apply, ← mul_assoc, endSign_mul_self, one_mul, ← endChart_eq_positiveEndChart] at h

end NormedSpace

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {K : ℂ → V → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → V → ℝ} {T₀ : ℝ}
  {u : ℝ × ℝ → V} {J : ℝ × ℝ → AlmostComplexStructure V} {B : Set V} {W : Set (ℝ × V)}

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
theorem exists_pos_eventually_norm_sub_le_exp_endChart_of_cylindrical
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
  set b := max T₀ 0 + 1
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_comp_positiveEndChart_le hKH hH hHs hu hB huB
    hfloer hE q hW hJq hJqper hBW hJqt hJ (lt_add_one _)
  -- The end structures `J_q` have uniform taming constants on `ℝ × B`.
  obtain ⟨c, hc, M, hcM⟩ := exists_pos_forall_mul_norm_sq_le_and_norm_le hB
    (hJq.continuousOn.mono hBW) hJqper hJqt
  have hJb (z : ℝ × ℝ) (hz : b < z.1) :
      J (positiveEndChart q z) = Jq (q.endSign * z.2) (u (positiveEndChart q z)) ∧
        u (positiveEndChart q z) ∈ B := by
    have hz₀ : max T₀ 0 < z.1 := (lt_add_one _).trans hz
    refine ⟨?_, huB _ (positiveEndChart_mem_thricePuncturedSphereReal
      ((le_max_right _ _).trans_lt hz₀))⟩
    obtain ⟨s, t⟩ := z
    simp only [positiveEndChart_mk]
    exact hJ s _ ((le_max_left _ _).trans hz₀.le)
  obtain ⟨y, hyper, hy, hconv⟩ :=
    exists_periodic_hasDerivAt_tendstoUniformly_endChart_atTop_of_floer_of_cylindrical hKH hH hHs
      hu hB huB hfloer hE q hW hJq hJqper hBW hJqt hJ hL hnd
  -- The limit orbit lies in `B`, so it is nondegenerate.
  have hyB (t : ℝ) : y t ∈ B := by
    refine hB.isClosed.mem_of_tendsto (hconv.tendsto_at t)
      ((eventually_gt_atTop 0).mono fun s hs ↦ huB _ ?_)
    rw [endChart_eq_positiveEndChart]
    exact positiveEndChart_mem_thricePuncturedSphereReal hs
  exact ⟨y, hyper, hy, exists_pos_eventually_norm_sub_le_exp_endChart_of_floer hKH hH
    (fun q ↦ (hHs q).of_le (by norm_num)) (hu.of_le (by norm_num)) hfloer hE q hL hyper hy
    (hnd y hyper hy hyB) hconv (fun z hz ↦ hC z hz.le) hc
    (fun z hz v ↦ by rw [(hJb z hz).1]; exact (hcM _ _ (hJb z hz).2 v).1)
    fun z hz v ↦ by rw [(hJb z hz).1]; exact (hcM _ _ (hJb z hz).2 v).2⟩

/-- **One exponential rate for all three ends.** Let `K` be equal to `H_q(t) dt` beyond `T₀` on
each end `q`, for `1`-periodic `C³` Hamiltonians `H_q` whose suspended Hamiltonian vector fields
are globally Lipschitz, and let `u` be `C³` on `S`, with image in a compact set `B`, solving the
Floer equation `(du - X_K)^{0,1} = 0` on `S` with finite energy. Suppose that on every end the
almost complex structure is cylindrical beyond `T₀`, `J(φ_q(±s, t)) = J_q(t, u(φ_q(±s, t)))`, for
`1`-periodic families `J_q(t, x)` which are `C²` on an open set `W ⊇ ℝ × B` and tamed by `ω` on
`ℝ × B`, and that every `1`-periodic orbit of every `H_q` in `B` is nondegenerate. Then there are
`1`-periodic orbits `y_q` of the `H_q`, a rate `κ > 0` and a constant `C` such that for all large
`s`, every end `q` and every `t`, `‖u(φ_q(±s, t)) - y_q(t)‖ ≤ C exp (-κ s)`. -/
theorem exists_pos_forall_eventually_norm_sub_le_exp_endChart_of_cylindrical
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
  choose y hyper hy κ hκ A hA using fun q ↦
    exists_pos_eventually_norm_sub_le_exp_endChart_of_cylindrical hKH hH hHs hu hB huB
      hfloer hE q hW (hJq q) (hJqper q) hBW (hJqt q) (hJ q) (hL q) (hnd q)
  -- The slowest rate and the largest constant serve for every end.
  set κ₀ := Finset.univ.inf' ⟨.zero, Finset.mem_univ _⟩ κ
  set A₀ := Finset.univ.sup' ⟨.zero, Finset.mem_univ _⟩ fun q ↦ max (A q) 0
  refine ⟨y, fun q ↦ ⟨hyper q, hy q⟩, κ₀, (Finset.lt_inf'_iff _).2 fun q _ ↦ hκ q, A₀, ?_⟩
  filter_upwards [eventually_all.2 hA, eventually_ge_atTop 0] with s hs hs₀ q t
  have hκq : κ₀ ≤ κ q := Finset.inf'_le _ (Finset.mem_univ q)
  have hAq : max (A q) 0 ≤ A₀ := Finset.le_sup' (fun q ↦ max (A q) 0) (Finset.mem_univ q)
  calc ‖u (endChart q (q.endSign * s, t)) - y q t‖ ≤ A q * Real.exp (-(κ q * s)) := hs q t
    _ ≤ A₀ * Real.exp (-(κ₀ * s)) :=
      mul_le_mul ((le_max_left _ _).trans hAq)
        (Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hκq hs₀)))
        (Real.exp_pos _).le ((le_max_right _ _).trans hAq)

end InnerProductSpace

end TauCeti.SymplecticForm
