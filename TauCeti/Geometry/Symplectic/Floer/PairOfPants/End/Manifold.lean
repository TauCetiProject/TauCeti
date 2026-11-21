/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit

/-!
# Asymptotic orbits and energy identity at the ends of a Floer pair of pants in a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, let `K` be a Hamiltonian perturbation on the pair of pants `S = ℂ ∖ {0, 1}`
equal to `H_q(t) dt` beyond some height `T₀` on each end `q`, for period-one Hamiltonians `H_q` on
`M`, and let `u : S → M` solve the Floer equation `(du - X_K)^{0,1} = 0` with finite energy and
image in a compact set `B ⊆ M`. This file proves that `u` breaks off a `1`-periodic orbit of `H_q`
at each end `q`, converges along the whole end when `(e ∘ u) ∘ φ'_q` has bounded derivative on a
half-cylinder and the `1`-periodic orbits of `H_q` in `B` are isolated or nondegenerate, and then,
when its symplectic area and curvature are integrable, satisfies the pair-of-pants energy identity
with the boundary terms evaluated at those asymptotic orbits.

The vector-space counterparts are `TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Orbit` and
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Convergence`. On a manifold target, uniform
convergence and uniform tameness near `B` are measured through a `C¹` map `e : M → F` into a
finite-dimensional normed space, injective on `B` and with injective differential at the points of
`B`. On a compact Hausdorff manifold such a map exists by Mathlib's
`exists_embedding_euclidean_of_compact`.

**Positive end charts.** On the end `q`, the positive end chart `φ'_q(s, t) = φ_q(±s, ±t)`
(`TauCeti.Floer.positiveEndChart`), with the sign `+1` on the input ends `0`, `1` and `-1` on the
output end `∞`, is holomorphic, and beyond `T₀` it pulls `K` back to `H'_q(t) dt` for the positive
end Hamiltonian `H'_q(t, x) = ±H_q(±t, x)` (`TauCeti.Floer.positiveEndHamiltonian`). By
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback`, `u ∘ φ'_q` solves the half-cylinder
Floer equation for `H'_q`
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart`), and its energy
over `(a, ∞) × [0, 1]` with `a ≥ max T₀ 0` is at most the energy of `u` over `S`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_le`). Reading a
`1`-periodic orbit of `H'_q` with the time `±t` of the end gives a `1`-periodic orbit of `H_q`,
and vice versa (`TauCeti.SmoothTwoForm.mem_periodicSolutions_comp_endSign_mul` and
`TauCeti.SmoothTwoForm.mem_periodicSolutions_positiveEndHamiltonian_iff`).

**Orbits and convergence at the ends.** Applying the manifold half-cylinder theorems of
`TauCeti.Geometry.Symplectic.Floer.HalfCylinder.Manifold` to `u ∘ φ'_q` gives, at each end `q`:

* along a sequence `s_n → ∞`, uniform convergence (after `e`) and pointwise convergence in `M` of
  the end loops `t ↦ u(φ_q(±s_n, t))` to a `1`-periodic orbit of `H_q` in `B`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact` and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer`, in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`). Only the part of the domain along the end matters:
  the same holds for a map defined only on an open set containing the part `±s > a` of one end
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen`), which applies to
  the ends of other punctured spheres built from `S`;
* along the whole end `s → ∞`, when `(e ∘ u) ∘ φ'_q` has bounded derivative on a half-cylinder and
  the `1`-periodic orbits of `H_q` in `B` are isolated — in particular when `H_q` is `C²` on a
  Hausdorff boundaryless manifold and each `1`-periodic orbit in `B` starts at a nondegenerate
  fixed point of `timeDependentFlowOf X_{H_q} 0 1` — uniform and pointwise convergence of
  `t ↦ u(φ_q(±s, t))` to a single `1`-periodic orbit `y_q` of `H_q`
  (`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated`,
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact`, and
  `exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer`). Since time reversal
  fixes `t = 0`, isolation of `1`-periodic orbits at `t = 0` transfers directly between `H_q` and
  `H'_q`.

**The energy identity at the asymptotic orbits.** Since `[0, 1] × B` is compact, a continuous `H_q`
is automatically bounded along the end loops in `B`, so dominated convergence gives
`∫₀¹ H_q(t, u(φ_q(±s, t))) dt → ∫₀¹ H_q(t, y_q(t)) dt` without assuming a global bound on `H_q`
(`TauCeti.Floer.tendsto_intervalIntegral_endChart_of_isCompact`). Combined with
`SmoothTwoForm.IsNondegenerate.integrable_floerEnergyDensity_of_eq_smul_endAngularForm` and
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`, when
symplectic area and curvature are integrable on `S`, this makes the Floer energy density integrable
on `S` and gives

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`

at the broken-off isolated (and in particular nondegenerate) `1`-periodic orbits `y_q`, both for
general perturbations that are cylindrical on the ends
(`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated`
and `exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm`) and for
`TauCeti.Floer.pairOfPantsPerturbation`
(`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isolated`,
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact`, and
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation`).

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1, on finite-energy Floer trajectories and their limits at
  nondegenerate orbits.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the asymptotics and the energy identity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations on punctured surfaces and their energy identities.
-/

public section

open Set Filter Topology MeasureTheory Function TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold ENNReal

namespace TauCeti

namespace SmoothTwoForm

open Floer

variable {E HM M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [TopologicalSpace M] [ChartedSpace HM M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M}
  {K : ℂ → M → ℂ →L[ℝ] ℝ} {H : Puncture → ℝ → M → ℝ} {T₀ : ℝ}

/-! ### Orbits in positive end charts -/

/-- Reading a one-periodic orbit of the positive end Hamiltonian `H'_q` with the time `±t` of the
end gives a one-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_comp_endSign_mul {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t))
      1) :
    (fun t ↦ x (q.endSign * t)) ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 :=
  by
  rw [mem_periodicSolutions] at hx ⊢
  refine ⟨fun t ↦ ?_, periodic_comp_endSign_mul hx.2⟩
  -- The velocity `±X_{H'_q(±t)}` of `x` at `±t`, rescaled by the sign of the end, is `X_{H_q(t)}`.
  have h : (1 : ℝ →L[ℝ] ℝ).smulRight (ω.hamiltonianVectorField (H q t) (x (q.endSign * t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
          (ω.hamiltonianVectorField (positiveEndHamiltonian H q (q.endSign * t))
            (x (q.endSign * t))) ∘SL (1 : ℝ →L[ℝ] ℝ).smulRight q.endSign := by
    simp [ContinuousLinearMap.smulRight_comp_smulRight,
      hamiltonianVectorField_positiveEndHamiltonian_endSign_mul, smul_smul]
  rw [h]
  refine (hx.1 (q.endSign * t)).comp t (hasMFDerivAt_iff_hasFDerivAt.2 ?_)
  exact ((hasDerivAt_id' t).const_mul q.endSign).hasFDerivAt.congr_fderiv
    (ContinuousLinearMap.ext_ring (by simp))

/-- A curve `x` is a `1`-periodic orbit of the positive end Hamiltonian `H'_q` if and only if
`t ↦ x(±t)`, with the sign of the end, is a `1`-periodic orbit of `H_q`. -/
theorem mem_periodicSolutions_positiveEndHamiltonian_iff {q : Puncture} {x : ℝ → M} :
    x ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1 ↔
      (fun t ↦ x (q.endSign * t)) ∈
        periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul, fun hx ↦ ?_⟩
  have hx' : (fun t ↦ (fun r ↦ x (q.endSign * r)) (q.endSign * t)) = x := by
    funext t
    simp only [endSign_mul_endSign_mul]
  have h := mem_periodicSolutions_comp_endSign_mul (ω := ω) (H := positiveEndHamiltonian H)
    (by rwa [positiveEndHamiltonian_positiveEndHamiltonian])
  rwa [hx'] at h

/-- Let `u` be defined on an open set `U` containing the part `±s > a` of the end `q`, for some
`a ≥ T₀`. Beyond `a`, `u ∘ φ'_q` is a `C¹`, `1`-periodic, `B`-valued, finite-energy solution of the
coordinate half-cylinder Floer equation for `H'_q`. -/
private theorem positiveEndChart_halfCylinder (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    {B : Set M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (huB : ∀ z ∈ U, u z ∈ B)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : ∀ z ∈ U,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (haT : T₀ ≤ a) (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (fun w ↦ u (positiveEndChart q w)) (Ioi a ×ˢ univ) ∧
      (∀ s, a < s → Periodic (fun t ↦ u (positiveEndChart q (s, t))) 1) ∧
      (∀ s, a < s → ∀ t, u (positiveEndChart q (s, t)) ∈ B) ∧
      (∀ z ∈ Ioi a ×ˢ Icc 0 1,
        mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineReal +
          J (positiveEndChart q z)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I (fun w ↦ u (positiveEndChart q w)) z stdComplexLineImag -
              ω.hamiltonianVectorField (positiveEndHamiltonian H q z.2)
                (u (positiveEndChart q z))) = 0) ∧
      ∫⁻ z in Ioi a ×ˢ Icc 0 1, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z) ≠ ⊤ := by
  have hHd : ∀ t, MDifferentiable I 𝓘(ℝ) (H q t) := fun t ↦
    (hHs.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero
  refine ⟨hu.comp (contDiff_positiveEndChart q 1).contMDiff.contMDiffOn fun z hz ↦ haU z hz.1,
    fun _ _ _ ↦ by simp only [positiveEndChart_add_one],
    fun s hs t ↦ huB _ (haU (s, t) hs), fun z hz ↦ ?_,
    ne_top_of_le_ne_top hE (setLIntegral_floerEnergyDensity_comp_positiveEndChart_le_of_isOpen q
      hKH hH hHd hU (hu.mdifferentiableOn one_ne_zero) haT haU)⟩
  have hS := haU z hz.1
  have hcl := isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart hKH hH hHd
    (haT.trans hz.1.le) ((hu.contMDiffAt (hU.mem_nhds hS)).mdifferentiableAt one_ne_zero)
    (hfloer _ hS)
  have hiff := (ω.isComplexLinearMap_perturbedMFDeriv_iff (fun _ _ ↦ 0)
    (fun w ↦ positiveEndHamiltonian H q w.2) (fun w ↦ u (positiveEndChart q w)) z
    (J (positiveEndChart q z))).1 hcl
  simpa only [hamiltonianVectorField_const, Pi.zero_apply, sub_zero] using hiff

/-- Transfer a `1`-periodic orbit `x` of `H'_q` in `B` and uniform/pointwise convergence of
`u(φ'_q(σ i, ·))` to `x` into a `1`-periodic orbit `t ↦ x(±t)` of `H_q` in `B` and convergence of
the end loops `u(φ_q(±σ i, ·))`. -/
private theorem mem_periodicSolutions_and_tendstoUniformly_endChart_of_positiveEndChart
    {ι α : Type*} [UniformSpace α] {f : M → α} {l : Filter ι} {σ : ι → ℝ} {B : Set M}
    {u : ℝ × ℝ → M} {q : Puncture} {x : ℝ → M}
    (hx : x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1)
    (hxB : ∀ t, x t ∈ B)
    (hconv : TendstoUniformly (fun i t ↦ f (u (positiveEndChart q (σ i, t)))) (f ∘ x) l)
    (hpt : ∀ t, Tendsto (fun i ↦ u (positiveEndChart q (σ i, t))) l (𝓝 (x t))) :
    (fun t ↦ x (q.endSign * t)) ∈
      periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
      (∀ t, x (q.endSign * t) ∈ B) ∧
      TendstoUniformly (fun i t ↦ f (u (endChart q (q.endSign * σ i, t))))
        (f ∘ fun t ↦ x (q.endSign * t)) l ∧
      ∀ t, Tendsto (fun i ↦ u (endChart q (q.endSign * σ i, t))) l
        (𝓝 (x (q.endSign * t))) := by
  refine ⟨mem_periodicSolutions_comp_endSign_mul hx, fun _ ↦ hxB _, ?_, fun t ↦ ?_⟩
  · rw [funext fun i ↦ comp_endChart_eq_comp_positiveEndChart (fun z ↦ f (u z)) q (σ i)]
    exact hconv.comp _
  · simpa only [endChart_eq_positiveEndChart] using hpt (q.endSign * t)

/-! ### Asymptotic orbits at the ends -/

variable [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {e : M → F}

namespace IsNondegenerate

/-! #### Breaking off periodic orbits along sequences -/

/-- **A finite-energy Floer solution breaks off an orbit along an end of the pair of pants.** Let
`ω` be a nondegenerate two-form on a manifold `M`, let `K` be equal to `H_q(t) dt` beyond `T₀` on
an end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let `u` be `C¹` on an open set `U`,
with image in a compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `U`. Let
`e : M → F` be a `C¹` map into a finite-dimensional normed space, injective on `B` and with
injective differential at the points of `B`, and suppose that the almost complex structures are
uniformly tame with respect to `e` on `U`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy
of `u` over `U` is finite and `U` contains the part `±s > a` of the end `q`, then there are a
`1`-periodic orbit `y` of the Hamiltonian vector field of `H_q` in `B` and `s_n → ∞` such that the
loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`, pointwise in `M` and
uniformly after applying `e`.

Only the part of `U` along the end matters, so `u` need not be defined on the whole pair of pants:
this applies to the ends of domains that contain an end of `S`, such as the ends of a plumbed
four-punctured sphere. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (huB : ∀ z ∈ U, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ U, ∀ v, c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ U,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    {a : ℝ} (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨hu', hper', huB', hfloer', hE'⟩ :=
    positiveEndChart_halfCylinder q hKH hH hHs hU hu huB hfloer hE (le_max_left T₀ a)
      fun ζ hζ ↦ haU ζ ((le_max_right T₀ a).trans_lt hζ)
  obtain ⟨x, hx, hxB, σ, -, hσ, hconv, hpt, -⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_of_floer_of_isCompact
      (contMDiff_uncurry_positiveEndHamiltonian hHs)
      (periodic_positiveEndHamiltonian hH) he hB he_inj hde hu' hper' huB'
      (fun z ↦ J (positiveEndChart q z)) hc
      (fun z hz v ↦ hJc _ (haU _ ((le_max_right T₀ a).trans_lt hz.1)) v) hfloer' hE'
  obtain ⟨hy, hyB, hconv', hpt'⟩ :=
    mem_periodicSolutions_and_tendstoUniformly_endChart_of_positiveEndChart hx hxB hconv hpt
  exact ⟨_, hy, hyB, σ, hσ, hconv', hpt'⟩

/-- **A finite-energy Floer pair of pants in a manifold breaks off an orbit at each end.** Let `ω`
be a nondegenerate two-form on a manifold `M`, let `K` be equal to `H_q(t) dt` beyond `T₀` on an
end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let `u` be `C¹` on `S`, with image in a
compact set `B`, solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a
`C¹` map into a finite-dimensional normed space, injective on `B` and with injective differential
at the points of `B`, and suppose that the almost complex structures are uniformly tame with
respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with `c > 0`. If the energy of `u` over `S` is finite,
then at the end `q` there are a `1`-periodic orbit `y` of the Hamiltonian vector field of `H_q`
in `B` and `s_n → ∞` such that the loops `t ↦ u(φ_q(±s_n, t))`, with the sign of the end,
converge to `y`, pointwise in `M` and uniformly after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact
    (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B) (he_inj : InjOn e B)
    (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) :=
  hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isOpen q hKH hH hHs he hB
    he_inj hde isOpen_thricePuncturedSphereReal hu huB J hc hJc hfloer hE (a := 0)
    fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal hζ

/-- **A finite-energy Floer pair of pants in a closed manifold breaks off an orbit at each end.**
Let `ω` be a nondegenerate two-form on a compact manifold `M`, let `K` be equal to `H_q(t) dt`
beyond `T₀` on an end `q`, for a `1`-periodic `C¹` Hamiltonian `H_q`, and let `u` be `C¹` on `S`,
solving the Floer equation `(du - X_K)^{0,1} = 0` on `S`. Let `e : M → F` be a `C¹` injective map
with injective differential into a finite-dimensional normed space, and suppose that the almost
complex structures are uniformly tame with respect to `e`: `c ‖d e v‖² ≤ ω(v, J z v)` with
`c > 0`. If the energy of `u` over `S` is finite, then at the end `q` there are a `1`-periodic
orbit `y` of the Hamiltonian vector field of `H_q` and `s_n → ∞` such that the loops
`t ↦ u(φ_q(±s_n, t))`, with the sign of the end, converge to `y`, pointwise in `M` and uniformly
after applying `e`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer
    [CompactSpace M] (hω : ω.IsNondegenerate) (q : Puncture)
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1) (hHs : ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      ∃ σ : ℕ → ℝ, Tendsto σ atTop atTop ∧
        TendstoUniformly (fun n t ↦ e (u (endChart q (q.endSign * σ n, t)))) (e ∘ y) atTop ∧
        ∀ t, Tendsto (fun n ↦ u (endChart q (q.endSign * σ n, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_of_floer_of_isCompact q hKH hH hHs
      he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc hfloer hE
  exact ⟨y, hy, h⟩

/-! #### Convergence of the ends to isolated and nondegenerate orbits -/

/-- **Convergence of an end of a Floer pair of pants in a manifold to an isolated orbit.** Let `ω`
be a nondegenerate two-form on a finite-dimensional manifold `M`, `K` equal to `H_q(t) dt` beyond
`T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and `u` a `C¹` map on `S` with
image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`. Fix an end
`q`, suppose that on `(b, ∞) × [0, 1]` in the positive end chart `φ'_q` the derivative of
`(e ∘ u) ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` with `c > 0`, and suppose that
each `1`-periodic orbit `y` of `H_q` in `B` is isolated at `t = 0` among the `1`-periodic orbits
of `H_q` in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to a single
`1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
    (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hiso : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  set a := max (max T₀ 0) b
  have ha₀ : 0 ≤ a := (le_max_right _ _).trans (le_max_left _ _)
  have haT : T₀ ≤ a := (le_max_left _ _).trans (le_max_left _ _)
  have hab {z : ℝ × ℝ} (hz : z ∈ Ioi a ×ˢ Icc 0 1) : z ∈ Ioi b ×ˢ Icc 0 1 :=
    ⟨(le_max_right _ _).trans_lt hz.1, hz.2⟩
  obtain ⟨hu', hper', huB', hfloer', hE'⟩ :=
    positiveEndChart_halfCylinder q (hKH q) (hH q) (hHs q) isOpen_thricePuncturedSphereReal hu huB
      hfloer hE haT fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal (ha₀.trans_lt hζ)
  -- Time reversal fixes `t = 0`, so isolation at `0` transfers from `H_q` to `H'_q`.
  have hiso' : ∀ x ∈ periodicSolutions
      (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1, (∀ t, x t ∈ B) →
      ∀ᶠ p in 𝓝 (x 0), ∀ x' ∈ periodicSolutions
        (fun t ↦ ω.hamiltonianVectorField (positiveEndHamiltonian H q t)) 1,
        (∀ t, x' t ∈ B) → x' 0 = p → x' = x := by
    intro x hx hxB
    have h0 := hiso (fun t ↦ x (q.endSign * t)) (mem_periodicSolutions_comp_endSign_mul hx)
      (fun t ↦ hxB _)
    rw [mul_zero] at h0
    refine h0.mono fun p hp x' hx' hx'B hx'0 ↦ funext fun t ↦ ?_
    have heq := congrFun (hp (fun r ↦ x' (q.endSign * r))
      (mem_periodicSolutions_comp_endSign_mul hx') (fun r ↦ hx'B _)
      (by simpa only [mul_zero] using hx'0)) (q.endSign * t)
    simpa only [← mul_assoc, endSign_mul_self, one_mul] using heq
  obtain ⟨x, hx, hxB, hconv, hpt⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_atTop_of_floer_of_isolated
      (contMDiff_uncurry_positiveEndHamiltonian (hHs q))
      (periodic_positiveEndHamiltonian (hH q)) he hB he_inj hde hu' hper' huB'
      (fun z ↦ J (positiveEndChart q z)) hc (fun z hz v ↦ hJc z (hab hz) v) hfloer' hE'
      (fun z hz ↦ hC z (hab hz)) hiso'
  exact ⟨_, mem_periodicSolutions_and_tendstoUniformly_endChart_of_positiveEndChart
    (σ := id) hx hxB hconv hpt⟩

/-- **Convergence of an end of a Floer pair of pants in a manifold to a nondegenerate orbit.** Let
`ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` equal to `H_q(t) dt`
beyond `T₀` on each end `q` for `1`-periodic `C²` Hamiltonians `H_q`, and `u` a `C¹` map on `S`
with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`. Fix an end
`q`, suppose that on `(b, ∞) × [0, 1]` in the positive end chart `φ'_q` the derivative of
`(e ∘ u) ∘ φ'_q` is bounded and `c ‖d e v‖² ≤ ω(v, J (φ'_q z) v)` with `c > 0`, and suppose that
every `1`-periodic orbit `y` of `H_q` in `B` is nondegenerate: `y 0` is a nondegenerate fixed point
of `timeDependentFlowOf X_{H_q} 0 1`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞`
to a single `1`-periodic orbit `y` of `H_q` in `B`, uniformly after `e` and pointwise in `M`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1, (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) :=
  hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated hKH hH
    (fun r ↦ (hHs r).of_le one_le_two) he hB he_inj hde hu huB J hfloer hE q hC hc hJc
    (hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq (hHs q) hnd)

/-- **Convergence of an end of a Floer pair of pants in a closed manifold to a nondegenerate
orbit.** Specialization of
`exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact` when `M` is
compact and `B = univ`. -/
theorem exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z)))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (q : Puncture) {b C : ℝ}
    (hC : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ Ioi b ×ˢ Icc 0 1, ∀ v,
      c * ‖mvfderiv I e (u (positiveEndChart q z)) v‖ ^ 2 ≤
        hω.symplecticFormAt (u (positiveEndChart q z)) v (J (positiveEndChart q z) v))
    (hnd : ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := by
  obtain ⟨y, hy, -, h⟩ :=
    hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isCompact hKH hH
      hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hfloer hE q
      hC hc hJc fun y hy _ ↦ hnd y hy
  exact ⟨y, hy, h⟩

/-! #### The energy identity at the asymptotic orbits -/

/-- **The pair-of-pants energy identity with isolated asymptotic orbits, for a manifold target.**
Let `ω` be a nondegenerate two-form on a manifold `M`, `K` a `C¹` perturbation on `S × M` equal to
`H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C¹` Hamiltonians `H_q`, and `u` a `C¹` map
on `S` with image in a compact set `B ⊆ M`, solving `(du - X_K)^{0,1} = 0` on `S` with finite energy
and integrable symplectic area and curvature. Let `e : M → F` be `C¹`, injective on `B` with
injective differential at the points of `B`, suppose that `c ‖d e v‖² ≤ ω(v, J z v)` on `S` with
`c > 0`, that `(e ∘ u) ∘ φ'_q` has bounded derivative on some strip `(b, ∞) × [0, 1]` at each end
`q`, and that every `1`-periodic orbit of `H_q` in `B` is isolated at `t = 0` among `1`-periodic
orbits of `H_q` in `B`. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic
orbits `y_q` of `H_q` in `B`, the Floer energy density of `u` is integrable on `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated
    (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  have hy_ex : ∀ q, ∃ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) ∧
      TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y) atTop ∧
      ∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y t)) := fun q ↦ by
    obtain ⟨b, C, hbC⟩ := hC q
    have hmem (z : ℝ × ℝ) (hz : max b 0 < z.1) :
        positiveEndChart q z ∈ thricePuncturedSphereReal :=
      positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hz)
    exact hω.exists_mem_periodicSolutions_tendstoUniformly_endChart_atTop_of_floer_of_isolated
      hKH hH hHs he hB he_inj hde hu huB J hfloer hE q
      (b := max b 0) (fun z hz ↦ hbC z ⟨(le_max_left _ _).trans_lt hz.1, hz.2⟩) hc
      (fun z hz v ↦ hJc _ (hmem z hz.1) v) (hiso q)
  choose y hy hyB hyu hyp using hy_ex
  have hh (q : Puncture) :
      Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
        atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t))) :=
    tendsto_intervalIntegral_endChart_of_isCompact (hHs q).continuous hB hu.continuousOn huB
      (hyp q)
  -- Uniform tameness relative to `e` with injective `d e` on `B` tames `J z`, so `E ≥ 0` on `S`.
  have he_nonneg (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z := by
    refine floerEnergyDensity_nonneg hω (fun v hv ↦ ?_) (hfloer z hz)
    have hdv : mvfderiv I e (u z) v ≠ 0 := fun h0 ↦
      hv (hde _ (huB z hz) (h0.trans (map_zero _).symm))
    exact (mul_pos hc (pow_pos (norm_pos_iff.2 hdv) 2)).trans_le (hJc z hz v)
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  have hA' : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) := by rwa [IntegrableOn, hS] at hA
  have hR' : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
    rwa [IntegrableOn, hS] at hR
  have hEint := hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he_nonneg
    hA' hR' hh
  refine ⟨y, fun q ↦ ⟨hy q, hyB q, hyu q, hyp q, hh q⟩, ?_, ?_⟩
  · rwa [IntegrableOn, hS]
  · simp only [hS]
    exact hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu hEint hA' hR' hh

/-- **The pair-of-pants energy identity with nondegenerate asymptotic orbits, for a manifold
target.** Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M`, `K` a `C¹`
perturbation on `S × M` equal to `H_q(t) dt` beyond `T₀` on each end `q` for `1`-periodic `C²`
Hamiltonians `H_q`, and `u` a `C¹` map on `S` with image in a compact set `B ⊆ M`, solving
`(du - X_K)^{0,1} = 0` on `S` with finite energy and integrable symplectic area and curvature. Let
`e : M → F` be `C¹`, injective on `B` with injective differential at the points of `B`, suppose that
`c ‖d e v‖² ≤ ω(v, J z v)` on `S` with `c > 0`, that `(e ∘ u) ∘ φ'_q` has bounded derivative on
some strip `(b, ∞) × [0, 1]` at each end `q`, and that every `1`-periodic orbit of `H_q` in `B` is
nondegenerate. Then the end loops `t ↦ u(φ_q(±s, t))` converge as `s → ∞` to `1`-periodic orbits
`y_q` of `H_q` in `B`, the Floer energy density of `u` is integrable on `S`, and

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, y_q(t)) dt - ∫_S R_K(u)`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hK : ∀ (w : ThricePuncturedSphere) x, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), x))
    (hKH : ∀ q w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z))
      thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) :=
  hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated
    hK hKH hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB J hc hJc hfloer hE hA hR
    hC fun q ↦ hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq (hHs q)
      (hnd q)

/-- **The energy identity for `pairOfPantsPerturbation` with isolated asymptotic orbits in a
compact set.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated` to
`TauCeti.Floer.pairOfPantsPerturbation H`, whose curvature is automatically integrable along `u`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isolated
    (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 1 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hiso : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → ∀ᶠ p in 𝓝 (y 0),
        ∀ y' ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
          (∀ t, y' t ∈ B) → y' 0 = p → y' = y) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm_of_isolated
    (fun w x ↦ contMDiffAt_pairOfPantsPerturbation hH hHs w x)
    (fun _ _ x hw ↦ pairOfPantsPerturbation_eq_smul_endAngularForm hw x) hH hHs he hB he_inj hde
    hu huB J hc hJc hfloer hE hA
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs hu.continuousOn) hC hiso

/-- **The energy identity for `pairOfPantsPerturbation` with nondegenerate asymptotic orbits in a
compact set.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_of_eq_smul_endAngularForm` to
`TauCeti.Floer.pairOfPantsPerturbation H`, whose curvature is automatically integrable along `u`. -/
theorem
    exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
    [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {B : Set M} (hB : IsCompact B)
    (he_inj : InjOn e B) (hde : ∀ p ∈ B, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (huB : ∀ z ∈ thricePuncturedSphereReal, u z ∈ B)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      (∀ t, y t ∈ B) → IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        (∀ t, y q t ∈ B) ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) :=
  hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isolated
    hH (fun q ↦ (hHs q).of_le one_le_two) he hB he_inj hde hu huB J hc hJc hfloer hE hA hC fun q ↦
      hω.forall_mem_periodicSolutions_hamiltonianVectorField_eventually_eq (hHs q) (hnd q)

/-- **The energy identity for `pairOfPantsPerturbation` on a closed manifold.** Specialization of
`exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact` when
`M` is compact and `B = univ`. -/
theorem exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation
    [CompactSpace M] [T2Space M] [BoundarylessManifold I M] (hω : ω.IsNondegenerate)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (uncurry (H q)))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e)
    (hde : ∀ p, Injective (mvfderiv I e p)) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    (J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))) {c : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ thricePuncturedSphereReal, ∀ v,
      c * ‖mvfderiv I e (u z) v‖ ^ 2 ≤ hω.symplecticFormAt (u z) v (J z v))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap)
    (hE : ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≠ ⊤)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    (hC : ∀ q, ∃ b C, ∀ z ∈ Ioi b ×ˢ Icc 0 1,
      ‖fderiv ℝ ((e ∘ u) ∘ positiveEndChart q) z‖ ≤ C)
    (hnd : ∀ q, ∀ y ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1,
      IsNondegenerateFixedPt I
        (timeDependentFlowOf (fun t ↦ ω.hamiltonianVectorField (H q t)) 0 1) (y 0)) :
    ∃ y : Puncture → ℝ → M,
      (∀ q, y q ∈ periodicSolutions (fun t ↦ ω.hamiltonianVectorField (H q t)) 1 ∧
        TendstoUniformly (fun s t ↦ e (u (endChart q (q.endSign * s, t)))) (e ∘ y q) atTop ∧
        (∀ t, Tendsto (fun s ↦ u (endChart q (q.endSign * s, t))) atTop (𝓝 (y q t))) ∧
        Tendsto (fun s ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * s, t))))
          atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (y q t)))) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        thricePuncturedSphereReal ∧
      ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (y q t)) -
          ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
            z (u z) := by
  obtain ⟨y, hy, hEint, hid⟩ :=
    hω.exists_mem_periodicSolutions_integral_floerEnergyDensity_pairOfPantsPerturbation_of_isCompact
      hH hHs he isCompact_univ he_inj.injOn (fun p _ ↦ hde p) hu (fun _ _ ↦ mem_univ _) J hc hJc
      hfloer hE hA hC fun q y hy _ ↦ hnd q y hy
  exact ⟨y, fun q ↦ ⟨(hy q).1, (hy q).2.2⟩, hEint, hid⟩

end IsNondegenerate

end SmoothTwoForm

end TauCeti
