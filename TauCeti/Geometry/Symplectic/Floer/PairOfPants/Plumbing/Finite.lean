/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Finite
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Topology.Order.MonotoneConvergence

/-!
# Finite-energy Floer solutions on the plumbed four-punctured sphere

Plumb the output end of a pair of pants `S'` with Hamiltonians `Ha` into the input end `q` of a
pair of pants `S` with Hamiltonians `Hb`, along a neck of length `L > 4`, with `Hb q = Ha ∞`. The
result is the four-punctured sphere `Σ = ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation
`K = TauCeti.Floer.plumbedPerturbation Ha Hb q L`. Its four outer ends are the two remaining ends
`r ≠ q` of `S`, with end loops `ℓ_r(R)(t) = u(φ_r(±R + i t))`, and the images under `ψ` of the two
input ends `r ≠ ∞` of `S'`, with end loops `ℓ'_r(R)(t) = u(ψ(φ_r(R + i t)))`.

For a map `u` into a symplectic vector space `(V, ω)`, the energy identity of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Action` holds on every truncation `Σ_R`,
`R ≥ L/2`, of the plumbed sphere. This file passes to the whole plumbed sphere, as
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Finite` does for the pair of pants.

* **The curvature is supported in `Σ_{L/2}`.** Off `Σ_{L/2}` every point of `Σ` lies on the part
  `±s > L/2` of one of the four outer ends, where `K` is the cylindrical datum `H(t) dt`
  (`SymplecticForm.hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation`).
  So the curvature `R_K(u)` is integrable over `Σ` as soon as `u` is continuous there, and its
  integral over `Σ_R` is its integral over `Σ` for every `R ≥ L/2`
  (`SymplecticForm.setIntegral_hamiltonianCurvature_plumbedTruncation_eq`).
* **The end actions are monotone.** For a solution of the Floer equation `(du - X_K)^{0,1} = 0`
  with tame almost complex structures, the signed actions `±A_{Hb r}(ℓ_r(R))` and the actions
  `A_{Ha r}(ℓ'_r(R))` increase with `R ≥ 2`
  (`SymplecticForm.monotoneOn_endSign_mul_hamiltonianAction_of_plumbedPerturbation`,
  `SymplecticForm.monotoneOn_hamiltonianAction_plumbingMap_of_plumbedPerturbation`): on each outer
  end the solution is a Floer half-cylinder for the end Hamiltonian, read through the plumbing
  chart on the inserted ends.
* **The energy identity.** If the four end actions converge, to `b r` on the receiving ends and to
  `a r` on the inserted ends, then the energy of `u` over `Σ` is

  `E(u) = ∑_{r ≠ q} ±b_r + ∑_{r ≠ ∞} a_r - ∫_Σ R_K(u)`

  (`SymplecticForm.lintegral_floerEnergyDensity_plumbedPerturbation_eq`), since the truncations
  `Σ_R` exhaust `Σ` (`TauCeti.ThricePuncturedSphere.Puncture.iUnion_plumbedTruncation`).
  Conversely, finite energy bounds the signed sum of the end actions
  (`SymplecticForm.sum_add_sum_hamiltonianAction_le_of_plumbedPerturbation`), so by monotonicity
  every end action converges: a Floer solution on the plumbed sphere has finite energy exactly
  when its four end actions converge
  (`SymplecticForm.lintegral_floerEnergyDensity_plumbedPerturbation_ne_top_iff`).

The plumbed spheres are the long-neck ends of the families joining the two compositions of the
pair-of-pants product, and this identity bounds the energy of their Floer solutions by the actions
of their asymptotic orbits, as needed for the finiteness of the counts of such solutions.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on energy estimates for compositions of pair-of-pants products.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  action functional and the energy identity.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_equivRealProdCLM equivRealProdCLM_symm_realChart)
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ} {u : ℝ × ℝ → V}

/-! ### The support of the curvature -/

/-- **The curvature of the plumbed perturbation is supported in `Σ_{L/2}`.** At a point of the
plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}` outside the truncation
`Σ_{L/2} = S_{L/2} ∪ ψ(S_{L/2})`, the curvature of the plumbed perturbation vanishes: such a point
lies on the part `±s > L/2` of one of the four outer ends, where the plumbed datum is the
cylindrical datum `H(t) dt` of that end. -/
theorem hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation
    (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1)
    (hzT : Complex.equivRealProdCLM.symm z ∉ q.plumbedTruncation L (L / 2)) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z x = 0 := by
  rcases mem_or_exists_plumbingMap_eq_of_mem_plumbedSphere hz with ⟨hS, hre⟩ | ⟨w', hS, hre, hψ⟩
  · -- On the receiving part, `z` lies beyond the height `L/2` on an end of `S`.
    obtain ⟨r, hr⟩ := exists_lt_endSign_mul_re_endCoord_of_notMem_truncation
      (mem_thricePuncturedSphereReal_iff.2 hS) fun h ↦
        hzT (mem_plumbedTruncation_iff.2 (Or.inl ⟨h, hre⟩))
    rw [← hamiltonianCurvature_constSmooth,
      ω.constSmooth.hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt hq hab
        (ne_endCenter hS q) (by linarith), hamiltonianCurvature_constSmooth]
    exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hHb hHbs hS
      (q := r) (by linarith) x
  · -- On the inserted part, `z = ψ(w')` with `w'` beyond the height `L/2` on an end of `S'`.
    set w : ℝ × ℝ := Complex.equivRealProdCLM w'
    have hw : Complex.equivRealProdCLM.symm w = w' := Complex.equivRealProdCLM.symm_apply_apply w'
    have hwS : Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1 := by
      rwa [hw]
    have hzw : realChart (q.plumbingMap L) w = z := by
      rw [realChart_equivRealProdCLM, hψ, ContinuousLinearEquiv.apply_symm_apply]
    obtain ⟨r, hr⟩ := exists_lt_endSign_mul_re_endCoord_of_notMem_truncation (z := w)
      (mem_thricePuncturedSphereReal_iff.2 hwS) fun h ↦
        hzT (mem_plumbedTruncation_iff.2 (Or.inr ⟨w', by rwa [hw] at h, hre, hψ⟩))
    -- The plumbed datum is differentiable in the domain at `z`.
    have hK (v : ℂ) : DifferentiableAt ℝ
        (fun z ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
        (realChart (q.plumbingMap L) w) :=
      hzw ▸ differentiableAt_plumbedPerturbation_domain hq hHa hHb
        (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
        (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL hz x v
    -- Its pullback along the plumbing chart is the datum of `S'`, whose curvature vanishes at `w`.
    have h := ω.hamiltonianCurvature_perturbationPullback
      (Ks := fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (Kt := fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      (contDiff_realChart_plumbingMap q L).contDiffAt (hK 1) (hK Complex.I)
    rw [← hamiltonianCurvature_constSmooth ω (perturbationPullback (realChart (q.plumbingMap L))
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal),
      ω.constSmooth.hamiltonianCurvature_perturbationPullback_plumbedPerturbation hq hab
        hwS.1 (by rw [hw]; linarith), hamiltonianCurvature_constSmooth,
      ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hHa hHas hwS
        (q := r) (by linarith) x, hzw] at h
    -- The Jacobian of the plumbing chart does not vanish.
    have hdet : (fderiv ℝ (realChart (q.plumbingMap L)) w).det ≠ 0 := by
      rw [TauCeti.Complex.det_fderiv_realChart (q.hasDerivAt_plumbingMap L _)]
      exact (Complex.normSq_pos.2 (q.plumbingFactor_ne_zero L)).ne'
    exact (mul_eq_zero.1 h.symm).resolve_left hdet

/-- **The curvature along a map on the plumbed sphere is integrable.** For a map `u` continuous on
the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, the curvature `R_K(z, u(z))` of the plumbed
perturbation is integrable over it: it is continuous there and vanishes off the compact
truncation `Σ_{L/2}`. -/
theorem integrableOn_hamiltonianCurvature_plumbedPerturbation (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
  have hK := contDiffOn_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
  exact (((ω.continuousOn_hamiltonianCurvature_comp (isOpen_plumbedSphere q L) hu (hK 1)
    (hK Complex.I)).mono fun z hz ↦
      plumbedTruncation_subset hq (by linarith) _ hz).integrableOn_compact
      (isCompact_preimage_plumbedTruncation q L (L / 2))).of_forall_sdiff_eq_zero
    (isOpen_plumbedSphere q L).measurableSet fun z hz ↦
      ω.hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation hq hHa hHb hHas
        hHbs hab hL hz.1 hz.2 (u z)

/-- **The integrated curvature over a truncation of the plumbed sphere.** For `R ≥ L/2` and every
map `u`, the integral of the curvature `R_K(z, u(z))` of the plumbed perturbation over the
truncation `Σ_R` is its integral over the whole plumbed four-punctured sphere. -/
theorem setIntegral_hamiltonianCurvature_plumbedTruncation_eq (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) (u : ℝ × ℝ → V) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  -- Both integrals are the integral over `Σ_{L/2}`.
  have hsub (R' : ℝ) : Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R' ⊆
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := fun z hz ↦
    plumbedTruncation_subset hq (by linarith) R' hz
  have hzero {t : Set (ℝ × ℝ)} (ht : t ⊆ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
      ∀ z ∈ t \ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L (L / 2),
        ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) = 0 := fun z hz ↦
    ω.hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation hq hHa hHb hHas
      hHbs hab hL (ht hz.1) hz.2 (u z)
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_preimage_plumbedTruncation q L R)
      (preimage_mono (plumbedTruncation_mono q L hR)) (hzero (hsub R)),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (isOpen_plumbedSphere q L).measurableSet
      (hsub (L / 2)) (hzero subset_rfl)]

/-! ### Monotonicity of the end actions -/

/-- **The actions on the receiving ends increase.** Let `u` be `C²` on the plumbed four-punctured
sphere and solve the Floer equation `(du - X_K)^{0,1} = 0` there for the plumbed perturbation `K`
and almost complex structures `J(z)` tamed by `ω`. Then on each end `r ≠ q` of the receiving pair
of pants the signed action `±A_{Hb r}(ℓ_r(R))` of the end loop `ℓ_r(R)(t) = u(φ_r(±R + i t))`
increases with `R ≥ 2`. -/
theorem monotoneOn_endSign_mul_hamiltonianAction_of_plumbedPerturbation (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {r : Puncture} (hr : r ≠ q) :
    MonotoneOn (fun R ↦ r.endSign * ω.hamiltonianAction (Hb r) (fun t ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) (Ici 2) := by
  -- The part `±s > 0` of the end `r` lies in the plumbed sphere, inside the circle `Re z = 0` of
  -- the end `q`, which separates it from the puncture `ψ(1)`.
  have hend {ζ : ℝ × ℝ} (hζ : 2 ≤ r.endSign * ζ.1) :
      ((Complex.equivRealProdCLM.symm (endChart r ζ) ≠ 0 ∧
        Complex.equivRealProdCLM.symm (endChart r ζ) ≠ 1) ∧
        Complex.equivRealProdCLM.symm (endChart r ζ) ≠ q.plumbingMap L 1) ∧
        (q.endCoord (Complex.equivRealProdCLM.symm (endChart r ζ))).re ≤ 0 := by
    have hpos : 0 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm (endChart r ζ))).re := by
      rw [re_endCoord_endChart]
      linarith
    have hq0 := endSign_mul_re_endCoord_nonpos hr hpos
    rw [endSign_eq_one hq, one_mul] at hq0
    refine ⟨⟨r.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos hpos, fun h ↦ ?_⟩, hq0⟩
    rw [h, re_endCoord_plumbingMap q L one_ne_zero] at hq0
    linarith [re_endCoord_inf_one_pos]
  refine ω.monotoneOn_endSign_mul_hamiltonianAction hHb hHbs (q := r) (isOpen_plumbedSphere q L) hu
    (fun ζ hζ ↦ (hend hζ).1) (fun ζ hζ ↦ hJ _ (hend hζ).1) fun ζ hζ ↦ ?_
  -- There the plumbed datum is the datum of the receiving pair of pants.
  have hre : (q.endCoord (Complex.equivRealProdCLM.symm (endChart r ζ))).re ≤ L - 2 := by
    linarith [(hend hζ).2]
  have heq : ω.perturbedFDeriv
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I) u
      (endChart r ζ) = ω.perturbedFDeriv
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u
      (endChart r ζ) :=
    ω.perturbedFDeriv_congr u
      (funext fun x ↦ by rw [plumbedPerturbation_of_re_endCoord_le hq hab hre x])
      (funext fun x ↦ by rw [plumbedPerturbation_of_re_endCoord_le hq hab hre x])
  rw [heq]
  exact hfloer _ (hend hζ).1

/-- **The actions on the inserted ends increase.** Let `u` be `C²` on the plumbed four-punctured
sphere and solve the Floer equation `(du - X_K)^{0,1} = 0` there for the plumbed perturbation `K`
and almost complex structures `J(z)` tamed by `ω`. Then on each input end `r ≠ ∞` of the inserted
pair of pants the action `A_{Ha r}(ℓ'_r(R))` of the end loop `ℓ'_r(R)(t) = u(ψ(φ_r(R + i t)))`
increases with `R ≥ 2`, where `ψ` is the plumbing map. -/
theorem monotoneOn_hamiltonianAction_plumbingMap_of_plumbedPerturbation (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {r : Puncture} (hr : r ≠ inf) :
    MonotoneOn (fun R : ℝ ↦ ω.hamiltonianAction (Ha r) (fun t ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) (Ici 2) := by
  set ψ : ℝ × ℝ → ℝ × ℝ := realChart (q.plumbingMap L)
  -- The part `s > 0` of the end `r` lies outside the circle `Re z = 0` of the end at `∞`, so `ψ`
  -- maps it into the plumbed sphere.
  have hend {ζ : ℝ × ℝ} (hζ : 2 ≤ r.endSign * ζ.1) :
      ((Complex.equivRealProdCLM.symm (endChart r ζ) ≠ 0 ∧
        Complex.equivRealProdCLM.symm (endChart r ζ) ≠ 1) ∧
        0 ≤ (inf.endCoord (Complex.equivRealProdCLM.symm (endChart r ζ))).re) ∧
        ψ (endChart r ζ) ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    have hpos : 0 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm (endChart r ζ))).re := by
      rw [re_endCoord_endChart]
      linarith
    have hS := r.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos hpos
    have hinf := endSign_mul_re_endCoord_nonpos hr hpos
    rw [endSign_inf, neg_one_mul, neg_nonpos] at hinf
    refine ⟨⟨hS, hinf⟩, ?_⟩
    rw [mem_ofPred_eq, equivRealProdCLM_symm_realChart]
    exact mapsTo_plumbingMap hq (by linarith) ⟨hS, by linarith⟩
  -- Along `ψ`, `u ∘ ψ` solves the Floer equation for the datum of the inserted pair of pants.
  have hfloer' (ζ : ℝ × ℝ) (hζ : 2 ≤ r.endSign * ζ.1) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (ψ (endChart r ζ)))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u ∘ ψ) (endChart r ζ) : ℝ × ℝ →ₗ[ℝ] V) := by
    obtain ⟨⟨hS, hre⟩, hψS⟩ := hend hζ
    exact ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap hq hHa hHb hHas hHbs hab
      hL ⟨hS, by linarith⟩
      ((hu.contDiffAt ((isOpen_plumbedSphere q L).mem_nhds hψS)).differentiableAt two_ne_zero)
      (hfloer _ hψS)
  have h := ω.monotoneOn_endSign_mul_hamiltonianAction hHa hHas (q := r)
    ((isOpen_plumbedSphere q L).preimage (contDiff_realChart_plumbingMap q L (n := 0)).continuous)
    (hu.comp (contDiff_realChart_plumbingMap q L).contDiffOn fun _ h ↦ h)
    (fun ζ hζ ↦ (hend hζ).2) (J := fun w ↦ J (ψ w)) (fun ζ hζ ↦ hJ _ (hend hζ).2) hfloer'
  refine h.congr fun R _ ↦ ?_
  simp only [endSign_eq_one hr, one_mul, comp_apply, realChart_equivRealProdCLM]

/-! ### The energy identity on the whole plumbed sphere -/

/-- On a truncation `Σ_R`, `R ≥ L/2`, the energy of a Floer solution is the signed sum of the
actions of its four boundary loops minus the integrated curvature over the plumbed sphere. -/
private theorem lintegral_floerEnergyDensity_plumbedTruncation_eq (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {R : ℝ} (hR : L / 2 ≤ R) :
    ∫⁻ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
      ENNReal.ofReal ((∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) -
        ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1) ∧
            Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) := by
  have hPS : Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R ⊆
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := fun z hz ↦
    plumbedTruncation_subset hq (by linarith) R hz
  have hK := contDiffOn_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
  have hint := ((ω.continuousOn_floerEnergyDensity (isOpen_plumbedSphere q L)
    (hu.of_le one_le_two) (hK 1) (hK Complex.I)).mono hPS).integrableOn_compact (μ := volume)
    (isCompact_preimage_plumbedTruncation q L R)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_restrict_of_forall_mem
      (measurableSet_preimage_plumbedTruncation q L R) fun z hz ↦
        ω.floerEnergyDensity_nonneg (hJ z (hPS hz)) (hfloer z (hPS hz))),
    integral_floerEnergyDensity_plumbedTruncation_eq_sum_hamiltonianAction ω hq hHa hHb hHas hHbs
      hab hL hR hu,
    setIntegral_hamiltonianCurvature_plumbedTruncation_eq ω hq hHa hHb hHas hHbs hab hL hR u]

/-- **The energy identity on the plumbed four-punctured sphere.** Let `u` be `C²` on the plumbed
four-punctured sphere `Σ = ℂ ∖ {0, 1, ψ(1)}` and solve the Floer equation `(du - X_K)^{0,1} = 0`
there for the plumbed perturbation `K` and almost complex structures `J(z)` tamed by `ω`. If the
actions of the end loops `ℓ_r(R)(t) = u(φ_r(±R + i t))` of the receiving ends `r ≠ q` tend to
`b r`, and those of the end loops `ℓ'_r(R)(t) = u(ψ(φ_r(R + i t)))` of the inserted ends `r ≠ ∞`
tend to `a r`, as `R → ∞`, then the energy of `u` is

`E(u) = ∑_{r ≠ q} ±b_r + ∑_{r ≠ ∞} a_r - ∫_Σ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_plumbedPerturbation_eq (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a b : Puncture → ℝ}
    (hb : ∀ r ≠ q, Tendsto (fun R ↦ ω.hamiltonianAction (Hb r) (fun t ↦ u
      (Complex.equivRealProdCLM (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))))
      atTop (𝓝 (b r)))
    (ha : ∀ r ≠ inf, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (Ha r) (fun t ↦ u
      (Complex.equivRealProdCLM (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))))
      atTop (𝓝 (a r))) :
    ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) =
      ENNReal.ofReal ((∑ r ∈ Finset.univ.erase q, r.endSign * b r) +
        (∑ r ∈ Finset.univ.erase inf, a r) -
        ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1) ∧
            Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)) := by
  -- The energies over the truncations `Σ_R` tend both to the energy and to the right-hand side.
  have hP := ((tendsto_finsetSum (Finset.univ.erase q) fun r hr ↦
    (hb r (Finset.ne_of_mem_erase hr)).const_mul r.endSign).add
      (tendsto_finsetSum (Finset.univ.erase inf) fun r hr ↦
        ha r (Finset.ne_of_mem_erase hr))).sub_const
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
  refine tendsto_nhds_unique (tendsto_setLIntegral_plumbedTruncation hq (by linarith) volume _)
    (((ENNReal.continuous_ofReal.tendsto _).comp hP).congr' ?_)
  filter_upwards [eventually_ge_atTop (L / 2)] with R hR
  exact (lintegral_floerEnergyDensity_plumbedTruncation_eq ω hq hHa hHb hHas hHbs hab hL hu hJ
    hfloer hR).symm

/-- **The end actions are bounded by the energy.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_plumbedPerturbation_eq`, if the energy of `u` is
finite, then for every `R ≥ L/2` the signed sum of the actions of the four boundary loops of the
truncation `Σ_R` is at most the energy of `u` plus the integrated curvature `∫_Σ R_K(u)`. -/
theorem sum_add_sum_hamiltonianAction_le_of_plumbedPerturbation (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hE : ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) ≠ ⊤)
    {R : ℝ} (hR : L / 2 ≤ R) :
    (∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r)
        (fun t ↦ u (Complex.equivRealProdCLM
          (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
      (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
        (fun t ↦ u (Complex.equivRealProdCLM
          (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) ≤
      (∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          ENNReal.ofReal (ω.floerEnergyDensity
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
              Complex.I) u z)).toReal +
        ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
            Complex.equivRealProdCLM.symm z ≠ 1) ∧
            Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  -- The energy over `Σ_R` is at most the total energy.
  have hle := ENNReal.toReal_mono hE (lintegral_mono_set (μ := volume)
    (f := fun z ↦ ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z))
    fun z (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) ↦
      plumbedTruncation_subset hq (by linarith) R hz)
  rw [lintegral_floerEnergyDensity_plumbedTruncation_eq ω hq hHa hHb hHas hHbs hab hL hu hJ
    hfloer hR, ENNReal.toReal_ofReal'] at hle
  linarith [(le_max_left _ 0).trans hle]

/-- **Finite energy is equivalent to convergence of the end actions.** Let `u` be `C²` on the
plumbed four-punctured sphere `Σ = ℂ ∖ {0, 1, ψ(1)}` and solve the Floer equation
`(du - X_K)^{0,1} = 0` there for the plumbed perturbation `K` and almost complex structures `J(z)`
tamed by `ω`. Then the energy of `u` is finite if and only if the actions of the end loops
`ℓ_r(R)(t) = u(φ_r(±R + i t))` of the receiving ends `r ≠ q` and those of the end loops
`ℓ'_r(R)(t) = u(ψ(φ_r(R + i t)))` of the inserted ends `r ≠ ∞` converge as `R → ∞`. In that case
the energy is given by `SymplecticForm.lintegral_floerEnergyDensity_plumbedPerturbation_eq`. -/
theorem lintegral_floerEnergyDensity_plumbedPerturbation_ne_top_iff (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ∫⁻ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z) ≠ ⊤ ↔
      (∃ b : Puncture → ℝ, ∀ r ≠ q, Tendsto (fun R ↦ ω.hamiltonianAction (Hb r) (fun t ↦ u
        (Complex.equivRealProdCLM (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))))
        atTop (𝓝 (b r))) ∧
      ∃ a : Puncture → ℝ, ∀ r ≠ inf, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (Ha r) (fun t ↦ u
        (Complex.equivRealProdCLM (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))))
        atTop (𝓝 (a r)) := by
  refine ⟨fun hE ↦ ?_, fun ⟨⟨b, hb⟩, ⟨a, ha⟩⟩ ↦
    (ω.lintegral_floerEnergyDensity_plumbedPerturbation_eq hq hHa hHb hHas hHbs hab hL hu hJ hfloer
      hb ha).trans_ne ENNReal.ofReal_ne_top⟩
  set fB : Puncture → ℝ → ℝ := fun r R ↦ r.endSign * ω.hamiltonianAction (Hb r) (fun t ↦ u
    (Complex.equivRealProdCLM (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))
  set fA : Puncture → ℝ → ℝ := fun r R ↦ ω.hamiltonianAction (Ha r) (fun t ↦ u
    (Complex.equivRealProdCLM (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))
  have hR₀ : Ici (L / 2) ⊆ Ici 2 := Ici_subset_Ici.2 (by linarith)
  have hmB (r : Puncture) (hr : r ≠ q) : MonotoneOn (fB r) (Ici (L / 2)) :=
    (ω.monotoneOn_endSign_mul_hamiltonianAction_of_plumbedPerturbation hq hHb hHbs hab hL hu hJ
      hfloer hr).mono hR₀
  have hmA (r : Puncture) (hr : r ≠ inf) : MonotoneOn (fA r) (Ici (L / 2)) :=
    (ω.monotoneOn_hamiltonianAction_plumbingMap_of_plumbedPerturbation hq hHa hHb hHas hHbs hab
      hL hu hJ hfloer hr).mono hR₀
  -- The signed sum of the end actions is bounded above, by the energy plus the curvature.
  obtain ⟨M, hsum⟩ : ∃ M, ∀ R, L / 2 ≤ R →
      (∑ r ∈ Finset.univ.erase q, fB r R) + ∑ r ∈ Finset.univ.erase inf, fA r R ≤ M :=
    ⟨_, fun R hR ↦ ω.sum_add_sum_hamiltonianAction_le_of_plumbedPerturbation hq hHa hHb hHas hHbs
      hab hL hu hJ hfloer hE hR⟩
  -- Each end action is a monotone summand of this bounded sum, so it converges.
  have hconv : ∀ i ∈ (Finset.univ.erase q).disjSum (Finset.univ.erase inf),
      ∃ l, Tendsto (Sum.elim fB fA i) atTop (𝓝 l) :=
    fun _ ↦ exists_tendsto_of_monotoneOn_Ici_of_sum_le
      (by
        rintro (r | r) hr
        · exact hmB r (Finset.ne_of_mem_erase (Finset.inl_mem_disjSum.1 hr))
        · exact hmA r (Finset.ne_of_mem_erase (Finset.inr_mem_disjSum.1 hr)))
      (fun R hR ↦ by simpa only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr] using hsum R hR)
  have hB (r : Puncture) (hr : r ≠ q) : ∃ l, Tendsto (fB r) atTop (𝓝 l) :=
    hconv (.inl r) (Finset.inl_mem_disjSum.2 (Finset.mem_erase.2 ⟨hr, Finset.mem_univ r⟩))
  have hA (r : Puncture) (hr : r ≠ inf) : ∃ l, Tendsto (fA r) atTop (𝓝 l) :=
    hconv (.inr r) (Finset.inr_mem_disjSum.2 (Finset.mem_erase.2 ⟨hr, Finset.mem_univ r⟩))
  choose! lB hlB using hB
  choose! lA hlA using hA
  refine ⟨⟨fun r ↦ r.endSign * lB r, fun r hr ↦ ((hlB r hr).const_mul r.endSign).congr
    fun R ↦ ?_⟩, ⟨lA, hlA⟩⟩
  simp only [fB, ← mul_assoc, endSign_mul_self, one_mul]

end TauCeti.SymplecticForm
