/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Energy
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The energy identity on the whole plumbed four-punctured sphere

Plumb the output end at `∞` of a pair of pants `S'`, with Hamiltonians `Ha`, into the input end
`q ≠ ∞` of a pair of pants `S`, with Hamiltonians `Hb q = Ha ∞`, along a neck of length `L > 4`.
The result is the four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`). Families of these domains connect the two broken products
`(a ⋆ b) ⋆ c` and `a ⋆ (b ⋆ c)`, and the energy of the Floer solutions over them controls the
support of the associativity homotopy.

`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Energy` computes the energy over the
truncations `Σ_R = q.plumbedTruncation L R`, `R ≥ L/2`, which increase with `R` and exhaust `Σ_L`
(`TauCeti.ThricePuncturedSphere.Puncture.iUnion_plumbedTruncation`). This file lets `R → ∞`, for a
map `u` into a finite-dimensional manifold `M` with a nondegenerate two-form `ω`, such as a closed
symplectic manifold. Suppose that `u` is `C¹` on `Σ_L`, that its energy density and its area
density are integrable over `Σ_L`, and that its loops along the four outer circles of `Σ_R`
converge pointwise as `R → ∞`: the loops `t ↦ u(ψ(φ_r(R + i t)))` along the inputs `r ≠ ∞` of the
inserted pair of pants to `x'_r`, and the loops `t ↦ u(φ_r(±R + i t))` along the ends `r ≠ q` of
the receiving one to `x_r`. If the Hamiltonians are bounded, then

`∫_{Σ_L} E = ∫_{Σ_L} u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, x'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, x_r(t)) dt
  - ∫_{Σ_L} R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`), with the sign
`+` on inputs and `-` on the output. The neck contributes no boundary term, and its length enters
only through the domain. When the neck carries a Hamiltonian `N`, the inputs of the inserted pair
of pants pushed forward by the plumbing map and the remaining input of the receiving one are input
ends `c_i + a_i φ₀(R + i t)` of centers `c_q`, `ψ(1)`, `c_r` and scales `f`, `-f`, `2 b_r`, so the
identity also holds in the coordinates of a sphere with moving input ends
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_update`).

The curvature is integrable over `Σ_L`
(`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_plumbedPerturbation`): it is integrable
over each `Σ_R`
(`TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_plumbedTruncation`) and vanishes outside
`Σ_R` for `R ≥ 2` (`SmoothTwoForm`'s
`hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation`).
So the three integrals over `Σ_R` converge to those over `Σ_L`, and by dominated convergence the
Hamiltonian terms along the outer circles converge to those along their limits.

The integral of the absolute value of the curvature over the plane is at most
`∑ r, Ba r + ∑ r, Bb r` for bounds `|Ha r| ≤ Ba r`, `|Hb r| ≤ Bb r`
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`). So the
energy differs from the area plus the Hamiltonian terms at the asymptotic loops by at most
`∑ r, Ba r + ∑ r, Bb r`, uniformly in the neck length `L > 4`
(`IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le`), and for a solution
of the Floer equation with tame almost complex structures this topological part is at least
`-(∑ r, Ba r + ∑ r, Bb r)`
(`IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedPerturbation`). On a target
which is not symplectically aspherical the area term depends on the homotopy class of `u`; caps of
the four asymptotic loops turn it into capped actions and the area of a sphere, which is not done
here.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `integrableOn_hamiltonianCurvature_plumbedPerturbation`: the curvature is integrable over the
  four-punctured sphere.
* `IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`: the energy identity on the
  whole plumbed four-punctured sphere, at the asymptotic loops of the four outer ends.
* `IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_update`: the same identity for
  a neck Hamiltonian `N`, read in the coordinates of moving input ends.
* `IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le`: the resulting
  energy bound, uniform in the neck length.
* `IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedPerturbation`: the lower
  bound on the topological energy of a Floer solution.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimates for compositions of pair-of-pants products.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the resulting energy bounds.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- **The curvature is integrable over the plumbed four-punctured sphere, for a manifold
target.** Along a map continuous on the four-punctured sphere `Σ_L`, the curvature of the plumbed
perturbation of period-one `C¹` Hamiltonians is integrable over `Σ_L`. -/
theorem integrableOn_hamiltonianCurvature_plumbedPerturbation (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} :=
  (ω.integrableOn_hamiltonianCurvature_plumbedTruncation hq hHa hHb hHas hHbs hab hL le_rfl
    hu).of_forall_sdiff_eq_zero (isOpen_plumbedSphere q L).measurableSet fun _ hz ↦
      ω.hamiltonianCurvature_plumbedPerturbation_eq_zero_of_notMem_plumbedTruncation hq hHa hHb
        hHas hHbs hab hL (by linarith) hz.1 hz.2 _

variable [FiniteDimensional ℝ E]

/-- **The energy identity on the plumbed four-punctured sphere, for a manifold target.** Plumb the
output end of a pair of pants with bounded period-one `C¹` Hamiltonians `Ha` into the input end
`q ≠ ∞` of one with bounded period-one `C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`, along a neck of
length `L > 4`, for Hamiltonians on a finite-dimensional manifold with a nondegenerate two-form,
such as a closed symplectic manifold. Let `u` be `C¹` on the four-punctured sphere
`Σ_L = ℂ ∖ {0, 1, ψ(1)}`, in real coordinates, with energy density and area density integrable over
`Σ_L`. Suppose its loops `t ↦ u(ψ(φ_r(R + i t)))` along the inputs `r ≠ ∞` of the inserted pair of
pants converge pointwise to loops `x'_r`, and its loops `t ↦ u(φ_r(±R + i t))` along the ends
`r ≠ q` of the receiving one to loops `x_r`, as `R → ∞`. Then

`∫_{Σ_L} E = ∫_{Σ_L} u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, x'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, x_r(t)) dt
  - ∫_{Σ_L} R_K(u)`,

with the sign `+` on inputs and `-` on the output. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {xa xb : Puncture → ℝ → M}
    (hxa : ∀ r, r ≠ inf → ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (xa r t)))
    (hxb : ∀ r, r ≠ q → ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xb r t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (xa r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (xb r t)) -
        ∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set T : ℝ → Set (ℝ × ℝ) := fun R ↦ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R
  have hL0 : 0 < L := by linarith
  have hTm (R : ℝ) : MeasurableSet (T R) := measurableSet_preimage_plumbedTruncation q L R
  have hTmono : Monotone T := fun _ _ h ↦ preimage_mono (plumbedTruncation_mono q L h)
  have hTP := iUnion_preimage_plumbedTruncation hq hL0
  have hRP := ω.integrableOn_hamiltonianCurvature_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
    hu.continuousOn
  -- The Hamiltonian terms along the outer circles converge, by dominated convergence, since for
  -- `R > 0` the circles lie in `Σ_R`, where `u` is continuous.
  have hmem {R : ℝ} {w : ℂ} (hw : w ∈ q.plumbedTruncation L R) :
      Complex.equivRealProdCLM w ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    simpa only [mem_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply] using
      plumbedTruncation_subset hq hL0 R hw
  have hHa_lim (r : Puncture) (hr : r ∈ Finset.univ.erase inf) :=
    tendsto_intervalIntegral_comp_of_continuousOn (hHas r).continuous
      (fun _ ↦ (Real.norm_eq_abs _).trans_le (hBa r _ _)) hu.continuousOn (t₁ := 0) (t₂ := 1)
      (y := fun R t ↦ Complex.equivRealProdCLM
        (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))
      (Eventually.of_forall fun R ↦ (Complex.equivRealProdCLM.continuous.comp
        ((q.contDiff_plumbingMap L (n := 0)).continuous.comp
          ((r.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop)))).continuousOn)
      ((eventually_gt_atTop 0).mono fun R hR t _ ↦ hmem
        (plumbingMap_cylindricalEndLift_mem_plumbedTruncation (Finset.ne_of_mem_erase hr) hL0.le
          hR t))
      fun t _ ↦ hxa r (Finset.ne_of_mem_erase hr) t
  have hHb_lim (r : Puncture) (hr : r ∈ Finset.univ.erase q) :=
    tendsto_intervalIntegral_comp_of_continuousOn (hHbs r).continuous
      (fun _ ↦ (Real.norm_eq_abs _).trans_le (hBb r _ _)) hu.continuousOn (t₁ := 0) (t₂ := 1)
      (y := fun R t ↦ Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))
      (Eventually.of_forall fun R ↦ (Complex.equivRealProdCLM.continuous.comp
        ((r.contDiff_cylindricalEndLift 0).continuous.comp (by fun_prop))).continuousOn)
      ((eventually_gt_atTop 0).mono fun R hR t _ ↦ hmem
        (cylindricalEndLift_mem_plumbedTruncation hq (Finset.ne_of_mem_erase hr) hL0.le hR t))
      fun t _ ↦ hxb r (Finset.ne_of_mem_erase hr) t
  -- Both sides of the identity on `Σ_R` converge, and they agree for `R ≥ L/2`.
  have hlim := ((tendsto_setIntegral_of_monotone hTm hTmono (hTP ▸ hA)).add
    ((tendsto_finsetSum _ hHa_lim).add
      (tendsto_finsetSum _ fun r hr ↦ (hHb_lim r hr).const_mul r.endSign))).sub
    (tendsto_setIntegral_of_monotone hTm hTmono (hTP ▸ hRP))
  have h := tendsto_nhds_unique (tendsto_setIntegral_of_monotone hTm hTmono (hTP ▸ hE))
    (hlim.congr' ((eventually_ge_atTop (L / 2)).mono fun R hR ↦
      (hω.integral_floerEnergyDensity_plumbedTruncation hq hHa hHb hHas hHbs hab hL hR hu).symm))
  rwa [hTP] at h

/-- The plane minus the three input punctures `c_q`, `ψ(1)` and `c_r` of a plumbed sphere, listed
as the centers of its input ends, is the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`. -/
private theorem setOf_forall_ne_plumbedCenters {r : Puncture} (hq : q ≠ inf) (hrq : r ≠ q)
    (hr : r ≠ inf) (L : ℝ) :
    {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠
        (![q.endCenter, q.plumbingMap L 1, r.endCenter] : Fin 3 → ℂ) i} =
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
  ext z
  simp only [mem_ofPred_eq, Fin.forall_fin_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]
  rcases eq_zero_and_eq_one_or_eq_one_and_eq_zero hq hrq hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [endCenter_zero, endCenter_one, IsEmpty.forall_iff, and_true] <;> tauto

/-- **The energy identity on a plumbed sphere, in the coordinates of moving input ends.** Plumb
the output end of a pair of pants with Hamiltonians `Ha` into the input end `q ≠ ∞` of one with
Hamiltonians `Hb`, along a neck of length `L > 4` carrying the Hamiltonian `N`, for bounded
period-one `C¹` Hamiltonians on a finite-dimensional manifold with a nondegenerate two-form. Read
the plumbed sphere as a sphere with the three input ends of centers `c = (c_q, ψ(1), c_r)`, scales
`a = (f, -f, 2 b_r)` and Hamiltonians `(Ha 0, Ha 1, Hb r)`, where `r` is the other input of the
receiving pair of pants, `f` the plumbing factor and `b_r` the scale of the end `r`. Then the
energy identity of the whole plumbed sphere holds at the asymptotic loops `x i` of these input
ends, along `c_i + a_i φ₀(R + i t)`, and `xout` of the output end. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_update
    (hω : ω.IsNondegenerate) {r : Puncture} (hq : q ≠ inf) (hrq : r ≠ q) (hr : r ≠ inf)
    {N : ℝ → M → ℝ} (hHa : ∀ p ≠ inf, Periodic (Ha p) 1) (hHb : ∀ p ≠ q, Periodic (Hb p) 1)
    (hN : Periodic N 1)
    (hHas : ∀ p ≠ inf, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha p)))
    (hHbs : ∀ p ≠ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb p)))
    (hNs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry N)) (hL : 4 < L)
    {Ba Bb : Puncture → ℝ} {BN : ℝ} (hBa : ∀ p ≠ inf, ∀ t x, |Ha p t x| ≤ Ba p)
    (hBb : ∀ p ≠ q, ∀ t x, |Hb p t x| ≤ Bb p) (hBN : ∀ t x, |N t x| ≤ BN)
    {c a : Fin 3 → ℂ} (hc : c = ![q.endCenter, q.plumbingMap L 1, r.endCenter])
    (ha : a = ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale])
    {H : Fin 3 → ℝ → M → ℝ} (hH : H = ![Ha zero, Ha one, Hb r]) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    {x : Fin 3 → ℝ → M} {xout : ℝ → M}
    (hx : ∀ i (t : ℝ), Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (c i + a i * zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x i t)))
    (hxout : ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop (𝓝 (xout t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (update Ha inf N) (update Hb q N) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (update Ha inf N) (update Hb q N) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}) :
    ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i}, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation (update Ha inf N) (update Hb q N) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (update Ha inf N) (update Hb q N) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ i, ∫ t in (0 : ℝ)..1, H i t (x i t)) - ∫ t in (0 : ℝ)..1, Hb inf t (xout t)) -
        ∫ z in {z : ℝ × ℝ | ∀ i, Complex.equivRealProdCLM.symm z ≠ c i},
          ω.hamiltonianCurvature
            (fun z x ↦ plumbedPerturbation (update Ha inf N) (update Hb q N) q L
              (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (update Ha inf N) (update Hb q N) q L
              (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  subst hc ha hH
  rw [setOf_forall_ne_plumbedCenters hq hrq hr L] at hu hE hA ⊢
  -- The plumbed datum with the neck Hamiltonian `N` on both sides of the neck.
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation hq
    ((forall_update_iff Ha fun _ f => Periodic f 1).2 ⟨hN, hHa⟩)
    ((forall_update_iff Hb fun _ f => Periodic f 1).2 ⟨hN, hHb⟩)
    ((forall_update_iff Ha fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry f)).2
      ⟨hNs, hHas⟩)
    ((forall_update_iff Hb fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry f)).2
      ⟨hNs, hHbs⟩)
    (by simp) hL
    ((forall_update_iff Ha fun p f => ∀ t x, |f t x| ≤ update Ba inf BN p).2
      ⟨by simpa using hBN, fun p hp => by simpa [update_of_ne hp] using hBa p hp⟩)
    ((forall_update_iff Hb fun p f => ∀ t x, |f t x| ≤ update Bb q BN p).2
      ⟨by simpa using hBN, fun p hp => by simpa [update_of_ne hp] using hBb p hp⟩) hu
    (xa := fun p ↦ if p = zero then x 0 else x 1)
    (xb := fun p ↦ if p = inf then xout else x 2) ?_ ?_ hE hA]
  · -- The Hamiltonian terms are those of the three input ends and of the output end.
    congr 2
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_erase_eq_sub (Finset.mem_univ _),
      Puncture.sum_univ, Puncture.sum_univ, Fin.sum_univ_three]
    rcases eq_zero_and_eq_one_or_eq_one_and_eq_zero hq hrq hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp <;> ring
  · -- The loops along the inputs of the inserted pair of pants.
    intro p hp t
    cases p
    · simpa only [Matrix.cons_val_zero, plumbingMap_apply, ↓reduceIte] using hx 0 t
    · simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, plumbingMap_cylindricalEndLift_one,
        reduceCtorEq, ↓reduceIte] using hx 1 t
    · exact absurd rfl hp
  · -- The loops along the remaining input `r` and the output of the receiving pair of pants.
    intro p hp t
    obtain rfl | rfl := eq_or_eq_inf_of_ne hq hrq hr hp
    · simp only [endSign_eq_one hr, one_mul,
        cylindricalEndLift_eq_add_mul_cylindricalEndLift_zero p]
      simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hr, ↓reduceIte]
        using hx 2 t
    · simpa using hxout t

/-- **The energy bound on the plumbed four-punctured sphere, for a manifold target.** Under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`, the
Floer energy over the four-punctured sphere differs from the symplectic area plus the Hamiltonian
terms at the asymptotic loops of its four outer ends by at most `∑ r, Ba r + ∑ r, Bb r`, uniformly
in the neck length `L > 4`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {xa xb : Puncture → ℝ → M}
    (hxa : ∀ r, r ≠ inf → ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (xa r t)))
    (hxb : ∀ r, r ≠ q → ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xb r t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (xa r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (xb r t))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hBa hBb hu hxa
    hxb hE hA, hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The topological energy of a solution on the plumbed four-punctured sphere is bounded below,
for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the
four-punctured sphere for almost complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed
by the two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`. Since its energy
is nonnegative, its symplectic area plus the Hamiltonian terms at the asymptotic loops of its four
outer ends is at least `-(∑ r, Ba r + ∑ r, Bb r)`, whatever the neck length `L > 4`. -/
theorem IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {xa xb : Puncture → ℝ → M}
    (hxa : ∀ r, r ≠ inf → ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) atTop (𝓝 (xa r t)))
    (hxb : ∀ r, r ≠ q → ∀ t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (xb r t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -(∑ r, Ba r + ∑ r, Bb r) ≤
      (∫ z in {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (xa r t)) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (xb r t)) := by
  have hpos := setIntegral_nonneg (μ := volume) (isOpen_plumbedSphere q L).measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le hq hHa hHb
    hHas hHbs hab hL hBa hBb hu hxa hxb hE hA)).2
  linarith

end TauCeti.SmoothTwoForm
