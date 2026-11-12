/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The energy identity on the plumbed four-punctured sphere, for a manifold target

Plumbing the output end at `∞` of a pair of pants `S'`, with Hamiltonians `Ha`, into the input end
`q ∈ {0, 1}` of a pair of pants `S`, with Hamiltonians `Hb`, along a neck of length `L` gives the
four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`). Families of such domains connect the two ways of composing
two pair-of-pants products. The file `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Energy`
computes the energy over the plumbed truncation `Σ = S_{L/2} ∪ ψ(S_{L/2})` for a symplectic vector
space target. This file computes it for a map `u` into a finite-dimensional manifold `M` with a
nondegenerate two-form `ω`, such as a closed symplectic manifold, which is `C¹` on the
four-punctured sphere, for `L > 4` and matching Hamiltonians `Hb q = Ha ∞`:

`∫_Σ E = ∫_Σ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, ℓ'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, ℓ_r(t)) dt
  - ∫_Σ R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_truncation`).
Here `ℓ'_r(t) = u(ψ(φ_r(L/2 + i t)))` runs along the two input circles of the inserted pair of
pants and `ℓ_r(t) = u(φ_r(±L/2 + i t))` along the remaining input and the output circle of the
receiving one, with the sign `+` on inputs and `-` on the output. Since the integrated curvature of
`K` is bounded independently of `L`
(`TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le`), the energy
differs from the topological part `∫_Σ u^*ω + ∑ ±∫ H` by at most the sum of bounds for the six
end Hamiltonians, uniformly in `L`
(`IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_truncation_sub_le`),
and for a solution of the Floer equation with tame almost complex structures the topological part
is at least minus that sum
(`IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap_plumbedPerturbation`).

The proof applies the energy identity of the truncated pair of pants on a manifold target,
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`, to
each of the two pieces. That identity needs a map which is `C¹` on all of `S = ℂ ∖ {0, 1}`, while
`u` is not defined at the puncture `ψ(1)` deep in the end `q` of `S`, and `u ∘ ψ` is not defined
deep in the end at `∞` of `S'`. A map into a manifold cannot be cut off by a function, so instead
it is composed with an *end retraction* of the domain
(`TauCeti.ThricePuncturedSphere.Puncture.endRetraction`): a smooth map of `ℂ` off the center of the
end, which is the identity up to the height `a = L/2 + 1/2` of the end and pushes the rest of the
end into the heights between `a` and `a + 1`, keeping the angular coordinate. The receiving piece
`u ∘ ρ_q` and the inserted piece `u ∘ ψ ∘ ρ_∞` are `C¹` on `S`, and agree with `u` and `u ∘ ψ` near
the truncation `S_{L/2}`. On `S_{L/2}` the plumbed perturbation is that of the receiving pair of
pants, and on `ψ(S_{L/2})` its pullback along `ψ` is that of the inserted one, while energy, area
and curvature are invariant under the holomorphic change of coordinates `ψ`
(`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image`). The neck does not contribute: its
middle circle is the output circle of the inserted pair of pants and the input circle `q` of the
receiving one, with the same Hamiltonian `Ha ∞ = Hb q` and opposite signs.

Truncations of the four outer ends at heights independent of `L`, and the energy identity over
the whole four-punctured sphere at the asymptotic orbits, are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimates for compositions of pair-of-pants products.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
-/

public noncomputable section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply realChart_injective)

open scoped Topology

namespace TauCeti.SmoothTwoForm

open Floer

/-! ### The receiving and inserted pieces of a map -/

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- The receiving piece `u ∘ ρ_q` of a map `u` that is `C¹` on the plumbed four-punctured sphere
is `C¹` on `S`. -/
private theorem contMDiffOn_receivingPiece (hq : q ≠ inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ realChart (endRetraction q (L / 2 + 1 / 2)))
      thricePuncturedSphereReal := by
  refine hu.comp (contMDiffOn_iff_contDiffOn.2 fun z hz ↦
    (contDiffAt_realChart_endRetraction q _
      (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q)).contDiffWithinAt) fun z hz ↦ ?_
  simp only [mem_preimage, mem_ofPred_eq, TauCeti.Complex.equivRealProdCLM_symm_realChart]
  exact endRetraction_mem_plumbedSphere hq hL (mem_thricePuncturedSphereReal_iff.1 hz)

/-- The inserted piece `u ∘ ψ ∘ ρ_∞` of a map `u` that is `C¹` on the plumbed four-punctured
sphere is `C¹` on `S`. -/
private theorem contMDiffOn_insertedPiece (hq : q ≠ inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1
      (u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2)))
      thricePuncturedSphereReal := by
  refine hu.comp (contMDiffOn_iff_contDiffOn.2 fun z hz ↦
    ((contDiff_realChart_plumbingMap q L).contDiffAt.comp z
      (contDiffAt_realChart_endRetraction inf _
        (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) inf))).contDiffWithinAt)
    fun z hz ↦ ?_
  simp only [mem_preimage, mem_ofPred_eq, comp_apply,
    TauCeti.Complex.equivRealProdCLM_symm_realChart]
  exact plumbingMap_endRetraction_mem_plumbedSphere hq hL (mem_thricePuncturedSphereReal_iff.1 hz)

/-- On the truncation `S_{L/2}`, the receiving piece agrees with the map near every point. -/
private theorem receivingPiece_eventuallyEq {X : Type*} (u : ℝ × ℝ → X) {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    u ∘ realChart (endRetraction q (L / 2 + 1 / 2)) =ᶠ[𝓝 z] u := by
  have hz' := mem_truncation.1 hz
  exact (realChart_endRetraction_eventuallyEq (ne_endCenter ⟨hz'.1, hz'.2.1⟩ q)
    (by linarith [hz'.2.2 q])).fun_comp u

/-- On the truncation `S_{L/2}`, the inserted piece agrees with `u ∘ ψ` near every point. -/
private theorem insertedPiece_eventuallyEq {X : Type*} (u : ℝ × ℝ → X) {w : ℝ × ℝ}
    (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2)) =ᶠ[𝓝 w]
      u ∘ realChart (q.plumbingMap L) := by
  have hw' := mem_truncation.1 hw
  exact (realChart_endRetraction_eventuallyEq (ne_endCenter ⟨hw'.1, hw'.2.1⟩ inf)
    (by linarith [hw'.2.2 inf])).fun_comp (u ∘ realChart (q.plumbingMap L))

/-! ### Perturbation data and densities -/

/-- The components of the plumbed perturbation are `C¹` on the plumbed four-punctured sphere times
the target, in real coordinates. -/
private theorem contMDiffOn_uncurry_plumbedPerturbation (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      ({z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) 1
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
      contMDiffAt_snd
  exact (((contMDiffAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hz x).comp (z, x)
    hφ).clm_apply contMDiffAt_const).contMDiffWithinAt

/-! ### The energy, area and curvature of the two pieces -/

variable [IsManifold I ⊤ M]

/-- Over the receiving truncation `S_{L/2}`, the Floer energy of `u` for the plumbed perturbation
is that of the receiving piece of `u` for the perturbation of the receiving pair of pants. -/
private theorem setIntegral_floerEnergyDensity_receiving (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (endRetraction q (L / 2 + 1 / 2))) z := by
  refine setIntegral_congr_fun (measurableSet_preimage_truncation _) fun z hz ↦ ?_
  rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (receivingPiece_eventuallyEq u hz)]
  simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag,
    plumbedPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation hq hab
      (by linarith : L / 2 + 2 ≤ L) hz]

/-- Over the receiving truncation `S_{L/2}`, the symplectic area of `u` is that of its receiving
piece. -/
private theorem setIntegral_area_receiving (ω : SmoothTwoForm I M) (u : ℝ × ℝ → M) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2),
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2),
        (SmoothBundleForm.eval₂ ω ((u ∘ realChart (endRetraction q (L / 2 + 1 / 2))) z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (endRetraction q (L / 2 + 1 / 2))) z
            stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (endRetraction q (L / 2 + 1 / 2))) z
            stdComplexLineImag) : ℝ) :=
  setIntegral_congr_fun (measurableSet_preimage_truncation _) fun _ hz ↦
    ω.eval₂_mfderiv_congr_of_eventuallyEq (receivingPiece_eventuallyEq u hz).symm

/-- On the receiving truncation `S_{L/2}`, the curvature of the plumbed perturbation along `u` is
the curvature of the receiving perturbation along the receiving piece of `u`. -/
private theorem hamiltonianCurvature_receiving (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z ((u ∘ realChart (endRetraction q (L / 2 + 1 / 2))) z) := by
  have hz' := mem_truncation.1 hz
  have hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re < L - 2 := by
    have h := hz'.2.2 q
    rw [endSign_eq_one hq, one_mul] at h
    linarith
  rw [(receivingPiece_eventuallyEq u hz).eq_of_nhds,
    hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt ω hq hab
      (ne_endCenter ⟨hz'.1, hz'.2.1⟩ q) hre]

omit [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M] in
/-- At a point `w` of the inserted truncation `S_{L/2}`, the pullback along the plumbing chart of
the plumbed perturbation is the perturbation of the inserted pair of pants. -/
private theorem perturbationPullback_plumbedPerturbation_stdComplexLine (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℝ × ℝ}
    (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    perturbationPullback (realChart (q.plumbingMap L))
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineReal w =
      (fun x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x 1) ∧
    perturbationPullback (realChart (q.plumbingMap L))
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        stdComplexLineImag w =
      (fun x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x Complex.I) := by
  constructor <;> funext x
  · rw [perturbationPullback_plumbedPerturbation_of_mem_truncation hq hab (by linarith) hw,
      equivRealProdCLM_symm_stdComplexLineReal]
  · rw [perturbationPullback_plumbedPerturbation_of_mem_truncation hq hab (by linarith) hw,
      equivRealProdCLM_symm_stdComplexLineImag]

/-- The plumbing chart sends the inserted truncation `S_{L/2}`, in real coordinates, into the
plumbed four-punctured sphere. -/
private theorem realChart_plumbingMap_mem_plumbedSphere (hq : q ≠ inf) (hL : 4 < L) {w : ℝ × ℝ}
    (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 0 ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 1) ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ q.plumbingMap L 1 := by
  rw [TauCeti.Complex.equivRealProdCLM_symm_realChart]
  exact plumbingMap_mem_plumbedSphere_of_mem_truncation hq hL hw

/-- Over the image under the plumbing chart of the inserted truncation `S_{L/2}`, the Floer energy
of `u` for the plumbed perturbation is that of the inserted piece of `u` over `S_{L/2}` for the
perturbation of the inserted pair of pants. -/
private theorem setIntegral_floerEnergyDensity_inserted (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2))) w := by
  have hP {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    realChart_plumbingMap_mem_plumbedSphere hq hL hw
  have htgt {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2))
      (v : ℂ) :=
    mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL (hP hw)
      (u (realChart (q.plumbingMap L) w)) v
  rw [ω.integral_floerEnergyDensity_image (measurableSet_preimage_truncation _)
    (realChart_injective (q.plumbingMap_injective L)).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
    (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
    (fun w hw ↦ ((hu.contMDiffAt ((isOpen_plumbedSphere q L).mem_nhds (hP hw))).mdifferentiableAt
      one_ne_zero)) (fun w hw ↦ htgt hw 1) (fun w hw ↦ htgt hw Complex.I)]
  refine setIntegral_congr_fun (measurableSet_preimage_truncation _) fun w hw ↦ ?_
  obtain ⟨hpR, hpI⟩ := perturbationPullback_plumbedPerturbation_stdComplexLine hq hab hL hw
  rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (insertedPiece_eventuallyEq u hw)]
  simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag, hpR, hpI]

/-- Over the image under the plumbing chart of the inserted truncation `S_{L/2}`, the symplectic
area of `u` is that of its inserted piece over `S_{L/2}`. -/
private theorem setIntegral_area_inserted (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hL : 4 < L)
    {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2),
        (SmoothBundleForm.eval₂ ω
          ((u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2))) w)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I
            (u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2))) w
            stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I
            (u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2))) w
            stdComplexLineImag) : ℝ) := by
  rw [ω.integral_eval₂_mfderiv_stdComplexLine_image (measurableSet_preimage_truncation _)
    (realChart_injective (q.plumbingMap_injective L)).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
    (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
    (fun w hw ↦ ((hu.contMDiffAt ((isOpen_plumbedSphere q L).mem_nhds
      (realChart_plumbingMap_mem_plumbedSphere hq hL hw))).mdifferentiableAt one_ne_zero))]
  exact setIntegral_congr_fun (measurableSet_preimage_truncation _) fun _ hw ↦
    ω.eval₂_mfderiv_congr_of_eventuallyEq (insertedPiece_eventuallyEq u hw).symm

/-- At a point `w` of the inserted truncation `S_{L/2}`, the Jacobian of the plumbing chart times
the curvature of the plumbed perturbation along `u` at `ψ(w)` is the curvature of the inserted
perturbation along the inserted piece of `u` at `w`. -/
private theorem det_mul_hamiltonianCurvature_inserted (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) {w : ℝ × ℝ}
    (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    (fderiv ℝ (realChart (q.plumbingMap L)) w).det * ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        (realChart (q.plumbingMap L) w) (u (realChart (q.plumbingMap L) w)) =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2)))
          w) := by
  have hw' := mem_truncation.1 hw
  have hre : 2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re := by
    have h := hw'.2.2 inf
    rw [endSign_inf, neg_one_mul] at h
    linarith
  have hP := realChart_plumbingMap_mem_plumbedSphere hq hL hw
  rw [(insertedPiece_eventuallyEq u hw).eq_of_nhds, comp_apply,
    ← hamiltonianCurvature_perturbationPullback_plumbedPerturbation ω hq hab hw'.1 hre,
    ω.hamiltonianCurvature_perturbationPullback (contDiff_realChart_plumbingMap q L).contDiffAt
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hP _ 1)
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hP _ Complex.I)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hP _ 1)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hP _ Complex.I)]

/-- Over the image under the plumbing chart of the inserted truncation `S_{L/2}`, the integrated
curvature of the plumbed perturbation along `u` is that of the inserted perturbation along the
inserted piece of `u` over `S_{L/2}`. -/
private theorem setIntegral_hamiltonianCurvature_inserted (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) :
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L) ∘ realChart (endRetraction inf (L / 2 + 1 / 2))) w) :=
  (integral_image_eq_integral_of_eq_abs_det_smul (measurableSet_preimage_truncation _)
    (realChart_injective (q.plumbingMap_injective L)).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
    fun w hw ↦ by
      rw [abs_of_nonneg (det_fderiv_realChart_plumbingMap_nonneg q L w), smul_eq_mul,
        det_mul_hamiltonianCurvature_inserted ω hq hHa hHb hHas hHbs hab hL u hw])

/-- Along a map `u` that is `C¹` on the plumbed four-punctured sphere, the curvature of the plumbed
perturbation is integrable over the receiving truncation `S_{L/2}`: there it is the curvature of the
receiving pair of pants along the receiving piece of `u`, which is integrable over `S`. -/
private theorem integrableOn_hamiltonianCurvature_receiving (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
  ((integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hHb hHbs
    (contMDiffOn_receivingPiece hq hL hu).continuousOn).mono_set
      (preimage_truncation_subset_thricePuncturedSphereReal _)).congr_fun
    (fun _ hz ↦ (hamiltonianCurvature_receiving ω hq hab hL u hz).symm)
    (measurableSet_preimage_truncation _)

/-- Along a map `u` that is `C¹` on the plumbed four-punctured sphere, the curvature of the plumbed
perturbation is integrable over the image under the plumbing chart of the inserted truncation
`S_{L/2}`: after the change of variables along the plumbing chart it is the curvature of the
inserted pair of pants along the inserted piece of `u`, which is integrable over `S`. -/
private theorem integrableOn_hamiltonianCurvature_inserted (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹'
        truncation (L / 2))) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    (measurableSet_preimage_truncation _)
    (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
      w).hasFDerivAt.hasFDerivWithinAt)
    (realChart_injective (q.plumbingMap_injective L)).injOn _).2
    (((integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hHa hHas
      (contMDiffOn_insertedPiece hq hL hu).continuousOn).mono_set
        (preimage_truncation_subset_thricePuncturedSphereReal _)).congr_fun
      (fun w hw ↦ ?_) (measurableSet_preimage_truncation _))
  rw [abs_of_nonneg (det_fderiv_realChart_plumbingMap_nonneg q L w), smul_eq_mul,
    det_mul_hamiltonianCurvature_inserted ω hq hHa hHb hHas hHbs hab hL u hw]

/-! ### The energy identity -/

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

/-- **The energy identity on the plumbed four-punctured sphere, for a manifold target.** Plumb the
output end of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the input end `q ≠ ∞`
of one with period-one `C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`, along a neck of length
`L > 4`. Let `u` be a map into a finite-dimensional manifold with a nondegenerate two-form, such as
a closed symplectic manifold, which is `C¹` on the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}` in real
coordinates. Over the plumbed truncation `Σ = S_{L/2} ∪ ψ(S_{L/2})`, the Floer energy of `u` for the
plumbed perturbation `K` is the symplectic area, plus the Hamiltonian terms along the four boundary
circles, minus the integrated curvature:

`∫_Σ E = ∫_Σ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, ℓ'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, ℓ_r(t)) dt
  - ∫_Σ R_K(u)`.

Here `ℓ'_r(t) = u(ψ(φ_r(L/2 + i t)))` runs along the input circles of the inserted pair of pants,
and `ℓ_r(t) = u(φ_r(±L/2 + i t))` along the remaining input and output circles of the receiving one,
with the sign `+` on inputs and `-` on the output. The neck does not contribute: its middle circle
is the output circle of the inserted pair of pants and the input circle `q` of the receiving one,
with the same Hamiltonian `Ha ∞ = Hb q` and opposite signs. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_truncation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t
            (u (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
            (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)
  set P := {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}
  have hTm : MeasurableSet T := measurableSet_preimage_truncation _
  have hT : IsCompact T := isCompact_preimage_truncation _
  have hψT : IsCompact (realChart (q.plumbingMap L) '' T) :=
    hT.image (contDiff_realChart_plumbingMap q L (n := 0)).continuous
  have hTP : T ⊆ P := fun z hz ↦ mem_plumbedSphere_of_mem_truncation hq hL hz
  have hψTP : realChart (q.plumbingMap L) '' T ⊆ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact realChart_plumbingMap_mem_plumbedSphere hq hL hw
  have hvb := contMDiffOn_receivingPiece hq hL hu
  have hva := contMDiffOn_insertedPiece hq hL hu
  -- The area density is continuous on the plumbed four-punctured sphere.
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv
    (isOpen_plumbedSphere q L) hu stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  have hRb := integrableOn_hamiltonianCurvature_receiving ω hq hHb hHbs hab hL hu
  have hRa := integrableOn_hamiltonianCurvature_inserted ω hq hHa hHb hHas hHbs hab hL hu
  have hKp := contMDiffOn_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
  have hE (D : Set (ℝ × ℝ)) (hD : IsCompact D) (hDP : D ⊆ P) (hR : IntegrableOn (fun z ↦
      ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) D) :=
    hω.integrableOn_floerEnergyDensity (isOpen_plumbedSphere q L) hu (hKp 1) (hKp Complex.I) hD
      hDP hR
  rw [setIntegral_truncation_union_image hq (hE T hT hTP hRb) (hE _ hψT hψTP hRa),
    setIntegral_truncation_union_image hq ((harea.mono hTP).integrableOn_compact hT)
      ((harea.mono hψTP).integrableOn_compact hψT),
    setIntegral_truncation_union_image hq hRb hRa,
    setIntegral_floerEnergyDensity_receiving ω hq hab hL u,
    setIntegral_floerEnergyDensity_inserted ω hq hHa hHb hHas hHbs hab hL hu,
    setIntegral_area_receiving (q := q) ω u, setIntegral_area_inserted ω hq hL hu,
    setIntegral_congr_fun hTm fun z hz ↦ hamiltonianCurvature_receiving ω hq hab hL u hz,
    setIntegral_hamiltonianCurvature_inserted ω hq hHa hHb hHas hHbs hab hL u,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hHb hHbs hvb
      (by linarith : (1 : ℝ) ≤ L / 2),
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hHa hHas hva
      (by linarith : (1 : ℝ) ≤ L / 2),
    smoothTransition.one_of_one_le (by linarith : (1 : ℝ) ≤ L / 2 - 1), one_mul, one_mul,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ q),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ inf)]
  -- On the boundary circles the two pieces of `u` are `u` and `u ∘ ψ`.
  simp only [comp_apply, TauCeti.Complex.realChart_equivRealProdCLM,
    endRetraction_cylindricalEndLift _ _ (by linarith : 0 < L / 2)
      (by linarith : L / 2 ≤ L / 2 + 1 / 2)]
  -- The inputs of the inserted pair of pants have sign `+`.
  have hinputs : ∑ r ∈ Finset.univ.erase inf, r.endSign * ∫ t in (0 : ℝ)..1, Ha r t
      (u (Complex.equivRealProdCLM (q.plumbingMap L
        (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))))) =
      ∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
        (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      rw [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, one_mul]
  -- The output loop of the inserted pair of pants is the input loop `q` of the receiving one,
  -- with the same Hamiltonian and the opposite sign, so their terms cancel.
  simp only [plumbingMap_cylindricalEndLift_inf hq]
  rw [hinputs, ← hab, endSign_inf, endSign_eq_one hq]
  ring

/-- **The energy bound on the plumbed four-punctured sphere, for a manifold target.** Under the
hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_truncation`, if
`|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then the Floer energy over the plumbed truncation
`S_{L/2} ∪ ψ(S_{L/2})` differs from the symplectic area plus the Hamiltonian terms along its four
boundary circles by at most `∑ r, Ba r + ∑ r, Bb r`, uniformly in the neck length `L > 4`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t
            (u (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I)))))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation_truncation hq hHa hHb hHas hHbs hab hL hu,
    hsub, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The topological energy of a plumbed solution is bounded below, for a manifold target.** Let
`u` solve the Floer equation `(du - X_K)^{0,1} = 0` of the plumbed perturbation on the plumbed
truncation `S_{L/2} ∪ ψ(S_{L/2})`, for almost complex structures `J z` on the tangent spaces
`T_{u(z)} M` tamed by the two-form, under the hypotheses of the energy bound
`IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_truncation_sub_le`.
Since its energy is nonnegative, its symplectic area plus the Hamiltonian terms along the four
boundary circles is at least `-(∑ r, Ba r + ∑ r, Bb r)`, for every neck length `L > 4`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_isComplexLinearMap_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -(∑ r, Ba r + ∑ r, Bb r) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t
            (u (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))))) := by
  have hpos := setIntegral_nonneg (μ := volume)
    (((isCompact_truncation _).union ((isCompact_truncation _).image
      (q.contDiff_plumbingMap L (n := 0)).continuous)).isClosed.preimage
        Complex.equivRealProdCLM.symm.continuous).measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedPerturbation_truncation_sub_le hq
    hHa hHb hHas hHbs hab hL hBa hBb hu)
  linarith [h.2]

end TauCeti.SmoothTwoForm
