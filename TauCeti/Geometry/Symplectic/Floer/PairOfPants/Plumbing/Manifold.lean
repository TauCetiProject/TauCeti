/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature

/-!
# The energy identity on the plumbed four-punctured sphere for a manifold target

Plumb the output end of a pair of pants `S'` with Hamiltonians `Ha` into the input end `q` of a
pair of pants `S` with Hamiltonians `Hb`, along a neck of length `L > 4`, with `Hb q = Ha ∞`, and
equip the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}` with the glued perturbation
`TauCeti.Floer.plumbedPerturbation`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`. Families of such domains connect the two
ways of composing two pair-of-pants products, so the energy of a Floer solution on them controls
the support of the associativity homotopy of the product.

This file proves the energy identity on the truncation `Σ_R` of the plumbed sphere
(`TauCeti.ThricePuncturedSphere.Puncture.plumbedTruncation`), `R ≥ L/2`, for maps into a
finite-dimensional manifold `M` with a nondegenerate two-form `ω`, such as a closed symplectic
manifold. For a map `u` which is `C¹` on the four-punctured sphere,

`∫_{Σ_R} E = ∫_{Σ_R} u^*ω + ∑_{r ≠ q} ±∫₀¹ H_b,r(t, ℓ_r) dt + ∑_{r ≠ ∞} ∫₀¹ H_a,r(t, ψ ∘ ℓ'_r) dt
  - ∫_{Σ_R} R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`). Here
`ℓ_r(t) = u(φ_r(±R + i t))` are the loops along the circles `±s = R` of the two remaining ends of
the receiving pair of pants `S`, and `(ψ ∘ ℓ'_r)(t) = u(ψ(φ_r(R + i t)))` are the images under `ψ`
of the loops along the circles `s = R` of the two input ends of the inserted one. With the
curvature bound
`TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le`, the energy
differs from the area plus these Hamiltonian terms by at most the sum of bounds for the six end
Hamiltonians, uniformly in `L` and `R`
(`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_sum_le`).
For a solution of the Floer equation with tame almost complex structures the energy is
nonnegative, so the area plus these Hamiltonian terms is at least minus that sum. For `R = L/2`
the truncation `Σ_R` is `S_{L/2} ∪ ψ(S_{L/2})`. For a symplectic vector space target the area
term is a signed sum of loop areas, and the identity is
`SymplecticForm.integral_floerEnergyDensity_plumbedTruncation_eq_sum_hamiltonianAction`.

The truncation `Σ_R` is the union of the part `±s ≤ L/2` of the end `q` of the truncation `S_R` of
the receiving pair of pants and the image under `ψ` of the part `±s ≤ L/2` of the end at `∞` of
the truncation `S'_R` of the inserted one, which meet in a null set
(`TauCeti.Floer.volume_inter_image_realChart_plumbingMap`). On the first part the plumbed datum is
the datum of `S`, and on the second its pullback along `ψ` is the datum of `S'`
(`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image_plumbingMap`,
`TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_image_plumbingMap`). The energy over each
part is given by the energy identity of a truncated pair of pants with one end cut short,
`IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_inter` in the
namespace `TauCeti.SmoothTwoForm`, which only needs `u` to be `C¹` inside the circle
`±s = L/2 + 1` of the cut end: no cutoff of the map, which is unavailable for a manifold target,
is involved. The two cut loops along the middle of the neck are the same loop, by the gluing law
of the end lifts, and they carry the same Hamiltonian `Hb q = Ha ∞` with opposite signs, so their
terms cancel.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`: the
  energy identity on the truncation `Σ_R` of the plumbed sphere, for a manifold target.
* `SmoothTwoForm.IsNondegenerate.integrableOn_plumbedTruncation`: the energy, area and curvature
  densities are integrable over `Σ_R`.
* `SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_sum_le`:
  the energy over `Σ_R` differs from the area plus the Hamiltonian terms of its four boundary
  loops by at most the sum of the six end bounds.
* `SmoothTwoForm`'s
  `IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedTruncation`: for
  solutions of the Floer equation with tame almost complex structures, the area plus these
  Hamiltonian terms is at least minus the sum of the six end bounds.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on energy estimates for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on energy
  estimates on glued domains.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity.
-/

public section

open Set Real Function Manifold MeasureTheory
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart det_fderiv_realChart_nonneg realChart_equivRealProdCLM
  realChart_injective)

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture}
  {L : ℝ}

/-- **The receiving part of the truncated plumbed sphere.** Inside the circle `±s = L/2` of the
end `q` the plumbed datum is the datum of the receiving pair of pants, so the energy there is
given by the energy identity of that pair of pants with the end `q` cut short; the energy and
curvature densities are integrable there. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_receiving
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    (IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u) (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2})) ∧
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1,
          Hb r t (u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        (∫ t in (0 : ℝ)..1,
          Hb q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
            {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
          ω.hamiltonianCurvature
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  set A := Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
    {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} with hA
  have hAm : MeasurableSet A := measurableSet_preimage_truncation_inter q R _
  have hAV : A ⊆ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} :=
    (preimage_truncation_inter_subset_setOf_lt q R (lt_add_one (L / 2))).trans
      (setOf_endSign_mul_re_endCoord_lt_subset_plumbedSphere hq hL)
  obtain ⟨hE, -, hR'⟩ := hω.integrableOn_truncation_inter_pairOfPantsPerturbation hHb hHbs q
    (c := L / 2) (by linarith) hR (isOpen_plumbedSphere q L) hAV hu
  have h := hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_inter hHb hHbs q
    (c := L / 2) (by linarith) hR (isOpen_plumbedSphere q L) hAV hu
  -- On `A` the plumbed datum is the datum of the receiving pair of pants.
  have hre {z : ℝ × ℝ} (hz : z ∈ A) :
      (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 := by
    have h' : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 := hz.2
    rwa [endSign_eq_one hq, one_mul] at h'
  have hEeq {z : ℝ × ℝ} (hz : z ∈ A) :=
    ω.floerEnergyDensity_plumbedPerturbation_of_re_endCoord_le hq hab u (L := L)
      (by linarith [hre hz])
  have hReq {z : ℝ × ℝ} (hz : z ∈ A) := congrFun
    (ω.hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt (Ha := Ha) (L := L) hq hab
      (ne_endCenter (truncation_subset _ hz.1) q) (by linarith [hre hz])) (u z)
  refine ⟨⟨hE.congr_fun (fun z hz ↦ (hEeq hz).symm) hAm,
    hR'.congr_fun (fun z hz ↦ (hReq hz).symm) hAm⟩, ?_⟩
  rw [setIntegral_congr_fun hAm fun z hz ↦ hEeq hz,
    setIntegral_congr_fun hAm fun z hz ↦ hReq hz, h,
    smoothTransition.one_of_one_le (by linarith), smoothTransition.one_of_one_le (by linarith)]
  simp only [hA, endSign_eq_one hq, one_mul]

/-- **The inserted part of the truncated plumbed sphere.** Outside the circle `Re z = -L/2` of the
end at `∞` of the inserted pair of pants, the pullback of the plumbed datum along the plumbing
chart `ψ` is the datum of the inserted pair of pants, so the energy over the image under `ψ` of
that part of its truncation is given by the energy identity of the inserted pair of pants with its
end at `∞` cut short. Its loop along the cut is the loop along the circle `Re z = L/2` of the end
`q`. The energy and curvature densities are integrable there. -/
private theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation_inserted
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    (IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u) (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2})) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}))) ∧
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}),
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
          {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1,
          Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) -
        (∫ t in (0 : ℝ)..1,
          Hb q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))))) -
        ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
            {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}),
          ω.hamiltonianCurvature
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  set B := Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
    {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} with hB
  have hBm : MeasurableSet B := measurableSet_preimage_truncation_inter inf R _
  have hBS := preimage_truncation_inter_subset_setOf_lt_re_endCoord_inf hL R
  have hS₄o := isOpen_plumbedSphere q L
  -- The pulled-back map `u ∘ ψ` is `C¹` inside the circle `±s = L/2 + 1` of the end at `∞`.
  have hu' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ realChart (q.plumbingMap L))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 ∧
        inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re < L / 2 + 1} :=
    hu.comp (contDiff_realChart_plumbingMap q L).contMDiff.contMDiffOn
      (mapsTo_realChart_plumbingMap_setOf_endSign_mul_re_endCoord_lt hq hL)
  have hBV := preimage_truncation_inter_subset_setOf_lt inf R (lt_add_one (L / 2))
  have hVo := isOpen_setOf_endSign_mul_re_endCoord_lt inf (L / 2 + 1)
  have hud := hu.mdifferentiableOn one_ne_zero
  obtain ⟨hE, -, hR'⟩ := hω.integrableOn_truncation_inter_pairOfPantsPerturbation hHa hHas inf
    (c := L / 2) (by linarith) hR hVo hBV hu'
  have h := hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_inter hHa hHas inf
    (c := L / 2) (by linarith) hR hVo hBV hu'
  refine ⟨⟨(ω.integrableOn_floerEnergyDensity_image_plumbingMap_iff hq hHa hHb hHas hHbs hab hL
      hBm hBS hud).2 hE,
    (ω.integrableOn_hamiltonianCurvature_image_plumbingMap_iff hq hHa hHb hHas hHbs hab hL
      hBm hBS u).2 hR'⟩, ?_⟩
  -- The symplectic area is invariant under the holomorphic change of coordinates `ψ`.
  have harea : ∫ z in realChart (q.plumbingMap L) '' B, (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      ∫ w in B, (SmoothBundleForm.eval₂ ω ((u ∘ realChart (q.plumbingMap L)) w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (q.plumbingMap L)) w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (q.plumbingMap L)) w stdComplexLineImag) : ℝ) :=
    ω.integral_eval₂_mfderiv_stdComplexLine_image hBm
      (realChart_injective (q.plumbingMap_injective L)).injOn
      (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
      (fun w _ ↦ det_fderiv_realChart_nonneg (q.hasDerivAt_plumbingMap L _))
      (fun w hw ↦ hud.mdifferentiableAt (hS₄o.mem_nhds
        (mapsTo_realChart_plumbingMap_setOf_endSign_mul_re_endCoord_lt hq hL (hBV hw))))
  -- The loop along the cut is the loop along the circle `Re z = L/2` of the end `q`, and the
  -- loops along the input ends are the images under the plumbing map.
  have hneck : (fun t : ℝ ↦ (u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(inf.endSign * (L / 2)) + ↑t * Complex.I)))) =
      fun t : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))) := by
    funext t
    rw [comp_apply, realChart_equivRealProdCLM, plumbingMap_cylindricalEndLift_inf hq,
      endSign_eq_one hq, one_mul]
  have hsum : ∑ r ∈ Finset.univ.erase inf, r.endSign * ∫ t in (0 : ℝ)..1, Ha r t
      ((u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) =
      ∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
          (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      simp only [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, comp_apply,
        realChart_equivRealProdCLM]
  rw [ω.integral_floerEnergyDensity_image_plumbingMap hq hHa hHb hHas hHbs hab hL hBm hBS hud,
    ω.integral_hamiltonianCurvature_image_plumbingMap hq hHa hHb hHas hHbs hab hL hBm hBS u,
    harea, h, smoothTransition.one_of_one_le (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul, one_mul, hsum]
  have hcut := congrArg (fun γ : ℝ → M ↦ ∫ t in (0 : ℝ)..1, Ha inf t (γ t)) hneck
  beta_reduce at hcut
  rw [hcut, ← hab, hB, endSign_inf]
  ring

/-- **Integrability on the truncated plumbed four-punctured sphere, for a manifold target.** Under
the hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`,
the Floer energy density, the symplectic area density and the curvature of the plumbed
perturbation are integrable over the truncated plumbed sphere `Σ_R = q.plumbedTruncation L R`. -/
theorem IsNondegenerate.integrableOn_plumbedTruncation (hω : ω.IsNondegenerate) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u) (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) ∧
      IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
        (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) ∧
      IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))
        (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) := by
  obtain ⟨⟨hEA, hRA⟩, -⟩ :=
    hω.integral_floerEnergyDensity_plumbedPerturbation_receiving hq hHb hHbs hab hL hR hu
  obtain ⟨⟨hEB, hRB⟩, -⟩ :=
    hω.integral_floerEnergyDensity_plumbedPerturbation_inserted hq hHa hHb hHas hHbs hab hL hR hu
  -- The area density is integrable over the compact set `Σ_R`, which lies in the four-punctured
  -- sphere where `u` is `C¹`.
  refine ⟨?_, ω.integrableOn_eval₂_mfderiv (isOpen_plumbedSphere q L) hu
    (isCompact_preimage_plumbedTruncation q L R)
    (fun z hz ↦ plumbedTruncation_subset hq (by linarith) R hz) _ _, ?_⟩ <;>
    rw [preimage_plumbedTruncation hq L R]
  exacts [hEA.union hEB, hRA.union hRB]

/-- **The energy identity on the truncated plumbed four-punctured sphere, for a manifold target.**
Plumb the output end of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the input end
`q` of one with period-one `C¹` Hamiltonians `Hb`, along a neck of length `L > 4`, where
`Hb q = Ha ∞`, all on a finite-dimensional manifold with a nondegenerate two-form, and let `K` be
the plumbed perturbation `TauCeti.Floer.plumbedPerturbation`, with components `K_s(z) = K(z)(1)`
and `K_t(z) = K(z)(i)`. Let `u` be a map which is `C¹` on the four-punctured sphere
`ℂ ∖ {0, 1, ψ(1)}`. For `R ≥ L / 2` the Floer energy of `u` over the truncated plumbed sphere
`Σ_R = q.plumbedTruncation L R` is its symplectic area, plus the signed sum of the integrals of the
end Hamiltonians along its four boundary loops, minus the integrated curvature:

`∫_{Σ_R} E = ∫_{Σ_R} u^*ω + ∑_{r ≠ q} ±∫₀¹ H_b,r(t, ℓ_r) dt + ∑_{r ≠ ∞} ∫₀¹ H_a,r(t, ψ ∘ ℓ'_r) dt
  - ∫_{Σ_R} R_K(u)`.

Here `ℓ_r(t) = u(φ_r(±R + i t))` are the loops along the circles `±s = R` of the two remaining ends
of the receiving pair of pants, and `(ψ ∘ ℓ'_r)(t) = u(ψ(φ_r(R + i t)))` are the images under the
plumbing map `ψ` of the loops along the circles `s = R` of the two input ends of the inserted one.
The terms of the loops along the middle of the neck cancel. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation (hω : ω.IsNondegenerate)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1,
          Hb r t (u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1,
          Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  obtain ⟨⟨hEA, hRA⟩, hA⟩ :=
    hω.integral_floerEnergyDensity_plumbedPerturbation_receiving hq hHb hHbs hab hL hR hu
  obtain ⟨⟨hEB, hRB⟩, hB⟩ :=
    hω.integral_floerEnergyDensity_plumbedPerturbation_inserted hq hHa hHb hHas hHbs hab hL hR hu
  obtain ⟨-, harea, -⟩ :=
    hω.integrableOn_plumbedTruncation hq hHa hHb hHas hHbs hab hL hR hu
  rw [preimage_plumbedTruncation hq L R] at harea ⊢
  -- Split `Σ_R` into its receiving and inserted parts, which meet in a null set.
  have hψBm : MeasurableSet (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹'
      truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2})) :=
    measurable_image_of_fderivWithin (measurableSet_preimage_truncation_inter inf R _)
      (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
        w).hasFDerivAt.hasFDerivWithinAt)
      (realChart_injective (q.plumbingMap_injective L)).injOn
  have hnull := volume_inter_image_realChart_plumbingMap hq (by linarith : 0 < L) R
  rw [setIntegral_union₀ hnull hψBm.nullMeasurableSet hEA hEB,
    setIntegral_union₀ hnull hψBm.nullMeasurableSet (harea.mono_set subset_union_left)
      (harea.mono_set subset_union_right),
    setIntegral_union₀ hnull hψBm.nullMeasurableSet hRA hRB, hA, hB]
  ring

/-- **The energy bound on a truncated plumbed sphere, for a manifold target.** Under the hypotheses
of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`, if moreover the
end Hamiltonians are bounded, `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then the Floer energy over `Σ_R`
differs from the symplectic area plus the signed sum of the integrals of the end Hamiltonians along
its four boundary loops by at most `∑ r, Ba r + ∑ r, Bb r`, uniformly in the neck length `L` and
in `R`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_sum_le
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {R : ℝ}
    (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ((∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1,
          Hb r t (u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        ∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1,
          Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  rw [hω.integral_floerEnergyDensity_plumbedTruncation hq hHa hHb hHas hHbs hab hL hR hu,
    sub_sub_cancel_left, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The topological energy of a solution on a truncated plumbed sphere is bounded below, for a
manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on the truncated plumbed
sphere `Σ_R` for almost complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the
two-form, under the hypotheses of
`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_sum_le`.
Since its energy is nonnegative, its symplectic area over `Σ_R` plus the Hamiltonian terms of the
four boundary loops is at least `-(∑ r, Ba r + ∑ r, Bb r)`, whatever the neck length `L > 4` and
`R ≥ L / 2`. -/
theorem IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedTruncation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {R : ℝ}
    (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -(∑ r, Ba r + ∑ r, Bb r) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1,
          Hb r t (u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        ∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1,
          Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) := by
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_plumbedTruncation q L R)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedTruncation_sub_sum_le hq hHa hHb
    hHas hHbs hab hL hBa hBb hR hu)).2
  linarith

end TauCeti.SmoothTwoForm
