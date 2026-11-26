/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder

/-!
# Compactness of the capping family in a closed manifold

The unit of the pair-of-pants product is the count of negative PSS planes, and its unit property
is proved with the *capping family*: plumbing the negative plane with Hamiltonian `H_1` into the
input end at `1` of the pair of pants `S = ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along
a neck of length `L > 4`, gives the datum
`K_L = TauCeti.Floer.plumbedPerturbation (Pi.single ∞ H_1) H 1 L` on the capped plane `ℂ ∖ {0}`, a
cylinder with the remaining input at `0` and the output at `∞`, together with almost complex
structures `J_L`. This file proves the interior part of Gromov–Floer compactness for the solutions
of the whole family in a closed manifold `M`, uniformly over a compact window of neck lengths, with
no condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Capping` assume instead that the images
stay in a compact subset of one symplectic chart.

The compactness theorem over a compact parameter window in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
applies once its hypotheses are checked for the family.

* **The data in the charts of `M`.** The data are smooth jointly in the neck length `L > 4`, the
  point of the capped plane and the target point
  (`TauCeti.Floer.contMDiffAt_plumbedPerturbation_single_inf_family`), so their Hamiltonian vector
  fields read in the chart at any point of `M` are `C²` in `(L, z, y)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`).
* **The energy bound.** Read a solution `u` in the coordinates `(s, t)` of the end at `0`, with
  asymptotic loops `x₀` as `s → ∞` and `x_∞` as `s → -∞`. Uniformly in `L > 4`, its Floer energy
  over every measurable part of the capped plane is at most the change of capped action
  `∫ (u ∘ φ_0)^*ω + ∫₀¹ H_0(t, x₀(t)) dt - ∫₀¹ H_∞(t, x_∞(t)) dt` plus `B_1 + (B_0 + B_1 + B_∞)`
  (`IsNondegenerate.setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le` in the
  namespace `TauCeti.SmoothTwoForm`), and it is integrable there
  (`TauCeti.SmoothTwoForm.integrableOn_floerEnergyDensity_plumbedPerturbation_single_inf`). The
  compact windows of the capped plane may contain the capped puncture `1`, so bubbling at the
  inserted plane is covered.
* **The almost complex structures of the family.** For the structures
  `TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex` of the family, built from a compatible
  base structure and period-one `C²` end structures, the structures read in the charts are `C²` in
  `(L, z, y)` for `L > 4` and `z ∈ ℂ ∖ {0}`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappingAlmostComplex`, read in the charts by
  `TauCeti.Floer.contDiffOn_almostComplexInChartAt_almostComplexStructureAt`), and they are tame
  everywhere (`TauCeti.SmoothTwoForm.Compatible.tames_cappingAlmostComplex`).

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping`: for any
  family `J_L(z, x)` of tame structures which is `C²` read in the charts of `M` near the windows of
  neck lengths and of the capped plane, there is a threshold `δ > 0` such that every sequence of
  solutions for neck lengths `Lₖ` in a compact window `C ⊆ (4, ∞)`, with change of capped action at
  most `A`, has a subsequence whose neck lengths converge to some `L₀ ∈ C` and which converges on
  an open `Ω ⊆ D` off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ A + B_1 + (B_0 + B_1 + B_∞)`.

In the namespace `TauCeti.SmoothTwoForm.Compatible`:

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappingAlmostComplex`
  is the same for the almost complex structures of the family.

The regularity of the limit, the bubbles at the points of `Z`, breaking at the two ends and the
long-neck end `L → ∞` are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Bundle Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {Hb : Puncture → ℝ → M → ℝ} {e : M → F}

namespace IsNondegenerate

/-- **Solutions of the capping family in a closed manifold converge off finitely many bubbling
points.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `Hb` be period-one `C³`
Hamiltonians with `|Hb r| ≤ Bb r`, and let `K_L` be the datum obtained by plumbing the negative
plane with Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians
`Hb`, along a neck of length `L`. Let `J_L(z, x)` be structures on the tangent spaces of `M`, tamed
by `ω` for `L` in a compact window `C ⊆ (4, ∞)` of neck lengths and `z` in the capped plane
`ℂ ∖ {0}` (in real coordinates), which read in the chart at every point of `M` are `C²` jointly in
`(L, z, y)` on `W × (chart target)`, for an open `W` containing `C × D` with `D` a compact subset of
the capped plane. Let `e : M → F` be injective and differentiable, with the structures uniformly
tame with respect to `e` over `C × D`, `κ ‖d e v‖² ≤ ω(v, J_L(z) v)` with `κ > 0`, and the
pushforwards through `e` of the Hamiltonian vector fields of the two components of `K_L` at most
`L'` there. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps from
the capped plane to `M` solving the Floer equation `(du - X_{K_{Lₖ}})^{0,1} = 0` there for the
structures `J_{Lₖ}(z, u)`, with `Lₖ ∈ C`. Read `uₖ` in the coordinates `(s, t)` of the end at `0`,
and suppose that its loops converge pointwise to `x₀ₖ` as `s → ∞` and to `x_infₖ` as `s → -∞`, that
its energy, area and curvature densities in these coordinates are integrable over the strip
`ℝ × [0, 1]`, and that the change of capped action
`∫ (uₖ ∘ φ_0)^*ω + ∫₀¹ Hb 0 (t, x₀ₖ(t)) dt - ∫₀¹ Hb ∞ (t, x_infₖ(t)) dt` is at most `A`, and let
`Ω ⊆ D` be open. Then there are a subsequence `φ`, a limit `L₀ ∈ C` of the neck lengths `L_{φ n}`
and a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + Bb 1 + ∑ r, Bb r` such that, along `φ`, every disc
about a point of `Z` eventually carries energy at least `δ`, the energy densities are uniformly
bounded on every compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a continuous
map `v`, locally uniformly after applying `e` and pointwise in `M`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r)))
    {Bb : Puncture → ℝ} (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} {C : Set ℝ} {D : Set (ℝ × ℝ)} (hW : IsOpen W) (hC : IsCompact C)
    (hC₄ : C ⊆ Ioi 4) (hD : IsCompact D) (hD₀ : ∀ z ∈ D, equivRealProdCLM.symm z ≠ 0)
    (hCDW : C ×ˢ D ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ L ∈ C, ∀ z, equivRealProdCLM.symm z ≠ 0 → ∀ x,
      (hω.symplecticFormAt x).Tames (J L z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L' : ℝ} (hκ : 0 < κ)
    (hJc : ∀ L ∈ C, ∀ z ∈ D, ∀ x v,
      κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J L z x v))
    (hLs : ∀ L ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (equivRealProdCLM.symm z) y 1) x)‖ ≤ L')
    (hLt : ∀ L ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L') :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x₀ x_inf : ℕ → ℝ → M⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (L k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k t, Tendsto (fun s ↦ u k (endChart zero (s, t))) atTop (𝓝 (x₀ k t))) →
      (∀ k t, Tendsto (fun s ↦ u k (endChart zero (s, t))) atBot (𝓝 (x_inf k t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (cappedCylinderComponent Hb (L k) 1)
        (cappedCylinderComponent Hb (L k) Complex.I) (u k ∘ endChart zero)) (univ ×ˢ Icc 0 1)) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω ((u k ∘ endChart zero) z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineImag) : ℝ))
        (univ ×ˢ Icc 0 1)) →
      (∀ k, IntegrableOn (fun z ↦ ω.hamiltonianCurvature (cappedCylinderComponent Hb (L k) 1)
        (cappedCylinderComponent Hb (L k) Complex.I) z ((u k ∘ endChart zero) z))
        (univ ×ˢ Icc 0 1)) →
      (∀ k, (∫ z in univ ×ˢ Icc 0 1, (SmoothBundleForm.eval₂ ω ((u k ∘ endChart zero) z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineImag) : ℝ)) +
        (∫ t in 0..1, Hb zero t (x₀ k t)) - (∫ t in 0..1, Hb inf t (x_inf k t)) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L₀ ∈ C, Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + Bb one + ∑ r, Bb r ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        (∀ L'', IsCompact L'' → L'' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L'', ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  set S₀ : Set (ℝ × ℝ) := {z | equivRealProdCLM.symm z ≠ 0}
  -- Each component `(L, z) ↦ K_L(z)(w)` of the data is `C³` jointly in the neck length, the point
  -- of the capped plane and the target point, so its Hamiltonian vector field is `C²` in every
  -- chart.
  have hg : ContMDiff (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 3
      (fun p : (ℝ × (ℝ × ℝ)) × M ↦ (p.1.1, (equivRealProdCLM.symm p.1.2, p.2))) :=
    (contDiff_fst.contMDiff.comp contMDiff_fst).prodMk
      (((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).prodMk
        contMDiff_snd)
  have hK (w : ℂ) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ Ioi 4 ×ˢ S₀) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry fun (p : ℝ × (ℝ × ℝ)) x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one
          p.1 (equivRealProdCLM.symm p.2) x w) (p, x) :=
    (((contMDiffAt_plumbedPerturbation_single_inf_family (n := 3) (q := one) (by simp) hHb hHbs
      hp.1 (eq_endCenter_one_or_of_ne_zero hp.2) x).comp (p, x) hg.contMDiffAt).clm_apply
        contMDiffAt_const).of_le (by norm_num)
  have hS₀ : IsOpen S₀ := isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const
  have hWS : IsOpen (W ∩ Ioi 4 ×ˢ S₀) := hW.inter (isOpen_Ioi.prod hS₀)
  have hCDWS : C ×ˢ D ⊆ W ∩ Ioi 4 ×ˢ S₀ := subset_inter hCDW (prod_mono hC₄ hD₀)
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun l z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one l
        (equivRealProdCLM.symm z) x 1)
      (Kt := fun l z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one l
        (equivRealProdCLM.symm z) x Complex.I)
      he he_inj hWS hC hD hCDWS
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun l hl z hz ↦ hJt l hl z (hD₀ z hz)) hκ hJc hLs hLt
  refine ⟨δ, hδ, fun Ω L u x₀ x_inf A hΩ hΩD hLC hu hfl hx₀ hx_inf hE hAr hR hA ↦ ?_⟩
  have hΩS₀ : Ω ⊆ S₀ := hΩD.trans hD₀
  -- The Floer energy over `Ω` is at most the change of capped action plus the curvature
  -- allowance `Bb 1 + ∑ r, Bb r`.
  refine hconv hΩ hΩD hLC (fun k ↦ (hu k).mono hΩS₀) (fun k z hz ↦ hfl k z (hΩS₀ hz))
    (fun k ↦ ω.integrableOn_floerEnergyDensity_plumbedPerturbation_single_inf hHb
      (fun r ↦ (hHbs r).of_le (by norm_num)) (hC₄ (hLC k)) hΩ.measurableSet hΩS₀
      (fun z hz ↦ ((hu k).contMDiffAt (hS₀.mem_nhds (hΩS₀ hz))).mdifferentiableAt (by norm_num))
      (hE k)) fun k ↦ ?_
  have hEk := hω.setIntegral_floerEnergyDensity_plumbedPerturbation_single_inf_le hHb
    (fun r ↦ (hHbs r).of_le (by norm_num)) (hC₄ (hLC k)) hBb ((hu k).of_le (by norm_num))
    (fun z hz ↦ hJt _ (hLC k) z hz _) (hfl k) (hx₀ k) (hx_inf k) (hE k) (hAr k) (hR k)
    hΩ.measurableSet hΩS₀
  linarith [hA k]

end IsNondegenerate

namespace Compatible

variable {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

/-- **Solutions of the capping family in a closed manifold converge off finitely many bubbling
points, for the structures of the family.** Let `σ` be a two-form on a closed manifold `M`
compatible with a smooth almost complex structure `J₀`, and let the end structures `Jb r t` be
tamed by `σ`, of period one in `t` and jointly `C²` on `ℝ × M`. Take the structures
`TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex` of the capping family at the input end `1`,
and otherwise the hypotheses of
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, for a compact window `C ⊆ (4, ∞)` of neck lengths
and a compact window `D` of the capped plane `ℂ ∖ {0}`: the structures of the family are tame and
regular in the charts of `M`, so only the uniform tameness with respect to `e` and the bound on the
Hamiltonian vector fields remain as hypotheses. Then there is a threshold `δ > 0` such that every
sequence of solutions for neck lengths in `C` with change of capped action at most `A` has a
subsequence whose neck lengths converge in `C` and which converges on an open `Ω ⊆ D` off a finite
set `Z` of bubbling points, with `#Z * δ ≤ A + Bb 1 + ∑ r, Bb r`. -/
theorem
    exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappingAlmostComplex
    (h₀ : σ.Compatible J₀) (Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJb : ∀ r t, σ.Tames (Jb r t)) (hJbp : ∀ r, Periodic (Jb r) 1)
    (hJbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((Jb r p.1).toEndomorphism p.2)))
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r)))
    {Bb : Puncture → ℝ} (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {C : Set ℝ} {D : Set (ℝ × ℝ)}
    (hC : IsCompact C) (hC₄ : C ⊆ Ioi 4) (hD : IsCompact D)
    (hD₀ : ∀ z ∈ D, equivRealProdCLM.symm z ≠ 0)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L' : ℝ} (hκ : 0 < κ)
    (hJc : ∀ L ∈ C, ∀ z ∈ D, ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.cappingAlmostComplex Jb hJb one L (equivRealProdCLM.symm z) x v))
    (hLs : ∀ L ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (equivRealProdCLM.symm z) y 1) x)‖ ≤ L')
    (hLt : ∀ L ∈ C, ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L') :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x₀ x_inf : ℕ → ℝ → M⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, L k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 → IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappingAlmostComplex Jb hJb one (L k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (σ.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k t, Tendsto (fun s ↦ u k (endChart zero (s, t))) atTop (𝓝 (x₀ k t))) →
      (∀ k t, Tendsto (fun s ↦ u k (endChart zero (s, t))) atBot (𝓝 (x_inf k t))) →
      (∀ k, IntegrableOn (σ.floerEnergyDensity (cappedCylinderComponent Hb (L k) 1)
        (cappedCylinderComponent Hb (L k) Complex.I) (u k ∘ endChart zero)) (univ ×ˢ Icc 0 1)) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ σ ((u k ∘ endChart zero) z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineImag) : ℝ))
        (univ ×ˢ Icc 0 1)) →
      (∀ k, IntegrableOn (fun z ↦ σ.hamiltonianCurvature (cappedCylinderComponent Hb (L k) 1)
        (cappedCylinderComponent Hb (L k) Complex.I) z ((u k ∘ endChart zero) z))
        (univ ×ˢ Icc 0 1)) →
      (∀ k, (∫ z in univ ×ˢ Icc 0 1, (SmoothBundleForm.eval₂ σ ((u k ∘ endChart zero) z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k ∘ endChart zero) z stdComplexLineImag) : ℝ)) +
        (∫ t in 0..1, Hb zero t (x₀ k t)) - (∫ t in 0..1, Hb inf t (x_inf k t)) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L₀ ∈ C, Tendsto (fun n ↦ L (φ n)) atTop (𝓝 L₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + Bb one + ∑ r, Bb r ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, σ.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        (∀ L'', IsCompact L'' → L'' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L'', σ.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L (φ n))
            (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hω := h₀.isNondegenerate
  set S₀ : Set (ℝ × ℝ) := {z | equivRealProdCLM.symm z ≠ 0}
  have hS₀ : IsOpen S₀ := isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const
  -- The structures of the family are `C²` jointly in `(L, z, x)` for `L > 4` and `z` in the
  -- capped plane: restrict the global smoothness of the family to this open set of parameters.
  have hJ' (p : ℝ × (ℝ × ℝ)) (hp : p ∈ Ioi 4 ×ˢ S₀) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × (ℝ × ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (2 : ℕ∞)
        (fun q : (ℝ × (ℝ × ℝ)) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
          ((h₀.cappingAlmostComplex Jb hJb one q.1.1
            (equivRealProdCLM.symm q.1.2)).toEndomorphism q.2)) (p, x) := by
    let U : TopologicalSpace.Opens ((ℝ × (ℝ × ℝ)) × M) :=
      ⟨(Ioi 4 ×ˢ S₀) ×ˢ univ, (isOpen_Ioi.prod hS₀).prod isOpen_univ⟩
    have hU := h₀.contMDiff_cappingAlmostComplex Jb hJb (n := 2) hJbp hJbs (q := one) (by simp)
      (ℓ := fun q : U ↦ q.val.1.1) (f := fun q : U ↦ equivRealProdCLM.symm q.val.1.2)
      (b := fun q : U ↦ q.val.2)
      ((contDiff_fst.contMDiff.comp contMDiff_fst).comp contMDiff_subtypeVal)
      (((equivRealProdCLM.symm.contDiff.comp contDiff_snd).contMDiff.comp contMDiff_fst).comp
        contMDiff_subtypeVal)
      (contMDiff_snd.comp contMDiff_subtypeVal) (fun q ↦ q.property.1.1)
      fun q ↦ eq_endCenter_one_or_of_ne_zero q.property.1.2
    exact contMDiffAt_subtype_iff (U := U) (x := ⟨(p, x), hp, trivial⟩) |>.mp (hU _)
  exact hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping
    (J := fun l z ↦
      (h₀.cappingAlmostComplex Jb hJb one l (equivRealProdCLM.symm z)).almostComplexStructureAt)
    hHb hHbs hBb (isOpen_Ioi.prod hS₀) hC hC₄ hD hD₀ (prod_mono hC₄ hD₀)
    (contDiffOn_almostComplexInChartAt_almostComplexStructureAt (n := 2)
      (J := fun q : ℝ × (ℝ × ℝ) ↦
        h₀.cappingAlmostComplex Jb hJb one q.1 (equivRealProdCLM.symm q.2)) hJ')
    (fun l _ z _ x ↦ hω.tames_iff.1 (h₀.tames_cappingAlmostComplex Jb hJb _) x) he he_inj
    hκ (fun l hl z hz x v ↦ by
      simpa only [IsNondegenerate.symplecticFormAt_apply,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJc l hl z hz x v)
    hLs hLt

end Compatible

end TauCeti.SmoothTwoForm
