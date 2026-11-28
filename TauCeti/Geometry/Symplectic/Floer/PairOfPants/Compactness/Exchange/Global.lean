/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Global
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange

/-!
# Compactness of the input-exchange family on the whole pair of pants

Graded commutativity of the pair-of-pants product compares the product with the product of the
exchanged inputs through the input-exchange family of Floer data on `S = ℂ ∖ {0, 1}`: the
perturbations `K_c = TauCeti.Floer.exchangePerturbation H c`, `c ∈ [0, 1]`, whose output end is
the end at `∞` recentred at `c`. Gromov–Floer compactness for this family is known on one compact
window of `S` at a time
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_exchange` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). This file proves it on the whole domain, in a
closed manifold `M`: a sequence of solutions for parameters in a compact window `C ⊆ [0, 1]`, of
topological energy at most `A`, has a subsequence whose parameters converge in `C` and which
converges on all of `S` off a finite set `Z` of bubbling points, with
`#Z * δ ≤ A + B₀ + B₁ + B_∞` for a threshold `δ > 0` that depends only on the data. This is the
finiteness of the bubbling set that the sphere trees at the bubbling points and the
breaking along the ends of the commutativity homotopy start from.

The family is cylindrical on its ends with data independent of `c`, but its output end moves
with `c`: beyond the height `2` of the input end `q`, `K_c` is `H_q(t) dt`
(`TauCeti.Floer.exchangePerturbation_eq_smul_endAngularForm`), and beyond the height `2` of the
output end `w ↦ K_c(w + c)` is `H_∞(t) dt`
(`TauCeti.Floer.exchangePerturbation_add_eq_smul_endAngularForm`). These are the hypotheses of
the whole-domain compactness theorem for families whose output end is recentred at a point
depending continuously on the parameter,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, with the centre `a(c) = c`. Its remaining
hypotheses are checked as for the compact windows: the components of the perturbations are `C³`
jointly in the parameter, the domain point and the target point
(`TauCeti.Floer.contMDiffAt_uncurry_exchangePerturbation_apply`), so their Hamiltonian vector
fields are `C²` in every chart and bounded over compact parts of `C × S`, and the Floer energy
over `S` exceeds the topological energy by at most `B₀ + B₁ + B_∞`
(`IsNondegenerate.setIntegral_floerEnergyDensity_exchangePerturbation_le`).

The structures `J_c` are taken cylindrical beyond some height `T₀` on each end, in the end chart
of an input end and in the end chart recentred at `c` of the output end, with end structures
independent of `c`. The bubbles at the points of `Z`, the regularity of the limit and the Floer
cylinders breaking off along the three ends are not treated here.

## Main results

* `exists_pos_forall_tendstoLocallyUniformlyOn_off_finset_exchange_thricePuncturedSphereReal`, in
  the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`: whole-domain compactness off finitely many
  bubbling points for the input-exchange family in a closed manifold.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points on a noncompact domain).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {e : M → F}

/-- **Solutions of the input-exchange family in a closed manifold converge off finitely many
bubbling points on the whole pair of pants.** Let `ω` be a nondegenerate two-form on a closed
manifold `M`, let `H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, and let `K_c` be the
perturbations of the input-exchange family. Let `J_c(z, x)` be structures on the tangent spaces of
`M`, tamed by `ω` for `c` in a compact window `C ⊆ [0, 1]` of parameters and `z ∈ S = ℂ ∖ {0, 1}`
(in real coordinates), which read in the chart at every point of `M` are `C²` jointly in
`(c, z, y)` on `W × (chart target)` for an open `W ⊇ C × S`, and which beyond `T₀` are structures
`J_q(t, x)` independent of `c` in the end coordinates of each input end `q` and of the output end
recentred at `c`. Let `e : M → F` be an injective `C¹` map into a normed space, such as the Whitney
embedding, and over every compact `D ⊆ S` let the structures `J_c`, `c ∈ C`, be uniformly tame
with respect to `e`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
maps from `S` to `M` solving the Floer equation `(du - X_{K_{cₖ}})^{0,1} = 0` for the structures
`J_{cₖ}(z, u)`, with `cₖ ∈ C`, whose input loops `uₖ(φ_q(R + i t))` and recentred output loops
`uₖ(cₖ + φ_∞(-R + i t))` converge pointwise to loops `xₖ q` as `R → ∞`, whose Floer energy and
symplectic area densities are integrable over `S`, and whose topological energy
`∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ q t) dt` is at most `A`. Then there are a subsequence `φ`, a limit
`c₀ ∈ C` of the parameters `c_{φ n}`, a finite set `Z ⊆ S` with `#Z * δ ≤ A + B₀ + B₁ + B_∞` and a
map `v : S \ Z → M`, continuous, such that along `φ` every disc about a point of `Z` eventually
carries energy at least `δ`, the energy densities are eventually bounded near every point of
`S \ Z`, and the solutions converge to `v` on `S \ Z`, locally uniformly after applying `e` and
pointwise in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_off_finset_exchange_thricePuncturedSphereReal
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (ℝ × (ℝ × ℝ))} {C : Set ℝ} (hW : IsOpen W) (hC : IsCompact C)
    (hC₀₁ : C ⊆ Icc 0 1) (hCW : C ×ˢ thricePuncturedSphereReal ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ c ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J c z x))
    (hJc : ∀ D, IsCompact D → D ⊆ thricePuncturedSphereReal → ∃ κ > 0, ∀ c ∈ C, ∀ z ∈ D,
      ∀ x v, κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J c z x v))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ c ∈ C, ∀ q, q ≠ .inf → ∀ s t x, T₀ ≤ s →
      J c (endChart q (q.endSign * s, t)) x = Jq q t x)
    (hJe' : ∀ c ∈ C, ∀ s t x, T₀ ≤ s → J c (endChart .inf (-s, t) + (c, 0)) x = Jq .inf t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃A : ℝ⦄,
      (∀ k, c k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, ∀ q ≠ Puncture.inf, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑R + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, ∀ t : ℝ, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (↑(c k) + Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) atTop
          (𝓝 (x k Puncture.inf t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ c₀ ∈ C, Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧
        ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), ↑Z ⊆ thricePuncturedSphereReal ∧
        Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ thricePuncturedSphereReal,
          ω.floerEnergyDensity
            (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x Complex.I)
            (u (φ n)) y) ∧
        (∀ y ∈ thricePuncturedSphereReal \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A', ∀ᶠ n in atTop, ∀ w ∈ N,
          ω.floerEnergyDensity
            (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x Complex.I)
            (u (φ n)) w ≤ A') ∧
        ContinuousOn v (thricePuncturedSphereReal \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          (thricePuncturedSphereReal \ ↑Z) ∧
        ∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  set S := thricePuncturedSphereReal
  -- Each component `(c, z) ↦ K_c(z)(w)` of the perturbations is `C³` jointly in the parameter,
  -- the domain point of `S` and the target point, so its Hamiltonian vector field is `C²` in
  -- every chart, and bounded over compact parts of `C × S`.
  have hK (w : ℂ) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ univ ×ˢ S) (x : M) :=
    contMDiffAt_uncurry_exchangePerturbation_apply (n := (2 : ℕ∞) + 1) hH hHs w hp.2 x
  have hWS : IsOpen (W ∩ univ ×ˢ S) := hW.inter (isOpen_univ.prod isOpen_thricePuncturedSphereReal)
  have hCWS : C ×ˢ S ⊆ W ∩ univ ×ˢ S := subset_inter hCW (prod_mono (subset_univ _) subset_rfl)
  have hBD (D : Set (ℝ × ℝ)) (hD : IsCompact D) (hDS : D ⊆ S) :
      ∃ L, ∀ c ∈ C, ∀ z ∈ D, ∀ x,
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ exchangePerturbation H c (equivRealProdCLM.symm z) y 1) x)‖ ≤ L ∧
        ‖mvfderiv I e x (ω.hamiltonianVectorField
          (fun y ↦ exchangePerturbation H c (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L := by
    have hL (w : ℂ) := hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le_of_isCompact
      (hC.prod hD) he (f := fun (p : ℝ × (ℝ × ℝ)) y ↦
        exchangePerturbation H p.1 (equivRealProdCLM.symm p.2) y w)
      fun p hp x ↦ (hK w p ⟨mem_univ _, hDS hp.2⟩ x).of_le (by norm_num)
    obtain ⟨Ls, hLs⟩ := hL 1
    obtain ⟨Lt, hLt⟩ := hL Complex.I
    exact ⟨max Ls Lt, fun c hc z hz x ↦ ⟨(hLs (c, z) ⟨hc, hz⟩ x).trans (le_max_left _ _),
      (hLt (c, z) ⟨hc, hz⟩ x).trans (le_max_right _ _)⟩⟩
  -- Beyond the height `2` the family is `H_q(t) dt` on the input ends, and its translate by `c` is
  -- `H_∞(t) dt` on the output end.
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset_of_recentered
      (K := fun c ↦ exchangePerturbation H c) (J := J) hWS hC hCWS
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).mono
        (prod_mono inter_subset_right subset_rfl))
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).mono
        (prod_mono inter_subset_right subset_rfl))
      hJt hJc hBD (a := id) continuousOn_id (T₀ := max T₀ 2)
      (fun c hc q hq w x hw ↦ exchangePerturbation_eq_smul_endAngularForm (hC₀₁ hc).1
        (hC₀₁ hc).2 hq ((le_max_right _ _).trans hw) x)
      (fun c hc w x hw ↦ exchangePerturbation_add_eq_smul_endAngularForm (hC₀₁ hc).1
        (hC₀₁ hc).2 ((le_max_right _ _).trans hw) x) hH hHs
      (fun c hc q hq s t x hs ↦ hJe c hc q hq s t x ((le_max_left _ _).trans hs))
      (fun c hc s t x hs ↦ hJe' c hc s t x ((le_max_left _ _).trans hs)) he he_inj
  refine ⟨δ, hδ, fun c u x A hcC hu hfl hx hxinf hint harea htop ↦ ?_⟩
  -- The Floer energy over `S` is at most the topological energy plus `B₀ + B₁ + B_∞`.
  exact hconv (p := c) (E := A + ∑ q, B q) hcC hu hfl hint fun k ↦
    hω.setIntegral_floerEnergyDensity_exchangePerturbation_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀₁ (hcC k)).1 (hC₀₁ (hcC k)).2
      ((hu k).of_le (by norm_num)) (hx k) (hxinf k) (hint k) (harea k)
      (fun z hz ↦ hJt _ (hcC k) z hz _) (hfl k) (htop k) subset_rfl

end TauCeti.SmoothTwoForm.IsNondegenerate
