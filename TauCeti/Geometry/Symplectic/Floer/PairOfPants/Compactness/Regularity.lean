/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Bubbling
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Global
import TauCeti.Geometry.Symplectic.Floer.Chart
import TauCeti.Topology.Order.Compact

/-!
# The limit of Floer pairs of pants in a closed manifold is a Floer solution

Let `ω` be a nondegenerate two-form on a closed manifold `M`, such as a closed symplectic manifold,
and let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of
period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q` on the three ends of `S = ℂ ∖ {0, 1}`.
A sequence of Floer pairs of pants `uₖ : S → M` of bounded topological energy has a subsequence
which converges on `S` off a finite set `Z` of bubbling points, with energy densities eventually
bounded near every point of `S \ Z`: in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`, this is
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_thricePuncturedSphereReal`,
in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Global`. This file proves that for
smooth solutions the limit `v` is itself a Floer pair of pants on `S \ Z`: `v` is `C¹` on
`S \ Z`, it solves `(dv - X_K)^{0,1} = 0` there, and the solutions converge to it
in `C¹`, in the sense that the derivatives of the coordinate expressions in every chart of `M`
converge locally uniformly. In the same namespace, this is
`exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_thricePuncturedSphereReal`.

Each `uₖ` is smooth, so its energy density is continuous and hence bounded on every compact set;
together with the eventual local bounds, the energy densities along the subsequence are then
uniformly bounded on every compact subset of `S \ Z`
(`IsCompact.exists_forall_le_of_eventually_nhds`). Bounded energy densities bound the
derivatives of the solutions in the charts of `M`, so the elliptic `C¹` convergence theorem for
the coordinate Floer equation applies near every point of `S \ Z`
(`SmoothTwoForm.IsNondegenerate.contMDiffOn_and_isComplexLinearMap_of_tendstoLocallyUniformlyOn`).
Since the convergence off `Z` was obtained on all of `S` at once, with one quantum `δ` of energy
for the windows of the core and of the ends, no new bubbling point appears in this step.

The bubbles at the points of `Z`, the breaking of Floer cylinders off the ends and the energy of
the limit are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Appendix B (elliptic regularity).
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compactness of the moduli spaces of the pair-of-pants product.
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

/-- **Floer pairs of pants in a closed manifold converge in `C¹` off finitely many bubbling
points, to a Floer pair of pants.** Let `ω` be a nondegenerate two-form on a closed manifold `M`,
such as a closed symplectic manifold, let `K` be the pair-of-pants perturbation of period-one `C³`
Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `J(z, x)` be structures on the tangent spaces of
`M`, tamed by `ω` for `z ∈ S = ℂ ∖ {0, 1}` (read in real coordinates) and `C²` read in the chart at
every point of `M`, which beyond `T₀` on each end `q` are structures `J_q(t, x)` in the end
coordinates. Let `e : M → F` be an injective `C¹` map into a normed space, such as the Whitney
embedding. There is a threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions
of `(du - X_K)^{0,1} = 0` on `S` for `J(z, u)`, whose end loops `t ↦ uₖ(φ_q(±R + i t))` converge
pointwise to loops `xₖ(q)` as `R → ∞`, with integrable energy and area densities and topological
energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ A`. Then there are a subsequence `φ`, a finite
set `Z ⊆ S` with `#Z * δ ≤ A + B_0 + B_1 + B_∞` and a map `v` such that, along `φ`,

* every disc about a point of `Z` eventually carries energy at least `δ`;
* the energy densities are uniformly bounded on every compact subset of `S \ Z`;
* `v` is `C¹` on `S \ Z`, and the solutions converge to `v` on `S \ Z`, locally uniformly after
  applying `e` and pointwise in `M`;
* the convergence holds in `C¹`: for every `α ∈ M`, the derivatives of the coordinate expressions
  `extChartAt I α ∘ u_{φ n}` converge to the derivative of `extChartAt I α ∘ v` locally uniformly
  on the open set of points of `S \ Z` at which `v` lies in the source of the chart at `α`;
* `v` solves the Floer equation `(dv - X_K)^{0,1} = 0` on `S \ Z` for `J(z, v)`. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_thricePuncturedSphereReal
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    {T₀ : ℝ} {Jq : Puncture → ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJe : ∀ q s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq q t x)
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) (he_inj : Injective e) :
    ∃ δ > 0, ∀ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃A : ℝ⦄,
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono φ ∧
        ↑Z ⊆ thricePuncturedSphereReal ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ thricePuncturedSphereReal,
          ω.floerEnergyDensity
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u (φ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ thricePuncturedSphereReal \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L,
          ω.floerEnergyDensity
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u (φ n)) y ≤ A') ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (thricePuncturedSphereReal \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop
          (thricePuncturedSphereReal \ ↑Z) ∧
        (∀ z ∈ thricePuncturedSphereReal \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z))) ∧
        (∀ α, TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u (φ n)))
          (fderiv ℝ (extChartAt I α ∘ v)) atTop
          ((thricePuncturedSphereReal \ ↑Z) ∩ v ⁻¹' (extChartAt I α).source)) ∧
        ∀ y ∈ thricePuncturedSphereReal \ ↑Z,
          IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (v y))
            (ω.perturbedMFDeriv
              (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
              (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
              v y).toLinearMap := by
  set S := thricePuncturedSphereReal
  have hS : IsOpen S := isOpen_thricePuncturedSphereReal
  have hX (w : ℂ) (α : M) :=
    hω.contDiffOn_hamiltonianVectorFieldInChartAt_pairOfPantsPerturbation hH hHs w α
  obtain ⟨δ, hδ, h0⟩ :=
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_thricePuncturedSphereReal
      hω hH hHs hB hJ hJt hJe he he_inj
  refine ⟨δ, hδ, fun u x A hu hfl hx hE hA htop ↦ ?_⟩
  obtain ⟨φ, Z, v, hφ, hZ, hcard, hconc, hbd, hv, hconv, hpt⟩ :=
    h0 (fun k ↦ (hu k).of_le (by norm_cast)) hfl hx hE hA htop
  have hSZ : IsOpen (S \ ↑Z) := hS.sdiff Z.finite_toSet.isClosed
  -- The energy densities are continuous, so their eventual bounds are bounds along the whole
  -- subsequence.
  have hbd' (L : Set (ℝ × ℝ)) (hL : IsCompact L) (hLZ : L ⊆ S \ ↑Z) :
      ∃ A', ∀ n, ∀ y ∈ L, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
        (u (φ n)) y ≤ A' := by
    exact hL.exists_forall_le_of_eventually_nhds (fun n ↦
      (ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt hS
        ((hu (φ n)).of_le (by norm_cast)) (fun α ↦ (hX 1 α).continuousOn)
        fun α ↦ (hX Complex.I α).continuousOn).mono (hLZ.trans sdiff_subset))
      fun y hy ↦ hbd y (hLZ hy)
  -- Off the bubbling points, the limit is a `C¹` Floer solution.
  obtain ⟨hvC1, hdconv, hvfl⟩ := hω.contMDiffOn_and_isComplexLinearMap_of_tendstoLocallyUniformlyOn
    hS isCompact_univ (fun α _ ↦ hJ α) (fun α _ ↦ hX 1 α) (fun α _ ↦ hX Complex.I α)
    he.continuous.continuousOn he_inj.injOn hSZ sdiff_subset (fun z hz ↦ hJt z hz.1)
    (fun n ↦ (hu (φ n)).mono sdiff_subset) (fun _ ↦ mapsTo_univ _ _)
    (fun n z hz ↦ hfl (φ n) z hz.1) hbd' hv (mapsTo_univ _ _) hconv hpt
  exact ⟨φ, Z, v, hφ, hZ, hcard, hconc, hbd', hvC1, hconv, hpt, fun α ↦ hdconv α (mem_univ α),
    hvfl⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
