/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.CompactCore

/-!
# Compactness of pairs of pants with core perturbations in a closed manifold

Transversality for the pair-of-pants product perturbs the canonical datum
`K = TauCeti.Floer.pairOfPantsPerturbation H` on `S = ℂ ∖ {0, 1}` by Hamiltonian one-forms
`δ_p = δ_{s,p} ds + δ_{t,p} dt`, depending on a parameter `p` of a finite-dimensional space `P`,
supported in a compact set `D` of the interior of the core, where `K` vanishes. The universal
moduli space of the transversality argument consists of the pairs `(p, u)` with `u` a solution of
`(du - X_{K + δ_p})^{0,1} = 0`. This file proves the interior part of Gromov–Floer compactness for
these solutions in a closed manifold `M`, uniformly over a compact window `A` of parameters, with
no condition on where the solutions take their values. The theorems of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.CompactCore` assume instead that the
images stay in a compact subset of one symplectic chart.

The compactness theorem over a compact parameter window in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in
the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
applies once its hypotheses are checked for the family.

* **The data in the charts of `M`.** The components of `K + δ_p` are smooth jointly in the
  parameter, the domain point of `S` and the target point
  (`TauCeti.Floer.contMDiffAt_uncurry_pairOfPantsPerturbation_add`), so their Hamiltonian vector
  fields read in the chart at any point of `M` are `C²` in `(p, z, y)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.contDiffOn_hamiltonianVectorFieldInChartAt`).
* **The energy bound.** Since `M` is compact, the whole of `M` is a compact target window for the
  core, so there is a constant `c ≥ 0` such that, uniformly in `p ∈ A`, the Floer energy over `S`
  exceeds the topological energy `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` by at most
  `B₀ + B₁ + B_∞ + c`
  (`IsNondegenerate.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le` in
  the namespace `TauCeti.SmoothTwoForm`). The energy density is integrable once the area density
  is (`IsNondegenerate.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_add`), so only the
  area density is assumed integrable; both facts are combined in
  `IsNondegenerate.exists_integrableOn_and_setIntegral_le_pairOfPantsPerturbation_add`.
* **The Hamiltonian vector fields.** On a compact window of parameters and of `S`, the
  pushforwards through a `C¹` map `e : M → F` of the Hamiltonian vector fields of the components
  of `K + δ_p` are bounded, uniformly in the target point, since the components are `C¹` in
  `(p, z, x)` there and `M` is compact
  (`IsNondegenerate.exists_forall_norm_mvfderiv_hamiltonianVectorField_le_of_isCompact` in the
  namespace `TauCeti.SmoothTwoForm`).

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation_add`:
  for any family `J_p(z, x)` of tame structures which is `C²` read in the charts of `M` near the
  parameter and domain windows, there are a constant `c ≥ 0` and a threshold `δ > 0` such that
  every sequence of solutions for parameters `pₖ` in a compact window `A`, with topological energy
  at most `E`, has a subsequence whose parameters converge to some `p₀ ∈ A` and which converges on
  an open `Ω ⊆ D'` off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ E + B₀ + B₁ + B_∞ + c`.
* `exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_add_le`: the bounds
  on the pushforwards of the Hamiltonian vector fields that the first theorem takes hold for every
  `C¹` map `e`, `C¹` Hamiltonians `H_q` and `C¹` family `δ`.

The regularity of the limit, the bubbles at the points of `Z` and breaking along the three ends
are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (Hamiltonian perturbations of the
  inhomogeneous equation and their energy).
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}
  {e : M → F}

/-- **The Hamiltonian vector fields of the core-perturbed datum are bounded on compact windows.**
Let `M` be compact, let `H_q` be period-one `C¹` Hamiltonians, and let `δ_p(z, x)` be `C¹` jointly
in the parameter `p`, the real coordinates `z` of `S = ℂ ∖ {0, 1}` and the target point `x`. On a
compact window `A` of parameters and a compact part `D'` of `S`, the pushforwards through a `C¹` map
`e : M → F` of the Hamiltonian vector fields of a component `K(z)(w) + δ_p(z)` of the pair-of-pants
perturbation plus `δ_p` are bounded, uniformly in the target point. These are the bounds that
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation_add`
takes on its windows. -/
theorem exists_forall_norm_mvfderiv_hamiltonianVectorField_pairOfPantsPerturbation_add_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {δ : P → ℝ × ℝ → M → ℝ} (hδ : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (P × (ℝ × ℝ)) × M ↦ δ q.1.1 q.1.2 q.2))
    (he : ContMDiff I 𝓘(ℝ, F) 1 e) {A : Set P} {D' : Set (ℝ × ℝ)} (hA : IsCompact A)
    (hD' : IsCompact D') (hD'S : D' ⊆ thricePuncturedSphereReal) (w : ℂ) :
    ∃ L, ∀ p ∈ A, ∀ z ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y w + δ p z y) x)‖ ≤ L := by
  obtain ⟨L, hL⟩ := hω.exists_forall_norm_mvfderiv_hamiltonianVectorField_le_of_isCompact
    (hA.prod hD') he fun r hr x ↦ contMDiffAt_uncurry_pairOfPantsPerturbation_add hH hHs hδ
      (hD'S hr.2) x w
  exact ⟨L, fun p hp z hz ↦ hL (p, z) ⟨hp, hz⟩⟩

variable [I.Boundaryless] [FiniteDimensional ℝ P] {B : Puncture → ℝ}

/-- **Floer pairs of pants with core perturbations in a closed manifold converge off finitely many
bubbling points, uniformly over a compact window of parameters.** Let `ω` be a nondegenerate
two-form on a closed manifold `M`, let `K` be the pair-of-pants perturbation of period-one `C³`
Hamiltonians `H_q` with `|H_q| ≤ B_q`, and let `δ_p = δ_{s,p} ds + δ_{t,p} dt` be a jointly `C³`
family of perturbations, for parameters `p` of a finite-dimensional space `P`, supported for `p` in
a compact window `A` in a common compact set `D` of the core: `D` lies in an open set `U` on which
the signed longitudinal coordinate of every end is at most `1`. Let `J_p(z, x)` be structures on the
tangent spaces of `M`, tamed by `ω` for `p ∈ A` and `z ∈ S = ℂ ∖ {0, 1}` (in real coordinates),
which read in the chart at every point of `M` are `C²` jointly in `(p, z, y)` on `W × (chart
target)`, for an open `W` containing `A × D'` with `D' ⊆ S` compact. Let `e : M → F` be injective
and differentiable, with the structures uniformly tame with respect to `e` over `A × D'`,
`κ ‖d e v‖² ≤ ω(v, J_p(z) v)` with `κ > 0`, and the pushforwards through `e` of the Hamiltonian
vector fields of the two components of `K + δ_p` at most `L` there. There are a constant `c ≥ 0` and
a threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps from `S` to `M` solving
`(du - X_{K + δ_{pₖ}})^{0,1} = 0` for the structures `J_{pₖ}(z, u)`, with `pₖ ∈ A`, whose end loops
`uₖ(φ_q(±R + i t))` converge pointwise to loops `xₖ q` as `R → ∞`, whose symplectic area densities
are integrable over `S`, and whose topological energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ q t) dt`
is at most `E`, and let `Ω ⊆ D'` be open. Then there are a subsequence `φ`, a limit `p₀ ∈ A` of the
parameters `p_{φ n}` and a finite set `Z ⊆ Ω` with `#Z * δ ≤ E + B₀ + B₁ + B_∞ + c` such that, along
`φ`, every disc about a point of `Z` eventually carries energy at least `δ`, the energy densities
are uniformly bounded on every compact subset of `Ω \ Z`, and the solutions converge on `Ω \ Z` to a
continuous map `v`, locally uniformly after applying `e` and pointwise in `M`. -/
theorem
  exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_pairOfPantsPerturbation_add
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : P → ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 3
      (fun q : (P × (ℝ × ℝ)) × M ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 3
      (fun q : (P × (ℝ × ℝ)) × M ↦ δt q.1.1 q.1.2 q.2))
    {A : Set P} {D U : Set (ℝ × ℝ)} (hA : IsCompact A) (hD : IsCompact D) (hU : IsOpen U)
    (hDU : D ⊆ U) (hcore : ∀ z ∈ U, ∀ q : Puncture, (positiveEndCoord q z).1 ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {W : Set (P × (ℝ × ℝ))} {D' : Set (ℝ × ℝ)} (hW : IsOpen W) (hD' : IsCompact D')
    (hD'S : D' ⊆ thricePuncturedSphereReal) (hAD'W : A ×ˢ D' ⊆ W)
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α (uncurry J))
      (W ×ˢ (extChartAt I α).target))
    (hJt : ∀ p ∈ A, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {κ L : ℝ} (hκ : 0 < κ)
    (hJc : ∀ p ∈ A, ∀ z ∈ D', ∀ x v,
      κ * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J p z x v))
    (hLs : ∀ p ∈ A, ∀ z ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1 + δs p z y) x)‖ ≤ L)
    (hLt : ∀ p ∈ A, ∀ z ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I + δt p z y) x)‖ ≤
        L) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄
      ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D' → (∀ k, p k ∈ A) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p k) z x)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I +
              δt (p k) z x) (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ E) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p₀ ∈ A, Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E + ((∑ q, B q) + c) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p (φ n)) z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I +
            δt (p (φ n)) z x) (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p (φ n)) z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I +
            δt (p (φ n)) z x) (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  set S := thricePuncturedSphereReal
  -- Since `M` is compact, the whole of `M` is a compact target window for the core.
  obtain ⟨c, hc, hbound⟩ :=
    hω.exists_integrableOn_and_setIntegral_le_pairOfPantsPerturbation_add hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hδs.of_le (by norm_num))
      (hδt.of_le (by norm_num)) hA hD isCompact_univ hU hDU hcore hs ht
  -- Each component of `K + δ_p` is `C³` jointly in the parameter, the domain point of `S` and the
  -- target point, so its Hamiltonian vector field is `C²` in every chart.
  have hX (w : ℂ) {δ' : P → ℝ × ℝ → M → ℝ}
      (hδ' : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 3
        (fun q : (P × (ℝ × ℝ)) × M ↦ δ' q.1.1 q.1.2 q.2)) (α : M) :=
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (U := univ ×ˢ S)
      (fun r hr x ↦ (contMDiffAt_uncurry_pairOfPantsPerturbation_add hH hHs hδ' hr.2 x
        w).of_le (by norm_num)) α).mono (prod_mono (inter_subset_right (s := W)) subset_rfl)
  have hWS : IsOpen (W ∩ univ ×ˢ S) := hW.inter (isOpen_univ.prod isOpen_thricePuncturedSphereReal)
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_comp_subseq_off_finset
      (Ks := fun p z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
      (Kt := fun p z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I + δt p z x)
      he he_inj hWS hA hD' (subset_inter hAD'W (prod_mono (subset_univ _) hD'S))
      (fun α ↦ (hJ α).mono (prod_mono inter_subset_left subset_rfl)) (hX 1 hδs) (hX Complex.I hδt)
      (fun p hp z hz ↦ hJt p hp z (hD'S hz)) hκ hJc hLs hLt
  refine ⟨c, hc, δ, hδ, fun Ω p u x E hΩ hΩD hpA hu hfl hx harea htop ↦ ?_⟩
  have hΩS : Ω ⊆ S := hΩD.trans hD'S
  -- The energy density is integrable, and the energy over `Ω` is at most `E + B₀ + B₁ + B_∞ + c`.
  have hE (k : ℕ) := hbound (p k) (hpA k) (u k) ((hu k).of_le (by norm_num))
    (fun _ _ ↦ mem_univ _) (x k) (hx k) (harea k) (fun z ↦ J (p k) z (u k z))
    (fun z hz ↦ hJt _ (hpA k) z hz _) (hfl k)
  exact hconv hΩ hΩD hpA (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz))
    (fun k ↦ (hE k).1.mono_set hΩS) fun k ↦ ((hE k).2 Ω hΩS).trans (by linarith [htop k])

end TauCeti.SmoothTwoForm.IsNondegenerate
