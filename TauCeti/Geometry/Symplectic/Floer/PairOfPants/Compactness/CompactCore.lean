/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.CompactCore

/-!
# Compactness of pairs of pants with core perturbations

Transversality for the pair-of-pants product perturbs the canonical datum
`K = TauCeti.Floer.pairOfPantsPerturbation H` on `S = ℂ ∖ {0, 1}` by Hamiltonian one-forms
`δ_p = δ_{s,p} ds + δ_{t,p} dt`, depending on a parameter `p`, supported in a compact set `D` of
the interior of the core: `D` lies in an open set `U` on which the signed longitudinal coordinate
of every end is at most `1`, so that `K` vanishes on `U`. The universal moduli space of the
transversality argument consists of the pairs `(p, u)` with `u` a solution of
`(du - X_{K + δ_p})^{0,1} = 0`. This file proves the interior part of Gromov–Floer compactness for
these solutions, uniformly over a compact window of parameters, for a symplectic vector space
target `(V, ω)` and for solutions in a symplectic chart of a manifold.

**The energy bound.** For a compact parameter window `A` and a compact target window `Q`
containing `u(D)`, a solution `u` with tamed almost complex structures whose end loops have limiting
actions `a_q` has integrable energy at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞ + C`, for bounds
`|H_q| ≤ B_q` and a constant `C` independent of `p ∈ A` and of `u`
(`SymplecticForm.exists_integrable_and_integral_floerEnergyDensity_pairOfPantsPerturbation_add_le`
in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.CompactCore`).

**Compactness.** The data `K + δ_p` and almost complex structures `J_p(z, x)` are jointly smooth in
`(p, z, x)`, so the compactness theorem over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D'` of `S`. The main result,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation_add`
in the namespace `TauCeti.SymplecticForm`, gives a constant `C ≥ 0` and a threshold `δ > 0` such
that every sequence of solutions for parameters `pₖ ∈ A`, with action differences
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ E`, core images in `Q` and images of an open `Ω ⊆ D'` in a compact `L`,
has a subsequence whose parameters converge to some `p₀ ∈ A` and which converges locally uniformly
on `Ω` off a finite set `Z` of bubbling points, with `#Z * δ ≤ E + B_0 + B_1 + B_∞ + C`. The
regularity of the limit, the bubbles at the points of `Z`, and breaking along the three ends are
not treated here.

**A manifold target.** Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`,
such as a closed symplectic manifold, and let `φ : M ⊇ U → V` be a symplectic chart onto an open
subset of a symplectic vector space `(V, ω₀)`, such as a Darboux chart. For solutions
`u : S → M` whose image of an open `Ω ⊆ D'` stays in a compact subset of the source of `φ`, the
same conclusion holds for the coordinate maps `φ ∘ u`, and the solutions converge pointwise in `M`
off `Z`
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation_add`
in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). Its two inputs are the uniform energy
bound for a manifold target
(`IsNondegenerate.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le` in the
namespace `TauCeti.SmoothTwoForm`), which bounds the energy by the topological energy
`∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` plus `B_0 + B_1 + B_∞ + C`, and the compactness theorem in
a symplectic chart over a compact parameter window
(`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`), which applies because the data `K + δ_p` read in the
chart, `(p, z, y) ↦ (K + δ_p)(z, φ⁻¹ y)`, are jointly `C³`
(`TauCeti.Floer.contDiffOn_pairOfPantsPerturbation_add_comp_symm`). The energy density of a
solution is integrable once its area density is
(`IsNondegenerate.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_add`), so only the area
density is assumed integrable. Localizing the images of small discs into charts on a closed
manifold is not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (Hamiltonian perturbations of the
  inhomogeneous equation and their energy).
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

section Compactness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {B : Puncture → ℝ}
  {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- **Floer pairs of pants with core perturbations converge off finitely many bubbling points,
uniformly over a compact window of parameters.** Let `K` be the pair-of-pants perturbation of
period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q`, let `δ_p = δ_{s,p} ds + δ_{t,p} dt` be a
jointly `C³` family of perturbations supported in a common compact set `D` of the core for
parameters `p` in a compact set `A`, as in
`SymplecticForm.exists_integrable_and_integral_floerEnergyDensity_pairOfPantsPerturbation_add_le`,
and let `J_p(z, x)` be a family of almost complex structures, jointly `C²` on `P × S × V` and
tamed by `ω` for `p ∈ A`. Fix a compact target window `Q` for the core, and compact sets
`D' ⊆ S` and `L ⊆ V`. There are a constant `C ≥ 0` and a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` solutions of `(du - X_{K + δ_{pₖ}})^{0,1} = 0` on `S` for
`J_{pₖ}(z, u)`, with parameters `pₖ ∈ A`, limiting end actions `aₖ(q)` satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ E`, `uₖ(D) ⊆ Q`, and `uₖ(Ω) ⊆ L` for an open `Ω ⊆ D'`. Then there are a
subsequence `φ`, a limit parameter `p₀ ∈ A` of `p_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ E + B_0 + B_1 + B_∞ + C`, and a continuous `v : Ω \ Z → L` such that along `φ` every
disc about a point of `Z` eventually carries energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem
  exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation_add
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) (hB : ∀ q t x, |H q t x| ≤ B q)
    {δs δt : P → ℝ × ℝ → V → ℝ}
    (hδs : ContDiff ℝ 3 (fun q : (P × (ℝ × ℝ)) × V ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContDiff ℝ 3 (fun q : (P × (ℝ × ℝ)) × V ↦ δt q.1.1 q.1.2 q.2))
    {A : Set P} {D U : Set (ℝ × ℝ)} {Q : Set V}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture, (positiveEndCoord q z).1 ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0)
    {J : P → ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2
      (fun r : P × ((ℝ × ℝ) × V) ↦ (J r.1 r.2.1 r.2.2).toLinearMap.toContinuousLinearMap)
      (univ ×ˢ (thricePuncturedSphereReal ×ˢ univ)))
    (hJt : ∀ p ∈ A, ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J p z x))
    {D' : Set (ℝ × ℝ)} {L : Set V} (hD' : IsCompact D') (hD'S : D' ⊆ thricePuncturedSphereReal)
    (hL : IsCompact L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄
      ⦃a : ℕ → Puncture → ℝ⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D' → (∀ k, p k ∈ A) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p k) z x)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt (p k) z x)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ E) →
      (∀ k, ∀ z ∈ D, u k z ∈ Q) → (∀ k, MapsTo (u k) Ω L) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ A ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ E + ((∑ q, B q) + C) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p (φ n)) z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt (p (φ n)) z x)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) L ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  obtain ⟨C, hC, henergy⟩ :=
    ω.exists_integrable_and_integral_floerEnergyDensity_pairOfPantsPerturbation_add_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hδs.of_le (by norm_num))
      (hδt.of_le (by norm_num)) hA hD hQ hU hDU hcore hs ht
  have hW : IsOpen (univ ×ˢ (thricePuncturedSphereReal ×ˢ (univ : Set V)) : Set (P × _)) :=
    isOpen_univ.prod (isOpen_thricePuncturedSphereReal.prod isOpen_univ)
  -- The perturbed data are jointly `C³` in the parameter and the domain and target points.
  have hKc (v : ℂ) {δ' : P → ℝ × ℝ → V → ℝ}
      (hδ' : ContDiff ℝ 3 (fun q : (P × (ℝ × ℝ)) × V ↦ δ' q.1.1 q.1.2 q.2)) :
      ContDiffOn ℝ 3 (fun r : P × ((ℝ × ℝ) × V) ↦
        pairOfPantsPerturbation H (equivRealProdCLM.symm r.2.1) r.2.2 v + δ' r.1 r.2.1 r.2.2)
        (univ ×ˢ (thricePuncturedSphereReal ×ˢ univ)) := by
    rintro ⟨p, z, x⟩ ⟨-, hz, -⟩
    have hι : ContDiff ℝ 3 (fun r : P × ((ℝ × ℝ) × V) ↦ ((r.1, r.2.1), r.2.2)) :=
      (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).prodMk
        (contDiff_snd.comp contDiff_snd)
    exact (((contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).comp (p, z, x)
      contDiffAt_snd).add (hδ'.comp hι).contDiffAt).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun p z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
    (Kt := fun p z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt p z x)
    hW (hKc 1 hδs) (hKc I hδt) hJ hA hD' hL
    (fun r hr ↦ ⟨mem_univ _, hD'S hr.2.1, mem_univ _⟩)
    fun p hp z hz x _ ↦ hJt p hp z (hD'S hz) x
  refine ⟨C, hC, δ, hδ, fun Ω p u a E hΩ hΩD hpA hu hfl ha hE huQ huL ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hD'S
  -- Each solution has integrable energy at most `E + B_0 + B_1 + B_∞ + C`, and so does its
  -- restriction to `Ω`, since the energy density is nonnegative on `S`.
  have hen (k : ℕ) := henergy (p k) (hpA k) (u k) ((hu k).of_le (by norm_num)) (huQ k)
    (fun z ↦ J (p k) z (u k z)) (fun z hz ↦ hJt _ (hpA k) z hz _) (hfl k) (a k) (ha k)
  refine hconv hΩ hΩD hpA (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huL
    (fun k ↦ (hen k).1.integrableOn) fun k ↦ ?_
  refine (setIntegral_le_integral (hen k).1 ?_).trans ((hen k).2.trans ?_)
  · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
    exact ω.floerEnergyDensity_nonneg (hJt _ (hpA k) z hz _) (hfl k z hz)
  · simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
      Puncture.endSign_inf]
    linarith [hE k]

end Compactness

end TauCeti.SymplecticForm

namespace TauCeti.Floer

variable {E G M V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup P] [NormedSpace ℝ P] {H : Puncture → ℝ → M → ℝ}

/-- **The core-perturbed datum read in a chart is smooth.** For period-one Hamiltonians which are
`C^n` on `ℝ × M`, a family of functions `δ_p(z, x)` which is `C^n` jointly in the parameter `p`, the
real coordinates `z` of `S = ℂ ∖ {0, 1}` and the target point `x`, and a `C^n` partial
diffeomorphism `φ` from `M` to a normed space `V`, each component
`K(z, φ⁻¹ y)(w) + δ_p(z, φ⁻¹ y)` of the pair-of-pants perturbation plus `δ_p`, read in the chart, is
`C^n` jointly in `p`, `z` and the chart coordinate `y` over `S` and the target of `φ`. -/
theorem contDiffOn_pairOfPantsPerturbation_add_comp_symm {n : ℕ∞} {m : WithTop ℕ∞}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q)))
    {δ : P → ℝ × ℝ → M → ℝ} (hδ : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) n
      (fun q : (P × (ℝ × ℝ)) × M ↦ δ q.1.1 q.1.2 q.2))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hnm : (n : WithTop ℕ∞) ≤ m) (w : ℂ) :
    ContDiffOn ℝ n (fun q : P × ((ℝ × ℝ) × V) ↦
        pairOfPantsPerturbation H (equivRealProdCLM.symm q.2.1) (φ.symm q.2.2) w +
          δ q.1 q.2.1 (φ.symm q.2.2))
      (univ ×ˢ (thricePuncturedSphereReal ×ˢ φ.target)) := by
  -- The perturbation is composed with `(p, z, y) ↦ ((p, z), φ⁻¹ y)`, and the canonical datum
  -- with `(p, z, y) ↦ (z, y)`.
  have hg : ContMDiffOn 𝓘(ℝ, P × ((ℝ × ℝ) × V)) ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) n
      (fun q : P × ((ℝ × ℝ) × V) ↦ ((q.1, q.2.1), φ.symm q.2.2))
      (univ ×ˢ (thricePuncturedSphereReal ×ˢ φ.target)) :=
    (contDiff_fst.contMDiff.contMDiffOn.prodMk
      (contDiff_fst.comp contDiff_snd).contMDiff.contMDiffOn).prodMk
      ((φ.symm.contMDiffOn.of_le hnm).comp
        (contDiff_snd.comp contDiff_snd).contMDiff.contMDiffOn fun _ hq ↦ hq.2.2)
  exact ((contDiffOn_pairOfPantsPerturbation_comp_symm hH hHs φ hnm w).comp
    (s := univ ×ˢ (thricePuncturedSphereReal ×ˢ φ.target)) contDiff_snd.contDiffOn
    fun _ hq ↦ hq.2).add (contMDiffOn_iff_contDiffOn.1 (hδ.comp_contMDiffOn hg))

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {H : Puncture → ℝ → M → ℝ} {B : Puncture → ℝ}

/-- **Floer pairs of pants with core perturbations in a symplectic chart of a manifold converge off
finitely many bubbling points, uniformly over a compact window of parameters.** Let `K` be the
pair-of-pants perturbation of period-one `C³` Hamiltonians `H_q` on `M` with `|H_q| ≤ B_q`, let
`δ_p = δ_{s,p} ds + δ_{t,p} dt` be a jointly `C³` family of perturbations supported in a common
compact set `D` of the core for parameters `p` in a compact set `A`, as in
`IsNondegenerate.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le`, and let
`J_p(z, x)` be structures on the tangent spaces of `M` tamed by `ω` for `p ∈ A` and `z ∈ S`. Fix a
compact target window `Q` for the core and compact sets `D' ⊆ S` and `C ⊆ φ.source`, where `φ` is a
smooth partial diffeomorphism from `M` onto an open subset of `V` pulling `ω₀` back to `ω` at the
points of `C`, and let `J'` be the family `J` read in the chart,
`dφ_x ∘ J_p(z, x) = J'_p(z, φ x) ∘ dφ_x` for `p ∈ A`, `z ∈ D'` and `x ∈ C`, and `C²` jointly in
`(p, z, y)` on an open set containing `A × D' × φ(C)`. There are a constant `c ≥ 0` and a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions of `(du - X_{K + δ_{pₖ}})^{0,1} = 0`
on `S` for `J_{pₖ}(z, u)`, with parameters `pₖ ∈ A`, whose end loops converge pointwise to loops
`xₖ(q)`, with integrable area density and topological energy
`∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ E`, with `uₖ(D) ⊆ Q` and `uₖ(Ω) ⊆ C` for an open
`Ω ⊆ D'`. Then there are a subsequence `ψ`, a limit `p₀ ∈ A` of `p_{ψ n}`, a finite set `Z ⊆ Ω`
with `#Z * δ ≤ E + B₀ + B₁ + B_∞ + c`, and a map `v`, continuous on `Ω \ Z` with values in `C`,
such that along `ψ` every disc about a point of `Z` eventually carries energy at least `δ`, the
differentials of the coordinate maps `φ ∘ u_{ψ n}` are uniformly bounded on every compact subset
of `Ω \ Z`, the coordinate maps converge to `φ ∘ v` locally uniformly on `Ω \ Z`, and
`u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem
  exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation_add
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : P → ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 3
      (fun q : (P × (ℝ × ℝ)) × M ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 3
      (fun q : (P × (ℝ × ℝ)) × M ↦ δt q.1.1 q.1.2 q.2))
    {A : Set P} {D U : Set (ℝ × ℝ)} {Q : Set M}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture, (positiveEndCoord q z).1 ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJt : ∀ p ∈ A, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J' : P → ℝ × ℝ → V → AlmostComplexStructure V} {D' : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ p ∈ A, ∀ z ∈ D', ∀ x ∈ C,
      IsComplexLinearMap (J p z x) (J' p z (φ x)) (mvfderiv I φ x).toLinearMap)
    {W : Set (P × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hD' : IsCompact D') (hD'S : D' ⊆ thricePuncturedSphereReal) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hACW : A ×ˢ (D' ×ˢ (φ '' C)) ⊆ W) :
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
      (∀ k, ∀ z ∈ D, u k z ∈ Q) → (∀ k, MapsTo (u k) Ω C) →
      ∃ (ψ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ p₀ ∈ A ∧
        Tendsto (fun n ↦ p (ψ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ E + ((∑ q, B q) + c) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p (ψ n)) z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I +
            δt (p (ψ n)) z x) (u (ψ n)) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z →
          ∃ M', ∀ n, ∀ y ∈ L, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ M') ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  obtain ⟨c, hc, hbound⟩ :=
    hω.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (hδs.of_le (by norm_num))
      (hδt.of_le (by norm_num)) hA hD hQ hU hDU hcore hs ht
  -- Read in the chart, the perturbed data are jointly `C³` over `A × S × φ(U)`, which contains
  -- `A × D' × φ(C)`.
  have hK' (w : ℂ) {δ' : P → ℝ × ℝ → M → ℝ}
      (hδ' : ContMDiff ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 3
        (fun q : (P × (ℝ × ℝ)) × M ↦ δ' q.1.1 q.1.2 q.2)) :=
    contDiffOn_pairOfPantsPerturbation_add_comp_symm hH hHs hδ' φ (WithTop.coe_le_coe.2 le_top) w
  have hWt : IsOpen (W ∩ univ ×ˢ (thricePuncturedSphereReal ×ˢ φ.target)) :=
    hW.inter (isOpen_univ.prod (isOpen_thricePuncturedSphereReal.prod φ.open_target))
  have hACW' : A ×ˢ (D' ×ˢ (φ '' C)) ⊆ W ∩ univ ×ˢ (thricePuncturedSphereReal ×ˢ φ.target) := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hq.2.2
    exact ⟨hACW hq, trivial, hD'S hq.2.1, hxq ▸ φ.toPartialEquiv.map_source (hCφ hx)⟩
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    φ (Ks := fun p z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
    (Kt := fun p z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I + δt p z x)
    (J := J) hφ hJJ' hWt ((hK' 1 hδs).mono inter_subset_right)
    ((hK' Complex.I hδt).mono inter_subset_right) (hJ'.mono inter_subset_left) hA hD' hC hCφ hACW'
    fun p hp z hz x _ ↦ hJt p hp z (hD'S hz) x
  refine ⟨c, hc, δ, hδ, fun Ω p u x E hΩ hΩD hpA hu hfl hx harea htop huQ huC ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hD'S
  have hι (k : ℕ) : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) ((𝓘(ℝ, P).prod 𝓘(ℝ, ℝ × ℝ)).prod I) 1
      (fun r : (ℝ × ℝ) × M ↦ ((p k, r.1), r.2)) :=
    (contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd
  -- The energy density of a solution is nonnegative on `S`, hence integrable there.
  have hnn (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    floerEnergyDensity_nonneg hω (hJt _ (hpA k) z hz _) (hfl k z hz)
  have hint (k : ℕ) := hω.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_add
    (δs := δs (p k)) (δt := δt (p k)) hH (fun q ↦ (hHs q).of_le (by norm_num)) hB
    ((hδs.of_le (by norm_num)).comp (hι k)) ((hδt.of_le (by norm_num)).comp (hι k)) hD hU hDU
    hcore (hs _ (hpA k)) (ht _ (hpA k)) ((hu k).of_le (by norm_num)) (hx k) (hnn k) (harea k)
  -- The energy over `Ω` is at most the energy over `S`, hence at most `E + B₀ + B₁ + B_∞ + c`.
  have hle (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p k) z x)
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I + δt (p k) z x)
      (u k) z ≤ E + ((∑ q, B q) + c) := by
    have habs := abs_le.1 (hbound (p k) (hpA k) (u k) ((hu k).of_le (by norm_num)) (huQ k) (x k)
      (hx k) (hint k) (harea k))
    refine (setIntegral_mono_set (hint k) (ae_restrict_of_forall_mem
      isOpen_thricePuncturedSphereReal.measurableSet (hnn k))
      (Eventually.of_forall hΩS)).trans ?_
    linarith [habs.2, htop k]
  exact hconv hΩ hΩD hpA (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huC
    (fun k ↦ (hint k).mono_set hΩS) hle

end TauCeti.SmoothTwoForm.IsNondegenerate
