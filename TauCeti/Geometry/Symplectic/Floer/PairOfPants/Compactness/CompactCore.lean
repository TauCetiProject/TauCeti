/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
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
target `(V, ω)`.

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
    (hcore : ∀ z ∈ U, ∀ q : Puncture, q.endSign * (q.endCoord (equivRealProdCLM.symm z)).re ≤ 1)
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
