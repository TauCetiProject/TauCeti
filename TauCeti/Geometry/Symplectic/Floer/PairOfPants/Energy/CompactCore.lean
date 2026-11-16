/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CompactCore
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

/-!
# The energy identity on the pair of pants with core perturbations

Transversality for the pair-of-pants product perturbs the canonical datum
`K = TauCeti.Floer.pairOfPantsPerturbation H` on `S = ℂ ∖ {0, 1}` by Hamiltonian one-forms
`δ = δ_s ds + δ_t dt` supported in a compact set `D` in the interior of the core: `D` lies in an
open set `U` on which the signed longitudinal coordinate of every end is at most `1`, so that `K`
vanishes on `U`. Such a perturbation leaves the ends untouched, so the perturbed datum is still
`H_q(t) dt` far out on each end `q`, and the energy identity for data cylindrical on the ends
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_eq_smul_endAngularForm`) applies:

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_{K + δ}(u)`

for a map `u` into a finite-dimensional manifold with a nondegenerate two-form, such as a closed
symplectic manifold, whose end loops converge to loops `x_q`. Since `K` vanishes on the
neighbourhood `U` of `D`, the curvature `R_{K + δ}` is `R_K + R_δ` without mixed Poisson-bracket
terms, and both are integrable. When the energy density is nonnegative, as for solutions of the
Floer equation with tamed almost complex structures, it is moreover integrable without further
assumption.

For a compact family `δ_p` of such core perturbations, `p ∈ A`, and a compact target window
`Q ⊆ M`, the curvature allowance of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.CompactCore` is
uniform, so the energy of a map sending `D` into `Q` differs from its topological part by at most
`B₀ + B₁ + B_∞ + C`, with `C` depending on `A` and `Q` but independent of `p ∈ A` and of the map.
For solutions of the Floer equation with tamed almost complex structures, whose energy is
nonnegative, this bounds the topological part below uniformly over the family. These are the energy
bounds over compact parameter and target windows that the compactness of the perturbed problems,
used for transversality with localized Hamiltonian variations, rests on.

## Main results

* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_add`: the
  energy identity for the pair-of-pants datum with a core perturbation.
* `SmoothTwoForm.IsNondegenerate.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_add`: a
  nonnegative energy density for a core perturbation is integrable.
* `IsNondegenerate.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le`, in
  the namespace `SmoothTwoForm`: the energy bound, uniform over a compact family of core
  perturbations.
* `IsNondegenerate.exists_neg_sum_add_le_integral_add_sum_of_pairOfPantsPerturbation_add`, in the
  namespace `SmoothTwoForm`: the uniform lower bound on the topological energy of solutions.
* `SymplecticForm.exists_integrable_and_integral_floerEnergyDensity_pairOfPantsPerturbation_add_le`:
  for a symplectic vector space target, solutions of the Floer equation have integrable energy
  bounded by their limiting end actions plus `B₀ + B₁ + B_∞ + C`, uniformly over the family.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations, their curvature and the energy identity.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimate for the pair-of-pants product.
-/

public section

open Set Filter
open scoped Topology Manifold

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory Function Real
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ} {B : Puncture → ℝ}

/-- The core-perturbed datum `K + δ`, as a one-form on `ℂ` with components `K_s + δ_s` and
`K_t + δ_t`, satisfies the hypotheses of the energy identity for data cylindrical on the ends: it
is `C¹` on `S × M` and `H_q(t) dt` beyond the height `2` on each end `q`, its curvature along `u`
is integrable, and the end-loop integrals of the Hamiltonians along `u` converge. -/
private theorem IsNondegenerate.pairOfPantsPerturbation_add_aux
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry δs))
    (hδt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry δt)) {D U : Set (ℝ × ℝ)}
    (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ z ∉ D, δs z = 0) (ht : ∀ z ∉ D, δt z = 0) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    {K : ℂ → M → ℂ →L[ℝ] ℝ} (hKdef : K = fun w y ↦ pairOfPantsPerturbation H w y +
      (δs (Complex.equivRealProdCLM w) y • Complex.reCLM +
        δt (Complex.equivRealProdCLM w) y • Complex.imCLM)) :
    ((fun z y ↦ K (Complex.equivRealProdCLM.symm z) y 1) =
      fun z y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y 1 + δs z y) ∧
    ((fun z y ↦ K (Complex.equivRealProdCLM.symm z) y Complex.I) =
      fun z y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y Complex.I +
        δt z y) ∧
    (∀ (w : ThricePuncturedSphere) y, ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × M ↦ K p.1 p.2) ((w : ℂ), y)) ∧
    (∀ q w y, 2 ≤ q.endSign * (q.endCoord w).re →
      K w y = H q (q.endCoord w).im y • q.endAngularForm w) ∧
    Integrable (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)) ∧
    ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, H q t (x q t))) := by
  have hKs : (fun z y ↦ K (Complex.equivRealProdCLM.symm z) y 1) =
      fun z y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y 1 + δs z y := by
    funext z y
    simp [hKdef]
  have hKt : (fun z y ↦ K (Complex.equivRealProdCLM.symm z) y Complex.I) =
      fun z y ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) y Complex.I +
        δt z y := by
    funext z y
    simp [hKdef]
  refine ⟨hKs, hKt, fun w y ↦ ?_, fun q w y hw ↦ ?_, ?_, fun q ↦ ?_⟩
  · -- The datum is `C¹` on `S × M`.
    have he : ContMDiff (𝓘(ℝ, ℂ).prod I) (𝓘(ℝ, ℝ × ℝ).prod I) 1
        (fun p : ℂ × M ↦ (Complex.equivRealProdCLM p.1, p.2)) :=
      (Complex.equivRealProdCLM.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    subst hKdef
    exact (contMDiffAt_pairOfPantsPerturbation hH hHs w y).add
      (((hδs.comp he).contMDiffAt.smul contMDiffAt_const).add
        ((hδt.comp he).contMDiffAt.smul contMDiffAt_const))
  · -- Beyond the height `2` on each end the core perturbation vanishes, so `K + δ` is `H_q dt`.
    rw [hKdef]
    exact pairOfPantsPerturbation_add_eq_smul_endAngularForm (fun z hz ↦ hcore z (hDU hz)) hs ht
      hw y
  · -- The curvature of `K + δ` is integrable.
    have hR := hω.integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_add hH hHs hδs hδt hD
      hU hDU hcore hs ht hu.continuousOn
    rwa [← hKs, ← hKt, IntegrableOn,
      Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal] at hR
  · simpa only [endChart_apply, Complex.equivRealProdCLM_symm_apply] using
      tendsto_intervalIntegral_endLoop (fun q ↦ (hHs q).continuous) hB hu.continuousOn (hx q)

/-- **The energy identity on the pair of pants with a core perturbation, for a manifold target.**
Let `K` be the pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians `H_q` on a
finite-dimensional manifold with a nondegenerate two-form, and let `δ = δ_s ds + δ_t dt` be a
jointly `C¹` perturbation supported in a compact set `D` of the core: `D` lies in an open set `U`
on which the signed longitudinal coordinate of every end is at most `1`, so that `K` vanishes on
`U`. Let `u` be a map which is `C¹` on `S`, whose loops `t ↦ u(φ_q(±R + i t))` along the circles of
the end `q` converge pointwise to loops `x_q` as `R → ∞`, and whose Floer energy density for
`K + δ` and symplectic area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_{K + δ}(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_add
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry δs))
    (hδt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry δt)) {D U : Set (ℝ × ℝ)}
    (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ z ∉ D, δs z = 0) (ht : ∀ z ∉ D, δt z = 0) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs z x)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
        δt z x) u) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs z x)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
          δt z x) u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs z x)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
            δt z x) z (u z) := by
  -- The perturbed datum as a one-form on `ℂ`, with components `K_s + δ_s` and `K_t + δ_t`.
  set K : ℂ → M → ℂ →L[ℝ] ℝ := fun w y ↦ pairOfPantsPerturbation H w y +
    (δs (Complex.equivRealProdCLM w) y • Complex.reCLM +
      δt (Complex.equivRealProdCLM w) y • Complex.imCLM) with hKdef
  obtain ⟨hKs, hKt, hK, hKH, hR, hh⟩ := hω.pairOfPantsPerturbation_add_aux hH hHs hB hδs hδt hD hU
    hDU hcore hs ht hu hx hKdef
  have hS : volume.restrict thricePuncturedSphereReal = volume :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal
  rw [IntegrableOn, hS] at hE hA
  have h := hω.integral_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu
    (by rw [hKs, hKt]; exact hE) hA hR hh
  rw [hKs, hKt] at h
  simpa only [hS] using h

/-- **A nonnegative energy density is integrable, for core perturbations.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_add`, suppose
that the Floer energy density of `u` for `K + δ` is nonnegative on `S`, as it is for a solution of
the Floer equation with tamed almost complex structures. Then no integrability of the energy
density needs to be assumed: it is integrable over `S`, so the energy identity applies to it. -/
theorem IsNondegenerate.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_add
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry δs))
    (hδt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry δt)) {D U : Set (ℝ × ℝ)}
    (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ z ∉ D, δs z = 0) (ht : ∀ z ∉ D, δt z = 0) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs z x)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
        δt z x) u z)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs z x)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
        δt z x) u) thricePuncturedSphereReal := by
  set K : ℂ → M → ℂ →L[ℝ] ℝ := fun w y ↦ pairOfPantsPerturbation H w y +
    (δs (Complex.equivRealProdCLM w) y • Complex.reCLM +
      δt (Complex.equivRealProdCLM w) y • Complex.imCLM) with hKdef
  obtain ⟨hKs, hKt, hK, hKH, hR, hh⟩ := hω.pairOfPantsPerturbation_add_aux hH hHs hB hδs hδt hD hU
    hDU hcore hs ht hu hx hKdef
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal] at hA ⊢
  rw [← hKs, ← hKt] at he ⊢
  exact hω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH hu he hA hR hh

variable {E' G' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace G']
  {J : ModelWithCorners ℝ E' G'} [TopologicalSpace N] [ChartedSpace G' N] [IsManifold J 1 N]

/-- **The uniform energy bound for core perturbations, for a manifold target.** Let `K` be the
pair-of-pants perturbation of bounded period-one `C¹` Hamiltonians `H_q`, `|H_q| ≤ B_q`, on a
finite-dimensional manifold with a nondegenerate two-form, and let `δ_p` be a jointly `C¹` family of
perturbations supported in a common compact set `D` of the core, for parameters `p` in a compact
set `A`. Then there is a constant `C ≥ 0` such that, for every `p ∈ A` and every map `u` as in
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_add` which
sends `D` into a fixed compact set `Q`, the Floer energy of `u` for `K + δ_p` differs from its
topological part, the symplectic area plus the Hamiltonian terms at the asymptotic orbits, by at
most `B₀ + B₁ + B_∞ + C`. -/
theorem IsNondegenerate.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : N → ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ δt q.1.1 q.1.2 q.2))
    {A : Set N} {D U : Set (ℝ × ℝ)} {Q : Set M}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal → (∀ z ∈ D, u z ∈ Q) →
      ∀ x : Puncture → ℝ → M, (∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t))) →
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs p z x)
        (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
          δt p z x) u) thricePuncturedSphereReal →
      IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal →
      |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 + δs p z x)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
            δt p z x) u z) -
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ (∑ q, B q) + C := by
  obtain ⟨C, hC, hbound⟩ :=
    hω.exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le hH hHs hB hδs hδt
      hA hD hQ hU hDU hcore hs ht
  refine ⟨C, hC, fun p hp u hu huQ x hx hE harea ↦ ?_⟩
  have hι : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 1
      (fun r : (ℝ × ℝ) × M ↦ ((p, r.1), r.2)) :=
    (contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsPerturbation_add (δs := δs p) (δt := δt p) hH hHs hB
    (hδs.comp hι)
    (hδt.comp hι) hD hU hDU hcore (hs p hp) (ht p hp) hu hx hE harea, hsub, abs_neg,
    ← ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun q _ ↦
      (abs_nonneg _).trans (hB q 0 (u 0))) hC), ← Real.eNorm_eq_ofReal_abs]
  exact (eNorm_integral_le_lintegral_eNorm _).trans
    ((setLIntegral_le_lintegral _ _).trans (hbound p hp u huQ))

/-- **The topological energy of solutions with core perturbations is bounded below, for a manifold
target.** Under the hypotheses of
`IsNondegenerate.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le` there
is a constant `C ≥ 0` such that, for every `p ∈ A`, every solution `u` of the Floer equation
`(du - X_{K + δ_p})^{0,1} = 0` on `S` for almost complex structures tamed by the two-form, as in
that theorem but with no integrability assumed of its energy density, has symplectic area plus
Hamiltonian terms at its asymptotic orbits at least `-(B₀ + B₁ + B_∞ + C)`. Once the area is
expressed through the actions of capped orbits and the class of `u`, this becomes a lower bound on
the valuations of the output monomials, uniform over the family. -/
theorem IsNondegenerate.exists_neg_sum_add_le_integral_add_sum_of_pairOfPantsPerturbation_add
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hB : ∀ q t x, |H q t x| ≤ B q) {δs δt : N → ℝ × ℝ → M → ℝ}
    (hδs : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContMDiff ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 𝓘(ℝ) 1
      (fun q : (N × (ℝ × ℝ)) × M ↦ δt q.1.1 q.1.2 q.2))
    {A : Set N} {D U : Set (ℝ × ℝ)} {Q : Set M}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture,
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal → (∀ z ∈ D, u z ∈ Q) →
      ∀ x : Puncture → ℝ → M, (∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t))) →
      IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal →
      ∀ Jz : ∀ z, AlmostComplexStructure (TangentSpace I (u z)),
      (∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (Jz z)) →
      (∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jz z)
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1 +
              δs p z x)
            (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I +
              δt p z x) u z).toLinearMap) →
      -((∑ q, B q) + C) ≤
        (∫ z in thricePuncturedSphereReal,
            (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
              (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  obtain ⟨C, hC, hbound⟩ :=
    hω.exists_abs_integral_floerEnergyDensity_pairOfPantsPerturbation_add_sub_le hH hHs hB hδs
      hδt hA hD hQ hU hDU hcore hs ht
  refine ⟨C, hC, fun p hp u hu huQ x hx harea Jz hJ hfloer ↦ ?_⟩
  have hι : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) ((J.prod 𝓘(ℝ, ℝ × ℝ)).prod I) 1
      (fun r : (ℝ × ℝ) × M ↦ ((p, r.1), r.2)) :=
    (contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd
  -- The energy density of a solution is nonnegative, hence integrable.
  have he (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) :=
    floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have hE := hω.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_add (δs := δs p)
    (δt := δt p) hH hHs hB (hδs.comp hι) (hδt.comp hι) hD hU hDU hcore (hs p hp) (ht p hp) hu hx he
    harea
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet he
  have h := abs_le.1 (hbound p hp u hu huQ x hx hE harea)
  linarith [h.2]

end TauCeti.SmoothTwoForm

open Complex Function MeasureTheory TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Puncture → ℝ → V → ℝ}
  {B : Puncture → ℝ}

/-- The core-perturbed datum `K + δ`, as a one-form on `ℂ` with components `K_s + δ_s` and
`K_t + δ_t`, satisfies the hypotheses of the energy identity for data cylindrical on the ends: it
is `C¹` on `S × V` and `H_q(t) dt` beyond the height `2` on each end `q`. -/
private theorem pairOfPantsPerturbation_add_aux (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {δs δt : ℝ × ℝ → V → ℝ}
    (hδs : ContDiff ℝ 1 (uncurry δs)) (hδt : ContDiff ℝ 1 (uncurry δt)) {D U : Set (ℝ × ℝ)}
    (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture, q.endSign * (q.endCoord (equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ z ∉ D, δs z = 0) (ht : ∀ z ∉ D, δt z = 0) {K : ℂ → V → ℂ →L[ℝ] ℝ}
    (hKdef : K = fun w y ↦ pairOfPantsPerturbation H w y +
      (δs (equivRealProdCLM w) y • reCLM + δt (equivRealProdCLM w) y • imCLM)) :
    ((fun z y ↦ K (equivRealProdCLM.symm z) y 1) =
      fun z y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1 + δs z y) ∧
    ((fun z y ↦ K (equivRealProdCLM.symm z) y I) =
      fun z y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y I + δt z y) ∧
    (∀ z ∈ thricePuncturedSphereReal, ∀ x v,
      ContDiffAt ℝ 1 (uncurry fun z x ↦ K (equivRealProdCLM.symm z) x v) (z, x)) ∧
    (∀ q w x, 2 ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w) := by
  refine ⟨?_, ?_, fun z hz x v ↦ ?_, fun q w x hw ↦ ?_⟩
  · funext z y
    simp [hKdef]
  · funext z y
    simp [hKdef]
  · -- The datum is `C¹` on `S × V`: the canonical part by the smoothness of `K`, and the core
    -- part since it is a combination of `δ_s` and `δ_t` with constant coefficients.
    have h : (uncurry fun z x ↦ K (equivRealProdCLM.symm z) x v) = fun r ↦
        uncurry (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v) r +
          (uncurry δs r * v.re + uncurry δt r * v.im) := by
      funext ⟨w, y⟩
      simp [hKdef]
    rw [h]
    exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).add
      ((hδs.contDiffAt.mul contDiffAt_const).add (hδt.contDiffAt.mul contDiffAt_const))
  · -- Beyond the height `2` on each end the core perturbation vanishes, so `K + δ` is `H_q dt`.
    rw [hKdef]
    exact pairOfPantsPerturbation_add_eq_smul_endAngularForm (fun z hz ↦ hcore z (hDU hz)) hs ht
      hw x

variable [FiniteDimensional ℝ V] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **The energy bound for pairs of pants with core perturbations, uniform over a compact family.**
Let `K` be the pair-of-pants perturbation of period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`,
and let `δ_p = δ_{s,p} ds + δ_{t,p} dt` be a jointly `C¹` family of perturbations supported in a
common compact set `D` of the core, for parameters `p` in a compact set `A`: `D` lies in an open
set `U` on which the signed longitudinal coordinate of every end is at most `1`. Fix a compact
target window `Q`. Then there is a constant `C ≥ 0` with the following property. Let `p ∈ A`, and
let `u` be `C²` on `S`, with `u(D) ⊆ Q`, solving `(du - X_{K + δ_p})^{0,1} = 0` on `S` for almost
complex structures `J(z)` tamed by `ω`, whose end loops `ℓ_q(t) = u(φ_q(±R + i t))` have actions
converging to `a_q` as `R → ∞`. Then the energy density of `u` is integrable and

`E(u) ≤ a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞ + C`. -/
theorem exists_integrable_and_integral_floerEnergyDensity_pairOfPantsPerturbation_add_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hB : ∀ q t x, |H q t x| ≤ B q)
    {δs δt : P → ℝ × ℝ → V → ℝ}
    (hδs : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ δs q.1.1 q.1.2 q.2))
    (hδt : ContDiff ℝ 1 (fun q : (P × (ℝ × ℝ)) × V ↦ δt q.1.1 q.1.2 q.2))
    {A : Set P} {D U : Set (ℝ × ℝ)} {Q : Set V}
    (hA : IsCompact A) (hD : IsCompact D) (hQ : IsCompact Q) (hU : IsOpen U) (hDU : D ⊆ U)
    (hcore : ∀ z ∈ U, ∀ q : Puncture, q.endSign * (q.endCoord (equivRealProdCLM.symm z)).re ≤ 1)
    (hs : ∀ p ∈ A, ∀ z ∉ D, δs p z = 0) (ht : ∀ p ∈ A, ∀ z ∉ D, δt p z = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ A, ∀ u : ℝ × ℝ → V, ContDiffOn ℝ 2 u thricePuncturedSphereReal →
      (∀ z ∈ D, u z ∈ Q) → ∀ J : ℝ × ℝ → AlmostComplexStructure V,
      (∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z)) →
      (∀ z ∈ thricePuncturedSphereReal, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J z) (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt p z x)
          u z : ℝ × ℝ →ₗ[ℝ] V)) →
      ∀ a : Puncture → ℝ, (∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q)
        (fun t ↦ u (equivRealProdCLM (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I)))))
        atTop (𝓝 (a q))) →
      Integrable (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt p z x) u) ∧
        ∫ z, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt p z x) u z ≤
          (∑ q, q.endSign * a q) + ((∑ q, B q) + C) := by
  obtain ⟨C, hC, hbound⟩ :=
    ω.exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le hH hHs hB hδs
      hδt hA hD hQ hU hDU hcore hs ht
  refine ⟨C, hC, fun p hp u hu huQ J hJ hfl a ha ↦ ?_⟩
  -- The perturbed datum as a one-form on `ℂ`, with components `K_s + δ_s` and `K_t + δ_t`.
  set K : ℂ → V → ℂ →L[ℝ] ℝ := fun w y ↦ pairOfPantsPerturbation H w y +
    (δs p (equivRealProdCLM w) y • reCLM + δt p (equivRealProdCLM w) y • imCLM) with hKdef
  have hι : ContDiff ℝ 1 (fun r : (ℝ × ℝ) × V ↦ ((p, r.1), r.2)) :=
    (contDiff_const.prodMk contDiff_fst).prodMk contDiff_snd
  obtain ⟨hKs, hKt, hK, hKH⟩ := pairOfPantsPerturbation_add_aux hH hHs (δs := δs p) (δt := δt p)
    (hδs.comp hι) (hδt.comp hι) hDU hcore (hs p hp) (ht p hp) hKdef
  -- The curvature is continuous on `S`, whose complement is null, and has finite integral.
  have hKc (v : ℂ) : ContDiffOn ℝ 1 (uncurry fun z x ↦ K (equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) :=
    fun r hr ↦ (hK r.1 hr.1 r.2 v).contDiffWithinAt
  have hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ K (equivRealProdCLM.symm z) x 1) (fun z x ↦ K (equivRealProdCLM.symm z) x I) z
      (u z) := by
    refine ⟨?_, ?_⟩
    · rw [← Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal]
      exact (ω.continuousOn_hamiltonianCurvature_comp isOpen_thricePuncturedSphereReal
        hu.continuousOn (hKc 1) (hKc I)).aestronglyMeasurable
          isOpen_thricePuncturedSphereReal.measurableSet
    · rw [HasFiniteIntegral, hKs, hKt]
      exact (hbound p hp u huQ).trans_lt ENNReal.ofReal_lt_top
  have he : ∀ z ∈ thricePuncturedSphereReal, 0 ≤ ω.floerEnergyDensity
      (fun z x ↦ K (equivRealProdCLM.symm z) x 1) (fun z x ↦ K (equivRealProdCLM.symm z) x I)
      u z := by
    rw [hKs, hKt]
    exact fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfl z hz)
  have ha' (q : Puncture) : Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a q)) := by
    simpa only [endChart_mk] using ha q
  have hE := ω.integrable_floerEnergyDensity_of_eq_smul_endAngularForm hK hKH hH
    (fun q ↦ (hHs q).continuous) hu he hR ha'
  have hid := ω.integral_floerEnergyDensity_eq_sum_hamiltonianAction_of_eq_smul_endAngularForm hK
    hKH hH (fun q ↦ (hHs q).continuous) hu hE hR ha'
  rw [hKs, hKt] at hE hid hR
  refine ⟨hE, ?_⟩
  -- The integrated curvature is at most `B_0 + B_1 + B_∞ + C` in absolute value.
  have habs : |∫ z, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs p z x)
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt p z x) z (u z)| ≤
      (∑ q, B q) + C := by
    rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun q _ ↦
      (abs_nonneg _).trans (hB q 0 (u 0))) hC), ← Real.eNorm_eq_ofReal_abs]
    exact (eNorm_integral_le_lintegral_eNorm _).trans (hbound p hp u huQ)
  rw [hid]
  linarith [(abs_le.1 habs).1]

end TauCeti.SymplecticForm
