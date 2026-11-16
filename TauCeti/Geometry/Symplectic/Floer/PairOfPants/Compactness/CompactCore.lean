/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CompactCore
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity

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

**The energy bound.** A core perturbation leaves the ends untouched, so `K + δ_p` is still
`H_q(t) dt` beyond the height `2` on each end `q`, and the energy identity for data cylindrical on
the ends (`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`)
applies. For a solution `u` with tamed almost complex structures whose end loops have limiting
actions `a_q`, the energy is `E(u) = a_0 + a_1 - a_∞ - ∫_S R_{K + δ_p}(u)`. For a compact
parameter window `A` and a compact target window `Q` containing `u(D)`, the integrated curvature is
at most `B_0 + B_1 + B_∞ + C` for bounds `|H_q| ≤ B_q` and a constant `C` independent of `p ∈ A`
and of `u`
(`SymplecticForm.exists_lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_add_le`).
Hence the energy is integrable and at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞ + C`
(`SymplecticForm.exists_integrable_and_integral_floerEnergyDensity_pairOfPantsPerturbation_add_le`).

**Compactness.** The data `K + δ_p` and almost complex structures `J_p(z, x)` are jointly smooth in
`(p, z, x)`, so the compactness theorem over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D'` of `S`. The main result,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation_add`
in the namespace `TauCeti.SymplecticForm`, gives a constant `C ≥ 0` and a threshold `δ > 0` such
that every sequence of solutions for parameters `pₖ ∈ A`, with action differences
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ E`, core images in `Q` and images of an open `Ω ⊆ D'` in a compact `K`,
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

section Energy

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
    have hwD : equivRealProdCLM w ∉ D := fun hwD ↦ by
      have := hcore _ (hDU hwD) q
      rw [ContinuousLinearEquiv.symm_apply_apply] at this
      linarith
    simp only [hKdef, congrFun (hs _ hwD) x, congrFun (ht _ hwD) x, Pi.zero_apply, zero_smul,
      add_zero, pairOfPantsPerturbation_eq_smul_endAngularForm hw]

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

end Energy

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
`D' ⊆ S` and `K ⊆ V`. There are a constant `C ≥ 0` and a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` solutions of `(du - X_{K + δ_{pₖ}})^{0,1} = 0` on `S` for
`J_{pₖ}(z, u)`, with parameters `pₖ ∈ A`, limiting end actions `aₖ(q)` satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ E`, `uₖ(D) ⊆ Q`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D'`. Then there are a
subsequence `φ`, a limit parameter `p₀ ∈ A` of `p_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ E + B_0 + B_1 + B_∞ + C`, and a continuous `v : Ω \ Z → K` such that along `φ` every
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
    {D' : Set (ℝ × ℝ)} {K : Set V} (hD' : IsCompact D') (hD'S : D' ⊆ thricePuncturedSphereReal)
    (hK : IsCompact K) :
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
      (∀ k, ∀ z ∈ D, u k z ∈ Q) → (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ A ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ E + ((∑ q, B q) + C) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1 + δs (p (φ n)) z x)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I + δt (p (φ n)) z x)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
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
    hW (hKc 1 hδs) (hKc I hδt) hJ hA hD' hK
    (fun r hr ↦ ⟨mem_univ _, hD'S hr.2.1, mem_univ _⟩)
    fun p hp z hz x _ ↦ hJt p hp z (hD'S hz) x
  refine ⟨C, hC, δ, hδ, fun Ω p u a E hΩ hΩD hpA hu hfl ha hE huQ huK ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hD'S
  -- Each solution has integrable energy at most `E + B_0 + B_1 + B_∞ + C`, and so does its
  -- restriction to `Ω`, since the energy density is nonnegative on `S`.
  have hen (k : ℕ) := henergy (p k) (hpA k) (u k) ((hu k).of_le (by norm_num)) (huQ k)
    (fun z ↦ J (p k) z (u k z)) (fun z hz ↦ hJt _ (hpA k) z hz _) (hfl k) (a k) (ha k)
  refine hconv hΩ hΩD hpA (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hen k).1.integrableOn) fun k ↦ ?_
  refine (setIntegral_le_integral (hen k).1 ?_).trans ((hen k).2.trans ?_)
  · filter_upwards [ae_mem_thricePuncturedSphereReal] with z hz
    exact ω.floerEnergyDensity_nonneg (hJt _ (hpA k) z hz _) (hfl k z hz)
  · simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
      Puncture.endSign_inf]
    linarith [hE k]

end Compactness

end TauCeti.SymplecticForm
