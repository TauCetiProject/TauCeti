/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Exchange

/-!
# Compactness of the input-exchange family

Graded commutativity of the pair-of-pants product compares the product with the product of the
exchanged inputs through the input-exchange family of Floer data on `S = ℂ ∖ {0, 1}`: the
perturbations `K_c = TauCeti.Floer.exchangePerturbation H c`, whose output end is the end at `∞`
recentred at `c`, together with almost complex structures `J_c`, for `c` in the parameter
interval `[0, 1]`. The member `c = 0` is the pair-of-pants problem, and the member `c = 1` is the
problem with exchanged inputs pulled back along `w ↦ 1 - w`. This file proves the interior part of
Gromov–Floer compactness for the solutions of the whole family, for a symplectic vector space
target `(V, ω)`.

The input is the energy bound of the family
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_le`): for period-one
Hamiltonians with `|H_q| ≤ B_q` and every `c ∈ [0, 1]`, a Floer solution for `(K_c, J_c)` on `S`
whose input loops and recentred output loops have limiting actions `a_q` has energy at most
`a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`. The data `K_c` are smooth jointly in `c`, in the domain point
of `S` and in the target point (`TauCeti.Floer.contDiffAt_exchangePerturbation_apply`). Hence
compactness over a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D` of `S`.

* `SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchange`
  is the statement for any family `J_c(z, x)` of `ω`-tame structures which is `C²` jointly in
  `(c, z, x)` near the parameter window.
* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchangeAlmostComplex`,
  in the same namespace, applies it to the almost complex structures
  `TauCeti.Floer.exchangeAlmostComplex` of the family, built from an `ω`-compatible base structure
  and period-one `C²` end structures (`TauCeti.Floer.contDiffAt_exchangeAlmostComplex`).

Both give a threshold `δ > 0` such that every sequence of solutions for parameters `cₖ` in a
compact window `C ⊆ [0, 1]`, with action differences `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` and images of
an open `Ω ⊆ D` in a compact `K ⊆ V`, has a subsequence whose parameters converge to some `c₀ ∈ C`
and which converges locally uniformly on `Ω` off a finite set `Z` of bubbling points, with
`#Z * δ ≤ A + B₀ + B₁ + B_∞`. The regularity of the limit, the bubbles at the points of `Z`, and
breaking along the three ends are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Solutions of the input-exchange family converge off finitely many bubbling points.** Let
`K_c` be the input-exchange family of period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and
let `J_c(z, x)` be almost complex structures which are `C²` jointly in `(c, z, x)` on `U × S × V`,
for an open set `U ⊆ ℝ` of parameters and `S = ℂ ∖ {0, 1}` read in real coordinates. Fix compact
sets `C ⊆ U ∩ [0, 1]`, `D ⊆ S` and `K ⊆ V`, with `J_c(z, x)` tamed by `ω` for `c ∈ C` and
`z ∈ S`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_{K_{cₖ}})^{0,1} = 0` on `S` for `J_{cₖ}(z, u)`, with `cₖ ∈ C`, limiting actions `aₖ(q)` of
the input loops `uₖ(φ_q(R + i t))` and of the recentred output loops `uₖ(cₖ + φ_∞(-R + i t))`
satisfying `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a
subsequence `φ`, a limit `c₀ ∈ C` of `c_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + B_0 + B_1 + B_∞`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc
about a point of `Z` eventually carries energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchange
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {U : Set ℝ} (hU : IsOpen U)
    (hJ : ContDiffOn ℝ 2
      (fun p : ℝ × ((ℝ × ℝ) × V) ↦ (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap)
      (U ×ˢ (thricePuncturedSphereReal ×ˢ univ)))
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hCU : C ⊆ U)
    (hC₀₁ : C ⊆ Icc 0 1) (hJt : ∀ c ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J c z x))
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, c k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (c k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .zero) (fun t ↦ u k (equivRealProdCLM
        (Puncture.zero.cylindricalEndLift (↑R + ↑t * I))))) atTop (𝓝 (a k .zero))) →
      (∀ k, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .one) (fun t ↦ u k (equivRealProdCLM
        (Puncture.one.cylindricalEndLift (↑R + ↑t * I))))) atTop (𝓝 (a k .one))) →
      (∀ k, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .inf) (fun t ↦ u k (equivRealProdCLM
        (↑(c k) + Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * I))))) atTop (𝓝 (a k .inf))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (c₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ c₀ ∈ C ∧
        Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hW : IsOpen (U ×ˢ (thricePuncturedSphereReal ×ˢ (univ : Set V))) :=
    hU.prod (isOpen_thricePuncturedSphereReal.prod isOpen_univ)
  have hK' (v : ℂ) : ContDiffOn ℝ 3 (fun p : ℝ × ((ℝ × ℝ) × V) ↦
      exchangePerturbation H p.1 (equivRealProdCLM.symm p.2.1) p.2.2 v)
      (U ×ˢ (thricePuncturedSphereReal ×ˢ univ)) := by
    rintro ⟨c, z, x⟩ ⟨-, hz, -⟩
    exact (contDiffAt_exchangePerturbation_apply (n := 3) hH hHs c hz x v).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
    (Kt := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x I)
    hW (hK' 1) (hK' I) hJ hC hD hK (prod_mono hCU (prod_mono hDS (subset_univ K)))
    fun c hc z hz x _ ↦ hJt c hc z (hDS hz) x
  refine ⟨δ, hδ, fun Ω c u a A hΩ hΩD hcC hu hfl ha₀ ha₁ ha hA huK ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  have hHs₁ (q : Puncture) : ContDiff ℝ 1 (uncurry (H q)) := (hHs q).of_le (by norm_num)
  have hJk (k : ℕ) : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J (c k) z (u k z)) :=
    fun z hz ↦ hJt _ (hcC k) z hz _
  have hKc (k : ℕ) (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := fun p hp ↦
    (contDiffAt_uncurry_exchangePerturbation hH hHs₁ (c k) hp.1 p.2 v).contDiffWithinAt
  -- The action bound `a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + ∑ q, B q := by
    linarith [hA 0, le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation ω hH hHs₁ hB
      (hC₀₁ (hcC 0)).1 (hC₀₁ (hcC 0)).2 ((hu 0).of_le (by norm_num)) (hJk 0) (hfl 0) (ha₀ 0)
      (ha₁ 0) (ha 0)]
  -- The energy over `Ω` is at most the energy over `S`, hence at most `A + B_0 + B_1 + B_∞`.
  have hE (k : ℕ) := ω.integrableOn_and_setIntegral_floerEnergyDensity_le
    isOpen_thricePuncturedSphereReal hΩ.measurableSet hΩS ((hu k).of_le (by norm_num)) (hKc k 1)
    (hKc k I) (fun z hz ↦ ω.floerEnergyDensity_nonneg (hJk k z (hΩS hz)) (hfl k z (hΩS hz)))
    hE0 <| (lintegral_floerEnergyDensity_exchangePerturbation_le ω hH hHs₁ hB (hC₀₁ (hcC k)).1
      (hC₀₁ (hcC k)).2 ((hu k).of_le (by norm_num)) (hJk k) (hfl k) (ha₀ k) (ha₁ k)
      (ha k)).trans (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  exact hconv hΩ hΩD hcC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hE k).1) fun k ↦ (hE k).2

/-- **Solutions of the input-exchange family converge off finitely many bubbling points**, for the
almost complex structures `TauCeti.Floer.exchangeAlmostComplex` of the family. Let `H_q` be
period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let `J_q(t, x)`
be period-one `C²` families of `ω`-tame structures on the three ends. Fix compact sets
`C ⊆ [0, 1]`, `D ⊆ S = ℂ ∖ {0, 1}` (in real coordinates) and `K ⊆ V`. There is a threshold
`δ > 0` such that every sequence of `C³` solutions `uₖ` on `S` of the Floer equation for the
members `cₖ ∈ C` of the family, with limiting end actions satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`, has a subsequence with
parameters converging in `C`, converging locally uniformly on `Ω` off a finite set `Z` of bubbling
points with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, as in
`SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchange`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchangeAlmostComplex
    (ω : SymplecticForm V) {J₀ : AlmostComplexStructure V}
    {J : Puncture → ℝ → V → AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t x, ω.Tames (J q t x)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hC₀₁ : C ⊆ Icc 0 1)
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃c : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, c k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (exchangeAlmostComplex h₀ J hJ (c k) (equivRealProdCLM.symm z) (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ exchangePerturbation H (c k) (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .zero) (fun t ↦ u k (equivRealProdCLM
        (Puncture.zero.cylindricalEndLift (↑R + ↑t * I))))) atTop (𝓝 (a k .zero))) →
      (∀ k, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .one) (fun t ↦ u k (equivRealProdCLM
        (Puncture.one.cylindricalEndLift (↑R + ↑t * I))))) atTop (𝓝 (a k .one))) →
      (∀ k, Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .inf) (fun t ↦ u k (equivRealProdCLM
        (↑(c k) + Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * I))))) atTop (𝓝 (a k .inf))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (c₀ : ℝ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ c₀ ∈ C ∧
        Tendsto (fun n ↦ c (φ n)) atTop (𝓝 c₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ exchangePerturbation H (c (φ n)) (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- The structures of the family, read in real coordinates, are jointly `C²` in `(c, z, x)` for
  -- `-1 < c < 2` and `z ∈ S`.
  have hJ' : ContDiffOn ℝ 2 (fun p : ℝ × ((ℝ × ℝ) × V) ↦ (exchangeAlmostComplex h₀ J hJ p.1
      (equivRealProdCLM.symm p.2.1) p.2.2).toLinearMap.toContinuousLinearMap)
      (Ioo (-1) 2 ×ˢ (thricePuncturedSphereReal ×ˢ univ)) := by
    rintro ⟨c, z, x⟩ ⟨hc, hz, -⟩
    exact (contDiffAt_exchangeAlmostComplex h₀ hJp hJs hc hz x).contDiffWithinAt
  exact ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchange hH hHs hB
    (J := fun c z x ↦ exchangeAlmostComplex h₀ J hJ c (equivRealProdCLM.symm z) x)
    (U := Ioo (-1) 2) isOpen_Ioo hJ' hC
    (fun c hc ↦ ⟨by linarith [(hC₀₁ hc).1], by linarith [(hC₀₁ hc).2]⟩) hC₀₁
    (fun c _ z _ x ↦ tames_exchangeAlmostComplex h₀ c _ x) hD hDS hK

end TauCeti.SymplecticForm
