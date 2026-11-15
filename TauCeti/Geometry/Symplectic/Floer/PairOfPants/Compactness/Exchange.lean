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

Graded commutativity of the pair-of-pants product is proved with the one-parameter family of
Floer data joining the pair of pants `S = ℂ ∖ {0, 1}` to the pair of pants with exchanged
inputs, pulled back along `w ↦ 1 - w`. Its Hamiltonian perturbations are the input-exchange
family `K_c = TauCeti.Floer.exchangePerturbation H c`, `0 ≤ c ≤ 1`, whose output end is the end at
`∞` recentred at `c`. This file proves the interior part of Gromov–Floer compactness for this
family over a compact window of parameters `C ⊆ [0, 1]`, for a symplectic vector space target
`(V, ω)`.

The input is the energy bound of the family
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_exchangePerturbation_le`): for `|H_q| ≤ B_q`
and every `0 ≤ c ≤ 1`, a Floer solution on `S` whose input loops and recentred output loop have
limiting actions `a_q` has energy at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`, a bound that does
not depend on `c`. The perturbations are smooth jointly in the parameter and in the domain and
target points (`TauCeti.Floer.contDiffAt_exchangePerturbation_apply`), so compactness over a
compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D ⊆ S`.

## Main results

Both results are in the namespace `TauCeti.SymplecticForm`.

* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchangePerturbation`:
  for any family of almost complex structures `J_c(z, x)` that is jointly `C²` near the window
  and tamed by `ω`, a sequence of solutions for parameters `cₖ ∈ C` with action differences
  `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` and images of an open `Ω ⊆ D` in a compact `K ⊆ V` has a
  subsequence whose parameters converge to some `c₀ ∈ C` and which converges locally uniformly
  on `Ω` off a finite set `Z` of bubbling points, with `#Z * δ ≤ A + B_0 + B_1 + B_∞`.
* `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchange`: the same
  for the almost complex structures of the family itself, `TauCeti.Floer.exchangeAlmostComplex`,
  which are smooth jointly in the parameter
  (`TauCeti.Floer.contDiffAt_exchangeAlmostComplex`).

The regularity of the limit, the bubbles at the points of `Z`, and breaking along the three ends
are not treated here.

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

section Energy

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- The Floer energy of a solution for the member `0 ≤ c ≤ 1` of the input-exchange family,
over an open `Ω ⊆ S`, is integrable and at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`. -/
private theorem integrableOn_and_setIntegral_floerEnergyDensity_exchangePerturbation_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha₀ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .zero) (fun t ↦ u (equivRealProdCLM
      (Puncture.zero.cylindricalEndLift (↑R + ↑t * I))))) atTop (𝓝 (a .zero)))
    (ha₁ : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .one) (fun t ↦ u (equivRealProdCLM
      (Puncture.one.cylindricalEndLift (↑R + ↑t * I))))) atTop (𝓝 (a .one)))
    (ha : Tendsto (fun R : ℝ ↦ ω.hamiltonianAction (H .inf) (fun t ↦ u (equivRealProdCLM
      (↑c + Puncture.inf.cylindricalEndLift (↑(-R) + ↑t * I))))) atTop (𝓝 (a .inf)))
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩS : Ω ⊆ thricePuncturedSphereReal) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x I) u) Ω ∧
    ∫ z in Ω, ω.floerEnergyDensity
      (fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x I) u z ≤
        a .zero + a .one - a .inf + ∑ q, B q := by
  have hKc (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) :=
    fun p hp ↦ (contDiffAt_uncurry_exchangePerturbation hH hHs c hp.1 p.2 v).contDiffWithinAt
  -- The action bound `a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞` makes the energy bound nonnegative.
  have hE0 : 0 ≤ a .zero + a .one - a .inf + ∑ q, B q := by
    linarith [le_add_add_sum_of_tendsto_hamiltonianAction_exchangePerturbation ω hH hHs hB hc₀
      hc₁ hu hJ hfloer ha₀ ha₁ ha]
  exact ω.integrableOn_and_setIntegral_floerEnergyDensity_le isOpen_thricePuncturedSphereReal
    (hu.of_le one_le_two) (hKc 1) (hKc I) hJ hfloer hE0
    (lintegral_floerEnergyDensity_exchangePerturbation_le ω hH hHs hB hc₀ hc₁ hu hJ hfloer ha₀
      ha₁ ha) hΩ.measurableSet hΩS

end Energy

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Solutions along the input-exchange family converge off finitely many bubbling points.** Let
`K_c` be the input-exchange family of period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q`, and
let `J_c(z, x)` be almost complex structures on `S × V`, where `S = ℂ ∖ {0, 1}` is read in real
coordinates, that are jointly `C²` in `(c, z, x)` on an open set `W` containing `C × D × K`, and
tamed by `ω` for `c ∈ C`. Here `C ⊆ [0, 1]`, `D ⊆ S` and `K ⊆ V` are compact. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions of `(du - X_{K_{cₖ}})^{0,1} = 0` on
`S` for `J_{cₖ}(z, u)`, with `cₖ ∈ C`, whose input loops and output loop, at the end at `∞`
recentred at `cₖ`, have limiting actions `aₖ(q)` satisfying `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`, and with
`uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `φ`, a limit `c₀ ∈ C` of
`c_{φ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries Floer
energy at least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`,
and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchangePerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ → ℝ × ℝ → V → AlmostComplexStructure V} {W : Set (ℝ × ((ℝ × ℝ) × V))}
    (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2
      (fun p : ℝ × ((ℝ × ℝ) × V) ↦ (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) W)
    {C : Set ℝ} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hC₀₁ : C ⊆ Icc 0 1)
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K)
    (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ c ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J c z x)) :
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
  -- The perturbations are `C³` jointly in `(c, z, x)` wherever `z ∈ S`, so the data of the family
  -- are smooth on the part of `W` over `S`.
  set W' : Set (ℝ × ((ℝ × ℝ) × V)) := W ∩ univ ×ˢ (thricePuncturedSphereReal ×ˢ univ)
  have hW' : IsOpen W' :=
    hW.inter (isOpen_univ.prod (isOpen_thricePuncturedSphereReal.prod isOpen_univ))
  have hK' (v : ℂ) : ContDiffOn ℝ 3 (fun p : ℝ × ((ℝ × ℝ) × V) ↦
      exchangePerturbation H p.1 (equivRealProdCLM.symm p.2.1) p.2.2 v) W' :=
    fun p hp ↦ (contDiffAt_exchangePerturbation_apply hH hHs p.1 hp.2.2.1 p.2.2
      v).contDiffWithinAt
  have hCDKW' : C ×ˢ (D ×ˢ K) ⊆ W' := fun p hp ↦
    ⟨hCDKW hp, mem_univ _, hDS hp.2.1, mem_univ _⟩
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x 1)
    (Kt := fun c z x ↦ exchangePerturbation H c (equivRealProdCLM.symm z) x I)
    hW' (hK' 1) (hK' I) (hJ.mono inter_subset_left) hC hD hK hCDKW'
    fun c hc z hz x _ ↦ hJt c hc z (hDS hz) x
  refine ⟨δ, hδ, fun Ω c u a A hΩ hΩD hcC hu hfl ha₀ ha₁ ha hA huK ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  -- Every solution has energy over `Ω` at most `A + B_0 + B_1 + B_∞`, uniformly in `c ∈ C`.
  have hE (k : ℕ) := integrableOn_and_setIntegral_floerEnergyDensity_exchangePerturbation_le ω hH
    (fun q ↦ (hHs q).of_le (by norm_num)) hB (hC₀₁ (hcC k)).1 (hC₀₁ (hcC k)).2
    ((hu k).of_le (by norm_num)) (fun z hz ↦ hJt _ (hcC k) z hz _) (hfl k) (ha₀ k) (ha₁ k) (ha k)
    hΩ hΩS
  exact hconv hΩ hΩD hcC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hE k).1) fun k ↦ (hE k).2.trans (by linarith [hA k])

variable {J₀ : AlmostComplexStructure V} {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- **The input-exchange family of Floer data is compact off finitely many bubbling points.** This
is `exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchangePerturbation`
for the almost complex structures `J_c = TauCeti.Floer.exchangeAlmostComplex h₀ J hJ c` of the
family, built from an `ω`-compatible `J₀` and period-one `C²` families `J_q(t, x)` of `ω`-tame
structures on the three ends. For a compact window `C ⊆ [0, 1]` of parameters and compact sets
`D ⊆ S` and `K ⊆ V`, there is a threshold `δ > 0` such that every sequence of solutions of the
Floer equations `(du - X_{K_{cₖ}})^{0,1} = 0` for `J_{cₖ}`, with `cₖ ∈ C`, action differences at
most `A` and images of an open `Ω ⊆ D` in `K`, has a subsequence whose parameters converge in `C`
and which converges locally uniformly on `Ω` off a finite set `Z` with
`#Z * δ ≤ A + B_0 + B_1 + B_∞`, every disc about a point of `Z` eventually carrying Floer energy
at least `δ`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchange
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
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
  -- The structures of the family are `C²` jointly in `(c, z, x)` for `-1 < c < 2` and `z ∈ S`.
  set W : Set (ℝ × ((ℝ × ℝ) × V)) := Ioo (-1) 2 ×ˢ (thricePuncturedSphereReal ×ˢ univ)
  have hW : IsOpen W :=
    isOpen_Ioo.prod (isOpen_thricePuncturedSphereReal.prod isOpen_univ)
  have hJW : ContDiffOn ℝ 2 (fun p : ℝ × ((ℝ × ℝ) × V) ↦ (exchangeAlmostComplex h₀ J hJ p.1
      (equivRealProdCLM.symm p.2.1) p.2.2).toLinearMap.toContinuousLinearMap) W :=
    fun p hp ↦ (contDiffAt_exchangeAlmostComplex h₀ hJp hJs hp.1 hp.2.1 p.2.2).contDiffWithinAt
  have hCDKW : C ×ˢ (D ×ˢ K) ⊆ W := fun p hp ↦
    ⟨⟨by linarith [(hC₀₁ hp.1).1], by linarith [(hC₀₁ hp.1).2]⟩, hDS hp.2.1, mem_univ _⟩
  exact ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_exchangePerturbation
    (J := fun c z x ↦ exchangeAlmostComplex h₀ J hJ c (equivRealProdCLM.symm z) x) hH hHs hB hW
    hJW hC hC₀₁ hD hDS hK hCDKW fun c _ z _ x ↦ tames_exchangeAlmostComplex h₀ c _ x

end TauCeti.SymplecticForm
