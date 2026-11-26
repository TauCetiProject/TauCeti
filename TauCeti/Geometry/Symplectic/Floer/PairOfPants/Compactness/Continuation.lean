/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Continuation
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Compactness of the pair-of-pants continuation family

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The Floer data of this gluing are
the perturbations `K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`, with
continuation necks at the positions `L_q` from the inner Hamiltonians `G_q` to the outer ones
`H_q`, together with almost complex structures `J_L`. Moving the neck positions along a path gives
the one-parameter families whose broken ends are the two compositions of continuation maps with
pair-of-pants products. This file proves the interior part of Gromov–Floer compactness for the
solutions of such families, for a symplectic vector space target `(V, ω)`, and for a manifold
target on the part of the domain mapped into a symplectic chart.

The neck positions are given by a `C³` map `L : P → (Puncture → ℝ)` on a real inner product
space `P` of parameters, such as a path `P = ℝ` or the whole space of neck positions
`P = EuclideanSpace ℝ Puncture`. The input is the energy bound of the family
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`):
if `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ Δ_q`, a Floer solution for `(K_L, J_L)` on `S` whose
end loops have limiting actions `a_q` has energy at most `a_0 + a_1 - a_∞ + ∑ q, (B_q + Δ_q)`,
whatever the neck positions, although the necks become arbitrarily long. The data `K_L` are smooth
jointly in the neck positions, in the domain point of `S` and in the target point
(`TauCeti.Floer.contMDiffAt_pairOfPantsContinuationPerturbation`). Hence compactness over a
compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on every compact window `D` of `S`.

For a symplectic vector space target, two results are named
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation`:

* in the namespace `TauCeti.SymplecticForm`, it is the statement for any family `J_p(z, x)` of
  `ω`-tame structures which is `C²` jointly in `(p, z, x)` near the parameter window;
* in the namespace `TauCeti.SymplecticForm.Compatible`, it applies the former to the almost complex
  structures `TauCeti.Floer.pairOfPantsContinuationAlmostComplex` of the family, built from an
  `ω`-compatible base structure and period-one `C²` inner and outer end structures
  (`TauCeti.Floer.contMDiffAt_pairOfPantsContinuationAlmostComplex`).

Both give a threshold `δ > 0` such that every sequence of solutions for parameters `pₖ` in a
compact window `C ⊆ P`, with action differences `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` and images of an open
`Ω ⊆ D` in a compact `K ⊆ V`, has a subsequence whose parameters converge to some `p₀ ∈ C` and
which converges locally uniformly on `Ω` off a finite set `Z` of bubbling points, with
`#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`. The regularity of the limit, the bubbles at the points of `Z`,
and breaking along the three ends and along the necks are not treated here.

**Manifold targets.** For a target manifold `M` with a nondegenerate two-form `ω`, such as a
closed symplectic manifold, the energy bound of the family (in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`,
`abs_integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_sub_le`) says that, whatever
the neck positions, the Floer energy over `S` exceeds the topological energy
`∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt`, the symplectic area plus the outer Hamiltonian terms at
the asymptotic orbits `x_q`, by at most `∑ q, (B_q + Δ_q)`. The data `K_L` are smooth jointly in
the neck positions, the domain point and the target point of `M`, so the Hamiltonians read in a
symplectic chart `φ : M ⊇ U → V`, such as a Darboux chart, are `C³` in `(p, z, y)`. The
compactness theorem over a compact parameter window in a symplectic chart (in the same namespace,
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`) then applies to
solutions with topological energy at most `A` whose images of `Ω` stay in a compact subset `K` of
the chart source; the result has the same name in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`. The structures `J_p(z, x)` on the tangent spaces of `M` are
any family tamed by `ω` on `S`, read in the chart by a family `J'_p(z, y)` with
`dφ_x ∘ J_p(z, x) = J'_p(z, φ x) ∘ dφ_x` that is `C²` in `(p, z, y)`. The limit is read in `M`:
the coordinate maps converge locally uniformly off the bubbling points, and the maps themselves
converge pointwise. Covering `M` by several charts is not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {G H : Puncture → ℝ → V → ℝ} {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

omit [FiniteDimensional ℝ V] in
/-- Reading the neck positions through `L : P → (Puncture → ℝ)` and the domain point of `S` in
real coordinates is as smooth as `L`. -/
private theorem contMDiff_neckPositions_realCoordinates {n : WithTop ℕ∞} {L : P → Puncture → ℝ}
    (hL : ContDiff ℝ n L) :
    ContMDiff 𝓘(ℝ, P × ((ℝ × ℝ) × V)) (𝓘(ℝ, Puncture → ℝ).prod (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V))) n
      fun p : P × ((ℝ × ℝ) × V) ↦ (L p.1, equivRealProdCLM.symm p.2.1, p.2.2) :=
  (hL.comp contDiff_fst).contMDiff.prodMk
    ((equivRealProdCLM.symm.contDiff.comp (contDiff_fst.comp contDiff_snd)).contMDiff.prodMk
      (contDiff_snd.comp contDiff_snd).contMDiff)

/-- The energy of a Floer solution of the continuation family over a measurable window `Ω ⊆ S`
is a Bochner integral bounded by `a_0 + a_1 - a_∞ + ∑ q, (B_q + Δ_q)`, whatever the neck
positions. -/
private theorem integrableOn_and_setIntegral_floerEnergyDensity_continuation_le
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q) (L : Puncture → ℝ) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfl : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a q)))
    {Ω : Set (ℝ × ℝ)} (hΩ : MeasurableSet Ω) (hΩS : Ω ⊆ thricePuncturedSphereReal) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I) u) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I) u z ≤
        a .zero + a .one - a .inf + ∑ q, (B q + Δ q) := by
  have hf0 := ae_restrict_of_forall_mem (μ := volume) hΩ fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z (hΩS hz)) (hfl z (hΩS hz))
  -- The action bound `a_∞ ≤ a_0 + a_1 + ∑ q, (B_q + Δ_q)` makes the energy bound nonnegative.
  have hE0 : 0 ≤ a .zero + a .one - a .inf + ∑ q, (B q + Δ q) := by
    linarith [le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation
      ω hG hH hGs hHs hGB hHB hΔ hu hJ hfl ha]
  -- The energy over `Ω` is at most the energy over `S`.
  have hlin : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I) u z) ≤
      ENNReal.ofReal (a .zero + a .one - a .inf + ∑ q, (B q + Δ q)) := by
    refine (setLIntegral_le_lintegral _ _).trans <|
      (lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le ω hG hH hGs hHs hGB hHB
        hΔ L hu hJ hfl (fun q ↦ by simpa only [endChart_mk] using ha q)).trans
        (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
      Puncture.endSign_inf]
    ring
  exact integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le
    (((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal (hu.of_le (by norm_num))
      (fun z hz ↦ (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz.1 z.2
        1).contDiffWithinAt)
      (fun z hz ↦ (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz.1 z.2
        I).contDiffWithinAt)).mono hΩS).aestronglyMeasurable hΩ) hf0 subset_rfl hE0 hlin

/-- **Solutions of the pair-of-pants continuation family converge off finitely many bubbling
points.** Let `K_L` be the pair-of-pants perturbation with continuation necks at the positions
`L` from period-one `C³` inner Hamiltonians `G_q` to outer Hamiltonians `H_q`, with
`|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ Δ_q`, and let the neck positions `L(p)` depend `C³` on a
parameter `p` in a real inner product space `P`. Let `J_p(z, x)` be almost complex structures
which are `C²` jointly in `(p, z, x)` on `U × S × V`, for an open set `U ⊆ P` and
`S = ℂ ∖ {0, 1}` read in real coordinates. Fix compact sets `C ⊆ U`, `D ⊆ S` and `K ⊆ V`, with
`J_p(z, x)` tamed by `ω` for `p ∈ C` and `z ∈ S`. There is a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` solutions of `(du - X_{K_{L(pₖ)}})^{0,1} = 0` on `S` for
`J_{pₖ}(z, u)`, with `pₖ ∈ C`, limiting actions `aₖ(q)` of the end loops `uₖ(φ_q(±R + i t))`
satisfying `aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a
subsequence `φ`, a limit `p₀ ∈ C` of `p_{φ n}`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc
about a point of `Z` eventually carries energy at least `δ`, the differentials are uniformly
bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem
    exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 3 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q) {L : P → Puncture → ℝ} (hL : ContDiff ℝ 3 L)
    {J : P → ℝ × ℝ → V → AlmostComplexStructure V} {U : Set P} (hU : IsOpen U)
    (hJ : ContDiffOn ℝ 2
      (fun p : P × ((ℝ × ℝ) × V) ↦ (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap)
      (U ×ˢ (thricePuncturedSphereReal ×ˢ univ)))
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hCU : C ⊆ U)
    (hJt : ∀ p ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J p z x))
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z)
              x 1)
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z)
              x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + ∑ q, (B q + Δ q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hW : IsOpen (U ×ˢ (thricePuncturedSphereReal ×ˢ (univ : Set V))) :=
    hU.prod (isOpen_thricePuncturedSphereReal.prod isOpen_univ)
  -- The perturbations are `C³` jointly in the parameter, the domain point and the target point.
  have hK' (v : ℂ) : ContDiffOn ℝ 3 (fun p : P × ((ℝ × ℝ) × V) ↦
      pairOfPantsContinuationPerturbation G H (L p.1) (equivRealProdCLM.symm p.2.1) p.2.2 v)
      (U ×ˢ (thricePuncturedSphereReal ×ˢ univ)) := by
    rintro ⟨p, z, x⟩ ⟨-, hz, -⟩
    have h := contMDiffAt_pairOfPantsContinuationPerturbation (I := 𝓘(ℝ, V)) hG hH
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hGs q).contMDiff)
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) (L p) ⟨_, hz⟩ x
    exact ((contMDiffAt_iff_contDiffAt.1 (h.comp (p, (z, x))
      (contMDiff_neckPositions_realCoordinates hL).contMDiffAt)).clm_apply
        contDiffAt_const).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun p z x ↦ pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) x 1)
    (Kt := fun p z x ↦ pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) x I)
    hW (hK' 1) (hK' I) hJ hC hD hK (prod_mono hCU (prod_mono hDS (subset_univ K)))
    fun p hp z hz x _ ↦ hJt p hp z (hDS hz) x
  refine ⟨δ, hδ, fun Ω p u a A hΩ hΩD hpC hu hfl ha hA huK ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  -- The energy over `Ω` is at most `A + ∑ q, (B_q + Δ_q)`, whatever the neck positions.
  have hE (k : ℕ) := integrableOn_and_setIntegral_floerEnergyDensity_continuation_le ω hG hH
    (fun q ↦ (hGs q).of_le (by norm_num)) (fun q ↦ (hHs q).of_le (by norm_num)) hGB hHB hΔ
    (L (p k)) ((hu k).of_le (by norm_num)) (fun z hz ↦ hJt _ (hpC k) z hz _) (hfl k) (ha k)
    hΩ.measurableSet hΩS
  exact hconv hΩ hΩD hpC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hE k).1) fun k ↦ (hE k).2.trans (by linarith [hA k])

namespace Compatible

/-- **Solutions of the pair-of-pants continuation family converge off finitely many bubbling
points**, for the almost complex structures `TauCeti.Floer.pairOfPantsContinuationAlmostComplex`
of the family. Let `G_q`, `H_q` be period-one `C³` Hamiltonians with `|G_q|, |H_q| ≤ B_q` and
`|H_q - G_q| ≤ Δ_q`, let `J₀` be `ω`-compatible, let `J₁ q t x` and `J₂ q t x` be period-one `C²`
families of `ω`-tame inner and outer structures on the three ends, and let the neck positions
`L(p)` depend `C³` on a parameter `p` in a real inner product space `P`. Fix compact sets
`C ⊆ P`, `D ⊆ S = ℂ ∖ {0, 1}` (in real coordinates) and `K ⊆ V`. There is a threshold `δ > 0`
such that every sequence of `C³` solutions `uₖ` on `S` of the Floer equation for the data
`(K_{L(pₖ)}, J_{L(pₖ)})` of the family, with `pₖ ∈ C`, limiting end actions satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ A` and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`, has a subsequence with
parameters converging in `C`, converging locally uniformly on `Ω` off a finite set `Z` of
bubbling points with `#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`, as in the statement
`exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation`
for any family of tame structures in the namespace `TauCeti.SymplecticForm`.
-/
theorem
    exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation
    {ω : SymplecticForm V} {J₀ : AlmostComplexStructure V}
    {J₁ J₂ : Puncture → ℝ → V → AlmostComplexStructure V} (h₀ : ω.Compatible J₀)
    (hJ₁ : ∀ q t x, ω.Tames (J₁ q t x)) (hJ₂ : ∀ q t x, ω.Tames (J₂ q t x))
    (hJ₁p : ∀ q, Periodic (J₁ q) 1) (hJ₂p : ∀ q, Periodic (J₂ q) 1)
    (hJ₁s : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J₁ q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hJ₂s : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J₂ q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 3 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q) {L : P → Puncture → ℝ} (hL : ContDiff ℝ 3 L)
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C) (hD : IsCompact D)
    (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ (L (p k))
            (equivRealProdCLM.symm z) (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z)
              x 1)
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z)
              x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + ∑ q, (B q + Δ q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (φ n)))
            (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- The structures of the family, read in real coordinates, are `C²` jointly in the neck
  -- positions, the domain point of `S` and the target point, hence in the parameter.
  have hJ' : ContDiffOn ℝ 2 (fun p : P × ((ℝ × ℝ) × V) ↦ (pairOfPantsContinuationAlmostComplex h₀
      J₁ J₂ hJ₁ hJ₂ (L p.1) (equivRealProdCLM.symm p.2.1) p.2.2).toLinearMap.toContinuousLinearMap)
      (univ ×ˢ (thricePuncturedSphereReal ×ˢ univ)) := by
    rintro ⟨p, z, x⟩ ⟨-, hz, -⟩
    have h := contMDiffAt_pairOfPantsContinuationAlmostComplex (I := 𝓘(ℝ, V)) (hJ₁ := hJ₁)
      (hJ₂ := hJ₂) h₀ hJ₁p hJ₂p
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hJ₁s q).contMDiff)
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hJ₂s q).contMDiff) (L p) ⟨_, hz⟩ x
    exact (contMDiffAt_iff_contDiffAt.1 (h.comp (p, (z, x))
      (contMDiff_neckPositions_realCoordinates (hL.of_le (by norm_num))).contMDiffAt))
      |>.contDiffWithinAt
  exact
    ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation
      hG hH hGs hHs hGB hHB hΔ hL
      (J := fun p z x ↦ pairOfPantsContinuationAlmostComplex h₀ J₁ J₂ hJ₁ hJ₂ (L p)
        (equivRealProdCLM.symm z) x)
      isOpen_univ hJ' hC (subset_univ C)
      (fun _ _ _ _ x ↦ tames_pairOfPantsContinuationAlmostComplex h₀ _ x) hD hDS hK

end Compatible

end TauCeti.SymplecticForm

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E F M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [TopologicalSpace M] [ChartedSpace F M]
  [IsManifold I ⊤ M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {G H : Puncture → ℝ → M → ℝ}
  {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- **Solutions of the pair-of-pants continuation family in a symplectic chart of a manifold
converge off finitely many bubbling points.** Let `ω` be a nondegenerate two-form on `M`, let
`G_q`, `H_q` be period-one `C³` Hamiltonians on `M` with `|G_q|, |H_q| ≤ B_q` and
`|H_q - G_q| ≤ Δ_q`, and let the neck positions `L(p)` depend `C³` on a parameter `p` in a real
inner product space `P`. Let `φ` be a smooth partial diffeomorphism from `M` onto an open subset of
`V` pulling the symplectic form `ω₀` back to `ω` on a compact set `K ⊆ φ.source`, such as a
Darboux chart. Let `J_p(z, x)` be structures on the tangent spaces of `M`, tamed by `ω` for `p` in
a compact window `C ⊆ P` and `z ∈ S = ℂ ∖ {0, 1}` (in real coordinates), and let `J'_p(z, y)` be
these structures read in the chart, `dφ_x ∘ J_p(z, x) = J'_p(z, φ x) ∘ dφ_x` for `p ∈ C`, `z ∈ D`
and `x ∈ K`, which are `C²` jointly in `(p, z, y)` on an open set `W` containing `C × D × φ(K)`,
for a compact `D ⊆ S`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
maps from `S` to `M` solving the Floer equation `(du - X_{K_{L(pₖ)}})^{0,1} = 0` for the structures
`J_{pₖ}(z, u)`, with `pₖ ∈ C`, whose end loops `uₖ(φ_q(±R + i t))` converge pointwise to loops
`xₖ q` as `R → ∞`, whose Floer energy and symplectic area densities are integrable over `S`, whose
topological energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ q t) dt` is at most `A`, and with
`uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `ψ`, a limit `p₀ ∈ C` of `p_{ψ n}`,
a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + ∑ q, (B_q + Δ_q)`, and a map `v`, continuous on `Ω \ Z`
with values in `K`, such that along `ψ` every disc about a point of `Z` eventually carries Floer
energy at least `δ`, the differentials of the coordinate maps `φ ∘ u_{ψ n}` are uniformly bounded
on every compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v` locally uniformly on
`Ω \ Z`, and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem
    exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B Δ : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hΔ : ∀ q t x, |H q t x - G q t x| ≤ Δ q) {L : P → Puncture → ℝ} (hL : ContDiff ℝ 3 L)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {J' : P → ℝ × ℝ → V → AlmostComplexStructure V} {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K,
      IsComplexLinearMap (J p z x) (J' p z (φ x)) (mvfderiv I φ x).toLinearMap)
    {W : Set (P × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ (J' q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hK : IsCompact K)
    (hKφ : K ⊆ φ.source) (hCDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ thricePuncturedSphereReal, ∀ x,
      (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄
      ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z)
              x 1)
            (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z)
              x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p k)) (equivRealProdCLM.symm z) x
          Complex.I) (u k)) thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
          ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (ψ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + ∑ q, (B q + Δ q) ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (ψ n)))
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L (p (ψ n)))
            (equivRealProdCLM.symm z) x Complex.I)
          (u (ψ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z →
          ∃ M', ∀ n, ∀ y ∈ L', ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ M') ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  set S := thricePuncturedSphereReal
  -- Read in the chart, the Hamiltonians are `C³` in `(p, z, y)`.
  have hK' (w : ℂ) : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦
      pairOfPantsContinuationPerturbation G H (L q.1) (equivRealProdCLM.symm q.2.1) (φ.symm q.2.2)
        w) (univ ×ˢ (S ×ˢ φ.target)) :=
    (contDiffOn_comp_prodMap_equivRealProdCLM_symm_symm
      (F := fun p : (Puncture → ℝ) × (ℂ × M) ↦
        pairOfPantsContinuationPerturbation G H p.1 p.2.1 p.2.2)
      (fun L' z hz x ↦ contMDiffAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L'
        ⟨_, mem_thricePuncturedSphereReal_iff.1 hz⟩ x) hL φ).clm_apply contDiffOn_const
  have hWt : IsOpen (W ∩ univ ×ˢ (S ×ˢ φ.target)) :=
    hW.inter (isOpen_univ.prod (isOpen_thricePuncturedSphereReal.prod φ.open_target))
  have hDKW : C ×ˢ (D ×ˢ (φ '' K)) ⊆ W ∩ univ ×ˢ (S ×ˢ φ.target) :=
    subset_inter hCDKW (prod_mono (subset_univ _)
      (prod_mono hDS (φ.toPartialEquiv.mapsTo.mono_left hKφ).image_subset))
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    φ (Ks := fun p z x ↦
      pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) x 1)
    (Kt := fun p z x ↦
      pairOfPantsContinuationPerturbation G H (L p) (equivRealProdCLM.symm z) x Complex.I) (J := J)
    hφ hJJ' hWt ((hK' 1).mono inter_subset_right) ((hK' Complex.I).mono inter_subset_right)
    (hJ'.mono inter_subset_left) hC hD hK hKφ hDKW fun p hp z hz x _ ↦ hJt p hp z (hDS hz) x
  refine ⟨δ, hδ, fun Ω p u x A hΩ hΩD hpC hu hfl hx hint harea htop huK ↦ ?_⟩
  have hΩS : Ω ⊆ S := hΩD.trans hDS
  -- The Floer energy over `Ω` is at most the energy over `S`, which exceeds the topological energy
  -- by at most `∑ q, (B_q + Δ_q)`, whatever the neck positions.
  exact hconv hΩ hΩD hpC (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK
    (fun k ↦ (hint k).mono_set hΩS) fun k ↦
      hω.setIntegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le hG hH
        (fun q ↦ (hGs q).of_le (by norm_num)) (fun q ↦ (hHs q).of_le (by norm_num)) hGB hHB hΔ
        ((hu k).of_le (by norm_num)) (hx k) (hint k) (harea k) (fun z hz ↦ hJt _ (hpC k) z hz _)
        (hfl k) (htop k) hΩS

end TauCeti.SmoothTwoForm.IsNondegenerate
