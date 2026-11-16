/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Continuation
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Compactness of the pair-of-pants continuation family

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. The Floer data of this gluing are
the perturbations `K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`, with
continuation necks at the positions `L_q` from the inner Hamiltonians `G_q` to the outer ones
`H_q`, together with almost complex structures `J_L`. Moving the neck positions along a path gives
the one-parameter families whose broken ends are the two compositions of continuation maps with
pair-of-pants products. This file proves the interior part of Gromov–Floer compactness for the
solutions of such families, for a symplectic vector space target `(V, ω)`.

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

Both results are named
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
  have hint : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I) u) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal (hu.of_le (by norm_num))
      (fun z hz ↦ (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz.1 z.2
        1).contDiffWithinAt)
      (fun z hz ↦ (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz.1 z.2
        I).contDiffWithinAt)).mono hΩS).aestronglyMeasurable hΩ,
      (hasFiniteIntegral_iff_ofReal hf0).2 (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hf0 hint.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hE0 hlin

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
