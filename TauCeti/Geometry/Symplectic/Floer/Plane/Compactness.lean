/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
public import TauCeti.Geometry.Symplectic.Floer.Plane.CappedAction

/-!
# Compactness of PSS planes with bounded end actions

Let `K` be the perturbation `TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a
period-one `C³` Hamiltonian `H` with `|H| ≤ B`, and let `ε = ±1` be the sign of the end of `p`:
`+1` for the positive plane, whose end is an input, and `-1` for the negative plane, whose end is
an output. For a map `u` of the plane write `ℓ_R(t) = u(φ(ε R + i t))` for its loop along the
circle `ε s = R` of the end, where `φ(z) = exp (2π ε z)` is the end lift. If the actions of the
loops `ℓ_R` converge to `a`, the energy of a Floer solution `u` on the plane is at most `ε a + B`
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_le` for a symplectic
vector space, and
`TauCeti.SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_le` for a
manifold, where the loop `ℓ_R` is capped by the disc of the plane that it bounds). So a sequence
of solutions whose signed end actions `ε a` are bounded above has uniformly bounded energy, and the
compactness theorems for Floer solutions of bounded energy apply on every compact window of the
plane. On the negative plane the bound is an upper bound on the output action; on the positive
plane it is a lower bound on the input action.

## Main results

* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation` in the
  namespace `TauCeti.SymplecticForm`: for a symplectic vector space target `(V, ω)` and a compact
  window `D` of the plane, there is a threshold `δ > 0` such that every sequence of `C³` solutions
  with signed end actions at most `A` and images of an open `Ω ⊆ D` in a compact set has a
  subsequence converging locally uniformly on `Ω` off a finite set `Z` of bubbling points, with
  `#Z * δ ≤ A + B`.
* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation` in the
  namespace `TauCeti.SmoothTwoForm.IsNondegenerate`: the same for a manifold `M` with a
  nondegenerate two-form `ω`, such as a closed symplectic manifold, for solutions mapping `Ω` into
  a compact subset of the source of a symplectic chart, with the end actions capped by the plane.
  The coordinate maps converge locally uniformly off `Z` and the solutions converge pointwise in
  `M`. Its smoothness input is that the perturbation of a `C^n` Hamiltonian, read in such a
  chart, is `C^n` (`TauCeti.Floer.PSSPlane.contDiffOn_perturbation_partialDiffeomorph_symm`).

The bound `#Z * δ ≤ A + B` is nonnegative because of the action bound `-B ≤ ε a` of a PSS plane.
This is the interior part of Gromov–Floer compactness for the PSS planes. The regularity of the
limit, the bubbles at the points of `Z`, the breaking of Floer cylinders off the end, and a
compactness statement for solutions that do not stay in a single chart are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  perturbed planes of the PSS maps.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Function Filter MeasureTheory Metric Real Set Topology
open scoped Manifold

namespace TauCeti

open Floer Floer.PSSPlane

namespace SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {p : PSSPlane} {H : ℝ → V → ℝ}

/-- **PSS planes with bounded end actions converge off finitely many bubbling points.** Let `K`
be the perturbation of a PSS plane given by a period-one `C³` Hamiltonian `H` with `|H| ≤ B`, and
let `J(z, x)` be a family of `ω`-tame structures on `(ℝ × ℝ) × V`. Fix compact sets `D ⊆ ℝ × ℝ`
and `K ⊆ V`, and let `J` be `C²` on an open set containing `D × K`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions of `(du - X_K)^{0,1} = 0` on the
plane for `J(z, u)`, whose end loops `ℓ_R(t) = uₖ(φ(ε R + i t))` have actions tending to `aₖ`
with `ε aₖ ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a subsequence `φ`, a
finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B`, and a continuous `v : Ω \ Z → K` such that along `φ`
every disc about a point of `Z` eventually carries energy at least `δ`, the differentials are
uniformly bounded on every compact subset of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation
    (ω : SymplecticForm V) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set ((ℝ × ℝ) × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ z x, ω.Tames (J z x)) {D : Set (ℝ × ℝ)} {K : Set V} (hD : IsCompact D)
    (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u k (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hK3 (v : ℂ) := contDiff_uncurry_perturbation (p := p) hH hHs v
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    hW (hK3 1).contDiffOn (hK3 Complex.I).contDiffOn hJ hD hK hDKW fun z _ x _ ↦ hJt z x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huK ↦ ?_⟩
  set Ks : ℝ × ℝ → V → ℝ := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → V → ℝ :=
    fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I
  have hHs1 : ContDiff ℝ 1 (uncurry H) := hHs.of_le (by norm_num)
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt z _) (hfl k z)
  -- The action bound `-B ≤ ε a` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + B := by
    have h := neg_le_endSign_mul_of_tendsto_hamiltonianAction_pssPlanePerturbation ω hH hHs1 hB
      ((hu 0).of_le (by norm_num)) (J := fun z ↦ J z (u 0 z)) (fun z ↦ hJt z _) (hfl 0) (ha 0)
    linarith [hA 0]
  -- The energy over `Ω` is at most the energy over the plane, hence at most `A + B`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + B) :=
    setLIntegral_le_lintegral _ _ |>.trans <|
      (lintegral_floerEnergyDensity_pssPlanePerturbation_le ω hH hHs1 hB
        ((hu k).of_le (by norm_num)) (J := fun z ↦ J z (u k z)) (fun z ↦ hJt z _) (hfl k)
        (ha k)).trans (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_univ ((hu k).of_le (by norm_num)).contDiffOn
      ((hK3 1).of_le (by norm_num)).contDiffOn
      ((hK3 Complex.I).of_le (by norm_num)).contDiffOn).mono
        (subset_univ Ω)).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z _ ↦ hf0 k z)).2
        ((hlin k).trans_lt ENNReal.ofReal_lt_top)⟩
  exact hconv hΩ hΩD (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK hint fun k ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hΩm fun z _ ↦ hf0 k z)
      (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hE0 (hlin k)

end SymplecticForm

namespace Floer.PSSPlane

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {p : PSSPlane} {H : ℝ → M → ℝ}

/-- **The perturbation read in a chart.** For a period-one `C^n` Hamiltonian `H` on `M` and a
`C^m` partial diffeomorphism `φ` from `M` onto an open subset of a normed space `V`, with `n ≤ m`,
the component along a tangent vector `v` of the perturbation of a PSS plane, read in the real
coordinates `ℝ × ℝ ≃ ℂ` of the plane and in the chart `φ`, is `C^n` on `(ℝ × ℝ) × φ.target`. -/
theorem contDiffOn_perturbation_partialDiffeomorph_symm {n : ℕ∞} {m : WithTop ℕ∞}
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hnm : (n : WithTop ℕ∞) ≤ m) (v : ℂ) :
    ContDiffOn ℝ n
      (fun q : (ℝ × ℝ) × V ↦ p.perturbation H (Complex.equivRealProdCLM.symm q.1) (φ.symm q.2) v)
      (univ ×ˢ φ.target) := by
  have h := (contMDiff_uncurry_perturbation (p := p) hH hHs v).comp_contMDiffOn
    (contMDiffOn_fst.prodMk ((φ.symm.contMDiffOn.of_le hnm).comp contMDiffOn_snd
      fun (q : (ℝ × ℝ) × V) (hq : q ∈ univ ×ˢ φ.target) ↦ hq.2))
  exact contMDiffOn_iff_contDiffOn.1 (contMDiffOn_prod_modelWithCornersSelf_iff.1 h)

end Floer.PSSPlane

namespace SmoothTwoForm.IsNondegenerate

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [FiniteDimensional ℝ E] [IsManifold I ⊤ M]
  [FiniteDimensional ℝ V] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {p : PSSPlane}
  {H : ℝ → M → ℝ}

/-- **PSS planes in a symplectic chart of a manifold, with bounded capped end actions, converge
off finitely many bubbling points.** Let `ω` be a nondegenerate two-form on `M`, and let `K` be the
perturbation of a PSS plane given by a period-one `C³` Hamiltonian `H` on `M` with `|H| ≤ B`. Let
`φ` be a smooth partial diffeomorphism from `M` onto an open subset of `V`, and let `D ⊆ ℝ × ℝ` and
`C ⊆ φ.source` be compact. Let `φ` pull the symplectic form `ω₀` back to `ω` at the points of `C`,
let the structures `J(z, x)` be tamed by `ω` everywhere, and let `J'` be the family `J` read in
the chart, `dφ_x ∘ J(z, x) = J'(z, φ x) ∘ dφ_x` for `z ∈ D` and `x ∈ C`, `C²` on an open set `W`
containing `D × φ(C)`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
solutions of `(du - X_K)^{0,1} = 0` on the plane for `J(z, u)`, whose end loops
`ℓ_R(t) = uₖ(φ(ε R + i t))`, capped by the discs `uₖ ∘ endDisc R` of the plane, have capped
actions tending to `aₖ` with `ε aₖ ≤ A`, and with `uₖ(Ω) ⊆ C` for an open `Ω ⊆ D`. Then there are
a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B`, and a map `v`, continuous on
`Ω \ Z` with values in `C`, such that along `ψ` every disc about a point of `Z` eventually carries
energy at least `δ`, the differentials of the coordinate maps `φ ∘ u_{ψ n}` are uniformly bounded
on every compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v` locally uniformly on
`Ω \ Z`, and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {J : ℝ × ℝ → (x : M) →
      AlmostComplexStructure (TangentSpace I x)} {J' : ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J' q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ z x, (hω.symplecticFormAt x).Tames (J z x))
    (hD : IsCompact D) (hC : IsCompact C) (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Tendsto (fun R ↦ cappedLoopAction ω.1 H (fun t ↦ u k (Complex.equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u k ∘ p.endDisc R))
          atTop (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) →
      (∀ k, MapsTo (u k) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u (ψ n)) y) ∧
        (∀ K, IsCompact K → K ⊆ Ω \ ↑Z →
          ∃ L, ∀ n, ∀ y ∈ K, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  -- In the chart, the components of the perturbation are `C³` over the chart target.
  have hK3 (v : ℂ) := contDiffOn_perturbation_partialDiffeomorph_symm (p := p) hH hHs φ
    (WithTop.coe_le_coe.2 le_top) v
  have hDCW' : D ×ˢ (φ '' C) ⊆ W ∩ univ ×ˢ φ.target := by
    rintro ⟨z, _⟩ ⟨hz, x, hx, rfl⟩
    exact ⟨hDCW ⟨hz, x, hx, rfl⟩, mem_univ _, φ.map_source (hCφ hx)⟩
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I) φ hφ hJJ'
    (hW.inter (isOpen_univ.prod φ.open_target)) ((hK3 1).mono inter_subset_right)
    ((hK3 Complex.I).mono inter_subset_right) (hJ'.mono inter_subset_left) hD hC hCφ hDCW'
    fun z _ x _ ↦ hJt z x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huC ↦ ?_⟩
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ :=
    fun z x ↦ p.perturbation H (Complex.equivRealProdCLM.symm z) x Complex.I
  have hHs1 : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H) := hHs.of_le (by norm_num)
  have hu1 (k : ℕ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u k) := (hu k).of_le (by norm_num)
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    floerEnergyDensity_nonneg hω (hJt z _) (hfl k z)
  -- The capped action bound `-B ≤ ε a` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + B := by
    have h := hω.neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation hH hHs1 hB
      (hu1 0) (J := fun z ↦ J z (u 0 z)) (fun z ↦ hJt z _) (hfl 0) (ha 0)
    linarith [hA 0]
  -- The energy over `Ω` is at most the energy over the plane, hence at most `A + B`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + B) :=
    setLIntegral_le_lintegral _ _ |>.trans <|
      (hω.lintegral_floerEnergyDensity_pssPlanePerturbation_le hH hHs1 hB (hu1 k)
        (J := fun z ↦ J z (u k z)) (fun z ↦ hJt z _) (hfl k) (ha k)).trans
        (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  -- The energy density is integrable over a disc `D_r` containing `D`, since the curvature is.
  obtain ⟨r, hr⟩ := (hD.image Complex.equivRealProdCLM.symm.continuous).isBounded.subset_closedBall
    (0 : ℂ)
  have hDr : D ⊆ Complex.equivRealProdCLM.symm ⁻¹' closedBall 0 (Real.exp (2 * π * r)) :=
    fun z hz ↦ closedBall_subset_closedBall (by
      have hr0 : 0 ≤ r := dist_nonneg.trans (mem_closedBall.1 (hr ⟨z, hz, rfl⟩))
      nlinarith [Real.add_one_le_exp (2 * π * r), Real.two_le_pi]) (hr ⟨z, hz, rfl⟩)
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    (hω.integrableOn_floerEnergyDensity isOpen_univ (hu1 k).contMDiffOn
      (contMDiff_uncurry_perturbation hH hHs1 1).contMDiffOn
      (contMDiff_uncurry_perturbation hH hHs1 Complex.I).contMDiffOn
      (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _))
      (subset_univ _)
      (ω.integrableOn_hamiltonianCurvature_pssPlanePerturbation_closedBall hH hHs1
        (hu1 k).continuous r)).mono_set (hΩD.trans hDr)
  exact hconv hΩ hΩD (fun k ↦ (hu k).contMDiffOn) (fun k z _ ↦ hfl k z) huC hint fun k ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_forall_mem hΩ.measurableSet fun z _ ↦ hf0 k z) (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hE0 (hlin k)

end SmoothTwoForm.IsNondegenerate

end TauCeti
