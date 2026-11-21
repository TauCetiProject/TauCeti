/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Plane.Action
public import TauCeti.Geometry.Symplectic.Floer.Plane.CappedAction
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# Compactness of PSS planes with bounded end action

The Piunikhin–Salamon–Schwarz maps, and the unit cycle of the pair-of-pants product, count
solutions `u : ℂ → X` of the perturbed Cauchy–Riemann equation `(du - X_K)^{0,1} = 0` for the
perturbation `K = TauCeti.Floer.PSSPlane.perturbation` of a PSS plane `p`, built from a period-one
Hamiltonian `H` with `|H| ≤ B`. Let `ε = ±1` be the sign of the end of `p`. If the actions of the
end loops of `u` converge to `a`, the energy of `u` is at most `ε a + B`. So a sequence of solutions
whose signed end actions `ε aₖ` are bounded above by `A` has energy at most `A + B`, and the
compactness theorems for Floer solutions of bounded energy apply on every compact window of the
plane. This file proves the resulting interior part of Gromov–Floer compactness for PSS planes.

* **Vector-space targets.** For a symplectic vector space `(V, ω)` and almost complex structures
  `J(z, x)` tamed by `ω` and `C²` near `D × K`, for compact `D ⊆ ℝ × ℝ` and `K ⊆ V`, there is a
  threshold `δ > 0` such that every sequence of `C³` solutions with `ε aₖ ≤ A` and with image of an
  open `Ω ⊆ D` in `K` has a subsequence converging locally uniformly on `Ω` off a finite set `Z` of
  bubbling points, with `#Z * δ ≤ A + B`, derivatives bounded on compact subsets of `Ω \ Z`, and
  energy at least `δ` concentrating at each point of `Z`
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation` in the
  namespace `TauCeti.SymplecticForm`). The energy bound is
  `SymplecticForm.lintegral_floerEnergyDensity_pssPlanePerturbation_le`, and the compactness
  theorem is `SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`.
* **Symplectic charts of a manifold.** For a nondegenerate two-form `ω` on a finite-dimensional
  manifold `M`, the action of an end loop is its capped action, capped by the disc of the plane
  that it bounds (`TauCeti.Floer.PSSPlane.endDisc`), and the energy bound is
  `SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pssPlanePerturbation_le`. Read in a
  smooth partial diffeomorphism `φ` from `M` to `V`, the perturbation has the Hamiltonians
  `K(z, φ⁻¹ y)`, which are `C^n` for a `C^n` Hamiltonian
  (`TauCeti.Floer.PSSPlane.contDiffOn_perturbation_comp_symm`). For a symplectic chart, the
  compactness theorem in a chart,
  `SmoothTwoForm.IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`,
  then gives the same conclusion for solutions whose image of `Ω` stays in a compact subset `C` of
  the source of `φ`: the coordinate maps `φ ∘ u` converge locally uniformly on `Ω \ Z`, and the
  maps converge pointwise in `M`
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation` in the
  namespace `TauCeti.SmoothTwoForm.IsNondegenerate`).

Both statements hold for the positive and for the negative plane. Since `ε a ≥ -B` for every
solution, the bound `A + B` on the energy is nonnegative. Localizing the images of small discs
into charts on a closed manifold, the bubbles at the points of `Z`, and breaking along the end are
not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points), Section 8.1 (the energy of solutions of the
  inhomogeneous equation) and Chapter 12 (the PSS isomorphism).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open scoped Manifold

namespace TauCeti

namespace SymplecticForm

open Floer Floer.PSSPlane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : ℝ → V → ℝ}

/-- **PSS planes with bounded end action converge off finitely many bubbling points.** Let `p` be
a PSS plane with end sign `ε`, let `H` be a period-one `C³` Hamiltonian with `|H| ≤ B`, and let
`J(z, x)` be almost complex structures on `V`, tamed by `ω` and `C²` on an open set `W ⊇ D × K`
for compact `D ⊆ ℝ × ℝ` and `K ⊆ V`. There is a threshold `δ > 0` with the following property.
Let `uₖ` be `C³` solutions on the plane of the Floer equation for `J(z, u)` and the perturbation
of `p` given by `H`, whose end loops along the circles `‖w‖ = exp (2πR)` have actions converging
to `aₖ` as `R → ∞`, with `ε aₖ ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a
subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B`, and a continuous `v : Ω \ Z → K`
such that along `ψ` every disc about a point of `Z` eventually carries energy at least `δ`, the
differentials are uniformly bounded on every compact subset of `Ω \ Z`, and `u_{ψ n} → v` locally
uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation
    (ω : SymplecticForm V) (p : PSSPlane) (hH : Periodic H 1) (hHs : ContDiff ℝ 3 (uncurry H))
    {B : ℝ} (hB : ∀ t x, |H t x| ≤ B) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2
      (fun q : (ℝ × ℝ) × V ↦ (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ z x, ω.Tames (J z x)) (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u k) z
          : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, Tendsto (fun R ↦ ω.hamiltonianAction H (fun t ↦ u k (equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * I))))) atTop (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) → (∀ k, MapsTo (u k) Ω K) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I) (u (ψ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (ψ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (ψ n)) v atTop (Ω \ ↑Z) := by
  set Ks : ℝ × ℝ → V → ℝ := fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → V → ℝ := fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x I
  have hK₃ (v : ℂ) := contDiff_uncurry_perturbation (p := p) hH hHs v
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := Ks) (Kt := Kt) hW (hK₃ 1).contDiffOn (hK₃ I).contDiffOn hJ hD hK hDKW
    fun z _ x _ ↦ hJt z x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huK ↦ ?_⟩
  have hu₂ (k : ℕ) : ContDiff ℝ 2 (u k) := (hu k).of_le (by norm_num)
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt z _) (hfl k z)
  -- The energy over the plane is at most `ε aₖ + B ≤ A + B`, and `-B ≤ ε a₀` makes `A + B ≥ 0`.
  have hE0 : 0 ≤ A + B := by
    linarith [hA 0, neg_le_endSign_mul_of_tendsto_hamiltonianAction_pssPlanePerturbation ω hH
      (hHs.of_le (by norm_num)) hB (hu₂ 0) (fun z ↦ hJt z _) (hfl 0) (ha 0)]
  have hlin (k : ℕ) : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + B) :=
    (lintegral_floerEnergyDensity_pssPlanePerturbation_le ω hH (hHs.of_le (by norm_num)) hB
      (hu₂ k) (fun z ↦ hJt z _) (hfl k) (ha k)).trans
      (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    ((continuousOn_univ.1 (ω.continuousOn_floerEnergyDensity isOpen_univ
      ((hu₂ k).of_le one_le_two).contDiffOn ((hK₃ 1).of_le (by norm_num)).contDiffOn
      ((hK₃ I).of_le (by norm_num)).contDiffOn)).continuousOn.integrableOn_compact hD).mono_set
      hΩD
  exact hconv hΩ hΩD (fun k ↦ (hu k).contDiffOn) (fun k z _ ↦ hfl k z) huK hint fun k ↦
    (integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le (hint k).aestronglyMeasurable
      (ae_of_all _ (hf0 k)) (subset_univ Ω) hE0 ((setLIntegral_univ _).trans_le (hlin k))).2

end SymplecticForm

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  {H : ℝ → M → ℝ}

namespace Floer.PSSPlane

variable [NormedSpace ℝ V]

/-- **The perturbation of a PSS plane read in a chart is smooth.** For a period-one Hamiltonian
which is `C^n` on `ℝ × M` and a `C^m` partial diffeomorphism `φ` from `M` to a normed space `V`,
with `n ≤ m`, each component `K(z, φ⁻¹ y)(v)` of the perturbation of a PSS plane read in the chart
is `C^n` jointly in the real coordinates `z` of the plane and the chart coordinate `y` in the
target of `φ`. -/
theorem contDiffOn_perturbation_comp_symm (p : PSSPlane) {n : ℕ∞} {m : WithTop ℕ∞}
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hnm : (n : WithTop ℕ∞) ≤ m) (v : ℂ) :
    ContDiffOn ℝ n (fun q : (ℝ × ℝ) × V ↦
        p.perturbation H (equivRealProdCLM.symm q.1) (φ.symm q.2) v) (univ ×ˢ φ.target) := by
  rintro ⟨z, y⟩ ⟨-, hy⟩
  exact ((φ.contDiffAt_comp_prodMap_symm hnm equivRealProdCLM.symm.contDiff.contDiffAt hy
    (contMDiff_perturbation (p := p) hH hHs _)).clm_apply contDiffAt_const).contDiffWithinAt

end Floer.PSSPlane

namespace SmoothTwoForm.IsNondegenerate

open Floer Floer.PSSPlane

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **PSS planes in a symplectic chart of a manifold converge off finitely many bubbling
points.** Let `K` be the perturbation of a PSS plane `p` with end sign `ε`, given by a period-one
`C³` Hamiltonian `H` on `M` with `|H| ≤ B`, let `J(z, x)` be structures on the tangent spaces of
`M` tamed by `ω`, and let `φ` be a smooth partial diffeomorphism from `M` onto an open subset of
`V`. Let `D ⊆ ℝ × ℝ` and `C ⊆ φ.source` be compact, let `φ` pull the symplectic form `ω₀` back to
`ω` at the points of `C`, and let `J'` be the family `J` read in the chart,
`dφ_x ∘ J(z, x) = J'(z, φ x) ∘ dφ_x` for `z ∈ D` and `x ∈ C`, and `C²` on an open set containing
`D × φ(C)`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions
of `(du - X_K)^{0,1} = 0` on the plane for `J(z, u)`, whose end loops along the circles
`‖w‖ = exp (2πR)`, each capped by the disc `uₖ ∘ endDisc R` of the plane that it bounds, have
capped actions converging to `aₖ` as `R → ∞`, with `ε aₖ ≤ A`, and with `uₖ(Ω) ⊆ C` for an open
`Ω ⊆ D`. Then there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B`, and a map
`v`, continuous on `Ω \ Z` with values in `C`, such that along `ψ` every disc about a point of `Z`
eventually carries energy at least `δ`, the differentials of the coordinate maps `φ ∘ u_{ψ n}` are
uniformly bounded on every compact subset of `Ω \ Z`, the coordinate maps converge to `φ ∘ v`
locally uniformly on `Ω \ Z`, and `u_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pssPlanePerturbation
    (hω : ω.IsNondegenerate) (p : PSSPlane) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
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
        (ω.perturbedMFDeriv (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u k)
          z).toLinearMap) →
      (∀ k, Tendsto (fun R ↦ cappedLoopAction ω.val H (fun t ↦ u k (equivRealProdCLM
        (p.cylindricalEndLift (↑(p.endSign * R) + ↑t * Complex.I)))) (u k ∘ p.endDisc R)) atTop
          (𝓝 (a k))) →
      (∀ k, p.endSign * a k ≤ A) → (∀ k, MapsTo (u k) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + B ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I) (u (ψ n)) y) ∧
        (∀ K, IsCompact K → K ⊆ Ω \ ↑Z →
          ∃ L, ∀ n, ∀ y ∈ K, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦ p.perturbation H (equivRealProdCLM.symm z) x Complex.I
  have hHs₁ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H) := hHs.of_le (by norm_num)
  -- Read in the chart, the perturbation is `C³` on `ℝ² × φ(U)`, which contains `D × φ(C)`.
  have hW' : IsOpen (W ∩ univ ×ˢ φ.target) := hW.inter (isOpen_univ.prod φ.open_target)
  have hDCW' : D ×ˢ (φ '' C) ⊆ W ∩ univ ×ˢ φ.target := by
    refine subset_inter hDCW (prod_mono (subset_univ D) ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact φ.toPartialEquiv.map_source (hCφ hx)
  have hK (v : ℂ) := (contDiffOn_perturbation_comp_symm p hH hHs φ
    (WithTop.coe_le_coe.2 le_top) v).mono (inter_subset_right (s := W))
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset φ
    (Ks := Ks) (Kt := Kt) hφ hJJ' hW' (hK 1) (hK Complex.I) (hJ'.mono inter_subset_left) hD hC
    hCφ hDCW' fun z _ x _ ↦ hJt z x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huC ↦ ?_⟩
  have hu₁ (k : ℕ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 (u k) := (hu k).of_le (by norm_num)
  have hf0 (k : ℕ) (z : ℝ × ℝ) : 0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    floerEnergyDensity_nonneg hω (hJt z _) (hfl k z)
  -- The energy over the plane is at most `ε aₖ + B ≤ A + B`, and `-B ≤ ε a₀` makes `A + B ≥ 0`.
  have hE0 : 0 ≤ A + B := by
    linarith [hA 0, hω.neg_le_endSign_mul_of_tendsto_cappedLoopAction_pssPlanePerturbation hH
      hHs₁ hB (hu₁ 0) (fun z ↦ hJt z _) (hfl 0) (ha 0)]
  have hlin (k : ℕ) : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + B) :=
    (hω.lintegral_floerEnergyDensity_pssPlanePerturbation_le hH hHs₁ hB (hu₁ k)
      (fun z ↦ hJt z _) (hfl k) (ha k)).trans (ENNReal.ofReal_le_ofReal (by linarith [hA k]))
  -- The energy density is integrable over a disc `D_R = {‖w‖ ≤ exp (2πR)}` containing `D`.
  obtain ⟨r, hr⟩ := (hD.image equivRealProdCLM.symm.continuous).isBounded.subset_closedBall 0
  have hr' : r ≤ Real.exp (2 * Real.pi * |r|) := by
    nlinarith [abs_nonneg r, le_abs_self r, Real.two_le_pi, Real.add_one_le_exp (2 * Real.pi * |r|)]
  have hDR : D ⊆ equivRealProdCLM.symm ⁻¹' closedBall 0 (Real.exp (2 * Real.pi * |r|)) :=
    fun z hz ↦ closedBall_subset_closedBall hr' (hr (mem_image_of_mem _ hz))
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    (hω.integrableOn_floerEnergyDensity isOpen_univ (hu₁ k).contMDiffOn
      (contMDiff_uncurry_perturbation hH hHs₁ 1).contMDiffOn
      (contMDiff_uncurry_perturbation hH hHs₁ Complex.I).contMDiffOn
      (equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _))
      (subset_univ _) (ω.integrableOn_hamiltonianCurvature_pssPlanePerturbation_closedBall hH
        hHs₁ (hu₁ k).continuous |r|)).mono_set (hΩD.trans hDR)
  exact hconv hΩ hΩD (fun k ↦ (hu k).contMDiffOn) (fun k z _ ↦ hfl k z) huC hint fun k ↦
    (integrableOn_and_setIntegral_le_of_setLIntegral_ofReal_le (hint k).aestronglyMeasurable
      (ae_of_all _ (hf0 k)) (subset_univ Ω) hE0 ((setLIntegral_univ _).trans_le (hlin k))).2

end SmoothTwoForm.IsNondegenerate

end TauCeti
