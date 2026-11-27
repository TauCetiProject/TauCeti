/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Pullback
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
import TauCeti.Order.Interval.Set.Prod

/-!
# Compactness of pairs of pants in a symplectic chart of a manifold

Let `ω` be a nondegenerate two-form on a finite-dimensional manifold `M`, such as a closed
symplectic manifold, and let `K` be the pair-of-pants perturbation
`TauCeti.Floer.pairOfPantsPerturbation` of period-one `C³` Hamiltonians `H_q` with `|H_q| ≤ B_q`
on the three ends of `S = ℂ ∖ {0, 1}`. This file proves the interior part of Gromov–Floer
compactness for solutions `u : S → M` of `(du - X_K)^{0,1} = 0`, on a part of the domain whose
image stays in a compact subset of the source of a symplectic chart `φ : M ⊇ U → V`. It is the
manifold-target counterpart of the vector-space theorem
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation` in the
namespace `TauCeti.SymplecticForm`.

Two inputs combine.

* **The energy bound.** For a solution `u` with asymptotic loops `x_q` at the ends, and integrable
  energy and area densities, the energy identity on the pair of pants
  (`TauCeti.SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation`)
  bounds the energy over `S` by its topological part
  `∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` plus `B₀ + B₁ + B_∞`. Since the energy density of a
  solution is nonnegative where the structures are tamed, this bounds the energy over every part
  of `S`.
* **Compactness in a symplectic chart.** Read in the chart, the perturbation has the Hamiltonians
  `K(z, φ⁻¹ y)`, which are `C³` on `S × φ(U)`
  (`TauCeti.Floer.contDiffOn_pairOfPantsPerturbation_comp_symm`). The compactness theorem for
  Floer solutions of bounded energy in a symplectic chart,
  `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset` in the namespace
  `TauCeti.SmoothTwoForm.IsNondegenerate`, then applies.

The main result, in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, is
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation`. It fixes
compact sets `D ⊆ S` and `C ⊆ U`, and gives a threshold `δ > 0`. For every open `Ω ⊆ D` and every
sequence of solutions with topological energy at most `A` and image of `Ω` in `C`, a
subsequence converges off a finite set `Z ⊆ Ω` of bubbling points with
`#Z * δ ≤ A + B₀ + B₁ + B_∞`: the coordinate maps `φ ∘ u` converge locally uniformly on `Ω \ Z`,
with locally bounded derivatives, the maps converge pointwise in `M`, and every disc about a point
of `Z` eventually carries energy at least `δ`.

Its first step, also in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`, is
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPants_of_setIntegral_le`: the
same conclusion with `#Z * δ ≤ A` for solutions on `Ω` alone whose energy over `Ω` is at most `A`,
for structures tamed only over `D × C`. It serves pieces of other domains, such as the two pairs of
pants of a plumbed four-punctured sphere, where the energy bound comes from elsewhere.

**Along the ends.** Breaking along an end `q` concerns windows that move off to the puncture: a
sequence of solutions `uₖ` is read at heights `Rₖ` through the translated ends
`vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))` of the positive end chart `TauCeti.Floer.positiveEndChart`. For a
perturbation `K` equal to `H_q(t) dt` beyond a height `T₀` on the end `q`, and structures `J` equal
to `J_q(t, x)` on the end `q` beyond `T₀`, every translated end solves the same cylindrical Floer
equation for the datum `H'_q(t) dt` of the positive end, whatever the height
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_add`), with energy
over a window of angular width one at most the energy of `uₖ`
(`TauCeti.SmoothTwoForm.setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le`). The
compactness theorem in a symplectic chart therefore applies to the `vₖ` on a fixed window
`D ⊆ (max T₀ 0, ∞) × (t₀, t₀ + 1)`, with a threshold `δ` that does not depend on the heights
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). It is the manifold-target counterpart of
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart` in the
namespace `TauCeti.SymplecticForm`. When `Rₖ → ∞` the limits of the `vₖ` are the Floer cylinders
that break off at the end `q`. For smooth solutions the coordinate maps converge in `C¹`, and the
limit is a `C¹` solution of the Floer equation of the positive end with energy at most `E`
(`exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_positiveEndChart` in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`), by the `C¹` compactness theorem in a symplectic
chart.

Here the image of `Ω`, or of the translated window, is assumed to stay in one chart. On a closed
manifold this assumption is removed in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Closed`. The bubbles at the points of
`Z` and the assembly of the levels at the ends into a broken configuration are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on Floer breaking at the ends.
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped Manifold

namespace TauCeti

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [NormedAddCommGroup V]
  {H : Puncture → ℝ → M → ℝ}

namespace Floer

variable [NormedSpace ℝ V]

/-- **The perturbation read in a chart is smooth.** For period-one Hamiltonians which are `C^n` on
`ℝ × M` and a `C^n` partial diffeomorphism `φ` from `M` to a normed space `V`, each component
`K(z, φ⁻¹ y)(v)` of the pair-of-pants perturbation read in the chart is `C^n` jointly in the real
coordinates `z` of `S = ℂ ∖ {0, 1}` and the chart coordinate `y` in the target of `φ`. -/
theorem contDiffOn_pairOfPantsPerturbation_comp_symm {n : ℕ∞} {m : WithTop ℕ∞}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q)))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hnm : (n : WithTop ℕ∞) ≤ m) (v : ℂ) :
    ContDiffOn ℝ n (fun p : (ℝ × ℝ) × V ↦
        pairOfPantsPerturbation H (equivRealProdCLM.symm p.1) (φ.symm p.2) v)
      (thricePuncturedSphereReal ×ˢ φ.target) := by
  refine φ.contDiffOn_comp_symm_of_contMDiffOn
    (K := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v)
    isOpen_thricePuncturedSphereReal ?_ hnm
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contMDiffWithinAt

/-- **The end Hamiltonian read in a chart is smooth.** For a period-one Hamiltonian `H_q` which is
`C^n` on `ℝ × M` and a `C^n` partial diffeomorphism `φ` from `M` to a normed space `V`, the
Hamiltonian `H'_q(t, φ⁻¹ y)` of the positive end `q` read in the chart is `C^n` jointly in the time
`t` and the chart coordinate `y` in the target of `φ`. -/
theorem contDiffOn_positiveEndHamiltonian_comp_symm {n : ℕ∞} {m : WithTop ℕ∞} {q : Puncture}
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q)))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V m) (hnm : (n : WithTop ℕ∞) ≤ m) :
    ContDiffOn ℝ n (fun p : ℝ × V ↦ positiveEndHamiltonian H q p.1 (φ.symm p.2))
      (univ ×ˢ φ.target) :=
  φ.contDiffOn_comp_symm_of_contMDiffOn (K := positiveEndHamiltonian H q) isOpen_univ
    (contMDiff_uncurry_positiveEndHamiltonian hHs).contMDiffOn hnm

/-- **The end datum read in a chart.** Read in a chart `φ`, the cylindrical datum `H'_q(t) dt` of
the positive end `q` is `C³`, and the structures `J'_q(±t)` are `C²`, on an open set containing
`D × φ(C)`, when `J'_q` is `C²` on an open set containing `ℝ × φ(C)`. -/
private theorem exists_isOpen_and_contDiffOn_positiveEndHamiltonian_comp_symm
    [FiniteDimensional ℝ V] {q : Puncture}
    (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {Jq' : ℝ → V → AlmostComplexStructure V}
    {W : Set (ℝ × V)} (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : ℝ × V ↦ (Jq' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    {D : Set (ℝ × ℝ)} {C : Set M} (hCφ : C ⊆ φ.source) (hCW : univ ×ˢ (φ '' C) ⊆ W) :
    ∃ Wc : Set ((ℝ × ℝ) × V), IsOpen Wc ∧ D ×ˢ (φ '' C) ⊆ Wc ∧
      ContDiffOn ℝ 3 (fun p : (ℝ × ℝ) × V ↦ positiveEndHamiltonian H q p.1.2 (φ.symm p.2)) Wc ∧
      ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦
        (Jq' (q.endSign * p.1.2) p.2).toLinearMap.toContinuousLinearMap) Wc := by
  have hσ : ContDiff ℝ 2 fun p : (ℝ × ℝ) × V ↦ (q.endSign * p.1.2, p.2) :=
    (contDiff_const.mul (contDiff_snd.comp contDiff_fst)).prodMk contDiff_snd
  refine ⟨(fun p : (ℝ × ℝ) × V ↦ (q.endSign * p.1.2, p.2)) ⁻¹' W ∩ univ ×ˢ φ.target,
    (hW.preimage hσ.continuous).inter (isOpen_univ.prod φ.open_target), ?_,
    (contDiffOn_positiveEndHamiltonian_comp_symm hHq φ (WithTop.coe_le_coe.2 le_top)).comp
      ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      fun _ hp ↦ ⟨mem_univ _, hp.2.2⟩, hJ'.comp hσ.contDiffOn fun _ hp ↦ hp.1⟩
  rintro ⟨z, _⟩ ⟨-, x, hx, rfl⟩
  exact ⟨hCW ⟨mem_univ _, x, hx, rfl⟩, mem_univ _, φ.toPartialEquiv.map_source (hCφ hx)⟩

/-- A translated end `v(z) = u(φ'_q(z + (R, 0)))`, on a window `Ω` whose translate lies in a band
`(a, ∞) × (t₀, t₀ + 1)` of the positive end, is `Cⁿ` on `Ω` when `u` is `Cⁿ` on a set `U`
containing the part `s > a` of the positive end chart. -/
private theorem contMDiffOn_comp_positiveEndChart_add {n : WithTop ℕ∞} {q : Puncture}
    {Ω U : Set (ℝ × ℝ)} {u : ℝ × ℝ → M} {R a t₀ : ℝ}
    (hΩT : ∀ z ∈ Ω, z + (R, 0) ∈ Ioi a ×ˢ Ioo t₀ (t₀ + 1))
    (haU : ∀ ζ : ℝ × ℝ, a < ζ.1 → positiveEndChart q ζ ∈ U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n u U) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I n (fun z ↦ u (positiveEndChart q (z + (R, 0)))) Ω :=
  hu.comp ((contDiff_positiveEndChart q n).comp
    (contDiff_id.add contDiff_const)).contMDiff.contMDiffOn fun z hz ↦ haU _ (hΩT z hz).1

end Floer

namespace SmoothTwoForm.IsNondegenerate

open Floer

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **The Hamiltonian vector fields of the perturbation are `C²` in every chart.** For period-one
`C³` Hamiltonians `H_q`, the Hamiltonian vector field of each component `z ↦ K_z(w)` of the
pair-of-pants perturbation, read in the real coordinates of `S = ℂ ∖ {0, 1}` and in the chart of
`M` at `α`, is `C²` on `S` times the chart target. -/
theorem contDiffOn_hamiltonianVectorFieldInChartAt_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q))) (w : ℂ) (α : M) :
    ContDiffOn ℝ 2 (ω.hamiltonianVectorFieldInChartAt α
        fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x w)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target) :=
  hω.contDiffOn_hamiltonianVectorFieldInChartAt
    (fun _ hz x ↦ (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x w).of_le
      (by norm_num)) α

/-- **Floer pairs of pants in a symplectic chart converge off finitely many bubbling points, for an
energy bound over the part of the domain considered.** This is the compactness theorem for Floer
solutions in a symplectic chart (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`)
for the pair-of-pants perturbation `K` of period-one `C³` Hamiltonians `H_q` on `M`. Let `D ⊆ S`
and `C ⊆ φ.source` be compact, let `φ` pull the symplectic form `ω₀` back to `ω` at the points of
`C`, let the structures `J(z, x)` be tamed by `ω` over `D × C`, and let `J'` be the family `J` read
in the chart, `C²` on an open set containing `D × φ(C)`. There is a threshold `δ > 0` such that for
every open `Ω ⊆ D` and every sequence of `C³` solutions `uₖ` of `(du - X_K)^{0,1} = 0` on `Ω` with
`uₖ(Ω) ⊆ C`, integrable energy density and energy over `Ω` at most `A`, a subsequence converges off
a finite set `Z ⊆ Ω` with `#Z * δ ≤ A`, in the sense of the chart theorem. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPants_of_setIntegral_le
    (hω : ω.IsNondegenerate) (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω C) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
        (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
        (u k) z ≤ A) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u (ψ n)) y) ∧
        (∀ K, IsCompact K → K ⊆ Ω \ ↑Z →
          ∃ L, ∀ n, ∀ y ∈ K, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  -- Read in the chart, the perturbation is `C³` on `S × φ(U)`, which contains `D × φ(C)`.
  have hW' : IsOpen (W ∩ thricePuncturedSphereReal ×ˢ φ.target) :=
    hW.inter (isOpen_thricePuncturedSphereReal.prod φ.open_target)
  have hDCW' : D ×ˢ (φ '' C) ⊆ W ∩ thricePuncturedSphereReal ×ˢ φ.target := by
    refine subset_inter hDCW (prod_mono hDS ?_)
    rintro _ ⟨x, hx, rfl⟩
    exact φ.toPartialEquiv.map_source (hCφ hx)
  have hK (v : ℂ) := (contDiffOn_pairOfPantsPerturbation_comp_symm hH hHs φ
    (WithTop.coe_le_coe.2 le_top) v).mono (inter_subset_right (s := W))
  exact hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset φ hφ hJJ' hW' (hK 1)
    (hK Complex.I) (hJ'.mono inter_subset_left) hD hC hCφ hDCW' hJt

/-- **Floer pairs of pants in a symplectic chart of a manifold converge off finitely many bubbling
points.** Let `K` be the pair-of-pants perturbation of period-one `C³` Hamiltonians `H_q` on `M`
with `|H_q| ≤ B_q`, let `J(z, x)` be structures on the tangent spaces of `M` tamed by `ω` over
`S = ℂ ∖ {0, 1}`, read in real coordinates, and let `φ` be a smooth partial diffeomorphism from `M`
onto an open subset of `V`. Let `D ⊆ S` and `C ⊆ φ.source` be compact, let `φ` pull the
symplectic form `ω₀` back to `ω` at the points of `C`, and let `J'` be the family `J` read in the
chart, `dφ_x ∘ J(z, x) = J'(z, φ x) ∘ dφ_x` for `z ∈ D` and `x ∈ C`, and `C²` on an open set
containing `D × φ(C)`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
solutions of `(du - X_K)^{0,1} = 0` on `S` for `J(z, u)`, whose end loops `t ↦ uₖ(φ_q(±R + i t))`
converge pointwise to loops `xₖ(q)` as `R → ∞`, with integrable energy and area densities and
topological energy `∫_S uₖ^*ω + ∑ q, ±∫₀¹ H_q(t, xₖ(q)(t)) dt ≤ A`, and with `uₖ(Ω) ⊆ C` for an
open `Ω ⊆ D`. Then there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ A + B₀ + B₁ + B_∞`, and a map `v`, continuous on `Ω \ Z` with values in `C`, such that
along `ψ` every disc about a point of `Z` eventually carries energy at least `δ`, the differentials
of the coordinate maps `φ ∘ u_{ψ n}` are uniformly bounded on every compact subset of `Ω \ Z`, the
coordinate maps converge to `φ ∘ v` locally uniformly on `Ω \ Z`, and `u_{ψ n} → v` pointwise on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation
    (hω : ω.IsNondegenerate) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞))
    {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {C : Set M}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ z ∈ D, ∀ x ∈ C,
      IsComplexLinearMap (J z x) (J' z (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hDCW : D ×ˢ (φ '' C) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃x : ℕ → Puncture → ℝ → M⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k q t, Tendsto (fun R : ℝ ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x k q t))) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u k))
        thricePuncturedSphereReal) →
      (∀ k, IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) →
      (∀ k, (∫ z in thricePuncturedSphereReal, (SmoothBundleForm.eval₂ ω (u k z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x k q t) ≤ A) →
      (∀ k, MapsTo (u k) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u (ψ n)) y) ∧
        (∀ K, IsCompact K → K ⊆ Ω \ ↑Z →
          ∃ L, ∀ n, ∀ y ∈ K, ‖fderiv ℝ (φ ∘ u (ψ n)) y‖ ≤ L) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (ψ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (ψ n) y) atTop (𝓝 (v y)) := by
  set Ks : ℝ × ℝ → M → ℝ := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → M → ℝ := fun z x ↦
    pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPants_of_setIntegral_le
      φ hH hHs hφ hJJ' hW hJ' hD hDS hC hCφ hDCW fun z hz x _ ↦ hJt z (hDS hz) x
  refine ⟨δ, hδ, fun Ω u x A hΩ hΩD hu hfl hx hE hA htop huC ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  -- The energy over `Ω` is at most the energy over `S`, hence at most `A + B₀ + B₁ + B_∞`.
  have hle (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ A + ∑ q, B q := by
    linarith [htop k, hω.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu k).of_le (by norm_num)) (hx k) (hE k) (hA k)
      (J := fun z ↦ J z (u k z)) (fun z hz ↦ hJt z hz _) (hfl k) hΩS]
  exact hconv hΩ hΩD (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huC
    (fun k ↦ (hE k).mono_set hΩS) hle

/-- **Translated ends of Floer solutions solve the Floer equation of the end.** Let `K` be equal
to `H_q(t) dt` beyond `T₀` on the end `q`, and the structures `J` equal to `J_q(t)` there. Let `u`
be a `C³` solution of energy at most `E` on an open set `U` containing the part `s > max T₀ 0` of
the positive end chart, such as a Floer pair of pants on `S`. A translated end
`v(z) = u(φ'_q(z + (R, 0)))`, `R ≥ 0`, on an open window `Ω` inside a band
`(max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end chart, whose image lies in a set `C` where the
end structures are tamed, is a `C³` solution of the cylindrical Floer equation
`(dv - X_{H'_q} dt)^{0,1} = 0` of the positive end on `Ω`, with integrable energy density and
energy over `Ω` at most `E`. This is how compactness theorems for a fixed cylindrical equation
apply to the windows that move off along an end. -/
theorem contMDiffOn_and_isComplexLinearMap_and_integral_le_comp_positiveEndChart_add
    (hω : ω.IsNondegenerate) {K : ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq t x) {C : Set M}
    (hJt : ∀ t, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (Jq t x)) {Ω D U : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) {u : ℝ × ℝ → M} {R E t₀ : ℝ} (hΩD : Ω ⊆ D)
    (hDT : D ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) (hR : 0 ≤ R) (hU : IsOpen U)
    (hUq : ∀ ζ : ℝ × ℝ, max T₀ 0 < ζ.1 → positiveEndChart q ζ ∈ U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u U)
    (hfl : ∀ z ∈ U,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedMFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) u z).toLinearMap)
    (hE0 : 0 ≤ E)
    (hE : ∫⁻ z in U, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) u z) ≤ ENNReal.ofReal E)
    (huC : MapsTo (fun z ↦ u (positiveEndChart q (z + (R, 0)))) Ω C) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (fun z ↦ u (positiveEndChart q (z + (R, 0)))) Ω ∧
      (∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jq (q.endSign * z.2) (u (positiveEndChart q (z + (R, 0)))))
        (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z).toLinearMap) ∧
      IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (positiveEndChart q (z + (R, 0))))) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
        (fun z ↦ u (positiveEndChart q (z + (R, 0)))) z ≤ E := by
  set v : ℝ × ℝ → M := fun z ↦ u (positiveEndChart q (z + (R, 0)))
  -- The translated window lies in the band `(max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end
  -- chart.
  have hΩT (z : ℝ × ℝ) (hz : z ∈ Ω) : z + (R, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) hR
  have hHd (t : ℝ) : MDifferentiable I 𝓘(ℝ) (H q t) :=
    (hHq.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by norm_num)
  have hT (z : ℝ × ℝ) (hz : z ∈ Ω) : T₀ ≤ z.1 + R := by
    simpa using ((le_max_left _ _).trans_lt (hΩT z hz).1).le
  have hS (z : ℝ × ℝ) (hz : z ∈ Ω) : positiveEndChart q (z + (R, 0)) ∈ U := hUq _ (hΩT z hz).1
  have hvC : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 v Ω := contMDiffOn_comp_positiveEndChart_add hΩT hUq hu
  -- Beyond `T₀` the structure on the end `q` is `J_q(±t)`, so `v` solves the cylindrical equation.
  have hvfl (z : ℝ × ℝ) (hz : z ∈ Ω) : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (Jq (q.endSign * z.2) (v z)) (ω.perturbedMFDeriv (fun _ _ ↦ 0)
        (fun w ↦ positiveEndHamiltonian H q w.2) v z).toLinearMap := by
    have hJz : J (positiveEndChart q (z + (R, 0))) = Jq (q.endSign * z.2) := by
      funext x
      rw [show z + (R, 0) = (z.1 + R, z.2) by ext <;> simp, positiveEndChart_mk]
      exact hJ _ _ x (hT z hz)
    have h := hfl _ (hS z hz)
    rw [hJz] at h
    exact isComplexLinearMap_perturbedMFDeriv_comp_positiveEndChart_add hKH hH hHd R (hT z hz)
      ((hu.contMDiffAt (hU.mem_nhds (hS z hz))).mdifferentiableAt (by norm_num)) h
  -- The energy of `v` over `Ω` is at most the energy of `u` over `U`.
  have hlin := (setLIntegral_floerEnergyDensity_comp_positiveEndChart_add_le_of_isOpen q hKH hH hHd
    hU (hu.mdifferentiableOn (by norm_num)) (le_max_left T₀ 0) hUq R hΩ.measurableSet hΩT).trans hE
  -- The Hamiltonian vector fields of `0` and of `H'_q(t)` are continuous, so the energy bound
  -- over `Ω` is one for the Bochner integral.
  have hX {F : ℝ × ℝ → M → ℝ} (hF : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 2 (uncurry F)) :
      ContinuousOn (fun p : (ℝ × ℝ) × M ↦
        (⟨p.2, ω.hamiltonianVectorField (F p.1) p.2⟩ : TangentBundle I M)) (Ω ×ˢ univ) :=
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp) hF).continuous.continuousOn
  have hH' : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 2
      (uncurry fun (w : ℝ × ℝ) x ↦ positiveEndHamiltonian H q w.2 x) :=
    ((contMDiff_uncurry_positiveEndHamiltonian hHq).comp
      ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)).of_le (by norm_num)
  exact ⟨hvC, hvfl, ω.integrableOn_and_setIntegral_floerEnergyDensity_le hΩ hΩ.measurableSet
    subset_rfl (hvC.of_le (by norm_num)) (hX contMDiff_const) (hX hH')
    (fun z hz ↦ floerEnergyDensity_nonneg (u := v) hω (hJt _ _ (huC hz)) (hvfl z hz)) hE0 hlin⟩

/-- **The translated ends of Floer pairs of pants in a symplectic chart of a manifold converge
off finitely many bubbling points.** Let `K` be equal to `H_q(t) dt` beyond `T₀` on the end `q`,
for a period-one Hamiltonian `H_q` which is `C³` on `ℝ × M`. Let `J(z, x)` be structures on the
tangent spaces of `M`, `z ∈ S = ℂ ∖ {0, 1}` read in real coordinates, which on the end `q` beyond
`T₀` are `J(φ_q(±s, t), x) = J_q(t, x)`. Let `φ` be a smooth partial diffeomorphism from `M` onto
an open subset of `V`, let `C ⊆ φ.source` be compact,
let `φ` pull the symplectic form `ω₀` back to `ω` at the points of `C`, let every `J_q(t, x)` with
`x ∈ C` be tamed by `ω`, and let `J'_q` be the family `J_q` read in the chart,
`dφ_x ∘ J_q(t, x) = J'_q(t, φ x) ∘ dφ_x` for `x ∈ C`, and `C²` on an open set containing
`ℝ × φ(C)`. Fix a compact window `D ⊆ (max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end chart.
There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_K)^{0,1} = 0` on `S` for `J(z, u)` with energy at most `E ≥ 0`, let `Rₖ ≥ 0` be heights,
and let the translated ends `vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))` map an open `Ω ⊆ D` into `C`. Then
there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a map `v`, continuous on
`Ω \ Z` with values in `C`, such that along `ψ` every disc about a point of `Z` eventually carries
energy at least `δ` for the cylindrical datum `H'_q dt`, the differentials of the coordinate maps
`φ ∘ v_{ψ n}` are uniformly bounded on every compact subset of `Ω \ Z`, the coordinate maps converge
to `φ ∘ v` locally uniformly on `Ω \ Z`, and `v_{ψ n} → v` pointwise on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart
    (hω : ω.IsNondegenerate) {K : ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq t x)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {Jq' : ℝ → V → AlmostComplexStructure V}
    {W : Set (ℝ × V)} {D : Set (ℝ × ℝ)} {C : Set M} {t₀ : ℝ}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ t, ∀ x ∈ C,
      IsComplexLinearMap (Jq t x) (Jq' t (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : ℝ × V ↦ (Jq' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ t, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (Jq t x))
    (hD : IsCompact D) (hDT : D ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hCW : univ ×ˢ (φ '' C) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (positiveEndChart q (z + (R k, 0)))) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (ψ n) (positiveEndChart q (z + (R (ψ n), 0)))) y) ∧
        (∀ L, IsCompact L → L ⊆ Ω \ ↑Z → ∃ B, ∀ n, ∀ y ∈ L,
          ‖fderiv ℝ (fun z ↦ φ (u (ψ n) (positiveEndChart q (z + (R (ψ n), 0))))) y‖ ≤ B) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn
          (fun n z ↦ φ (u (ψ n) (positiveEndChart q (z + (R (ψ n), 0))))) (φ ∘ v) atTop
          (Ω \ ↑Z) ∧
        ∀ y ∈ Ω \ ↑Z,
          Tendsto (fun n ↦ u (ψ n) (positiveEndChart q (y + (R (ψ n), 0)))) atTop (𝓝 (v y)) := by
  obtain ⟨Wc, hWc, hDCW, hKt, hJc⟩ :=
    exists_isOpen_and_contDiffOn_positiveEndHamiltonian_comp_symm hHq φ hW hJ' hCφ hCW (D := D)
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset φ
    (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ positiveEndHamiltonian H q w.2)
    (J := fun z ↦ Jq (q.endSign * z.2)) (J' := fun z ↦ Jq' (q.endSign * z.2))
    hφ (fun _ _ x hx ↦ hJJ' _ x hx) hWc contDiffOn_const hKt hJc hD hC hCφ hDCW
    fun _ _ x hx ↦ hJt _ x hx
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huC ↦ ?_⟩
  have h (k : ℕ) :=
    contMDiffOn_and_isComplexLinearMap_and_integral_le_comp_positiveEndChart_add hω hKH hH hHq
      hJ hJt hΩ hΩD hDT (hR k) isOpen_thricePuncturedSphereReal
      (fun _ hζ ↦ positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hζ))
      (hu k) (hfl k) hE0 (hE k) (huC k)
  exact hconv hΩ hΩD (fun k ↦ (h k).1) (fun k ↦ (h k).2.1) huC (fun k ↦ (h k).2.2.1)
    fun k ↦ (h k).2.2.2

/-- **The translated ends of smooth Floer pairs of pants in a symplectic chart of a manifold
converge in `C¹` off finitely many bubbling points to a solution of the Floer equation of the
positive end on `Ω \ Z`.** Under the hypotheses of
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart`, there is a
threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions of
`(du - X_K)^{0,1} = 0` on `S` for `J(z, u)` with energy at most `E ≥ 0`, let `Rₖ ≥ 0` be heights,
and let the translated ends `vₖ(z) = uₖ(φ'_q(z + (Rₖ, 0)))` map an open `Ω ⊆ D` into `C`. Then
there are a subsequence `ψ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a map `v` with values in
`C` on `Ω \ Z` such that along `ψ` every disc about a point of `Z` eventually carries energy at
least `δ` for the cylindrical datum `H'_q dt`, the coordinate maps `φ ∘ v_{ψ n}` and their
derivatives converge to `φ ∘ v` and its derivative locally uniformly on `Ω \ Z`, `v` is a `C¹`
solution on `Ω \ Z` of the Floer equation of the positive end, for the datum `H'_q dt` and the
structures `J_q(±t)`, and the energy of `v` over `Ω \ Z` is finite and at most `E`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset_comp_positiveEndChart
    (hω : ω.IsNondegenerate) {K : ℂ → M → ℂ →L[ℝ] ℝ} {T₀ : ℝ} {q : Puncture}
    (hKH : ∀ w x, T₀ ≤ q.endSign * (q.endCoord w).re →
      K w x = H q (q.endCoord w).im x • q.endAngularForm w)
    (hH : Periodic (H q) 1)
    (hHq : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {Jq : ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ s t x, T₀ ≤ s → J (endChart q (q.endSign * s, t)) x = Jq t x)
    (φ : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {Jq' : ℝ → V → AlmostComplexStructure V}
    {W : Set (ℝ × V)} {D : Set (ℝ × ℝ)} {C : Set M} {t₀ : ℝ}
    (hφ : ∀ x ∈ C, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hJJ' : ∀ t, ∀ x ∈ C,
      IsComplexLinearMap (Jq t x) (Jq' t (φ x)) (mvfderiv I φ x).toLinearMap) (hW : IsOpen W)
    (hJ' : ContDiffOn ℝ 2
      (fun p : ℝ × V ↦ (Jq' p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJt : ∀ t, ∀ x ∈ C, (hω.symplecticFormAt x).Tames (Jq t x))
    (hD : IsCompact D) (hDT : D ⊆ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1)) (hC : IsCompact C)
    (hCφ : C ⊆ φ.source) (hCW : univ ×ˢ (φ '' C) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃R : ℕ → ℝ⦄ ⦃E : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, 0 ≤ R k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedMFDeriv (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) (u k) z).toLinearMap) →
      0 ≤ E →
      (∀ k, ∫⁻ z in thricePuncturedSphereReal, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ K (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ K (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ ENNReal.ofReal E) →
      (∀ k, MapsTo (fun z ↦ u k (positiveEndChart q (z + (R k, 0)))) Ω C) →
      ∃ (ψ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M), StrictMono ψ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          (fun z ↦ u (ψ n) (positiveEndChart q (z + (R (ψ n), 0)))) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) C ∧
        TendstoLocallyUniformlyOn
          (fun n ↦ φ ∘ fun z ↦ u (ψ n) (positiveEndChart q (z + (R (ψ n), 0)))) (φ ∘ v) atTop
          (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn
          (fun n ↦ fderiv ℝ (φ ∘ fun z ↦ u (ψ n) (positiveEndChart q (z + (R (ψ n), 0)))))
          (fderiv ℝ (φ ∘ v)) atTop (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
          (Jq (q.endSign * z.2) (v z))
          (ω.perturbedMFDeriv (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2) v
            z).toLinearMap) ∧
        IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ positiveEndHamiltonian H q w.2)
          v) (Ω \ ↑Z) ∧
        ∫ z in Ω \ ↑Z, ω.floerEnergyDensity (fun _ _ ↦ 0)
          (fun w ↦ positiveEndHamiltonian H q w.2) v z ≤ E := by
  obtain ⟨Wc, hWc, hDCW, hKt, hJc⟩ :=
    exists_isOpen_and_contDiffOn_positiveEndHamiltonian_comp_symm hHq φ hW hJ' hCφ hCW (D := D)
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset φ
      (Ks := fun _ _ ↦ 0) (Kt := fun w ↦ positiveEndHamiltonian H q w.2)
      (J := fun z ↦ Jq (q.endSign * z.2)) (J' := fun z ↦ Jq' (q.endSign * z.2))
      hφ (fun _ _ x hx ↦ hJJ' _ x hx) hWc contDiffOn_const hKt hJc hD hC hCφ hDCW
      fun _ _ x hx ↦ hJt _ x hx
  refine ⟨δ, hδ, fun Ω u R E hΩ hΩD hR hu hfl hE0 hE huC ↦ ?_⟩
  -- The translated windows lie in the band `(max T₀ 0, ∞) × (t₀, t₀ + 1)` of the positive end
  -- chart.
  have hΩT (k : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) :
      z + (R k, 0) ∈ Ioi (max T₀ 0) ×ˢ Ioo t₀ (t₀ + 1) :=
    add_mk_zero_mem_Ioi_prod (hDT (hΩD hz)) (hR k)
  have hSq (ζ : ℝ × ℝ) (hζ : max T₀ 0 < ζ.1) : positiveEndChart q ζ ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal ((le_max_right _ _).trans_lt hζ)
  have hvC (k : ℕ) := contMDiffOn_comp_positiveEndChart_add (q := q) (hΩT k) hSq (hu k)
  have h (k : ℕ) :=
    contMDiffOn_and_isComplexLinearMap_and_integral_le_comp_positiveEndChart_add hω hKH hH hHq
      hJ hJt hΩ hΩD hDT (hR k) isOpen_thricePuncturedSphereReal hSq
      ((hu k).of_le (WithTop.coe_le_coe.2 le_top)) (hfl k) hE0 (hE k) (huC k)
  exact hconv hΩ hΩD hvC (fun k ↦ (h k).2.1) huC (fun k ↦ (h k).2.2.1) fun k ↦ (h k).2.2.2

end SmoothTwoForm.IsNondegenerate

end TauCeti
