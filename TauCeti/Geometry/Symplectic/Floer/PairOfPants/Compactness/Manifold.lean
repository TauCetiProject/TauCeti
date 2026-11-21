/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic

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

Here the image of `Ω` is assumed to stay in one chart. Localizing the images of small discs into
charts on a closed manifold, the bubbles at the points of `Z` and breaking along the three ends are
not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
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
  rintro ⟨z, y⟩ ⟨hz, hy⟩
  refine ContDiffAt.contDiffWithinAt ?_
  -- The point `z` of `S` and the chart inverse `φ⁻¹` are `C^n` into the product `ℂ × M`.
  have hsymm : ContMDiffAt 𝓘(ℝ, V) I n φ.symm y :=
    (φ.symm.contMDiffOn.of_le hnm).contMDiffAt (φ.open_target.mem_nhds hy)
  have hpair : ContMDiffAt 𝓘(ℝ, (ℝ × ℝ) × V) (𝓘(ℝ, ℂ).prod I) n
      (fun p : (ℝ × ℝ) × V ↦ (equivRealProdCLM.symm p.1, φ.symm p.2)) (z, y) :=
    ((equivRealProdCLM.symm.contDiff.comp contDiff_fst).contMDiff.contMDiffAt).prodMk
      (hsymm.comp (z, y) contDiff_snd.contMDiff.contMDiffAt)
  have hK := (contMDiffAt_pairOfPantsPerturbation hH hHs ⟨equivRealProdCLM.symm z, hz⟩
    (φ.symm y)).comp (z, y) hpair
  exact (contMDiffAt_iff_contDiffAt.1 hK).clm_apply contDiffAt_const

end Floer

namespace SmoothTwoForm.IsNondegenerate

open Floer

variable [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ E]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V}
  {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
  {J' : ℝ × ℝ → V → AlmostComplexStructure V}

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
    have habs := abs_le.1 (hω.abs_integral_floerEnergyDensity_pairOfPantsPerturbation_sub_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu k).of_le (by norm_num)) (hx k) (hE k)
      (hA k))
    refine (setIntegral_mono_set (hE k) (ae_restrict_of_forall_mem
      isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦ ?_)
      (Eventually.of_forall hΩS)).trans ?_
    · exact floerEnergyDensity_nonneg hω (hJt z hz _) (hfl k z hz)
    · linarith [habs.2, htop k]
  exact hconv hΩ hΩD (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huC
    (fun k ↦ (hE k).mono_set hΩS) hle

end SmoothTwoForm.IsNondegenerate

end TauCeti
