/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Compactness of Floer pairs of pants

Let `K` be the pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation` of period-one
`C³` Hamiltonians `H_q` with `|H_q| ≤ B_q` on the three ends of `S = ℂ ∖ {0, 1}`, with values in a
symplectic vector space `(V, ω)`, and let `J(z, x)` be a `C²` family of `ω`-tame almost complex
structures on `S × V`. A Floer solution `u` on `S` whose end loops have limiting actions `a_q`
has energy at most `a_0 + a_1 - a_∞ + B_0 + B_1 + B_∞`
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsPerturbation_le`). So a sequence
of such solutions whose action differences `a_0 + a_1 - a_∞` are bounded above has uniformly
bounded energy, and the compactness theorem for Floer solutions of bounded energy
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) applies
on every compact window of `S`.

The main result fixes compact sets `D ⊆ S` and `K ⊆ V`, and gives a threshold `δ > 0`. For every
open `Ω ⊆ D` and every sequence of solutions with image of `Ω` in `K` and action differences at
most `A`, a subsequence converges locally uniformly on `Ω` off a finite set `Z` of bubbling points
with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, and every disc about a point of `Z` eventually carries energy
at least `δ`. This is the interior part of Gromov–Floer compactness for the pair of pants: the
regularity of the limit, the bubbles at the points of `Z`, and breaking along the three ends are
not treated here.

**Pairs of pants with continuation necks.** Pair-of-pants products for two choices of end
Hamiltonians are compared by the pairs of pants with continuation necks,
`K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`: on each end `q` the datum
interpolates, across a neck at the signed longitudinal coordinate `L_q`, from the inner
Hamiltonian `G_q` to the outer Hamiltonian `H_q`. As the neck positions tend to infinity these
domains break into a pair of pants with end Hamiltonians `G` and continuation cylinders on its
ends; these broken configurations are the compositions of continuation maps with pair-of-pants
products compared by `TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap`.
The same interior compactness holds on both pieces of the broken domain, uniformly in the neck
positions. On a truncation `S_R` the datum depends on the neck positions only through `min L_q R`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_of_min_eq`), so if every neck either lies
beyond `R` or stays at a fixed position, the compactness theorem applies on `S_R`:
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuationPerturbation`.
Read in the positive end chart `φ'_q` translated by the neck position, the map
`w ↦ u(φ'_q(w + (L_q, 0)))` solves the continuation equation of the cylinder where
`s + L_q ≥ 2`, with the same energy on bands of angular width one
(`isComplexLinearMap_perturbedFDeriv_continuationHomotopy_comp_positiveEndChart_add`,
`setIntegral_floerEnergyDensity_continuationHomotopy_comp_positiveEndChart_add_eq`). So the
compactness theorem applies on every window `[a, b] × [t₀, t₀ + 1]` of the cylinder as soon as
`a + L_q ≥ 2`
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart_add`).
In both theorems the threshold `δ` does not depend on the neck positions, and the energy bound is
the total Floer energy on `S`, which
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`
bounds by the end actions uniformly in the neck positions. Applying the two theorems in turn, to
the pants piece and to the necks one end at a time, gives a single subsequence converging on all
pieces. Limits on the whole pieces, the bubbles at the concentration points, the breaking of
Floer cylinders off the necks, and neck positions moving in a compact parameter window are not
treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.

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

/-- **Floer pairs of pants with bounded end actions converge off finitely many bubbling points.**
Let `K` be the pair-of-pants perturbation of period-one `C³` Hamiltonians `H_q` with
`|H_q| ≤ B_q`, and let `J(z, x)` be a `C²` family of `ω`-tame structures on `S × V`, where
`S = ℂ ∖ {0, 1}` is read in real coordinates. Fix compact sets `D ⊆ S` and `K ⊆ V`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions of
`(du - X_K)^{0,1} = 0` on `S` for `J(z, u)`, with limiting end actions `aₖ(q)` satisfying
`aₖ(0) + aₖ(1) - aₖ(∞) ≤ A`, and with `uₖ(Ω) ⊆ K` for an open `Ω ⊆ D`. Then there are a
subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + B_0 + B_1 + B_∞`, and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries energy at
least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsPerturbation
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q))) {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, ω.Tames (J z x))
    {D : Set (ℝ × ℝ)} {K : Set V} (hD : IsCompact D) (hDS : D ⊆ thricePuncturedSphereReal)
    (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃a : ℕ → Puncture → ℝ⦄ ⦃A : ℝ⦄,
      IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
          (ω.perturbedFDeriv
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I)
            (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u k (equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * I))))) atTop (𝓝 (a k q))) →
      (∀ k, a k .zero + a k .one - a k .inf ≤ A) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hS : IsOpen (thricePuncturedSphereReal ×ˢ (univ : Set V)) :=
    isOpen_thricePuncturedSphereReal.prod isOpen_univ
  have hK' {n : ℕ∞} (hn : (n : WithTop ℕ∞) ≤ 3) (v : ℂ) : ContDiffOn ℝ n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le hn) hz x
      v).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (hK' (by norm_num) 1) (hK' (by norm_num) I) hJ hD hK (prod_mono hDS (subset_univ K))
    fun z hz x _ ↦ hJt z (hDS hz) x
  refine ⟨δ, hδ, fun Ω u a A hΩ hΩD hu hfl ha hA huK ↦ ?_⟩
  set Ks : ℝ × ℝ → V → ℝ := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1
  set Kt : ℝ × ℝ → V → ℝ := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  -- The energy over `Ω` is at most the energy over `S`, hence at most `A + B_0 + B_1 + B_∞`.
  have hf0 (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) :
      0 ≤ ω.floerEnergyDensity Ks Kt (u k) z :=
    ω.floerEnergyDensity_nonneg (hJt z hz _) (hfl k z hz)
  -- The action bound `a_∞ ≤ a_0 + a_1 + B_0 + B_1 + B_∞` makes the energy bound nonnegative.
  have hE0 : 0 ≤ A + ∑ q, B q := by
    have h := le_add_add_sum_of_tendsto_hamiltonianAction ω hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu 0).of_le (by norm_num))
      (fun z hz ↦ hJt z hz _) (hfl 0) (ha 0)
    linarith [hA 0]
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ks Kt (u k) z) ≤
      ENNReal.ofReal (A + ∑ q, B q) := by
    refine (lintegral_mono_set hΩS).trans <|
      (lintegral_floerEnergyDensity_pairOfPantsPerturbation_le ω hH
        (fun q ↦ (hHs q).of_le (by norm_num)) hB ((hu k).of_le (by norm_num))
        (fun z hz ↦ hJt z hz _) (hfl k) (ha k)).trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [Puncture.sum_univ, Puncture.endSign_zero, Puncture.endSign_one,
      Puncture.endSign_inf]
    linarith [hA k]
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal
      ((hu k).of_le (by norm_num)) (hK' (by norm_num) 1) (hK' (by norm_num) I)).mono
        hΩS).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z hz ↦ hf0 k (hΩS hz))).2
        ((hlin k).trans_lt ENNReal.ofReal_lt_top)⟩
  exact hconv hΩ hΩD (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hfl k z (hΩS hz)) huK hint
    fun k ↦ by
      rw [integral_eq_lintegral_of_nonneg_ae
        (ae_restrict_of_forall_mem hΩm fun z hz ↦ hf0 k (hΩS hz))
        (hint k).aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hE0 (hlin k)


/-! ### Pairs of pants with continuation necks -/

section ContinuationNecks

open TauCeti.MeasureTheory
open scoped NNReal

variable {G : Puncture → ℝ → V → ℝ}

/-- **Compactness on the pants side of the necks.** Let `G`, `H` be period-one `C³` inner and
outer Hamiltonians, fix a truncation `S_R`, neck positions `L₀`, a compact `K ⊆ V`, and a `C²`
family `J` of structures on `S × V`, in real coordinates, which is `ω`-tame on `S_R × K`. There is
a threshold `δ > 0` with the following property. Let `uₖ` be maps which are `C³` on `S`, with
total Floer energy on `S` at most `E` for the pair-of-pants perturbation `K` with continuation
necks at positions `Lₖ`, where `min (Lₖ q) R = min (L₀ q) R` for every end `q` (each neck either
lies beyond `R` or is at the fixed position `L₀ q`). Suppose that on an open `Ω ⊆ S_R` they solve
the Floer equation `(du - X_K)^{0,1} = 0` and `uₖ(Ω) ⊆ K`. Then there are a subsequence `φ`, a
finite set `Z ⊆ Ω` with `#Z * δ ≤ E` and a continuous `v : Ω \ Z → K` such that along `φ` every
disc about a point of `Z` eventually carries energy at least `δ` for the datum with necks at `L₀`,
the differentials are bounded on compact subsets of `Ω \ Z`, and `u_{φ n} → v` locally uniformly
on `Ω \ Z`. -/
theorem
  exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 3 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (L₀ : Puncture → ℝ) (R : ℝ) {K : Set V} (hK : IsCompact K)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → Puncture → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' truncation R →
      (∀ k q, min (L k q) R = min (L₀ q) R) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
        (u k) z) ≤ E) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L₀ (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L₀ (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  set T := equivRealProdCLM.symm ⁻¹' truncation R
  set K₀ : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    pairOfPantsContinuationPerturbation G H L₀ (equivRealProdCLM.symm z) x v
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  have hW : IsOpen (thricePuncturedSphereReal ×ˢ (univ : Set V)) :=
    isOpen_thricePuncturedSphereReal.prod isOpen_univ
  have hK₀ {n : ℕ∞} (hn : (n : WithTop ℕ∞) ≤ 3) (v : ℂ) :
      ContDiffOn ℝ n (uncurry (K₀ v)) (thricePuncturedSphereReal ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH
      (fun r ↦ (hGs r).of_le hn) (fun r ↦ (hHs r).of_le hn) L₀ hz x v).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW
    (hK₀ (by norm_num) 1) (hK₀ (by norm_num) I) hJ (isCompact_preimage_truncation R) hK
    (prod_mono hTS (subset_univ K)) hJt
  refine ⟨δ, hδ, fun Ω L u E hΩ hΩT hL hu hfl hE huK ↦ ?_⟩
  set KL : ℕ → ℂ → ℝ × ℝ → V → ℝ := fun k v z x ↦
    pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x v
  -- On the truncation the datum with necks at `L k` is the datum with necks at `L₀`.
  have hKL (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ T) (v : ℂ) : KL k v z = K₀ v z :=
    funext fun x ↦ DFunLike.congr_fun
      (pairOfPantsContinuationPerturbation_eq_of_min_eq (hL k) hz x) v
  -- The densities are continuous on `S`, so integrable on the compact truncation.
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (K₀ 1) (K₀ I) (u k)) Ω :=
    (((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal
      ((hu k).of_le (by norm_num)) (hK₀ (by norm_num) 1) (hK₀ (by norm_num) I)).mono
        hTS).integrableOn_compact (isCompact_preimage_truncation R)).mono_set hΩT
  -- The energy over `Ω` is at most the total energy.
  have hEΩ (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity (K₀ 1) (K₀ I) (u k) z ≤ E := by
    rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation _ (hKL k (hΩT hz) 1).symm (hKL k (hΩT hz) I).symm]
    exact (ENNReal.ofReal_le_ofReal_iff E.coe_nonneg).1 (ofReal_integral_le_lintegral_ofReal.trans
      ((setLIntegral_le_lintegral _ _).trans ((hE k).trans_eq ENNReal.ofReal_coe_nnreal.symm)))
  exact hconv hΩ hΩT (fun k ↦ (hu k).mono fun z hz ↦ hTS (hΩT hz))
    (fun k z hz ↦ by
      have h := hfl k z hz
      rwa [ω.perturbedFDeriv_congr _ (hKL k (hΩT hz) 1) (hKL k (hΩT hz) I)] at h)
    huK hint hEΩ

/-- **Compactness along the necks.** Let `G`, `H` be period-one `C³` inner and outer
Hamiltonians, fix an end `q`, a window `D = [a, b] × [t₀, t₀ + 1]` of the cylinder `ℝ × ℝ`, a
compact `K ⊆ V` and a family `J` of structures on the cylinder, `C²` on an open neighbourhood of
`D × K` and `ω`-tame on `D × K`. There is a threshold `δ > 0` with the following property. Let `uₖ`
be maps which are `C³` on `S`, with total Floer energy on `S` at most `E` for the pair-of-pants
perturbation with continuation necks at positions `Lₖ`, where `a + Lₖ q ≥ 2`. Read the end `q` in
its positive end chart `φ'_q` translated by the neck position, `vₖ(w) = uₖ(φ'_q(w + (Lₖ q, 0)))`,
and let `Ω` be an open subset of `[a, b] × (t₀, t₀ + 1)` on which the `uₖ` solve the Floer
equation, with structures `J` in these coordinates, and `vₖ(Ω) ⊆ K`. Then there are a subsequence
`φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` and a continuous `v : Ω \ Z → K` such that along `φ`
every disc about a point of `Z` eventually carries energy at least `δ` for the continuation datum
`C'_q(s, t) dt` from `G'_q` to `H'_q`, the differentials of the `vₖ` are bounded on compact
subsets of `Ω \ Z`, and `v_{φ n} → v` locally uniformly on `Ω \ Z`. When `Lₖ q → ∞` this is the
convergence of the neck to a continuation cylinder, broken off the pair of pants. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart_add
    (ω : SymplecticForm V) (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 3 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (q : Puncture) (a b t₀ : ℝ) {K : Set V} (hK : IsCompact K)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hDW : (Icc a b ×ˢ Icc t₀ (t₀ + 1)) ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ Icc a b ×ˢ Icc t₀ (t₀ + 1), ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → Puncture → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Icc a b ×ˢ Ioo t₀ (t₀ + 1) → (∀ k, 2 ≤ a + L k q) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ w ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J w (u k (positiveEndChart q (w + (L k q, 0)))))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
          (u k) (positiveEndChart q (w + (L k q, 0))) : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
        (u k) z) ≤ E) →
      (∀ k, MapsTo (fun w ↦ u k (positiveEndChart q (w + (L k q, 0)))) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0)
          (continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q))
          (fun w ↦ u (φ n) (positiveEndChart q (w + (L (φ n) q, 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C,
          ‖fderiv ℝ (fun w ↦ u (φ n) (positiveEndChart q (w + (L (φ n) q, 0)))) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn
          (fun n w ↦ u (φ n) (positiveEndChart q (w + (L (φ n) q, 0)))) v atTop (Ω \ ↑Z) := by
  set D := Icc a b ×ˢ Icc t₀ (t₀ + 1)
  set C' := continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q)
  have hC' : ContDiff ℝ 3 (uncurry C') := contDiff_uncurry_continuationHomotopy
    (contDiff_uncurry_positiveEndHamiltonian (hGs q))
    (contDiff_uncurry_positiveEndHamiltonian (hHs q))
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := C') hW contDiffOn_const hC'.contDiffOn hJ hD hK hDW hJt
  refine ⟨δ, hδ, fun Ω L u E hΩ hΩD hL hu hfl hE huK ↦ ?_⟩
  -- The translated maps are `C³` where the translated chart lands in `S`.
  set U : ℕ → Set (ℝ × ℝ) := fun k ↦ {w | 0 < w.1 + L k q}
  have hUo (k : ℕ) : IsOpen (U k) :=
    isOpen_lt continuous_const (continuous_fst.add continuous_const)
  have hUS (k : ℕ) : MapsTo (fun w ↦ positiveEndChart q (w + (L k q, 0))) (U k)
      thricePuncturedSphereReal := fun w hw ↦
    positiveEndChart_mem_thricePuncturedSphereReal
      (by simpa only [U, Set.mem_ofPred_eq, Prod.fst_add] using hw)
  have hv (k : ℕ) : ContDiffOn ℝ 3 (fun w ↦ u k (positiveEndChart q (w + (L k q, 0)))) (U k) :=
    (hu k).comp ((contDiff_positiveEndChart q 3).comp (contDiff_id.add contDiff_const)).contDiffOn
      (hUS k)
  have hDU (k : ℕ) : D ⊆ U k := fun w hw ↦ by
    simp only [U, Set.mem_ofPred_eq]
    linarith [hw.1.1, hL k]
  have hΩD' : Ω ⊆ D := hΩD.trans (prod_mono le_rfl Ioo_subset_Icc_self)
  have hΩL (k : ℕ) : ∀ w ∈ Ω, 2 ≤ w.1 + L k q := fun w hw ↦ by
    linarith [(hΩD hw).1.1, hL k]
  -- The densities are continuous where the translated maps are `C¹`, so integrable on `D`.
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (fun _ _ ↦ 0) C'
      (fun w ↦ u k (positiveEndChart q (w + (L k q, 0))))) Ω :=
    (((ω.continuousOn_floerEnergyDensity (hUo k) ((hv k).of_le (by norm_num))
      contDiffOn_const (hC'.of_le (by norm_num)).contDiffOn).mono (hDU k)).integrableOn_compact
        hD).mono_set hΩD'
  -- The energy over `Ω` is the energy of `u k` over the image of `Ω`, at most the total energy.
  have hEΩ (k : ℕ) : ∫ w in Ω, ω.floerEnergyDensity (fun _ _ ↦ 0) C'
      (fun w ↦ u k (positiveEndChart q (w + (L k q, 0)))) w ≤ E := by
    rw [ω.setIntegral_floerEnergyDensity_continuationHomotopy_comp_positiveEndChart_add_eq hG hH
      (fun r ↦ (hGs r).of_le (by norm_num)) (fun r ↦ (hHs r).of_le (by norm_num))
      ((hu k).differentiableOn (by norm_num)) hΩ.measurableSet (hΩL k)
      (hΩD.trans (prod_mono (subset_univ _) le_rfl))]
    exact (ENNReal.ofReal_le_ofReal_iff E.coe_nonneg).1 (ofReal_integral_le_lintegral_ofReal.trans
      ((setLIntegral_le_lintegral _ _).trans ((hE k).trans_eq ENNReal.ofReal_coe_nnreal.symm)))
  have hS (k : ℕ) {w : ℝ × ℝ} (hw : w ∈ Ω) :
      positiveEndChart q (w + (L k q, 0)) ∈ thricePuncturedSphereReal :=
    hUS k (hDU k (hΩD' hw))
  exact hconv hΩ hΩD' (fun k ↦ (hv k).mono fun w hw ↦ hDU k (hΩD' hw))
    (fun k w hw ↦
      ω.isComplexLinearMap_perturbedFDeriv_continuationHomotopy_comp_positiveEndChart_add hG hH
        (fun r ↦ (hGs r).of_le (by norm_num)) (fun r ↦ (hHs r).of_le (by norm_num)) (hΩL k w hw)
        (((hu k).differentiableOn (by norm_num)).differentiableAt
          (isOpen_thricePuncturedSphereReal.mem_nhds (hS k hw))) (hfl k w hw))
    huK hint hEΩ

end ContinuationNecks

end TauCeti.SymplecticForm
