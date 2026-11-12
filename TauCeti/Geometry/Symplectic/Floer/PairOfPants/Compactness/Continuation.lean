/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Compactness of pairs of pants with continuation necks as the necks stretch

Pair-of-pants products for two choices of end Hamiltonians are compared by the families of pairs
of pants with continuation necks, `K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`
on `S = ℂ ∖ {0, 1}`: on each end `q` the datum interpolates, across a neck at the signed
longitudinal coordinate `L_q`, from the inner Hamiltonian `G_q` to the outer Hamiltonian `H_q`.
As the neck positions tend to infinity these domains break into a pair of pants with end
Hamiltonians `G` and continuation cylinders on its ends; these broken configurations are the
compositions of continuation maps with pair-of-pants products compared by
`TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap`. This file proves the
interior part of Gromov–Floer compactness for such families on both pieces of the broken domain,
for a symplectic vector space target `(V, ω)`, uniformly in the neck positions.

**The pants piece.** On the truncation `S_R` the datum depends on the neck positions only through
`min L_q R` (`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_of_min_eq`). So if every
neck either lies beyond `R` or stays at a fixed position, the data agree on `S_R` with one fixed
datum, and the compactness theorem for Floer solutions of bounded energy
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) applies
there
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation`).

**The necks.** Read in the positive end chart `φ'_q` of the end `q`
(`TauCeti.Floer.positiveEndChart`), beyond the collar `s ≥ 2` the datum is
`C'_q(s - L_q, t) dt`, where `C'_q` is the continuation homotopy from the end Hamiltonian `G'_q` to
`H'_q` of the positive end
(`perturbationPullback_positiveEndChart_pairOfPantsContinuationPerturbation_stdComplexLineImag`).
Translated by the neck position, it is the continuation datum `C'_q(s, t) dt` of the cylinder,
whatever `L_q`. Since `φ'_q` is holomorphic, the translated map `w ↦ u(φ'_q(w + (L_q, 0)))` of a
solution `u` solves the continuation equation there
(`isComplexLinearMap_perturbedFDeriv_continuationHomotopy_comp_positiveEndChart_add`),
and on a band of angular width one its energy is the energy of `u` over the image
(`TauCeti.SymplecticForm.setIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq`). The
compactness theorem then applies on a fixed window `[a, b] × [0, 1]` of the cylinder as soon as
`a + L_q ≥ 2`
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart_add`).

In both theorems the threshold `δ` does not depend on the neck positions, and the energy bound is
the total Floer energy on `S`, which the energy identity of the family
(`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`)
bounds by the end actions uniformly in the neck positions. Applying the two theorems in turn, to
the pants piece and to the necks one end at a time, gives a single subsequence converging on all
pieces. Convergence on one fixed window of each piece is what is proved. Limits on the whole
pieces, the regularity of the limits, the bubbles at the finitely many concentration points, and
the breaking of Floer cylinders off the necks are not treated here, nor are neck positions moving
in a compact parameter window.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal ENNReal

namespace TauCeti

namespace Floer

/-! ### The perturbation on a truncation and on a neck -/

section Datum

variable {X : Type*} {G H : Puncture → ℝ → X → ℝ}

/-- Below the height `R`, moving a neck position beyond `R` does not change the cutoff of the
continuation homotopy. -/
private theorem smoothTransition_sub_min {σ R : ℝ} (hσ : σ ≤ R) (a : ℝ) :
    Real.smoothTransition (σ - min a R) = Real.smoothTransition (σ - a) := by
  rcases le_total a R with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]

/-- **On a truncation the necks only matter up to its height.** On the truncation `S_R`, the
pair-of-pants perturbation with continuation necks depends on the neck positions `L_q` only
through `min L_q R`: every neck beyond `R` lies outside `S_R`, and there the datum is that of the
inner Hamiltonians `G_q`. -/
theorem pairOfPantsContinuationPerturbation_eq_of_min_eq {L L' : Puncture → ℝ} {R : ℝ}
    (hL : ∀ q, min (L q) R = min (L' q) R) {w : ℂ} (hw : w ∈ truncation R) (x : X) :
    pairOfPantsContinuationPerturbation G H L w x =
      pairOfPantsContinuationPerturbation G H L' w x := by
  rw [pairOfPantsContinuationPerturbation_def, pairOfPantsContinuationPerturbation_def]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have hσ := (mem_truncation.1 hw).2.2 q
  simp only [continuationHomotopy_def]
  rw [← smoothTransition_sub_min hσ (L q), hL q, smoothTransition_sub_min hσ]

variable {L : Puncture → ℝ} {q : Puncture}

/-- In the positive end chart of `q`, the pair-of-pants perturbation with continuation necks
sends `∂_s` to `0`. -/
theorem perturbationPullback_positiveEndChart_pairOfPantsContinuationPerturbation_stdComplexLineReal
    (hG : Periodic (G q) 1) (hH : Periodic (H q) 1) {ζ : ℝ × ℝ} (hζ : 0 < ζ.1) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
        stdComplexLineReal ζ x = 0 := by
  have h1 : equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  rw [perturbationPullback_positiveEndChart,
    perturbationPullback_endChart_eq_cylindricalEndLift (pairOfPantsContinuationPerturbation G H L),
    h1]
  beta_reduce
  rw [pairOfPantsContinuationPerturbation_cylindricalEndLift_of_pos hG hH
    (by simpa [equivRealProdCLM_symm_apply, ← mul_assoc] using hζ)]
  simp

/-- **The perturbation on a neck.** In the positive end chart of `q`, beyond the collar
`s ≥ 2`, the pair-of-pants perturbation with continuation necks sends `∂_t` to the continuation
homotopy `C'_q(s - L_q, t)` from the end Hamiltonian `G'_q` to `H'_q` of the positive end. So,
translated by the neck position `L_q`, it is the continuation datum `C'_q(s, t) dt` from `G'_q`
to `H'_q`, whatever `L_q`. -/
theorem perturbationPullback_positiveEndChart_pairOfPantsContinuationPerturbation_stdComplexLineImag
    (hG : Periodic (G q) 1) (hH : Periodic (H q) 1) {ζ : ℝ × ℝ} (hζ : 2 ≤ ζ.1) (x : X) :
    perturbationPullback (positiveEndChart q)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
        stdComplexLineImag ζ x =
      continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q)
        (ζ.1 - L q, ζ.2) x := by
  have hI : equivRealProdCLM.symm stdComplexLineImag = I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  rw [perturbationPullback_positiveEndChart,
    perturbationPullback_endChart_eq_cylindricalEndLift (pairOfPantsContinuationPerturbation G H L),
    hI]
  beta_reduce
  rw [pairOfPantsContinuationPerturbation_cylindricalEndLift_of_pos hG hH
    (by simpa [equivRealProdCLM_symm_apply, ← mul_assoc] using (by linarith : (0 : ℝ) < ζ.1))]
  simp only [equivRealProdCLM_symm_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.add_im, Complex.mul_im, I_im, one_mul, mul_zero, zero_mul, sub_zero,
    add_zero, zero_add, ← mul_assoc, endSign_mul_self, continuationHomotopy_def,
    positiveEndHamiltonian_apply]
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  simp only [mul_one]
  ring

end Datum

end Floer

namespace SymplecticForm

open Floer TauCeti.MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {G H : Puncture → ℝ → V → ℝ} {L : Puncture → ℝ} {q : Puncture}

/-! ### The necks as continuation cylinders -/

section Neck

/-- The positive end chart of `q` translated by `c` is differentiable. -/
private theorem differentiableAt_positiveEndChart_add (q : Puncture) (c : ℝ) (w : ℝ × ℝ) :
    DifferentiableAt ℝ (fun w ↦ positiveEndChart q (w + (c, 0))) w :=
  ((contDiff_positiveEndChart q 1).differentiable one_ne_zero _).comp w
    (differentiableAt_id.add_const _)

omit [FiniteDimensional ℝ V] in
/-- The components of the perturbation are differentiable in the target point at every point
of `S`. -/
private theorem differentiableAt_pairOfPantsContinuationPerturbation
    (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 1 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r)))
    (L : Puncture → ℝ) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) (x : V) (v : ℂ) :
    DifferentiableAt ℝ
      (fun y ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) y v) x :=
  differentiableAt_target_of_differentiableAt
    ((contDiffAt_pairOfPantsContinuationPerturbation_prod hG hH hGs hHs L hz x).differentiableAt
      one_ne_zero) v

/-- On the neck of the end `q`, beyond the collar, the pullback of the perturbation along the
translated positive end chart is the continuation datum. -/
private theorem perturbedFDeriv_comp_positiveEndChart_add_eq (ω : SymplecticForm V)
    (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1) (u : ℝ × ℝ → V) {w : ℝ × ℝ}
    (hw : 2 ≤ w.1 + L q) :
    ω.perturbedFDeriv (fun _ _ ↦ 0)
        (continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q))
        (fun w ↦ u (positiveEndChart q (w + (L q, 0)))) w =
      ω.perturbedFDeriv
        (perturbationPullback (fun w ↦ positiveEndChart q (w + (L q, 0)))
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
          stdComplexLineReal)
        (perturbationPullback (fun w ↦ positiveEndChart q (w + (L q, 0)))
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
          stdComplexLineImag)
        (fun w ↦ u (positiveEndChart q (w + (L q, 0)))) w := by
  refine ω.perturbedFDeriv_congr _ (funext fun x ↦ ?_) (funext fun x ↦ ?_)
  · rw [perturbationPullback_comp_add_right,
      perturbationPullback_positiveEndChart_pairOfPantsContinuationPerturbation_stdComplexLineReal
        (hG q) (hH q) (by simp only [Prod.fst_add]; linarith)]
  · rw [perturbationPullback_comp_add_right,
      perturbationPullback_positiveEndChart_pairOfPantsContinuationPerturbation_stdComplexLineImag
        (hG q) (hH q) (by simpa only [Prod.fst_add] using hw)]
    simp

/-- **The necks solve the continuation equation.** Let `u` solve the Floer equation of the
pair-of-pants perturbation with continuation necks at the point `φ'_q(w + (L_q, 0))` of the end
`q`, read in its positive end chart `φ'_q` translated by the neck position `L_q`, with
`w.1 + L_q ≥ 2`. Then the translated map `w ↦ u(φ'_q(w + (L_q, 0)))` solves at `w` the Floer
equation of the continuation datum `C'_q(s, t) dt` from the end Hamiltonian `G'_q` to `H'_q` of
the positive end. -/
theorem isComplexLinearMap_perturbedFDeriv_continuationHomotopy_comp_positiveEndChart_add
    (ω : SymplecticForm V) (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 1 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r)))
    {u : ℝ × ℝ → V} {J : AlmostComplexStructure V} {w : ℝ × ℝ} (hw : 2 ≤ w.1 + L q)
    (hu : DifferentiableAt ℝ u (positiveEndChart q (w + (L q, 0))))
    (hfloer : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I) u
        (positiveEndChart q (w + (L q, 0))) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (fun _ _ ↦ 0)
        (continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q))
        (fun w ↦ u (positiveEndChart q (w + (L q, 0)))) w : ℝ × ℝ →ₗ[ℝ] V) := by
  have hS : positiveEndChart q (w + (L q, 0)) ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal (by simp only [Prod.fst_add]; linarith)
  rw [perturbedFDeriv_comp_positiveEndChart_add_eq ω hG hH u hw]
  refine ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback (u := u)
    (φ := fun w ↦ positiveEndChart q (w + (L q, 0)))
    (differentiableAt_positiveEndChart_add q (L q) w) hu
    (differentiableAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L hS _ 1)
    (differentiableAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L hS _ I) ?_ hfloer
  rw [fderiv_comp_add_right]
  exact isComplexLinearMap_fderiv_positiveEndChart q _

/-- **The energy of a neck.** Let `u` be differentiable on `S`, and let `s` be a measurable set of
points `w` with `w.1 + L_q ≥ 2` in the band `ℝ × (0, 1)`. The energy over `s` of the translated
map `w ↦ u(φ'_q(w + (L_q, 0)))` for the continuation datum `C'_q(s, t) dt` is the energy of `u`
over the image of `s` for the pair-of-pants perturbation with continuation necks. -/
theorem setIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq (ω : SymplecticForm V)
    (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 1 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r)))
    {u : ℝ × ℝ → V} (hu : DifferentiableOn ℝ u thricePuncturedSphereReal) {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hsL : ∀ w ∈ s, 2 ≤ w.1 + L q) (hsI : s ⊆ univ ×ˢ Ioo 0 1) :
    ∫ w in s, ω.floerEnergyDensity (fun _ _ ↦ 0)
        (continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q))
        (fun w ↦ u (positiveEndChart q (w + (L q, 0)))) w =
      ∫ z in (fun w ↦ positiveEndChart q (w + (L q, 0))) '' s, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (equivRealProdCLM.symm z) x I)
        u z := by
  have hS (w : ℝ × ℝ) (hw : w ∈ s) :
      positiveEndChart q (w + (L q, 0)) ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal
      (by simp only [Prod.fst_add]; linarith [hsL w hw])
  have hinj : InjOn (fun w ↦ positiveEndChart q (w + (L q, 0))) s := by
    intro w hw w' hw' h
    have h' := injOn_positiveEndChart q (x₁ := w + (L q, 0)) (x₂ := w' + (L q, 0))
      ⟨mem_univ _, by simpa using (hsI hw).2⟩ ⟨mem_univ _, by simpa using (hsI hw').2⟩ h
    simpa using h'
  rw [ω.integral_floerEnergyDensity_image hs hinj
    (fun w _ ↦ differentiableAt_positiveEndChart_add q (L q) w)
    (fun w _ ↦ by rw [fderiv_comp_add_right]; exact (det_fderiv_positiveEndChart_pos q _).le)
    (fun w hw ↦ (hu _ (hS w hw)).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hS w hw)))
    (fun w hw ↦ differentiableAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L (hS w hw) _ 1)
    (fun w hw ↦ differentiableAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L (hS w hw) _ I)]
  refine setIntegral_congr_fun hs fun w hw ↦ ?_
  simp only [floerEnergyDensity_def, Function.comp_def,
    perturbedFDeriv_comp_positiveEndChart_add_eq ω hG hH u (hsL w hw)]

end Neck

/-! ### Compactness on the two pieces -/

section Compactness

/-- **Compactness on the pants side of the necks.** Let `G`, `H` be period-one `C³` inner and
outer Hamiltonians, fix a truncation `S_R`, neck positions `L₀`, a compact `K ⊆ V`, and a `C²`
family `J` of structures on `S × V`, in real coordinates, which is `ω`-tame on `S_R × K`. There is
a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions on an open
`Ω ⊆ S_R` of the Floer equation `(du - X_K)^{0,1} = 0` for the pair-of-pants perturbation `K` with
continuation necks at positions `Lₖ`, where `min (Lₖ q) R = min (L₀ q) R` for every end `q` (each
neck either lies beyond `R` or is at the fixed position `L₀ q`), with Floer energy at most `E` and
`uₖ(Ω) ⊆ K`. Then there are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` and a
continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries
energy at least `δ` for the datum with necks at `L₀`, the differentials are bounded on compact
subsets of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuation
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
Hamiltonians, fix an end `q`, a window `[a, b] × [0, 1]`, a compact `K ⊆ V` and a `C²` family `J`
of structures on the cylinder `ℝ × ℝ`, `ω`-tame on the window over `K`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions on `S` of the Floer equation for
the pair-of-pants perturbation with continuation necks at positions `Lₖ`, with
`a + Lₖ q ≥ 2` and Floer energy at most `E`. Read the end `q` in its positive end chart `φ'_q`
translated by the neck position, `vₖ(w) = uₖ(φ'_q(w + (Lₖ q, 0)))`, and let `Ω` be an open subset
of `[a, b] × (0, 1)` on which the structures are `J` in these coordinates and `vₖ(Ω) ⊆ K`. Then
there are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries energy at
least `δ` for the continuation datum `C'_q(s, t) dt` from `G'_q` to `H'_q`, the differentials of
the `vₖ` are bounded on compact subsets of `Ω \ Z`, and `v_{φ n} → v` locally uniformly on
`Ω \ Z`. When `Lₖ q → ∞` this is the convergence of the neck to a continuation cylinder, broken
off the pair of pants. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart_add
    (ω : SymplecticForm V) (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 3 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (q : Puncture) (a b : ℝ) {K : Set V} (hK : IsCompact K)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap))
    (hJt : ∀ z ∈ Icc a b ×ˢ Icc (0 : ℝ) 1, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → Puncture → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Icc a b ×ˢ Ioo 0 1 → (∀ k, 2 ≤ a + L k q) →
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
  set D := Icc a b ×ˢ Icc (0 : ℝ) 1
  set C' := continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q)
  have hC' : ContDiff ℝ 3 (uncurry C') := contDiff_uncurry_continuationHomotopy
    (contDiff_uncurry_positiveEndHamiltonian (hGs q))
    (contDiff_uncurry_positiveEndHamiltonian (hHs q))
  have hD : IsCompact D := isCompact_Icc.prod isCompact_Icc
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := C') isOpen_univ contDiffOn_const hC'.contDiffOn hJ.contDiffOn hD hK
    (subset_univ _) hJt
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
    rw [ω.setIntegral_floerEnergyDensity_comp_positiveEndChart_add_eq hG hH
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

end Compactness

end SymplecticForm

end TauCeti
