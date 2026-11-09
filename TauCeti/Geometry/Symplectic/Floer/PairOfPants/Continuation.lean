/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Curvature
public import TauCeti.Geometry.Symplectic.Floer.Continuation
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

/-!
# Changing the end Hamiltonians of the pair of pants by continuation

Pair-of-pants products for two choices of end Hamiltonians are compared by gluing continuation
cylinders to the ends of the pair of pants `S = ℂ ∖ {0, 1}`. This file constructs the perturbation
data of this gluing. Given period-one Hamiltonians `G_q` (inner) and `H_q` (outer) on each end `q`
and a neck position `L_q ∈ ℝ`, the datum `TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`
is, in the coordinates `(s, t)` of the end `q` with signed longitudinal coordinate `σ = ±s`,

`β(σ - 1) C_q(σ - L_q, t) dt`,  where  `C_q(s, t) = G_q(t) + β(s) (H_q(t) - G_q(t))`

is the continuation homotopy `TauCeti.Floer.continuationHomotopy` from `G_q` to `H_q` and `β` is
the smooth transition from `0` on `(-∞, 0]` to `1` on `[1, ∞)`. So the datum is the pair-of-pants
datum of `G` wherever `σ ≤ L_q` on every end, it is `H_q(t) dt` once `σ ≥ max 2 (L_q + 1)`, and,
for `L_q ≥ 2`, on the neck `L_q ≤ σ ≤ L_q + 1` it is a continuation datum from `G_q` to `H_q`; for
smaller `L_q` the collar cutoff `β(σ - 1)` also acts on the neck, giving a cutoff-modified
continuation datum. As `L_q → ∞` it breaks into a pair of pants with end Hamiltonians `G` and
continuation cylinders on its ends, while for `L_q ≤ 0` on every end it is the pair-of-pants datum
of `H`. Moving the neck positions along a path gives one-parameter families of pairs of pants whose
broken ends are the two compositions of continuation maps with pair-of-pants products compared by
`TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap`.

Compactness of such a family needs an energy bound that is uniform in the neck positions, although
the necks become arbitrarily long. On the end `q` the curvature is
`±(β'(σ - 1) C_q(σ - L_q, t) + β(σ - 1) β'(σ - L_q) (H_q - G_q)(t))`: the first term lives on the
collar `1 ≤ σ ≤ 2` and the second on the neck, and the derivative `β'` has total integral one.
Hence, if `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, the integrated curvature along any map is
at most `∑ q, (B_q + D_q)` for all neck positions; by the energy identity this bounds the energy by
its topological part plus that constant.

## Main definitions

* `TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`: the pair-of-pants perturbation with
  continuation necks at the positions `L_q` from the inner Hamiltonians `G_q` to the outer ones
  `H_q`.

## Main results

* `TauCeti.Floer.contMDiffAt_pairOfPantsContinuationPerturbation`: the perturbation is smooth on
  `S × M` for smooth Hamiltonians on a manifold `M`;
  `TauCeti.Floer.contDiffAt_pairOfPantsContinuationPerturbation_prod` is the `Cⁿ` statement for a
  vector space target.
* `TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_forall_le`:
  where every `σ ≤ L_q`, on the pants side of the necks, it is the pair-of-pants perturbation
  of `G`;
  `TauCeti.Floer.pairOfPantsContinuationPerturbation_of_nonpos`: for nonpositive neck positions it
  is the pair-of-pants perturbation of `H`;
  `TauCeti.Floer.pairOfPantsContinuationPerturbation_self`: for `G = H` it is the pair-of-pants
  perturbation of `H`.
* `TauCeti.Floer.pairOfPantsContinuationPerturbation_cylindricalEndLift_of_pos`: its pullback to
  the end `q` is `β(σ - 1) C_q(σ - L_q, t) dt`;
  `TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_smul_endAngularForm`: beyond the neck and
  the collar, where `σ ≥ max 2 (L_q + 1)`, it is `H_q(t) dt`, so there it is the pair-of-pants
  perturbation of `H`
  (`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le`).
* `SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le`,
  `SymplecticForm.abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le`:
  the integrated curvature is at most `∑ q, (B_q + D_q)`, uniformly in the neck positions.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 8 and 9, on
  perturbation data on surfaces with strip-like ends and their behaviour along long necks.
-/

public noncomputable section

open Set Real Function MeasureTheory Filter Manifold TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti

namespace Floer

variable {M : Type*}

/-- The pair-of-pants perturbation with continuation necks on its ends. Given period-one
Hamiltonians `G_q` (inner) and `H_q` (outer) on the three ends of `S = ℂ ∖ {0, 1}` and neck
positions `L_q`, at `w ∈ ℂ` and `x ∈ M` it is the covector
`∑ q, β(σ_q - 1) C_q(σ_q - L_q, t_q, x) dt_q`, where `(s_q, t_q)` are the coordinates of the end
`q`, `σ_q = ±s_q` is its signed longitudinal coordinate, `β` is the smooth transition and
`C_q = TauCeti.Floer.continuationHomotopy (G q) (H q)` is the continuation homotopy from `G_q` to
`H_q`. -/
def pairOfPantsContinuationPerturbation (G H : Puncture → ℝ → M → ℝ) (L : Puncture → ℝ) (w : ℂ)
    (x : M) : ℂ →L[ℝ] ℝ :=
  ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
      continuationHomotopy (G q) (H q)
        (q.endSign * (q.endCoord w).re - L q, (q.endCoord w).im) x) •
    q.endAngularForm w

theorem pairOfPantsContinuationPerturbation_def (G H : Puncture → ℝ → M → ℝ) (L : Puncture → ℝ)
    (w : ℂ) (x : M) :
    pairOfPantsContinuationPerturbation G H L w x =
      ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
          continuationHomotopy (G q) (H q)
            (q.endSign * (q.endCoord w).re - L q, (q.endCoord w).im) x) •
        q.endAngularForm w := by
  rw [pairOfPantsContinuationPerturbation]

variable {G H : Puncture → ℝ → M → ℝ} {L : Puncture → ℝ}

/-- The perturbation vanishes at every point where the signed longitudinal coordinate of every
end is at most `1`. -/
theorem pairOfPantsContinuationPerturbation_eq_zero_of_forall_le {w : ℂ}
    (h : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) (x : M) :
    pairOfPantsContinuationPerturbation G H L w x = 0 := by
  rw [pairOfPantsContinuationPerturbation_def]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [smoothTransition.zero_of_nonpos (by linarith [h q]), zero_mul, zero_smul]

/-- **The perturbation is the pair-of-pants datum of `G` on the pants side of the necks.** At a
point where the
signed longitudinal coordinate of every end `q` is at most its neck position `L_q`, the
perturbation is the pair-of-pants perturbation of the inner Hamiltonians `G`. -/
theorem pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_forall_le {w : ℂ}
    (h : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L q) (x : M) :
    pairOfPantsContinuationPerturbation G H L w x = pairOfPantsPerturbation G w x := by
  rw [pairOfPantsContinuationPerturbation_def, pairOfPantsPerturbation_def]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [continuationHomotopy_of_nonpos (by dsimp only; linarith [h q])]

/-- **Without necks the perturbation is the pair-of-pants datum of `H`.** If every neck position is
nonpositive, the continuation is already complete where the cutoff of each end is nonzero, and the
perturbation is the pair-of-pants perturbation of the outer Hamiltonians `H`. -/
theorem pairOfPantsContinuationPerturbation_of_nonpos (hL : ∀ q, L q ≤ 0) :
    pairOfPantsContinuationPerturbation G H L = pairOfPantsPerturbation H := by
  funext w x
  rw [pairOfPantsContinuationPerturbation_def, pairOfPantsPerturbation_def]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hc : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0
  · simp [hc]
  · have h₁ := (one_lt_endSign_mul_re_endCoord hc).1
    rw [continuationHomotopy_of_one_le (by dsimp only; linarith [hL q])]

/-- If the inner and outer Hamiltonians agree, the perturbation is their pair-of-pants
perturbation, for all neck positions. -/
@[simp]
theorem pairOfPantsContinuationPerturbation_self (H : Puncture → ℝ → M → ℝ) (L : Puncture → ℝ) :
    pairOfPantsContinuationPerturbation H H L = pairOfPantsPerturbation H := by
  funext w x
  simp [pairOfPantsContinuationPerturbation_def, pairOfPantsPerturbation_def,
    continuationHomotopy_def]

/-- **The perturbation on an end.** On the part `±s > 0` of the end `q`, the pullback of the
perturbation along the end lift `φ` is `β(±s - 1) C_q(±s - L_q, t) dt`: it sends a tangent vector
`v` of the cylinder to `Im v · β(±s - 1) C_q(±s - L_q, t)`, where `C_q` is the continuation
homotopy from `G_q` to `H_q`. -/
theorem pairOfPantsContinuationPerturbation_cylindricalEndLift_of_pos {q : Puncture}
    (hG : Periodic (G q) 1) (hH : Periodic (H q) 1) {z : ℂ} (hz : 0 < q.endSign * z.re) (x : M)
    (v : ℂ) :
    pairOfPantsContinuationPerturbation G H L (q.cylindricalEndLift z) x
        (deriv q.cylindricalEndLift z * v) =
      v.im * (smoothTransition (q.endSign * z.re - 1) *
        continuationHomotopy (G q) (H q) (q.endSign * z.re - L q, z.im) x) := by
  rw [pairOfPantsContinuationPerturbation, Finset.sum_eq_single q]
  · obtain ⟨k, hk⟩ := q.exists_endCoord_cylindricalEndLift z
    have hre : (q.endCoord (q.cylindricalEndLift z)).re = z.re := by simp [hk]
    have him : (q.endCoord (q.cylindricalEndLift z)).im = z.im + k := by simp [hk]
    have hGp : G q (z.im + k) x = G q z.im x := by simpa using congrFun (hG.int_mul k z.im) x
    have hHp : H q (z.im + k) x = H q z.im x := by simpa using congrFun (hH.int_mul k z.im) x
    rw [smul_apply, endAngularForm_cylindricalEndLift, hre, him, smul_eq_mul,
      mul_comm]
    simp only [continuationHomotopy_def, hGp, hHp]
  · intro r _ hr
    simp [smoothTransition_endCoord_cylindricalEndLift_eq_zero hr hz]
  · simp

/-- **The perturbation is `H_r(t_r) dt_r` beyond the neck and the collar.** At a point `w` of the
end `r` whose signed longitudinal coordinate is at least `2` and at least `L_r + 1`, the
perturbation is the angular form of `r` scaled by the outer Hamiltonian `H_r` at the angular
coordinate of `w`. -/
theorem pairOfPantsContinuationPerturbation_eq_smul_endAngularForm {r : Puncture} {w : ℂ}
    (hw : 2 ≤ r.endSign * (r.endCoord w).re) (hwL : L r + 1 ≤ r.endSign * (r.endCoord w).re)
    (x : M) :
    pairOfPantsContinuationPerturbation G H L w x =
      H r (r.endCoord w).im x • r.endAngularForm w := by
  rw [pairOfPantsContinuationPerturbation_def, Finset.sum_eq_single r,
    smoothTransition.one_of_one_le (by linarith), one_mul,
    continuationHomotopy_of_one_le (by dsimp only; linarith)]
  · intro s _ hs
    have hs' := endSign_mul_re_endCoord_nonpos hs.symm (w := w) (by linarith)
    rw [smoothTransition.zero_of_nonpos (by linarith), zero_mul, zero_smul]
  · simp

/-- **Beyond the neck and the collar the perturbation is the pair-of-pants datum of `H`.** At a
point `w` of the end `r` whose signed longitudinal coordinate is at least `2` and at least
`L_r + 1`, the perturbation is the pair-of-pants perturbation of the outer Hamiltonians `H`. -/
theorem pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le {r : Puncture}
    {w : ℂ} (hw : 2 ≤ r.endSign * (r.endCoord w).re)
    (hwL : L r + 1 ≤ r.endSign * (r.endCoord w).re) (x : M) :
    pairOfPantsContinuationPerturbation G H L w x = pairOfPantsPerturbation H w x := by
  rw [pairOfPantsContinuationPerturbation_eq_smul_endAngularForm hw hwL,
    pairOfPantsPerturbation_eq_smul_endAngularForm hw]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace F]
  {I : ModelWithCorners ℝ E F} [TopologicalSpace M] [ChartedSpace F M]

/-- **The perturbation is smooth.** For inner and outer Hamiltonians of period one which are `C^n`
on `ℝ × M`, the perturbation is `C^n` on `S × M`, where `S = ℂ ∖ {0, 1}` is the thrice-punctured
sphere, for all neck positions. -/
theorem contMDiffAt_pairOfPantsContinuationPerturbation {n : ℕ∞}
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q)))
    (L : Puncture → ℝ) (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => pairOfPantsContinuationPerturbation G H L p.1 p.2) ((w : ℂ), x) := by
  simp only [pairOfPantsContinuationPerturbation, continuationHomotopy_def]
  refine contMDiffAt_finsetSum fun q _ => ?_
  have hw : (w : ℂ) ≠ q.endCenter := ne_endCenter w.2 q
  have hf : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => q.endAngularForm p.1) ((w : ℂ), x) :=
    ContMDiffAt.comp (I' := 𝓘(ℝ, ℂ)) (g := q.endAngularForm) _
      (q.contDiffAt_endAngularForm hw).contMDiffAt contMDiffAt_fst
  have hGq := q.contMDiffAt_comp_im_endCoord (hG q) (hGs q) hw x
  have hHq := q.contMDiffAt_comp_im_endCoord (hH q) (hHs q) hw x
  exact ((contMDiffAt_smoothTransition_endCoord q 1 hw x).smul (hGq.add
    ((contMDiffAt_smoothTransition_endCoord q (L q) hw x).smul (hHq.sub hGq)))).smul hf

/-- The perturbation is `Cⁿ` jointly in the domain point of `S` and the target point, for
`Cⁿ` inner and outer Hamiltonians. -/
theorem contDiffAt_pairOfPantsContinuationPerturbation_prod {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {G H : Puncture → ℝ → V → ℝ} {n : ℕ∞} (hG : ∀ q, Periodic (G q) 1)
    (hH : ∀ q, Periodic (H q) 1) (hGs : ∀ q, ContDiff ℝ n (uncurry (G q)))
    (hHs : ∀ q, ContDiff ℝ n (uncurry (H q))) (L : Puncture → ℝ) {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1)
    (x : V) :
    ContDiffAt ℝ n (fun p : ℂ × V => pairOfPantsContinuationPerturbation G H L p.1 p.2) (w, x) :=
  (contMDiffAt_prod_modelWithCornersSelf_iff.1
    (contMDiffAt_pairOfPantsContinuationPerturbation hG hH
      (fun q => contMDiff_prod_modelWithCornersSelf_iff.2 (hGs q).contMDiff)
      (fun q => contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) L ⟨w, hw⟩
      x)).contDiffAt

section RealCoordinates

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {G H : Puncture → ℝ → V → ℝ}

/-- In the real coordinates of `S`, the components of the perturbation are `Cⁿ` jointly in the
domain and target points, for `Cⁿ` inner and outer Hamiltonians. -/
theorem contDiffAt_uncurry_pairOfPantsContinuationPerturbation {n : ℕ∞}
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ n (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ n (uncurry (H q)))
    (L : Puncture → ℝ) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal) (x : V) (v : ℂ) :
    ContDiffAt ℝ n
      (uncurry fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x v)
      (z, x) :=
  ((contDiffAt_pairOfPantsContinuationPerturbation_prod hG hH hGs hHs L hz x).comp
    (f := fun p : (ℝ × ℝ) × V ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).clm_apply contDiffAt_const

end RealCoordinates

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {G H : Puncture → ℝ → V → ℝ}
  {L : Puncture → ℝ}

variable [FiniteDimensional ℝ V]

/-- **The curvature in the coordinates of an end.** On the end `q`, where `σ = ±s > 0`, the
pulled-back perturbation is `β(σ - 1) C_q(σ - L_q, t) dt`, and its curvature is
`±(β'(σ - 1) C_q(σ - L_q, t) + β(σ - 1) β'(σ - L_q) (H_q - G_q)(t))`. -/
private theorem hamiltonianCurvature_perturbationPullback_endChart (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {q : Puncture} {z : ℝ × ℝ} (hz : 0 < q.endSign * z.1) (x : V) :
    ω.hamiltonianCurvature
        (perturbationPullback (endChart q)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineReal)
        (perturbationPullback (endChart q)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
          stdComplexLineImag) z x =
      q.endSign * (deriv smoothTransition (q.endSign * z.1 - 1) *
          continuationHomotopy (G q) (H q) (q.endSign * z.1 - L q, z.2) x +
        smoothTransition (q.endSign * z.1 - 1) * deriv smoothTransition (q.endSign * z.1 - L q) *
          (H q z.2 x - G q z.2 x)) := by
  have hU : IsOpen {w : ℝ × ℝ | 0 < q.endSign * w.1} :=
    isOpen_lt continuous_const (continuous_const.mul continuous_fst)
  -- Near `z` the pulled-back datum is `β(σ - 1) C_q(σ - L_q, t) dt`.
  have hs : perturbationPullback (endChart q)
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineReal =ᶠ[𝓝 z] fun _ _ ↦ 0 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [perturbationPullback_endChart_eq_cylindricalEndLift,
      equivRealProdCLM_symm_stdComplexLineReal]
    funext y
    beta_reduce
    rw [pairOfPantsContinuationPerturbation_cylindricalEndLift_of_pos (hG q) (hH q)
      (z := Complex.equivRealProdCLM.symm w) (by simpa using hw)]
    simp
  have ht : perturbationPullback (endChart q)
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineImag =ᶠ[𝓝 z] fun w y ↦ smoothTransition (q.endSign * w.1 - 1) *
        continuationHomotopy (G q) (H q) (q.endSign * w.1 - L q, w.2) y := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [perturbationPullback_endChart_eq_cylindricalEndLift,
      equivRealProdCLM_symm_stdComplexLineImag]
    funext y
    beta_reduce
    rw [pairOfPantsContinuationPerturbation_cylindricalEndLift_of_pos (hG q) (hH q)
      (z := Complex.equivRealProdCLM.symm w) (by simpa using hw)]
    simp
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht, hamiltonianCurvature_zero_left,
    stdComplexLineReal_eq]
  set F : ℝ × ℝ → ℝ := fun w ↦ smoothTransition (q.endSign * w.1 - 1) *
    continuationHomotopy (G q) (H q) (q.endSign * w.1 - L q, w.2) x with hF
  -- The `s`-derivative of the datum, computed along the line through `z`.
  have hβ : Differentiable ℝ smoothTransition :=
    (smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
  have hb (c : ℝ) : DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ smoothTransition (q.endSign * w.1 - c)) z :=
    (hβ _).comp z ((differentiableAt_fst.const_mul _).sub_const c)
  have hK (K : ℝ → V → ℝ) (hK : ContDiff ℝ 1 (uncurry K)) :
      DifferentiableAt ℝ (fun w : ℝ × ℝ ↦ K w.2 x) z :=
    DifferentiableAt.comp (g := uncurry K) (f := fun w : ℝ × ℝ ↦ (w.2, x)) z
      (hK.differentiable one_ne_zero (z.2, x))
      (differentiableAt_snd.prodMk (differentiableAt_const x))
  have hFd : DifferentiableAt ℝ F z := by
    simp only [hF, continuationHomotopy_def]
    exact (hb 1).mul ((hK _ (hGs q)).add ((hb (L q)).mul ((hK _ (hHs q)).sub (hK _ (hGs q)))))
  have hline : HasDerivAt (fun s ↦ F (s, z.2)) (fderiv ℝ F z (1, 0)) z.1 :=
    hFd.hasFDerivAt.comp_hasDerivAt (x := z.1) (f := fun s ↦ (s, z.2))
      (HasDerivAt.prodMk (hasDerivAt_id' z.1) (hasDerivAt_const z.1 z.2))
  have hβc (c : ℝ) : HasDerivAt (fun s ↦ smoothTransition (q.endSign * s - c))
      (deriv smoothTransition (q.endSign * z.1 - c) * q.endSign) z.1 :=
    (((hasDerivAt_id z.1).const_mul q.endSign).sub_const c).smoothTransition.congr_deriv
      (by simp)
  have hs' := (hβc 1).mul ((hasDerivAt_const z.1 (G q z.2 x)).add
    ((hβc (L q)).mul_const (H q z.2 x - G q z.2 x)))
  refine hline.unique ?_
  convert hs' using 1
  · funext s
    simp [hF, continuationHomotopy_def]
  · simp only [continuationHomotopy_def, Pi.add_apply]
    ring

/-- The curvature of the perturbation over the image of the strip of the end `q` is at most
`B_q + D_q`, for a common bound `B_q` of `G_q` and `H_q` and a bound `D_q` of `H_q - G_q`,
independently of the neck position `L_q`. -/
private theorem setLIntegral_image_endChart_le (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (u : ℝ × ℝ → V) (q : Puncture) :
    ∫⁻ z in endChart q '' endStrip q, ‖ω.hamiltonianCurvature
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B q) + ENNReal.ofReal (D q) := by
  have hψ : ∀ s, 0 ≤ deriv smoothTransition s := fun _ ↦ smoothTransition.monotone.deriv_nonneg
  set f : ℝ → ENNReal := fun s ↦
    ENNReal.ofReal (deriv smoothTransition (q.endSign * s - 1)) * ENNReal.ofReal (B q) +
      ENNReal.ofReal (deriv smoothTransition (q.endSign * s - L q)) * ENNReal.ofReal (D q) with hf
  have hfm : Measurable f := by
    have hc (c : ℝ) : Measurable fun s : ℝ ↦
        ENNReal.ofReal (deriv smoothTransition (q.endSign * s - c)) :=
      (ENNReal.continuous_ofReal.comp
        (((smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl).comp
          (by fun_prop))).measurable
    exact ((hc 1).mul_const _).add ((hc (L q)).mul_const _)
  -- The perturbation is differentiable jointly in the domain and target points, at points of `S`.
  have hJ {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : V) : DifferentiableAt ℝ
      (fun p : ℂ × V ↦ pairOfPantsContinuationPerturbation G H L p.1 p.2) (w, x) :=
    (contDiffAt_pairOfPantsContinuationPerturbation_prod hG hH hGs hHs L hw
      x).differentiableAt one_ne_zero
  have h := ω.constSmooth.setLIntegral_image_endChart_enorm_hamiltonianCurvature_le_lintegral
    (fun w hw x v ↦ ((hJ hw x).comp (f := fun w' : ℂ ↦ (w', x)) w
      (differentiableAt_id.prodMk (differentiableAt_const x))).clm_apply
        (differentiableAt_const v))
    (fun w hw x v ↦ (((hJ hw x).comp (f := fun y : V ↦ (w, y)) x
      ((differentiableAt_const w).prodMk differentiableAt_id)).clm_apply
        (differentiableAt_const v)).mdifferentiableAt) hfm
    (K := pairOfPantsContinuationPerturbation G H L) (f := f) (u := u) (q := q) ?_
  · simp only [hamiltonianCurvature_constSmooth] at h
    refine h.trans_eq ?_
    have hc (c : ℝ) :
        ∫⁻ s, ENNReal.ofReal (deriv smoothTransition (q.endSign * s - c)) = 1 := by
      rw [smoothTransition.lintegral_ofReal_deriv_mul_sub c q.endSign_ne_zero, abs_endSign,
        inv_one, ENNReal.ofReal_one]
    rw [hf, lintegral_add_left (by fun_prop), lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hc, hc, one_mul, one_mul]
  · intro z hz x
    -- In the coordinates of the end the curvature is
    -- `±(β'(σ - 1) C_q + β(σ - 1) β'(σ - L_q) (H_q - G_q))`.
    rw [hamiltonianCurvature_constSmooth, hamiltonianCurvature_perturbationPullback_endChart ω hG
      hH hGs hHs (endSign_mul_pos_of_mem_endStrip hz), Real.enorm_eq_ofReal_abs, abs_mul,
      abs_endSign, one_mul]
    simp only [hf]
    rw [← ENNReal.ofReal_mul (hψ _), ← ENNReal.ofReal_mul (hψ _),
      ← ENNReal.ofReal_add (mul_nonneg (hψ _) ((abs_nonneg _).trans (hGB q 0 0)))
        (mul_nonneg (hψ _) ((abs_nonneg _).trans (hD q 0 0)))]
    refine ENNReal.ofReal_le_ofReal ((abs_add_le _ _).trans (add_le_add ?_ ?_))
    · rw [abs_mul, abs_of_nonneg (hψ _)]
      exact mul_le_mul_of_nonneg_left
        (abs_continuationHomotopy_le (hGB q _ _) (hHB q _ _)) (hψ _)
    · rw [abs_mul, abs_mul, abs_of_nonneg (smoothTransition.nonneg _), abs_of_nonneg (hψ _)]
      calc _ ≤ 1 * deriv smoothTransition (q.endSign * z.1 - L q) * D q := by
            exact mul_le_mul (mul_le_mul_of_nonneg_right (smoothTransition.le_one _) (hψ _))
              (hD q _ _) (abs_nonneg _) (mul_nonneg zero_le_one (hψ _))
        _ = _ := by rw [one_mul]

/-- **The integrated curvature of the pair-of-pants perturbation with continuation necks.** Let
`K` be the perturbation with period-one `C¹` inner and outer Hamiltonians `G_q` and `H_q` on the
three ends of `S = ℂ ∖ {0, 1}`, with `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, and write its
components in the global coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and
`K_t(z) = K(z)(i)`. Then for every map `u` into the target and all neck positions `L_q`, the
integral of `|R_K(z, u(z))|` over the plane is at most `∑ q, (B_q + D_q)`. -/
theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (L : Puncture → ℝ) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, (ENNReal.ofReal (B q) + ENNReal.ofReal (D q)) := by
  have h := ω.constSmooth.lintegral_enorm_hamiltonianCurvature_le_sum_endStrip
    (K := pairOfPantsContinuationPerturbation G H L)
    (fun w hw y ↦ pairOfPantsContinuationPerturbation_eq_zero_of_forall_le hw y) u
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h.trans
    (Finset.sum_le_sum fun q _ ↦ setLIntegral_image_endChart_le ω hG hH hGs hHs hGB hHB hD u q)

/-- The integral of the curvature of the pair-of-pants perturbation with continuation necks along
any map, over any set, has absolute value at most `∑ q, (B_q + D_q)` when `|G_q|, |H_q| ≤ B_q`
and `|H_q - G_q| ≤ D_q`, for all neck positions. -/
theorem abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (L : Puncture → ℝ) (u : ℝ × ℝ → V)
    (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ q, (B q + D q) := by
  have hB₀ (q : Puncture) : 0 ≤ B q := (abs_nonneg _).trans (hGB q 0 0)
  have hD₀ (q : Puncture) : 0 ≤ D q := (abs_nonneg _).trans (hD q 0 0)
  have hsum : ∑ q, (ENNReal.ofReal (B q) + ENNReal.ofReal (D q)) =
      ENNReal.ofReal (∑ q, (B q + D q)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun q _ => add_nonneg (hB₀ q) (hD₀ q)]
    exact Finset.sum_congr rfl fun q _ => (ENNReal.ofReal_add (hB₀ q) (hD₀ q)).symm
  rw [← ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q _ => add_nonneg (hB₀ q) (hD₀ q)),
    ← Real.enorm_eq_ofReal_abs, ← hsum]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs hHs
      hGB hHB hD L u))

end SymplecticForm

end TauCeti
