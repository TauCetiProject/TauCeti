/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Analysis.Complex.ThricePuncturedSphere.Exchange

/-!
# Perturbation data with movable input ends

The pair-of-pants datum `TauCeti.Floer.pairOfPantsPerturbation` lives on the sphere with the three
fixed punctures `0`, `1` and `∞`. Comparing the two ways of composing two pair-of-pants products,
`(a ⋆ b) ⋆ c` and `a ⋆ (b ⋆ c)`, needs a one-parameter family of four-punctured spheres whose
modulus moves from one broken configuration to the other, so the input punctures must move.
This file constructs Hamiltonian perturbation data on spheres whose input ends have arbitrary
centres and scales.

An input end with centre `c ∈ ℂ` and scale `b ≠ 0` has the end lift `z ↦ c + b exp (-2πz)` on
the half-plane `Re z > 0`; the ends of the pair of pants at `0` and `1` are the cases
`(c, b) = (0, 1/2)` and `(1, -1/2)`. Its datum `TauCeti.Floer.inputEndPerturbation H c b` is the
positive plane datum `TauCeti.Floer.positivePlanePerturbation H` transported along the affine map
`w ↦ c + 2b w`, which carries the end lift `z ↦ exp (-2πz) / 2` of the positive plane to that of
the end. A sphere with finitely many input ends `(cᵢ, bᵢ)` and the standard output end at `∞` with
Hamiltonian `H₀` carries the sum of their data and the negative plane datum of `H₀`,
`TauCeti.Floer.inputEndsPerturbation H H₀ c b`. The results are:

* `TauCeti.Floer.inputEndPerturbation_endLift_of_pos`: the datum of an input end pulls back along
  its end lift to the continuation datum `β(s - 1) H(t) dt`, hence to `H(t) dt` for `s ≥ 2`
  (`TauCeti.Floer.inputEndPerturbation_endLift`).
* `TauCeti.Floer.inputEndPerturbation_eq_zero_of_notMem_inputEndDisc`: it vanishes off the closed
  disc `TauCeti.Floer.inputEndDisc c b` of radius `‖b‖ exp (-2π)` about `c`.
* `TauCeti.Floer.pairOfPantsPerturbation_eq_inputEndsPerturbation`: the pair-of-pants datum is the
  datum of the input ends `(0, 1/2)` and `(1, -1/2)` with the standard output end.
* `TauCeti.Floer.contMDiffAt_inputEndsPerturbation`: the datum is smooth jointly in the centres,
  the scales, the domain point off the centres, and the target point, so a smooth path of
  configurations gives a smooth family of data.
* `TauCeti.Floer.inputEndsPerturbation_endLift_of_one_le` and
  `TauCeti.Floer.inputEndsPerturbation_cylindricalEndLift_inf_of_le_neg_one`: if the input ends
  are separated (`TauCeti.Floer.SeparatedInputEnds`), that is their discs are pairwise disjoint
  and lie inside the pole disc `‖w‖ < 2 exp (2π)` of the output end, every end carries its own
  continuation datum; the input ends of the pair of pants are separated
  (`TauCeti.Floer.separatedInputEnds_pairOfPants`).
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_inputEndsPerturbation_le`: under the
  same separation, for a target manifold with a two-form and `|Hᵢ| ≤ Bᵢ`, `|H₀| ≤ B₀`, the
  integrated curvature `∫ |R_K(u)|` along any map `u` is at most `∑ Bᵢ + B₀`, whatever the centres
  and scales. This is the curvature allowance entering the energy identity, uniformly along any
  path of separated configurations.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product via families of
  four-punctured spheres.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on
  perturbation data over families of punctured spheres with moving ends.
-/

public noncomputable section

open Set Real Manifold Topology Function Metric
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {H : ℝ → M → ℝ}

/-! ### One input end -/

/-- **The datum of an input end with centre `c` and scale `b`.** It is the positive plane datum of
`H` transported along the affine map `w ↦ c + 2b w`: at `w` it is the positive plane datum at
`(w - c) / (2b)`, evaluated on the tangent vector `v / (2b)`. Its end lift is
`z ↦ c + b exp (-2πz)`, on which it is `β(s - 1) H(t) dt`. -/
def inputEndPerturbation (H : ℝ → M → ℝ) (c b w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  (positivePlanePerturbation H ((w - c) / (2 * b)) x).comp
    (ContinuousLinearMap.mul ℝ ℂ (2 * b)⁻¹)

theorem inputEndPerturbation_apply (H : ℝ → M → ℝ) (c b w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation H c b w x v =
      positivePlanePerturbation H ((w - c) / (2 * b)) x ((2 * b)⁻¹ * v) :=
  (rfl)

/-- **Transport to the positive plane.** Along the affine map `w ↦ c + 2b w`, the datum of the
input end is the positive plane datum. -/
theorem inputEndPerturbation_add_mul {b : ℂ} (hb : b ≠ 0) (c w : ℂ) (x : M) (v : ℂ) :
    inputEndPerturbation H c b (c + 2 * b * w) x (2 * b * v) =
      positivePlanePerturbation H w x v := by
  have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hb
  rw [inputEndPerturbation_apply, add_sub_cancel_left, mul_div_cancel_left₀ _ h2b,
    inv_mul_cancel_left₀ h2b]

/-- The input end with centre `0` and scale `1/2` is the positive plane. -/
theorem inputEndPerturbation_zero_one_half (H : ℝ → M → ℝ) :
    inputEndPerturbation H 0 (1 / 2) = positivePlanePerturbation H := by
  funext w x
  ext v
  simp [inputEndPerturbation_apply]

/-- The input end with centre `1` and scale `-1/2` is the input end at `1` of the pair of
pants. -/
theorem inputEndPerturbation_one_neg_one_half (H : ℝ → M → ℝ) :
    inputEndPerturbation H 1 (-(1 / 2)) = pairOfPantsPerturbation (Pi.single one H) := by
  funext w x
  ext v
  rw [pairOfPantsPerturbation_def, Fintype.sum_eq_single one fun q hq => by
    simp [Pi.single_eq_of_ne hq]]
  have hw : (w - 1) / (2 * -(1 / 2)) = 1 - w := by ring
  have hv : (2 * -(1 / 2 : ℂ))⁻¹ * v = -v := by ring
  rw [inputEndPerturbation_apply, hw, hv, positivePlanePerturbation_def, endCoord_zero_one_sub,
    endAngularForm_zero_one_sub]
  simp only [Pi.single_eq_same, endSign_one, one_mul, smul_apply, neg_apply, map_neg, smul_eq_mul,
    mul_neg, neg_neg]

/-- **The datum on the end.** On the half-plane `Re z > 0`, the pullback of the datum of the input
end along its end lift `φ(z) = c + b exp (-2πz)`, whose derivative is
`φ'(z) = -2π b exp (-2πz)`, is the continuation datum `β(s - 1) H(t) dt`: it sends a tangent
vector `v` of the cylinder to `Im v · β(Re z - 1) H(Im z)`. -/
theorem inputEndPerturbation_endLift_of_pos (hH : Periodic H 1) {b : ℂ} (hb : b ≠ 0) (c : ℂ)
    {z : ℂ} (hz : 0 < z.re) (x : M) (v : ℂ) :
    inputEndPerturbation H c b (c + b * Complex.exp (-(2 * (π : ℂ)) * z)) x
        (-(2 * π * b * Complex.exp (-(2 * (π : ℂ)) * z)) * v) =
      v.im * (smoothTransition (z.re - 1) * H z.im x) := by
  have hw : c + b * Complex.exp (-(2 * (π : ℂ)) * z) = c + 2 * b * zero.cylindricalEndLift z := by
    simp only [cylindricalEndLift_zero]
    ring
  have hv : -(2 * π * b * Complex.exp (-(2 * (π : ℂ)) * z)) * v =
      2 * b * (deriv zero.cylindricalEndLift z * v) := by
    rw [deriv_cylindricalEndLift, endCenter_zero, sub_zero, cylindricalEndLift_zero]
    ring
  rw [hw, hv, inputEndPerturbation_add_mul hb,
    positivePlanePerturbation_cylindricalEndLift_of_pos hH hz]

/-- **The datum is `H(t) dt` far out on the end.** On the half-plane `Re z ≥ 2`, the pullback of
the datum of the input end along its end lift sends a tangent vector `v` of the cylinder to
`Im v · H(Im z)`. -/
theorem inputEndPerturbation_endLift (hH : Periodic H 1) {b : ℂ} (hb : b ≠ 0) (c : ℂ) {z : ℂ}
    (hz : 2 ≤ z.re) (x : M) (v : ℂ) :
    inputEndPerturbation H c b (c + b * Complex.exp (-(2 * (π : ℂ)) * z)) x
        (-(2 * π * b * Complex.exp (-(2 * (π : ℂ)) * z)) * v) =
      v.im * H z.im x := by
  rw [inputEndPerturbation_endLift_of_pos hH hb c (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-- The closed disc of radius `‖b‖ exp (-2π)` about `c`, off which the datum of the input end with
centre `c` and scale `b` vanishes. It is the image under `w ↦ c + 2b w` of the closed disc of
radius `exp (-2π) / 2` about `0`, off which the positive plane datum vanishes. -/
def inputEndDisc (c b : ℂ) : Set ℂ :=
  closedBall c (‖b‖ * Real.exp (-(2 * π)))

theorem mem_inputEndDisc {c b w : ℂ} :
    w ∈ inputEndDisc c b ↔ ‖w - c‖ ≤ ‖b‖ * Real.exp (-(2 * π)) := by
  rw [inputEndDisc, mem_closedBall, dist_eq_norm]

theorem isClosed_inputEndDisc (c b : ℂ) : IsClosed (inputEndDisc c b) :=
  isClosed_closedBall

/-- The centre of an input end lies in its disc. -/
theorem mem_inputEndDisc_self (c b : ℂ) : c ∈ inputEndDisc c b :=
  mem_closedBall_self (by positivity)

/-- **The support of the datum.** The datum of the input end vanishes off its disc. -/
theorem inputEndPerturbation_eq_zero_of_notMem_inputEndDisc {b : ℂ} (hb : b ≠ 0) {c w : ℂ}
    (hw : w ∉ inputEndDisc c b) (x : M) : inputEndPerturbation H c b w x = 0 := by
  have hw' : Real.exp (-(2 * π)) / 2 ≤ ‖(w - c) / (2 * b)‖ := by
    rw [mem_inputEndDisc, not_le] at hw
    rw [norm_div, norm_mul, Complex.norm_ofNat, le_div_iff₀ (by positivity)]
    nlinarith [norm_pos_iff.2 hb]
  ext v
  simp [inputEndPerturbation_apply, positivePlanePerturbation_eq_zero_of_le_norm hw']

/-- Near a point off its disc, the datum of the input end vanishes. -/
theorem eventually_inputEndPerturbation_eq_zero {b : ℂ} (hb : b ≠ 0) {c w : ℂ}
    (hw : w ∉ inputEndDisc c b) : ∀ᶠ w' in 𝓝 w, inputEndPerturbation H c b w' = fun _ ↦ 0 := by
  filter_upwards [(isClosed_inputEndDisc c b).isOpen_compl.mem_nhds hw] with w' hw'
  exact funext (inputEndPerturbation_eq_zero_of_notMem_inputEndDisc hb hw')

section Smooth

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The datum is smooth in the centre, the scale, the domain point and the target point.** For a
period-one Hamiltonian which is `C^n` on `ℝ × M`, the datum of the input end is `C^n` jointly in
`(c, b, w, x)` at every point with `b ≠ 0` and `w ≠ c`. -/
theorem contMDiffAt_inputEndPerturbation {n : ℕ∞} (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H)) {c b w : ℂ} (hb : b ≠ 0)
    (hw : w ≠ c) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => inputEndPerturbation H p.1.1 p.1.2 p.2.1 p.2.2)
      ((c, b), (w, x)) := by
  have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hb
  have hscale : ContDiffAt ℝ n (fun p : (ℂ × ℂ) × ℂ => (2 * p.1.2)⁻¹) ((c, b), w) :=
    (contDiffAt_const.mul (contDiffAt_snd.comp _ contDiffAt_fst)).inv h2b
  have hcoord : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => (p.2.1 - p.1.1) / (2 * p.1.2)) ((c, b), (w, x)) := by
    have h : ContDiffAt ℝ n (fun p : (ℂ × ℂ) × ℂ => (p.2 - p.1.1) * (2 * p.1.2)⁻¹)
        ((c, b), w) :=
      (contDiffAt_snd.sub (contDiffAt_fst.comp _ contDiffAt_fst)).mul hscale
    simp only [div_eq_mul_inv]
    exact h.contMDiffAt.comp (f := fun p : (ℂ × ℂ) × (ℂ × M) => (p.1, p.2.1)) ((c, b), (w, x))
      (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd))
  have hmul : ContMDiffAt (𝓘(ℝ, ℂ × ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
      (fun p : (ℂ × ℂ) × (ℂ × M) => ContinuousLinearMap.mul ℝ ℂ (2 * p.1.2)⁻¹)
      ((c, b), (w, x)) :=
    (((ContinuousLinearMap.mul ℝ ℂ).contDiff.contDiffAt.comp _ hscale).contMDiffAt).comp
      (f := fun p : (ℂ × ℂ) × (ℂ × M) => (p.1, p.2.1)) ((c, b), (w, x))
      (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd))
  have hne : (w - c) / (2 * b) ≠ 0 := div_ne_zero (sub_ne_zero.2 hw) h2b
  exact ((contMDiffAt_positivePlanePerturbation hH hHs hne x).comp ((c, b), (w, x))
    (hcoord.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).clm_comp hmul

end Smooth

/-! ### Several input ends -/

section Several

variable {ι : Type*} [Fintype ι] {Hs : ι → ℝ → M → ℝ} {H₀ : ℝ → M → ℝ} {c b : ι → ℂ}

/-- **The datum of a sphere with movable input ends.** The sum of the data of the input ends with
centres `cᵢ`, scales `bᵢ` and Hamiltonians `Hᵢ`, and of the negative plane datum of `H₀` on the
standard output end at `∞`, with end lift `z ↦ 2 exp (-2πz)`. -/
def inputEndsPerturbation (Hs : ι → ℝ → M → ℝ) (H₀ : ℝ → M → ℝ) (c b : ι → ℂ) (w : ℂ) (x : M) :
    ℂ →L[ℝ] ℝ :=
  ∑ i, inputEndPerturbation (Hs i) (c i) (b i) w x + negativePlanePerturbation H₀ w x

theorem inputEndsPerturbation_def (Hs : ι → ℝ → M → ℝ) (H₀ : ℝ → M → ℝ) (c b : ι → ℂ) (w : ℂ)
    (x : M) :
    inputEndsPerturbation Hs H₀ c b w x =
      ∑ i, inputEndPerturbation (Hs i) (c i) (b i) w x + negativePlanePerturbation H₀ w x :=
  (rfl)

/-- **The pair of pants has input ends `(0, 1/2)` and `(1, -1/2)`.** -/
theorem pairOfPantsPerturbation_eq_inputEndsPerturbation (H : Puncture → ℝ → M → ℝ) :
    pairOfPantsPerturbation H =
      inputEndsPerturbation ![H zero, H one] (H inf) ![0, 1] ![1 / 2, -(1 / 2)] := by
  funext w x
  rw [inputEndsPerturbation_def, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inputEndPerturbation_zero_one_half,
    inputEndPerturbation_one_neg_one_half]
  simp [pairOfPantsPerturbation_def, positivePlanePerturbation_def, negativePlanePerturbation_def,
    Puncture.sum_univ, add_assoc]

/-- **Separated input ends.** The input ends with centres `cᵢ` and scales `bᵢ` are separated if
the scales are nonzero, the discs `TauCeti.Floer.inputEndDisc (cᵢ) (bᵢ)` off which their data
vanish are pairwise disjoint, and they lie in the open pole disc `‖w‖ < 2 exp (2π)` on which the
datum of the output end at `∞` vanishes. Then near every point at most one of the end data is
nonzero. -/
structure SeparatedInputEnds (c b : ι → ℂ) : Prop where
  ne_zero : ∀ i, b i ≠ 0
  disjoint : Pairwise fun i j => Disjoint (inputEndDisc (c i) (b i)) (inputEndDisc (c j) (b j))
  subset_ball : ∀ i, inputEndDisc (c i) (b i) ⊆ ball 0 (2 * Real.exp (2 * π))

/-- The input ends `(0, 1/2)` and `(1, -1/2)` of the pair of pants are separated. -/
theorem separatedInputEnds_pairOfPants :
    SeparatedInputEnds (ι := Fin 2) ![0, 1] ![1 / 2, -(1 / 2)] := by
  have he : Real.exp (-(2 * π)) < 1 := Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos])
  have he' : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  have hdisc (i : Fin 2) : inputEndDisc (![0, 1] i) (![1 / 2, -(1 / 2)] i) =
      closedBall (![0, 1] i) (Real.exp (-(2 * π)) / 2) := by
    fin_cases i <;> simp [inputEndDisc] <;> ring_nf
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_, fun i => ?_⟩
  · intro i j hij
    rw [hdisc, hdisc]
    refine closedBall_disjoint_closedBall (α := ℂ) ?_
    fin_cases i <;> fin_cases j <;> simp_all [dist_eq_norm]
  · rw [hdisc]
    refine closedBall_subset_ball' ?_
    fin_cases i <;> simp [dist_eq_norm] <;> linarith

/-- Near a point of the disc of the input end `i`, the datum of separated input ends is the datum
of that end alone. -/
theorem eventually_inputEndsPerturbation_eq_of_mem (hs : SeparatedInputEnds c b) {i : ι}
    {w : ℂ} (hw : w ∈ inputEndDisc (c i) (b i)) :
    ∀ᶠ w' in 𝓝 w, inputEndsPerturbation Hs H₀ c b w' =
      inputEndPerturbation (Hs i) (c i) (b i) w' := by
  have hj : ∀ᶠ w' in 𝓝 w, ∀ j, j ≠ i → inputEndPerturbation (Hs j) (c j) (b j) w' =
      fun _ ↦ 0 := by
    refine Filter.eventually_all.2 fun j => ?_
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ h => absurd hji h
    · filter_upwards [eventually_inputEndPerturbation_eq_zero (H := Hs j) (hs.ne_zero j)
        fun h => (hs.disjoint hji).ne_of_mem h hw rfl] with w' hw' _ using hw'
  have hball : ‖w‖ < 2 * Real.exp (2 * π) := by
    simpa using hs.subset_ball i hw
  filter_upwards [hj, continuous_norm.continuousAt.eventually (gt_mem_nhds hball)]
    with w' hw' hn'
  funext x
  rw [inputEndsPerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hn'.le, add_zero,
    Finset.sum_eq_single i (fun j _ hji => by rw [hw' j hji]) (by simp)]

/-- Near a point off the discs of all input ends, the datum of the input ends is the datum of the
output end. -/
theorem eventually_inputEndsPerturbation_eq_of_forall_notMem (hb : ∀ i, b i ≠ 0) {w : ℂ}
    (hw : ∀ i, w ∉ inputEndDisc (c i) (b i)) :
    ∀ᶠ w' in 𝓝 w, inputEndsPerturbation Hs H₀ c b w' = negativePlanePerturbation H₀ w' := by
  filter_upwards [Filter.eventually_all.2 fun i =>
    eventually_inputEndPerturbation_eq_zero (H := Hs i) (hb i) (hw i)] with w' hw'
  funext x
  simp [inputEndsPerturbation_def, hw']

/-- **The datum on an input end.** For separated input ends, on the part `Re z ≥ 1` of the end
`i`, the pullback of the datum along the end lift `φ(z) = cᵢ + bᵢ exp (-2πz)` is the continuation
datum `β(s - 1) Hᵢ(t) dt`. -/
theorem inputEndsPerturbation_endLift_of_one_le (hH : ∀ i, Periodic (Hs i) 1)
    (hs : SeparatedInputEnds c b) (i : ι) {z : ℂ} (hz : 1 ≤ z.re) (x : M) (v : ℂ) :
    inputEndsPerturbation Hs H₀ c b (c i + b i * Complex.exp (-(2 * (π : ℂ)) * z)) x
        (-(2 * π * b i * Complex.exp (-(2 * (π : ℂ)) * z)) * v) =
      v.im * (smoothTransition (z.re - 1) * Hs i z.im x) := by
  have hmem : c i + b i * Complex.exp (-(2 * (π : ℂ)) * z) ∈ inputEndDisc (c i) (b i) := by
    rw [mem_inputEndDisc, add_sub_cancel_left, norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h : (-(2 * (π : ℂ)) * z).re = -(2 * π * z.re) := by simp
    rw [h]
    nlinarith [Real.pi_pos]
  rw [(eventually_inputEndsPerturbation_eq_of_mem hs hmem).self_of_nhds,
    inputEndPerturbation_endLift_of_pos (hH i) (hs.ne_zero i) (c i) (by linarith)]

/-- **The datum on the output end.** For separated input ends, on the part `Re z ≤ -1` of the end
at `∞`, the pullback of the datum along the end lift `φ(z) = 2 exp (-2πz)` is the continuation
datum `β(-s - 1) H₀(t) dt`. -/
theorem inputEndsPerturbation_cylindricalEndLift_inf_of_le_neg_one (hH₀ : Periodic H₀ 1)
    (hs : SeparatedInputEnds c b) {z : ℂ} (hz : z.re ≤ -1) (x : M) (v : ℂ) :
    inputEndsPerturbation Hs H₀ c b (inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * H₀ z.im x) := by
  have hnorm : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ := by
    rw [cylindricalEndLift_inf, norm_mul, Complex.norm_exp, Complex.norm_ofNat]
    have h : (-(2 * (π : ℂ)) * z).re = -(2 * π * z.re) := by simp
    rw [h]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos]))
      zero_le_two
  have hout : ∀ i, inf.cylindricalEndLift z ∉ inputEndDisc (c i) (b i) := fun i h => by
    have := hs.subset_ball i h
    rw [mem_ball_zero_iff] at this
    linarith
  rw [(eventually_inputEndsPerturbation_eq_of_forall_notMem hs.ne_zero hout).self_of_nhds,
    negativePlanePerturbation_cylindricalEndLift_of_neg hH₀ (by linarith)]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The datum is smooth in the configuration.** For period-one Hamiltonians which are `C^n` on
`ℝ × M`, the datum of the input ends is `C^n` jointly in the centres `c`, the scales `b`, the
domain point `w` and the target point, at every configuration with nonzero scales and every `w`
other than the centres. -/
theorem contMDiffAt_inputEndsPerturbation {n : ℕ∞} (hH : ∀ i, Periodic (Hs i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hs i))) (hH₀ : Periodic H₀ 1)
    (hH₀s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry H₀)) (hb : ∀ i, b i ≠ 0) {w : ℂ}
    (hw : ∀ i, w ≠ c i) (x : M) :
    ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) =>
        inputEndsPerturbation Hs H₀ p.1.1 p.1.2 p.2.1 p.2.2) ((c, b), (w, x)) := by
  simp only [inputEndsPerturbation_def]
  refine (contMDiffAt_finsetSum fun i _ => ?_).add
    ((contMDiff_negativePlanePerturbation hH₀ hH₀s).contMDiffAt.comp _ contMDiffAt_snd)
  -- The `i`-th end only sees the `i`-th centre and scale.
  have hproj : ContMDiffAt (𝓘(ℝ, (ι → ℂ) × (ι → ℂ)).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ × ℂ) n
      (fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => (p.1.1 i, p.1.2 i)) ((c, b), (w, x)) :=
    (((by fun_prop : ContDiff ℝ n fun q : (ι → ℂ) × (ι → ℂ) => (q.1 i, q.2 i)).contMDiff
      ).contMDiffAt).comp _ contMDiffAt_fst
  exact (contMDiffAt_inputEndPerturbation (hH i) (hHs i) (hb i) (hw i) x).comp
    (f := fun p : ((ι → ℂ) × (ι → ℂ)) × (ℂ × M) => ((p.1.1 i, p.1.2 i), p.2)) ((c, b), (w, x))
    (hproj.prodMk contMDiffAt_snd)

end Several

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory TauCeti.Complex

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] {H : ℝ → M → ℝ}

/-- Off its centre, the components of the datum of an input end are differentiable in the domain
point, for a `C¹` Hamiltonian on a manifold. -/
private theorem differentiableAt_inputEndPerturbation_domain (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c b : ℂ} (hb : b ≠ 0)
    {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm z ≠ c) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' ↦ inputEndPerturbation H c b (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ inputEndPerturbation H c b w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_inputEndPerturbation (n := 1) hH hHs hb hz x).comp
      (f := fun w : ℂ ↦ ((c, b), (w, x))) _
      (contMDiffAt_const.prodMk (contMDiffAt_id.prodMk contMDiffAt_const))
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- Off its centre, the components of the datum of an input end are differentiable in the target
point, for a `C¹` Hamiltonian on a manifold. -/
private theorem mdifferentiableAt_inputEndPerturbation_target (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {c b : ℂ} (hb : b ≠ 0) {w : ℂ}
    (hw : w ≠ c) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ inputEndPerturbation H c b w y v) x :=
  (((contMDiffAt_inputEndPerturbation (n := 1) hH hHs hb hw x).comp
    (f := fun y : M ↦ ((c, b), (w, y))) x
    (contMDiffAt_const.prodMk (contMDiffAt_const.prodMk contMDiffAt_id))).clm_apply
    contMDiffAt_const).mdifferentiableAt one_ne_zero

/-- In real coordinates, the affine map `w ↦ c + a w` with `a ≠ 0` is injective. -/
private theorem injective_realChart_affine {c a : ℂ} (ha : a ≠ 0) :
    Injective (realChart fun w ↦ c + a * w) := fun z z' h => by
  have h' := congrArg Complex.equivRealProdCLM.symm h
  simp only [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, add_right_inj,
    mul_right_inj' ha] at h'
  exact Complex.equivRealProdCLM.symm.injective h'

/-- In real coordinates, the affine map `w ↦ c + a w` with `a ≠ 0` carries the plane punctured at
the origin onto the plane punctured at `c`. -/
private theorem image_realChart_affine {c a : ℂ} (ha : a ≠ 0) :
    realChart (fun w ↦ c + a * w) '' {z | Complex.equivRealProdCLM.symm z ≠ 0} =
      {z | Complex.equivRealProdCLM.symm z ≠ c} := by
  ext z
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, rfl⟩ h
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, add_eq_left] at h
    exact hw ((mul_eq_zero.1 h).resolve_left ha)
  · intro hz
    refine ⟨Complex.equivRealProdCLM ((Complex.equivRealProdCLM.symm z - c) / a), ?_, ?_⟩
    · rw [ContinuousLinearEquiv.symm_apply_apply]
      exact div_ne_zero (sub_ne_zero.2 hz) ha
    · apply Complex.equivRealProdCLM.symm.injective
      rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
        ContinuousLinearEquiv.symm_apply_apply, mul_div_cancel₀ _ ha, add_sub_cancel]

/-- In real coordinates, a point of the plane is a null set. -/
private theorem volume_setOf_equivRealProdCLM_symm_eq (c : ℂ) :
    volume {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z = c} = 0 := by
  have h : {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z = c} = {c.re} ×ˢ {c.im} := by
    ext z
    simp only [mem_ofPred_eq, Set.singleton_prod_singleton, mem_singleton_iff]
    constructor
    · rintro rfl
      simp
    · rintro rfl
      apply Complex.ext <;> simp
  rw [h, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

variable [IsManifold I ⊤ M]

/-- The integrated curvature of the pair-of-pants datum whose only nonzero Hamiltonian is `H`, on
the end `p`, is at most a bound for `H`. -/
private theorem lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_single_le
    (ω : SmoothTwoForm I M) (hH : Periodic H 1)
    (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ} (hB : ∀ t x, |H t x| ≤ B)
    (p : Puncture) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation (Pi.single p H) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation (Pi.single p H) (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  have h := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le
    (H := Pi.single p H) (B := Pi.single p B)
    (fun q => by
      rcases eq_or_ne q p with rfl | hq
      · simpa using hH
      · rw [Pi.single_eq_of_ne hq]
        exact fun _ => rfl)
    (fun q => by
      rcases eq_or_ne q p with rfl | hq
      · simpa using hHs
      · rw [Pi.single_eq_of_ne hq]
        exact contMDiff_const)
    (fun q t x => by
      rcases eq_or_ne q p with rfl | hq
      · simpa using hB t x
      · simp [Pi.single_eq_of_ne hq]) u
  rwa [Fintype.sum_eq_single p fun r hr => by simp [Pi.single_eq_of_ne hr],
    Pi.single_eq_same] at h

/-- **The integrated curvature of an input end.** Let `K` be the datum of the input end with
centre `c` and scale `b ≠ 0` of a period-one `C¹` Hamiltonian `H` with `|H| ≤ B`, on a manifold
`M` with a two-form `ω`, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global
coordinate `z = s + i t` of `ℂ`. Then for every map `u` into `M`, the integral of `|R_K(z, u(z))|`
over the plane is at most `B`, whatever the centre and the scale. -/
theorem lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le (ω : SmoothTwoForm I M)
    (hH : Periodic H 1) (hHs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H)) {B : ℝ}
    (hB : ∀ t x, |H t x| ≤ B) {b : ℂ} (hb : b ≠ 0) (c : ℂ) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation H c b (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation H c b (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal B := by
  have h2b : 2 * b ≠ 0 := mul_ne_zero two_ne_zero hb
  -- The affine change of coordinates `w ↦ c + 2b w` carries the positive plane to the end, and
  -- the punctured plane onto the plane punctured at `c`, which has full measure.
  have hf (w : ℂ) : HasDerivAt (fun w ↦ c + 2 * b * w) (2 * b) w := by
    simpa using ((hasDerivAt_id' w).const_mul (2 * b)).const_add c
  have hA := image_realChart_affine (c := c) h2b
  have hAm : MeasurableSet {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ c} :=
    (measurableSet_singleton c).compl.preimage Complex.equivRealProdCLM.symm.continuous.measurable
  have hSm : MeasurableSet {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0} :=
    (measurableSet_singleton 0).compl.preimage Complex.equivRealProdCLM.symm.continuous.measurable
  have hAc : volume {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ c}ᶜ = 0 := by
    simpa only [compl_ofPred, not_not] using volume_setOf_equivRealProdCLM_symm_eq c
  have hφS {w : ℝ × ℝ} (hw : Complex.equivRealProdCLM.symm w ≠ 0) :
      Complex.equivRealProdCLM.symm (realChart (fun w ↦ c + 2 * b * w) w) ≠ c :=
    (hA ▸ mem_image_of_mem _ hw : realChart (fun w ↦ c + 2 * b * w) w ∈ _)
  -- Along the change of coordinates, the datum pulls back to the positive plane datum.
  have hpull (v : ℂ) : perturbationPullback (realChart fun w ↦ c + 2 * b * w)
      (fun z x ↦ inputEndPerturbation H c b (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ inputEndPerturbation H c b (Complex.equivRealProdCLM.symm z) x Complex.I)
      (Complex.equivRealProdCLM v) =
      fun w x ↦ positivePlanePerturbation H (Complex.equivRealProdCLM.symm w) x v := by
    funext w x
    rw [perturbationPullback_realChart _ (hf _), ContinuousLinearEquiv.symm_apply_apply,
      inputEndPerturbation_add_mul hb]
  have h₁ : stdComplexLineReal = Complex.equivRealProdCLM 1 := by
    simp [stdComplexLineReal_eq]
  have hI : stdComplexLineImag = Complex.equivRealProdCLM Complex.I := by
    simp [stdComplexLineImag_eq]
  have hplane := lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_single_le ω hH hHs
    hB zero (u ∘ realChart fun w ↦ c + 2 * b * w)
  rw [pairOfPantsPerturbation_single_zero] at hplane
  rw [← lintegral_add_compl _ hAm, setLIntegral_measure_zero _ _ hAc, add_zero, ← hA,
    ω.lintegral_enorm_hamiltonianCurvature_image hSm (injective_realChart_affine h2b).injOn
      (fun w _ ↦ (contDiff_realChart (by fun_prop)).contDiffAt)
      (fun w hw ↦ differentiableAt_inputEndPerturbation_domain hH hHs hb (hφS hw) _ 1)
      (fun w hw ↦ differentiableAt_inputEndPerturbation_domain hH hHs hb (hφS hw) _ Complex.I)
      (fun w hw ↦ mdifferentiableAt_inputEndPerturbation_target hH hHs hb (hφS hw) _ 1)
      (fun w hw ↦ mdifferentiableAt_inputEndPerturbation_target hH hHs hb (hφS hw) _ Complex.I),
    h₁, hI, hpull, hpull]
  exact (setLIntegral_le_lintegral _ _).trans hplane

variable {ι : Type*} [Fintype ι] {Hs : ι → ℝ → M → ℝ} {H₀ : ℝ → M → ℝ} {c b : ι → ℂ}

/-- **The integrated curvature of separated input ends is bounded uniformly.** Let `K` be the
datum of separated input ends with centres `cᵢ` and scales `bᵢ`, period-one `C¹` Hamiltonians
`Hᵢ` with `|Hᵢ| ≤ Bᵢ`, and output Hamiltonian `H₀` with `|H₀| ≤ B₀`, on a manifold `M` with a
two-form `ω`. Then for every map `u` into `M`, the integral of `|R_K(z, u(z))|` over the plane is
at most `∑ Bᵢ + B₀`. The bound does not depend on the centres and scales, so it holds uniformly
along every family of separated configurations. -/
theorem lintegral_enorm_hamiltonianCurvature_inputEndsPerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ i, Periodic (Hs i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hs i))) (hH₀ : Periodic H₀ 1)
    (hH₀s : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry H₀)) {B : ι → ℝ}
    (hB : ∀ i t x, |Hs i t x| ≤ B i) {B₀ : ℝ} (hB₀ : ∀ t x, |H₀ t x| ≤ B₀)
    (hs : SeparatedInputEnds c b) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ inputEndsPerturbation Hs H₀ c b (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndsPerturbation Hs H₀ c b (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal B₀ := by
  -- Split the plane into the discs of the input ends and their complement.
  set D : ι → Set (ℝ × ℝ) := fun i => Complex.equivRealProdCLM.symm ⁻¹' inputEndDisc (c i) (b i)
  have hDm (i : ι) : MeasurableSet (D i) :=
    ((isClosed_inputEndDisc _ _).preimage Complex.equivRealProdCLM.symm.continuous).measurableSet
  have hDd : Pairwise (Disjoint on D) := fun i j hij => (hs.disjoint hij).preimage _
  have hUm : MeasurableSet (⋃ i, D i) := MeasurableSet.iUnion hDm
  -- On the disc of the end `i` the curvature is that of the end `i`, and off all discs it is
  -- that of the output end.
  have hRi (i : ι) {z : ℝ × ℝ} (hz : z ∈ D i) :
      ω.hamiltonianCurvature
        (fun z x ↦ inputEndsPerturbation Hs H₀ c b (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndsPerturbation Hs H₀ c b (Complex.equivRealProdCLM.symm z) x Complex.I)
        z =
      ω.hamiltonianCurvature
        (fun z x ↦ inputEndPerturbation (Hs i) (c i) (b i) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndPerturbation (Hs i) (c i) (b i) (Complex.equivRealProdCLM.symm z) x
          Complex.I) z := by
    have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
      (eventually_inputEndsPerturbation_eq_of_mem (Hs := Hs) (H₀ := H₀) hs hz)
    exact ω.hamiltonianCurvature_congr_of_eventuallyEq
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
  have hR₀ {z : ℝ × ℝ} (hz : z ∈ (⋃ i, D i)ᶜ) :
      ω.hamiltonianCurvature
        (fun z x ↦ inputEndsPerturbation Hs H₀ c b (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ inputEndsPerturbation Hs H₀ c b (Complex.equivRealProdCLM.symm z) x Complex.I)
        z =
      ω.hamiltonianCurvature
        (fun z x ↦ negativePlanePerturbation H₀ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ negativePlanePerturbation H₀ (Complex.equivRealProdCLM.symm z) x Complex.I)
        z := by
    simp only [mem_compl_iff, mem_iUnion, not_exists] at hz
    have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
      (eventually_inputEndsPerturbation_eq_of_forall_notMem (Hs := Hs) (H₀ := H₀) hs.ne_zero hz)
    exact ω.hamiltonianCurvature_congr_of_eventuallyEq
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
      (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
  have hout := lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_single_le ω hH₀ hH₀s
    hB₀ inf u
  rw [pairOfPantsPerturbation_single_inf] at hout
  rw [← lintegral_add_compl _ hUm, lintegral_iUnion hDm hDd, tsum_fintype]
  gcongr with i
  · calc _ = ∫⁻ z in D i, ‖ω.hamiltonianCurvature
            (fun z x ↦ inputEndPerturbation (Hs i) (c i) (b i)
              (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ inputEndPerturbation (Hs i) (c i) (b i)
              (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z)‖ₑ :=
          setLIntegral_congr_fun (hDm i) fun z hz ↦ by rw [hRi i hz]
      _ ≤ _ := (setLIntegral_le_lintegral _ _).trans
          (lintegral_enorm_hamiltonianCurvature_inputEndPerturbation_le ω (hH i) (hHs i) (hB i)
            (hs.ne_zero i) (c i) u)
  · calc _ = ∫⁻ z in (⋃ i, D i)ᶜ, ‖ω.hamiltonianCurvature
            (fun z x ↦ negativePlanePerturbation H₀ (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ negativePlanePerturbation H₀ (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z)‖ₑ :=
          setLIntegral_congr_fun hUm.compl fun z hz ↦ by rw [hR₀ hz]
      _ ≤ _ := (setLIntegral_le_lintegral _ _).trans hout

end TauCeti.SmoothTwoForm
