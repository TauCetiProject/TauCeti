/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.MovingEnds

/-!
# Switching off the neck of a plumbed four-punctured sphere

The associativity of the pair-of-pants product compares the two ways of composing two products.
Each composition is a plumbed four-punctured sphere: the output end of a pair of pants with
Hamiltonians `Ha` is glued into the input end `q ∈ {0, 1}` of one with Hamiltonians `Hb`, along a
neck of length `L` carrying the common Hamiltonian `G = Ha ∞ = Hb q`
(`TauCeti.Floer.plumbedPerturbation`). The domain is `ℂ ∖ {c_q, ψ(1), c_r}`, where `ψ` is the
plumbing map, `c_q` the center of the end `q` and `r` the other input. The two compositions sit on
different four-punctured spheres; between them the inputs move, and the datum on spheres with
moving input ends is `TauCeti.Floer.puncturedSpherePerturbation`, which has no neck. This file
joins each plumbed datum to a datum of that family, by scaling the neck Hamiltonian.

For `λ ∈ ℝ` let `K_λ` be the plumbed datum whose neck Hamiltonian is `λ G`, that is,
`plumbedPerturbation (update Ha ∞ (λ G)) (update Hb q (λ G)) q L`. It is linear in `λ`
(`TauCeti.Floer.plumbedPerturbation_update_smul`):

`K_λ = K_0 + λ N`,

where the *neck datum* `N` is the plumbed datum of the negative plane of `G` inserted into the
positive end `q` with Hamiltonian `G`. For `L ≥ 0` the datum `K_0` with switched-off neck is the
datum of the sphere with the three input ends of centers `c_q`, `ψ(1)`, `c_r`, scales `f`, `-f`,
`2 b_r` and Hamiltonians `Ha 0`, `Ha 1`, `Hb r`, and output Hamiltonian `Hb ∞`, where `f` is the
plumbing factor and `b_r` the scale of the end `r`
(`TauCeti.Floer.plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation`). On the inserted
half of the neck the inputs of the inserted pair of pants are pushed forward along
`ψ(w) = c_q + f w` to input ends (`TauCeti.Floer.inputEndPerturbation_sub_div_comp`); elsewhere the
receiving pair of pants with its input `q` switched off is already a sphere with one input end
(`TauCeti.Floer.pairOfPantsPerturbation_update_zero_eq_puncturedSpherePerturbation`).

The neck datum is supported in the annulus `exp (-2π(L - 1)) / 2 < ‖w - c_q‖ < exp (-2π) / 2`
(`TauCeti.Floer.plumbedPerturbation_single_inf_single_eq_zero`), away from all the ends. So every
member of the family agrees with `K_0` near the four punctures, and for `L > 2` it is `H(t) dt`
far out on each end, with the same Hamiltonians and end coordinates for every `λ`
(`TauCeti.Floer.plumbedPerturbation_update_smul_cylindricalEndLift_of_pos`,
`TauCeti.Floer.plumbedPerturbation_update_smul_cylindricalEndLift_inf_of_le`). For `L > 4` the
family is jointly `C^n` in `λ`, the neck length, the domain point and the target point
(`TauCeti.Floer.contMDiffAt_plumbedPerturbation_update_smul`), and for `|λ| ≤ 1` its integrated
curvature along any map into a manifold is bounded uniformly in `λ` and `L`
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_update_smul_le`).

Thus `λ ∈ [0, 1]` is a one-parameter family of Floer data with fixed ends from a datum of the
moving-ends family to the plumbed datum of either composition. The path of configurations joining
the two moving-ends data, and the moduli spaces over the resulting family, are not treated here.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 10, on
  gluing surfaces with strip-like ends and consistent perturbation data over families of them.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9, on
  gluing punctured Riemann surfaces along cylindrical ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {q r : Puncture} {L : ℝ}

/-! ### Switching off the neck -/

/-- On the inserted half `Re z > L/2` of the end `q`, the input ends of the receiving pair of pants
other than `q`, and its output datum, vanish. -/
private theorem receiving_eq_zero_of_lt_re_endCoord (hq : q ≠ inf) (hrq : r ≠ q) (hr : r ≠ inf)
    (hL : 0 ≤ L) {w : ℂ} (h : L / 2 < (q.endCoord w).re) (H Hout : ℝ → M → ℝ) (x : M) :
    inputEndPerturbation r.endCenter (2 * r.endScale) H w x = 0 ∧
      negativePlanePerturbation Hout w x = 0 := by
  have hc : w ≠ q.endCenter := q.ne_endCenter_of_re_endCoord_ne_zero (by
    have : 0 ≤ L / 2 := by positivity
    linarith)
  have hlt : ‖w - q.endCenter‖ < Real.exp (-(2 * π * (L / 2))) / 2 :=
    not_le.1 fun h' => (not_le.2 h) ((re_endCoord_le_iff hq hc).2 h')
  have hexp : Real.exp (-(2 * π * (L / 2))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have hexp' : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [pi_pos])
  refine ⟨inputEndPerturbation_eq_zero_of_le_norm_sub ?_ x,
    negativePlanePerturbation_eq_zero_of_norm_le ?_ x⟩
  · rw [norm_two_mul_endScale hr]
    linarith [one_sub_norm_sub_endCenter_le hq hr hrq w]
  · have h₁ := norm_add_le (w - q.endCenter) q.endCenter
    rw [sub_add_cancel] at h₁
    linarith [norm_endCenter_le_one q, Real.one_le_exp (by positivity : 0 ≤ 2 * π)]

/-- On the receiving part `Re z ≤ L/2` of the end `q`, the input ends of the inserted pair of pants
vanish. -/
private theorem inserted_eq_zero_of_re_endCoord_le (hq : q ≠ inf) (hL : 0 ≤ L) {w : ℂ}
    (h : (q.endCoord w).re ≤ L / 2) (H₀ H₁ : ℝ → M → ℝ) (x : M) :
    inputEndPerturbation q.endCenter (q.plumbingFactor L) H₀ w x = 0 ∧
      inputEndPerturbation (q.plumbingMap L 1) (-q.plumbingFactor L) H₁ w x = 0 := by
  set u := Real.exp (-(2 * π * (L / 2)))
  have hu₀ : 0 < u := Real.exp_pos _
  have hu₁ : u ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have hf : ‖q.plumbingFactor L‖ = u ^ 2 / 4 := by
    rw [norm_plumbingFactor_of_ne_inf hq, ← Real.exp_nat_mul]
    ring_nf
  have he₁ : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [pi_pos])
  have hψ := q.plumbingMap_one_sub_endCenter L
  rcases eq_or_ne w q.endCenter with rfl | hc
  · refine ⟨inputEndPerturbation_self _ _ _ x, inputEndPerturbation_eq_zero_of_le_norm_sub ?_ x⟩
    rw [norm_neg, norm_sub_rev, hψ, hf]
    nlinarith
  · have hge : u / 2 ≤ ‖w - q.endCenter‖ := (re_endCoord_le_iff hq hc).1 h
    refine ⟨inputEndPerturbation_eq_zero_of_le_norm_sub ?_ x,
      inputEndPerturbation_eq_zero_of_le_norm_sub ?_ x⟩
    · rw [hf]
      nlinarith
    · have h₁ := norm_sub_norm_le (w - q.endCenter) (q.plumbingMap L 1 - q.endCenter)
      rw [sub_sub_sub_cancel_right, hψ, hf] at h₁
      rw [norm_neg, hf]
      nlinarith

/-- **With the neck switched off, the plumbed sphere has moving input ends.** Plumb the output end
of a pair of pants with Hamiltonians `Ha` into the input end `q ≠ ∞` of one with Hamiltonians
`Hb`, along a neck of length `L ≥ 0`, with the Hamiltonian of the neck set to zero. The plumbed
datum is the datum of the sphere with the three input ends of centers `c_q`, `ψ(1)` and `c_r`,
scales `f`, `-f` and `2 b_r`, and Hamiltonians `Ha 0`, `Ha 1` and `Hb r`, and with output
Hamiltonian `Hb ∞`. Here `r` is the other input, `ψ` the plumbing map, `f` the plumbing factor and
`b_r` the scale of the end `r`. -/
theorem plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation (hq : q ≠ inf)
    (hrq : r ≠ q) (hr : r ≠ inf) (hL : 0 ≤ L) (Ha Hb : Puncture → ℝ → M → ℝ) :
    plumbedPerturbation (update Ha inf 0) (update Hb q 0) q L =
      puncturedSpherePerturbation ![q.endCenter, q.plumbingMap L 1, r.endCenter]
        ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] ![Ha zero, Ha one, Hb r]
        (Hb inf) := by
  funext w x
  rw [plumbedPerturbation_def, puncturedSpherePerturbation_def, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  split_ifs with h
  · -- On the inserted half the two inputs of the inserted pair of pants are pushed forward.
    obtain ⟨h₁, h₂⟩ := receiving_eq_zero_of_lt_re_endCoord hq hrq hr hL h (Hb r) (Hb inf) x
    rw [← puncturedSpherePerturbation_eq_pairOfPantsPerturbation, puncturedSpherePerturbation_def,
      Fin.sum_univ_two, update_self, h₁, h₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ne_eq,
      reduceCtorEq, not_false_eq_true, update_of_ne, negativePlanePerturbation_zero, add_zero,
      ContinuousLinearMap.add_comp, inputEndPerturbation_sub_div_comp,
      mul_zero, mul_one, mul_neg, plumbingMap_apply]
  · -- On the receiving part the inputs of the inserted pair of pants vanish.
    obtain ⟨h₁, h₂⟩ := inserted_eq_zero_of_re_endCoord_le hq hL (not_lt.1 h) (Ha zero) (Ha one) x
    rw [pairOfPantsPerturbation_update_zero_eq_puncturedSpherePerturbation hq hrq hr,
      puncturedSpherePerturbation_def, Fin.sum_univ_one, h₁, h₂, zero_add, zero_add]
    simp only [Matrix.cons_val_fin_one]

/-! ### The neck datum -/

/-- **The neck datum is supported in the neck.** For `L > 2`, the plumbed datum of the negative
plane of `G` inserted into the positive end `q` with Hamiltonian `G` vanishes off the annulus
`exp (-2π(L - 1)) / 2 < ‖w - c_q‖ < exp (-2π) / 2`. -/
theorem plumbedPerturbation_single_inf_single_eq_zero (hq : q ≠ inf) (hL : 2 < L)
    (G : ℝ → M → ℝ) {w : ℂ}
    (hw : ‖w - q.endCenter‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2 ∨
      Real.exp (-(2 * π)) / 2 ≤ ‖w - q.endCenter‖) (x : M) :
    plumbedPerturbation (Pi.single inf G) (Pi.single q G) q L w x = 0 := by
  rcases hw with hw | hw
  · exact plumbedPerturbation_single_inf_eq_zero hq hL hw x
  · have hc : w ≠ q.endCenter := by
      rintro rfl
      rw [sub_self, norm_zero] at hw
      linarith [Real.exp_pos (-(2 * π))]
    have hre : (q.endCoord w).re ≤ 1 := (re_endCoord_le_iff hq hc).2 (by simpa using hw)
    rw [plumbedPerturbation_def, ite_eq_right (by linarith), pairOfPantsPerturbation_single,
      endSign_eq_one hq, one_mul, smoothTransition.zero_of_nonpos (by linarith), zero_mul,
      zero_smul]

/-- **Scaling the neck Hamiltonian.** The plumbed datum with neck Hamiltonian `λ G` is the datum
with the neck switched off plus `λ` times the neck datum. -/
theorem plumbedPerturbation_update_smul (Ha Hb : Puncture → ℝ → M → ℝ) (q : Puncture) (L : ℝ)
    (G : ℝ → M → ℝ) (c : ℝ) :
    plumbedPerturbation (update Ha inf (c • G)) (update Hb q (c • G)) q L =
      plumbedPerturbation (update Ha inf 0) (update Hb q 0) q L +
        c • plumbedPerturbation (Pi.single inf G) (Pi.single q G) q L := by
  have hupd : ∀ (H : Puncture → ℝ → M → ℝ) (p : Puncture),
      update H p (c • G) = update H p 0 + c • (Pi.single p G : Puncture → ℝ → M → ℝ) :=
      fun H p => by
    funext s
    rcases eq_or_ne s p with rfl | hs <;> simp [*]
  rw [hupd Ha, hupd Hb, plumbedPerturbation_add, plumbedPerturbation_smul]

/-! ### The ends of the family -/

/-- The centers `c_q`, `ψ(1)` and `c_r` of the three input ends of the plumbed sphere. -/
private def plumbedCenters (q r : Puncture) (L : ℝ) : Fin 3 → ℂ :=
  ![q.endCenter, q.plumbingMap L 1, r.endCenter]

/-- The scales `f`, `-f` and `2 b_r` of the three input ends of the plumbed sphere. -/
private def plumbedScales (q r : Puncture) (L : ℝ) : Fin 3 → ℂ :=
  ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale]

private theorem plumbedCenters_def (q r : Puncture) (L : ℝ) :
    plumbedCenters q r L = ![q.endCenter, q.plumbingMap L 1, r.endCenter] := rfl

private theorem plumbedScales_def (q r : Puncture) (L : ℝ) :
    plumbedScales q r L = ![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] := rfl

private theorem plumbedCenters_zero : plumbedCenters q r L 0 = q.endCenter := rfl

private theorem plumbedCenters_one : plumbedCenters q r L 1 = q.plumbingMap L 1 := rfl

private theorem plumbedCenters_two : plumbedCenters q r L 2 = r.endCenter := rfl

private theorem norm_plumbedScales_zero (hq : q ≠ inf) :
    ‖plumbedScales q r L 0‖ = Real.exp (-(2 * π * L)) / 4 :=
  norm_plumbingFactor_of_ne_inf hq L

private theorem norm_plumbedScales_one (hq : q ≠ inf) :
    ‖plumbedScales q r L 1‖ = Real.exp (-(2 * π * L)) / 4 :=
  (norm_neg _).trans (norm_plumbingFactor_of_ne_inf hq L)

private theorem norm_plumbedScales_two (hr : r ≠ inf) : ‖plumbedScales q r L 2‖ = 1 :=
  norm_two_mul_endScale hr

private theorem plumbedScales_ne_zero (i : Fin 3) : plumbedScales q r L i ≠ 0 :=
  match i with
  | 0 => q.plumbingFactor_ne_zero L
  | 1 => neg_ne_zero.2 (q.plumbingFactor_ne_zero L)
  | 2 => mul_ne_zero two_ne_zero r.endScale_ne_zero

/-- The three input ends of the plumbed sphere have pairwise disjoint end discs. -/
private theorem pairwise_norm_add_le (hq : q ≠ inf) (hrq : r ≠ q) (hr : r ≠ inf) (hL : 0 ≤ L) :
    Pairwise fun i j : Fin 3 =>
      ‖plumbedScales q r L i‖ / 2 + ‖plumbedScales q r L j‖ / 2 ≤
        ‖plumbedCenters q r L i - plumbedCenters q r L j‖ := by
  have hε : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have h01 : ‖plumbedScales q r L 0‖ / 2 + ‖plumbedScales q r L 1‖ / 2 ≤
      ‖plumbedCenters q r L 0 - plumbedCenters q r L 1‖ := by
    rw [norm_plumbedScales_zero hq, norm_plumbedScales_one hq, plumbedCenters_zero,
      plumbedCenters_one, norm_sub_rev, q.plumbingMap_one_sub_endCenter,
      norm_plumbingFactor_of_ne_inf hq]
    linarith
  have h02 : ‖plumbedScales q r L 0‖ / 2 + ‖plumbedScales q r L 2‖ / 2 ≤
      ‖plumbedCenters q r L 0 - plumbedCenters q r L 2‖ := by
    rw [norm_plumbedScales_zero hq, norm_plumbedScales_two hr, plumbedCenters_zero,
      plumbedCenters_two, norm_endCenter_sub_endCenter hq hr hrq]
    linarith
  have h12 : ‖plumbedScales q r L 1‖ / 2 + ‖plumbedScales q r L 2‖ / 2 ≤
      ‖plumbedCenters q r L 1 - plumbedCenters q r L 2‖ := by
    rw [norm_plumbedScales_one hq, norm_plumbedScales_two hr, plumbedCenters_one,
      plumbedCenters_two]
    have h := one_sub_norm_plumbingFactor_le hq hr hrq L
    rw [norm_plumbingFactor_of_ne_inf hq] at h
    linarith
  intro i j hij
  match i, j with
  | 0, 0 | 1, 1 | 2, 2 => exact absurd rfl hij
  | 0, 1 => exact h01
  | 0, 2 => exact h02
  | 1, 2 => exact h12
  | 1, 0 => rw [add_comm, norm_sub_rev]; exact h01
  | 2, 0 => rw [add_comm, norm_sub_rev]; exact h02
  | 2, 1 => rw [add_comm, norm_sub_rev]; exact h12

/-- The three input ends of the plumbed sphere lie in the disc on which the output datum
vanishes. -/
private theorem norm_add_le_two_mul_exp (hq : q ≠ inf) (hr : r ≠ inf) (hL : 0 ≤ L) (i : Fin 3) :
    ‖plumbedCenters q r L i‖ + ‖plumbedScales q r L i‖ / 2 ≤ 2 * Real.exp (2 * π) := by
  have hε : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  have h1 : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  match i with
  | 0 =>
    rw [plumbedCenters_zero, norm_plumbedScales_zero hq]
    linarith [norm_endCenter_le_one q]
  | 1 =>
    have hψ : ‖q.plumbingMap L 1‖ ≤ 1 + ‖q.plumbingFactor L‖ := by
      rw [plumbingMap_apply, mul_one]
      exact (norm_add_le _ _).trans (by linarith [norm_endCenter_le_one q])
    rw [plumbedCenters_one, norm_plumbedScales_one hq]
    rw [norm_plumbingFactor_of_ne_inf hq] at hψ
    linarith
  | 2 =>
    rw [plumbedCenters_two, norm_plumbedScales_two hr]
    linarith [norm_endCenter_le_one r]

/-- On the end disc `‖w - c_i‖ < ‖a_i‖ / 2` of each input end of the plumbed sphere, the neck
datum vanishes, for `L > 2`. -/
private theorem neck_eq_zero_of_norm_sub_lt (hq : q ≠ inf) (hrq : r ≠ q) (hr : r ≠ inf)
    (hL : 2 < L) (G : ℝ → M → ℝ) {i : Fin 3} {w : ℂ}
    (hw : ‖w - plumbedCenters q r L i‖ < ‖plumbedScales q r L i‖ / 2) (x : M) :
    plumbedPerturbation (Pi.single inf G) (Pi.single q G) q L w x = 0 := by
  refine plumbedPerturbation_single_inf_single_eq_zero hq hL G ?_ x
  -- The inner radius of the neck is `exp (2π) exp (-2πL) / 2`, at least `2 ‖f‖`.
  have hinner : Real.exp (-(2 * π * (L - 1))) = Real.exp (2 * π) * Real.exp (-(2 * π * L)) := by
    rw [← Real.exp_add]
    ring_nf
  have h1 : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  have hε₀ : 0 < Real.exp (-(2 * π * L)) := Real.exp_pos _
  have he₁ : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [pi_pos])
  match i with
  | 0 =>
    rw [plumbedCenters_zero, norm_plumbedScales_zero hq] at hw
    left
    rw [hinner]
    nlinarith
  | 1 =>
    rw [plumbedCenters_one, norm_plumbedScales_one hq] at hw
    left
    have h := norm_add_le (w - q.plumbingMap L 1) (q.plumbingMap L 1 - q.endCenter)
    rw [sub_add_sub_cancel, q.plumbingMap_one_sub_endCenter,
      norm_plumbingFactor_of_ne_inf hq] at h
    rw [hinner]
    nlinarith
  | 2 =>
    rw [plumbedCenters_two, norm_plumbedScales_two hr] at hw
    right
    linarith [one_sub_norm_sub_endCenter_le hq hr hrq w]

variable {Ha Hb : Puncture → ℝ → M → ℝ} {G : ℝ → M → ℝ}

/-- **The family on the input ends.** For every `λ` and `L > 2`, on the part `s > 0` of each of
the three input ends of the plumbed sphere, the pullback of the plumbed datum with neck
Hamiltonian `λ G` along the end lift `z ↦ c_i + a_i φ₀(z)` is the continuation datum
`β(s - 1) H_i(t) dt`, where `c_i`, `a_i` and `H_i` are the centers, scales and Hamiltonians of
`plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation`. In particular it is
`H_i(t) dt` for `s ≥ 2`, independently of `λ`. -/
theorem plumbedPerturbation_update_smul_cylindricalEndLift_of_pos (hq : q ≠ inf) (hrq : r ≠ q)
    (hr : r ≠ inf) (hL : 2 < L) (c : ℝ) (i : Fin 3)
    (hH : Periodic ((![Ha zero, Ha one, Hb r] : Fin 3 → ℝ → M → ℝ) i) 1) {z : ℂ} (hz : 0 < z.re)
    (x : M) (v : ℂ) :
    plumbedPerturbation (update Ha inf (c • G)) (update Hb q (c • G)) q L
        ((![q.endCenter, q.plumbingMap L 1, r.endCenter] : Fin 3 → ℂ) i +
          (![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] : Fin 3 → ℂ) i *
            zero.cylindricalEndLift z) x
        ((![q.plumbingFactor L, -q.plumbingFactor L, 2 * r.endScale] : Fin 3 → ℂ) i *
          (deriv zero.cylindricalEndLift z * v)) =
      v.im * (smoothTransition (z.re - 1) *
        (![Ha zero, Ha one, Hb r] : Fin 3 → ℝ → M → ℝ) i z.im x) := by
  rw [← plumbedCenters_def, ← plumbedScales_def]
  have ha : plumbedScales q r L i ≠ 0 := plumbedScales_ne_zero i
  -- The point lies in the end disc of the input `i`, where the neck datum vanishes.
  have hlt : ‖plumbedCenters q r L i + plumbedScales q r L i * zero.cylindricalEndLift z -
      plumbedCenters q r L i‖ < ‖plumbedScales q r L i‖ / 2 := by
    have h := norm_cylindricalEndLift_sub_endCenter zero z
    rw [endCenter_zero, sub_zero, endScale_zero] at h
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [add_sub_cancel_left, norm_mul, h, h2]
    have : Real.exp (-(2 * π * z.re)) < 1 :=
      Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
    nlinarith [norm_pos_iff.2 ha]
  rw [plumbedPerturbation_update_smul,
    plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation hq hrq hr (by linarith),
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, ← plumbedCenters_def,
    ← plumbedScales_def, neck_eq_zero_of_norm_sub_lt hq hrq hr hL G hlt, smul_zero, add_zero]
  exact puncturedSpherePerturbation_cylindricalEndLift_of_pos
    (pairwise_norm_add_le hq hrq hr (by linarith)) (norm_add_le_two_mul_exp hq hr (by linarith))
    hH ha hz x v

/-- **The family on the output end.** For every `λ` and `L > 2`, on the part `s ≤ -1` of the
output end, the pullback of the plumbed datum with neck Hamiltonian `λ G` along the end lift `φ_∞`
is the continuation datum `β(-s - 1) Hb_∞(t) dt`. -/
theorem plumbedPerturbation_update_smul_cylindricalEndLift_inf_of_le (hq : q ≠ inf) (hL : 2 < L)
    (hHb : Periodic (Hb inf) 1) (c : ℝ) {z : ℂ} (hz : z.re ≤ -1) (x : M) (v : ℂ) :
    plumbedPerturbation (update Ha inf (c • G)) (update Hb q (c • G)) q L
        (inf.cylindricalEndLift z) x (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * Hb inf z.im x) := by
  -- The moving-ends identification is stated with the remaining finite input `r` of `Hb`.
  obtain ⟨r, hrq, hr⟩ : ∃ r : Puncture, r ≠ q ∧ r ≠ inf := by
    cases q
    exacts [⟨one, by decide, by decide⟩, ⟨zero, by decide, by decide⟩, absurd rfl hq]
  have hnorm : 2 * Real.exp (2 * π) ≤ ‖inf.cylindricalEndLift z‖ := by
    have h := norm_cylindricalEndLift_sub_endCenter inf z
    rw [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h
    rw [h]
    gcongr
    nlinarith [Real.pi_pos]
  have hneck : plumbedPerturbation (Pi.single inf G) (Pi.single q G) q L
      (inf.cylindricalEndLift z) x = 0 := by
    refine plumbedPerturbation_single_inf_single_eq_zero hq hL G (Or.inr ?_) x
    have h := norm_sub_norm_le (inf.cylindricalEndLift z) q.endCenter
    linarith [norm_endCenter_le_one q, Real.one_le_exp (by positivity : 0 ≤ 2 * π),
      Real.exp_le_one_iff.2 (by linarith [pi_pos] : -(2 * π) ≤ 0)]
  rw [plumbedPerturbation_update_smul,
    plumbedPerturbation_update_zero_eq_puncturedSpherePerturbation hq hrq hr (by linarith),
    Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hneck, smul_zero, add_zero,
    ← plumbedCenters_def, ← plumbedScales_def]
  exact puncturedSpherePerturbation_cylindricalEndLift_inf_of_le
    (norm_add_le_two_mul_exp hq hr (by linarith)) hHb hz x v

/-! ### Smoothness and curvature of the family -/

section Manifold

variable {E G' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G']
  {I : ModelWithCorners ℝ E G'} [TopologicalSpace M] [ChartedSpace G' M]

/-- **The family is smooth.** For period-one Hamiltonians `Ha`, `Hb` and `G` of class `C^n` on
`ℝ × M` (only needed for the entries `Ha p`, `p ≠ ∞`, and `Hb p`, `p ≠ q`, that are not replaced by
the neck Hamiltonian), the plumbed datum with neck Hamiltonian `λ G` is `C^n` jointly in `λ`,
the neck length `L > 4`, the domain point and the target point, at every domain point other than
the four punctures `0`, `1`, `∞` and `ψ_L(1)`. -/
theorem contMDiffAt_plumbedPerturbation_update_smul {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ p ≠ inf, Periodic (Ha p) 1) (hHb : ∀ p ≠ q, Periodic (Hb p) 1) (hG : Periodic G 1)
    (hHas : ∀ p ≠ inf, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Ha p)))
    (hHbs : ∀ p ≠ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb p)))
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry G)) (c : ℝ) (hL : 4 < L) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I))) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℝ × (ℂ × M)) =>
        plumbedPerturbation (update Ha inf (p.1 • G)) (update Hb q (p.1 • G)) q p.2.1 p.2.2.1
          p.2.2.2)
      (c, (L, (w, x))) := by
  -- Both summands of `plumbedPerturbation_update_smul` are plumbed data of smooth families,
  -- whose entries are entries of `Ha`, `Hb`, `G` or `0`; `Pi.single p G` is `update 0 p G`.
  have hsm₀ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (0 : ℝ → M → ℝ)) := contMDiff_const
  have hA := contMDiffAt_plumbedPerturbation_family hq
    ((forall_update_iff Ha fun _ f => Periodic f 1).2 ⟨fun _ => rfl, hHa⟩)
    ((forall_update_iff Hb fun _ f => Periodic f 1).2 ⟨fun _ => rfl, hHb⟩)
    ((forall_update_iff Ha fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
      ⟨hsm₀, hHas⟩)
    ((forall_update_iff Hb fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
      ⟨hsm₀, hHbs⟩)
    (by simp) hL hw x
  have hN := contMDiffAt_plumbedPerturbation_family (Ha := Pi.single inf G) (Hb := Pi.single q G)
    hq ((forall_update_iff _ fun _ f => Periodic f 1).2 ⟨hG, fun _ _ _ => rfl⟩)
    ((forall_update_iff _ fun _ f => Periodic f 1).2 ⟨hG, fun _ _ _ => rfl⟩)
    ((forall_update_iff _ fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
      ⟨hGs, fun _ _ => hsm₀⟩)
    ((forall_update_iff _ fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
      ⟨hGs, fun _ _ => hsm₀⟩)
    (by simp) hL hw x
  simp_rw [plumbedPerturbation_update_smul, Pi.add_apply, Pi.smul_apply]
  -- Scalar multiplication is a smooth map on `ℝ × (ℂ →L[ℝ] ℝ)`.
  have hpair := contMDiffAt_fst.prodMk_space (hN.comp (c, (L, (w, x))) contMDiffAt_snd)
  exact (hA.comp (c, (L, (w, x))) contMDiffAt_snd).add
    ((contDiff_smul.contMDiff.contMDiffAt).comp (c, (L, (w, x))) hpair)

end Manifold

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory

variable {E G' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G']
  {I : ModelWithCorners ℝ E G'} [TopologicalSpace M] [ChartedSpace G' M] [IsManifold I ⊤ M]
  {Ha Hb : Puncture → ℝ → M → ℝ} {G : ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- **The integrated curvature of the family is bounded uniformly.** For period-one `C¹`
Hamiltonians `Ha`, `Hb` and `G` on a manifold `M` with a two-form `ω`, with `|Ha p| ≤ Ba p`,
`|Hb p| ≤ Bb p` and `|G| ≤ B` (only needed for the entries `Ha p`, `p ≠ ∞`, and `Hb p`, `p ≠ q`,
that are not replaced by the neck Hamiltonian), the integral of `|R_K|` along any map, for the
plumbed datum `K` with neck Hamiltonian `λ G`, is at most the sum of the bounds of `Ha` and `Hb`
with `|λ| B` in place of the bounds at the neck, for all neck lengths `L > 4`. In particular it is
bounded uniformly over `|λ| ≤ 1` and `L > 4`. -/
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_update_smul_le
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHa : ∀ p ≠ inf, Periodic (Ha p) 1)
    (hHb : ∀ p ≠ q, Periodic (Hb p) 1) (hG : Periodic G 1)
    (hHas : ∀ p ≠ inf, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha p)))
    (hHbs : ∀ p ≠ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb p)))
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G)) (hL : 4 < L) (c : ℝ)
    {Ba Bb : Puncture → ℝ} {B : ℝ} (hBa : ∀ p ≠ inf, ∀ t x, |Ha p t x| ≤ Ba p)
    (hBb : ∀ p ≠ q, ∀ t x, |Hb p t x| ≤ Bb p) (hB : ∀ t x, |G t x| ≤ B) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation (update Ha inf (c • G)) (update Hb q (c • G)) q L
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation (update Ha inf (c • G)) (update Hb q (c • G)) q L
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤
      ∑ p, ENNReal.ofReal (update Ba inf (|c| * B) p) +
        ∑ p, ENNReal.ofReal (update Bb q (|c| * B) p) := by
  have hcG : Periodic (c • G) 1 := fun t => by simp [hG t]
  have hcGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (c • G)) := by
    have : uncurry (c • G) = (fun y : ℝ => c • y) ∘ uncurry G := by
      funext ⟨t, x⟩
      simp
    rw [this]
    exact (contDiff_const_smul c).contMDiff.comp hGs
  have hcB : ∀ t x, |(c • G) t x| ≤ |c| * B := fun t x => by
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB t x) (abs_nonneg c)
  exact ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le hq
    ((forall_update_iff Ha fun _ f => Periodic f 1).2 ⟨hcG, hHa⟩)
    ((forall_update_iff Hb fun _ f => Periodic f 1).2 ⟨hcG, hHb⟩)
    ((forall_update_iff Ha fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry f)).2
      ⟨hcGs, hHas⟩)
    ((forall_update_iff Hb fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry f)).2
      ⟨hcGs, hHbs⟩)
    (by simp) hL
    ((forall_update_iff Ha fun p f => ∀ t x, |f t x| ≤ update Ba inf (|c| * B) p).2
      ⟨by simpa using hcB, fun p hp => by simpa [update_of_ne hp] using hBa p hp⟩)
    ((forall_update_iff Hb fun p f => ∀ t x, |f t x| ≤ update Bb q (|c| * B) p).2
      ⟨by simpa using hcB, fun p hp => by simpa [update_of_ne hp] using hBb p hp⟩) u

end TauCeti.SmoothTwoForm
