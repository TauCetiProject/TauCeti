/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.AssociativityPath
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# The associativity family of Floer data

The associativity of the pair-of-pants product on homology compares the two compositions
`(x₁ x₂) x₃` and `x₁ (x₂ x₃)` of three inputs with Hamiltonians `H₀, H₁, H₂` and an output with
Hamiltonian `Hout`. Each composition is a plumbed four-punctured sphere,
`TauCeti.Floer.plumbedPerturbation`: a pair of pants is inserted into the input `0`, respectively
`1`, of another along a neck of length `L` carrying an intermediate Hamiltonian `G`, respectively
`G'`. This file joins the two data by one family `K_τ`, `τ ∈ ℝ`, of Floer data on spheres with
three moving input ends, `TauCeti.Floer.associativityPerturbation H Hout G G' L τ`:

`K_τ = Σ_τ + β(-τ) N + β(τ - 1) N'`,

where `β = smoothTransition`, `Σ_τ` is the datum `TauCeti.Floer.puncturedSpherePerturbation` of
the input ends along the associativity path `TauCeti.Floer.associativityCenter`,
`TauCeti.Floer.associativityScale` of plumbing factor `e^{-2πL} / 4`, the path along which the
almost complex structures and the compactness results over spheres with moving input ends are
stated, and `N`, `N'` are the neck data of the two compositions
(`TauCeti.Floer.plumbedPerturbation_update_smul`). Along the family:

* for `τ ≤ -1` it is the plumbed datum of `(x₁ x₂) x₃`
  (`TauCeti.Floer.associativityPerturbation_of_le_neg_one`), and for `τ ≥ 2` that of
  `x₁ (x₂ x₃)` (`TauCeti.Floer.associativityPerturbation_of_two_le`); on `[-1, 0]` and `[1, 2]`
  it is the plumbed datum with the neck Hamiltonian scaled by `β(-τ)`, respectively `β(τ - 1)`
  (`TauCeti.Floer.associativityPerturbation_of_nonpos`,
  `TauCeti.Floer.associativityPerturbation_of_one_le`), and on `[0, 1]` it is the datum of the
  moving input ends alone (`TauCeti.Floer.associativityPerturbation_of_mem_Icc`);
* for `L > 2` it is `H_i(t) dt` far out on every input end `i` and `Hout(t) dt` far out on the
  output end, in the end coordinates of the configuration at `τ`, for every `τ`
  (`TauCeti.Floer.associativityPerturbation_cylindricalEndLift_of_pos`,
  `TauCeti.Floer.associativityPerturbation_cylindricalEndLift_inf_of_le`); there the neck data
  vanish, and the family is the datum `Σ_τ` of the moving input ends on the part `s > 0` of every
  input end and the part `s ≤ -1` of the output end
  (`associativityPerturbation_add_mul_cylindricalEndLift_eq_puncturedSpherePerturbation`,
  `associativityPerturbation_cylindricalEndLift_inf_eq_puncturedSpherePerturbation`, in the
  namespace `TauCeti.Floer`);
* for `L > 4` it is `C^n` jointly in the neck length `L`, `τ`, the domain point and the target
  point, away from the three moving input punctures
  (`TauCeti.Floer.contMDiffAt_associativityPerturbation`, and
  `TauCeti.Floer.contDiffAt_uncurry_associativityPerturbation` for its components on a normed
  space target, in real coordinates on the domain);
* for `L > 4` its integrated curvature along any map is bounded uniformly in `τ` and `L`, by
  `∑ i, B i + Bout + 2 (BG + BG')` for bounds `B i`, `Bout`, `BG`, `BG'` of the Hamiltonians
  (`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le`,
  and `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le`
  for a symplectic vector space target), and so is its integral over every region
  (`TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_associativityPerturbation_le`).

So the two ends of the family are the plumbed data of the two compositions, which break into the
two composed products as the neck length `L` grows, and its curvature bound is the input to
energy bounds for its Floer solutions that are uniform over the family. The energy identity is in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Associativity`, and the semi-Fredholm
estimate of the linearized operator of each member of the family in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Associativity.SemiFredholm`; the moduli spaces over
the family and their boundary are not treated here.

## References

* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Sections 9 and 12, on
  consistent perturbation data over families of punctured surfaces and their gluing ends.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations and their curvature.
-/

public noncomputable section

open Set Real Manifold Topology Function Filter
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {H : Fin 3 → ℝ → M → ℝ} {Hout G G' : ℝ → M → ℝ} {L τ : ℝ}

/-- **The associativity family of Floer data.** For input Hamiltonians `H i`, output Hamiltonian
`Hout`, intermediate Hamiltonians `G` of `(x₁ x₂) x₃` and `G'` of `x₁ (x₂ x₃)`, and neck length
`L`, the datum `Σ_τ + β(-τ) N + β(τ - 1) N'`: the datum `Σ_τ` of the input ends along the
associativity path of plumbing factor `e^{-2πL} / 4`, plus the neck data `N` of `(x₁ x₂) x₃` and
`N'` of `x₁ (x₂ x₃)` scaled by `β(-τ)` and `β(τ - 1)`, where `β = smoothTransition`. -/
def associativityPerturbation (H : Fin 3 → ℝ → M → ℝ) (Hout G G' : ℝ → M → ℝ) (L τ : ℝ) (w : ℂ)
    (x : M) : ℂ →L[ℝ] ℝ :=
  puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
      (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout w x +
    smoothTransition (-τ) • plumbedPerturbation (Pi.single inf G) (Pi.single zero G) zero L w x +
    smoothTransition (τ - 1) • plumbedPerturbation (Pi.single inf G') (Pi.single one G') one L w x

theorem associativityPerturbation_def (H : Fin 3 → ℝ → M → ℝ) (Hout G G' : ℝ → M → ℝ)
    (L τ : ℝ) (w : ℂ) (x : M) :
    associativityPerturbation H Hout G G' L τ w x =
      puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
          (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout w x +
        smoothTransition (-τ) •
          plumbedPerturbation (Pi.single inf G) (Pi.single zero G) zero L w x +
        smoothTransition (τ - 1) •
          plumbedPerturbation (Pi.single inf G') (Pi.single one G') one L w x :=
  (rfl)

/-! ### The pieces of the family -/

/-- **On `[0, 1]` the family is the datum of the moving input ends.** -/
theorem associativityPerturbation_of_mem_Icc (hτ : τ ∈ Icc 0 1) :
    associativityPerturbation H Hout G G' L τ =
      puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout := by
  funext w x
  rw [associativityPerturbation_def, smoothTransition.zero_of_nonpos (by linarith [hτ.1]),
    smoothTransition.zero_of_nonpos (by linarith [hτ.2]), zero_smul, zero_smul, add_zero,
    add_zero]

/-- **For `τ ≤ 0` the family is the plumbed datum of `(x₁ x₂) x₃` with a scaled neck.** Inserting
a pair of pants with Hamiltonians `Ha` into the input `0` of one with Hamiltonians `Hb`, the
family with inputs `Ha 0, Ha 1, Hb 1` and output `Hb ∞` is the plumbed datum whose neck
Hamiltonian is `β(-τ) G`. -/
theorem associativityPerturbation_of_nonpos (hL : 0 ≤ L) (hτ : τ ≤ 0)
    (Ha Hb : Puncture → ℝ → M → ℝ) (G G' : ℝ → M → ℝ) :
    associativityPerturbation ![Ha zero, Ha one, Hb one] (Hb inf) G G' L τ =
      plumbedPerturbation (update Ha inf (smoothTransition (-τ) • G))
        (update Hb zero (smoothTransition (-τ) • G)) zero L := by
  funext w x
  rw [associativityPerturbation_def, smoothTransition.zero_of_nonpos (by linarith : τ - 1 ≤ 0),
    zero_smul, add_zero, plumbedPerturbation_update_smul,
    ← puncturedSpherePerturbation_associativity_of_nonpos hτ hL, Pi.add_apply, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply]

/-- **For `τ ≤ -1` the family is the plumbed datum of `(x₁ x₂) x₃`.** Inserting a pair of pants
with Hamiltonians `Ha` into the input `0` of one with Hamiltonians `Hb`, along a neck carrying
`Hb 0 = Ha ∞`, the family with inputs `Ha 0, Ha 1, Hb 1`, output `Hb ∞` and intermediate
Hamiltonian `Ha ∞` is the plumbed datum. -/
theorem associativityPerturbation_of_le_neg_one (hL : 0 ≤ L) (hτ : τ ≤ -1)
    {Ha Hb : Puncture → ℝ → M → ℝ} (hab : Hb zero = Ha inf) (G' : ℝ → M → ℝ) :
    associativityPerturbation ![Ha zero, Ha one, Hb one] (Hb inf) (Ha inf) G' L τ =
      plumbedPerturbation Ha Hb zero L := by
  rw [associativityPerturbation_of_nonpos hL (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_smul, update_eq_self, ← hab,
    update_eq_self]

/-- **For `τ ≥ 1` the family is the plumbed datum of `x₁ (x₂ x₃)` with a scaled neck.** Inserting
a pair of pants with Hamiltonians `Ha` into the input `1` of one with Hamiltonians `Hb`, the
family with inputs `Hb 0, Ha 0, Ha 1` and output `Hb ∞` is the plumbed datum whose neck
Hamiltonian is `β(τ - 1) G'`. -/
theorem associativityPerturbation_of_one_le (hL : 0 ≤ L) (hτ : 1 ≤ τ)
    (Ha Hb : Puncture → ℝ → M → ℝ) (G G' : ℝ → M → ℝ) :
    associativityPerturbation ![Hb zero, Ha zero, Ha one] (Hb inf) G G' L τ =
      plumbedPerturbation (update Ha inf (smoothTransition (τ - 1) • G'))
        (update Hb one (smoothTransition (τ - 1) • G')) one L := by
  funext w x
  rw [associativityPerturbation_def, smoothTransition.zero_of_nonpos (by linarith : -τ ≤ 0),
    zero_smul, add_zero, plumbedPerturbation_update_smul,
    ← puncturedSpherePerturbation_associativity_of_one_le hτ hL, Pi.add_apply, Pi.add_apply,
    Pi.smul_apply, Pi.smul_apply]

/-- **For `τ ≥ 2` the family is the plumbed datum of `x₁ (x₂ x₃)`.** Inserting a pair of pants
with Hamiltonians `Ha` into the input `1` of one with Hamiltonians `Hb`, along a neck carrying
`Hb 1 = Ha ∞`, the family with inputs `Hb 0, Ha 0, Ha 1`, output `Hb ∞` and intermediate
Hamiltonian `Ha ∞` is the plumbed datum. -/
theorem associativityPerturbation_of_two_le (hL : 0 ≤ L) (hτ : 2 ≤ τ)
    {Ha Hb : Puncture → ℝ → M → ℝ} (hab : Hb one = Ha inf) (G : ℝ → M → ℝ) :
    associativityPerturbation ![Hb zero, Ha zero, Ha one] (Hb inf) G (Ha inf) L τ =
      plumbedPerturbation Ha Hb one L := by
  rw [associativityPerturbation_of_one_le hL (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_smul, update_eq_self, ← hab,
    update_eq_self]

/-- The inputs of `(x₁ x₂) x₃` are the inputs of its two pairs of pants other than the neck. -/
private theorem vecCons_leftInserted_leftReceiving (H : Fin 3 → ℝ → M → ℝ) (Hout G : ℝ → M → ℝ) :
    ![associativityLeftInserted H G zero, associativityLeftInserted H G one,
      associativityLeftReceiving H Hout G one] = H := by
  funext i
  fin_cases i <;> simp

/-- The inputs of `x₁ (x₂ x₃)` are the inputs of its two pairs of pants other than the neck. -/
private theorem vecCons_rightReceiving_rightInserted (H : Fin 3 → ℝ → M → ℝ)
    (Hout G' : ℝ → M → ℝ) :
    ![associativityRightReceiving H Hout G' zero, associativityRightInserted H G' zero,
      associativityRightInserted H G' one] = H := by
  funext i
  fin_cases i <;> simp

/-- The inputs of `x₁ (x₂ x₃)`, listed from the input `x₂` as in the plumbed sphere, are the
inputs relabelled by `finRotate 3`. -/
private theorem vecCons_rightInserted_rightReceiving (H : Fin 3 → ℝ → M → ℝ)
    (Hout G' : ℝ → M → ℝ) :
    ![associativityRightInserted H G' zero, associativityRightInserted H G' one,
      associativityRightReceiving H Hout G' zero] = H ∘ finRotate 3 := by
  funext i
  fin_cases i <;> simp

/-- For `τ ≤ 0` the family is the plumbed datum of `(x₁ x₂) x₃` with a scaled neck, with the
pairs of pants read off from the input Hamiltonians. -/
private theorem associativityPerturbation_eq_left (hL : 0 ≤ L) (hτ : τ ≤ 0) :
    associativityPerturbation H Hout G G' L τ =
      plumbedPerturbation (update (associativityLeftInserted H G) inf (smoothTransition (-τ) • G))
        (update (associativityLeftReceiving H Hout G) zero (smoothTransition (-τ) • G)) zero L := by
  have key := associativityPerturbation_of_nonpos hL hτ (associativityLeftInserted H G)
    (associativityLeftReceiving H Hout G) G G'
  rw [vecCons_leftInserted_leftReceiving, associativityLeftReceiving_inf] at key
  exact key

/-- For `τ ≥ 1` the family is the plumbed datum of `x₁ (x₂ x₃)` with a scaled neck, with the
pairs of pants read off from the input Hamiltonians. -/
private theorem associativityPerturbation_eq_right (hL : 0 ≤ L) (hτ : 1 ≤ τ) :
    associativityPerturbation H Hout G G' L τ =
      plumbedPerturbation
        (update (associativityRightInserted H G') inf (smoothTransition (τ - 1) • G'))
        (update (associativityRightReceiving H Hout G') one (smoothTransition (τ - 1) • G'))
        one L := by
  have key := associativityPerturbation_of_one_le hL hτ (associativityRightInserted H G')
    (associativityRightReceiving H Hout G') G G'
  rw [vecCons_rightReceiving_rightInserted, associativityRightReceiving_inf] at key
  exact key

/-- For `L ≥ 0` the plumbing factor `e^{-2πL} / 4` lies in `(0, 1 / 3]`. -/
theorem exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (hL : 0 ≤ L) :
    0 < Real.exp (-(2 * π * L)) / 4 ∧ 3 * (Real.exp (-(2 * π * L)) / 4) ≤ 1 := by
  have : Real.exp (-(2 * π * L)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [pi_pos])
  exact ⟨by positivity, by linarith⟩

/-! ### The ends of the family -/

/-- **The family on the input ends.** For `L > 2` and every `τ`, on the part `s > 0` of the
input end `i` of the configuration at `τ`, the pullback of the family along the end lift
`z ↦ c_i + a_i φ₀(z)` is the continuation datum `β(s - 1) H_i(t) dt`. In particular it is
`H_i(t) dt` for `s ≥ 2`, with the same Hamiltonian along the whole family. -/
theorem associativityPerturbation_cylindricalEndLift_of_pos (hL : 2 < L) (τ : ℝ) {i : Fin 3}
    (hH : Periodic (H i) 1) {z : ℂ} (hz : 0 < z.re) (x : M) (v : ℂ) :
    associativityPerturbation H Hout G G' L τ
        (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) x
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
          (deriv zero.cylindricalEndLift z * v)) =
      v.im * (smoothTransition (z.re - 1) * H i z.im x) := by
  rcases lt_or_ge τ 0 with hτ | hτ₀
  · -- Before the path, this is the input end `i` of the plumbed sphere of `(x₁ x₂) x₃`.
    rw [associativityPerturbation_eq_left (by linarith) hτ.le,
      associativityCenter_eq_plumbingMap_of_nonpos hτ.le,
      associativityScale_eq_plumbingFactor_of_nonpos hτ.le]
    have hvec := vecCons_leftInserted_leftReceiving H Hout G
    have h := plumbedPerturbation_update_smul_cylindricalEndLift_of_pos (q := zero) (r := one)
      (Ha := associativityLeftInserted H G) (Hb := associativityLeftReceiving H Hout G) (G := G)
      (by decide) (by decide) (by decide) hL (smoothTransition (-τ)) i (by rwa [hvec]) hz x v
    rwa [hvec] at h
  rcases le_or_gt τ 1 with hτ₁ | hτ
  · -- Along the path, this is the input end `i` of the sphere with moving input ends.
    obtain ⟨hf₀, hf₃⟩ :=
      exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (show 0 ≤ L by linarith)
    rw [associativityPerturbation_of_mem_Icc ⟨hτ₀, hτ₁⟩]
    exact puncturedSpherePerturbation_cylindricalEndLift_of_pos
      (pairwise_add_le_norm_associativityCenter_sub hf₀.le hf₃ τ)
      (norm_associativityCenter_add_le hf₀.le (by linarith) τ) hH
      (associativityScale_ne_zero hf₀ τ i) hz x v
  · -- After the path, the input end `finRotate 3 j` is the input end `j` of the plumbed sphere
    -- of `x₁ (x₂ x₃)`.
    obtain ⟨j, rfl⟩ := (finRotate 3).surjective i
    have hc := congrFun (associativityCenter_comp_finRotate_of_one_le (L := L) hτ.le) j
    have ha := congrFun (associativityScale_comp_finRotate_of_one_le (L := L) hτ.le) j
    have hvec := congrFun (vecCons_rightInserted_rightReceiving H Hout G') j
    rw [comp_apply] at hc ha hvec
    rw [associativityPerturbation_eq_right (by linarith) hτ.le, hc, ha]
    have h := plumbedPerturbation_update_smul_cylindricalEndLift_of_pos (q := one) (r := zero)
      (Ha := associativityRightInserted H G') (Hb := associativityRightReceiving H Hout G')
      (G := G') (by decide) (by decide) (by decide) hL (smoothTransition (τ - 1)) j
      (by rwa [hvec]) hz x v
    rwa [hvec] at h

/-- **The family on the output end.** For `L > 2` and every `τ`, on the part `s ≤ -1` of the
output end, the pullback of the family along the end lift `φ_∞` is the continuation datum
`β(-s - 1) Hout(t) dt`. In particular it is `Hout(t) dt` for `s ≤ -2`, with the same end
coordinates along the whole family. -/
theorem associativityPerturbation_cylindricalEndLift_inf_of_le (hL : 2 < L) (τ : ℝ)
    (hHout : Periodic Hout 1) {z : ℂ} (hz : z.re ≤ -1) (x : M) (v : ℂ) :
    associativityPerturbation H Hout G G' L τ (inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * Hout z.im x) := by
  rcases lt_or_ge τ 0 with hτ | hτ₀
  · rw [associativityPerturbation_eq_left (by linarith) hτ.le]
    simpa using plumbedPerturbation_update_smul_cylindricalEndLift_inf_of_le
      (Hb := associativityLeftReceiving H Hout G) (q := zero) (by decide) hL (by simpa using hHout)
      (smoothTransition (-τ)) hz x v
  rcases le_or_gt τ 1 with hτ₁ | hτ
  · obtain ⟨hf₀, hf₃⟩ :=
      exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (show 0 ≤ L by linarith)
    rw [associativityPerturbation_of_mem_Icc ⟨hτ₀, hτ₁⟩]
    exact puncturedSpherePerturbation_cylindricalEndLift_inf_of_le
      (norm_associativityCenter_add_le hf₀.le (by linarith) τ) hHout hz x v
  · rw [associativityPerturbation_eq_right (by linarith) hτ.le]
    simpa using plumbedPerturbation_update_smul_cylindricalEndLift_inf_of_le
      (Hb := associativityRightReceiving H Hout G') (q := one) (by decide) hL
      (by simpa using hHout) (smoothTransition (τ - 1)) hz x v

/-- **On the input ends the family is the datum of the moving input ends.** For `L > 2` and every
`τ`, on the part `s > 0` of the input end `i` of the configuration at `τ`, the family is the datum
`Σ_τ` of the moving input ends: both are `β(s - 1) H_i(t) dt` in the end coordinates, so the neck
data vanish there. -/
theorem associativityPerturbation_add_mul_cylindricalEndLift_eq_puncturedSpherePerturbation
    (hL : 2 < L) (τ : ℝ) {i : Fin 3} (hH : Periodic (H i) 1) {z : ℂ} (hz : 0 < z.re) (x : M) :
    associativityPerturbation H Hout G G' L τ
        (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) x =
      puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout
        (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i +
          associativityScale (Real.exp (-(2 * π * L)) / 4) τ i * zero.cylindricalEndLift z) x := by
  obtain ⟨hf₀, hf₃⟩ :=
    exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (show 0 ≤ L by linarith)
  have hd : associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
      deriv zero.cylindricalEndLift z ≠ 0 :=
    mul_ne_zero (associativityScale_ne_zero hf₀ τ i) (zero.deriv_cylindricalEndLift_ne_zero z)
  -- Every tangent vector of the sphere is the image of a tangent vector of the end.
  refine ContinuousLinearMap.ext fun v ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v', v = associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
      (deriv zero.cylindricalEndLift z * v') :=
    ⟨v / (associativityScale (Real.exp (-(2 * π * L)) / 4) τ i *
      deriv zero.cylindricalEndLift z), by rw [← mul_assoc, mul_div_cancel₀ v hd]⟩
  rw [associativityPerturbation_cylindricalEndLift_of_pos hL τ hH hz,
    puncturedSpherePerturbation_cylindricalEndLift_of_pos
      (pairwise_add_le_norm_associativityCenter_sub hf₀.le hf₃ τ)
      (norm_associativityCenter_add_le hf₀.le (by linarith) τ) hH
      (associativityScale_ne_zero hf₀ τ i) hz]

/-- **On the output end the family is the datum of the moving input ends.** For `L > 2` and every
`τ`, on the part `s ≤ -1` of the output end, the family is the datum `Σ_τ` of the moving input
ends: both are `β(-s - 1) Hout(t) dt` in the end coordinates, so the neck data vanish there. -/
theorem associativityPerturbation_cylindricalEndLift_inf_eq_puncturedSpherePerturbation
    (hL : 2 < L) (τ : ℝ) (hHout : Periodic Hout 1) {z : ℂ} (hz : z.re ≤ -1) (x : M) :
    associativityPerturbation H Hout G G' L τ (inf.cylindricalEndLift z) x =
      puncturedSpherePerturbation (associativityCenter (Real.exp (-(2 * π * L)) / 4) τ)
        (associativityScale (Real.exp (-(2 * π * L)) / 4) τ) H Hout (inf.cylindricalEndLift z)
        x := by
  obtain ⟨hf₀, hf₃⟩ :=
    exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (show 0 ≤ L by linarith)
  -- Every tangent vector of the sphere is the image of a tangent vector of the end.
  refine ContinuousLinearMap.ext fun v ↦ ?_
  obtain ⟨v, rfl⟩ : ∃ v', v = deriv inf.cylindricalEndLift z * v' :=
    ⟨v / deriv inf.cylindricalEndLift z,
      (mul_div_cancel₀ v (inf.deriv_cylindricalEndLift_ne_zero z)).symm⟩
  rw [associativityPerturbation_cylindricalEndLift_inf_of_le hL τ hHout hz,
    puncturedSpherePerturbation_cylindricalEndLift_inf_of_le
      (norm_associativityCenter_add_le hf₀.le (by linarith) τ) hHout hz]

/-! ### Smoothness -/

section Manifold

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace E']
  {I : ModelWithCorners ℝ E E'} [TopologicalSpace M] [ChartedSpace E' M]

/-- A neck datum scaled by a smooth function `φ` of the parameter is smooth jointly in the neck
length, the parameter, the domain point and the target point, at every domain point other than
the punctures of its plumbed sphere, and wherever `φ` vanishes near the parameter. -/
private theorem contMDiffAt_smul_neck {n : ℕ∞} {q : Puncture} (hq : q ≠ inf) (hG : Periodic G 1)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry G)) (hL : 4 < L) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ n φ) {w : ℂ}
    (h : φ =ᶠ[𝓝 τ] 0 ∨ (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℝ × ℝ) × (ℂ × M) =>
        φ p.1.2 • plumbedPerturbation (Pi.single inf G) (Pi.single q G) q p.1.1 p.2.1 p.2.2)
      ((L, τ), (w, x)) := by
  rcases h with h | hw
  · refine (contMDiffAt_const (c := (0 : ℂ →L[ℝ] ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_snd.comp continuous_fst).continuousAt.eventually h] with p hp
    rw [comp_apply, Pi.zero_apply] at hp
    rw [hp, zero_smul]
  · have hsm₀ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (0 : ℝ → M → ℝ)) :=
      contMDiff_const
    have hN := contMDiffAt_plumbedPerturbation_family (Ha := Pi.single inf G)
      (Hb := Pi.single q G) hq ((forall_update_iff _ fun _ f => Periodic f 1).2
        ⟨hG, fun _ _ _ => rfl⟩)
      ((forall_update_iff _ fun _ f => Periodic f 1).2 ⟨hG, fun _ _ _ => rfl⟩)
      ((forall_update_iff _ fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
        ⟨hGs, fun _ _ => hsm₀⟩)
      ((forall_update_iff _ fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
        ⟨hGs, fun _ _ => hsm₀⟩)
      (by simp) hL hw x
    have hN' : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
        (fun p : (ℝ × ℝ) × (ℂ × M) =>
          plumbedPerturbation (Pi.single inf G) (Pi.single q G) q p.1.1 p.2.1 p.2.2)
        ((L, τ), (w, x)) :=
      hN.comp ((L, τ), (w, x))
        ((contDiff_fst.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
    -- Scalar multiplication is a smooth map on `ℝ × (ℂ →L[ℝ] ℝ)`.
    exact contDiff_smul.contMDiff.contMDiffAt.comp ((L, τ), (w, x))
      (((hφ.comp contDiff_snd).contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk_space hN')

/-- **The family is smooth.** For period-one Hamiltonians `H i`, `Hout`, `G` and `G'` of class
`C^n` on `ℝ × M`, the associativity family is `C^n` jointly in the neck length `L`, the parameter
`τ`, the domain point `w` and the target point, at every `L > 4` and every `w` other than the
three input punctures of the configuration at `τ`. -/
theorem contMDiffAt_associativityPerturbation {n : ℕ∞} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry Hout))
    (hG : Periodic G 1) (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry G))
    (hG' : Periodic G' 1) (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry G'))
    (hL : 4 < L) {w : ℂ}
    (hw : ∀ i, w ≠ associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℝ × ℝ) × (ℂ × M) => associativityPerturbation H Hout G G' p.1.1 p.1.2 p.2.1 p.2.2)
      ((L, τ), (w, x)) := by
  -- The moving input ends follow the associativity path of plumbing factor `e^{-2πL} / 4`.
  have hfac : ContDiff ℝ n fun q : ℝ × ℝ => (Real.exp (-(2 * π * q.1)) / 4, q.2) := by
    fun_prop
  have hS := (contMDiffAt_puncturedSpherePerturbation_associativity hH hHs hHout hHouts
    (by positivity) hw x).comp ((L, τ), (w, x))
    ((hfac.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk contMDiffAt_snd)
  -- The neck of `(x₁ x₂) x₃` is switched off for `τ ≥ 0`; before, the punctures are `0, ψ₀(1), 1`.
  have hN : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℝ × ℝ) × (ℂ × M) => smoothTransition (-p.1.2) •
        plumbedPerturbation (Pi.single inf G) (Pi.single zero G) zero p.1.1 p.2.1 p.2.2)
      ((L, τ), (w, x)) := by
    refine contMDiffAt_smul_neck (φ := fun t => smoothTransition (-t)) (by decide) hG hGs hL
      (smoothTransition.contDiff.comp contDiff_neg) ?_ x
    rcases le_or_gt τ 0 with hτ | hτ
    · have hc := associativityCenter_eq_plumbingMap_of_nonpos (L := L) hτ
      refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
      · simpa [hc] using hw 0
      · simpa [hc] using hw 2
      · simpa [hc] using hw 1
    · left
      filter_upwards [lt_mem_nhds hτ] with t ht
      exact smoothTransition.zero_of_nonpos (by linarith)
  -- The neck of `x₁ (x₂ x₃)` is switched off for `τ ≤ 1`; after, the punctures are `1, ψ₁(1), 0`.
  have hN' : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : (ℝ × ℝ) × (ℂ × M) => smoothTransition (p.1.2 - 1) •
        plumbedPerturbation (Pi.single inf G') (Pi.single one G') one p.1.1 p.2.1 p.2.2)
      ((L, τ), (w, x)) := by
    refine contMDiffAt_smul_neck (φ := fun t => smoothTransition (t - 1)) (by decide) hG' hG's hL
      (smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)) ?_ x
    rcases le_or_gt 1 τ with hτ | hτ
    · have hc (j : Fin 3) :
          w ≠ (![one.endCenter, one.plumbingMap L 1, zero.endCenter] : Fin 3 → ℂ) j := by
        rw [← congrFun (associativityCenter_comp_finRotate_of_one_le hτ) j]
        exact hw _
      refine Or.inr ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using hc 2
      · simpa using hc 0
      · simpa using hc 1
    · left
      filter_upwards [gt_mem_nhds hτ] with t ht
      exact smoothTransition.zero_of_nonpos (by linarith)
  simp only [associativityPerturbation_def]
  exact (hS.add hN).add hN'

end Manifold

section SmoothProd

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {H : Fin 3 → ℝ → V → ℝ}
  {Hout G G' : ℝ → V → ℝ}

/-- Off the three input punctures of the configuration at `τ`, the components of the associativity
family on a normed space are `C^n` jointly in the domain point, in real coordinates, and the target
point, for period-one `C^n` Hamiltonians and neck length `L > 4`. -/
theorem contDiffAt_uncurry_associativityPerturbation {n : ℕ∞} (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContDiff ℝ n (uncurry (H i))) (hHout : Periodic Hout 1)
    (hHouts : ContDiff ℝ n (uncurry Hout)) (hG : Periodic G 1) (hGs : ContDiff ℝ n (uncurry G))
    (hG' : Periodic G' 1) (hG's : ContDiff ℝ n (uncurry G')) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : ∀ i, Complex.equivRealProdCLM.symm z ≠
      associativityCenter (Real.exp (-(2 * π * L)) / 4) τ i) (x : V) (v : ℂ) :
    ContDiffAt ℝ n
      (uncurry fun z x ↦
        associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x v)
      (z, x) := by
  have h := contMDiffAt_associativityPerturbation (I := 𝓘(ℝ, V)) hH
    (fun i ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hHout
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff) hG
    (contMDiff_prod_modelWithCornersSelf_iff.2 hGs.contMDiff) hG'
    (contMDiff_prod_modelWithCornersSelf_iff.2 hG's.contMDiff) hL hz x
  -- Freeze the neck length and the parameter.
  have hg : ContMDiffAt 𝓘(ℝ, ℂ × V) (𝓘(ℝ, ℝ × ℝ).prod (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V))) n
      (fun p : ℂ × V ↦ ((L, τ), (p.1, p.2))) (Complex.equivRealProdCLM.symm z, x) :=
    contMDiffAt_const.prodMk (contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff).contMDiffAt
  have hp : ContDiffAt ℝ n
      (fun p : ℂ × V ↦ associativityPerturbation H Hout G G' L τ p.1 p.2)
      (Complex.equivRealProdCLM.symm z, x) := (h.comp _ hg).contDiffAt
  exact (hp.comp (f := fun p : (ℝ × ℝ) × V ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).clm_apply contDiffAt_const

end SmoothProd

end TauCeti.Floer

/-! ### Curvature -/

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory

variable {E E' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace E']
  {I : ModelWithCorners ℝ E E'} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold I ⊤ M]
  {H : Fin 3 → ℝ → M → ℝ} {Hout G G' : ℝ → M → ℝ} {L : ℝ}

/-- The two copies of a neck Hamiltonian scaled by `β ∈ [0, 1]` are absorbed into twice any
bound `c` of the unscaled neck. -/
private theorem add_ofReal_abs_smoothTransition_mul_le (a : ENNReal) {b : ℝ} {c : ENNReal}
    (hb : 0 ≤ b) (s : ℝ) (hc : ENNReal.ofReal b ≤ c) :
    a + (ENNReal.ofReal (|smoothTransition s| * b) +
      ENNReal.ofReal (|smoothTransition s| * b)) ≤ a + 2 * c := by
  have hβ := (smoothTransition.ofReal_abs_mul_le s hb).trans hc
  rw [two_mul]
  exact add_le_add le_rfl (add_le_add hβ hβ)

/-- Before the path, the family is the plumbed datum of `(x₁ x₂) x₃` with a scaled neck, whose
curvature bound is that of the plumbed datum. -/
private theorem lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le_of_neg
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout))
    (hG : Periodic G 1) (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G))
    (hL : 4 < L) {τ : ℝ} (hτ : τ < 0) {B : Fin 3 → ℝ} {Bout BG BG' : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    (hBG : ∀ t x, |G t x| ≤ BG) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤
      ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout +
        2 * (ENNReal.ofReal BG + ENNReal.ofReal BG') := by
  rw [associativityPerturbation_eq_left (by linarith) hτ.le]
  refine (ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_update_smul_le
    (q := zero) (Ha := associativityLeftInserted H G) (Hb := associativityLeftReceiving H Hout G)
    (by decide)
    (fun p hp => by cases p <;> simp_all)
    (fun p hp => by cases p <;> simp_all) hG
    (fun p hp => by cases p <;> simp_all)
    (fun p hp => by cases p <;> simp_all) hGs hL
    (smoothTransition (-τ))
    (Ba := fun p => match p with | zero => B 0 | one => B 1 | inf => 0)
    (Bb := fun p => match p with | zero => 0 | one => B 2 | inf => Bout)
    (fun p hp => by cases p <;> simp_all)
    (fun p hp => by cases p <;> simp_all) hBG u).trans ?_
  simp only [Puncture.sum_univ, Fin.sum_univ_three, update_apply, reduceCtorEq, ite_false,
    ite_true]
  exact (le_of_eq (by ring)).trans (add_ofReal_abs_smoothTransition_mul_le _
    ((abs_nonneg _).trans (hBG 0 (u 0))) (-τ) le_self_add)

/-- After the path, the family is the plumbed datum of `x₁ (x₂ x₃)` with a scaled neck, whose
curvature bound is that of the plumbed datum. -/
private theorem lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le_of_one_lt
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout))
    (hG' : Periodic G' 1) (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G'))
    (hL : 4 < L) {τ : ℝ} (hτ : 1 < τ) {B : Fin 3 → ℝ} {Bout BG BG' : ℝ}
    (hB : ∀ i t x, |H i t x| ≤ B i) (hBout : ∀ t x, |Hout t x| ≤ Bout)
    (hBG' : ∀ t x, |G' t x| ≤ BG') (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤
      ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout +
        2 * (ENNReal.ofReal BG + ENNReal.ofReal BG') := by
  rw [associativityPerturbation_eq_right (by linarith) hτ.le]
  refine (ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_update_smul_le
    (q := one) (Ha := associativityRightInserted H G')
    (Hb := associativityRightReceiving H Hout G') (by decide)
    (fun p hp => by cases p <;> simp_all)
    (fun p hp => by cases p <;> simp_all) hG'
    (fun p hp => by cases p <;> simp_all)
    (fun p hp => by cases p <;> simp_all) hG's hL
    (smoothTransition (τ - 1))
    (Ba := fun p => match p with | zero => B 1 | one => B 2 | inf => 0)
    (Bb := fun p => match p with | zero => B 0 | one => 0 | inf => Bout)
    (fun p hp => by cases p <;> simp_all)
    (fun p hp => by cases p <;> simp_all) hBG' u).trans ?_
  simp only [Puncture.sum_univ, Fin.sum_univ_three, update_apply, reduceCtorEq, ite_false,
    ite_true]
  exact (le_of_eq (by ring)).trans (add_ofReal_abs_smoothTransition_mul_le _
    ((abs_nonneg _).trans (hBG' 0 (u 0))) (τ - 1) le_add_self)

/-- **The integrated curvature of the associativity family is bounded uniformly.** For period-one
`C¹` Hamiltonians `H i`, `Hout`, `G` and `G'` on a manifold `M` with a two-form `ω`, bounded by
`|H i| ≤ B i`, `|Hout| ≤ Bout`, `|G| ≤ BG` and `|G'| ≤ BG'`, and a neck length `L > 4`, the
integral of `|R_K|` along any map for the member `K` of the family at any `τ` is at most
`∑ i, B i + Bout + 2 (BG + BG')`. -/
theorem lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout))
    (hG : Periodic G 1) (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G))
    (hG' : Periodic G' 1) (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G'))
    (hL : 4 < L) (τ : ℝ) {B : Fin 3 → ℝ} {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG)
    (hBG' : ∀ t x, |G' t x| ≤ BG') (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤
      ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout +
        2 * (ENNReal.ofReal BG + ENNReal.ofReal BG') := by
  rcases lt_or_ge τ 0 with hτ | hτ₀
  · exact lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le_of_neg ω hH hHs hHout
      hHouts hG hGs hL hτ hB hBout hBG u
  rcases le_or_gt τ 1 with hτ₁ | hτ
  · -- Along the path, the family is the datum of the moving input ends.
    obtain ⟨hf₀, hf₃⟩ :=
      exp_neg_two_pi_mul_div_four_pos_and_three_mul_le_one (show 0 ≤ L by linarith)
    rw [associativityPerturbation_of_mem_Icc ⟨hτ₀, hτ₁⟩]
    exact (ω.lintegral_enorm_hamiltonianCurvature_puncturedSpherePerturbation_associativity_le hH
      hHs hHout hHouts hf₀ hf₃ τ hB hBout u).trans le_self_add
  · exact lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le_of_one_lt ω hH hHs
      hHout hHouts hG' hG's hL hτ hB hBout hBG' u

/-- **The integrated curvature of the associativity family is bounded uniformly over every
region.** Under the hypotheses of
`SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le`, the integral of
the curvature of the member of the family at any `τ` along any map, over any region `s`, is at most
`∑ i, B i + Bout + 2 (BG + BG')` in absolute value. -/
theorem abs_setIntegral_hamiltonianCurvature_associativityPerturbation_le
    (ω : SmoothTwoForm I M) (hH : ∀ i, Periodic (H i) 1)
    (hHs : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry Hout))
    (hG : Periodic G 1) (hGs : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G))
    (hG' : Periodic G' 1) (hG's : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry G'))
    (hL : 4 < L) (τ : ℝ) {B : Fin 3 → ℝ} {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG)
    (hBG' : ∀ t x, |G' t x| ≤ BG') (u : ℝ × ℝ → M) (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)| ≤ ∑ i, B i + Bout + 2 * (BG + BG') := by
  have hB₀ (i : Fin 3) : 0 ≤ B i := (abs_nonneg _).trans (hB i 0 (u 0))
  have hBout₀ : 0 ≤ Bout := (abs_nonneg _).trans (hBout 0 (u 0))
  have hBG₀ : 0 ≤ BG := (abs_nonneg _).trans (hBG 0 (u 0))
  have hBG'₀ : 0 ≤ BG' := (abs_nonneg _).trans (hBG' 0 (u 0))
  have hsum₀ : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ ↦ hB₀ i
  rw [← ENNReal.ofReal_le_ofReal_iff (by positivity), ← Real.eNorm_eq_ofReal_abs]
  refine (eNorm_integral_le_lintegral_eNorm _).trans ((setLIntegral_le_lintegral _ _).trans
    ((ω.lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le hH hHs hHout hHouts hG
      hGs hG' hG's hL τ hB hBout hBG hBG' u).trans_eq ?_))
  -- The bound is the image under `ENNReal.ofReal` of the sum of the nonnegative real bounds.
  simp [ENNReal.ofReal_add, ENNReal.ofReal_mul, ENNReal.ofReal_sum_of_nonneg, add_nonneg, hB₀,
    hBout₀, hBG₀, hBG'₀, hsum₀]

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Fin 3 → ℝ → V → ℝ} {Hout G G' : ℝ → V → ℝ} {L : ℝ}

/-- **The integrated curvature of the associativity family is bounded uniformly**, for a
symplectic vector space target. For period-one `C¹` Hamiltonians `H i`, `Hout`, `G` and `G'`
bounded by `|H i| ≤ B i`, `|Hout| ≤ Bout`, `|G| ≤ BG` and `|G'| ≤ BG'`, and a neck length `L > 4`,
the integral of `|R_K|` along any map for the member `K` of the family at any `τ` is at most
`∑ i, B i + Bout + 2 (BG + BG')`. -/
theorem lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le (ω : SymplecticForm V)
    (hH : ∀ i, Periodic (H i) 1) (hHs : ∀ i, ContDiff ℝ 1 (uncurry (H i)))
    (hHout : Periodic Hout 1) (hHouts : ContDiff ℝ 1 (uncurry Hout)) (hG : Periodic G 1)
    (hGs : ContDiff ℝ 1 (uncurry G)) (hG' : Periodic G' 1) (hG's : ContDiff ℝ 1 (uncurry G'))
    (hL : 4 < L) (τ : ℝ) {B : Fin 3 → ℝ} {Bout BG BG' : ℝ} (hB : ∀ i t x, |H i t x| ≤ B i)
    (hBout : ∀ t x, |Hout t x| ≤ Bout) (hBG : ∀ t x, |G t x| ≤ BG)
    (hBG' : ∀ t x, |G' t x| ≤ BG') (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ associativityPerturbation H Hout G G' L τ (Complex.equivRealProdCLM.symm z) x
          Complex.I) z (u z)‖ₑ ≤
      ∑ i, ENNReal.ofReal (B i) + ENNReal.ofReal Bout +
        2 * (ENNReal.ofReal BG + ENNReal.ofReal BG') := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_associativityPerturbation_le hH
    (fun i ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs i).contMDiff) hHout
    (contMDiff_prod_modelWithCornersSelf_iff.2 hHouts.contMDiff) hG
    (contMDiff_prod_modelWithCornersSelf_iff.2 hGs.contMDiff) hG'
    (contMDiff_prod_modelWithCornersSelf_iff.2 hG's.contMDiff) hL τ hB hBout hBG hBG' u

end TauCeti.SymplecticForm
