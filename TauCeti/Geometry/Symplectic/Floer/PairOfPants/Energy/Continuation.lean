/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# The energy of pairs of pants with continuation necks

Pair-of-pants products for two choices of end Hamiltonians are compared by the one-parameter
families of pairs of pants with continuation necks on their ends: the perturbation
`K = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L` on `S = ℂ ∖ {0, 1}` interpolates,
on each end `q`, from the inner Hamiltonian `G_q` to the outer Hamiltonian `H_q` across a neck at
the signed longitudinal coordinate `L_q`. As the neck positions move, the counts of rigid members
of such a family form the kernel of a chain homotopy between the two compositions of continuation
maps with pair-of-pants products, and that kernel has to satisfy a potential bound uniform in the
neck positions. This file does not construct the moduli spaces or their counts. It proves, for a
symplectic vector space target `(V, ω)`, the energy identity of the family and the action bound
for individual Floer solutions, uniformly in the neck positions, from which such a potential bound
follows.

Far out on each end, where the signed coordinate `±s` is at least `2` and at least `L_q + 1`, the
datum is `H_q(t) dt`, the pair-of-pants perturbation of the outer Hamiltonians `H`
(`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le`). So the two
data agree outside a compact part of `S`, and its curvature vanishes there
(`SymplecticForm.hamiltonianCurvature_pairOfPantsContinuationPerturbation_eq_zero_of_lt`). By the
pointwise energy identity, the energy plus the integrated curvature over a compact region does not
change when the datum is changed inside it
(`TauCeti.SymplecticForm.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`).
Comparing with the energy identity of the pair of pants in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action` therefore gives, for a map `u` which is `C²`
on `S` and every `R ≥ 2` with `R ≥ L_q + 1` for all `q`,

`∫_{S_R} E = A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ_∞) - ∫_S R_K(u)`

(`integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_eq_sum`),
where `ℓ_q(t) = u(φ_q(±R + i t))` are the loops on the boundary circles of the truncation `S_R` and
`A_H` is the Hamiltonian action. The curvature bound of the family,
`|∫ R_K(u)| ≤ ∑ q, (B_q + D_q)` for `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, does not depend on
the neck positions. For a solution of the Floer equation with tamed almost complex structures the
energy is nonnegative, which gives the action bound

`A_{H_∞}(ℓ_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) + ∑ q, (B_q + D_q)`

on every such truncation
(`SymplecticForm.hamiltonianAction_le_add_add_sum_of_pairOfPantsContinuationPerturbation`) and, in
the limit, `a_∞ ≤ a_0 + a_1 + ∑ q, (B_q + D_q)` for the limiting actions of the ends
(`SymplecticForm.le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation`).
The constant is the same for all neck positions `L`, although the necks become arbitrarily long.

Beyond the single height `2 + ∑ q, |L_q|` the datum is `H_q(t) dt` on every end, so the energy
identity of `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity` also applies to it on
the whole of `S`. For a solution `u` of the Floer equation with tame almost complex structures
whose end loops have actions converging to `a_q`, the energy is
`E(u) = a_0 + a_1 - a_∞ - ∫_S R_K(u)`
(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq`), and
`E(u) ≤ a_0 + a_1 - a_∞ + ∑ q, (B_q + D_q)`
(`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`), whatever
the neck positions.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {G H : Puncture → ℝ → V → ℝ}
  {L : Puncture → ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Near a point of `S` beyond the neck and the collar of some end, the components of the
perturbation with continuation necks agree with those of the pair-of-pants perturbation of the
outer Hamiltonians. -/
private theorem pairOfPantsContinuationPerturbation_eventuallyEq {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) {r : Puncture}
    (h₂ : 2 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (hL : L r + 1 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re) (v : ℂ) :
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x v)
      =ᶠ[𝓝 z] fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v := by
  have hc : ContinuousAt
      (fun z : ℝ × ℝ ↦ r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re) z :=
    continuousAt_const.mul ((r.contDiffAt_re_endCoord (n := 0)
      (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) r)).continuousAt.comp
        Complex.equivRealProdCLM.symm.continuous.continuousAt)
  filter_upwards [hc.eventually (lt_mem_nhds h₂), hc.eventually (lt_mem_nhds hL)] with w hw₂ hwL
  funext x
  rw [pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le hw₂.le hwL.le]

/-- **The curvature vanishes beyond the necks.** At a point of `S` where the signed longitudinal
coordinate of some end `r` is greater than `2` and greater than `L_r + 1`, the perturbation with
continuation necks is `H_r(t) dt` in the coordinates of that end, and its curvature vanishes.
Together with the vanishing of the perturbation on the core, this confines the curvature to a
compact part of `S`, which grows with the neck positions. -/
theorem hamiltonianCurvature_pairOfPantsContinuationPerturbation_eq_zero_of_lt
    [FiniteDimensional ℝ V] (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {z : ℝ × ℝ} (hz : z ∈ thricePuncturedSphereReal)
    {r : Puncture} (h₂ : 2 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (hL : L r + 1 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re) (x : V) :
    ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z x = 0 := by
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq
    (pairOfPantsContinuationPerturbation_eventuallyEq hz h₂ hL 1)
    (pairOfPantsContinuationPerturbation_eventuallyEq hz h₂ hL Complex.I)]
  exact ω.hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt hH hHs
    (mem_thricePuncturedSphereReal_iff.1 hz) h₂ x

variable [FiniteDimensional ℝ V]

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- On `S` outside a truncation `S_R` with `R ≥ 2` and `R ≥ L_q + 1` for all `q`, the perturbation
with continuation necks is the pair-of-pants perturbation of the outer Hamiltonians. -/
private theorem eqOn_pairOfPantsContinuationPerturbation {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) (v : ℂ) :
    EqOn
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x v)
      (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal \ Complex.equivRealProdCLM.symm ⁻¹' truncation R) := by
  intro z hz
  obtain ⟨q, hq⟩ := exists_lt_endSign_mul_re_endCoord_of_notMem_truncation hz.1 hz.2
  funext x
  exact congrArg (· v) (pairOfPantsContinuationPerturbation_eq_pairOfPantsPerturbation_of_le
    (G := G) (L := L) (by linarith) (by linarith [hRL q]) x)

/-- **The energy identity on a truncated pair of pants with continuation necks, in terms of
actions.** Let `K` be the pair-of-pants perturbation with continuation necks at the positions
`L_q` from period-one `C¹` inner Hamiltonians `G_q` to outer Hamiltonians `H_q`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`, and let
`u` be a map which is `C²` on `S = ℂ ∖ {0, 1}`. For `R ≥ 2` with `R ≥ L_q + 1` for every end `q`,
the Floer energy of `u` over the truncation `S_R` is the signed sum of the actions, for the outer
Hamiltonians, of the loops `ℓ_q(t) = u(φ_q(±R + i t))` along its three boundary circles, minus the
integrated curvature over `S`:

`∫_{S_R} E = ∑ q, ±A_{H_q}(ℓ_q) - ∫_S R_K(u)`,

with the sign `+` on the input ends `0` and `1` and `-` on the output end `∞`. -/
theorem integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_eq_sum
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∑ q, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z (u z) := by
  -- Outside `S_R` the datum is the pair-of-pants datum of `H`, so the energy plus the integrated
  -- curvature over `S_R` is the same for both data.
  have hC {K : ℂ → V → ℂ →L[ℝ] ℝ}
      (hK : ∀ z ∈ thricePuncturedSphereReal, ∀ x v, ContDiffAt ℝ 1
        (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v) (z, x)) (v : ℂ) :
      ContDiffOn ℝ 1 (uncurry fun z x ↦ K (Complex.equivRealProdCLM.symm z) x v)
        (thricePuncturedSphereReal ×ˢ univ) :=
    fun p hp ↦ (hK p.1 hp.1 p.2 v).contDiffWithinAt
  have hKc := fun z (hz : z ∈ thricePuncturedSphereReal) x v ↦
    contDiffAt_uncurry_pairOfPantsContinuationPerturbation (n := 1) hG hH hGs hHs L hz x v
  have hKp := fun z (hz : z ∈ thricePuncturedSphereReal) x v ↦
    contDiffAt_uncurry_pairOfPantsPerturbation (n := 1) hH hHs hz x v
  have hcomp := ω.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn
    isOpen_thricePuncturedSphereReal (hu.of_le one_le_two) (hC hKc 1) (hC hKc Complex.I)
    (hC hKp 1) (hC hKp Complex.I)
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R))
    (preimage_truncation_subset_thricePuncturedSphereReal R)
    (eqOn_pairOfPantsContinuationPerturbation hR hRL 1)
    (eqOn_pairOfPantsContinuationPerturbation hR hRL Complex.I) (u := u)
    (D := Complex.equivRealProdCLM.symm ⁻¹' truncation R)
  -- Both curvatures vanish on `S` outside `S_R`.
  have hRc := setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation (R := R)
    (f := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z)) fun z hz q hq ↦
      hamiltonianCurvature_pairOfPantsContinuationPerturbation_eq_zero_of_lt ω hH hHs hz
        (by linarith) (by linarith [hRL q]) _
  have hRp := setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation (R := R)
    (f := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z)) fun z hz q hq ↦
      hamiltonianCurvature_pairOfPantsPerturbation_eq_zero_of_two_lt ω hH hHs
        (mem_thricePuncturedSphereReal_iff.1 hz) (by linarith) _
  have hP := integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction
    ω hH hHs hu hR
  beta_reduce at hRc hRp
  rw [hRc]
  rw [← thricePuncturedSphereReal, hRp] at hP
  linarith

/-- **The energy and the actions on a truncated pair of pants with continuation necks.** If
`|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, then for every `R ≥ 2` with `R ≥ L_q + 1` for all
`q`, the Floer energy of `u` over the truncation `S_R` differs from the signed sum
`A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) - A_{H_∞}(ℓ_∞)` of the actions of its boundary loops by at most
`∑ q, (B_q + D_q)`, uniformly in `R` and in the neck positions. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_sub_sum_le
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ∑ q, q.endSign * ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))| ≤ ∑ q, (B q + D q) := by
  rw [integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_eq_sum
    ω hG hH hGs hHs hu hR hRL, sub_sub_cancel_left, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs hHs
    hGB hHB hD L u _

/-- **The action bound on a truncated pair of pants with continuation necks.** Let `u` be a map
which is `C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation `(du - X_K)^{0,1} = 0` on the
truncation `S_R` for almost complex structures `J(z)` tamed by `ω`, where `K` is the pair-of-pants
perturbation with continuation necks at the positions `L_q` from period-one `C¹` Hamiltonians `G_q`
to `H_q`, with `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`. If `R ≥ 2` and `R ≥ L_q + 1` for all
`q`, then the loops `ℓ_q(t) = u(φ_q(±R + i t))` on the boundary of `S_R` satisfy

`A_{H_∞}(ℓ_∞) ≤ A_{H_0}(ℓ_0) + A_{H_1}(ℓ_1) + ∑ q, (B_q + D_q)`.

The constant does not depend on the neck positions. -/
theorem hamiltonianAction_le_add_add_sum_of_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑R + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑R + ↑t * Complex.I)))) + ∑ q, (B q + D q) := by
  -- The energy over `S_R` is nonnegative, and it is the signed sum of the actions minus the
  -- integrated curvature, which is at least `-∑ q, (B_q + D_q)`.
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_truncation R) fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  rw [integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_eq_sum
    ω hG hH hGs hHs hu hR hRL] at hE
  have hC := (abs_le.1 (abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le
    ω hG hH hGs hHs hGB hHB hD L u thricePuncturedSphereReal)).1
  simp only [sum_univ, endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul] at hE hC ⊢
  linarith

/-- **The action bound for a pair of pants with continuation necks.** Let `u` be a map which is
`C²` on `S = ℂ ∖ {0, 1}` and solves the Floer equation on `S` for almost complex structures tamed
by `ω`, for the pair-of-pants perturbation with continuation necks at the positions `L_q` from
period-one `C¹` Hamiltonians `G_q` to `H_q`, with `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`.
If the actions `A_{H_q}` of the loops `ℓ_q(t) = u(φ_q(±R + i t))` converge to `a_q` as `R → ∞`,
then

`a_∞ ≤ a_0 + a_1 + ∑ q, (B_q + D_q)`.

This is the limit `R → ∞` of
`SymplecticForm.hamiltonianAction_le_add_add_sum_of_pairOfPantsContinuationPerturbation`; the
constant does not depend on the neck positions. -/
theorem le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal) {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun R ↦ ω.hamiltonianAction (H q) (fun t ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) atTop (𝓝 (a q))) :
    a inf ≤ a zero + a one + ∑ q, (B q + D q) := by
  -- The truncated bound holds for all large `R`.
  have hev : ∀ᶠ R in atTop, ω.hamiltonianAction (H inf) (fun t ↦ u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(inf.endSign * R) + ↑t * Complex.I)))) ≤
      ω.hamiltonianAction (H zero) (fun t ↦ u (Complex.equivRealProdCLM
          (zero.cylindricalEndLift (↑(zero.endSign * R) + ↑t * Complex.I)))) +
        ω.hamiltonianAction (H one) (fun t ↦ u (Complex.equivRealProdCLM
          (one.cylindricalEndLift (↑(one.endSign * R) + ↑t * Complex.I)))) +
        ∑ q, (B q + D q) := by
    filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop (∑ q, |L q| + 1)] with R hR hRL
    have hRL' (q : Puncture) : L q + 1 ≤ R := by
      have := Finset.single_le_sum (f := fun q : Puncture ↦ |L q|) (fun q _ ↦ abs_nonneg _)
        (Finset.mem_univ q)
      linarith [le_abs_self (L q)]
    simpa only [endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul,
      Complex.ofReal_neg] using
      hamiltonianAction_le_add_add_sum_of_pairOfPantsContinuationPerturbation ω hG hH hGs hHs hGB
        hHB hD hu hR hRL'
        (fun z hz ↦ hJ z (preimage_truncation_subset_thricePuncturedSphereReal R hz))
        fun z hz ↦ hfloer z (preimage_truncation_subset_thricePuncturedSphereReal R hz)
  exact le_of_tendsto_of_tendsto (ha inf) (((ha zero).add (ha one)).add_const _) hev

section WholeEnergy

variable {u : ℝ × ℝ → V}

/-- **The energy identity for the pair of pants with continuation necks.** Let `K` be the
pair-of-pants perturbation with continuation necks at the positions `L_q` from period-one `C¹`
inner Hamiltonians `G_q` to outer Hamiltonians `H_q`, and let `u` be a `C²` map from
`S = ℂ ∖ {0, 1}` to a symplectic vector space which solves the Floer equation
`(du - X_K)^{0,1} = 0` on `S` for almost complex structures `J(z)` tamed by `ω`, and whose
curvature term `R_K(u)` is integrable. If on each end `q` the actions `A_{H_q}` of the loops
`t ↦ u(φ_q(s, t))` tend to `a_q` as `±s → ∞`, then the energy of `u` is

`E(u) = a_0 + a_1 - a_∞ - ∫ R_K(u)`. -/
theorem lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (L : Puncture → ℝ) (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) =
      ENNReal.ofReal (∑ q, q.endSign * a q - ∫ z, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) :=
  lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm ω
    (fun _ hz x v ↦ contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH hGs hHs L hz x v)
    (fun _ _ x hw ↦ pairOfPantsContinuationPerturbation_eq_smul_endAngularForm_of_le hw x) hH
    (fun q ↦ (hHs q).continuous) hu
    (fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)) hR ha

/-- **The energy bound for the pair of pants with continuation necks.** Under the hypotheses of
`SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq`, without the
integrability of the curvature, if `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, then the energy
of `u` is at most `a_0 + a_1 - a_∞ + ∑ q, (B_q + D_q)`, whatever the neck positions. -/
theorem lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) (L : Puncture → ℝ)
    (hu : ContDiffOn ℝ 2 u thricePuncturedSphereReal)
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, ω.Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    {a : Puncture → ℝ}
    (ha : ∀ q, Tendsto (fun σ ↦ ω.hamiltonianAction (H q)
      (fun t ↦ u (endChart q (q.endSign * σ, t)))) atTop (𝓝 (a q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≤
      ENNReal.ofReal (∑ q, q.endSign * a q + ∑ q, (B q + D q)) := by
  rw [lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq ω hG hH hGs hHs L hu hJ
    hfloer (integrable_hamiltonianCurvature_pairOfPantsContinuationPerturbation ω hG hH hGs hHs hGB
      hHB hD L hu.continuousOn) ha]
  refine ENNReal.ofReal_le_ofReal (sub_le_iff_le_add.2 ?_)
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z)), abs_integral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs
    hHs hGB hHB hD L u]

end WholeEnergy

end TauCeti.SymplecticForm
