/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Asymptotic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Identity
import TauCeti.Geometry.Manifold.ContMDiff.Prod
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
neck positions. This file does not construct the moduli spaces or their counts. It proves the
energy identity of the family and the action bound for individual Floer solutions, uniformly in the
neck positions, from which such a potential bound follows, first for a symplectic vector space
target `(V, ω)` and then for a manifold target.

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

The same comparison works for a finite-dimensional manifold `M` with a nondegenerate two-form `ω`,
such as a closed symplectic manifold, and a map `u` which is only `C¹` on `S`. Without caps for the
boundary loops the area `∫ u^*ω` is not a difference of actions, so the identity keeps it, as the
manifold energy identity of the pair of pants
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`)
does: for `R ≥ 2` with `R ≥ L_q + 1` for all `q`,

`∫_{S_R} E = ∫_{S_R} u^*ω + ∑ q, ±∫₀¹ H_q(t, ℓ_q(t)) dt - ∫_S R_K(u)`

(`IsNondegenerate.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation`, in
the namespace `SmoothTwoForm`). The integrability of the energy density, which the comparison
needs, follows from that of the curvature
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsContinuationPerturbation`).
For a solution of the Floer equation with tamed almost complex structures the right-hand side
without the curvature term is at least `-∑ q, (B_q + D_q)`, on every such truncation and, letting
`R → ∞`, for the asymptotic loops `x_q` of the ends
(`IsNondegenerate.neg_sum_le_integral_add_sum_of_pairOfPantsContinuationPerturbation`, in the
namespace `SmoothTwoForm`).

Since the datum is `H_q(t) dt` beyond a single height on every end, the energy identity for data
cylindrical on the ends
(`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm`) also
gives the energy of a Floer solution as an extended integral, assuming only that the area density
is integrable and that the integrals `∫₀¹ H_q(t, u(φ_q(s, t))) dt` of the outer Hamiltonians
along the end loops tend to limits `h_q`: then `E(u) = ∫ u^*ω + h_0 + h_1 - h_∞ - ∫_S R_K(u)` and
`E(u) ≤ ∫ u^*ω + h_0 + h_1 - h_∞ + ∑ q, (B_q + D_q)`, whatever the neck positions
(`IsNondegenerate.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq` and
`IsNondegenerate.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`, in the
namespace `SmoothTwoForm`).

## Main results

* `integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_eq_sum`,
  `hamiltonianAction_le_add_add_sum_of_pairOfPantsContinuationPerturbation` and
  `le_add_add_sum_of_tendsto_hamiltonianAction_pairOfPantsContinuationPerturbation`, in the
  namespace `SymplecticForm`: the energy identity in terms of actions and the action bounds, for a
  symplectic vector space target.
* `lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq` and
  `lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`, in the namespace
  `SymplecticForm`: the energy identity and the energy bound on the whole of `S` for a Floer
  solution, for a symplectic vector space target.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation`
  and its truncated version: the energy identity for a manifold target.
* `IsNondegenerate.abs_integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_sub_le`,
  in the namespace `SmoothTwoForm`, and its truncated version: the energy differs from its
  topological part by at most `∑ q, (B_q + D_q)`, for a manifold target.
* `SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_pairOfPantsContinuationPerturbation`
  and its truncated version: the lower bound on the topological energy of a Floer solution, for a
  manifold target, uniform in the neck positions.
* `IsNondegenerate.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq` and
  `IsNondegenerate.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`, in the
  namespace `SmoothTwoForm`: the energy identity and the energy bound of a Floer solution, for a
  manifold target, in terms of the limits of the end integrals.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold

namespace TauCeti.Floer

variable {X : Type*} {G H : Puncture → ℝ → X → ℝ} {L : Puncture → ℝ}

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

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace F]
  {I : ModelWithCorners ℝ E F} [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ⊤ M]
  {G H : Puncture → ℝ → M → ℝ} {L : Puncture → ℝ}

/-- **The curvature vanishes beyond the necks, for a manifold target.** At a point of `S` where the
signed longitudinal coordinate of some end `r` is greater than `2` and greater than `L_r + 1`, the
perturbation with continuation necks is `H_r(t) dt` in the coordinates of that end, and its
curvature vanishes. -/
theorem hamiltonianCurvature_pairOfPantsContinuationPerturbation_eq_zero_of_lt
    (ω : SmoothTwoForm I M) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) {r : Puncture}
    (h₂ : 2 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re)
    (hL : L r + 1 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re) (x : M) :
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

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {G H : Puncture → ℝ → V → ℝ}
  {L : Puncture → ℝ}

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
  simpa using ω.constSmooth.hamiltonianCurvature_pairOfPantsContinuationPerturbation_eq_zero_of_lt
    hH (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hz h₂ hL x

variable [FiniteDimensional ℝ V]

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
    (isCompact_preimage_truncation R)
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
        (by linarith) _
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
    filter_upwards [eventually_ge_atTop 2,
      Filter.eventually_all.2 fun q ↦ eventually_ge_atTop (L q + 1)] with R hR hRL
    simpa only [endSign_zero, endSign_one, endSign_inf, one_mul, neg_one_mul,
      Complex.ofReal_neg] using
      hamiltonianAction_le_add_add_sum_of_pairOfPantsContinuationPerturbation ω hG hH hGs hHs hGB
        hHB hD hu hR hRL
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

/-! ### Manifold targets -/

namespace TauCeti.SmoothTwoForm

open Floer

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace F]
  {I : ModelWithCorners ℝ E F} [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ⊤ M]
  {G H : Puncture → ℝ → M → ℝ} {L : Puncture → ℝ}

variable [FiniteDimensional ℝ E] {ω : SmoothTwoForm I M}

namespace IsNondegenerate

/-- **The energy identity on a truncated pair of pants with continuation necks, for a manifold
target.** Let `K` be the pair-of-pants perturbation with continuation necks at the positions `L_q`
from period-one `C¹` inner Hamiltonians `G_q` to outer Hamiltonians `H_q` on a finite-dimensional
manifold with a nondegenerate two-form, with components `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`
in the global coordinate `z = s + i t` of `ℂ`, and let `u` be a map which is `C¹` on `S`. For
`R ≥ 2` with `R ≥ L_q + 1` for every end `q`, the Floer energy of `u` over the truncation `S_R` is
the symplectic area, plus the signed sum of the integrals of the outer Hamiltonians along the
boundary loops `ℓ_q(t) = u(φ_q(±R + i t))`, minus the integrated curvature over `S`:

`∫_{S_R} E = ∫_{S_R} u^*ω + ∑ q, ±∫₀¹ H_q(t, ℓ_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0` and `1` and `-` on the output end `∞`. The energy, area and
curvature densities are integrable over `S_R` automatically. -/
theorem integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z (u z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  have hT : IsCompact T :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation R)
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  have hKc := contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    (contMDiffAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L)
  have hKp := contMDiffOn_thricePuncturedSphereReal_prod_univ_of_forall_contMDiffAt
    (contMDiffAt_pairOfPantsPerturbation hH hHs)
  have hRc := (integrableOn_hamiltonianCurvature_pairOfPantsContinuationPerturbation ω hG hH hGs
    hHs L hu.continuousOn).mono_set hTS
  have hRp := (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation ω hH hHs
    hu.continuousOn).mono_set hTS
  -- Outside `S_R` the datum is the pair-of-pants datum of `H`, so the energy plus the integrated
  -- curvature over `S_R` is the same for both data.
  have hcomp := hω.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn
    isOpen_thricePuncturedSphereReal hu (hKc 1) (hKc Complex.I) (hKp 1) (hKp Complex.I) hT hTS
    (eqOn_pairOfPantsContinuationPerturbation hR hRL 1)
    (eqOn_pairOfPantsContinuationPerturbation hR hRL Complex.I)
    (hω.integrableOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu (hKc 1)
      (hKc Complex.I) hT hTS hRc) hRc
    (hω.integrableOn_floerEnergyDensity isOpen_thricePuncturedSphereReal hu (hKp 1)
      (hKp Complex.I) hT hTS hRp) hRp
  -- The curvature of the datum with continuation necks vanishes on `S` outside `S_R`.
  have hRS := setIntegral_thricePuncturedSphereReal_eq_setIntegral_truncation (R := R)
    (f := fun z ↦ ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z)) fun z hz q hq ↦
      hamiltonianCurvature_pairOfPantsContinuationPerturbation_eq_zero_of_lt ω hH hHs hz
        (by linarith) (by linarith [hRL q]) _
  have hP := hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation hH hHs
    isOpen_thricePuncturedSphereReal (preimage_truncation_subset_thricePuncturedSphereReal R) hu
    (by linarith : 1 ≤ R)
  rw [smoothTransition.one_of_one_le (by linarith), one_mul] at hP
  rw [hRS]
  linarith

/-- **The energy bound on a truncated pair of pants with continuation necks, for a manifold
target.** If `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, then for every `R ≥ 2` with
`R ≥ L_q + 1` for all `q`, the Floer energy of `u` over the truncation `S_R` differs from the
symplectic area plus the Hamiltonian boundary terms by at most `∑ q, (B_q + D_q)`, uniformly in
`R` and in the neck positions. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_sub_le
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I))))| ≤ ∑ q, (B q + D q) := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation hG hH hGs hHs
    hu hR hRL, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs hHs
    hGB hHB hD L u _

/-- **The topological energy of a truncated pair of pants with continuation necks is bounded
below, for a manifold target.** Let `u` be a map which is `C¹` on `S` and solves the Floer equation
`(du - X_K)^{0,1} = 0` on the truncation `S_R` for almost complex structures `J z` on the tangent
spaces `T_{u(z)} M` tamed by the two-form, where `K` is the perturbation with continuation necks
from period-one `C¹` Hamiltonians `G_q` to `H_q` with `|G_q|, |H_q| ≤ B_q` and
`|H_q - G_q| ≤ D_q`. If `R ≥ 2` and `R ≥ L_q + 1` for all `q`, then the symplectic area of `u`
over `S_R` plus the Hamiltonian boundary terms is at least `-∑ q, (B_q + D_q)`. The constant does
not depend on the neck positions. -/
theorem neg_sum_le_integral_add_sum_of_pairOfPantsContinuationPerturbation_truncation
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {R : ℝ} (hR : 2 ≤ R)
    (hRL : ∀ q, L q + 1 ≤ R) {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          u z).toLinearMap) :
    -∑ q, (B q + D q) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1,
          H q t (u (Complex.equivRealProdCLM
            (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) := by
  have hpos := setIntegral_nonneg (μ := volume) (measurableSet_preimage_truncation R)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := abs_le.1
    (hω.abs_integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation_sub_le hG hH
      hGs hHs hGB hHB hD hu hR hRL)
  linarith [h.2]

/-- **The energy identity on a pair of pants with continuation necks, for a manifold target.**
Let `K` be the perturbation with continuation necks at the positions `L_q` from bounded period-one
`C¹` Hamiltonians `G_q` to `H_q` on a finite-dimensional manifold with a nondegenerate two-form.
Let `u` be a map which is `C¹` on `S`, whose loops `t ↦ u(φ_q(±R + i t))` along the circles of the
end `q` converge pointwise to loops `x_q` as `R → ∞`, and whose Floer energy density and
symplectic area density are integrable over `S`. Then

`∫_S E = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`,

with the sign `+` on the input ends `0`, `1` and `-` on the output end `∞`. Only the outer
Hamiltonians appear in the boundary term, and the curvature term is integrable
(`SmoothTwoForm.integrableOn_hamiltonianCurvature_pairOfPantsContinuationPerturbation`). -/
theorem integral_floerEnergyDensity_pairOfPantsContinuationPerturbation
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hHB : ∀ q t x, |H q t x| ≤ B q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)) -
        ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z (u z) := by
  -- Both sides are the limits as `R → ∞` of the two sides of the identity on the truncation
  -- `S_R`, which holds once `R ≥ 2` and `R ≥ L_q + 1` for all `q`.
  have hrhs := ((tendsto_setIntegral_truncation hA).add
    (tendsto_finsetSum Finset.univ fun q _ ↦
      (tendsto_intervalIntegral_endLoop (fun q ↦ (hHs q).continuous) hHB hu.continuousOn
        (hx q)).const_mul q.endSign)).sub_const
    (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z))
  refine tendsto_nhds_unique (tendsto_setIntegral_truncation hE) (hrhs.congr' ?_)
  filter_upwards [eventually_ge_atTop 2,
    Filter.eventually_all.2 fun q ↦ eventually_ge_atTop (L q + 1)] with R hR hRL
  exact (hω.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation hG hH hGs
    hHs hu hR hRL).symm

/-- **The energy bound on the pair of pants with continuation necks, for a manifold target.** Under
the hypotheses of the energy identity
`integral_floerEnergyDensity_pairOfPantsContinuationPerturbation`, if `|G_q|, |H_q| ≤ B_q` and
`|H_q - G_q| ≤ D_q`, the Floer energy over `S` differs from its topological part, the symplectic
area plus the Hamiltonian terms at the asymptotic orbits, by at most `∑ q, (B_q + D_q)`, whatever
the neck positions. -/
theorem abs_integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
      thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal) :
    |(∫ z in thricePuncturedSphereReal, ω.floerEnergyDensity
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t)| ≤ ∑ q, (B q + D q) := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation hG hH hGs hHs hHB hu hx hE
    hA, hsub, abs_neg]
  exact abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH hGs hHs
    hGB hHB hD L u _

/-- **The topological energy of a pair of pants with continuation necks is bounded below, for a
manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost
complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form, under the
hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation`,
with `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`. Since its energy is nonnegative, its symplectic
area plus the Hamiltonian terms of the outer Hamiltonians at the asymptotic orbits is at least
`-∑ q, (B_q + D_q)`, for all neck positions. -/
theorem neg_sum_le_integral_add_sum_of_pairOfPantsContinuationPerturbation
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal) {x : Puncture → ℝ → M}
    (hx : ∀ q t, Tendsto (fun R : ℝ ↦ u (Complex.equivRealProdCLM
      (q.cylindricalEndLift (↑(q.endSign * R) + ↑t * Complex.I)))) atTop (𝓝 (x q t)))
    (hE : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦
        pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u) thricePuncturedSphereReal)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          u z).toLinearMap) :
    -∑ q, (B q + D q) ≤
      (∫ z in thricePuncturedSphereReal,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, H q t (x q t) := by
  have hpos := setIntegral_nonneg (μ := volume) isOpen_thricePuncturedSphereReal.measurableSet
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have hC := (abs_le.1 (abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le
    ω hG hH hGs hHs hGB hHB hD L u thricePuncturedSphereReal)).1
  rw [hω.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation hG hH hGs hHs hHB hu hx hE
    hA] at hpos
  linarith

/-- **The energy identity for the pair of pants with continuation necks, for a manifold target,
in terms of the limits of the end integrals.** Let `u` be a map which is `C¹` on `S` and solves the
Floer equation `(du - X_K)^{0,1} = 0` on `S` for almost complex structures `J z` on the tangent
spaces `T_{u(z)} M` tamed by the two-form, where `K` is the perturbation with continuation necks
from period-one `C¹` Hamiltonians `G_q` to `H_q`, and suppose that its symplectic area density is
integrable. If on each end `q` the integrals `∫₀¹ H_q(t, u(φ_q(s, t))) dt` tend to `h_q` as
`±s → ∞`, then the energy of `u` is

`E(u) = ∫ u^*ω + h₀ + h₁ - h_∞ - ∫ R_K(u)`.

Neither the integrability of the energy density nor the convergence of the end loops is
assumed. -/
theorem lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          u z).toLinearMap)
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    {h : Puncture → ℝ}
    (hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (h q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) =
      ENNReal.ofReal ((∫ z, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q -
        ∫ z, ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z (u z)) := by
  -- The complement of `S` is null, so the curvature, integrable over `S`, is integrable.
  have hR := integrableOn_hamiltonianCurvature_pairOfPantsContinuationPerturbation ω hG hH hGs hHs
    L hu.continuousOn
  rw [IntegrableOn, Measure.restrict_eq_self_of_ae_mem ae_mem_thricePuncturedSphereReal] at hR
  exact hω.lintegral_floerEnergyDensity_eq_of_eq_smul_endAngularForm
    (fun w x ↦ contMDiffAt_pairOfPantsContinuationPerturbation hG hH hGs hHs L w x)
    (fun _ _ x hw ↦ pairOfPantsContinuationPerturbation_eq_smul_endAngularForm_of_le hw x) hH hu
    (fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)) hA hR hh

/-- **The energy bound for the pair of pants with continuation necks, for a manifold target, in
terms of the limits of the end integrals.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq`,
if `|G_q|, |H_q| ≤ B_q` and `|H_q - G_q| ≤ D_q`, then the energy of `u` is at most
`∫ u^*ω + h₀ + h₁ - h_∞ + ∑ q, (B_q + D_q)`, whatever the neck positions. -/
theorem lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le
    (hω : ω.IsNondegenerate) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B D : Puncture → ℝ} (hGB : ∀ q t x, |G q t x| ≤ B q) (hHB : ∀ q t x, |H q t x| ≤ B q)
    (hD : ∀ q t x, |H q t x - G q t x| ≤ D q) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u thricePuncturedSphereReal)
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ thricePuncturedSphereReal, (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ thricePuncturedSphereReal,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          u z).toLinearMap)
    (hA : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ))
    {h : Puncture → ℝ}
    (hh : ∀ q, Tendsto (fun σ ↦ ∫ t in (0 : ℝ)..1, H q t (u (endChart q (q.endSign * σ, t))))
      atTop (𝓝 (h q))) :
    ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) ≤
      ENNReal.ofReal ((∫ z, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ∑ q, q.endSign * h q + ∑ q, (B q + D q)) := by
  rw [hω.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_eq hG hH hGs hHs hu hJ
    hfloer hA hh]
  refine ENNReal.ofReal_le_ofReal ?_
  have hRB := abs_setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_le ω hG hH
    hGs hHs hGB hHB hD L u univ
  rw [setIntegral_univ] at hRB
  linarith [neg_abs_le (∫ z, ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦
      pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
    z (u z))]

end IsNondegenerate

end TauCeti.SmoothTwoForm
