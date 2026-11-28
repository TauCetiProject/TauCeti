/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.DG.Circle.LoopChain
import TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane
import TauCeti.Topology.Homotopy.HomotopyGroup.Homotopy

/-!
# The path-loop fibration of the circle in DG Morse homology

Let `X` be a pseudo-gradient adapted to the height function `circleCos` of the circle
`S¹ = ℝ ⧸ 2πℤ`, with its maximum at `0` and its minimum at `π`, and let `S` be a twisting chain
system on its trajectory spaces. In the construction of Barraud and Cornea the Barraud–Cornea
cocycle (`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) evaluates the broken trajectories
into the Moore loops of the circle itself, through a self-map `θ` of `S¹` which sends both critical
points to `0` and is homotopic to the identity: the collapse of an embedded tree joining the
critical points, followed by a homotopy inverse of that collapse. This file carries out the
computation of the DG Morse homology of the circle in this setting, `Y = S¹` and `y₀ = 0`.

* **The collapse of the upper half-circle.** The tree joining the critical points can be taken to
  be the upper half-circle `[0, π]`. The map `TauCeti.circleCosArcCollapse` sends it to `0` and
  stretches the lower half-circle `[π, 2π]` once over the circle, at the angle `2 (φ - π)`
  (`TauCeti.circleCosArcCollapse_coe`). It is homotopic to the identity relative to `0`
  (`TauCeti.homotopicRel_circleCosArcCollapse`), through the maps
  `x ↦ x + (1 - s) σ(x)` for the displacement `σ` of the collapse.
* **The cocycle is `1 - t`.** For every self-map `θ` homotopic to the identity relative to `0`
  and constant on the upper half-circle, such as the collapse, the two trajectories from the
  maximum to the minimum are carried to the loop of class `1`, along the upper half-circle, and to
  the loop of class `t`, along the lower one, where `t` is the class of the loop once around the
  circle, the generator of `π₁(S¹, 0) ≅ ℤ` of winding number `1`. So when `S` gives the two
  trajectories opposite coefficients `r` and `-r`, the image of the cocycle in
  `R[π₁(S¹, 0)] = R[t, t⁻¹]` is `(1 - t) r`
  (`..._circleCos_eq_single_sub_single` below), the twisted Morse differential `d = 1 - t` of the
  circle. With coefficients `1` in characteristic two it is `1 + t`
  (`..._circleCos_eq_single_add_single_of_charTwo`).
* **The path-loop fibration has the homology of a point.** Take as coefficients the chains
  `C_*(Ω₀ S¹; R)` on the Moore loops of the circle, a right DG module over themselves: the DG
  local system of the path fibration `P₀ S¹ → S¹`, whose total space is contractible. The circle
  is aspherical and the image of the loop once around the circle under a self-map homotopic to
  the identity relative to `0` is the generator `t`, of infinite order. So the hypotheses of
  `TauCeti.IsAdaptedPseudoGradient.exists_twistedDifferential_eq_circleCos` hold, and every cycle
  of the DG Morse complex with these coefficients whose coefficient of the minimum has
  augmentation zero is a boundary
  (`IsAdaptedPseudoGradient.exists_twistedDifferential_eq_circleCos_of_homotopicRel`, and
  `IsAdaptedPseudoGradient.exists_twistedDifferential_eq_circleCos_of_homotopicRel_of_charTwo`
  in characteristic two). Since the augmentation of that coefficient vanishes on boundaries and
  is `1` on the cycle `1 ⊗ π`, the DG Morse homology `H_*(S¹; C_*(Ω S¹))` is `R`, the homology of
  the total space `P₀ S¹` of the fibration. With the loops acting trivially, a twisted complex of
  the circle computes `H_*(S¹) ⊗ H_*(Ω S¹)` instead, as for Brown's cocycle of the circle
  (`TauCeti.nonempty_loopCellCocycle_homology_iso_of_forall_op_smul_eq`).

The lemmas in the namespace `TauCeti.IsAdaptedPseudoGradient` are abbreviated above.

## Main definitions

* `TauCeti.circleCosArcCollapse`: the collapse of the upper half-circle, a self-map of the circle
  homotopic to the identity relative to `0` that sends both critical points of the cosine to `0`.

## Main results

* `TauCeti.circleCosArcCollapse_coe`, `TauCeti.circleCosArcCollapse_coe_of_mem_Icc`,
  `TauCeti.homotopicRel_circleCosArcCollapse`: the collapse of the upper half-circle, its values
  and its homotopy to the identity.

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_single_sub_single`: through a
  collapse of the upper half-circle, the degree-zero entry of the Barraud–Cornea cocycle of the
  cosine is `(1 - t) r`; `..._eq_single_add_single_of_charTwo` is its form `1 + t` modulo two.
* `exists_twistedDifferential_eq_circleCos_of_homotopicRel`: the DG Morse complex of the circle
  with coefficients in the chains on its Moore loops has the homology of a point;
  `..._of_charTwo` is its form modulo two.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3, 5 and 7.
-/

public section

open Function MonoidAlgebra Set
open scoped Manifold Real

namespace TauCeti

local instance morseDGCirclePathLoopTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-! ### The collapse of the upper half-circle -/

/-- The displacement of the collapse of the upper half-circle, `max 0 (2 (φ - π)) - φ` on the
fundamental domain `[0, 2π)`. It vanishes at both ends of the domain, so it is continuous on the
circle. -/
private noncomputable def circleCosArcCollapseShift : C(AddCircle (2 * π), ℝ) :=
  ⟨AddCircle.liftIco (2 * π) 0 fun φ ↦ max 0 (2 * (φ - π)) - φ,
    AddCircle.liftIco_zero_continuous
      (by
        rw [max_eq_left (by linarith [Real.pi_pos]), max_eq_right (by linarith [Real.pi_pos])]
        ring)
      (by fun_prop)⟩

private theorem circleCosArcCollapseShift_coe {φ : ℝ} (hφ : φ ∈ Ico 0 (2 * π)) :
    circleCosArcCollapseShift φ = max 0 (2 * (φ - π)) - φ := by
  simp only [circleCosArcCollapseShift, ContinuousMap.coe_mk]
  exact AddCircle.liftIco_zero_coe_apply hφ

private theorem circleCosArcCollapseShift_zero : circleCosArcCollapseShift 0 = 0 := by
  have h := circleCosArcCollapseShift_coe ⟨le_rfl, Real.two_pi_pos⟩
  rwa [AddCircle.coe_zero, max_eq_left (by linarith [Real.pi_pos]), sub_zero] at h

/-- **The collapse of the upper half-circle.** The self-map of the circle `ℝ ⧸ 2πℤ` sending the
point at the angle `φ ∈ [0, 2π)` to the angle `max 0 (2 (φ - π))`
(`TauCeti.circleCosArcCollapse_coe`): it sends the upper half-circle `[0, π]`, the arc joining the
maximum `0` and the minimum `π` of the cosine, to `0`, and stretches the lower half-circle once
over the whole circle. It is the collapse of this arc followed by the identification of the
quotient with the circle, and it is homotopic to the identity relative to `0`
(`TauCeti.homotopicRel_circleCosArcCollapse`). -/
noncomputable def circleCosArcCollapse : C(AddCircle (2 * π), AddCircle (2 * π)) :=
  ⟨fun x ↦ x + (circleCosArcCollapseShift x : AddCircle (2 * π)),
    continuous_id.add ((AddCircle.continuous_mk' _).comp circleCosArcCollapseShift.continuous)⟩

/-- The collapse of the upper half-circle is at the angle `max 0 (2 (φ - π))` at the angle
`φ ∈ [0, 2π)`. -/
theorem circleCosArcCollapse_coe {φ : ℝ} (hφ : φ ∈ Ico 0 (2 * π)) :
    circleCosArcCollapse φ = (max 0 (2 * (φ - π)) : ℝ) := by
  rw [circleCosArcCollapse, ContinuousMap.coe_mk, circleCosArcCollapseShift_coe hφ,
    ← AddCircle.coe_add, add_sub_cancel]

/-- The collapse of the upper half-circle sends the upper half-circle `[0, π]` to `0`. -/
theorem circleCosArcCollapse_coe_of_mem_Icc {φ : ℝ} (hφ : φ ∈ Icc 0 π) :
    circleCosArcCollapse φ = 0 := by
  rw [circleCosArcCollapse_coe ⟨hφ.1, by linarith [hφ.2, Real.pi_pos]⟩,
    max_eq_left (by linarith [hφ.2]), AddCircle.coe_zero]

/-- The collapse of the upper half-circle sends both critical points of the cosine to `0`. -/
theorem circleCosArcCollapse_apply_criticalPoints (x : criticalPoints 𝓘(ℝ) circleCos) :
    circleCosArcCollapse x = 0 := by
  rcases eq_circleCosMaxCrit_or_eq_circleCosMinCrit x with rfl | rfl
  · rw [coe_circleCosMaxCrit, ← AddCircle.coe_zero]
    exact circleCosArcCollapse_coe_of_mem_Icc ⟨le_rfl, Real.pi_pos.le⟩
  · rw [coe_circleCosMinCrit]
    exact circleCosArcCollapse_coe_of_mem_Icc ⟨Real.pi_pos.le, le_rfl⟩

/-- **The collapse of the upper half-circle is homotopic to the identity relative to `0`**,
through the maps `x ↦ x + (1 - s) σ(x)` for the displacement `σ` of the collapse, which vanishes
at `0`. -/
theorem homotopicRel_circleCosArcCollapse :
    circleCosArcCollapse.HomotopicRel (ContinuousMap.id _) {0} :=
  ⟨{ toFun := fun p ↦ p.2 + (((1 - (p.1 : ℝ)) * circleCosArcCollapseShift p.2 : ℝ) :
        AddCircle (2 * π))
     continuous_toFun := continuous_snd.add <| (AddCircle.continuous_mk' _).comp <|
        (continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).mul
          (circleCosArcCollapseShift.continuous.comp continuous_snd)
     map_zero_left x := by simp [circleCosArcCollapse]
     map_one_left x := by simp
     prop' t x hx := by
       rw [mem_singleton_iff.1 hx]
       simp [circleCosArcCollapse, circleCosArcCollapseShift_zero] }⟩

/-! ### The Barraud–Cornea cocycle through a collapse -/

namespace IsAdaptedPseudoGradient

variable {X : (x : AddCircle (2 * π)) → TangentSpace 𝓘(ℝ) x}
  (hX : IsAdaptedPseudoGradient circleCos X) {ι : Type*} {c : ι → ℝ}
  {θ : C(AddCircle (2 * π), AddCircle (2 * π))}
  {R : Type} [CommRing R] {ind : criticalPoints 𝓘(ℝ) circleCos → ℤ}
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ) circleCos,
    Ioo (circleCos y) (circleCos x) ⊆ closure (range c))
  (hθ : ∀ x : criticalPoints 𝓘(ℝ) circleCos, θ x = 0)
  (hc : ∀ i (x : criticalPoints 𝓘(ℝ) circleCos), c i ≠ circleCos x)
  (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
  (hθ' : θ.HomotopicRel (ContinuousMap.id _) {0})

include hθ' in
/-- A self-map of the circle homotopic to the identity relative to `0` fixes the class of the loop
once around the circle. -/
private theorem mapOfEq_fundamentalGroupHom_circleCosLoop :
    FundamentalGroup.mapOfEq θ (hθ circleCosMaxCrit)
        (MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop) =
      MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop :=
  FundamentalGroup.mapOfEq_apply_eq_self_of_homotopicRel (hθ circleCosMaxCrit)
    (mem_singleton _) hθ' _

include hθ' in
/-- **Through a collapse of the upper half-circle, the Barraud–Cornea cocycle of the cosine is
`(1 - t) r`.** Let `θ` be a self-map of the circle homotopic to the identity relative to `0` and
sending the upper half-circle `[0, π]` to `0`, such as `TauCeti.circleCosArcCollapse`, and let `S`
give the trajectories from the maximum to the minimum through the upper and the lower half-circle
opposite coefficients `r` and `-r`. Then the image in the group ring `R[π₁(S¹, 0)]` of the entry
of the Barraud–Cornea cocycle at `(0, π)` is `r - t r`, where `t` is the class of the loop once
around the circle, of winding number `1`
(`TauCeti.windingNumber_fundamentalGroupHom_circleCosLoop`): the trajectories evaluate to loops of
classes `1` and `t`. -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_single_sub_single
    (harc : ∀ φ ∈ Icc 0 π, θ (φ : AddCircle (2 * π)) = 0) {r : R}
    (hS₁ : NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
      (hX.circleCosTrajectory c 1) = r)
    (hS₂ : NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
      (hX.circleCosTrajectory c (-1)) = -r) :
    loopChainToGroupAlgebra (AddCircle (2 * π)) 0 R
        ((hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m circleCosMaxCrit
          circleCosMinCrit) =
      single 1 r - single (MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop) r := by
  have hg := fundamentalGroupHom_circleCosHalfLoop_one_eq_one θ (hθ circleCosMaxCrit)
    (hθ circleCosMinCrit) harc
  rw [hX.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_one_sub_mul hdense hθ hc S
      hS₁ hS₂, mapOfEq_fundamentalGroupHom_circleCosLoop hθ hθ', hg, sub_mul, one_mul,
    single_mul_single, mul_one, one_mul]

include hθ' in
/-- **Through a collapse of the upper half-circle, the Barraud–Cornea cocycle of the cosine is
`1 + t` modulo two.** Over a ring of characteristic two, when `S` gives both trajectories from the
maximum to the minimum the coefficient `1`, as the fundamental chains of the two-point trajectory
space do, the image in `R[π₁(S¹, 0)]` of the entry of the Barraud–Cornea cocycle at `(0, π)` is
`1 + t`, for every self-map `θ` homotopic to the identity relative to `0` and sending the upper
half-circle to `0`, with `t` the class of the loop once around the circle. -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_single_add_single_of_charTwo
    [CharP R 2] (harc : ∀ φ ∈ Icc 0 π, θ (φ : AddCircle (2 * π)) = 0)
    (hS : ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0) w
      = 1) :
    loopChainToGroupAlgebra (AddCircle (2 * π)) 0 R
        ((hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m circleCosMaxCrit
          circleCosMinCrit) =
      single 1 1 + single (MooreLoopSpace.fundamentalGroupHom 0 circleCosLoop) 1 := by
  rw [hX.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_single_sub_single hdense hθ hc
      S hθ' harc (hS _) ((hS _).trans CharTwo.neg_one_eq_one.symm), sub_eq_add_neg, ← single_neg,
    CharTwo.neg_eq]

/-! ### The homology of the path-loop fibration -/

variable {r : R}
  (hS₁ : NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
    (hX.circleCosTrajectory c 1) = r)
  (hS₂ : NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0)
    (hX.circleCosTrajectory c (-1)) = -r)

include hθ' hS₁ hS₂ in
/-- **The DG Morse complex of the circle with coefficients in the chains on its Moore loops has the
homology of a point.** Let `θ` be a self-map of the circle homotopic to the identity relative to
`0` and sending both critical points of the cosine to `0`, such as the collapse of the upper
half-circle `TauCeti.circleCosArcCollapse`, and let `S` give the two trajectories from the maximum
to the minimum opposite unit coefficients `r` and `-r`. Then every cycle `u` of the DG Morse
complex with coefficients in the chain algebra `C_*(Ω₀ S¹; R)`, the DG local system of the path
fibration of the circle, whose coefficient of the minimum has augmentation zero is a boundary.
Since the augmentation vanishes on boundaries
(`TauCeti.IsAdaptedPseudoGradient.loopChainAugmentation_twistedDifferential_circleCos`) and takes
the value `1` on the cycle `1 ⊗ π`
(`TauCeti.IsAdaptedPseudoGradient.twistedDifferential_single_circleCosMinCrit_one`), the homology
is `R`, in the degree of the minimum: the homology of the contractible total space of the path
fibration. -/
theorem exists_twistedDifferential_eq_circleCos_of_homotopicRel
    (hind : ind circleCosMinCrit < ind circleCosMaxCrit) (hr : IsUnit r)
    {u : criticalPoints 𝓘(ℝ) circleCos → loopChainAlgebra (AddCircle (2 * π)) 0 R}
    (hu : twistedDifferential (hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
      (cubicalChainGrading (MooreLoopSpace (AddCircle (2 * π)) 0) R)
      (cubicalChainDifferential (MooreLoopSpace (AddCircle (2 * π)) 0) R) u = 0)
    (hε : loopChainAugmentation (AddCircle (2 * π)) 0 R (u circleCosMinCrit) = 0) :
    ∃ v, twistedDifferential (hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
      (cubicalChainGrading (MooreLoopSpace (AddCircle (2 * π)) 0) R)
      (cubicalChainDifferential (MooreLoopSpace (AddCircle (2 * π)) 0) R) v = u :=
  hX.exists_twistedDifferential_eq_circleCos hdense hθ hc S hind hS₁ hS₂
    (isAspherical_iff.1 (AddCircle.isAspherical _ 0)).2
    ((mapOfEq_fundamentalGroupHom_circleCosLoop hθ hθ').symm ▸
      zpowers_fundamentalGroupHom_circleCosLoop)
    ((mapOfEq_fundamentalGroupHom_circleCosLoop hθ hθ').symm ▸
      not_isOfFinOrder_fundamentalGroupHom_circleCosLoop)
    hr hu hε

omit hS₁ hS₂ in
include hθ' in
/-- **The DG Morse complex of the circle with coefficients in the chains on its Moore loops has the
homology of a point, modulo two.** Over a ring of characteristic two, for a twisting chain system
giving both trajectories from the maximum to the minimum the coefficient `1` and a self-map `θ`
homotopic to the identity relative to `0` sending the critical points to `0`, every cycle of the
DG Morse complex with coefficients in `C_*(Ω₀ S¹; R)` whose coefficient of the minimum has
augmentation zero is a boundary, as in
`TauCeti.IsAdaptedPseudoGradient.exists_twistedDifferential_eq_circleCos_of_homotopicRel`. -/
theorem exists_twistedDifferential_eq_circleCos_of_homotopicRel_of_charTwo [CharP R 2]
    (hind : ind circleCosMinCrit < ind circleCosMaxCrit)
    (hS : ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain circleCosMaxCrit circleCosMinCrit 0) w
      = 1)
    {u : criticalPoints 𝓘(ℝ) circleCos → loopChainAlgebra (AddCircle (2 * π)) 0 R}
    (hu : twistedDifferential (hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
      (cubicalChainGrading (MooreLoopSpace (AddCircle (2 * π)) 0) R)
      (cubicalChainDifferential (MooreLoopSpace (AddCircle (2 * π)) 0) R) u = 0)
    (hε : loopChainAugmentation (AddCircle (2 * π)) 0 R (u circleCosMinCrit) = 0) :
    ∃ v, twistedDifferential (hX.barraudCorneaCocycle isMorse_circleCos hdense hθ hc S).m
      (cubicalChainGrading (MooreLoopSpace (AddCircle (2 * π)) 0) R)
      (cubicalChainDifferential (MooreLoopSpace (AddCircle (2 * π)) 0) R) v = u :=
  hX.exists_twistedDifferential_eq_circleCos_of_homotopicRel hdense hθ hc S hθ' (hS _)
    ((hS _).trans CharTwo.neg_one_eq_one.symm) hind isUnit_one hu hε

end IsAdaptedPseudoGradient

end TauCeti
