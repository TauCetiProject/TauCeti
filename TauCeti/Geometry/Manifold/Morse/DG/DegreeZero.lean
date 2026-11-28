/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic
public import TauCeti.Geometry.Manifold.Morse.DG.BarraudCornea

/-!
# The degree-zero part of the Barraud–Cornea cocycle

Let `f` be a Morse function on a compact boundaryless manifold `M`, with an adapted
pseudo-gradient `X`, and let `S` be a twisting chain system on the trajectory spaces `L(x, y)` of
`f`. Its Barraud–Cornea cocycle (`TauCeti.IsAdaptedPseudoGradient.barraudCorneaCocycle`) has as
entry at `(x, y)` the push-forward of the chain of `L(x, y)` into the chains `C^□_*(Ω_{y₀} Y; R)`
on the Moore loops, along the evaluation of broken trajectories into loops through a map
`θ : M → Y` that sends every critical point to `y₀`. This file computes the degree-zero
truncation of these entries, their image in the group ring `R[π₁(Y, y₀)]`
(`TauCeti.loopChainToGroupAlgebra`), which is the part of the cocycle seen by the classical complex
with local coefficients in the second page of its index spectral sequence.

* **The truncation of an entry counts loops.** The truncation of the entry at `(x, y)` only sees
  the `0`-chain `∑ r_u [u]` of `L(x, y)`, and it is `∑ r_u [θ ∘ u]`: every broken trajectory `u`
  contributes the class in `π₁(Y, y₀)` of the loop `θ ∘ u`, with the coefficient of `u`
  (`IsAdaptedPseudoGradient.loopChainToGroupAlgebra_barraudCorneaCocycle_m`).
* **Between consecutive indices it is the Morse differential with monodromy.** Under the
  Morse–Smale condition, if `ind x = ind y + 1`, the trajectory space `L(x, y)` is a finite set
  of unbroken trajectories from `x` to `y`, one point for each unparametrized trajectory
  (`IsAdaptedPseudoGradient.IsMorseSmale.finite_morseBrokenTrajectorySpace`,
  `IsAdaptedPseudoGradient.IsMorseSmale.natCard_morseBrokenTrajectorySpace`). If every trajectory
  carries the coefficient `1` in the chain of `S`, the truncated entry is the sum of the classes
  of the loops `θ ∘ u` over the trajectories `u`, and its augmentation is the number of
  trajectories. With coefficients in `ZMod 2` this is the coefficient of `y` in the mod-two Morse
  boundary of `x`
  (`IsMorseSmale.augmentation_loopChainToGroupAlgebra_barraudCorneaCocycle_m` and its form
  `..._eq_morseBoundaryCoeff`, in the namespace `TauCeti.IsAdaptedPseudoGradient`).

So the degree-zero part of the Barraud–Cornea cocycle is the Morse differential in which each
trajectory is weighted by the homotopy class of its loop. For instance, for the height function of
the circle, the two trajectories from the maximum to the minimum have loops of classes `g` and
`t g`, with `t` the image of a generator of `π₁(S¹)`, so the entry is `(1 + t) g` when both carry
the coefficient `1` (`TauCeti.fundamentalGroupHom_circleCosHalfLoop_neg_one` and
`TauCeti.IsAdaptedPseudoGradient.loopChainToGroupAlgebra_barraudCorneaCocycle_m_circleCos_eq_mul`,
in `TauCeti.Geometry.Manifold.Morse.DG.Circle.Basic`). With `θ` collapsing the upper arc (through
`π / 2`) between the critical points (an illustration, not formalized here), `g = 1` and the entry
is `1 + t` in `(ZMod 2)[π₁(S¹)]`; collapsing the lower arc instead gives `t g = 1` and the entry
`1 + t⁻¹`. For integral fundamental chains of the trajectory spaces the coefficients
`r_u` are instead the orientation signs of the trajectories; this integral form is a remark, not
formalized here.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `loopChainToGroupAlgebra_barraudCorneaCocycle_m`: the truncated entry is the sum, over the
  points `u` of the `0`-chain of `L(x, y)`, of the classes of the loops `θ ∘ u`.
* `IsMorseSmale.augmentation_loopChainToGroupAlgebra_barraudCorneaCocycle_m`: between consecutive
  indices, for a chain giving every trajectory the coefficient `1`, the truncated entry has
  augmentation the number of trajectories.
* `IsMorseSmale.augmentation_loopChainToGroupAlgebra_barraudCorneaCocycle_m_eq_morseBoundaryCoeff`:
  modulo two, it is the coefficient of the Morse boundary.

## References

* J.-F. Barraud, O. Cornea, *Lagrangian intersections and the Serre spectral sequence*, Ann. of
  Math. (2) 166 (2007), 657–722, §2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3 and 5.
-/

public section

open Set
open scoped ContDiff Manifold

universe u

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {ι : Type*}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X) {c : ι → ℝ} (hf : IsMorse 𝓘(ℝ, E) f)
  (hdense : ∀ x y : criticalPoints 𝓘(ℝ, E) f, Ioo (f y) (f x) ⊆ closure (range c))
  {Y : Type u} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
  (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀)
  {R : Type u} [CommRing R] [Fintype (criticalPoints 𝓘(ℝ, E) f)]
  {ind : criticalPoints 𝓘(ℝ, E) f → ℤ} (hc : ∀ i (x : criticalPoints 𝓘(ℝ, E) f), c i ≠ f x)

/-- **The truncated Barraud–Cornea cocycle counts loops.** The image in the group ring
`R[π₁(Y, y₀)]` of the entry at `(x, y)` of the Barraud–Cornea cocycle of `S` only sees the
`0`-chain `∑ r_u [u]` of the trajectory space `L(x, y)` in the chain of `S`: it is `∑ r_u [θ ∘ u]`,
each broken trajectory `u` contributing the class of its loop with the coefficient of `u`. -/
theorem loopChainToGroupAlgebra_barraudCorneaCocycle_m
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    (x y : criticalPoints 𝓘(ℝ, E) f) :
    loopChainToGroupAlgebra Y y₀ R ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y) =
      (NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0)).sum fun w r ↦
        MonoidAlgebra.single (MooreLoopSpace.fundamentalGroupHom y₀
          (hX.morseLoopEvaluation hf hdense hθ x y
            (ContinuousMap.inclusion (morseBrokenTrajectorySpace_subset _ _) w))) r := by
  rw [barraudCorneaCocycle_m, loopChainToGroupAlgebra_cubicalChainSumMap]
  simp only [ContinuousMap.comp_apply]

namespace IsMorseSmale

variable {hX}

omit [Fintype (criticalPoints 𝓘(ℝ, E) f)] in
include hf hdense in
/-- Between critical points of consecutive index, the trajectory space has one point for each
unparametrized trajectory, also when no level of `c` lies between them: then there is no
trajectory at all. -/
private theorem natCard_morseBrokenTrajectorySpace_of_eq_add_one (h : hX.IsMorseSmale)
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1) :
    Nat.card (hX.morseBrokenTrajectorySpace c x y) =
      Nat.card (Quotient (Flow.connectingOrbitSetoid hX.flow x y)) := by
  have hxy : (x : M) ≠ y := fun hxy ↦ by rw [hxy] at hind; omega
  by_cases hlt : f y < f x
  · -- A level of `c` lies between `f y` and `f x`, since the levels are dense there.
    obtain ⟨m, hm⟩ := exists_between hlt
    obtain ⟨-, hmc, i, rfl⟩ := mem_closure_iff.1 (hdense x y hm) _ isOpen_Ioo hm
    exact h.natCard_morseBrokenTrajectorySpace hf
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 x.property)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 y.property) hxy hind.le ⟨i, hmc⟩
  · -- Without a drop in value there are no trajectories at all.
    have hL : IsEmpty (hX.morseBrokenTrajectorySpace c x y) :=
      ⟨fun w ↦ hlt (value_lt_of_mem_morseBrokenTrajectorySpace w.property)⟩
    rw [Nat.card_of_isEmpty, hX.natCard_orbitQuotient_eq_ncard_morseTrajectorySlice,
      eq_empty_of_forall_notMem fun z hz ↦ hlt (hX.value_lt_of_mem_morseTrajectorySlice hxy hz),
      ncard_empty]

/-- **Between consecutive indices the truncated Barraud–Cornea cocycle counts trajectories.**
Under the Morse–Smale condition, let `ind x = ind y + 1`, and let the chain of `S` give every
trajectory from `x` to `y` the coefficient `1`. Then the truncation of the entry at `(x, y)`, the
sum of the classes of the loops of the trajectories, has as augmentation the number of
unparametrized trajectories from `x` to `y`. -/
theorem augmentation_loopChainToGroupAlgebra_barraudCorneaCocycle_m (h : hX.IsMorseSmale)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) R)
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
    (hS : ∀ w, NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0) w = 1) :
    MonoidAlgebra.augmentation R (FundamentalGroup Y y₀)
        (loopChainToGroupAlgebra Y y₀ R ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      Nat.card (Quotient (Flow.connectingOrbitSetoid hX.flow x y)) := by
  rw [loopChainToGroupAlgebra_barraudCorneaCocycle_m, map_finsuppSum]
  simp only [MonoidAlgebra.augmentation_single]
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  set a := NormalizedCubicalChain.zeroEquiv _ R (S.chain x y 0)
  -- Every trajectory has the nonzero coefficient `1`, so the support of `a` is everything.
  have hsupp : (a.support : Set (hX.morseBrokenTrajectorySpace c x y)) = univ :=
    eq_univ_of_forall fun w ↦ by simp [hS w]
  rw [← natCard_morseBrokenTrajectorySpace_of_eq_add_one hf hdense h hind, ← ncard_univ, ← hsupp]
  simp [Finsupp.sum, hS]

/-- **Modulo two the truncated Barraud–Cornea cocycle is the Morse differential.** Under the
Morse–Smale condition, let `ind x = ind y + 1`, and let the chain of `S`, with coefficients in
`ZMod 2`, give every trajectory from `x` to `y` the coefficient `1`, as the chain of the finite set
`L(x, y)` with every point weighted `1` does. Then the augmentation of the truncation of the entry
at `(x, y)` is the coefficient of `y` in the mod-two Morse boundary of `x`. -/
theorem augmentation_loopChainToGroupAlgebra_barraudCorneaCocycle_m_eq_morseBoundaryCoeff
    {Y : Type} [TopologicalSpace Y] {θ : C(M, Y)} {y₀ : Y}
    (hθ : ∀ x : criticalPoints 𝓘(ℝ, E) f, θ x = y₀) (h : hX.IsMorseSmale)
    (S : TwistingChainSystem ind (hX.morseBrokenTrajectorySpaceComp hc) (ZMod 2))
    {x y : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f x = manifoldMorseIndex 𝓘(ℝ, E) f y + 1)
    (hS : ∀ w, NormalizedCubicalChain.zeroEquiv _ (ZMod 2) (S.chain x y 0) w = 1) :
    MonoidAlgebra.augmentation (ZMod 2) (FundamentalGroup Y y₀)
        (loopChainToGroupAlgebra Y y₀ (ZMod 2)
          ((hX.barraudCorneaCocycle hf hdense hθ hc S).m x y)) =
      h.morseBoundaryCoeff hf x y := by
  rw [h.augmentation_loopChainToGroupAlgebra_barraudCorneaCocycle_m hf hdense hθ hc S hind hS,
    h.morseBoundaryCoeff_eq_natCard hf hind]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
